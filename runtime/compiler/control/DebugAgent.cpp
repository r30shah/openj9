/*******************************************************************************
 * Copyright IBM Corp. and others 2021
 *
 * This program and the accompanying materials are made available under
 * the terms of the Eclipse Public License 2.0 which accompanies this
 * distribution and is available at https://www.eclipse.org/legal/epl-2.0/
 * or the Apache License, Version 2.0 which accompanies this distribution and
 * is available at https://www.apache.org/licenses/LICENSE-2.0.
 *
 * This Source Code may also be made available under the following
 * Secondary Licenses when the conditions for such availability set
 * forth in the Eclipse Public License, v. 2.0 are satisfied: GNU
 * General Public License, version 2 with the GNU Classpath
 * Exception [1] and GNU General Public License, version 2 with the
 * OpenJDK Assembly Exception [2].
 *
 * [1] https://www.gnu.org/software/classpath/license.html
 * [2] http://openjdk.java.net/legal/assembly-exception.html
 *
 * SPDX-License-Identifier: EPL-2.0 OR Apache-2.0 OR GPL-2.0 WITH Classpath-exception-2.0 OR LicenseRef-GPL-2.0 WITH Assembly-exception
 *******************************************************************************/

#include "control/DebugAgent.hpp"

#include "codegen/CodeGenerator.hpp"
#include "control/MethodToBeCompiled.hpp"
#include "control/CompilationRuntime.hpp"
#include "control/CompilationThread.hpp"
#include "env/ut_j9jit.h"
#include "env/VMAccessCriticalSection.hpp"
#include "env/VMJ9.h"
#include "ilgen/J9ByteCodeIlGenerator.hpp"
#include "jithash.h"
#include "nls/j9dmpnls.h"
#include <queue>
#include <set>

void
debugAgentSetForceUsePreexistence(J9VMThread* vmThread)
    {
    TR::Options::getCmdLineOptions()->setOption(TR_ForceUsePreexistence);
    }

BOOLEAN
debugAgentStart(J9VMThread* vmThread)
    {
    PORT_ACCESS_FROM_VMC(vmThread);

    J9JITConfig *jitConfig = vmThread->javaVM->jitConfig;
    if (NULL == jitConfig)
        {
        fprintf(stderr, "Could not locate J9JITConfig\n");
        return false;
        }
        
    TR::CompilationInfo *compInfo = TR::CompilationInfo::get(jitConfig);
    if (NULL == compInfo)
        {
        fprintf(stderr, "Could not locate TR::CompilationInfo\n");
        return false;
        }
        
    TR_J9VMBase *frontendOfThread = TR_J9VMBase::get(jitConfig, vmThread);
    if (NULL == frontendOfThread)
        {
        fprintf(stderr, "Could not locate TR_J9VMBase\n");
        return false;
        }

    // To avoid a deadlock, release compilation monitor until we are no longer holding it
    while (compInfo->getCompilationMonitor()->owned_by_self())
        {
        compInfo->releaseCompMonitor(vmThread);
        }

    // Release other monitors as well. In particular CHTable and classUnloadMonitor must not be held.
    while (TR::MonitorTable::get()->getClassTableMutex()->owned_by_self())
        {
        frontendOfThread->releaseClassTableMutex(false);
        }

    TR::CompilationInfoPerThread *threadCompInfo = compInfo->getCompInfoForThread(vmThread);
    if (NULL != threadCompInfo)
        {
        TR_MethodToBeCompiled *methodBeingCompiled = threadCompInfo->getMethodBeingCompiled();

        // If we are currently compiling a method, wake everyone waiting for it to compile
        if (NULL != methodBeingCompiled && NULL != methodBeingCompiled->getMonitor())
            {
            methodBeingCompiled->getMonitor()->enter();
            methodBeingCompiled->getMonitor()->notifyAll();
            methodBeingCompiled->getMonitor()->exit();
            
            fprintf(stderr, "Notified threads waiting\n");
            }
        }

    compInfo->getPersistentInfo()->setDisableFurtherCompilation(true);

    TR::CompilationInfoPerThread *recompilationThreadInfo = compInfo->getCompilationInfoForDiagnosticThread();
    if (NULL == recompilationThreadInfo)
        {
        j9nls_printf(PORTLIB, J9NLS_ERROR | J9NLS_STDERR, J9NLS_DMP_ERROR_IN_DUMP_STR, "JIT", "Could not locate the diagnostic thread info");
        return OMR_ERROR_INTERNAL;
        }

    auto *recompilationThread = recompilationThreadInfo->getCompilationThread();
    if (NULL == recompilationThread)
        {
        j9nls_printf(PORTLIB, J9NLS_ERROR | J9NLS_STDERR, J9NLS_DMP_ERROR_IN_DUMP_STR, "JIT", "Could not locate the diagnostic thread");
        return OMR_ERROR_INTERNAL;
        }

    compInfo->acquireCompMonitor(vmThread);
    compInfo->purgeMethodQueue(compilationFailure);
    compInfo->releaseCompMonitor(vmThread);
    
    recompilationThreadInfo->resumeCompilationThread();

    return true;
    }

BOOLEAN
debugAgentGetAllJitMethods(J9VMThread* vmThread, jobject jitMethodSet)
    {
    JNIEnv *env = (JNIEnv*)vmThread;

    jclass java_lang_Long = env->FindClass("java/lang/Long");
    jmethodID java_lang_Long_init = env->GetMethodID(java_lang_Long, "<init>", "(J)V");
    jmethodID java_lang_Long_longValue = env->GetMethodID(java_lang_Long, "longValue", "()J");

    jclass java_util_HashSet = env->FindClass("java/util/HashSet");
    jmethodID java_util_HashSet_init = env->GetMethodID(java_util_HashSet, "<init>", "()V");
    jmethodID java_util_HashSet_add = env->GetMethodID(java_util_HashSet, "add", "(Ljava/lang/Object;)Z");
    jmethodID java_util_HashSet_size = env->GetMethodID(java_util_HashSet, "size", "()I");

    jclass java_util_LinkedList = env->FindClass("java/util/LinkedList");
    jmethodID java_util_LinkedList_init = env->GetMethodID(java_util_LinkedList, "<init>", "()V");
    jmethodID java_util_LinkedList_add = env->GetMethodID(java_util_LinkedList, "add", "(Ljava/lang/Object;)Z");
    jmethodID java_util_LinkedList_isEmpty = env->GetMethodID(java_util_LinkedList, "isEmpty", "()Z");
    jmethodID java_util_LinkedList_remove = env->GetMethodID(java_util_LinkedList, "remove", "()Ljava/lang/Object;");

    jobject jitAVLQueue = env->NewObject(java_util_LinkedList, java_util_LinkedList_init);

    jobject rootNode = env->NewObject(java_lang_Long, java_lang_Long_init, (jlong)jitConfig->translationArtifacts->rootNode);
    env->CallBooleanMethod(jitAVLQueue, java_util_LinkedList_add, rootNode);
    env->DeleteLocalRef(rootNode);

    jboolean jitAVLQueueIsEmpty = env->CallBooleanMethod(jitAVLQueue, java_util_LinkedList_isEmpty);
    while (jitAVLQueueIsEmpty != JNI_TRUE)
        {
        jobject nodeObject = env->CallObjectMethod(jitAVLQueue, java_util_LinkedList_remove);
        J9AVLTreeNode *node = (J9AVLTreeNode *)env->CallLongMethod(nodeObject, java_lang_Long_longValue);
        env->DeleteLocalRef(nodeObject);

        if (NULL != node)
            {
            jobject leftChild = env->NewObject(java_lang_Long, java_lang_Long_init, (jlong)J9AVLTREENODE_LEFTCHILD(node));
            jobject rightChild = env->NewObject(java_lang_Long, java_lang_Long_init, (jlong)J9AVLTREENODE_RIGHTCHILD(node));
            env->CallBooleanMethod(jitAVLQueue, java_util_LinkedList_add, leftChild);
            env->CallBooleanMethod(jitAVLQueue, java_util_LinkedList_add, rightChild);


            J9JITHashTableWalkState state;
            J9JITExceptionTable* metadata = hash_jit_start_do(&state, reinterpret_cast<J9JITHashTable*>(node));
            while (NULL != metadata)
                {
                jobject jitMethod = env->NewObject(java_lang_Long, java_lang_Long_init, (jlong)metadata);
                env->CallBooleanMethod(jitMethodSet, java_util_HashSet_add, jitMethod);
                env->DeleteLocalRef(jitMethod);
                
                metadata = hash_jit_next_do(&state);
                }

            env->DeleteLocalRef(leftChild);
            env->DeleteLocalRef(rightChild);
            }

        jitAVLQueueIsEmpty = env->CallBooleanMethod(jitAVLQueue, java_util_LinkedList_isEmpty);
        }

    env->DeleteLocalRef(java_lang_Long);
    env->DeleteLocalRef(java_util_HashSet);
    env->DeleteLocalRef(java_util_LinkedList);
    env->DeleteLocalRef(jitAVLQueue);

    return true;
    }

BOOLEAN
debugAgentRevertToInterpreter(J9VMThread* vmThread, J9JITExceptionTable *jitMethod)
    {
    J9JITConfig *jitConfig = vmThread->javaVM->jitConfig;
    if (NULL == jitConfig)
        {
        fprintf(stderr, "Could not locate J9JITConfig\n");
        return false;
        }
        
    TR::CompilationInfo *compInfo = TR::CompilationInfo::get(jitConfig);
    if (NULL == compInfo)
        {
        fprintf(stderr, "Could not locate TR::CompilationInfo\n");
        return false;
        }
        
    TR_J9VMBase *frontendOfThread = TR_J9VMBase::get(jitConfig, vmThread);
    if (NULL == frontendOfThread)
        {
        fprintf(stderr, "Could not locate TR_J9VMBase\n");
        return false;
        }

    TR_PersistentJittedBodyInfo *bodyInfo = reinterpret_cast<TR_PersistentJittedBodyInfo *>(jitMethod->bodyInfo);
    if (NULL == bodyInfo)
        {
        fprintf(stderr, "Could not locate persistent body info for JIT method %p\n", jitMethod);
        return false;
        }
    
    PORT_ACCESS_FROM_VMC(vmThread);
    J9Class *clazz = J9_CLASS_FROM_METHOD(jitMethod->ramMethod);
    J9ROMMethod *romMethod = J9_ROM_METHOD_FROM_RAM_METHOD(jitMethod->ramMethod);
    J9UTF8 *methName = J9ROMMETHOD_NAME(romMethod);
    J9UTF8 *methSig = J9ROMMETHOD_SIGNATURE(romMethod);
    J9UTF8 *className = J9ROMCLASS_CLASSNAME(clazz->romClass);

    void *pc = compInfo->getPCIfCompiled(jitMethod->ramMethod);
    int lengthOfSig = (int)J9UTF8_LENGTH(className) + (int)J9UTF8_LENGTH(methName) + (int)J9UTF8_LENGTH(methSig);
    char m[lengthOfSig+1];
    sprintf(m,"%.*s.%.*s%.*s",
        (int)J9UTF8_LENGTH(className), J9UTF8_DATA(className),
        (int)J9UTF8_LENGTH(methName), J9UTF8_DATA(methName),
        (int)J9UTF8_LENGTH(methSig), J9UTF8_DATA(methSig));
    
    char s[218] ="javasoft/sqe/tests/api/java/util/stream/Stream/StreamAssert.checkElementsRegardingOrder(Ljava/lang/Iterable;Ljava/util/Iterator;Ljavasoft/sqe/tests/api/java/util/stream/Stream/ComparisonProperties;Ljava/lang/String;)V";
    
    if (pc != NULL && (strncmp(s, m, lengthOfSig) != 0))
        {
        char str[]
        fprintf(stderr, "Invalidating PC = %p %.*s.%.*s%.*s, isAOT = %s\n", pc,
            (int)J9UTF8_LENGTH(className), J9UTF8_DATA(className),
            (int)J9UTF8_LENGTH(methName), J9UTF8_DATA(methName),
            (int)J9UTF8_LENGTH(methSig), J9UTF8_DATA(methSig), bodyInfo->getIsAotedBody() ? "true" : "false");
        }
    else
        {
        fprintf(stderr, "Cannot invalidate method because PC == NULL %.*s.%.*s%.*s\n",
            (int)J9UTF8_LENGTH(className), J9UTF8_DATA(className),
            (int)J9UTF8_LENGTH(methName), J9UTF8_DATA(methName),
            (int)J9UTF8_LENGTH(methSig), J9UTF8_DATA(methSig));
        
        return false;
        }

    TR::Recompilation::methodCannotBeRecompiled(pc, frontendOfThread);

    return true;
    }

extern J9_CFUNC BOOLEAN
debugAgentRecompile(J9VMThread* vmThread, J9JITExceptionTable *jitMethod, IDATA lastOptIndex, IDATA lastOptSubIndex, BOOLEAN enableTracing, BOOLEAN goodLog)
    {
    J9JITConfig *jitConfig = vmThread->javaVM->jitConfig;
    if (NULL == jitConfig)
        {
        fprintf(stderr, "Could not locate J9JITConfig\n");
        return false;
        }
        
    TR::CompilationInfo *compInfo = TR::CompilationInfo::get(jitConfig);
    if (NULL == compInfo)
        {
        fprintf(stderr, "Could not locate TR::CompilationInfo\n");
        return false;
        }
        
    TR_J9VMBase *frontendOfThread = TR_J9VMBase::get(jitConfig, vmThread);
    if (NULL == frontendOfThread)
        {
        fprintf(stderr, "Could not locate TR_J9VMBase\n");
        return false;
        }

    TR_PersistentJittedBodyInfo *bodyInfo = reinterpret_cast<TR_PersistentJittedBodyInfo *>(jitMethod->bodyInfo);
    if (NULL == bodyInfo)
        {
        fprintf(stderr, "Could not locate persistent body info for JIT method %p\n", jitMethod);
        return false;
        }
        
    PORT_ACCESS_FROM_VMC(vmThread);
    J9Class *clazz = J9_CLASS_FROM_METHOD(jitMethod->ramMethod);
    J9ROMMethod *romMethod = J9_ROM_METHOD_FROM_RAM_METHOD(jitMethod->ramMethod);
    J9UTF8 *methName = J9ROMMETHOD_NAME(romMethod);
    J9UTF8 *methSig = J9ROMMETHOD_SIGNATURE(romMethod);
    J9UTF8 *className = J9ROMCLASS_CLASSNAME(clazz->romClass);

    void *pc = compInfo->getPCIfCompiled(jitMethod->ramMethod);
    fprintf(stderr, "Recompiling PC = %p lastOptIndex = %d lastOptSubIndex = %d %.*s.%.*s%.*s\n", pc, (int)lastOptIndex, (int)lastOptSubIndex, 
        (int)J9UTF8_LENGTH(className), J9UTF8_DATA(className),
        (int)J9UTF8_LENGTH(methName), J9UTF8_DATA(methName),
        (int)J9UTF8_LENGTH(methSig), J9UTF8_DATA(methSig));

    // The request to use a trace log gets passed to the compilation via the optimization plan. The options object
    // created before the compile is issued will use the trace log we provide to initialize IL tracing.
    TR_OptimizationPlan *plan = TR_OptimizationPlan::alloc(bodyInfo->getHotness());
    if (NULL == plan)
        {
        j9nls_printf(PORTLIB, J9NLS_INFO | J9NLS_STDERR, J9NLS_DMP_JIT_OPTIMIZATION_PLAN);
        return false;
        }

    plan->setInsertInstrumentation(bodyInfo->getIsProfilingBody());

    char *fileName = "goodJitCompilationLog_opt_index_";
    if (!goodLog)
    {
        fileName = "badJitCompilationLog_opt_index_";
    }
    // Ref: https://github.com/eclipse-openj9/openj9-omr/blob/openj9/compiler/ras/Tree.cpp#L1168
    int numDigits = ( lastOptIndex == 0 ? 1 : ((int) log10( (double)lastOptIndex ) + 1) );
    int maxSize = strlen(fileName) + numDigits + 5;
    char fileNameWithLastOptIndex[maxSize];
    snprintf(fileNameWithLastOptIndex, maxSize, "%s%d.log", fileName, (int)lastOptIndex);
    TR::FILE *jitCompilationLog = enableTracing ? trfopen(fileNameWithLastOptIndex, "ab", false) : NULL;
    if (enableTracing)
    {
        plan->setLogCompilation(jitCompilationLog);
        TR::Options::getCmdLineOptions()->setOption(TR_TraceAll);
    }

    TR::Options::getCmdLineOptions()->setLastOptIndex(lastOptIndex);
    TR::Options::getCmdLineOptions()->setLastOptSubIndex(lastOptSubIndex);

    // This API is meant to be called from within JNI so we must acquire VM access here before queuing the compilation
    // beacuse we will attempt to release VM access right before a synchronous compilation
    vmThread->javaVM->internalVMFunctions->internalAcquireVMAccess(vmThread);

    J9::JitDumpMethodDetails details(jitMethod->ramMethod, NULL, bodyInfo->getIsAotedBody());
    auto rc = compilationOK;
    auto queued = false;
    compInfo->compileMethod(vmThread, details, pc, TR_no, &rc, &queued, plan);
    if (enableTracing)
    {
        trfflush(jitCompilationLog);
        trfclose(jitCompilationLog);
    }

    vmThread->javaVM->internalVMFunctions->internalReleaseVMAccess(vmThread);

    return true;
    }

BOOLEAN
debugAgentEnd(J9VMThread* vmThread)
    {
    J9JITConfig *jitConfig = vmThread->javaVM->jitConfig;
    if (NULL == jitConfig)
        {
        fprintf(stderr, "Could not locate J9JITConfig\n");
        return false;
        }
        
    TR::CompilationInfo *compInfo = TR::CompilationInfo::get(jitConfig);
    if (NULL == compInfo)
        {
        fprintf(stderr, "Could not locate TR::CompilationInfo\n");
        return false;
        }

    compInfo->getPersistentInfo()->setDisableFurtherCompilation(false);

    compInfo->getCompilationInfoForDiagnosticThread()->suspendCompilationThread();
    return true;
    }
