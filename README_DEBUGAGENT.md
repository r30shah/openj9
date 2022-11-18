<!--
Copyright (c) 2017, 2021 IBM Corp. and others

This program and the accompanying materials are made available under
the terms of the Eclipse Public License 2.0 which accompanies this
distribution and is available at https://www.eclipse.org/legal/epl-2.0/
or the Apache License, Version 2.0 which accompanies this distribution and
is available at https://www.apache.org/licenses/LICENSE-2.0.

This Source Code may also be made available under the following
Secondary Licenses when the conditions for such availability set
forth in the Eclipse Public License, v. 2.0 are satisfied: GNU
General Public License, version 2 with the GNU Classpath
Exception [1] and GNU General Public License, version 2 with the
OpenJDK Assembly Exception [2].

[1] https://www.gnu.org/software/classpath/license.html
[2] http://openjdk.java.net/legal/assembly-exception.html

SPDX-License-Identifier: EPL-2.0 OR Apache-2.0 OR GPL-2.0 WITH Classpath-exception-2.0 OR LicenseRef-GPL-2.0 WITH Assembly-exception
-->
OpenJ9 JIT Debug Agent
========================================

This tool semi-automatically obtains a limited JIT trace log for a miscompiled method. It works by using preexistence
and a hooked internal API to repeatedly run a test by sequentially reverting JIT methods to be executed in the interpreter.
By repeatedly executing a test in a controlled environment we are able to devertmine which JIT method needs to be interpreted
for the test to start passing. This is how the tool determines which JIT method _may_ be responsible for the test case failure.

Once the JIT method is identified the tool performs a `lastOptIndex` search by recompiling the JIT method at different
optimization levels. Once again, when the test starts passing we have determined the minimal `lastOptIndex` which causes the
failure. At that point the tool gather a _"good"_ and _"bad"_ JIT trace log with the optimization included and excluded for
JIT developers to investigate.

# When to use this tool

This tool should be used for highly intermittent JIT defects from automated testing environments where we are either not able
to determine the JIT method responsible for the failure, or we are unable to trace the suspect JIT method due to a Heisenbug.

# How to use this tool

Using the tool currently requires a bit of a setup.

1. Find an injection point into the test framework.

    Typically test frameworks work via reflection to call stateless tests. More often than not the injection point for triggering
    this tool will be the `java/lang/reflect/Method.invoke` API. We hook this API by changing the original implementation to
    forward the call to our own custom `JITHelpers` method which implements this tool:

    ```
    public Object invoke(Object obj, Object... args)
        throws IllegalAccessException, IllegalArgumentException,
           InvocationTargetException
    {
        if (!override) {
            if (!Reflection.quickCheckMemberAccess(clazz, modifiers)) {
                Class<?> caller = Reflection.getCallerClass();
                checkAccess(caller, clazz, obj, modifiers);
            }
        }
        MethodAccessor ma = methodAccessor;             // read volatile
        if (ma == null) {
            ma = acquireMethodAccessor();
        }
        return com.ibm.jit.JITHelpers.invoke(ma, obj, args);
    }
    ```

2. Change the exception name inside of `com/ibm/jit/JITHelpers.invoke`

    Currently the tool is configured to execute the target method and if an `InvocationTargetException` is caught and the exception
    type is `java.lang.AssertionError` then the exception is likely because of a test case failure, a JUnit or TestNG assertion in
    this case. The particular exception you may want to catch may be different.

3. Run the test by forcing preexistence.

    Currently the tool is not robust enough to enable this automatically, so we have to force every JIT method compilation to use
    preexistence. This is to ensure that we have a _revert to interpreter_ stub inserted in the preprologue of every method.
    Inserting this stub happens at binary encoding and should not affect the semantics of the method itself.

    ```
    java -Xdump:none -Xnoaot -Xcheck:jni -Xjit:forceUsePreexistence <test>
    ```

# Example run

While developing the tool [Problem Report 142445](https://jazz103.hursley.ibm.com:9443/jazz/web/projects/JTC-JAT#action=com.ibm.team.workitem.viewWorkItem&id=142445) 
was used as an example defect for which one may use this tool. This particular defect was an assertion error that a result
was not computed correctly. It also happen to be intermittent at the time, however a unit test was later developed for the
failure. We packaged up the unit test into a testing bucket and used this tool to generate a JIT trace log showing the issue.
However one does not need to create a unit test to run this tool. This tool could have been run on the actual test bucket
as one normally would via a grinder to produce the same output.

DebugAgentRunner.java

```
import org.junit.runner.Description;
import org.junit.runner.JUnitCore;
import org.junit.runner.Request;
import org.junit.runner.Result;
import org.junit.runner.manipulation.Filter;
import org.junit.runner.notification.Failure;
import org.junit.runner.notification.RunListener;

public class DebugAgentRunner
{
    public static void main(String[] args)
	{
        for (int i = 0; i < Integer.parseInt(args[0]); ++i) {
            Result result = JUnitCore.runClasses(DebugAgentTest.class);
            for (Failure failure : result.getFailures()) {
                System.out.println(failure.toString());
            }
        }
    }
}
```

DebugAgentTest.java

```
import static org.junit.Assert.*;
import org.junit.Test;
import org.junit.Assert;
import java.math.*;

public class DebugAgentTest
{
	@Test
	public void testConstrDoubleMinus01()
	{
		double a = -1.E-1;
		int aScale = 55;
		BigInteger bA = new BigInteger("-1000000000000000055511151231257827021181583404541015625");
		BigDecimal aNumber = new BigDecimal(a);
		assertEquals("Incorrect result!", bA, aNumber.unscaledValue());
	}
}
```

Compile the test and run it which kicks the debug agent into action:

```
./build/linux-s390x-normal-server-release/images/j2sdk-image/bin/javac -J-Xint -cp ./junit.jar DebugAgentTest.java DebugAgentRunner.java
./build/linux-s390x-normal-server-release/images/j2sdk-image/bin/java -cp ./junit.jar:./hamcrest-all-1.3.jar:. -Xdump:none -Xnoaot -Xcheck:jni -Xjit:forceUsePreexistence DebugAgentRunner 50000
```

Output:

```
JVMJNCK001I JNI check utility installed. Use -Xcheck:jni:help for usage
Caught org.opentest4j.AssertionFailedError inside JITHelpers
Total number of JIT methods in HashSet = 503
Could not locate persistent body info for JIT method 0x3ff5e87f178
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff649498f4 java/util/Formatter$FormatSpecifier.width(Ljava/lang/String;)I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6494c0f6 java/lang/CharacterDataLatin1.getType(I)I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6453d8f4 java/util/LinkedHashMap$LinkedKeySet.<init>(Ljava/util/LinkedHashMap;)V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6492fcfa java/lang/Class.copyFields([Ljava/lang/reflect/Field;)[Ljava/lang/reflect/Field;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64730bfa org/junit/runners/model/TestClass.getName()Ljava/lang/String;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64737bf0 java/util/concurrent/ConcurrentHashMap.addCount(JI)V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff649363f4 java/util/Formatter$FormatSpecifier.checkBadFlags([Ljava/util/Formatter$Flags;)V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6493c4fa java/lang/String.toCharArray()[C
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6472e0ee java/util/HashMap.put(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff647270fa org/junit/runners/ParentRunner.classRules()Ljava/util/List;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff649294fa java/lang/StringBuilder.length()I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64335afa java/lang/reflect/AccessibleObject.getAnnotations()[Ljava/lang/annotation/Annotation;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff643365fa java/util/regex/Matcher.reset()Ljava/util/regex/Matcher;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff645346fa java/util/Arrays$ArrayList.size()I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64538afa java/lang/reflect/Method.getReturnType()Ljava/lang/Class;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff641376f2 java/lang/Class.getMethodHelper(ZZLjava/util/List;Ljava/lang/String;[Ljava/lang/Class;)Ljava/lang/reflect/Method;
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e882578
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e880578
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff643304fa java/util/ArrayList$Itr.hasNext()Z
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff645270fa java/lang/Class.getTypeName()Ljava/lang/String;
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e883d78
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e881178
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6432cff4 java/lang/StringBuilder.append(Ljava/lang/String;)Ljava/lang/StringBuilder;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6432dafa java/lang/J9VMInternals.fastIdentityHashCode(Ljava/lang/Object;)I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6413acf4 com/ibm/jit/JITHelpers.getJ9ClassFromObject64(Ljava/lang/Object;)J
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e87f538
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6433c0fa java/util/concurrent/locks/ReentrantLock.unlock()V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6473e9fc java/lang/Character.getType(I)I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff647416f4 org/junit/runners/ParentRunner.run(Lorg/junit/runner/notification/RunNotifier;)V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64947eee java/util/Formatter.format(Ljava/util/Locale;Ljava/lang/String;[Ljava/lang/Object;)Ljava/util/Formatter;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff649506fa org/junit/internal/runners/model/ReflectiveCallable.run()Ljava/lang/Object;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff649535f0 java/math/Multiplication.square([II[I)[I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6453e3fa java/util/Formatter.ensureOpen()V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6453fefc java/util/Formatter$Conversion.isText(C)Z
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff645401fa java/util/regex/Matcher.end()I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff649391fa java/util/Collections.unmodifiableCollection(Ljava/util/Collection;)Ljava/util/Collection;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64738ffa com/sun/proxy/$Proxy1.annotationType()Ljava/lang/Class;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6493b9fa java/util/AbstractList.iterator()Ljava/util/Iterator;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6493d7f2 java/math/BigInteger.<init>(II[I)V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64939efa java/lang/Class.isMemberClass()Z
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6473a3f4 org/junit/runners/ParentRunner.<init>(Ljava/lang/Class;)V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff649372f4 org/junit/runners/model/FrameworkMethod.getAnnotation(Ljava/lang/Class;)Ljava/lang/annotation/Annotation;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff649369f4 java/util/Formatter$FormatSpecifier.justify(Ljava/lang/String;)Ljava/lang/String;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff647292fa java/util/regex/Matcher.groupCount()I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6472b4fa org/junit/runners/ParentRunner.getFilteredChildren()Ljava/util/Collection;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff643383f4 java/util/ArrayList.addAll(Ljava/util/Collection;)Z
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6452d0f2 java/lang/String.substring(II)Ljava/lang/String;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64532af0 java/math/Multiplication.multiplyByInt([I[III)I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64534af4 java/util/Collections$EmptySet.toArray([Ljava/lang/Object;)[Ljava/lang/Object;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64534ff4 java/util/LinkedHashMap$LinkedHashIterator.<init>(Ljava/util/LinkedHashMap;)V
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e884138
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e880938
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff641305f2 java/lang/String.replace(CC)Ljava/lang/String;
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e881538
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff643301fa java/util/Collections$UnmodifiableCollection.iterator()Ljava/util/Iterator;
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e882938
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6413a3f4 java/util/HashMap.get(Ljava/lang/Object;)Ljava/lang/Object;
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e87fdf8
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6473c3fa org/junit/runners/model/TestClass.getOnlyConstructor()Ljava/lang/reflect/Constructor;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff647425ee org/junit/runners/BlockJUnit4ClassRunner.withMethodRules(Lorg/junit/runners/model/FrameworkMethod;Ljava/util/List;Ljava/lang/Object;Lorg/junit/runners/model/Statement;)Lorg/junit/runners/model/Statement;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6433b5f4 java/lang/Class.cast(Ljava/lang/Object;)Ljava/lang/Object;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64730800 java/util/Arrays$LegacyMergeSort.access$000()Z
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6492d4fa java/util/LinkedHashMap.values()Ljava/util/Collection;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6492cefa java/lang/String.toString()Ljava/lang/String;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6493e9fa java/util/HashMap.size()I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6493f3f6 sun/reflect/Reflection.quickCheckMemberAccess(Ljava/lang/Class;I)Z
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff647329f4 java/util/LinkedHashMap$LinkedEntrySet.<init>(Ljava/util/LinkedHashMap;)V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6453b8fa java/util/concurrent/CopyOnWriteArrayList.iterator()Ljava/util/Iterator;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64934ef8 java/util/regex/ASCII.isType(II)Z
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64927ef4 org/junit/runners/model/TestClass.getAnnotatedFields(Ljava/lang/Class;)Ljava/util/List;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6472f8fa java/util/concurrent/ConcurrentLinkedQueue.<init>()V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6413d6fa java/lang/StringBuilder.toString()Ljava/lang/String;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6413ddf6 java/lang/StringBuilder.<init>(I)V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6492caf6 java/util/regex/Matcher.search(I)Z
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6492a0f4 org/junit/validator/AnnotationsValidator$AnnotatableValidator.validateTestClass(Lorg/junit/runners/model/TestClass;)Ljava/util/List;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff645303fa java/util/Collections$EmptyList.iterator()Ljava/util/Iterator;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff645391fa java/util/LinkedHashMap.<init>()V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64539bee org/junit/runner/Description.<init>(Ljava/lang/Class;Ljava/lang/String;Ljava/io/Serializable;[Ljava/lang/annotation/Annotation;)V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6432eefa java/util/Collections$UnmodifiableCollection$1.hasNext()Z
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6412ddf6 java/lang/String.charAt(I)C
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6413a0f0 java/lang/String.decompressedArrayCopy([CI[CII)V
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e881df8
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e8865f8
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff641370f6 java/io/ByteArrayOutputStream.ensureCapacity(I)V
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e8855f8
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff643313f4 java/util/HashMap.containsKey(Ljava/lang/Object;)Z
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6452c3f0 org/junit/runners/model/TestClass.getAnnotatedMembers(Ljava/util/Map;Ljava/lang/Class;Z)Ljava/util/List;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6452b1fa java/lang/reflect/Executable.declaredAnnotations()Ljava/util/Map;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6452abee org/junit/internal/MethodSorter$1.compare(Ljava/lang/reflect/Method;Ljava/lang/reflect/Method;)I
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e8835f8
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff647433f4 org/junit/runners/ParentRunner.withBeforeClasses(Lorg/junit/runners/model/Statement;)Lorg/junit/runners/model/Statement;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64741df4 org/junit/runners/ParentRunner.classBlock(Lorg/junit/runner/notification/RunNotifier;)Lorg/junit/runners/model/Statement;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64742ef6 java/math/Multiplication.pow(Ljava/math/BigInteger;I)Ljava/math/BigInteger;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6473c1ee org/junit/Assert.assertEquals(Ljava/lang/String;JJ)V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6473c9f2 java/util/HashSet.<init>(IFZ)V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6494e5ee java/util/Formatter$FixedString.print(Ljava/lang/Object;Ljava/util/Locale;)V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6453f5fc java/util/Formatter$Conversion.isValid(C)Z
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e8a39b8
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff647315f6 java/util/regex/Pattern$Single.isSatisfiedBy(I)Z
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6453bdf4 java/math/BigInteger.equalsArrays([I)Z
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff647373f6 java/util/concurrent/locks/AbstractQueuedSynchronizer.release(I)Z
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6493e0fc java/lang/Character.charCount(I)I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff649301f4 org/junit/runners/model/RunnerBuilder.runners([Ljava/lang/Class;)Ljava/util/List;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff649324f4 org/junit/runners/model/TestClass.collectValues(Ljava/util/Map;)Ljava/util/List;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff649354f4 org/junit/runners/BlockJUnit4ClassRunner.describeChild(Lorg/junit/runners/model/FrameworkMethod;)Lorg/junit/runner/Description;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff649397f4 java/lang/Object.equals(Ljava/lang/Object;)Z
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6493ecf6 java/util/Formatter$Flags.<init>(I)V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6472fbfa java/util/Collections$UnmodifiableCollection.isEmpty()Z
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6472bbfa java/util/HashMap.resize()[Ljava/util/HashMap$Node;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff649284f2 java/math/BigInteger.<init>(II)V
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff645360f4 java/math/Multiplication.karatsuba(Ljava/math/BigInteger;Ljava/math/BigInteger;)Ljava/math/BigInteger;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff645366f4 java/lang/Class$ReflectCache.find(Ljava/lang/Class$CacheKey;)Ljava/lang/Object;
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e8801b8
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6432e4f6 java/lang/CharacterDataLatin1.getProperties(I)I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff641357fa java/lang/String.hashCode()I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff641361f4 sun/misc/ProxyGenerator$ConstantPool.getIndirect(Lsun/misc/ProxyGenerator$ConstantPool$IndirectEntry;)S
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e8851b8
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6432a2fa java/util/HashMap.hash(Ljava/lang/Object;)I
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e8821b8
Rerunning test
Caught exception after invoking test
Could not locate persistent body info for JIT method 0x3ff5e8839b8
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6432caee com/ibm/jit/JITHelpers.getIntFromObject(Ljava/lang/Object;J)I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6432e1fa java/lang/reflect/Method.getName()Ljava/lang/String;
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff64944af2 java/util/TimSort.countRunAndMakeAscending([Ljava/lang/Object;IILjava/util/Comparator;)I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff6494e4fa java/util/Formatter$FixedString.index()I
Rerunning test
Caught exception after invoking test
Invalidating PC = 0x3ff649523f0 java/math/BigDecimal.<init>(DLjava/math/MathContext;)V
Rerunning test
Identified problematic method
Recompiling PC = 0x3ff649523f0 lastOptIndex = 100 lastOptSubIndex = 1024 java/math/BigDecimal.<init>(DLjava/math/MathContext;)V
Rerunning test
Caught exception after invoking test with lastOptIndex = 100
Recompiling PC = 0x3ff64953df0 lastOptIndex = 99 lastOptSubIndex = 1024 java/math/BigDecimal.<init>(DLjava/math/MathContext;)V
Rerunning test
Caught exception after invoking test with lastOptIndex = 99
Recompiling PC = 0x3ff649564f0 lastOptIndex = 98 lastOptSubIndex = 1024 java/math/BigDecimal.<init>(DLjava/math/MathContext;)V
Rerunning test
Caught exception after invoking test with lastOptIndex = 98
Recompiling PC = 0x3ff64958bf0 lastOptIndex = 97 lastOptSubIndex = 1024 java/math/BigDecimal.<init>(DLjava/math/MathContext;)V
Rerunning test
Caught exception after invoking test with lastOptIndex = 97
Recompiling PC = 0x3ff6495b2f0 lastOptIndex = 96 lastOptSubIndex = 1024 java/math/BigDecimal.<init>(DLjava/math/MathContext;)V
JVMDUMP052I JIT dump recursive crash occurred on diagnostic thread
Rerunning test
LastOptIndex = 97 is the potential culprit
Recompiling PC = 0x3ff6495b2f0 lastOptIndex = 96 lastOptSubIndex = 1024 java/math/BigDecimal.<init>(DLjava/math/MathContext;)V
JVMDUMP052I JIT dump recursive crash occurred on diagnostic thread
Rerunning test expecting it to pass
Test passed
Recompiling PC = 0x3ff6495b2f0 lastOptIndex = 97 lastOptSubIndex = 1024 java/math/BigDecimal.<init>(DLjava/math/MathContext;)V
Rerunning test expecting it to fail
Test failed
Aborting JVM
```

From the output we see that `java/math/BigDecimal.<init>(DLjava/math/MathContext;)V` was identified as the method which
causes the `java.lang.AssertionError` exception to be thrown, and `lastOptIndex=96` was the cause of the problem. The JIT
trace file which is collected clearly shows the issue right at the end of the log which is easily identified by comparing
the _"good"_ and _"bad"_ logs generated:

```
------------------------------
 n1540n   (  0)  lRegStore GPR6                                                                       [     0x3ff5451d110] bci=[-1,38,459] rc=0 vc=1593 vn=- li=105 udi=- nc=1
 n1541n   (  3)    land (X>=0 cannotOverflow )                                                        [     0x3ff5451d160] bci=[-1,37,459] rc=3 vc=1593 vn=- li=105 udi=- nc=2 flg=0x1100
 n1181n   (  0)      ==>dbits2l (in GPR_0081)
 n1542n   (  1)      lconst 0xfffffffffffff (X!=0 X>=0 )                                              [     0x3ff5451d1b0] bci=[-1,34,459] rc=1 vc=1593 vn=- li=105 udi=- nc=0 flg=0x104
------------------------------
[000003FF5451D160] land => rotated-and-insert: tZeros 0, lZeros 12, popCnt 52
          => rotated-and-insert: lOnes 0, tOnes 52
------------------------------
 n1540n   (  0)  lRegStore GPR6                                                                       [     0x3ff5451d110] bci=[-1,38,459] rc=0 vc=1593 vn=- li=105 udi=- nc=1
 n1541n   (  2)    land (in GPR_0081) (X>=0 cannotOverflow )                                          [     0x3ff5451d160] bci=[-1,37,459] rc=2 vc=1593 vn=- li=105 udi=- nc=2 flg=0x1100
 n1181n   ( -1)      ==>dbits2l (in GPR_0081)
 n1542n   (  0)      lconst 0xfffffffffffff (X!=0 X>=0 )                                              [     0x3ff5451d1b0] bci=[-1,34,459] rc=0 vc=1593 vn=- li=105 udi=- nc=0 flg=0x104
------------------------------

 [     0x3ff547b4640]                          NIHH    GPR_0081,0xf
 ```

 In particular the `dbits2l` node decrements the reference count below zero which causes all sorts of problems. The fix
 for the issue was merged in [eclipse/omr#4427](https://github.com/eclipse/omr/pull/4427).
