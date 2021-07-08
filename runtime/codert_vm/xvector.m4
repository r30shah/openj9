dnl Copyright IBM Corp. and others 2021
dnl
dnl This program and the accompanying materials are made available under
dnl the terms of the Eclipse Public License 2.0 which accompanies this
dnl distribution and is available at https://www.eclipse.org/legal/epl-2.0/
dnl or the Apache License, Version 2.0 which accompanies this distribution and
dnl is available at https://www.apache.org/licenses/LICENSE-2.0.
dnl
dnl This Source Code may also be made available under the following
dnl Secondary Licenses when the conditions for such availability set
dnl forth in the Eclipse Public License, v. 2.0 are satisfied: GNU
dnl General Public License, version 2 with the GNU Classpath
dnl Exception [1] and GNU General Public License, version 2 with the
dnl OpenJDK Assembly Exception [2].
dnl
dnl [1] https://www.gnu.org/software/classpath/license.html
dnl [2] https://openjdk.org/legal/assembly-exception.html
dnl
dnl SPDX-License-Identifier: EPL-2.0 OR Apache-2.0 OR GPL-2.0-only WITH Classpath-exception-2.0 OR GPL-2.0-only WITH OpenJDK-assembly-exception-1.0

include(xhelpers.m4)

	FILE_START

dnl The functions herein only apply to 64-bit targets.
dnl
dnl Assumptions on entry to each of these functions:
dnl 1) the return address is on top of the stack
dnl 2) register r8 is available as a scratch register

START_PROC(jitSaveVectorRegistersAVX512)
	dnl lfence prevents CPU throttling penalty caused by speculative execution of AVX-512 instructions
	lfence

	dnl save ZMM registers
	pop r8
	forloop({REG_CTR}, 0, 31, {SAVE_ZMM_REG(REG_CTR, J9TR_cframe_jitFPRs+(REG_CTR*64))})

	dnl vzeroupper is recommended when transitioning between AVX and SSE code to eliminate performance penalties caused by false dependencies
	vzeroupper

	dnl save Opmask registers
	forloop({REG_CTR}, 0, 7, {SAVE_MASK_64(REG_CTR, J9TR_cframe_maskRegisters+(REG_CTR*8))})

	push r8
	ret
END_PROC(jitSaveVectorRegistersAVX512)

START_PROC(jitRestoreVectorRegistersAVX512)
	lfence

	dnl restore ZMM registers
	pop r8
	forloop({REG_CTR}, 0, 31, {RESTORE_ZMM_REG(REG_CTR, J9TR_cframe_jitFPRs+(REG_CTR*64))})

	dnl restore Opmask registers
	forloop({REG_CTR}, 0, 7, {RESTORE_MASK_64(REG_CTR, J9TR_cframe_maskRegisters+(REG_CTR*8))})

	push r8
	ret
END_PROC(jitRestoreVectorRegistersAVX512)

START_PROC(jitSaveVectorRegistersAVX)
	dnl lfence prevents CPU throttling penalty caused by speculative execution of AVX-512 instructions
	lfence

	dnl save YMM registers
	pop r8
	forloop({REG_CTR}, 0, 15, {vmovdqu ymmword ptr J9TR_cframe_jitFPRs+(REG_CTR*32)[_rsp],ymm{}REG_CTR})

	dnl vzeroupper is recommended when transitioning between AVX and SSE code to eliminate performance penalties caused by false dependencies
	vzeroupper

	push r8
	ret
END_PROC(jitSaveVectorRegistersAVX)

START_PROC(jitRestoreVectorRegistersAVX)
	lfence

	dnl restore YMM registers
	pop r8
	forloop({REG_CTR}, 0, 15, {vmovdqu ymm{}REG_CTR,ymmword ptr J9TR_cframe_jitFPRs+(REG_CTR*32)[_rsp]})

	push r8
	ret
END_PROC(jitRestoreVectorRegistersAVX)

	FILE_END
