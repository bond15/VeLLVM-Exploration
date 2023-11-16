	.text
	.file	"test1.c"
	.globl	main                            # -- Begin function main
	.p2align	4, 0x90
	.type	main,@function
main:                                   # @main
	.cfi_startproc
# %bb.0:
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset %rbp, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register %rbp
	subq	$128, %rsp
	xorl	%esi, %esi
	movabsq	$.L__const.main.A, %rax
	movl	$0, -4(%rbp)
	leaq	-48(%rbp), %rcx
	movq	%rcx, %rdi
	movl	%esi, -108(%rbp)                # 4-byte Spill
	movq	%rax, %rsi
	movl	$40, %eax
	movq	%rax, %rdx
	movq	%rax, -120(%rbp)                # 8-byte Spill
	callq	memcpy
	leaq	-96(%rbp), %rax
	movq	%rax, %rdi
	movl	-108(%rbp), %esi                # 4-byte Reload
	movq	-120(%rbp), %rdx                # 8-byte Reload
	callq	memset
	movl	$0, -104(%rbp)
	movl	$0, -100(%rbp)
.LBB0_1:                                # =>This Inner Loop Header: Depth=1
	cmpl	$10, -100(%rbp)
	jge	.LBB0_6
# %bb.2:                                #   in Loop: Header=BB0_1 Depth=1
	movslq	-104(%rbp), %rax
	imull	$11, -48(%rbp,%rax,4), %ecx
	addl	-100(%rbp), %ecx
	movslq	-100(%rbp), %rax
	movl	%ecx, -96(%rbp,%rax,4)
	cmpl	$8, -100(%rbp)
	jge	.LBB0_4
# %bb.3:                                #   in Loop: Header=BB0_1 Depth=1
	movl	-100(%rbp), %eax
	movl	%eax, -104(%rbp)
.LBB0_4:                                #   in Loop: Header=BB0_1 Depth=1
	jmp	.LBB0_5
.LBB0_5:                                #   in Loop: Header=BB0_1 Depth=1
	movl	-100(%rbp), %eax
	addl	$1, %eax
	movl	%eax, -100(%rbp)
	jmp	.LBB0_1
.LBB0_6:
	xorl	%eax, %eax
	addq	$128, %rsp
	popq	%rbp
	.cfi_def_cfa %rsp, 8
	retq
.Lfunc_end0:
	.size	main, .Lfunc_end0-main
	.cfi_endproc
                                        # -- End function
	.type	.L__const.main.A,@object        # @__const.main.A
	.section	.rodata,"a",@progbits
	.p2align	4
.L__const.main.A:
	.long	0                               # 0x0
	.long	1                               # 0x1
	.long	2                               # 0x2
	.long	3                               # 0x3
	.long	4                               # 0x4
	.long	5                               # 0x5
	.long	6                               # 0x6
	.long	7                               # 0x7
	.long	8                               # 0x8
	.long	9                               # 0x9
	.size	.L__const.main.A, 40

	.ident	"Debian clang version 11.0.1-2"
	.section	".note.GNU-stack","",@progbits
	.addrsig
