	.text	0x00400000
	.globl	main
main:
	la	$28, _heap_
	ori	$2, $0, 5
# was:	ori	2, 0, 5
	syscall
# 	ori	_apply__19_,2,0
# 	ori	2,_apply__19_,0
	jal	fib
# was:	jal	fib, 2
# 	ori	dead,2,0
	ori	$4, $2, 0
# was:	ori	4, dead, 0
	ori	$2, $0, 1
# was:	ori	2, 0, 1
	syscall
	la	$4, _cr_
# was:	la	4, _cr_
	ori	$2, $0, 4
# was:	ori	2, 0, 4
	syscall
	j	_stop_
# 
fib:
	sw	$31, -4($29)
	sw	$17, -12($29)
	sw	$16, -8($29)
	addi	$29, $29, -16
# 	ori	fib_arg__1_,2,0
	ori	$3, $0, 0
# was:	ori	_constPat__6_, 0, 0
	bne	$2, $3, _match__5_
# was:	bne	fib_arg__1_, _constPat__6_, _match__5_
	ori	$2, $0, 0
# was:	ori	fib_res__2_, 0, 0
	j	fib_return__3_
_match__5_:
	ori	$3, $0, 1
# was:	ori	_constPat__8_, 0, 1
	bne	$2, $3, _match__7_
# was:	bne	fib_arg__1_, _constPat__8_, _match__7_
	ori	$2, $0, 1
# was:	ori	fib_res__2_, 0, 1
	j	fib_return__3_
_match__7_:
	ori	$17, $2, 0
# was:	ori	_patVar_n__10_, fib_arg__1_, 0
# 	ori	_minus1__14_,_patVar_n__10_,0
	ori	$2, $0, 1
# was:	ori	_minus2__15_, 0, 1
	sub	$2, $17, $2
# was:	sub	_apply__13_, _minus1__14_, _minus2__15_
# 	ori	2,_apply__13_,0
	jal	fib
# was:	jal	fib, 2
	ori	$16, $2, 0
# was:	ori	_plus1__11_, 2, 0
# 	ori	_minus1__17_,_patVar_n__10_,0
	ori	$2, $0, 2
# was:	ori	_minus2__18_, 0, 2
	sub	$2, $17, $2
# was:	sub	_apply__16_, _minus1__17_, _minus2__18_
# 	ori	2,_apply__16_,0
	jal	fib
# was:	jal	fib, 2
# 	ori	_plus2__12_,2,0
	add	$2, $16, $2
# was:	add	fib_res__2_, _plus1__11_, _plus2__12_
	j	fib_return__3_
_match__9_:
	j	fib_fail__4_
fib_return__3_:
# 	ori	2,fib_res__2_,0
	addi	$29, $29, 16
	lw	$17, -12($29)
	lw	$16, -8($29)
	lw	$31, -4($29)
	jr	$31
fib_fail__4_:
	ori	$5, $0, 4
	j	_Error_
_stop_:
	ori	$2, $0, 10
	syscall
_Error_:
	la	$4, _ErrorString_
	ori	$2, $0, 4
	syscall
	ori	$4, $5, 0
	ori	$2, $0, 1
	syscall
	la	$4, _cr_
	ori	$2, $0, 4
	syscall
	j	_stop_
	.data	
_cr_:
	.asciiz	"\n"
_ErrorString_:
	.asciiz	"Match failed near line "
	.align	2
_heap_:
	.space	100000
