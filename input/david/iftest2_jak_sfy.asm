
main:
0x080483eb:	pushl	%ebp
0x080483ec:	movl	%esp, %ebp
0x080483ee:	subl	$0x10, %esp
0x080483f1:	movl	$0x4, -4(%ebp)
0x080483f8:	cmpl	$0x5, -4(%ebp)
0x080483fc:	jle	0x08048407	; targets: 0x080483fe(MAY), 0x08048407(MAY)
0x080483fe:	movl	$0x1, -4(%ebp)	; from: 0x080483fc(MAY)
0x08048405:	jmp	0x0804840e	; targets: 0x0804840e(MAY)
0x08048407:	movl	$0xa, -4(%ebp)	; from: 0x080483fc(MAY)
0x0804840e:	movl	-4(%ebp), %eax	; from: 0x08048405(MAY)
0x08048411:	leave	
0x08048412:	ret	; targets: 0xfee70000(MAY)

