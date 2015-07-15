
main:
0x080483eb:	pushl	%ebp
0x080483ec:	movl	%esp, %ebp
0x080483ee:	subl	$0x10, %esp
0x080483f1:	movl	$0x7, -4(%ebp)
0x080483f8:	movl	$0xb, -8(%ebp)
0x080483ff:	movl	-4(%ebp), %eax
0x08048402:	andl	-8(%ebp), %eax
0x08048405:	leave	
0x08048406:	ret	; targets: 0xfee70000(MAY)

