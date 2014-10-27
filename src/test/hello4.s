	.file	"hello4.c"
	.section	".toc","aw"
	.section	".text"
	.align 2
	.globl main
	.section	".opd","aw"
	.align 3
main:
	.quad	.L.main,.TOC.@tocbase
	.previous
	.type	main, @function
.L.main:
	std 31,-8(1)
	stdu 1,-80(1)
	mr 31,1
	li 0,6
	stw 0,56(31)
	li 0,7
	stw 0,52(31)
	li 0,0
	stw 0,48(31)
	lwz 9,56(31)
	lwz 0,52(31)
	mullw 0,9,0
	extsw 9,0
	lwz 11,56(31)
	lwz 0,52(31)
	subf 0,0,11
	extsw 0,0
	cmpw 7,9,0
	ble 7,.L2
	lwz 9,56(31)
	lwz 0,52(31)
	mullw 0,9,0
	stw 0,48(31)
	b .L3
.L2:
	lwz 9,56(31)
	lwz 0,52(31)
	subf 0,0,9
	stw 0,48(31)
.L3:
	lwz 0,48(31)
	extsw 0,0
	mr 3,0
	addi 1,31,80
	ld 31,-8(1)
	blr
	.long 0
	.byte 0,0,0,0,128,1,0,1
	.size	main,.-.L.main
	.ident	"GCC: (GNU) 4.4.7 20120313 (Red Hat 4.4.7-3)"
	.section	.note.GNU-stack,"",@progbits
