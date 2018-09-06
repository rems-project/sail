.global _start

.text

_start:
	auipc	t0, 0x0
	addi	a1, t0, 32
	csrr	a0, mhartid
	ld	t0, 24(t0)
	jr	t0
.short  0x0000
.word	0x00000000, 0x80000000
