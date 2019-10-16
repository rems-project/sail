
/* 
 * Enabling and disabling interrupts setting is clearly not going
 * to be very useful for running on x86 in Linux userspace, but
 * mostly here just to think about what we might need for ARM
 */
.macro 	enable_interrupts
#ifdef SAIL_DISABLE_INTERRUPTS
	sti
#endif
.endm

.macro 	disable_interrupts
#ifdef SAIL_DISABLE_INTERRUPTS
	cli
#endif
.endm
	
sail_spin_unlock:
	movl	$1, (%rdi)
	xorl	%eax, %eax
	enable_interrupts
	ret

	.globl	sail_spin_unlock

/* Attempt to aquire the lock. zero flag will be set on success, otherwise set */
.macro	acquire	reg, mem
	disable_interrupts
	movl	$0, \reg
	xchgl	\reg, \mem
	cmpl	$1, \reg
.endm

sail_spin_lock:
	/* If the value pointed to by %rdi is equal to 0 (locked), then spin */
	cmpl	$0, (%rdi)
	je	.spin
.acquire:
	acquire	%eax, (%rdi)
#ifdef SAIL_DISABLE_INTERRUPTS
	jnz	.failed
#else
	jnz	.spin
#endif
	xorl	%eax, %eax
	ret
.failed:
	enable_interrupts
.spin:
	pause
	cmpl	$0, (%rdi)
	je	.spin
	jmp	.acquire

	.globl sail_spin_lock

sail_spin_trylock:
	acquire	%eax, (%rdi)
	jnz	.failed_try
	xorl 	%eax, %eax
	ret
.failed_try:
	enable_interrupts
	movl	$1, %eax
	ret

	.globl sail_spin_trylock
