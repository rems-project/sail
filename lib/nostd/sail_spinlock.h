#ifndef __SAIL_SPINLOCK__
#define __SAIL_SPINLOCK__

int sail_spin_unlock(volatile int *lock);

int sail_spin_lock(volatile int *lock);

int sail_spin_trylock(volatile int *lock);

#endif
