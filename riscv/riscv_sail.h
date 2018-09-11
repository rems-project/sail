/* Top-level entry points into the Sail model. */

typedef int unit;
#define UNIT 0
typedef uint64_t mach_bits;

unit zinit_platform(unit);
unit zinit_sys(unit);
bool zstep(sail_int);

void model_init(void);
void model_fini(void);

extern bool zhtif_done;
extern mach_bits zhtif_exit_code;
extern bool have_exception;
extern mach_bits zPC;
extern mach_bits zminstret;
