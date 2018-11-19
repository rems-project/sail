#include "sail.h"
#include "rts.h"
#include "elf.h"

// union option
enum kind_zoption { Kind_zNone };

struct zoption {
  enum kind_zoption kind;
  union {struct { unit zNone; };};
};

static void CREATE(zoption)(struct zoption *op)
{
  op->kind = Kind_zNone;
  
}

static void RECREATE(zoption)(struct zoption *op) {}

static void KILL(zoption)(struct zoption *op)
{
  if (op->kind == Kind_zNone){
    /* do nothing */
  };
}

static void COPY(zoption)(struct zoption *rop, struct zoption op)
{
  if (rop->kind == Kind_zNone){
    /* do nothing */
  };
  rop->kind = op.kind;
  if (op.kind == Kind_zNone){
    rop->zNone = op.zNone;
  }
}

static bool EQUAL(zoption)(struct zoption op1, struct zoption op2) {
  if (op1.kind == Kind_zNone && op2.kind == Kind_zNone) {
    return EQUAL(unit)(op1.zNone, op2.zNone);
  } else return false;
}

static void zNone(struct zoption *rop, unit op)
{
  if (rop->kind == Kind_zNone){
    /* do nothing */
  }
  rop->kind = Kind_zNone;
  rop->zNone = op;
}





























void zzzeros(sail_bits *rop, sail_int, unit);

void zzzeros(sail_bits *zgsz31, sail_int zn__tv, unit zgsz30)
{
  __label__ end_function_1, end_block_exception_2;

  zeros(*(&zgsz31), zn__tv);
end_function_1: ;
end_block_exception_2: ;
}

// register R
mach_bits zR;

// register S
mach_bits zS;

unit zmain(unit);

sail_bits zghz30;
sail_int zghz31;
sail_bits zghz32;

void startup_zmain(void)
{
  CREATE(sail_bits)(&zghz30);
  CREATE(sail_int)(&zghz31);
  CREATE(sail_bits)(&zghz32);
}

unit zmain(unit zgsz34)
{
  __label__ end_block_exception_4;

  unit zgsz39;
  {
    RECREATE_OF(sail_int, mach_int)(&zghz31, 32l);
    {
      /* copy call */
      RECREATE(sail_bits)(&zghz32);
      zzzeros(&zghz32, zghz31, UNIT);
      zR = CONVERT_OF(mach_bits, sail_bits)(zghz32, true);
    }
    unit zgsz37;
    zgsz37 = UNIT;
  }
  RECREATE_OF(sail_bits, mach_bits)(&zghz30, zR, UINT64_C(32) , true);
  zgsz39 = print_bits("R = ", zghz30);
  /* early return cleanup */
  return zgsz39;
end_block_exception_4: ;

  return UNIT;
}



void finish_zmain(void)
{
  KILL(sail_bits)(&zghz32);
  KILL(sail_int)(&zghz31);
  KILL(sail_bits)(&zghz30);
}

unit zinitializze_registers(unit);

unit zinitializze_registers(unit zgsz311)
{
  __label__ end_block_exception_6;

  unit zgsz313;
  mach_bits zgsz312;
  {    zgsz312 = UINT64_C(0);
  }
  zS = UINT64_C(0);
  zgsz313 = UNIT;

  /* early return cleanup */
  return zgsz313;
end_block_exception_6: ;

  return UNIT;
}

void model_init(void)
{
  setup_rts();
  startup_zmain();
  sail_int zgsz32;
  CREATE_OF(sail_int, mach_int)(&zgsz32, 32l);
  {
    /* copy call */
    sail_bits zgsz33;
    CREATE(sail_bits)(&zgsz33);
    zzzeros(&zgsz33, zgsz32, UNIT);
    zR = CONVERT_OF(mach_bits, sail_bits)(zgsz33, true);
    KILL(sail_bits)(&zgsz33);
  }
  KILL(sail_int)(&zgsz32);
  zinitializze_registers(UNIT);
}

void model_fini(void)
{
  finish_zmain();
  cleanup_rts();
}

int model_main(int argc, char *argv[])
{
  model_init();
  if (process_arguments(argc, argv)) exit(EXIT_FAILURE);
  zmain(UNIT);
  model_fini();
  return EXIT_SUCCESS;
}

int main(int argc, char *argv[])
{
  return model_main(argc, argv);
}
