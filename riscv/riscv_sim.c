#include <getopt.h>
#include <stdio.h>
#include <stdlib.h>

#include "elf.h"
#include "sail.h"
#include "rts.h"
#include "riscv_platform.h"
#include "riscv_platform_impl.h"
#include "riscv_sail.h"

#ifdef SPIKE
#include "tv_spike_intf.h"
#else
struct tv_spike_t;
#endif

/* Selected CSRs from riscv-isa-sim/riscv/encoding.h */
#define CSR_STVEC 0x105
#define CSR_SEPC 0x141
#define CSR_SCAUSE 0x142
#define CSR_STVAL 0x143

#define CSR_MSTATUS 0x300
#define CSR_MISA 0x301
#define CSR_MEDELEG 0x302
#define CSR_MIDELEG 0x303
#define CSR_MIE 0x304
#define CSR_MTVEC 0x305
#define CSR_MEPC 0x341
#define CSR_MCAUSE 0x342
#define CSR_MTVAL 0x343
#define CSR_MIP 0x344

static bool do_dump_dts = false;
struct tv_spike_t *s = NULL;

static struct option options[] = {
  {"enable-dirty",      no_argument,       0, 'd'},
  {"enable-misaligned", no_argument,       0, 'm'},
  {"dump-dts",          no_argument,       0, 's'},
  {"verbosity",         required_argument, 0, 'v'},
  {"help",              no_argument,       0, 'h'},
  {0, 0, 0, 0}
};

static void print_usage(const char *argv0, int ec)
{
  fprintf(stdout, "Usage: %s [options] <elf_file>\n", argv0);
  struct option *opt = options;
  while (opt->name) {
    fprintf(stdout, "\t -%c\t %s\n", (char)opt->val, opt->name);
    opt++;
  }
  exit(ec);
}

char *process_args(int argc, char **argv)
{
  int c, idx = 1;
  while(true) {
    c = getopt_long(argc, argv, "dmsv:h", options, &idx);
    if (c == -1) break;
    switch (c) {
    case 'd':
      rv_enable_dirty_update = true;
      break;
    case 'm':
      rv_enable_misaligned = true;
      break;
    case 's':
      do_dump_dts = true;
      break;
    case 'h':
      print_usage(argv[0], 0);
      break;
    default:
      fprintf(stderr, "Unrecognized optchar %c\n", c);
      print_usage(argv[0], 1);
    }
  }

  if (idx >= argc) print_usage(argv[0], 0);
  return argv[idx];
}

uint64_t load_sail(char *f)
{
  bool is32bit;
  uint64_t entry;
  load_elf(f, &is32bit, &entry);
  if (is32bit) {
    fprintf(stderr, "32-bit RISC-V not yet supported.\n");
    exit(1);
  }
  fprintf(stdout, "ELF Entry @ %lx\n", entry);
  /* locate htif ports */
  if (lookup_sym(f, "tohost", &rv_htif_tohost) < 0) {
    fprintf(stderr, "Unable to locate htif tohost port.\n");
    exit(1);
  }
  fprintf(stderr, "tohost located at %0" PRIx64 "\n", rv_htif_tohost);
  return entry;
}

void init_spike(const char *f, uint64_t entry)
{
#ifdef SPIKE
  s = tv_init("RV64IMAC");
  tv_set_verbose(s, 1);
  tv_set_dtb_in_rom(s, 1);
  tv_load_elf(s, f);
  tv_reset(s);
  /* sync the insns per tick */
  rv_insns_per_tick = tv_get_insns_per_tick(s);
#else
  s = NULL;
#endif
}

void init_sail_reset_vector(uint64_t entry)
{
#define RST_VEC_SIZE 8
  uint32_t reset_vec[RST_VEC_SIZE] = {
    0x297,                                      // auipc  t0,0x0
    0x28593 + (RST_VEC_SIZE * 4 << 20),         // addi   a1, t0, &dtb
    0xf1402573,                                 // csrr   a0, mhartid
    SAIL_XLEN == 32 ?
      0x0182a283u :                             // lw     t0,24(t0)
      0x0182b283u,                              // ld     t0,24(t0)
    0x28067,                                    // jr     t0
    0,
    (uint32_t) (entry & 0xffffffff),
    (uint32_t) (entry >> 32)
  };

  rv_rom_base = DEFAULT_RSTVEC;
  uint64_t addr = rv_rom_base;
  for (int i = 0; i < sizeof(reset_vec); i++)
    write_mem(addr++, (uint64_t)((char *)reset_vec)[i]);
#ifdef SPIKE
  const unsigned char *dtb = NULL;
  int dtb_len;
  tv_get_dtb(s, &dtb, &dtb_len);
  fprintf(stderr, "Got %d bytes of dtb at %p\n", dtb_len, dtb);
  for (int i = 0; i < dtb_len; i++)
    write_mem(addr++, dtb[i]);
#else
  fprintf(stdout, "Running without rom device tree.\n");
  /* TODO: write DTB */
#endif

  /* zero-fill to page boundary */
  const int align = 0x1000;
  uint64_t rom_end = (addr + align -1)/align * align;
  for (int i = addr; i < rom_end; i++)
    write_mem(addr++, 0);

  /* set rom size */
  rv_rom_size = rom_end - rv_rom_base;
  /* boot at reset vector */
  zPC = rv_rom_base;
}

void init_sail(uint64_t elf_entry)
{
  model_init();
  zinit_platform(UNIT);
  zinit_sys(UNIT);
  init_sail_reset_vector(elf_entry);
}

int init_check(struct tv_spike_t *s)
{
  int passed = 1;
#ifdef SPIKE
  passed &= tv_check_csr(s, CSR_MISA, zmisa.zMisa_chunk_0);
#endif
  return passed;
}

void finish(int ec)
{
  model_fini();
#ifdef SPIKE
  tv_free(s);
#endif
  exit(ec);
}

int compare_states(struct tv_spike_t *s)
{
  int passed = 1;

#ifdef SPIKE
  // fix default C enum map for cur_privilege
  uint8_t priv = (zcur_privilege == 2) ? 3 : zcur_privilege;
  passed &= tv_check_priv(s, priv);

  passed &= tv_check_pc(s, zPC);

  passed &= tv_check_gpr(s, 1, zx1);
  passed &= tv_check_gpr(s, 2, zx2);
  passed &= tv_check_gpr(s, 3, zx3);
  passed &= tv_check_gpr(s, 4, zx4);
  passed &= tv_check_gpr(s, 5, zx5);
  passed &= tv_check_gpr(s, 6, zx6);
  passed &= tv_check_gpr(s, 7, zx7);
  passed &= tv_check_gpr(s, 8, zx8);
  passed &= tv_check_gpr(s, 9, zx9);
  passed &= tv_check_gpr(s, 10, zx10);
  passed &= tv_check_gpr(s, 11, zx11);
  passed &= tv_check_gpr(s, 12, zx12);
  passed &= tv_check_gpr(s, 13, zx13);
  passed &= tv_check_gpr(s, 14, zx14);
  passed &= tv_check_gpr(s, 15, zx15);
  passed &= tv_check_gpr(s, 15, zx15);
  passed &= tv_check_gpr(s, 16, zx16);
  passed &= tv_check_gpr(s, 17, zx17);
  passed &= tv_check_gpr(s, 18, zx18);
  passed &= tv_check_gpr(s, 19, zx19);
  passed &= tv_check_gpr(s, 20, zx20);
  passed &= tv_check_gpr(s, 21, zx21);
  passed &= tv_check_gpr(s, 22, zx22);
  passed &= tv_check_gpr(s, 23, zx23);
  passed &= tv_check_gpr(s, 24, zx24);
  passed &= tv_check_gpr(s, 25, zx25);
  passed &= tv_check_gpr(s, 25, zx25);
  passed &= tv_check_gpr(s, 26, zx26);
  passed &= tv_check_gpr(s, 27, zx27);
  passed &= tv_check_gpr(s, 28, zx28);
  passed &= tv_check_gpr(s, 29, zx29);
  passed &= tv_check_gpr(s, 30, zx30);
  passed &= tv_check_gpr(s, 31, zx31);

  /* some selected CSRs for now */

  passed &= tv_check_csr(s, CSR_MCAUSE, zmcause.zMcause_chunk_0);
  passed &= tv_check_csr(s, CSR_MEPC, zmepc);
  passed &= tv_check_csr(s, CSR_MTVAL, zmtval);

  passed &= tv_check_csr(s, CSR_SCAUSE, zscause.zMcause_chunk_0);
  passed &= tv_check_csr(s, CSR_SEPC, zsepc);
  passed &= tv_check_csr(s, CSR_STVAL, zstval);
#endif

  return passed;
}

void flush_logs(void)
{
  fprintf(stderr, "\n");
  fflush(stderr);
  fprintf(stdout, "\n");
  fflush(stdout);
}

void run_sail(void)
{
  bool spike_done;
  bool stepped;
  bool diverged = false;

  /* initialize the step number */
  mach_int step_no = 0;
  int insn_cnt = 0;

  while (!zhtif_done) {
    { /* run a Sail step */
      sail_int sail_step;
      CREATE(sail_int)(&sail_step);
      CONVERT_OF(sail_int, mach_int)(&sail_step, step_no);
      stepped = zstep(sail_step);
      if (have_exception) goto step_exception;
      flush_logs();
    }
    if (stepped) {
      step_no++;
      insn_cnt++;
    }

#ifdef SPIKE
    { /* run a Spike step */
      tv_step(s);
      spike_done = tv_is_done(s);
      flush_logs();
    }

    if (zhtif_done) {
      if (!spike_done) {
        fprintf(stdout, "Sail done (exit-code %ld), but not Spike!\n", zhtif_exit_code);
        exit(1);
      }
      /* check exit code */
      if (zhtif_exit_code == 0)
        fprintf(stdout, "SUCCESS\n");
      else
        fprintf(stdout, "FAILURE: %ld\n", zhtif_exit_code);
    } else {
      if (spike_done) {
        fprintf(stdout, "Spike done, but not Sail!\n");
        exit(1);
      }

      if (!compare_states(s)) {
        diverged = true;
        break;
      }
    }
#endif

    if (insn_cnt == rv_insns_per_tick) {
      insn_cnt = 0;
      ztick_clock(UNIT);
      ztick_platform(UNIT);
#ifdef SPIKE
      tv_tick_clock(s);
      tv_step_io(s);
#endif
    }
  }

 dump_state:
  if (diverged) {
    /* TODO */
  }
  finish(diverged);

 step_exception:
  fprintf(stdout, "Sail exception!");
  goto dump_state;
}

int main(int argc, char **argv)
{
  char *file = process_args(argc, argv);
  uint64_t entry = load_sail(file);

  /* initialize spike before sail so that we can access the device-tree blob,
   * until we roll our own.
   */
  init_spike(file, entry);
  init_sail(entry);

  if (!init_check(s)) finish(1);

  run_sail();
}
