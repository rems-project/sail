#include <getopt.h>
#include <stdio.h>
#include <stdlib.h>

#include "elf.h"
#include "sail.h"
#include "rts.h"
#include "riscv_platform.h"
#include "riscv_platform_impl.h"
#include "riscv_sail.h"
#include "tv_spike_intf.h"

struct tv_spike_t *s = NULL;

static bool do_dump_dts = false;

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
  return entry;
}

/* for now, override the reset-vector using the elf entry */
void init_spike(const char *f, uint64_t entry)
{
  s = tv_init("RV64IMAFDC");
  tv_set_verbose(s, 1);
  tv_load_elf(s, f);
  tv_reset(s);
  tv_set_pc(s, entry);
}

void init_sail(uint64_t entry)
{
  model_init();
  zinit_platform(UNIT);
  zinit_sys(UNIT);
  zPC = entry;
}

void run_sail(void)
{
  bool spike_done;
  bool stepped;
  /* initialize the step number */
  mach_int step_no = 0;

  while (!zhtif_done) {
    { /* run a Sail step */
      sail_int sail_step;
      CREATE(sail_int)(&sail_step);
      CONVERT_OF(sail_int, mach_int)(&sail_step, step_no);
      stepped = zstep(sail_step);
      if (have_exception) goto step_exception;
    }
    if (stepped) step_no++;

    { /* run a Spike step */
      tv_step(s);
      spike_done = tv_is_done(s);
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
      /* TODO: update time */
    }
  }

 step_exception:
  model_fini();
  tv_free(s);
}

int main(int argc, char **argv)
{
  char *file = process_args(argc, argv);
  uint64_t entry = load_sail(file);

  init_sail(entry);
  init_spike(file, entry);

  run_sail();
}
