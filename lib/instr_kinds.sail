union read_kind = {
  Read_plain : unit,
  Read_reserve : unit,
  Read_acquire : unit,
  Read_exclusive : unit,
  Read_exclusive_acquire : unit,
  Read_stream : unit,
  Read_RISCV_acquire : unit,
  Read_RISCV_strong_acquire : unit,
  Read_RISCV_reserved : unit,
  Read_RISCV_reserved_acquire : unit,
  Read_RISCV_reserved_strong_acquire : unit,
  Read_X86_locked : unit
}

union write_kind = {
  Write_plain  : unit
  Write_conditional : unit
  Write_release : unit
  Write_exclusive : unit
  Write_exclusive_release : unit
  Write_RISCV_release : unit
  Write_RISCV_strong_release : unit
  Write_RISCV_conditional : unit
  Write_RISCV_conditional_release : unit
  Write_RISCV_conditional_strong_release : unit
  Write_X86_locked : unit
}