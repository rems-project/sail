open Endianness
  
open Error
  
let decimal_string_of_int64 e = let i = Int64.to_int e in string_of_int i
  
let hex_string_of_int64 (e : Int64.t) : string =
  let i = Int64.to_int e in Printf.sprintf "0x%x" i
  
let partition_bitstring size bitstring =
  ((Bitstring.takebits size bitstring), (Bitstring.dropbits size bitstring))
  
let acquire_bitstring path_to_target =
  try
    let bitstring = Bitstring.bitstring_of_file path_to_target
    in return bitstring
  with | _ -> Fail ("acquire_bitstring: cannot open file" ^ path_to_target)
  
(** Unsigned char type *)
let read_unsigned_char_le bs rest =
  let (__pabitstring_data_1001, __pabitstring_original_off_1004,
       __pabitstring_original_len_1005) =
    bs in
  let __pabitstring_off_1002 = __pabitstring_original_off_1004
  and __pabitstring_len_1003 = __pabitstring_original_len_1005 in
  let __pabitstring_off_aligned_1006 = (__pabitstring_off_1002 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1006;
     let __pabitstring_result_1007 = ref None
     in
       ((try
           (if __pabitstring_len_1003 >= 8
            then
              (let v =
                 if __pabitstring_off_aligned_1006
                 then
                   (let o = (__pabitstring_original_off_1004 lsr 3) + 0
                    in
                      Char.code (String.unsafe_get __pabitstring_data_1001 o))
                 else
                   Bitstring.extract_char_unsigned __pabitstring_data_1001
                     __pabitstring_off_1002 __pabitstring_len_1003 8 in
               let __pabitstring_off_1002 = __pabitstring_off_1002 + 8
               and __pabitstring_len_1003 = __pabitstring_len_1003 - 8
               in
                 match v with
                 | unsigned when true ->
                     (__pabitstring_result_1007 :=
                        Some (return ((Uint32.of_int unsigned), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1007 := Some (Fail "read_unsigned_char_le");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1007 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 28, 2))))
  
let read_unsigned_char_be bs rest =
  let (__pabitstring_data_1008, __pabitstring_original_off_1011,
       __pabitstring_original_len_1012) =
    bs in
  let __pabitstring_off_1009 = __pabitstring_original_off_1011
  and __pabitstring_len_1010 = __pabitstring_original_len_1012 in
  let __pabitstring_off_aligned_1013 = (__pabitstring_off_1009 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1013;
     let __pabitstring_result_1014 = ref None
     in
       ((try
           (if __pabitstring_len_1010 >= 8
            then
              (let v =
                 if __pabitstring_off_aligned_1013
                 then
                   (let o = (__pabitstring_original_off_1011 lsr 3) + 0
                    in
                      Char.code (String.unsafe_get __pabitstring_data_1008 o))
                 else
                   Bitstring.extract_char_unsigned __pabitstring_data_1008
                     __pabitstring_off_1009 __pabitstring_len_1010 8 in
               let __pabitstring_off_1009 = __pabitstring_off_1009 + 8
               and __pabitstring_len_1010 = __pabitstring_len_1010 - 8
               in
                 match v with
                 | unsigned when true ->
                     (__pabitstring_result_1014 :=
                        Some (return ((Uint32.of_int unsigned), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1014 := Some (Fail "read_unsigned_char_be");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1014 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 34, 2))))
  
let read_unsigned_char endian bs =
  let (cut, rest) = partition_bitstring 8 bs
  in
    match endian with
    | Little -> read_unsigned_char_le cut rest
    | Big -> read_unsigned_char_be cut rest
  
(** ELF address type:
  * 4 byte unsigned type on 32-bit architectures.
  * 8 byte unsigned type on 64-bit architectures.
  *)
let read_elf32_addr_le bs rest =
  let (__pabitstring_data_1015, __pabitstring_original_off_1018,
       __pabitstring_original_len_1019) =
    bs in
  let __pabitstring_off_1016 = __pabitstring_original_off_1018
  and __pabitstring_len_1017 = __pabitstring_original_len_1019 in
  let __pabitstring_off_aligned_1020 = (__pabitstring_off_1016 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1020;
     let __pabitstring_result_1021 = ref None
     in
       ((try
           (if __pabitstring_len_1017 >= 32
            then
              (let v =
                 if __pabitstring_off_aligned_1020
                 then
                   (let o = (__pabitstring_original_off_1018 lsr 3) + 0 in
                    let zero = Int32.of_int 0
                    in
                      Bitstring.extract_fastpath_int32_le_unsigned
                        __pabitstring_data_1015 o zero)
                 else
                   Bitstring.extract_int32_le_unsigned
                     __pabitstring_data_1015 __pabitstring_off_1016
                     __pabitstring_len_1017 32 in
               let __pabitstring_off_1016 = __pabitstring_off_1016 + 32
               and __pabitstring_len_1017 = __pabitstring_len_1017 - 32
               in
                 match v with
                 | addr when true ->
                     (__pabitstring_result_1021 :=
                        Some (return ((Uint32.of_int32 addr), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1021 := Some (Fail "read_elf32_addr_le");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1021 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 52, 2))))
  
let read_elf32_addr_be bs rest =
  let (__pabitstring_data_1022, __pabitstring_original_off_1025,
       __pabitstring_original_len_1026) =
    bs in
  let __pabitstring_off_1023 = __pabitstring_original_off_1025
  and __pabitstring_len_1024 = __pabitstring_original_len_1026 in
  let __pabitstring_off_aligned_1027 = (__pabitstring_off_1023 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1027;
     let __pabitstring_result_1028 = ref None
     in
       ((try
           (if __pabitstring_len_1024 >= 32
            then
              (let v =
                 if __pabitstring_off_aligned_1027
                 then
                   (let o = (__pabitstring_original_off_1025 lsr 3) + 0 in
                    let zero = Int32.of_int 0
                    in
                      Bitstring.extract_fastpath_int32_be_unsigned
                        __pabitstring_data_1022 o zero)
                 else
                   Bitstring.extract_int32_be_unsigned
                     __pabitstring_data_1022 __pabitstring_off_1023
                     __pabitstring_len_1024 32 in
               let __pabitstring_off_1023 = __pabitstring_off_1023 + 32
               and __pabitstring_len_1024 = __pabitstring_len_1024 - 32
               in
                 match v with
                 | addr when true ->
                     (__pabitstring_result_1028 :=
                        Some (return ((Uint32.of_int32 addr), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1028 := Some (Fail "read_elf32_addr_be");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1028 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 58, 2))))
  
let read_elf32_addr endian bs =
  let (cut, rest) = partition_bitstring 32 bs
  in
    match endian with
    | Little -> read_elf32_addr_le cut rest
    | Big -> read_elf32_addr_be cut rest
  
let read_elf64_addr_le bs rest =
  let (__pabitstring_data_1029, __pabitstring_original_off_1032,
       __pabitstring_original_len_1033) =
    bs in
  let __pabitstring_off_1030 = __pabitstring_original_off_1032
  and __pabitstring_len_1031 = __pabitstring_original_len_1033 in
  let __pabitstring_off_aligned_1034 = (__pabitstring_off_1030 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1034;
     let __pabitstring_result_1035 = ref None
     in
       ((try
           (if __pabitstring_len_1031 >= 64
            then
              (let v =
                 if __pabitstring_off_aligned_1034
                 then
                   (let o = (__pabitstring_original_off_1032 lsr 3) + 0 in
                    let zero = Int64.of_int 0
                    in
                      Bitstring.extract_fastpath_int64_le_unsigned
                        __pabitstring_data_1029 o zero)
                 else
                   Bitstring.extract_int64_le_unsigned
                     __pabitstring_data_1029 __pabitstring_off_1030
                     __pabitstring_len_1031 64 in
               let __pabitstring_off_1030 = __pabitstring_off_1030 + 64
               and __pabitstring_len_1031 = __pabitstring_len_1031 - 64
               in
                 match v with
                 | addr when true ->
                     (__pabitstring_result_1035 :=
                        Some (return ((Uint64.of_int64 addr), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1035 := Some (Fail "read_elf64_addr_le");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1035 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 71, 2))))
  
let read_elf64_addr_be bs rest =
  let (__pabitstring_data_1036, __pabitstring_original_off_1039,
       __pabitstring_original_len_1040) =
    bs in
  let __pabitstring_off_1037 = __pabitstring_original_off_1039
  and __pabitstring_len_1038 = __pabitstring_original_len_1040 in
  let __pabitstring_off_aligned_1041 = (__pabitstring_off_1037 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1041;
     let __pabitstring_result_1042 = ref None
     in
       ((try
           (if __pabitstring_len_1038 >= 64
            then
              (let v =
                 if __pabitstring_off_aligned_1041
                 then
                   (let o = (__pabitstring_original_off_1039 lsr 3) + 0 in
                    let zero = Int64.of_int 0
                    in
                      Bitstring.extract_fastpath_int64_be_unsigned
                        __pabitstring_data_1036 o zero)
                 else
                   Bitstring.extract_int64_be_unsigned
                     __pabitstring_data_1036 __pabitstring_off_1037
                     __pabitstring_len_1038 64 in
               let __pabitstring_off_1037 = __pabitstring_off_1037 + 64
               and __pabitstring_len_1038 = __pabitstring_len_1038 - 64
               in
                 match v with
                 | addr when true ->
                     (__pabitstring_result_1042 :=
                        Some (return ((Uint64.of_int64 addr), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1042 := Some (Fail "read_elf64_addr_be");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1042 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 77, 2))))
  
let read_elf64_addr endian bs =
  let (cut, rest) = partition_bitstring 64 bs
  in
    match endian with
    | Little -> read_elf64_addr_le cut rest
    | Big -> read_elf64_addr_be cut rest
  
(** ELF offset type:
  * 4 byte unsigned type on 32-bit architectures.
  * 8 byte unsigned type on 64-bit architectures.
  *)
let read_elf32_off_le bs rest =
  let (__pabitstring_data_1043, __pabitstring_original_off_1046,
       __pabitstring_original_len_1047) =
    bs in
  let __pabitstring_off_1044 = __pabitstring_original_off_1046
  and __pabitstring_len_1045 = __pabitstring_original_len_1047 in
  let __pabitstring_off_aligned_1048 = (__pabitstring_off_1044 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1048;
     let __pabitstring_result_1049 = ref None
     in
       ((try
           (if __pabitstring_len_1045 >= 32
            then
              (let v =
                 if __pabitstring_off_aligned_1048
                 then
                   (let o = (__pabitstring_original_off_1046 lsr 3) + 0 in
                    let zero = Int32.of_int 0
                    in
                      Bitstring.extract_fastpath_int32_le_unsigned
                        __pabitstring_data_1043 o zero)
                 else
                   Bitstring.extract_int32_le_unsigned
                     __pabitstring_data_1043 __pabitstring_off_1044
                     __pabitstring_len_1045 32 in
               let __pabitstring_off_1044 = __pabitstring_off_1044 + 32
               and __pabitstring_len_1045 = __pabitstring_len_1045 - 32
               in
                 match v with
                 | off when true ->
                     (__pabitstring_result_1049 :=
                        Some (return ((Uint32.of_int32 off), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1049 := Some (Fail "read_elf32_off_le");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1049 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 94, 2))))
  
let read_elf32_off_be bs rest =
  let (__pabitstring_data_1050, __pabitstring_original_off_1053,
       __pabitstring_original_len_1054) =
    bs in
  let __pabitstring_off_1051 = __pabitstring_original_off_1053
  and __pabitstring_len_1052 = __pabitstring_original_len_1054 in
  let __pabitstring_off_aligned_1055 = (__pabitstring_off_1051 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1055;
     let __pabitstring_result_1056 = ref None
     in
       ((try
           (if __pabitstring_len_1052 >= 32
            then
              (let v =
                 if __pabitstring_off_aligned_1055
                 then
                   (let o = (__pabitstring_original_off_1053 lsr 3) + 0 in
                    let zero = Int32.of_int 0
                    in
                      Bitstring.extract_fastpath_int32_be_unsigned
                        __pabitstring_data_1050 o zero)
                 else
                   Bitstring.extract_int32_be_unsigned
                     __pabitstring_data_1050 __pabitstring_off_1051
                     __pabitstring_len_1052 32 in
               let __pabitstring_off_1051 = __pabitstring_off_1051 + 32
               and __pabitstring_len_1052 = __pabitstring_len_1052 - 32
               in
                 match v with
                 | off when true ->
                     (__pabitstring_result_1056 :=
                        Some (return ((Uint32.of_int32 off), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1056 := Some (Fail "read_elf32_off_be");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1056 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 100, 2))))
  
let read_elf32_off endian bs =
  let (cut, rest) = partition_bitstring 32 bs
  in
    match endian with
    | Little -> read_elf32_off_le cut rest
    | Big -> read_elf32_off_be cut rest
  
let read_elf64_off_le bs rest =
  let (__pabitstring_data_1057, __pabitstring_original_off_1060,
       __pabitstring_original_len_1061) =
    bs in
  let __pabitstring_off_1058 = __pabitstring_original_off_1060
  and __pabitstring_len_1059 = __pabitstring_original_len_1061 in
  let __pabitstring_off_aligned_1062 = (__pabitstring_off_1058 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1062;
     let __pabitstring_result_1063 = ref None
     in
       ((try
           (if __pabitstring_len_1059 >= 64
            then
              (let v =
                 if __pabitstring_off_aligned_1062
                 then
                   (let o = (__pabitstring_original_off_1060 lsr 3) + 0 in
                    let zero = Int64.of_int 0
                    in
                      Bitstring.extract_fastpath_int64_le_unsigned
                        __pabitstring_data_1057 o zero)
                 else
                   Bitstring.extract_int64_le_unsigned
                     __pabitstring_data_1057 __pabitstring_off_1058
                     __pabitstring_len_1059 64 in
               let __pabitstring_off_1058 = __pabitstring_off_1058 + 64
               and __pabitstring_len_1059 = __pabitstring_len_1059 - 64
               in
                 match v with
                 | off when true ->
                     (__pabitstring_result_1063 :=
                        Some (return ((Uint64.of_int64 off), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1063 := Some (Fail "read_elf64_off_le");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1063 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 113, 2))))
  
let read_elf64_off_be bs rest =
  let (__pabitstring_data_1064, __pabitstring_original_off_1067,
       __pabitstring_original_len_1068) =
    bs in
  let __pabitstring_off_1065 = __pabitstring_original_off_1067
  and __pabitstring_len_1066 = __pabitstring_original_len_1068 in
  let __pabitstring_off_aligned_1069 = (__pabitstring_off_1065 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1069;
     let __pabitstring_result_1070 = ref None
     in
       ((try
           (if __pabitstring_len_1066 >= 64
            then
              (let v =
                 if __pabitstring_off_aligned_1069
                 then
                   (let o = (__pabitstring_original_off_1067 lsr 3) + 0 in
                    let zero = Int64.of_int 0
                    in
                      Bitstring.extract_fastpath_int64_be_unsigned
                        __pabitstring_data_1064 o zero)
                 else
                   Bitstring.extract_int64_be_unsigned
                     __pabitstring_data_1064 __pabitstring_off_1065
                     __pabitstring_len_1066 64 in
               let __pabitstring_off_1065 = __pabitstring_off_1065 + 64
               and __pabitstring_len_1066 = __pabitstring_len_1066 - 64
               in
                 match v with
                 | off when true ->
                     (__pabitstring_result_1070 :=
                        Some (return ((Uint64.of_int64 off), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1070 := Some (Fail "read_elf64_off_be");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1070 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 119, 2))))
  
let read_elf64_off endian bs =
  let (cut, rest) = partition_bitstring 64 bs
  in
    match endian with
    | Little -> read_elf64_off_le cut rest
    | Big -> read_elf64_off_be cut rest
  
(** ELF half word type:
  * 2 byte unsigned type on 32-bit architectures.
  * 2 byte unsigned type on 64-bit architecutres.
  *)
let read_elf32_half_le bs rest =
  let (__pabitstring_data_1071, __pabitstring_original_off_1074,
       __pabitstring_original_len_1075) =
    bs in
  let __pabitstring_off_1072 = __pabitstring_original_off_1074
  and __pabitstring_len_1073 = __pabitstring_original_len_1075 in
  let __pabitstring_off_aligned_1076 = (__pabitstring_off_1072 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1076;
     let __pabitstring_result_1077 = ref None
     in
       ((try
           (if __pabitstring_len_1073 >= 16
            then
              (let v =
                 if __pabitstring_off_aligned_1076
                 then
                   (let o = (__pabitstring_original_off_1074 lsr 3) + 0
                    in
                      Bitstring.extract_fastpath_int16_le_unsigned
                        __pabitstring_data_1071 o)
                 else
                   Bitstring.extract_int_le_unsigned __pabitstring_data_1071
                     __pabitstring_off_1072 __pabitstring_len_1073 16 in
               let __pabitstring_off_1072 = __pabitstring_off_1072 + 16
               and __pabitstring_len_1073 = __pabitstring_len_1073 - 16
               in
                 match v with
                 | half when true ->
                     (__pabitstring_result_1077 :=
                        Some (return ((Uint32.of_int half), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1077 := Some (Fail "read_elf32_half_le");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1077 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 137, 2))))
  
let read_elf32_half_be bs rest =
  let (__pabitstring_data_1078, __pabitstring_original_off_1081,
       __pabitstring_original_len_1082) =
    bs in
  let __pabitstring_off_1079 = __pabitstring_original_off_1081
  and __pabitstring_len_1080 = __pabitstring_original_len_1082 in
  let __pabitstring_off_aligned_1083 = (__pabitstring_off_1079 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1083;
     let __pabitstring_result_1084 = ref None
     in
       ((try
           (if __pabitstring_len_1080 >= 16
            then
              (let v =
                 if __pabitstring_off_aligned_1083
                 then
                   (let o = (__pabitstring_original_off_1081 lsr 3) + 0
                    in
                      Bitstring.extract_fastpath_int16_be_unsigned
                        __pabitstring_data_1078 o)
                 else
                   Bitstring.extract_int_be_unsigned __pabitstring_data_1078
                     __pabitstring_off_1079 __pabitstring_len_1080 16 in
               let __pabitstring_off_1079 = __pabitstring_off_1079 + 16
               and __pabitstring_len_1080 = __pabitstring_len_1080 - 16
               in
                 match v with
                 | half when true ->
                     (__pabitstring_result_1084 :=
                        Some (return ((Uint32.of_int half), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1084 := Some (Fail "read_elf32_half_be");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1084 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 143, 2))))
  
let read_elf32_half endian bs =
  let (cut, rest) = partition_bitstring 16 bs
  in
    match endian with
    | Little -> read_elf32_half_le cut rest
    | Big -> read_elf32_half_be cut rest
  
let read_elf64_half_le bs rest =
  let (__pabitstring_data_1085, __pabitstring_original_off_1088,
       __pabitstring_original_len_1089) =
    bs in
  let __pabitstring_off_1086 = __pabitstring_original_off_1088
  and __pabitstring_len_1087 = __pabitstring_original_len_1089 in
  let __pabitstring_off_aligned_1090 = (__pabitstring_off_1086 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1090;
     let __pabitstring_result_1091 = ref None
     in
       ((try
           (if __pabitstring_len_1087 >= 16
            then
              (let v =
                 if __pabitstring_off_aligned_1090
                 then
                   (let o = (__pabitstring_original_off_1088 lsr 3) + 0
                    in
                      Bitstring.extract_fastpath_int16_le_unsigned
                        __pabitstring_data_1085 o)
                 else
                   Bitstring.extract_int_le_unsigned __pabitstring_data_1085
                     __pabitstring_off_1086 __pabitstring_len_1087 16 in
               let __pabitstring_off_1086 = __pabitstring_off_1086 + 16
               and __pabitstring_len_1087 = __pabitstring_len_1087 - 16
               in
                 match v with
                 | half when true ->
                     (__pabitstring_result_1091 :=
                        Some (return ((Uint32.of_int half), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1091 := Some (Fail "read_elf64_half_le");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1091 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 156, 2))))
  
let read_elf64_half_be bs rest =
  let (__pabitstring_data_1092, __pabitstring_original_off_1095,
       __pabitstring_original_len_1096) =
    bs in
  let __pabitstring_off_1093 = __pabitstring_original_off_1095
  and __pabitstring_len_1094 = __pabitstring_original_len_1096 in
  let __pabitstring_off_aligned_1097 = (__pabitstring_off_1093 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1097;
     let __pabitstring_result_1098 = ref None
     in
       ((try
           (if __pabitstring_len_1094 >= 16
            then
              (let v =
                 if __pabitstring_off_aligned_1097
                 then
                   (let o = (__pabitstring_original_off_1095 lsr 3) + 0
                    in
                      Bitstring.extract_fastpath_int16_be_unsigned
                        __pabitstring_data_1092 o)
                 else
                   Bitstring.extract_int_be_unsigned __pabitstring_data_1092
                     __pabitstring_off_1093 __pabitstring_len_1094 16 in
               let __pabitstring_off_1093 = __pabitstring_off_1093 + 16
               and __pabitstring_len_1094 = __pabitstring_len_1094 - 16
               in
                 match v with
                 | half when true ->
                     (__pabitstring_result_1098 :=
                        Some (return ((Uint32.of_int half), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1098 := Some (Fail "read_elf64_half_be");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1098 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 162, 2))))
  
let read_elf64_half endian bs =
  let (cut, rest) = partition_bitstring 16 bs
  in
    match endian with
    | Little -> read_elf64_half_le cut rest
    | Big -> read_elf64_half_be cut rest
  
(** ELF word type:
  * 4 byte unsigned type on 32-bit architectures.
  * 4 byte unsigned type on 32-bit architectures.
  *)
let read_elf32_word_le bs rest =
  let (__pabitstring_data_1099, __pabitstring_original_off_1102,
       __pabitstring_original_len_1103) =
    bs in
  let __pabitstring_off_1100 = __pabitstring_original_off_1102
  and __pabitstring_len_1101 = __pabitstring_original_len_1103 in
  let __pabitstring_off_aligned_1104 = (__pabitstring_off_1100 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1104;
     let __pabitstring_result_1105 = ref None
     in
       ((try
           (if __pabitstring_len_1101 >= 32
            then
              (let v =
                 if __pabitstring_off_aligned_1104
                 then
                   (let o = (__pabitstring_original_off_1102 lsr 3) + 0 in
                    let zero = Int32.of_int 0
                    in
                      Bitstring.extract_fastpath_int32_le_unsigned
                        __pabitstring_data_1099 o zero)
                 else
                   Bitstring.extract_int32_le_unsigned
                     __pabitstring_data_1099 __pabitstring_off_1100
                     __pabitstring_len_1101 32 in
               let __pabitstring_off_1100 = __pabitstring_off_1100 + 32
               and __pabitstring_len_1101 = __pabitstring_len_1101 - 32
               in
                 match v with
                 | word when true ->
                     (__pabitstring_result_1105 :=
                        Some (return ((Uint32.of_int32 word), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1105 := Some (Fail "read_elf32_word_le");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1105 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 180, 2))))
  
let read_elf32_word_be bs rest =
  let (__pabitstring_data_1106, __pabitstring_original_off_1109,
       __pabitstring_original_len_1110) =
    bs in
  let __pabitstring_off_1107 = __pabitstring_original_off_1109
  and __pabitstring_len_1108 = __pabitstring_original_len_1110 in
  let __pabitstring_off_aligned_1111 = (__pabitstring_off_1107 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1111;
     let __pabitstring_result_1112 = ref None
     in
       ((try
           (if __pabitstring_len_1108 >= 32
            then
              (let v =
                 if __pabitstring_off_aligned_1111
                 then
                   (let o = (__pabitstring_original_off_1109 lsr 3) + 0 in
                    let zero = Int32.of_int 0
                    in
                      Bitstring.extract_fastpath_int32_be_unsigned
                        __pabitstring_data_1106 o zero)
                 else
                   Bitstring.extract_int32_be_unsigned
                     __pabitstring_data_1106 __pabitstring_off_1107
                     __pabitstring_len_1108 32 in
               let __pabitstring_off_1107 = __pabitstring_off_1107 + 32
               and __pabitstring_len_1108 = __pabitstring_len_1108 - 32
               in
                 match v with
                 | word when true ->
                     (__pabitstring_result_1112 :=
                        Some (return ((Uint32.of_int32 word), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1112 := Some (Fail "read_elf32_word_be");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1112 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 186, 2))))
  
let read_elf32_word endian bs =
  let (cut, rest) = partition_bitstring 32 bs
  in
    match endian with
    | Little -> read_elf32_word_le cut rest
    | Big -> read_elf32_word_be cut rest
  
let read_elf64_word_le bs rest =
  let (__pabitstring_data_1113, __pabitstring_original_off_1116,
       __pabitstring_original_len_1117) =
    bs in
  let __pabitstring_off_1114 = __pabitstring_original_off_1116
  and __pabitstring_len_1115 = __pabitstring_original_len_1117 in
  let __pabitstring_off_aligned_1118 = (__pabitstring_off_1114 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1118;
     let __pabitstring_result_1119 = ref None
     in
       ((try
           (if __pabitstring_len_1115 >= 32
            then
              (let v =
                 if __pabitstring_off_aligned_1118
                 then
                   (let o = (__pabitstring_original_off_1116 lsr 3) + 0 in
                    let zero = Int32.of_int 0
                    in
                      Bitstring.extract_fastpath_int32_le_unsigned
                        __pabitstring_data_1113 o zero)
                 else
                   Bitstring.extract_int32_le_unsigned
                     __pabitstring_data_1113 __pabitstring_off_1114
                     __pabitstring_len_1115 32 in
               let __pabitstring_off_1114 = __pabitstring_off_1114 + 32
               and __pabitstring_len_1115 = __pabitstring_len_1115 - 32
               in
                 match v with
                 | word when true ->
                     (__pabitstring_result_1119 :=
                        Some (return ((Uint32.of_int32 word), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1119 := Some (Fail "read_elf64_word_le");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1119 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 199, 2))))
  
let read_elf64_word_be bs rest =
  let (__pabitstring_data_1120, __pabitstring_original_off_1123,
       __pabitstring_original_len_1124) =
    bs in
  let __pabitstring_off_1121 = __pabitstring_original_off_1123
  and __pabitstring_len_1122 = __pabitstring_original_len_1124 in
  let __pabitstring_off_aligned_1125 = (__pabitstring_off_1121 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1125;
     let __pabitstring_result_1126 = ref None
     in
       ((try
           (if __pabitstring_len_1122 >= 32
            then
              (let v =
                 if __pabitstring_off_aligned_1125
                 then
                   (let o = (__pabitstring_original_off_1123 lsr 3) + 0 in
                    let zero = Int32.of_int 0
                    in
                      Bitstring.extract_fastpath_int32_be_unsigned
                        __pabitstring_data_1120 o zero)
                 else
                   Bitstring.extract_int32_be_unsigned
                     __pabitstring_data_1120 __pabitstring_off_1121
                     __pabitstring_len_1122 32 in
               let __pabitstring_off_1121 = __pabitstring_off_1121 + 32
               and __pabitstring_len_1122 = __pabitstring_len_1122 - 32
               in
                 match v with
                 | word when true ->
                     (__pabitstring_result_1126 :=
                        Some (return ((Uint32.of_int32 word), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1126 := Some (Fail "read_elf64_word_be");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1126 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 205, 2))))
  
let read_elf64_word endian bs =
  let (cut, rest) = partition_bitstring 32 bs
  in
    match endian with
    | Little -> read_elf64_word_le cut rest
    | Big -> read_elf64_word_be cut rest
  
(** ELF signed word type:
  * 4 byte signed type on 32-bit architectures
  * 4 byte signed type on 64-bit architectures
  *)
let read_elf32_sword_le bs rest =
  let (__pabitstring_data_1127, __pabitstring_original_off_1130,
       __pabitstring_original_len_1131) =
    bs in
  let __pabitstring_off_1128 = __pabitstring_original_off_1130
  and __pabitstring_len_1129 = __pabitstring_original_len_1131 in
  let __pabitstring_off_aligned_1132 = (__pabitstring_off_1128 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1132;
     let __pabitstring_result_1133 = ref None
     in
       ((try
           (if __pabitstring_len_1129 >= 32
            then
              (let v =
                 if __pabitstring_off_aligned_1132
                 then
                   (let o = (__pabitstring_original_off_1130 lsr 3) + 0 in
                    let zero = Int32.of_int 0
                    in
                      Bitstring.extract_fastpath_int32_le_unsigned
                        __pabitstring_data_1127 o zero)
                 else
                   Bitstring.extract_int32_le_unsigned
                     __pabitstring_data_1127 __pabitstring_off_1128
                     __pabitstring_len_1129 32 in
               let __pabitstring_off_1128 = __pabitstring_off_1128 + 32
               and __pabitstring_len_1129 = __pabitstring_len_1129 - 32
               in
                 match v with
                 | word when true ->
                     (__pabitstring_result_1133 := Some (return (word, rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1133 := Some (Fail "read_elf32_sword_le");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1133 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 223, 2))))
  
let read_elf32_sword_be bs rest =
  let (__pabitstring_data_1134, __pabitstring_original_off_1137,
       __pabitstring_original_len_1138) =
    bs in
  let __pabitstring_off_1135 = __pabitstring_original_off_1137
  and __pabitstring_len_1136 = __pabitstring_original_len_1138 in
  let __pabitstring_off_aligned_1139 = (__pabitstring_off_1135 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1139;
     let __pabitstring_result_1140 = ref None
     in
       ((try
           (if __pabitstring_len_1136 >= 32
            then
              (let v =
                 if __pabitstring_off_aligned_1139
                 then
                   (let o = (__pabitstring_original_off_1137 lsr 3) + 0 in
                    let zero = Int32.of_int 0
                    in
                      Bitstring.extract_fastpath_int32_be_unsigned
                        __pabitstring_data_1134 o zero)
                 else
                   Bitstring.extract_int32_be_unsigned
                     __pabitstring_data_1134 __pabitstring_off_1135
                     __pabitstring_len_1136 32 in
               let __pabitstring_off_1135 = __pabitstring_off_1135 + 32
               and __pabitstring_len_1136 = __pabitstring_len_1136 - 32
               in
                 match v with
                 | word when true ->
                     (__pabitstring_result_1140 := Some (return (word, rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1140 := Some (Fail "read_elf32_sword_be");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1140 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 229, 2))))
  
let read_elf32_sword endian bs =
  let (cut, rest) = partition_bitstring 32 bs
  in
    match endian with
    | Little -> read_elf32_sword_le cut rest
    | Big -> read_elf32_sword_be cut rest
  
let read_elf64_sword_le bs rest =
  let (__pabitstring_data_1141, __pabitstring_original_off_1144,
       __pabitstring_original_len_1145) =
    bs in
  let __pabitstring_off_1142 = __pabitstring_original_off_1144
  and __pabitstring_len_1143 = __pabitstring_original_len_1145 in
  let __pabitstring_off_aligned_1146 = (__pabitstring_off_1142 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1146;
     let __pabitstring_result_1147 = ref None
     in
       ((try
           (if __pabitstring_len_1143 >= 32
            then
              (let v =
                 if __pabitstring_off_aligned_1146
                 then
                   (let o = (__pabitstring_original_off_1144 lsr 3) + 0 in
                    let zero = Int32.of_int 0
                    in
                      Bitstring.extract_fastpath_int32_le_unsigned
                        __pabitstring_data_1141 o zero)
                 else
                   Bitstring.extract_int32_le_unsigned
                     __pabitstring_data_1141 __pabitstring_off_1142
                     __pabitstring_len_1143 32 in
               let __pabitstring_off_1142 = __pabitstring_off_1142 + 32
               and __pabitstring_len_1143 = __pabitstring_len_1143 - 32
               in
                 match v with
                 | word when true ->
                     (__pabitstring_result_1147 := Some (return (word, rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1147 := Some (Fail "read_elf64_sword_le");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1147 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 242, 2))))
  
let read_elf64_sword_be bs rest =
  let (__pabitstring_data_1148, __pabitstring_original_off_1151,
       __pabitstring_original_len_1152) =
    bs in
  let __pabitstring_off_1149 = __pabitstring_original_off_1151
  and __pabitstring_len_1150 = __pabitstring_original_len_1152 in
  let __pabitstring_off_aligned_1153 = (__pabitstring_off_1149 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1153;
     let __pabitstring_result_1154 = ref None
     in
       ((try
           (if __pabitstring_len_1150 >= 32
            then
              (let v =
                 if __pabitstring_off_aligned_1153
                 then
                   (let o = (__pabitstring_original_off_1151 lsr 3) + 0 in
                    let zero = Int32.of_int 0
                    in
                      Bitstring.extract_fastpath_int32_be_unsigned
                        __pabitstring_data_1148 o zero)
                 else
                   Bitstring.extract_int32_be_unsigned
                     __pabitstring_data_1148 __pabitstring_off_1149
                     __pabitstring_len_1150 32 in
               let __pabitstring_off_1149 = __pabitstring_off_1149 + 32
               and __pabitstring_len_1150 = __pabitstring_len_1150 - 32
               in
                 match v with
                 | word when true ->
                     (__pabitstring_result_1154 := Some (return (word, rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1154 := Some (Fail "read_elf64_sword_be");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1154 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 248, 2))))
  
let read_elf64_sword endian bs =
  let (cut, rest) = partition_bitstring 32 bs
  in
    match endian with
    | Little -> read_elf64_sword_le cut rest
    | Big -> read_elf64_sword_be cut rest
  
(** ELF extra wide word type:
  * 8 byte unsigned type on 64-bit architectures.
  *)
let read_elf64_xword_le bs rest =
  let (__pabitstring_data_1155, __pabitstring_original_off_1158,
       __pabitstring_original_len_1159) =
    bs in
  let __pabitstring_off_1156 = __pabitstring_original_off_1158
  and __pabitstring_len_1157 = __pabitstring_original_len_1159 in
  let __pabitstring_off_aligned_1160 = (__pabitstring_off_1156 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1160;
     let __pabitstring_result_1161 = ref None
     in
       ((try
           (if __pabitstring_len_1157 >= 64
            then
              (let v =
                 if __pabitstring_off_aligned_1160
                 then
                   (let o = (__pabitstring_original_off_1158 lsr 3) + 0 in
                    let zero = Int64.of_int 0
                    in
                      Bitstring.extract_fastpath_int64_le_unsigned
                        __pabitstring_data_1155 o zero)
                 else
                   Bitstring.extract_int64_le_unsigned
                     __pabitstring_data_1155 __pabitstring_off_1156
                     __pabitstring_len_1157 64 in
               let __pabitstring_off_1156 = __pabitstring_off_1156 + 64
               and __pabitstring_len_1157 = __pabitstring_len_1157 - 64
               in
                 match v with
                 | addr when true ->
                     (__pabitstring_result_1161 :=
                        Some (return ((Uint64.of_int64 addr), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1161 := Some (Fail "read_elf64_xword_le");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1161 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 265, 2))))
  
let read_elf64_xword_be bs rest =
  let (__pabitstring_data_1162, __pabitstring_original_off_1165,
       __pabitstring_original_len_1166) =
    bs in
  let __pabitstring_off_1163 = __pabitstring_original_off_1165
  and __pabitstring_len_1164 = __pabitstring_original_len_1166 in
  let __pabitstring_off_aligned_1167 = (__pabitstring_off_1163 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1167;
     let __pabitstring_result_1168 = ref None
     in
       ((try
           (if __pabitstring_len_1164 >= 64
            then
              (let v =
                 if __pabitstring_off_aligned_1167
                 then
                   (let o = (__pabitstring_original_off_1165 lsr 3) + 0 in
                    let zero = Int64.of_int 0
                    in
                      Bitstring.extract_fastpath_int64_be_unsigned
                        __pabitstring_data_1162 o zero)
                 else
                   Bitstring.extract_int64_be_unsigned
                     __pabitstring_data_1162 __pabitstring_off_1163
                     __pabitstring_len_1164 64 in
               let __pabitstring_off_1163 = __pabitstring_off_1163 + 64
               and __pabitstring_len_1164 = __pabitstring_len_1164 - 64
               in
                 match v with
                 | addr when true ->
                     (__pabitstring_result_1168 :=
                        Some (return ((Uint64.of_int64 addr), rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1168 := Some (Fail "read_elf64_xword_be");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1168 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 271, 2))))
  
let read_elf64_xword endian bs =
  let (cut, rest) = partition_bitstring 64 bs
  in
    match endian with
    | Little -> read_elf64_xword_le cut rest
    | Big -> read_elf64_xword_be cut rest
  
(** ELF signed extra wide word type:
  * 8 byte signed type on 64-bit architectures.
  *)
let read_elf64_sxword_le bs rest =
  let (__pabitstring_data_1169, __pabitstring_original_off_1172,
       __pabitstring_original_len_1173) =
    bs in
  let __pabitstring_off_1170 = __pabitstring_original_off_1172
  and __pabitstring_len_1171 = __pabitstring_original_len_1173 in
  let __pabitstring_off_aligned_1174 = (__pabitstring_off_1170 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1174;
     let __pabitstring_result_1175 = ref None
     in
       ((try
           (if __pabitstring_len_1171 >= 64
            then
              (let v =
                 if __pabitstring_off_aligned_1174
                 then
                   (let o = (__pabitstring_original_off_1172 lsr 3) + 0 in
                    let zero = Int64.of_int 0
                    in
                      Bitstring.extract_fastpath_int64_le_unsigned
                        __pabitstring_data_1169 o zero)
                 else
                   Bitstring.extract_int64_le_unsigned
                     __pabitstring_data_1169 __pabitstring_off_1170
                     __pabitstring_len_1171 64 in
               let __pabitstring_off_1170 = __pabitstring_off_1170 + 64
               and __pabitstring_len_1171 = __pabitstring_len_1171 - 64
               in
                 match v with
                 | addr when true ->
                     (__pabitstring_result_1175 := Some (return (addr, rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1175 := Some (Fail "read_elf64_sxword_le");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1175 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 288, 2))))
  
let read_elf64_sxword_be bs rest =
  let (__pabitstring_data_1176, __pabitstring_original_off_1179,
       __pabitstring_original_len_1180) =
    bs in
  let __pabitstring_off_1177 = __pabitstring_original_off_1179
  and __pabitstring_len_1178 = __pabitstring_original_len_1180 in
  let __pabitstring_off_aligned_1181 = (__pabitstring_off_1177 land 7) = 0
  in
    (ignore __pabitstring_off_aligned_1181;
     let __pabitstring_result_1182 = ref None
     in
       ((try
           (if __pabitstring_len_1178 >= 64
            then
              (let v =
                 if __pabitstring_off_aligned_1181
                 then
                   (let o = (__pabitstring_original_off_1179 lsr 3) + 0 in
                    let zero = Int64.of_int 0
                    in
                      Bitstring.extract_fastpath_int64_be_unsigned
                        __pabitstring_data_1176 o zero)
                 else
                   Bitstring.extract_int64_be_unsigned
                     __pabitstring_data_1176 __pabitstring_off_1177
                     __pabitstring_len_1178 64 in
               let __pabitstring_off_1177 = __pabitstring_off_1177 + 64
               and __pabitstring_len_1178 = __pabitstring_len_1178 - 64
               in
                 match v with
                 | addr when true ->
                     (__pabitstring_result_1182 := Some (return (addr, rest));
                      raise Exit)
                 | _ -> ())
            else ();
            __pabitstring_result_1182 := Some (Fail "read_elf64_sxword_be");
            raise Exit)
         with | Exit -> ());
        match !__pabitstring_result_1182 with
        | Some x -> x
        | None ->
            raise (Match_failure ("ml_bindings_camlp4_sugared.ml", 294, 2))))
  
let read_elf64_sxword endian bs =
  let (cut, rest) = partition_bitstring 64 bs
  in
    match endian with
    | Little -> read_elf64_sxword_le cut rest
    | Big -> read_elf64_sxword_be cut rest
  
(** Misc. string operations. *)
let split_string_on_char strings c =
  let enum = BatString.enum strings in
  let groups = BatEnum.group (fun char -> char <> c) enum in
  let enums = BatEnum.map BatString.of_enum groups in BatList.of_enum enums
  
let string_suffix index str =
  if (index < 0) || (index > (String.length str))
  then None
  else
    (try Some (String.sub str index ((String.length str) - index))
     with | _ -> None)
  

