open Jib
include Visitor

class type jib_visitor = object
  method vid : Ast.id -> Ast.id option
  method vname : name -> name option
  method vctyp : ctyp -> ctyp visit_action
  method vcval : cval -> cval visit_action
  method vclexp : clexp -> clexp visit_action
  method vinstrs : instr list -> instr list visit_action
  method vinstr : instr -> instr visit_action
  method vcdef : cdef -> cdef visit_action
end

let visit_id vis id = Option.value ~default:id (vis#vid id)

let visit_name vis name = Option.value ~default:name (vis#vname name)

let rec visit_ctyp vis outer_ctyp =
  let aux vis no_change =
    match no_change with
    | CT_lint | CT_fint _ | CT_constant _ | CT_lbits | CT_sbits _ | CT_fbits _ | CT_unit | CT_bool | CT_bit | CT_string
    | CT_real | CT_float _ | CT_rounding_mode | CT_poly _ ->
        no_change
    | CT_tup ctyps ->
        let ctyps' = visit_ctyps vis ctyps in
        if ctyps == ctyps' then no_change else CT_tup ctyps'
    | CT_enum (id, members) ->
        let id' = visit_id vis id in
        let members' = map_no_copy (visit_id vis) members in
        if id == id' && members == members' then no_change else CT_enum (id', members')
    | CT_struct (id, fields) ->
        let id' = visit_id vis id in
        let fields' = map_no_copy (visit_binding vis) fields in
        if id == id' && fields == fields' then no_change else CT_struct (id', fields')
    | CT_variant (id, ctors) ->
        let id' = visit_id vis id in
        let ctors' = map_no_copy (visit_binding vis) ctors in
        if id == id' && ctors == ctors' then no_change else CT_variant (id', ctors')
    | CT_fvector (n, ctyp) ->
        let ctyp' = visit_ctyp vis ctyp in
        if ctyp == ctyp' then no_change else CT_fvector (n, ctyp')
    | CT_vector ctyp ->
        let ctyp' = visit_ctyp vis ctyp in
        if ctyp == ctyp' then no_change else CT_vector ctyp'
    | CT_list ctyp ->
        let ctyp' = visit_ctyp vis ctyp in
        if ctyp == ctyp' then no_change else CT_list ctyp'
    | CT_ref ctyp ->
        let ctyp' = visit_ctyp vis ctyp in
        if ctyp == ctyp' then no_change else CT_ref ctyp'
  in
  do_visit vis (vis#vctyp outer_ctyp) aux outer_ctyp

and visit_ctyps vis ctyps = map_no_copy (visit_ctyp vis) ctyps

and visit_binding vis ((id, ctyp) as binding) =
  let id' = visit_id vis id in
  let ctyp' = visit_ctyp vis ctyp in
  if id == id' && ctyp == ctyp' then binding else (id', ctyp')

let visit_ctype_def vis no_change =
  match no_change with
  | CTD_enum (id, members) ->
      let id' = visit_id vis id in
      let members' = map_no_copy (visit_id vis) members in
      if id == id' && members == members' then no_change else CTD_enum (id', members')
  | CTD_struct (id, fields) ->
      let id' = visit_id vis id in
      let fields' = map_no_copy (visit_binding vis) fields in
      if id == id' && fields == fields' then no_change else CTD_struct (id', fields')
  | CTD_variant (id, ctors) ->
      let id' = visit_id vis id in
      let ctors' = map_no_copy (visit_binding vis) ctors in
      if id == id' && ctors == ctors' then no_change else CTD_variant (id', ctors')

let rec visit_clexp vis outer_clexp =
  let aux vis no_change =
    match no_change with
    | CL_id (name, ctyp) ->
        let name' = visit_name vis name in
        let ctyp' = visit_ctyp vis ctyp in
        if name == name' && ctyp == ctyp' then no_change else CL_id (name', ctyp')
    | CL_rmw (name1, name2, ctyp) ->
        let name1' = visit_name vis name1 in
        let name2' = visit_name vis name2 in
        let ctyp' = visit_ctyp vis ctyp in
        if name1 == name1' && name2 == name2' && ctyp == ctyp' then no_change else CL_rmw (name1', name2', ctyp')
    | CL_field (clexp, id) ->
        let clexp' = visit_clexp vis clexp in
        let id' = visit_id vis id in
        if clexp == clexp' && id == id' then no_change else CL_field (clexp', id')
    | CL_addr clexp ->
        let clexp' = visit_clexp vis clexp in
        if clexp == clexp' then no_change else CL_addr clexp'
    | CL_tuple (clexp, n) ->
        let clexp' = visit_clexp vis clexp in
        if clexp == clexp' then no_change else CL_tuple (clexp', n)
    | CL_void -> no_change
  in
  do_visit vis (vis#vclexp outer_clexp) aux outer_clexp

let rec visit_cval vis outer_cval =
  let aux vis no_change =
    match no_change with
    | V_id (name, ctyp) ->
        let name' = visit_name vis name in
        let ctyp' = visit_ctyp vis ctyp in
        if name == name' && ctyp == ctyp' then no_change else V_id (name', ctyp')
    | V_lit (value, ctyp) ->
        let ctyp' = visit_ctyp vis ctyp in
        if ctyp == ctyp' then no_change else V_lit (value, ctyp')
    | V_tuple (cvals, ctyp) ->
        let cvals' = visit_cvals vis cvals in
        let ctyp' = visit_ctyp vis ctyp in
        if cvals == cvals' && ctyp == ctyp' then no_change else V_tuple (cvals', ctyp')
    | V_struct (fields, ctyp) ->
        let fields' = map_no_copy (visit_field vis) fields in
        let ctyp' = visit_ctyp vis ctyp in
        if fields == fields' && ctyp == ctyp' then no_change else V_struct (fields', ctyp')
    | V_ctor_kind (cval, (id, ctyps), ctyp) ->
        let cval' = visit_cval vis cval in
        let id' = visit_id vis id in
        let ctyps' = visit_ctyps vis ctyps in
        let ctyp' = visit_ctyp vis ctyp in
        if cval == cval' && id == id' && ctyps == ctyps' && ctyp == ctyp' then no_change
        else V_ctor_kind (cval', (id', ctyps'), ctyp')
    | V_ctor_unwrap (cval, (id, ctyps), ctyp) ->
        let cval' = visit_cval vis cval in
        let id' = visit_id vis id in
        let ctyps' = visit_ctyps vis ctyps in
        let ctyp' = visit_ctyp vis ctyp in
        if cval == cval' && id == id' && ctyps == ctyps' && ctyp == ctyp' then no_change
        else V_ctor_unwrap (cval', (id', ctyps'), ctyp')
    | V_tuple_member (cval, n, m) ->
        let cval' = visit_cval vis cval in
        if cval == cval' then no_change else V_tuple_member (cval', n, m)
    | V_call (op, cvals) ->
        let cvals' = visit_cvals vis cvals in
        if cvals == cvals' then no_change else V_call (op, cvals')
    | V_field (cval, id) ->
        let cval' = visit_cval vis cval in
        let id' = visit_id vis id in
        if cval == cval' && id == id' then no_change else V_field (cval', id')
  in
  do_visit vis (vis#vcval outer_cval) aux outer_cval

and visit_field vis ((id, cval) as field) =
  let id' = visit_id vis id in
  let cval' = visit_cval vis cval in
  if id == id' && cval == cval' then field else (id', cval')

and visit_cvals vis cvals = map_no_copy (visit_cval vis) cvals

let rec visit_instr vis outer_instr =
  let aux vis no_change =
    match no_change with
    | I_aux (I_decl (ctyp, name), aux) ->
        let ctyp' = visit_ctyp vis ctyp in
        let name' = visit_name vis name in
        if ctyp == ctyp' && name == name' then no_change else I_aux (I_decl (ctyp', name'), aux)
    | I_aux (I_init (ctyp, name, cval), aux) ->
        let ctyp' = visit_ctyp vis ctyp in
        let name' = visit_name vis name in
        let cval' = visit_cval vis cval in
        if ctyp == ctyp' && name == name' && cval == cval' then no_change else I_aux (I_init (ctyp', name', cval'), aux)
    | I_aux (I_jump (cval, label), aux) ->
        let cval' = visit_cval vis cval in
        if cval == cval' then no_change else I_aux (I_jump (cval', label), aux)
    | I_aux (I_goto _, aux) -> no_change
    | I_aux (I_label _, aux) -> no_change
    | I_aux (I_funcall (clexp, extern, (id, ctyps), cvals), aux) ->
        let clexp' = visit_clexp vis clexp in
        let id' = visit_id vis id in
        let ctyps' = visit_ctyps vis ctyps in
        let cvals' = visit_cvals vis cvals in
        if clexp == clexp' && id == id' && ctyps == ctyps' && cvals == cvals' then no_change
        else I_aux (I_funcall (clexp', extern, (id', ctyps'), cvals'), aux)
    | I_aux (I_copy (clexp, cval), aux) ->
        let clexp' = visit_clexp vis clexp in
        let cval' = visit_cval vis cval in
        if clexp == clexp' && cval == cval' then no_change else I_aux (I_copy (clexp', cval'), aux)
    | I_aux (I_clear (ctyp, name), aux) ->
        let ctyp' = visit_ctyp vis ctyp in
        let name' = visit_name vis name in
        if ctyp == ctyp' && name == name' then no_change else I_aux (I_clear (ctyp', name'), aux)
    | I_aux (I_undefined ctyp, aux) ->
        let ctyp' = visit_ctyp vis ctyp in
        if ctyp == ctyp' then no_change else I_aux (I_undefined ctyp', aux)
    | I_aux (I_exit _, aux) -> no_change
    | I_aux (I_end name, aux) ->
        let name' = visit_name vis name in
        if name == name' then no_change else I_aux (I_end name', aux)
    | I_aux (I_comment _, aux) -> no_change
    | I_aux (I_raw _, aux) -> no_change
    | I_aux (I_return cval, aux) ->
        let cval' = visit_cval vis cval in
        if cval == cval' then no_change else I_aux (I_return cval', aux)
    | I_aux (I_if (cval, then_instrs, else_instrs, ctyp), aux) ->
        let cval' = visit_cval vis cval in
        let then_instrs' = visit_instrs vis then_instrs in
        let else_instrs' = visit_instrs vis else_instrs in
        let ctyp' = visit_ctyp vis ctyp in
        if cval == cval' && then_instrs == then_instrs' && else_instrs == else_instrs' && ctyp == ctyp' then no_change
        else I_aux (I_if (cval', then_instrs', else_instrs', ctyp'), aux)
    | I_aux (I_block instrs, aux) ->
        let instrs' = visit_instrs vis instrs in
        if instrs == instrs' then no_change else I_aux (I_block instrs', aux)
    | I_aux (I_try_block instrs, aux) ->
        let instrs' = visit_instrs vis instrs in
        if instrs == instrs' then no_change else I_aux (I_try_block instrs', aux)
    | I_aux (I_throw cval, aux) ->
        let cval' = visit_cval vis cval in
        if cval == cval' then no_change else I_aux (I_throw cval', aux)
    | I_aux (I_reset (ctyp, name), aux) ->
        let ctyp' = visit_ctyp vis ctyp in
        let name' = visit_name vis name in
        if ctyp == ctyp' && name == name' then no_change else I_aux (I_reset (ctyp', name'), aux)
    | I_aux (I_reinit (ctyp, name, cval), aux) ->
        let ctyp' = visit_ctyp vis ctyp in
        let name' = visit_name vis name in
        let cval' = visit_cval vis cval in
        if ctyp == ctyp' && name == name' && cval == cval' then no_change
        else I_aux (I_reinit (ctyp', name', cval'), aux)
  in
  do_visit vis (vis#vinstr outer_instr) aux outer_instr

and visit_instrs vis outer_instrs =
  let aux vis no_change =
    match no_change with
    | instr :: instrs ->
        let instr' = visit_instr vis instr in
        let instrs' = visit_instrs vis instrs in
        if instr == instr' && instrs == instrs' then no_change else instr' :: instrs'
    | [] -> []
  in
  do_visit vis (vis#vinstrs outer_instrs) aux outer_instrs

let rec visit_cdef vis outer_cdef =
  let aux vis no_change =
    match no_change with
    | CDEF_register (id, ctyp, instrs) ->
        let id' = visit_id vis id in
        let ctyp' = visit_ctyp vis ctyp in
        let instrs' = visit_instrs vis instrs in
        if id == id' && ctyp == ctyp' && instrs == instrs' then no_change else CDEF_register (id', ctyp', instrs')
    | CDEF_type ctd ->
        let ctd' = visit_ctype_def vis ctd in
        if ctd == ctd' then no_change else CDEF_type ctd'
    | CDEF_let (n, bindings, instrs) ->
        let bindings' = map_no_copy (visit_binding vis) bindings in
        let instrs' = visit_instrs vis instrs in
        if bindings == bindings' && instrs == instrs' then no_change else CDEF_let (n, bindings', instrs')
    | CDEF_val (id, extern, ctyps, ctyp) ->
        let id' = visit_id vis id in
        let ctyps' = visit_ctyps vis ctyps in
        let ctyp' = visit_ctyp vis ctyp in
        if id == id' && ctyps == ctyps' && ctyp == ctyp' then no_change else CDEF_val (id', extern, ctyps', ctyp')
    | CDEF_fundef (id, ret_id, params, instrs) ->
        let id' = visit_id vis id in
        let ret_id' = map_no_copy_opt (visit_id vis) ret_id in
        let params' = map_no_copy (visit_id vis) params in
        let instrs' = visit_instrs vis instrs in
        if id == id' && ret_id == ret_id' && params == params' && instrs == instrs' then no_change
        else CDEF_fundef (id', ret_id', params', instrs')
    | CDEF_startup (id, instrs) ->
        let id' = visit_id vis id in
        let instrs' = visit_instrs vis instrs in
        if id == id' && instrs == instrs' then no_change else CDEF_startup (id', instrs')
    | CDEF_finish (id, instrs) ->
        let id' = visit_id vis id in
        let instrs' = visit_instrs vis instrs in
        if id == id' && instrs == instrs' then no_change else CDEF_finish (id', instrs')
    | CDEF_pragma (_, _) -> no_change
  in
  do_visit vis (vis#vcdef outer_cdef) aux outer_cdef

let visit_cdefs vis cdefs = map_no_copy (visit_cdef vis) cdefs

class empty_jib_visitor : jib_visitor =
  object
    method vid _ = None
    method vname _ = None
    method vctyp _ = DoChildren
    method vcval _ = DoChildren
    method vclexp _ = DoChildren
    method vinstrs _ = DoChildren
    method vinstr _ = DoChildren
    method vcdef _ = DoChildren
  end
