open Jib

type 'a visit_action =
  | SkipChildren  (** Do not visit the children. Return the node as it is. *)
  | DoChildren
      (** Continue with the children of this node. Rebuild the node on
     return if any of the children changes (use == test) *)
  | ChangeTo of 'a  (** Replace the expression with the given one *)
  | ChangeDoChildrenPost of 'a * ('a -> 'a)
      (** First consider that the entire exp is replaced by the first
     parameter. Then continue with the children. On return rebuild the
     node if any of the children has changed and then apply the
     function on the node *)

val change_do_children : 'a -> 'a visit_action

val map_no_copy : ('a -> 'a) -> 'a list -> 'a list

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

class empty_jib_visitor : jib_visitor

val visit_ctyp : jib_visitor -> ctyp -> ctyp

val visit_cval : jib_visitor -> cval -> cval

val visit_clexp : jib_visitor -> clexp -> clexp

val visit_instr : jib_visitor -> instr -> instr

val visit_instrs : jib_visitor -> instr list -> instr list

val visit_cdef : jib_visitor -> cdef -> cdef

val visit_cdefs : jib_visitor -> cdef list -> cdef list
