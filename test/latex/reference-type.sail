default Order dec

$include <flow.sail>
$include <vector_dec.sail>

type cap_uperms_width : Int = 4
let cap_uperms_width = sizeof(cap_uperms_width)

/*!
 * - Ref to [cap_uperms_width]
 * - Ref to [description][cap_uperms_width]
 * - Ref to [type description][type cap_uperms_width]
 * - Ref to % FIXME: this should be using type\_description [type_description][type_cap_uperms_width]
 * - Ref to \sailreftype{cap_uperms_width}{uperms\_width}
 * - Ref to \sailreftype{cap\_uperms\_width}{uperms\_width}
 */
function main() -> unit = return(())

/*!
 * - [NAME]
 * - [THIS]
 * - [NAME][NOT NAME]
 * - [THIS][NOT THIS]
 * - [NOT NAME][NAME]
 * - [NOT THIS][THIS]
 */
function function_with_underscores() -> unit = return(())
