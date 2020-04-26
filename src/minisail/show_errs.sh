echo "Total Defs: " `fgrep -c "CHECK DEF:" ~/a`
echo "Total Fails: " `fgrep -c "CHECK DEF: Failed" ~/a`
echo "check_pat tuple: " `fgrep -c "check_pat Tuple" ~/a`
echo "tuple type unexpected: " `fgrep -c "Pp_tup. type unexpected" ~/a`

echo "function args: " `fgrep -c "FunctionArgWrong" ~/a`
echo "invalid decl / shadowing " `fgrep -c "invalid declaration" ~/a`

#echo "not implemented: "  `fgrep -c "Not implemented" ~/a`
echo "unknown fun: " `fgrep -c "CHECK DEF: failed. Function " ~/a`
echo "general check expr: " `fgrep -c "general check expr" ~/a`
echo "assign unit type: " `fgrep -c "assign unit type" ~/a`
echo "no valspec: " `fgrep -c "No valspec" ~/a`
echo "not impl infer case: " `fgrep -c "infer case  expr" ~/a`
echo "not impl throw: " `fgrep -c "therow expr" ~/a`
echo "not impl record update: " `fgrep -c "record update" ~/a`
echo "not impl cons expr: " `fgrep -c "cons expr" ~/a`
echo "pp_id constructor: " `fgrep -c "Pp_id / constructor" ~/a`
echo "SMT Related"
echo "Z3 result unknown: " `fgrep -c "Z3 Result: unknown" ~/a`
echo "segmentation fault: " `fgrep -c "Segmentation" ~/a`
echo "unknown constant: " `fgrep -c "unknown constant" ~/a`
echo "already declared: " `fgrep -c "already declared" ~/a`
