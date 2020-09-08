To build:

cp ~/MiniSailPlus_win/tc_checker_rules.ml . && (cd .. && make )


To test e.g.

../../sail  -ddump_tc_ast_ott_raw x.ast -dtc_check ~/github/research/minisail/tests/01_basic_0.sail
