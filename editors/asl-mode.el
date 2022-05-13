; quick-and-dirty emacs mode for ASL, taking the keywords from the ott-generated lexer of asl-interpreter

(define-generic-mode 'asl-mode
  '( "////" )
  '(
; extra keywords not in asli lexer
    "bit"
    "boolean"
    "integer"
; asli lexer keywords
"__unpredictable_unless"
"__instruction_set"
"CONSTRAINED_UNPREDICTABLE"
"__ExceptionTaken"
"__UNPREDICTABLE"
"__operator1"
"__operator2"
"IMPLEMENTATION_DEFINED"
"__conditional"
"__instruction"
"__UNALLOCATED"
"__postdecode"
"__readwrite"
"__encoding"
"__function"
"__newevent"
"__register"
"__builtin"
"__execute"
"__config"
"__decode"
"__newmap"
"__opcode"
"__array"
"__event"
"__field"
"__guard"
"__write"
"__map"
"__NOP"
"UNPREDICTABLE"
"enumeration"
"otherwise"
"UNDEFINED"
"constant"
"IMPLIES"
"UNKNOWN"
"assert"
"DEDENT"
"downto"
"INDENT"
"record"
"repeat"
"return"
"typeof"
"array"
"catch"
"elsif"
"throw"
"until"
"while"
"bits"
"case"
"else"
"QUOT"
"then"
"type"
"when"
"AND"
"DIV"
"EOL"
"EOR"
"for"
"IFF"
"MOD"
"NOT"
"REM"
"SEE"
"try"
"do"
"if"
"IN"
"is"
"of"
"OR"
"to"
)
  '(
; old ott rules
;    ("\\[\\[.+\\]\\]" . 'font-lock-warning-face)
;    ("\\[\\[[^\\]]+\\]\\]" . 'font-lock-warning-face)
;    ("{{\\([^{}]+{[^{}]*}\\)*[^{}]*}}" . 'font-lock-doc-face)
;    ("{{[^}]+}}" . 'font-lock-doc-face)
; asli lexer symbols
; ("&&" . 'font-lock-keyword-face)
; ("{{" . 'font-lock-keyword-face)
; ("}}" . 'font-lock-keyword-face)
; ("+:" . 'font-lock-keyword-face)
; ("&"  . 'font-lock-keyword-face)
; ("++" . 'font-lock-keyword-face)
; (";"  . 'font-lock-keyword-face)
; ("!=" . 'font-lock-keyword-face)
; ("||" . 'font-lock-keyword-face)
; (".." . 'font-lock-keyword-face)
; ("{"  . 'font-lock-keyword-face)
; ("["  . 'font-lock-keyword-face)
; ("("  . 'font-lock-keyword-face)
; ("}"  . 'font-lock-keyword-face)
; ("]"  . 'font-lock-keyword-face)
; (")"  . 'font-lock-keyword-face)
; ("^"  . 'font-lock-keyword-face)
; (":"  . 'font-lock-keyword-face)
; (","  . 'font-lock-keyword-face)
; ("==" . 'font-lock-keyword-face)
; ("=>" . 'font-lock-keyword-face)
; (">=" . 'font-lock-keyword-face)
; (">>" . 'font-lock-keyword-face)
; ("<=" . 'font-lock-keyword-face)
; ("<<" . 'font-lock-keyword-face)
; ("-"  . 'font-lock-keyword-face)
; ("/"  . 'font-lock-keyword-face)
; ("!"  . 'font-lock-keyword-face)
; ("+"  . 'font-lock-keyword-face)
; ("*"  . 'font-lock-keyword-face)
; ("."  . 'font-lock-keyword-face)
; ("="  . 'font-lock-keyword-face)
; (">"  . 'font-lock-keyword-face)
; ("<"  . 'font-lock-keyword-face)
    )
    (list "\\.asl\\'")
;  '(".keymap\\'" ".map\\'")
  nil
  "Major mode for editing asl format files.")


;    ("\\%.*" . 'font-lock-doc-face)

(provide 'asl-mode)


; other asli lexer rules    
; | '"' [^'"']* '"' as stringLit
; | '\'' ['0' '1'     ' ']* '\'' as bitsLit
; | '\'' ['0' '1' 'x' ' ']* '\'' as maskLit
; | ['0'-'9']+ '.' ['0'-'9']+ as realLit
; | '0''x'['0'-'9' 'A' - 'F' 'a'-'f' '_']+ as hexLit
; | ['0'-'9']+ as intLit
; | ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']* as typeid
; | ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']* as id
