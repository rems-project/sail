
(defvar sail2-mode-hook nil)

(add-to-list 'auto-mode-alist '("\\.sail\\'" . sail-mode))

(defconst sail2-keywords
  '("val" "function" "type" "struct" "union" "enum" "let" "var" "if" "then"
    "else" "match" "in" "return" "register" "ref" "forall" "operator" "effect"
    "overload" "cast" "sizeof" "constraint" "default" "assert" "newtype"
    "pure" "infixl" "infixr" "infix" "scattered" "end" "try" "catch" "and"
    "throw" "clause" "as" "repeat" "until" "while" "do" "foreach" "bitfield"))

(defconst sail2-kinds
  '("Int" "Type" "Order" "inc" "dec"
    "barr" "depend" "rreg" "wreg" "rmem" "rmemt" "wmv" "wmvt" "eamem" "wmem"
    "exmem" "undef" "unspec" "nondet" "escape"))

(defconst sail2-types
  '("vector" "int" "nat" "atom" "range" "unit" "bit" "real" "list" "bool" "string" "bits"
    "uint64_t" "int64_t" "bv_t" "mpz_t"))

(defconst sail2-special
  '("_prove" "create" "kill" "convert" "$define" "$include" "$ifdef" "$ifndef" "$else" "$endif"))

(defconst sail2-font-lock-keywords
  `((,(regexp-opt sail2-keywords 'symbols) . font-lock-keyword-face)
    (,(regexp-opt sail2-kinds 'symbols) . font-lock-builtin-face)
    (,(regexp-opt sail2-types 'symbols) . font-lock-type-face)
    (,(regexp-opt sail2-special 'symbols) . font-lock-preprocessor-face)
    ("\'[a-zA-z_]+" . font-lock-variable-name-face)
    ("\\_<\\([0-9]+\\|0b[0-9]+\\|0x[0-9a-fA-F]+\\|true\\|false\\|bitone\\|bitzero\\)\\_>\\|()" . font-lock-constant-face)))

(defconst sail2-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?> "." st)
    (modify-syntax-entry ?_ "w" st)
    (modify-syntax-entry ?' "w" st)
    (modify-syntax-entry ?* ". 23" st)
    (modify-syntax-entry ?/ ". 124b" st)
    (modify-syntax-entry ?\n "> b" st)
    st)
  "Syntax table for Sail2 mode")

(defun sail2-mode ()
  "Major mode for editing Sail Language files"
  (interactive)
  (kill-all-local-variables)
  (set-syntax-table sail2-mode-syntax-table)
  (setq font-lock-defaults '(sail2-font-lock-keywords))
  (setq major-mode 'sail2-mode)
  (setq mode-name "Sail2")
  (run-hooks 'sail2-mode-hook))

(provide 'sail2-mode)

