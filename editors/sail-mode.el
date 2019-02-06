;;; sail-mode.el --- Major mode for editing .sail files -*- lexical-binding: t; -*-

;; Copyright (C) 2013-2018 The Sail Authors
;;
;; Author: The Sail Authors
;; URL: http://github.com/rems-project/sail
;; Package-Requires: ((emacs "25"))
;; Version: 0.0.1
;; Keywords: language

;; This file is not part of GNU Emacs.

;;; License:

;; 2-Clause BSD License (See LICENSE file in Sail repository)

;;; Commentary:

;; This mode is only compatible with new, recent of the new Sail on the "sail2" branch.

;;; Code:

(require 'easymenu)

(defvar sail2-mode-hook nil)

(add-to-list 'auto-mode-alist '("\\.sail\\'" . sail2-mode))

(defconst sail2-keywords
  '("val" "function" "type" "struct" "union" "enum" "let" "var" "if" "then" "by"
    "else" "match" "in" "return" "register" "ref" "forall" "operator" "effect"
    "overload" "cast" "sizeof" "constant" "constraint" "default" "assert" "newtype" "from"
    "pure" "infixl" "infixr" "infix" "scattered" "end" "try" "catch" "and" "to"
    "throw" "clause" "as" "repeat" "until" "while" "do" "foreach" "bitfield"
    "mapping" "where" "with" "implicit"))

(defconst sail2-kinds
  '("Int" "Type" "Order" "Bool" "inc" "dec"
    "barr" "depend" "rreg" "wreg" "rmem" "rmemt" "wmv" "wmvt" "eamem" "wmem"
    "exmem" "undef" "unspec" "nondet" "escape" "configuration"))

(defconst sail2-types
  '("vector" "int" "nat" "atom" "range" "unit" "bit" "real" "list" "bool" "string" "bits" "option"
    "uint64_t" "int64_t" "bv_t" "mpz_t"))

(defconst sail2-special
  '("_prove" "_not_prove" "create" "kill" "convert" "undefined"
    "$define" "$include" "$ifdef" "$ifndef" "$else" "$endif" "$option" "$optimize" "$latex"))

(defconst sail2-font-lock-keywords
  `((,(regexp-opt sail2-keywords 'symbols) . font-lock-keyword-face)
    (,(regexp-opt sail2-kinds 'symbols) . font-lock-builtin-face)
    (,(regexp-opt sail2-types 'symbols) . font-lock-type-face)
    (,(regexp-opt sail2-special 'symbols) . font-lock-preprocessor-face)
    ("~" . font-lock-negation-char-face)
    ("\\(::\\)<" 1 font-lock-keyword-face)
    ("@" . font-lock-preprocessor-face)
    ("<->" . font-lock-negation-char-face)
    ("\'[a-zA-Z0-9_]+" . font-lock-variable-name-face)
    ("\\([a-zA-Z0-9_]+\\)(" 1 font-lock-function-name-face)
    ("function \\([a-zA-Z0-9_]+\\)" 1 font-lock-function-name-face)
    ("val \\([a-zA-Z0-9_]+\\)" 1 font-lock-function-name-face)
    ("\\_<\\([0-9]+\\|0b[0-9_]+\\|0x[0-9a-fA-F_]+\\|true\\|false\\|bitone\\|bitzero\\)\\_>\\|()" . font-lock-constant-face)))

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
  (use-local-map sail-mode-map)
  (sail-build-menu)
  (setq font-lock-defaults '(sail2-font-lock-keywords))
  (setq comment-start-skip "\\(//+\\|/\\*+\\)\\s *")
  (setq comment-start "/*")
  (setq comment-end "*/")
  (setq major-mode 'sail2-mode)
  (setq mode-name "Sail2")
  (run-hooks 'sail2-mode-hook))

(defvar sail-process nil)

(defun sail-filter (proc string)
  (when (buffer-live-p (process-buffer proc))
    (with-current-buffer (process-buffer proc)
      (let ((moving (= (point) (process-mark proc))))
	(save-excursion
	  ;; Insert the text, advancing the process marker.
	  (goto-char (process-mark proc))
	  (insert string)
	  (set-marker (process-mark proc) (point)))
	(if moving (goto-char (process-mark proc)))))
    (eval (car (read-from-string string)))))

(defun sail-start ()
  "start Sail interactive mode"
  (interactive)
  (setq sail-process (start-process "sail" "Sail" "sail" "-i" "-emacs"))
  (set-process-filter sail-process 'sail-filter))

(defun sail-quit ()
  "quit Sail interactive mode"
  (interactive)
  (when sail-process
    (process-send-string sail-process ":quit\n")
    (setq sail-process nil)))

(defun sail-error-region (begin end text)
  (progn
    (let ((overlay (make-overlay begin end)))
      (overlay-put overlay 'face 'error)
      (overlay-put overlay 'help-echo text)
      (setq mark-active nil))))

(defun sail-error (l1 c1 l2 c2 text)
  (let ((begin (save-excursion
		 (goto-line l1)
		 (forward-char c1)
		 (point)))
	(end (save-excursion
	       (goto-line l2)
	       (forward-char c2)
	       (point))))
    (sail-error-region begin end text)
    (message text)))

(defun sail-test ()
  (interactive)
  (sail-error 6 18 6 19 "error message\ntooltip"))

(defun sail-load ()
  "load a Sail file"
  (interactive)
  (if (null sail-process)
      (error "No sail process (call sail-start)")
    (progn
      (remove-overlays)
      (process-send-string sail-process ":unload\n")
      (process-send-string sail-process (mapconcat 'identity `(":load " ,buffer-file-name "\n") "")))))

(defvar sail-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-s") 'sail-start)
    (define-key map (kbd "C-c C-l") 'sail-load)
    (define-key map (kbd "C-c C-q") 'sail-quit)
    map))

(defun sail-build-menu ()
  (easy-menu-define
    sail-mode-menu (list sail-mode-map)
    "Sail Mode Menu."
    '("Sail"
      ["Start" sail-start t]
      ["Quit" sail-quit t]
      ["Check buffer" sail-load t]))
  (easy-menu-add sail-mode-menu))

(provide 'sail2-mode)

;;; sail-mode.el ends here
