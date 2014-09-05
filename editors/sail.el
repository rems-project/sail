;;; sail.el --- Sail mode for Emacs.
;;; based on tuareg.el which was
    ;; Copyright (C) 1997-2006 Albert Cohen, all rights reserved.
    ;; Copyright (C) 2009-2010 Jane Street Holding, LLC.
    ;; Licensed under the GNU General Public License.

    ;; Author: Albert Cohen <Albert.Cohen@inria.fr>
    ;;         Sam Steingold <sds@gnu.org>
    ;;	       Christophe Troestler <Christophe.Troestler@umons.ac.be>
    ;;	       Till Varoquaux <till@pps.jussieu.fr>
    ;;	       Sean McLaughlin <seanmcl@gmail.com>
    ;; Created: 8 Jan 1997
    ;; Version: 2.0.5
    ;; URL: http://forge.ocamlcore.org/projects/tuareg/
    ;; EmacsWiki: TuaregMode

(eval-when-compile (require 'cl))
(require 'easymenu)

(defalias 'sail-match-string
  (if (fboundp 'match-string-no-properties)
      'match-string-no-properties
    'match-string))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                       User customizable variables

;; Use the standard `customize' interface or `sail-mode-hook' to
;; Configure these variables

(require 'custom)

(defgroup sail nil
  "Support for the Sail language."
  :group 'languages)

;; Comments

(defcustom sail-indent-leading-comments t
  "*If true, indent leading comment lines (starting with `(*') like others."
  :group 'sail :type 'boolean)

(defcustom sail-indent-comments t
  "*If true, automatically align multi-line comments."
  :group 'sail :type 'boolean)

(defcustom sail-comment-end-extra-indent 0
  "*How many spaces to indent a leading comment end `*)'.
If you expect comments to be indented like
        (*
          ...
         *)
even without leading `*', use `sail-comment-end-extra-indent' = 1."
  :group 'sail
  :type '(radio :extra-offset 8
                :format "%{Comment End Extra Indent%}:
   Comment alignment:\n%v"
                (const :tag "align with `(' in comment opening" 0)
                (const :tag "align with `*' in comment opening" 1)
                (integer :tag "custom alignment" 0)))

(defcustom sail-support-leading-star-comments t
  "*Enable automatic intentation of comments of the form
        (*
         * ...
         *)
Documentation comments (** *) are not concerned by this variable
unless `sail-leading-star-in-doc' is also set.

If you do not set this variable and still expect comments to be
indented like
        (*
          ...
         *)
\(without leading `*'), set `sail-comment-end-extra-indent' to 1."
  :group 'sail :type 'boolean)

(defcustom sail-leading-star-in-doc nil
  "*Enable automatic intentation of documentation comments of the form
        (**
         * ...
         *)"
  :group 'sail :type 'boolean)

;; Indentation defaults

(defcustom sail-default-indent 2
  "*Default indentation.

Global indentation variable (large values may lead to indentation overflows).
When no governing keyword is found, this value is used to indent the line
if it has to."
  :group 'sail :type 'integer)

(defcustom sail-let-always-indent t
  "*If true, enforce indentation is at least `sail-let-indent' after a `let'.

As an example, set it to false when you have `sail-with-indent' set to 0,
and you want `let x = match ... with' and `match ... with' indent the
same way."
  :group 'sail :type 'boolean)

(defcustom sail-case-extra-unindent sail-default-indent
  "*Extra backward indent for Sail lines starting with the `case' operator.

It is NOT the variable controlling the indentation of the `case' itself:
this value is automatically added to `switch' to leave enough space for `case' backward
indentation."

  :group 'sail :type 'integer)

(defcustom sail-enum-indent sail-default-indent
  "*How many spaces to indent from an `enumerate' keyword."
  :group 'sail :type 'integer)

(defcustom sail-struct-struct-indent sail-default-indent
  "*How many spaces to indent from a `struct' keyword."
  :group 'sail :type 'integer)

(defcustom sail-foreach-indent sail-default-indent
  "*How many spaces to indent from a `foreach' keyword."
  :group 'sail :type 'integer)

(defcustom sail-function-indent sail-default-indent
  "*How many spaces to indent from a `function' keyword."
  :group 'sail :type 'integer)

(defcustom sail-if-then-else-indent sail-default-indent
  "*How many spaces to indent from an `if', `then' or `else' keyword."
  :group 'sail :type 'integer)

(defcustom sail-let-indent sail-default-indent
  "*How many spaces to indent from a `let' keyword."
  :group 'sail :type 'integer)

(defcustom sail-in-indent sail-default-indent
  "*How many spaces to indent from a `in' keyword."
  :group 'sail :type 'integer)

(defcustom sail-switch-indent sail-default-indent
  "*How many spaces to indent from a `switch' keyword."
  :group 'sail :type 'integer)

(defcustom sail-with-indent sail-default-indent
  "*How many spaces to indent from a `with' keyword."
  :group 'sail :type 'integer)

(defcustom sail-typedef-indent sail-default-indent
  "*How many spaces to indent from a `typedef' keyword."
  :group 'sail :type 'integer)

(defcustom sail-val-indent sail-default-indent
  "*How many spaces to indent from a `val' keyword."
  :group 'sail :type 'integer)

;; Automatic indentation
;; Using abbrev-mode and electric keys

(defcustom sail-use-abbrev-mode t
  "*Non-nil means electrically indent lines starting with leading keywords.
It makes use of `abbrev-mode'.

Many people find eletric keywords irritating, so you can disable them by
setting this variable to nil."
  :group 'sail :type 'boolean
  :set '(lambda (var val)
          (setq sail-use-abbrev-mode val)
          (abbrev-mode val)))

(defcustom sail-electric-indent t
  "*Non-nil means electrically indent lines starting with `|]', '||]', '>', `)', `]' or `}'.

Many people find eletric keys irritating, so you can disable them in
setting this variable to nil."
  :group 'sail :type 'boolean)

(defcustom sail-electric-close-list t
  "*Non-nil means electrically insert `||' before a list-closing `]'.

Many people find eletric keys irritating, so you can disable them in
setting this variable to nil. You should probably have this on,
though, if you also have `sail-electric-indent' on."
  :group 'sail :type 'boolean)


(defvar sail-options-list
  '(("Automatic indentation of leading keywords" . 'sail-use-abbrev-mode)
    ("Automatic indentation of ), ], |], ||], >, and }" . 'sail-electric-indent)
    ("Automatic matching of [||" . 'sail-electric-close-list)
    "---"
    ("Indent body of comments" . 'sail-indent-comments)
    ("Indent first line of comments" . 'sail-indent-leading-comments)
    ("Leading-`*' comment style" . 'sail-support-leading-star-comments))
  "*List of menu-configurable Sail options.")

(eval-and-compile
  (defconst sail-use-syntax-ppss (fboundp 'syntax-ppss)
    "*If nil, use our own parsing and caching."))

(defgroup sail-faces nil
  "Special faces for the Sail mode."
  :group 'sail)

(defconst sail-faces-inherit-p
  (and (boundp 'face-attribute-name-alist)
       (assq :inherit face-attribute-name-alist)))

(defface sail-font-lock-governing-face
  '((((background light)) (:foreground "blue" :bold t))
    (t (:foreground "orange" :bold t)))
  "Face description for governing/leading keywords."
  :group 'sail-faces)
(defvar sail-font-lock-governing-face
  'sail-font-lock-governing-face)

(defface sail-font-lock-operator-face
  '((((background light)) (:foreground "brown"))
    (t (:foreground "khaki")))
  "Face description for all operators."
  :group 'sail-faces)
(defvar sail-font-lock-operator-face
  'sail-font-lock-operator-face)

(defface sail-font-lock-error-face
  '((t (:foreground "yellow" :background "red" :bold t)))
  "Face description for all errors reported to the source."
  :group 'sail-faces)
(defvar sail-font-lock-error-face
  'sail-font-lock-error-face)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                            Support definitions

(defun sail-leading-star-p ()
  (and sail-support-leading-star-comments
       (save-excursion ; this function does not make sense outside of a comment
         (sail-beginning-of-literal-or-comment)
         (and (or sail-leading-star-in-doc
                  (not (looking-at "(\\*[Tt][Ee][Xx]\\|(\\*\\*")))
              (progn
                (forward-line 1)
                (back-to-indentation)
                (looking-at "\\*[^)]"))))))

(defun sail-auto-fill-insert-leading-star (&optional leading-star)
  (let ((point-leading-comment (looking-at "(\\*")) (return-leading nil))
    (save-excursion
      (back-to-indentation)
      (when sail-electric-indent
        (when (and (sail-in-comment-p)
                   (or leading-star
                       (sail-leading-star-p)))
          (unless (looking-at "(?\\*")
            (insert-before-markers "* "))
          (setq return-leading t))
        (unless point-leading-comment
          ;; Use optional argument to break recursion
          (sail-indent-command t))))
    return-leading))

(defun sail-auto-fill-function ()
  (unless (sail-in-literal-p)
    (let ((leading-star
           (and (not (char-equal ?\n last-command-event))
                (sail-auto-fill-insert-leading-star))))
      (do-auto-fill)
      (unless (char-equal ?\n last-command-event)
        (sail-auto-fill-insert-leading-star leading-star)))))

;; these two functions are different from the standard
;; in that they do NOT signal errors beginning-of-buffer and end-of-buffer
(defun sail-forward-char (&optional step)
  (if step (goto-char (+ (point) step))
    (goto-char (1+ (point)))))

(defun sail-backward-char (&optional step)
  (if step (goto-char (- (point) step))
    (goto-char (1- (point)))))

(defun sail-in-indentation-p ()
  "Return non-nil if all chars between beginning of line and point are blanks."
  (save-excursion
    (skip-chars-backward " \t")
    (bolp)))

(defvar sail-cache-stop (point-min))
(make-variable-buffer-local 'sail-cache-stop)
(defvar sail-cache nil)
(make-variable-buffer-local 'sail-cache)
(defvar sail-cache-local nil)
(make-variable-buffer-local 'sail-cache-local)
(defvar sail-cache-last-local nil)
(make-variable-buffer-local 'sail-cache-last-local)
(defvar sail-last-loc (cons nil nil))

;; PPSS definitions
(defun sail-ppss-in-literal-or-comment () (error "sail uses PPSS"))
(defun sail-ppss-fontify (beg end) (error "sail uses PPSS"))
(defun sail-ppss-in-literal-p ()
  "Returns non-nil if point is inside a Sail literal."
  (nth 3 (syntax-ppss)))
(defun sail-ppss-in-comment-p ()
  "Returns non-nil if point is inside or right before a Sail comment."
  (or (nth 4 (syntax-ppss))
      (looking-at "[ \t]*(\\*")))
(defun sail-ppss-in-literal-or-comment-p ()
  "Returns non-nil if point is inside a Sail literal or comment."
  (nth 8 (syntax-ppss)))
(defun sail-ppss-beginning-of-literal-or-comment ()
  "Skips to the beginning of the current literal or comment (or buffer)."
  (interactive)
  (goto-char (or (nth 8 (syntax-ppss)) (point))))
(defun sail-ppss-beginning-of-literal-or-comment-fast ()
  (goto-char (or (nth 8 (syntax-ppss)) (point-min))))
;; FIXME: not clear if moving out of a string/comment counts as 1 or no.
(defalias 'sail-backward-up-list 'backward-up-list)

;; non-PPSS definitions
(defun sail-!ppss-in-literal-p ()
  "Return non-nil if point is inside a Sail literal."
  (car (sail-in-literal-or-comment)))
(defun sail-!ppss-in-comment-p ()
  "Return non-nil if point is inside a Sail comment."
  (cdr (sail-in-literal-or-comment)))
(defun sail-!ppss-in-literal-or-comment-p ()
  "Return non-nil if point is inside a Sail literal or comment."
  (sail-in-literal-or-comment)
  (or (car sail-last-loc) (cdr sail-last-loc)))
(defun sail-!ppss-in-literal-or-comment ()
  "Return the pair `((sail-in-literal-p) . (sail-in-comment-p))'."
  (if (and (<= (point) sail-cache-stop) sail-cache)
      (progn
        (if (or (not sail-cache-local) (not sail-cache-last-local)
                (and (>= (point) (caar sail-cache-last-local))))
            (setq sail-cache-local sail-cache))
        (while (and sail-cache-local (< (point) (caar sail-cache-local)))
          (setq sail-cache-last-local sail-cache-local
                sail-cache-local (cdr sail-cache-local)))
        (setq sail-last-loc
              (if sail-cache-local
                  (cons (eq (cadar sail-cache-local) 'b)
                        (> (cddar sail-cache-local) 0))
                  (cons nil nil))))
    (let ((flag t) (op (point)) (mp (min (point) (1- (point-max))))
          (balance 0) (end-of-comment nil))
      (while (and sail-cache (<= sail-cache-stop (caar sail-cache)))
        (setq sail-cache (cdr sail-cache)))
      (if sail-cache
          (if (eq (cadar sail-cache) 'b)
              (progn
                (setq sail-cache-stop (1- (caar sail-cache)))
                (goto-char sail-cache-stop)
                (setq balance (cddar sail-cache))
                (setq sail-cache (cdr sail-cache)))
            (setq balance (cddar sail-cache))
            (setq sail-cache-stop (caar sail-cache))
            (goto-char sail-cache-stop)
            (skip-chars-forward "("))
          (goto-char (point-min)))
      (skip-chars-backward "\\\\*")
      (while flag
        (if end-of-comment (setq balance 0 end-of-comment nil))
        (skip-chars-forward "^\\\\'`\"(\\*")
        (cond
          ((looking-at "\\\\")
           (sail-forward-char 2))
          ((looking-at "'\\([^\n\\']\\|\\\\[^ \t\n][^ \t\n]?[^ \t\n]?\\)'")
           (setq sail-cache (cons (cons (1+ (point)) (cons 'b balance))
				  sail-cache))
           (goto-char (match-end 0))
           (setq sail-cache (cons (cons (point) (cons 'e balance))
				  sail-cache)))
          ((looking-at "\"")
           (sail-forward-char)
           (setq sail-cache (cons (cons (point) (cons 'b balance))
				  sail-cache))
           (skip-chars-forward "^\\\\\"")
           (while (looking-at "\\\\")
             (sail-forward-char 2) (skip-chars-forward "^\\\\\""))
           (sail-forward-char)
           (setq sail-cache (cons (cons (point) (cons 'e balance))
				  sail-cache)))
          ((looking-at "(\\*")
           (setq balance (1+ balance))
           (setq sail-cache (cons (cons (point) (cons nil balance))
				  sail-cache))
           (sail-forward-char 2))
          ((looking-at "\\*)")
           (sail-forward-char 2)
           (if (> balance 1)
               (progn
                 (setq balance (1- balance))
                 (setq sail-cache (cons (cons (point) (cons nil balance))
					sail-cache)))
	     (setq end-of-comment t)
	     (setq sail-cache (cons (cons (point) (cons nil 0))
				    sail-cache))))
          (t (sail-forward-char)))
        (setq flag (<= (point) mp)))
      (setq sail-cache-local sail-cache
            sail-cache-stop (point))
      (goto-char op)
      (if sail-cache (sail-in-literal-or-comment)
          (setq sail-last-loc (cons nil nil))
          sail-last-loc))))
(defun sail-!ppss-beginning-of-literal-or-comment ()
  "Skips to the beginning of the current literal or comment (or buffer)."
  (interactive)
  (when (sail-in-literal-or-comment-p)
    (sail-beginning-of-literal-or-comment-fast)))

(defun sail-!ppss-beginning-of-literal-or-comment-fast ()
  (while (and sail-cache-local
              (or (eq 'b (cadar sail-cache-local))
                  (> (cddar sail-cache-local) 0)))
    (setq sail-cache-last-local sail-cache-local
          sail-cache-local (cdr sail-cache-local)))
  (if sail-cache-last-local
      (goto-char (caar sail-cache-last-local))
    (goto-char (point-min)))
  (when (eq 'b (cadar sail-cache-last-local)) (sail-backward-char)))

(defun sail-!ppss-backward-up-list ()
  "Safe up-list regarding comments, literals and errors."
  (let ((balance 1) (op (point)) (oc nil))
    (sail-in-literal-or-comment)
    (while (and (> (point) (point-min)) (> balance 0))
      (setq oc (if sail-cache-local (caar sail-cache-local) (point-min)))
      (condition-case nil (up-list -1) (error (goto-char (point-min))))
      (if (>= (point) oc) (setq balance (1- balance))
        (goto-char op)
        (skip-chars-backward "^[]{}()<>") (sail-backward-char)
        (cond ((sail-in-literal-or-comment-p)
               (sail-beginning-of-literal-or-comment-fast))
              ((looking-at "[[{(<]")
               (setq balance (1- balance)))
              ((looking-at "[]})>]")
               (setq balance (1+ balance)))))
      (setq op (point)))))

(defalias 'sail-in-literal-or-comment
    (eval-and-compile (if sail-use-syntax-ppss
                          'sail-ppss-in-literal-or-comment
                          'sail-!ppss-in-literal-or-comment)))
(defalias 'sail-fontify
    (eval-and-compile (if sail-use-syntax-ppss
                          'sail-ppss-fontify
                          'sail-!ppss-fontify)))
(defalias 'sail-in-literal-p
    (eval-and-compile (if sail-use-syntax-ppss
                          'sail-ppss-in-literal-p
                          'sail-!ppss-in-literal-p)))
(defalias 'sail-in-comment-p
    (eval-and-compile (if sail-use-syntax-ppss
                          'sail-ppss-in-comment-p
                          'sail-!ppss-in-comment-p)))
(defalias 'sail-in-literal-or-comment-p
    (eval-and-compile (if sail-use-syntax-ppss
                          'sail-ppss-in-literal-or-comment-p
                          'sail-!ppss-in-literal-or-comment-p)))
(defalias 'sail-beginning-of-literal-or-comment
    (eval-and-compile (if sail-use-syntax-ppss
                          'sail-ppss-beginning-of-literal-or-comment
                          'sail-!ppss-beginning-of-literal-or-comment)))
(defalias 'sail-beginning-of-literal-or-comment-fast
    (eval-and-compile (if sail-use-syntax-ppss
                          'sail-ppss-beginning-of-literal-or-comment-fast
                          'sail-!ppss-beginning-of-literal-or-comment-fast)))
(defalias 'sail-backward-up-list
    ;; FIXME: not clear if moving out of a string/comment counts as 1 or no.
    (eval-and-compile (if sail-use-syntax-ppss
                          'backward-up-list
			'sail-!ppss-backward-up-list)))

(defun sail-false-=-p ()
  "Is the underlying `=' the first/second letter of an operator?"
  (or (memq (preceding-char) '(?: ?> ?< ?=))
      (char-equal ?= (char-after (1+ (point))))))

(defun sail-at-phrase-break-p ()
  "Is the underlying `;' a phrase break?"
  (and (char-equal ?\; (following-char))
       (or (and (not (eobp))
                (char-equal ?\; (char-after (1+ (point)))))
           (char-equal ?\; (preceding-char)))))

(defvar sail-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?_ "_" st)
    (modify-syntax-entry ?? ". p" st)
    (modify-syntax-entry ?~ ". p" st)
    (modify-syntax-entry ?: "." st)
    (modify-syntax-entry ?' "w" st) ; ' is part of words (for primes).
    (modify-syntax-entry ?\" "\"" st) ; " is a string delimiter
    (modify-syntax-entry ?\\ "\\" st)
    (modify-syntax-entry ?*  ". 23" st)
    (condition-case nil
        (progn
          (modify-syntax-entry ?\( "()1n" st)
          (modify-syntax-entry ?\) ")(4n" st))
      (error               ;XEmacs signals an error instead of ignoring `n'.
       (modify-syntax-entry ?\( "()1" st)
       (modify-syntax-entry ?\) ")(4" st)))
    st)
  "Syntax table in use in Sail mode buffers.")

(defmacro sail-with-internal-syntax (&rest body)
  `(progn
     ;; Switch to a modified internal syntax.
     (modify-syntax-entry ?. "w" sail-mode-syntax-table)
     (modify-syntax-entry ?_ "w" sail-mode-syntax-table)
     (unwind-protect (progn ,@body)
       ;; Switch back to the interactive syntax.
       (modify-syntax-entry ?. "." sail-mode-syntax-table)
       (modify-syntax-entry ?_ "_" sail-mode-syntax-table))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                  Font-Lock

(defvar sail-doc-face 'font-lock-doc-face)

(unless sail-use-syntax-ppss

  (defun sail-fontify-buffer ()
    (font-lock-default-fontify-buffer)
    (sail-fontify (point-min) (point-max)))

  (defun sail-fontify-region (begin end &optional verbose)
    (font-lock-default-fontify-region begin end verbose)
    (sail-fontify begin end))

  (defun sail-fontify (begin end)
    (when (eq major-mode 'sail-mode)
      (save-excursion
       (sail-with-internal-syntax

        (let ((case-fold-search nil)
              (modified (buffer-modified-p))) ; Emacs hack (see below)
          (goto-char begin)
          (setq begin (line-beginning-position))
          (goto-char (1- end))
          (end-of-line)
          ;; Dirty hack to trick `font-lock-default-unfontify-region'
          (forward-line 2)
          (setq end (point))

          (while (> end begin)
            (goto-char (1- end))
            (sail-in-literal-or-comment)
            (cond
              ((cdr sail-last-loc)
               (sail-beginning-of-literal-or-comment)
               (put-text-property (max begin (point)) end 'face
                                  (if (looking-at
                                       "(\\*[Tt][Ee][Xx]\\|(\\*\\*[^*]")
                                      sail-doc-face
                                      'font-lock-comment-face))
               (setq end (1- (point))))
              ((car sail-last-loc)
               (sail-beginning-of-literal-or-comment)
               (put-text-property (max begin (point)) end 'face
                                  'font-lock-string-face)
               (setq end (point)))
              (t (while (and sail-cache-local
                             (or (> (caar sail-cache-local) end)
                                 (eq 'b (cadar sail-cache-local))))
                   (setq sail-cache-local (cdr sail-cache-local)))
                 (setq end (if sail-cache-local
                               (caar sail-cache-local) begin)))))
          (unless modified (set-buffer-modified-p nil)))
        ))))
  ) ;; end sail-use-syntax-ppss

(defconst sail-font-lock-syntactic-keywords
  ;; Char constants start with ' but ' can also appear in identifiers.
  ;; Beware not to match things like '*)hel' or '"hel' since the first '
  ;; might be inside a string or comment.
  '(("\\<\\('\\)\\([^'\\\n]\\|\\\\.[^\\'\n \")]*\\)\\('\\)"
     (1 '(7)) (3 '(7)))))

(defun sail-font-lock-syntactic-face-function (state)
  (if (nth 3 state) font-lock-string-face
    (let ((start (nth 8 state)))
      (if (and (> (point-max) (+ start 2))
               (eq (char-after (+ start 2)) ?*)
               (not (eq (char-after (+ start 3)) ?*)))
          ;; This is a documentation comment
          sail-doc-face
        font-lock-comment-face))))

;; Initially empty, set in `sail-install-font-lock'
(defvar sail-font-lock-keywords ()
  "Font-Lock patterns for Sail mode.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                    Keymap

(defvar sail-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "|]" 'sail-electric-piperb)
    (define-key map ")" 'sail-electric-rp)
    (define-key map "}" 'sail-electric-rc)
    (define-key map "]" 'sail-electric-rb)
    (define-key map ">" 'sail-electric-lt)
    (define-key map "\M-q" 'sail-indent-phrase)
    (define-key map "\C-c\C-q" 'sail-indent-phrase)
    (define-key map "\M-\C-\\" 'indent-region)
    (define-key map "\C-c\C-a" 'sail-find-alternate-file)
    (define-key map "\C-c\C-c" 'compile)
    (define-key map "\C-xnd" 'sail-narrow-to-phrase)
    (define-key map "\C-c\C-n" 'sail-next-phrase)
    (define-key map "\C-c\C-p" 'sail-previous-phrase)
    (define-key map [(backspace)] 'backward-delete-char-untabify)
    (define-key map [(control c) (control down)] 'sail-next-phrase)
    (define-key map [(control c) (control up)] 'sail-previous-phrase)
    (define-key map [(meta control down)]  'sail-next-phrase)
    (define-key map [(meta control up)] 'sail-previous-phrase)
    (define-key map [(meta control n)]  'sail-next-phrase)
    (define-key map [(meta control p)] 'sail-previous-phrase)
    (define-key map [(meta control h)] 'sail-mark-phrase)
    map)
  "Keymap used in Sail mode.")

(defconst sail-font-lock-syntax
  `((?_ . "w") (?` . ".")
    ,@(unless sail-use-syntax-ppss
        '((?\" . ".") (?\( . ".") (?\) . ".") (?* . "."))))
  "Syntax changes for Font-Lock.")

(defvar sail-mode-abbrev-table ()
  "Abbrev table used for Sail mode buffers.")
(defun sail-define-abbrev (keyword)
  (define-abbrev sail-mode-abbrev-table keyword keyword 'sail-abbrev-hook))
(if sail-mode-abbrev-table ()
    (setq sail-mode-abbrev-table (make-abbrev-table))
  (mapc 'sail-define-abbrev
        '("scattered" "function" "typedef" "let" "default" "val" "register"
          "alias" "union" "member" "clause" "extern" "effect"
          "rec" "and" "switch" "case" "exit" "foreach" "from" "else"
          "to" "end" "downto" "in" "then" "with" "if" "nondet" "as"
	  "undefined" "const" "struct" "IN" "deinfix"))
  (setq abbrevs-changed nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                              The major mode

;;;###autoload (add-to-list 'auto-mode-alist '("\\.sail?" . sail-mode))

;;;###autoload
(defun sail-mode ()
  "Major mode for editing Sail code.

Based on Tuareg mode. See Tuareg mode for usage"
  (interactive)
  (kill-all-local-variables)
  (setq major-mode 'sail-mode)
  (setq mode-name "Sail")
  (use-local-map sail-mode-map)
  (set-syntax-table sail-mode-syntax-table)
  (setq local-abbrev-sail sail-mode-abbrev-table)

  ;; Initialize the Sail menu
  (sail-build-menu)

  ;; Initialize indentation regexps
  (sail-make-indentation-regexps)

  (make-local-variable 'paragraph-start)
  (setq paragraph-start (concat "^[ \t]*$\\|\\*)$\\|" page-delimiter))
  (make-local-variable 'paragraph-separate)
  (setq paragraph-separate paragraph-start)
  (make-local-variable 'require-final-newline)
  (setq require-final-newline t)
  (make-local-variable 'comment-start)
  (setq comment-start "(* ")
  (make-local-variable 'comment-end)
  (setq comment-end " *)")
  (make-local-variable 'comment-column)
  (setq comment-column 40)
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip "(\\*+[ \t]*")
  (make-local-variable 'comment-multi-line)
  (setq comment-multi-line t)
  (make-local-variable 'parse-sexp-ignore-comments)
  (setq parse-sexp-ignore-comments nil)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'sail-indent-command)
  (unless sail-use-syntax-ppss
    (add-hook 'before-change-functions 'sail-before-change-function nil t))
  (make-local-variable 'normal-auto-fill-function)
  (setq normal-auto-fill-function 'sail-auto-fill-function)

  (when (featurep 'imenu)
    (setq imenu-prev-index-position-function 'sail-imenu-prev-index-position
          imenu-extract-index-name-function 'sail-imenu-extract-index-name))

  ;; Hooks for sail-mode, use them for sail-mode configuration
  (sail-install-font-lock)
  (run-hooks 'sail-mode-hook)
  (when sail-use-abbrev-mode (abbrev-mode 1))
  (message nil))

(defun sail-install-font-lock ()
  (setq
   sail-font-lock-keywords
   `(("\\<\\(extern\\|function\\|scattered\\|clause\\|effect\\|default\\|struct\\|const\\|union\\|val\\|typedef\\|in\\|let\\|rec\\|and\\|end\\|register\\|alias\\|member\\|enumerate\\)\\>"
      0 sail-font-lock-governing-face nil nil)
     ("\\<\\(false\\|true\\)\\>" 0 font-lock-constant-face nil nil)
     ("\\<\\(as\\|downto\\|else\\|foreach\\|if\\|t\\(hen\\|o\\)\\|when\\|switch\\|with\\|case\\|exit\\|nondet\\|from\\|by\\)\\>"
      0 font-lock-keyword-face nil nil)
     ("\\<\\(clause\\)\\>[ \t\n]*\\(\\(\\w\\|[_ \t()*,]\\)+\\)"
      2 font-lock-variable-name-face keep nil)
     ("\\<\\(typedef\\|union\\)\\>[ \t\n]*\\(\\(\\w\\|[_ \t()*,]\\)+\\)"
      2 font-lock-type-face keep nil)
     ("\\<\\(Type\\|Nat\\|Order\\|Effect\\|inc\\|dec\\|rreg\\|wreg\\|rmem\\|wmem\\|barr\\|undef\\|unspec\\|nondet\\|pure\\|effect\\|IN\\|forall\\)\\>"
      0 font-lock-type-face keep nil)
     ("\\<\\(val\\|extern\\|clause\\|and\\||let\\|rec\\>[ \t\n]*\\(\\(\\w\\|[_,?~.]\\)*\\)"
      2 font-lock-variable-name-face keep nil)
     ("\\<\\(val\\|and\\|let\\>[ \t\n]*\\(\\(\\w\\|[_,?~.]\\)*\\)\\>\\(\\(\\w\\|[->_ \t,?~.]\\|(\\(\\w\\|[--->_ \t,?~.=]\\)*)\\)*\\)"
      6 font-lock-variable-name-face keep nil)
     ("\\<\\([?~]?[_[:alpha:]]\\w*\\)[ \t\n]*:[^:>=]"
      1 font-lock-variable-name-face keep nil)
     ("^#\\w+\\>" 0 font-lock-preprocessor-face t nil)
     ))
  (setq font-lock-defaults
        (list*
         'sail-font-lock-keywords (not sail-use-syntax-ppss) nil
         sail-font-lock-syntax nil
         '(font-lock-syntactic-keywords
           . sail-font-lock-syntactic-keywords)
         '(parse-sexp-lookup-properties
           . t)
         '(font-lock-syntactic-face-function
           . sail-font-lock-syntactic-face-function)
         (unless sail-use-syntax-ppss
           '((font-lock-fontify-region-function
              . sail-fontify-region)))))
  (when (and (boundp 'font-lock-fontify-region-function)
             (not sail-use-syntax-ppss))
    (make-local-variable 'font-lock-fontify-region-function)
    (setq font-lock-fontify-region-function 'sail-fontify-region)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                               Indentation stuff

(eval-and-compile
  (defconst sail-no-more-code-this-line-regexp "[ \t]*\\((\\*\\|$\\)"
    "Regexp matching lines which have no more code:
 blanks + (maybe) comment start."))

(defmacro sail-no-code-after (rex)
  `(eval-when-compile (concat ,rex sail-no-more-code-this-line-regexp)))

(defconst sail-no-code-this-line-regexp
  (concat "^" sail-no-more-code-this-line-regexp))

(defun sail-ro (&rest words) (concat "\\<" (regexp-opt words t) "\\>"))

(defconst sail-extra-unindent-regexp
  (concat "\\(" (sail-ro "function")
          "\\|\\[" sail-no-more-code-this-line-regexp "\\)")
  "Regexp for keywords needing extra indentation to compensate for case matches.")

(defun sail-give-extra-unindent-regexp ()
  sail-extra-unindent-regexp)

(defconst sail-keyword-regexp
  (concat (sail-ro "scattered" "function" "typedef" "let" "default" "val" "register"
		   "alias" "union" "member" "clause" "extern" "effect"
		   "rec" "and" "switch" "case" "exit" "foreach" "from" "else"
		   "to" "end" "downto" "in" "then" "with" "if" "nondet" "as"
		   "undefined" "const" "struct" "IN" "deinfix")
          "\\|->\\|[;,|]")
  "Regexp for all recognized keywords.")

(defun sail-give-keyword-regexp () sail-keyword-regexp)

(defconst sail-operator-regexp "[---+*/=<>@^&|]\\|:>\\|::\\|\\<\\(or\\|l\\(and\\|x?or\\|s[lr]\\)\\|as[lr]\\|mod\\)\\>"
  "Regexp for all operators.")

(defconst sail-matching-keyword-regexp
  (sail-ro "and" "then" "else" "in")
  "Regexp matching Sail keywords which act as end block delimiters.")

(defun sail-give-matching-keyword-regexp () sail-matching-keyword-regexp)

(defconst sail-matching-kwop-regexp
  (concat sail-matching-keyword-regexp
          "\\|\\<with\\>\\|[|>]?\\]\\|>?}\\|[|)]\\|;;")
  "Regexp matching Sail keywords or operators which act as end block
delimiters.")

(defun sail-give-matching-kwop-regexp () sail-matching-kwop-regexp)

(defconst sail-block-regexp
  (concat (sail-ro "foreach" "nondet" "if" "clause" "switch" "case")
          "\\|[][(){}]\\|\\*)"))

(defconst sail-find-kwop-regexp
  (concat sail-matching-keyword-regexp "\\|" sail-block-regexp))

(defun sail-give-find-kwop-regexp () sail-find-kwop-regexp)

(defconst sail-governing-phrase-regexp
  (sail-ro "val" "typedef" "function" "scattered" "default" "union" "member"
             "end" "extern" "let")
  "Regexp matching Sail phrase delimitors.")

(defconst sail-keyword-alist
  '(("end" . sail-default-indent)
    ("foreach" . sail-foreach-indent)
    ("val" . sail-val-indent)
    ("function" . sail-fun-indent)
    ("if" . sail-if-then-else-indent)
    ("then" . sail-if-then-else-indent)
    ("else" . sail-if-then-else-indent)
    ("let" . sail-let-indent)
    ("switch" . sail-match-indent)

    ;; Case match keywords
    ("case" . sail-case-indent)

    ;; Assume default indentation for other keywords and operators
    )
  "Association list of indentation values based on governing keywords.")

(defconst sail-leading-kwop-alist
  '(("}" . sail-find-match)
    (">" . sail-find-match)
    (")" . sail-find-match)
    ("]" . sail-find-match)
    ("|]" . sail-find-match)
    ("||]" . sail-find-match)
    ("in" . sail-find-in-match)
    ("else" . sail-find-else-match)
    ("then" . sail-find-then-match)
    ("to" . sail-find-match)
    ("downto" . sail-find-match)
    ("by" . sail-find-match)
    ("and" . sail-find-and-match))
  "Association list used in Sail mode for skipping back over nested blocks.")

(defun sail-find-leading-kwop-match (kwop)
  (funcall (cdr (assoc kwop sail-leading-kwop-alist))))

(defconst sail-binding-regexp "\\(\\<and\\>\\|(*\\<let\\>\\)")

(defun sail-assoc-indent (kwop &optional look-for-let-or-and)
  "Return relative indentation of the keyword given in argument."
  (let ((ind (or (symbol-value (cdr (assoc kwop sail-keyword-alist)))
                 sail-default-indent))
        (looking-let-or-and (and look-for-let-or-and
                                 (looking-at sail-binding-regexp))))
    (if (string-match (sail-give-extra-unindent-regexp) kwop)
        (if (and sail-let-always-indent
		 looking-let-or-and (< ind sail-let-indent))
	    sail-let-indent ind)
      ind)))

(defconst sail-meaningful-word-regexp
  "[^ \t\n_[:alnum:]]\\|\\<\\(\\w\\|_\\)+\\>\\|\\*)")
(defun sail-find-meaningful-word ()
  "Look back for a word, skipping comments and blanks.
Returns the actual text of the word, if found."
  (let ((found nil) (kwop nil) (pt (point)))
    (while (and (not found)
                (re-search-backward sail-meaningful-word-regexp
                                    (point-min) t))
      (setq kwop (sail-match-string 0))
      (cond ((or (string= kwop "=") (string= kwop ">"))                  
             (backward-char 2)
             (setq kwop (concat ">>" kwop)))
            ((and (string= kwop ">") (char-equal ?- (char-before)))
             (backward-char)
             (setq kwop "->")))
      (when (= pt (point))
        (error "sail-find-meaningful-word: inf loop at %d, kwop=%s" pt kwop))
      (setq pt (point))
      (if kwop
          (if (sail-in-comment-p)
              (sail-beginning-of-literal-or-comment-fast)
            (setq found t))
        (setq found t)))
    (if found kwop (goto-char (point-min)) nil)))

(defun sail-make-find-kwop-regexp (kwop-regexp)
  "Make a custom indentation regexp."
  (concat (sail-give-find-kwop-regexp) "\\|" kwop-regexp))

;; Static regexps
(defconst sail-find-and-match-regexp
  (concat (sail-ro "else" "in" "then" "downto" "by" "from"
                     "foreach" "if" "function" 
                     "let" "in" "typedef" "val" "end")
          "\\|[][(){}]\\|\\*)"))
(defconst sail-find-phrase-beginning-regexp
  (concat (sail-ro "end" "typedef" "let")
          "\\|^#[ \t]*[a-z][_a-z]*\\>\\|;;"))
(defconst sail-find-phrase-beginning-and-regexp
  (concat "\\<\\(and\\)\\>\\|" sail-find-phrase-beginning-regexp))
(defconst sail-back-to-paren-or-indentation-regexp
  "[][(){}]\\|\\.<\\|>\\.\\|\\*)\\|^[ \t]*\\(.\\|\n\\)")

(defun sail-make-indentation-regexps ()
  "Initialisation of specific indentation regexp.
Gathered here for memoization and dynamic reconfiguration purposes."
  (setq
   sail-find-comma-match-regexp
    (sail-make-find-kwop-regexp
     (concat (sail-ro "and" "switch" "else" "then" "function" "let" "foreach")
             "\\|->\\|[[{(]"))
   sail-find-with-match-regexp
    (sail-make-find-kwop-regexp
     (concat (sail-ro "switch" "case" "typedef")
             "\\|[[{(]"))
   sail-find-in-match-regexp
    (sail-make-find-kwop-regexp (sail-ro "let" "function"))
   sail-find-else-match-regexp
    (sail-make-find-kwop-regexp ";")
   sail-find-do-match-regexp
    (sail-make-find-kwop-regexp "->")
   sail-find-=-match-regexp
    (sail-make-find-kwop-regexp
     (concat (sail-ro "val" "let" "function" "typedef" "if" "in")
             "\\|="))
   sail-find-arrow-match-regexp
    (sail-make-find-kwop-regexp
     (concat (sail-ro "extern" "typedef" "val" "function" "let")
             "\\|[|;]"))
   sail-find-semicolon-match-regexp
    (sail-make-find-kwop-regexp
     (concat ";" sail-no-more-code-this-line-regexp "\\|->\\|"
             (sail-ro "let")))
   sail-find-phrase-indentation-regexp
    (sail-make-find-kwop-regexp
     (concat sail-governing-phrase-regexp "\\|" (sail-ro "and")))
   sail-find-phrase-indentation-break-regexp
    (concat sail-find-phrase-indentation-regexp "\\|;")
   sail-compute-argument-indent-regexp
    (sail-make-find-kwop-regexp
     (concat (sail-give-keyword-regexp) "\\|="))
   sail-compute-normal-indent-regexp
    (concat sail-compute-argument-indent-regexp "\\|^.[ \t]*")
   sail-find-monadic-match-regexp
    (concat sail-block-regexp "\\|\\([;=]\\)\\|\\(->\\)\\|"
            (sail-ro "val" "let" "function" "typedef" "if" "in" "end"))))

(defun sail-strip-trailing-whitespace (string)
  (if (string-match "[ \t]*\\'" string)
      (substring string 0 (match-beginning 0))
    string))

(defun sail-find-kwop-pos (kr do-not-skip-regexp may-terminate-early)
  "Look back for a keyword or operator matching KR (short for kwop regexp).
Skips blocks etc...

Ignore occurences inside literals and comments.
If found, return the actual text of the keyword or operator."
  (let ((found nil)
        (kwop nil) pos
        (kwop-regexp kr))
    (while (and (not found)
                (setq pos (re-search-backward kwop-regexp (point-min) t))
                (setq kwop (sail-strip-trailing-whitespace
                            ;; for trailing blanks after a semicolon
                            (sail-match-string 0))))
      (cond
       ((sail-in-literal-or-comment-p)
        (sail-beginning-of-literal-or-comment-fast))
       ((looking-at "[>]})]")
        (sail-backward-up-list))
       ((sail-at-phrase-break-p)
        (setq found t))
       ((and do-not-skip-regexp (looking-at do-not-skip-regexp))
        (if (and (string= kwop "|") (char-equal ?| (preceding-char)))
            (backward-char)
          (setq found t)))
       ((looking-at (sail-give-matching-keyword-regexp))
        (let ((mkwop (sail-find-leading-kwop-match (sail-match-string 0))))
          (when (and may-terminate-early (string-match kwop-regexp mkwop))
            (setq found t))))
       (t
        (setq found t))))
    (if found (list kwop pos) (goto-char (point-min)) nil)))

(defun sail-find-kwop (kr &optional do-not-skip-regexp)
  (car (sail-find-kwop-pos kr do-not-skip-regexp nil)))

(defun sail-find-match ()
  (let ((kwop (sail-find-kwop (sail-give-find-kwop-regexp))))
    (when (string= kwop "then")
      (sail-find-then-match)
      (sail-find-match))
    kwop))

(defun sail-find-comma-match ()
  (car (sail-find-kwop-pos sail-find-comma-match-regexp nil t)))

(defun sail-find-in-match ()
  (let ((kwop (sail-find-kwop sail-find-in-match-regexp "\\<and\\>")))
    (cond
     ((string= kwop "and")
      (sail-find-in-match))
     (t
      kwop))))

(defconst sail-find-then-match-regexp
  (sail-make-find-kwop-regexp "\\(->\\)"))
(defun sail-find-then-kwop ()
  (sail-find-kwop sail-find-then-match-regexp "\\(->\\)"))
(defun sail-find-then-match ()
  (let ((kwop (sail-find-then-kwop)))
    (cond ((string= kwop "if")
           (let ((back (point)))
             (sail-back-to-paren-or-indentation)
             (if (looking-at "else[ \t]*\\((\\*.*\\*)\\)*[ \t]*if")
                 "else if"
               (goto-char back)
               kwop)))
          (t kwop))))

(defun sail-find-then-else-match ()
  (let ((kwop (sail-find-then-kwop)))
    (cond
     ((string= kwop "if")
      (let ((pos (point)))
        (if (and (not (sail-in-indentation-p))
                 (string= "else" (sail-find-meaningful-word)))
            "else"
          (goto-char pos)
          kwop)))
     (t
      kwop))))

(defun sail-find-else-match ()
  (let ((kwop (sail-find-kwop sail-find-else-match-regexp
                                "\\<then\\>")))
    (cond
     ((string= kwop "then")
      (sail-find-then-else-match))
     ((string= kwop ";")
      (sail-find-semicolon-match)
      (sail-find-else-match)))))


(defconst sail-done-match-stop-regexp (sail-ro "and"))
(defun sail-find-done-match ()
  (let ((kwop (sail-find-kwop (sail-give-find-kwop-regexp)
			      sail-done-match-stop-regexp)))
    (cond
     ((string= kwop "and")
      (sail-find-and-match))
     (t
      kwop))))

(defun sail-find-and-match ()
  (let* ((kwop (sail-find-kwop
                sail-find-and-match-regexp
                (sail-give-and-stop-regexp)))
         (old-point (point)))
    (cond
     ((string= kwop "typedef")
      (let ((kwop2 (sail-find-meaningful-word)))
        (cond ((string= kwop2 "and")
               (sail-find-and-match))
              ((and (string= kwop "function")
                    (string= kwop2 "let"))
               kwop2)
              (t (goto-char old-point) kwop))))
     (t kwop))))

(defconst sail-=-stop-regexp (concat (sail-ro "and" "in") "\\|="))
(defun sail-give-=-stop-regexp () sail-=-stop-regexp)

(defun sail-find-=-match ()
  (let ((kwop (sail-find-kwop
               sail-find-=-match-regexp
               (sail-give-=-stop-regexp))))
    (cond
     ((string= kwop "and")
      (sail-find-and-match))
     ((and (string= kwop "=")
           (not (sail-false-=-p)))
      (while (and (string= kwop "=")
                  (not (sail-false-=-p)))
        (setq kwop (sail-find-=-match)))
      kwop)
     (t kwop))))

(defconst sail-captive-regexp
  (sail-ro "let" "if" "typedef"))
(defun sail-captive-= ()
  (save-excursion
    (sail-find-=-match)
    (looking-at sail-captive-regexp)))


(defun sail-find-arrow-match ()
  (let ((kwop (sail-find-kwop (sail-give-find-arrow-match-regexp)
                                "\\<with\\>")))
    (cond
     ((string= kwop "function")
      (let ((pos (point)))
        (progn (goto-char pos) kwop)))
     ((not (string= kwop ":"))
      kwop)
     ;; If we get this far, we know we're looking at a colon.
     ((or (char-equal (char-before) ?:)
          (char-equal (char-after (1+ (point))) ?:)
          (char-equal (char-after (1+ (point))) ?>))
      (sail-find-arrow-match))
     ;; Patch by T. Freeman
     (t
      (let ((oldpoint (point))
            (match (sail-find-arrow-match)))
        (if (looking-at ":")
            match
          (progn
            ;; Go back to where we were before the recursive call.
            (goto-char oldpoint)
            kwop)))))))

(defconst sail-semicolon-match-stop-regexp
  (sail-ro "and" "end" "in"))
(defconst sail-no-code-after-paren-regexp
  (sail-no-code-after "[[{(][|<]?"))
(defun sail-semicolon-indent-kwop-point (&optional leading-semi-colon)
  ;; return (kwop kwop-point indentation)
  (let ((kwop (sail-find-kwop sail-find-semicolon-match-regexp
			      sail-semicolon-match-stop-regexp))
        (point (point)))
    ;; We don't need to find the keyword matching `and' since we know it's `let'!
    (list
     (cond
       ((string= kwop ";")
        (forward-line 1)
        (while (or (sail-in-comment-p)
                   (looking-at sail-no-code-this-line-regexp))
          (forward-line 1))
        (back-to-indentation)
        (current-column))
       ((and leading-semi-colon
             (looking-at "\\((\\|\\[[<|]?\\|{<?\\)[ \t]*[^ \t\n]")
             (not (looking-at sail-no-code-after-paren-regexp)))
        (current-column))
       ;; ((looking-at (tuareg-no-code-after "\\((\\|\\[[<|]?\\|{<?\\)"))
       ;;  (+ (current-column) tuareg-default-indent))
       ((looking-at "\\(\\.<\\|(\\|\\[[<|]?\\|{<?\\)") ; paren with subsequent text
        (sail-search-forward-paren)
        (current-column))
       ((string= kwop "->")
        (if (save-excursion
              (sail-find-arrow-match)
              (or (looking-at "\\<function\\>\\||")
                  (looking-at (sail-give-extra-unindent-regexp))))
            (sail-paren-or-indentation-indent)
          (sail-find-semicolon-match)))
       ((string= kwop "in")
        (sail-find-in-match)
        (+ (current-column) sail-in-indent))
       ((string= kwop "let")
        (+ (current-column) sail-let-indent))
       (t (sail-paren-or-indentation-indent)))
     kwop point)))

(defun sail-find-semicolon-match (&optional leading-semi-colon)
  (car (sail-semicolon-indent-kwop-point leading-semi-colon)))

(defmacro sail-reset-and-kwop (kwop)
  `(when (and ,kwop (string= ,kwop "and"))
     (setq ,kwop (sail-find-and-match))))

(defconst sail-phrase-regexp-1 (sail-ro "typedef" "end"))
(defconst sail-phrase-regexp-2 (sail-ro "and" "let" "function" "case"))
(defconst sail-phrase-regexp-3
  (sail-ro "and" "in"))
(defun sail-find-phrase-indentation (&optional phrase-break)
  (if (and (looking-at sail-phrase-regexp-1) (> (point) (point-min))
           (save-excursion
             (sail-find-meaningful-word)
             (looking-at sail-phrase-regexp-2)))
      (progn
        (sail-find-meaningful-word)
        (+ (current-column) sail-default-indent))
    (let ((looking-at-and (looking-at "\\<and\\>"))
          (kwop (sail-find-kwop
                 (if phrase-break
                     sail-find-phrase-indentation-break-regexp
                   sail-find-phrase-indentation-regexp)
                 sail-phrase-regexp-3))
          (tmpkwop nil) (curr nil))
      (sail-reset-and-kwop kwop)
      (cond ((not kwop) (current-column))
            ((and (string= kwop "in")
                  (not (save-excursion
                         (setq tmpkwop (sail-find-in-match))
                         (sail-reset-and-kwop tmpkwop)
                         (setq curr (point))
                         (and (string= tmpkwop "let")
                              (not (sail-looking-at-internal-let))))))
             (goto-char curr)
             (sail-find-phrase-indentation phrase-break))
            ((sail-at-phrase-break-p)
             (end-of-line)
             (sail-skip-blank-and-comments)
             (current-column))
            ((string= kwop "let")
             (if (sail-looking-at-internal-let)
                 (sail-find-phrase-indentation phrase-break)
                 (current-column)))
            ((string= kwop "in")
             (sail-find-in-match)
             (current-column))
            ((looking-at "\\(\\.<\\|(\\|\\[[<|]?\\|{<?\\)[ \t]*[^ \t\n]")
             (sail-search-forward-paren)
             (current-column))
            (t (current-column))))))

(defconst sail-paren-or-indentation-stop-regexp
  (sail-ro "and" "in"))
(defun sail-back-to-paren-or-indentation ()
  "Search backwards for the first open paren in line, or skip to indentation.
Returns t iff skipped to indentation."
  (if (or (bolp) (sail-in-indentation-p))
      (progn (back-to-indentation) t)
    (let ((kwop (sail-find-kwop
                 sail-back-to-paren-or-indentation-regexp
                 sail-paren-or-indentation-stop-regexp))
          (retval))
      (setq retval
            (cond
             ((string= kwop "in")
              (sail-in-indentation-p))
;            ((looking-at "[[{(]") (tuareg-search-forward-paren) nil)
;            ((looking-at "\\.<")
;             (if tuareg-support-metaocaml
;                 (progn
;                   (tuareg-search-forward-paren) nil)
;               (tuareg-back-to-paren-or-indentation)))
             (t (back-to-indentation) t)))
      (cond
    ;   ((looking-at "|[^|]")
    ;    (re-search-forward "|[^|][ \t]*") nil)
       ((string= kwop "in")
        (sail-find-in-match)
        (sail-back-to-paren-or-indentation)
        (if (looking-at "\\<\\(let\\|and\\)\\>")
            (forward-char sail-in-indent)) nil)
       (t retval)))))

(defun sail-paren-or-indentation-column ()
  (sail-back-to-paren-or-indentation)
  (current-column))

(defun sail-paren-or-indentation-indent ()
  (+ (sail-paren-or-indentation-column) sail-default-indent))

(defun sail-search-forward-paren ()
  (re-search-forward "\\(\\.<\\|(\\|\\[[<|]?\\|{|<\\)[ \t]*"))

(defun sail-add-default-indent (leading-operator)
  (if leading-operator 0 sail-default-indent))

(defconst sail-internal-let-regexp
  (concat "[[({;=]\\|"
           (sail-ro "if" "in" "then" "else" "switch")))
(defun sail-looking-at-internal-let ()
  (save-excursion
    (sail-find-meaningful-word)
    (and (not (sail-at-phrase-break-p))
         (or (looking-at sail-internal-let-regexp)
             (looking-at sail-operator-regexp)))))

(defun sail-looking-at-in-let ()
  (save-excursion
    (string= (sail-find-meaningful-word) "in")))

(defun sail-indent-from-previous-kwop ()
  (let* ((start-pos (point))
         (kwop (sail-find-argument-kwop-non-blank t))
         (captive= (and (string= kwop "=") (sail-captive-=)))
         (kwop-pos (point)))
    (forward-char (length kwop))
    (sail-skip-blank-and-comments)
    (cond ((or (not captive=)
               (/= (point) start-pos)) ; code between paren and kwop
           (goto-char start-pos)
           (sail-paren-or-indentation-indent))
          (t
           (goto-char kwop-pos)
           (when (string= kwop "=")
             (setq kwop (sail-find-=-match)))
           (+ sail-default-indent
              (if (assoc kwop sail-leading-kwop-alist)
                  (sail-compute-kwop-indent kwop)
                  (current-column)))))))

(defun sail-indent-from-paren (leading-operator start-pos)
  (cond
   ((looking-at (sail-no-code-after "\\(\\(\\.<\\|(\\|\\[[<|]?\\|{\\|<\\)\\)"))
    (cond ((sail-in-indentation-p)
           (+ sail-default-indent
              (current-column)))
          (t (sail-indent-from-previous-kwop))))
   ((looking-at "([ \t]*\\(\\w\\)")
    (goto-char (match-beginning 1))
    (current-column))
   (t
    (+ (sail-add-default-indent leading-operator)
       (current-column)))))

(defun sail-skip-to-next-form (old-point)
  (while (and (not (looking-at sail-no-more-code-this-line-regexp))
              (< (point) old-point)) ; do not go beyond old-point
    (forward-sexp 1))
  (sail-skip-blank-and-comments)
  (sail-back-to-paren-or-indentation))

(defun sail-find-argument-kwop (leading-operator)
  (sail-find-kwop (if leading-operator
                      sail-compute-argument-indent-regexp
                      sail-compute-normal-indent-regexp)
                    (sail-give-keyword-regexp)))

(defun sail-find-argument-kwop-clean (leading-operator)
  (let (kwop)
    (while (or (progn (setq kwop (sail-find-argument-kwop leading-operator))
                      (sail-reset-and-kwop kwop)
                      nil)
               (and (string= kwop "=") (sail-false-=-p))
               (and (looking-at sail-no-code-this-line-regexp)
                    (not (= (point) (point-min))))))
    kwop))

(defun sail-find-argument-kwop-non-blank (leading-operator)
  (let ((kwop "") (point (1+ (point))))
    (while (and (> point (point)) (string= "" kwop))
      (setq point (point)
            kwop (sail-find-argument-kwop-clean leading-operator)))
    kwop))

(defun sail-compute-argument-indent (leading-operator)
  (let* ((old-point (line-beginning-position))
         (kwop (sail-find-argument-kwop-non-blank leading-operator))
         (match-end-point (+ (point) (length kwop)))) ; match-end is invalid!
    (cond
     ((let (matching-kwop matching-pos)
        (save-excursion
          (setq matching-kwop (sail-find-arrow-match))
          (setq matching-pos (point)))
        (cond
         ((or (string= matching-kwop "val") (string= matching-kwop "let") (string= matching-kwop "function"))
          (+ (current-column) sail-val-indent))
         (t
          (+ (sail-paren-or-indentation-column)
             (sail-add-default-indent leading-operator))))))
     ((string= kwop "function")
      (+ (sail-paren-or-indentation-column)
         (sail-add-default-indent leading-operator)
         (sail-assoc-indent kwop)))
     ((<= old-point (point))
      (+ (sail-add-default-indent leading-operator)
         (current-column)))
     (t
      (goto-char match-end-point) ; skip kwop == (forward-char (length kwop))
      (sail-skip-to-next-form old-point)
      (+ (sail-add-default-indent
          (if (save-excursion (goto-char match-end-point)
                              (looking-at sail-no-more-code-this-line-regexp))
              (or leading-operator (string= kwop "{")
                  (looking-at (sail-no-code-after "[[:upper:]].*\\.")))
            (not (looking-at sail-operator-regexp))))
         (current-column))))))

(defun sail-compute-arrow-indent (start-pos)
  (let (kwop pos)
    (save-excursion (setq kwop (sail-find-arrow-match) pos (point)))
    (cond ((or (string= kwop "val")
               (string= kwop "let"))
           (goto-char pos)
           (+ (current-column) sail-val-indent))
          ((string= kwop "typedef")
           (goto-char pos)
           (+ (current-column) sail-type-indent
              sail-default-indent))
          ((string= kwop "(")
           (goto-char pos)
           (sail-indent-after-next-char))
          ((or (string= kwop "{")
               (string= kwop ";"))
           (if (and (looking-at "->")
                    (search-backward ":" pos t))
               (sail-indent-after-next-char)
             (sail-back-to-paren-or-indentation)
             (current-column)))
          (t (sail-paren-or-indentation-indent)))))

(defun sail-compute-keyword-indent (kwop leading-operator start-pos)
  (cond ((string= kwop ";")
         (if (looking-at (sail-no-code-after ";"))
             (let* ((pos (point)) (indent (sail-find-semicolon-match)))
               (if (looking-at sail-phrase-regexp-1)
                   (progn
                     (goto-char start-pos)
                     (if (search-backward ":" pos t)
                         (sail-indent-after-next-char)
                       indent))
                 indent))
           (sail-paren-or-indentation-indent)))
        ((string= kwop ",")
         (if (looking-at (sail-no-code-after ","))
             (let ((mkwop (sail-find-comma-match)))
               (cond ((or (string= mkwop "[")
                          (string= mkwop "{")
                          (string= mkwop "(")
			  (string= mkwop "<")
			  (string- mkwop "[|"))
                      (forward-char 1) (skip-syntax-forward " ")
                      (current-column))
                     ((looking-at "[[{(]\\|\\<")
                      (sail-indent-from-paren t start-pos))
                     ((or (and (looking-at "[<|]")
                               (char-equal ?\[ (preceding-char)))
                          (and (looking-at "<")
                               (char-equal ?\{ (preceding-char))))
                      (sail-backward-char)
                      (sail-indent-from-paren t start-pos))
                     ((and (looking-at "\\<let\\>") (string= mkwop "in"))
                      (+ (current-column) sail-in-indent))
                     (t (+ (sail-paren-or-indentation-column)
                           (sail-assoc-indent mkwop)))))
           (sail-paren-or-indentation-indent)))
        ((or (string= kwop "function") (string= kwop "and"))
         (sail-back-to-paren-or-indentation)
         (+ (sail-paren-or-indentation-indent)
            (sail-assoc-indent kwop t)))
        ((string-match "\\<\\(function\\)\\>" kwop)
         (+ (sail-paren-or-indentation-column)
            (sail-add-default-indent leading-operator)
            (sail-assoc-indent kwop t)))
        ((string-match (sail-give-extra-unindent-regexp) kwop)
         (+ (sail-paren-or-indentation-column)
            (sail-assoc-indent kwop t)))
        ((string= kwop "in")
         (when (looking-at (sail-no-code-after "\\<in\\>"))
           (sail-find-in-match))
         (+ (current-column)
            sail-in-indent))
        ((string-match (sail-give-matching-kwop-regexp) kwop)
         (sail-find-leading-kwop-match kwop)
         (if (sail-in-indentation-p)
             (+ (current-column)
                (sail-assoc-indent kwop t))
           (sail-back-to-paren-or-indentation)
           (+ (sail-paren-or-indentation-indent)
              (sail-assoc-indent kwop t))))
        (t (+ (if (sail-in-indentation-p)
                  (current-column)
                (sail-paren-or-indentation-indent))
              (sail-assoc-indent kwop t)))))

(defconst sail-=-indent-regexp-1
  (sail-ro "val" "let" "function" "scattered" "foreach" "if"))

(defun sail-compute-=-indent (start-pos)
  (let ((current-column-module-type nil) (kwop1 (sail-find-=-match))
        (next-pos (point)))
    (+ (save-excursion
         (sail-reset-and-kwop kwop1)
         (cond ((string= kwop1 "typedef")
                (sail-find-meaningful-word)
                (cond (t (goto-char start-pos)
                         (beginning-of-line)
                         (+ (sail-add-default-indent
                             (looking-at "[ \t]*[\[|]"))
                            sail-type-indent))))
               ((looking-at sail-=-indent-regexp-1)
                (let ((matched-string (sail-match-string 0)))
                  (setq current-column-module-type (current-column))
                  (sail-assoc-indent matched-string)))
               ((looking-at sail-no-code-after-paren-regexp)
                (setq current-column-module-type
                      (sail-indent-from-paren nil next-pos))
                sail-default-indent)
               (t (setq current-column-module-type
                        (sail-paren-or-indentation-indent))
                  sail-default-indent)))
       (or current-column-module-type
           (current-column)))))

(defun sail-indent-after-next-char ()
  (forward-char 1)
  (sail-skip-blank-and-comments)
  (current-column))

(defconst sail-definitions-regexp
  (sail-ro "and" "val" "typedef" "scattered" "function" "default" "register" "let")
  "Regexp matching definition phrases.")

(defun sail-compute-normal-indent ()
  (let ((leading-operator (looking-at sail-operator-regexp)))
    (beginning-of-line)
    (save-excursion
      (let ((start-pos (point))
            (kwop (sail-find-argument-kwop-clean leading-operator)))
        (cond
          ((not kwop) (current-column))
          ((sail-at-phrase-break-p)
           (sail-find-phrase-indentation t))
          ((or (looking-at "[[{(<]")
               (and (looking-at "[<|]")
                    (char-equal ?\[ (preceding-char))
                    (progn (sail-backward-char) t))
               (and (looking-at "<")
                    (char-equal ?\{ (preceding-char))
                    (progn (sail-backward-char) t)))
           (cond ((looking-at "{ *[A-Z]")
                  (forward-char 1) (skip-syntax-forward " ")
                  (current-column))
                 ((looking-at (sail-no-code-after "[[{(][<|]?"))
                  (sail-indent-from-paren leading-operator start-pos))
                 ((and leading-operator (string= kwop "("))
                  (sail-indent-after-next-char))
                 (t (+ sail-default-indent
                       (sail-indent-from-paren leading-operator start-pos)))))
          ((looking-at (sail-give-keyword-regexp))
           (sail-compute-keyword-indent kwop leading-operator start-pos))
          ((and (string= kwop "=") (not (sail-false-=-p))
                (or (null leading-operator)
                    ;; defining "=", not testing for equality
                    (string-match sail-definitions-regexp
                                  (save-excursion
                                    (sail-find-argument-kwop-clean t)))))
           (sail-compute-=-indent start-pos))
          (nil 0)
          (t (sail-compute-argument-indent leading-operator)))))))

(defun sail-compute-paren-indent (paren-match-p old-point)
  (unless paren-match-p
    (sail-search-forward-paren))
  (let ((looking-at-paren (char-equal ?\( (char-after))) (start-pos (point)))
    (when (or looking-at-paren
              (looking-at (sail-no-code-after "\\(\{\\(.*with[ \t]*\\([[:upper:]].*\\.\\)?\\)?\\|\\[\\)")))
      (if (sail-in-indentation-p)
	  (sail-back-to-paren-or-indentation)
        (sail-indent-from-previous-kwop))
      (when looking-at-paren
        (skip-chars-forward "( \t" start-pos))
      (while (and (looking-at "[([{]")
                  (> (scan-sexps (point) 1)
                     (save-excursion (goto-char old-point)
                                     (line-end-position))))
        (forward-char 1)
        (skip-syntax-forward " "))))
  (current-column))

(defun sail-compute-kwop-indent-general (kwop matching-kwop)
  (let* ((looking-at-matching (looking-at matching-kwop))
         (extra-unindent        ; non-paren code before matching-kwop
          (unless (save-excursion
                    (skip-chars-backward "( \t" (line-beginning-position))
                    (bolp))
            (sail-back-to-paren-or-indentation)
            t)))
    (+ (current-column)
       (sail-add-default-indent
        (or (not (string= kwop "then"))
	    looking-at-matching)))))

(defun ail-compute-kwop-indent (kwop)
  (when (string= kwop "rec")
    (setq kwop "and"))
  (let* ((old-point (point))
         (paren-match-p (looking-at "[|>]?[]})]\\|>\\."))
         (real-pipe (looking-at "|\\([^|]\\|$\\)"))
         (matching-kwop (sail-find-leading-kwop-match kwop)))
    (cond ((looking-at "[[{(][<|]?\\|\\.<")
           (sail-compute-paren-indent paren-match-p old-point))
          ((string= kwop "and")
	   (if (sail-in-indentation-p)
               (current-column)
             (sail-paren-or-indentation-column)))
          ((string= kwop "in")
           (+ (current-column)
              (sail-add-default-indent (string= matching-kwop "let"))))
          ((not (string= kwop "and")) ; pretty general case
           (sail-compute-kwop-indent-general kwop matching-kwop))
          (t (sail-paren-or-indentation-column)))))

(defun sail-indent-to-code (beg-pos match)
  (unless (and (string= match "(")
               (search-forward "->" beg-pos t))
    (forward-char (length match)))
  (sail-skip-blank-and-comments)
  (current-column))

(defun sail-indent-command (&optional from-leading-star)
  "Indent the current line in Sail mode.

Compute new indentation based on Sail syntax."
  (interactive "*")
  (unless from-leading-star
    (sail-auto-fill-insert-leading-star))
  (let ((case-fold-search nil))
   (sail-with-internal-syntax
    (save-excursion
      (back-to-indentation)
      (indent-line-to (max 0 (sail-compute-indent))))
    (when (sail-in-indentation-p) (back-to-indentation)))))

(defun sail-compute-indent ()
  (save-excursion
    (cond
     ((sail-in-comment-p)
      (cond
       ((looking-at "(\\*")
        (if sail-indent-leading-comments
            (save-excursion
              (sail-skip-blank-and-comments)
              (back-to-indentation)
              (current-column))
          (current-column)))
       ((looking-at "\\*\\**)")
        (sail-beginning-of-literal-or-comment-fast)
        (if (sail-leading-star-p)
            (+ (current-column)
               (if (save-excursion
                     (forward-line 1)
                     (back-to-indentation)
                     (looking-at "*")) 1
                 sail-comment-end-extra-indent))
          (+ (current-column) sail-comment-end-extra-indent)))
       (sail-indent-comments
        (let ((star (and (sail-leading-star-p)
                         (looking-at "\\*"))))
          (sail-beginning-of-literal-or-comment-fast)
          (if star (re-search-forward "(") (re-search-forward "(\\*+[ \t]*"))
          (current-column)))
       (t (current-column))))
     ((sail-in-literal-p)
      (current-column))
     ((looking-at "\\<let\\>")
      (if (sail-looking-at-internal-let)
          (if (sail-looking-at-in-let)
              (progn
                (sail-find-meaningful-word)
                (sail-find-in-match)
                (current-column))
            (sail-compute-normal-indent))
        (sail-find-phrase-indentation)))
     ((or (looking-at sail-governing-phrase-regexp)
          (looking-at ";"))
      (sail-find-phrase-indentation))
     ((looking-at ";")
      (sail-find-semicolon-match t))
     ((or (looking-at (sail-give-matching-kwop-regexp))
          (looking-at "\\<rec\\>"))
      (sail-compute-kwop-indent (sail-match-string 0)))
     (t (sail-compute-normal-indent)))))

(defun sail-split-string ()
  "Called whenever a line is broken inside an Sail string literal."
  (insert-before-markers "\\ ")
  (sail-backward-char))

(defadvice newline-and-indent (around
                               sail-newline-and-indent
                               activate)
  "Handle multi-line strings in Sail mode."
  (let ((hooked (and (eq major-mode 'sail-mode) (sail-in-literal-p)))
        (split-mark))
    (when hooked
      (setq split-mark (set-marker (make-marker) (point)))
      (sail-split-string))
    ad-do-it
    (when hooked
      (goto-char split-mark)
      (set-marker split-mark nil))))

(defun sail-electric-rp ()
  "If inserting a ) operator or a comment-end at beginning of line,
reindent the line."
  (interactive "*")
  (let ((electric (and sail-electric-indent
                       (or (sail-in-indentation-p)
                           (char-equal ?* (preceding-char)))
                       (not (sail-in-literal-p))
                       (or (not (sail-in-comment-p))
                           (save-excursion
                             (back-to-indentation)
                             (looking-at "\\*"))))))
    (self-insert-command 1)
    (and electric
         (indent-according-to-mode))))

(defun sail-electric-rc ()
  "If inserting a } operator at beginning of line, reindent the line."
  (interactive "*")
  (let* ((prec (preceding-char))
         (look-bra (and sail-electric-close-vector
                        (not (sail-in-literal-or-comment-p))
                        (not (char-equal ?> prec))))
         (electric (and sail-electric-indent
                        (or (sail-in-indentation-p)
                            (and (char-equal ?> prec)
                                 (save-excursion (sail-backward-char)
                                                 (sail-in-indentation-p))))
                        (not (sail-in-literal-or-comment-p)))))
    (self-insert-command 1)
    (when look-bra
      (save-excursion
        (let ((inserted-char
               (save-excursion
                 (sail-backward-char)
                 (sail-backward-up-list)
                 (cond ((looking-at "{<") ">")
                       (t "")))))
          (sail-backward-char)
          (insert inserted-char))))
    (when electric (indent-according-to-mode))))

(defun sail-electric-rb ()
  "If inserting a ] operator at beginning of line, reindent the line.

Reindent also if ] is inserted after a | operator at beginning of line.
Also, if the matching [ is followed by a | and this ] is not preceded
by |, insert one |."
  (interactive "*")
  (let* ((prec (preceding-char))
         (look-pipe-or-bra (and sail-electric-close-list
                                (not (sail-in-literal-or-comment-p))
                                (not (and (char-equal ?| prec)
                                          (not (char-equal
                                                (save-excursion
                                                  (sail-backward-char)
                                                  (preceding-char)) ?\[))))))
         (electric (and sail-electric-indent
                        (or (sail-in-indentation-p)
                            (and (char-equal ?| prec)
                                 (save-excursion (sail-backward-char)
                                                 (sail-in-indentation-p))))
                        (not (sail-in-literal-or-comment-p)))))
    (self-insert-command 1)
    (when look-pipe-or-bra
      (save-excursion
        (let ((inserted-char
               (save-excursion
                 (sail-backward-char)
                 (sail-backward-up-list)
                 (cond ((looking-at "\\[|") "|")
                       (t "")))))
          (sail-backward-char)
          (insert inserted-char))))
    (when electric (indent-according-to-mode))))

(defun sail-abbrev-hook ()
  "If inserting a leading keyword at beginning of line, reindent the line."
  (unless (sail-in-literal-or-comment-p)
    (let* ((bol (line-beginning-position))
           (kw (save-excursion
                 (and (re-search-backward "^[ \t]*\\(\\w\\|_\\)+\\=" bol t)
                      (sail-match-string 1)))))
      (when kw
        (insert " ")
        (indent-according-to-mode)
        (backward-delete-char-untabify 1)))))

(defun sail-skip-to-end-of-phrase ()
  (let ((old-point (point)))
    (when (and (string= (sail-find-meaningful-word) ";")
               (char-equal (preceding-char) ?\;))
      (setq old-point (1- (point))))
    (goto-char old-point)
    (let ((kwop (sail-find-meaningful-word)))
      (goto-char (+ (point) (length kwop))))))

(defun sail-skip-blank-and-comments ()
  (skip-syntax-forward " ")
  (while (and (not (eobp)) (sail-in-comment-p)
              (search-forward "*)" nil t))
    (skip-syntax-forward " ")))

(defun sail-skip-back-blank-and-comments ()
  (skip-syntax-backward " ")
  (while (save-excursion (sail-backward-char)
                         (and (> (point) (point-min)) (sail-in-comment-p)))
    (sail-backward-char)
    (sail-beginning-of-literal-or-comment) (skip-syntax-backward " ")))

(defun sail-find-phrase-beginning (&optional stop-at-and)
  "Find `real' phrase beginning and return point."
  (beginning-of-line)
  (sail-skip-blank-and-comments)
  (end-of-line)
  (sail-skip-to-end-of-phrase)
  (let ((old-point (point)) (pt (point)))
    (if stop-at-and
        (sail-find-kwop sail-find-phrase-beginning-and-regexp "and")
      (sail-find-kwop sail-find-phrase-beginning-regexp))
    (while (and (> (point) (point-min)) (< (point) old-point)
                (or (not (looking-at sail-find-phrase-beginning-and-regexp))
                    (and (looking-at "\\<let\\>")
                         (sail-looking-at-internal-let))
                    (and (looking-at "\\<and\\>")
                         (save-excursion
                           (sail-find-and-match)
                           (sail-looking-at-internal-let)))
		    )
      (when (= pt (point))
        (error "sail-find-phrase-beginning: inf loop at %d" pt))
      (setq pt (point))
      (if (looking-at "\\<end\\>")
          (sail-find-match)
        (unless (bolp) (sail-backward-char))
        (setq old-point (point))
        (if stop-at-and
            (sail-find-kwop sail-find-phrase-beginning-and-regexp "and")
          (sail-find-kwop sail-find-phrase-beginning-regexp))))
    (when (sail-at-phrase-break-p)
      (end-of-line) (sail-skip-blank-and-comments))
    (back-to-indentation)
    (point))))

(defun sail-imenu-prev-index-position ()
  "The default value for `imenu-prev-index-position-function'."
  (let ((pos (point)) ret)
    (while (and (<= 0 pos)
                (<= pos (setq ret (sail-find-phrase-beginning t))))
      (setq pos (goto-char (1- pos))))
    (and (<= 0 pos) ret)))

(defun sail-imenu-extract-index-name ()
  "The default value for `imenu-extract-index-name-function'."
  (forward-sexp 1)
  (skip-syntax-forward " ")
  (buffer-substring-no-properties (point) (scan-sexps (point) 1)))

(defun sail-mark-phrase ()
  "Put mark at end of this Sail phrase, point at beginning.
The Sail phrase is the phrase just before the point."
  (interactive)
  (let ((pair (sail-discover-phrase)))
    (goto-char (nth 1 pair)) (push-mark (nth 0 pair) t t)))

(defun sail-next-phrase (&optional quiet stop-at-and)
  "Skip to the beginning of the next phrase."
  (interactive "i")
  (goto-char (save-excursion
               (nth 2 (sail-discover-phrase quiet stop-at-and))))
  (cond
   ((looking-at "}")
    (forward-char 1)
    (sail-skip-blank-and-comments))
   ((looking-at ")")
    (forward-char 1)
    (sail-skip-blank-and-comments))
   ((looking-at ";")
    (forward-char 1)
    (sail-skip-blank-and-comments))))

(defun sail-previous-phrase ()
  "Skip to the beginning of the previous phrase."
  (interactive)
  (beginning-of-line)
  (sail-skip-to-end-of-phrase)
  (sail-discover-phrase))

(defun sail-indent-phrase ()
  "Depending of the context: justify and indent a comment,
or indent all lines in the current phrase."
  (interactive)
  (save-excursion
    (back-to-indentation)
    (if (sail-in-comment-p)
        (let* ((cobpoint (save-excursion
                           (sail-beginning-of-literal-or-comment)
                           (point)))
               (begpoint (save-excursion
                           (while (and (> (point) cobpoint)
                                       (sail-in-comment-p)
                                       (not (looking-at "^[ \t]*$")))
                             (forward-line -1))
                           (max cobpoint (point))))
               (coepoint (save-excursion
                           (while (sail-in-comment-p)
                             (re-search-forward "\\*)" nil 'end))
                           (point)))
               (endpoint (save-excursion
                           (re-search-forward "^[ \t]*$" coepoint 'end)
                           (line-beginning-position 2)))
               (leading-star (sail-leading-star-p)))
          (goto-char begpoint)
          (while (and leading-star
                      (< (point) endpoint)
                      (not (looking-at "^[ \t]*$")))
            (forward-line 1)
            (back-to-indentation)
            (when (looking-at "\\*\\**\\([^)]\\|$\\)")
              (delete-char 1)
              (setq endpoint (1- endpoint))))
          (goto-char (min (point) endpoint))
          (fill-region begpoint endpoint)
          (re-search-forward "\\*)" nil 'end)
          (setq endpoint (point))
          (when leading-star
            (goto-char begpoint)
            (forward-line 1)
            (if (< (point) endpoint)
                (sail-auto-fill-insert-leading-star t)))
          (indent-region begpoint endpoint nil))
      (let ((pair (sail-discover-phrase)))
        (indent-region (nth 0 pair) (nth 1 pair) nil)))))

(defun sail-complete (arg)
  "Completes qualified Sail identifiers."
  (interactive "p")
  (modify-syntax-entry ?_ "w" sail-mode-syntax-table)
  (caml-complete arg)
  (modify-syntax-entry ?_ "_" sail-mode-syntax-table))

(defun sail-ensure-space ()
  (let ((prec (preceding-char)))
    (when (and prec (not (char-equal ?\  (char-syntax prec))))
      (insert " "))))

(defun sail-insert-if-form ()
  "Insert a nicely formatted if-then-else form, leaving a mark after else."
  (interactive "*")
  (sail-ensure-space)
  (let ((old (point)))
    (insert "if\n\nthen\n\nelse\n")
    (end-of-line)
    (indent-region old (point) nil)
    (indent-according-to-mode)
    (push-mark)
    (forward-line -2)
    (indent-according-to-mode)
    (forward-line -2)
    (indent-according-to-mode)))

(defun sail-insert-let-form ()
  "Insert a nicely formatted let-in form, leaving a mark after in."
  (interactive "*")
  (sail-ensure-space)
  (let ((old (point)))
    (insert "let  in\n")
    (end-of-line)
    (indent-region old (point) nil)
    (indent-according-to-mode)
    (push-mark)
    (beginning-of-line)
    (backward-char 4)
    (indent-according-to-mode)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                               Menu support

(defun sail-about ()
  (interactive)
  (describe-variable 'sail-mode-version))

(defun sail-short-cuts ()
  "Short cuts for the sail mode:
\\{sail-mode-map}

"
  (interactive)
  (describe-function 'sail-short-cuts))

(defun sail-help ()
  (interactive)
  (describe-function 'sail-mode))

(defvar sail-definitions-menu (list ["Scan..." sail-list-definitions t])
  "Initial content of the definitions menu.")
(make-variable-buffer-local 'sail-definitions-menu)

(defvar sail-definitions-menu-last-buffer nil)
(defvar sail-definitions-keymaps nil)

(defun sail-build-menu ()
  (easy-menu-define
   sail-mode-menu (list sail-mode-map)
   "Sail Mode Menu."
   '("Sail"
     ("Sail Forms"
      ["let .. in .." sail-insert-let-form t]
      ["if .. then .. else .." sail-insert-if-form t])
     "---"
     ["Customize Sail Mode..." (customize-group 'sail) t]
     ("Sail Options" ["Dummy" nil t])
     "---"
     ["About" sail-about t]
     ["Short Cuts" sail-short-cuts]
     ["Help" sail-help t]))
  (easy-menu-add sail-mode-menu)
  (sail-update-options-menu)
  ;; Save and update definitions menu
  (when (functionp 'easy-menu-create-menu)
    ;; Patch for Emacs
    (add-hook 'menu-bar-update-hook
              'sail-with-emacs-update-definitions-menu)
    (make-local-variable 'sail-definitions-keymaps)
    (setq sail-definitions-keymaps
          (cdr (easy-menu-create-menu
                "Definitions" sail-definitions-menu)))
    (setq sail-definitions-menu-last-buffer nil)))

(defun sail-update-definitions-menu ()
  (when (eq major-mode 'sail-mode)
    (easy-menu-change
     '("Sail") "Definitions"
     sail-definitions-menu)))

(defun sail-with-emacs-update-definitions-menu ()
  (when (current-local-map)
    (let ((keymap
           (lookup-key (current-local-map) [menu-bar Sail Definitions])))
      (if (and
           (keymapp keymap)
           (not (eq sail-definitions-menu-last-buffer (current-buffer))))
          (setcdr keymap sail-definitions-keymaps)
        (setq sail-definitions-menu-last-buffer (current-buffer))))))

(defun sail-toggle-option (symbol)
  (interactive)
  (set symbol (not (symbol-value symbol)))
  (when (eq 'sail-use-abbrev-mode symbol)
    (abbrev-mode sail-use-abbrev-mode)) ; toggle abbrev minor mode
  (sail-update-options-menu))

(defun sail-update-options-menu ()
  (easy-menu-change
   '("Sail") "Sail Options"
   (mapcar (lambda (pair)
             (if (consp pair)
                 (vector (car pair)
                         (list 'sail-toggle-option (cdr pair))
                         ':style 'toggle
                         ':selected (nth 1 (cdr pair))
                         ':active t)
               pair)) sail-options-list))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                             Definitions List

;; Designed from original code by M. Quercia

(defconst sail--id-regexp "[[:alpha:]][_'[:alnum:]]*")

(defconst sail-definitions-bind-skip-regexp
  (concat (sail-ro "rec" "typedef" "function") "\\|'"
          sail--id-regexp "\\|('.*)")
  "Regexp matching stuff to ignore after a binding keyword.")

(defconst sail-identifier-regexp (concat "\\<" sail--id-regexp "\\>"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                             Hooks and Exit

(eval-when-compile
  (autoload 'speedbar-add-supported-extension "speedbar"))
(when (require 'speedbar nil t)
  (speedbar-add-supported-extension
   '(".sail")))

(defvar sail-load-hook nil
  "This hook is run when Sail is loaded in. It is a good place to put
key-bindings or hack Font-Lock keywords...")

(run-hooks 'sail-load-hook)

(provide 'sail_mode)

;;; sail.el ends here
