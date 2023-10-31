(lang dune 3.0)

(using menhir 2.1)
(using dune_site 0.1)

(name sail)
(version 0.17)

(generate_opam_files true)

(wrapped_executables false)

(source
  (github rems-project/sail))

(maintainers "Sail Devs <cl-sail-dev@lists.cam.ac.uk>")

(license BSD-2-Clause)

(authors
  "Alasdair Armstrong"
  "Thomas Bauereiss"
  "Brian Campbell"
  "Shaked Flur"
  "Jonathan French"
  "Kathy Gray"
  "Robert Norton"
  "Christopher Pulte"
  "Peter Sewell"
  "Mark Wassell")

(package
  (synopsis "Helper tool for compiling Sail")
  (name sail_manifest))

(package
  (sites (share plugins))
  (name libsail)
  (synopsis "Sail is a language for describing the instruction semantics of processors")
  (description "\
Sail is a language for describing the instruction-set
architecture (ISA) semantics of processors. Sail aims to provide a
engineer-friendly, vendor-pseudocode-like language for describing
instruction semantics. It is essentially a first-order imperative
language, but with lightweight dependent typing for numeric types and
bitvector lengths, which are automatically checked using Z3. It has
been used for several papers, available from
http://www.cl.cam.ac.uk/~pes20/sail/.
")
  (depends
    (dune-site (>= 3.0.2))
    (bisect_ppx (and :dev (>= "2.5.0")))
    (menhir (and (>= 20180523) :build))
    (ott (and (>= 0.28) :build))
    (lem (>= "2018-12-14"))
    (linksem (>= "0.3"))
    conf-gmp
    conf-zlib
    (yojson (>= 1.6.0))
    (pprint (>= 20220103))))

(package
  (name sail_ocaml_backend)
  (synopsis "Sail to OCaml translation")
  (depends
    (libsail (= :version))
    (base64 (>= 3.1.0))))

(package
  (name sail_c_backend)
  (synopsis "Sail to C translation")
  (depends
    (libsail (= :version))))

(package
  (name sail_smt_backend)
  (synopsis "Sail to C translation")
  (depends
    (libsail (= :version))))

(package
  (name sail_sv_backend)
  (synopsis "Sail to Systemverilog translation")
  (depends
    (libsail (= :version))))

(package
  (name sail_lem_backend)
  (synopsis "Sail to Lem translation")
  (depends
    (libsail (= :version))))

(package
  (name sail_coq_backend)
  (synopsis "Sail to Coq translation")
  (depends
    (libsail (= :version))))

(package
  (name sail_output)
  (synopsis "Example Sail output plugin")
  (depends
    (libsail (= :version))))

(package
  (name sail_latex_backend)
  (synopsis "Sail to LaTeX formatting")
  (depends
    (libsail (= :version))
    (omd (and (>= 1.3.1) (< 1.4.0)))))

(package
  (name sail_doc_backend)
  (synopsis "Sail documentation generator")
  (depends
    (libsail (= :version))
    (base64 (>= 3.1.0))
    (omd (and (>= 1.3.1) (< 1.4.0)))))

(package
  (name sail)
  (synopsis "Sail is a language for describing the instruction semantics of processors")
  (description "\
Sail is a language for describing the instruction-set
architecture (ISA) semantics of processors. Sail aims to provide a
engineer-friendly, vendor-pseudocode-like language for describing
instruction semantics. It is essentially a first-order imperative
language, but with lightweight dependent typing for numeric types and
bitvector lengths, which are automatically checked using Z3. It has
been used for several papers, available from
http://www.cl.cam.ac.uk/~pes20/sail/.
")
  (depends
    (libsail (= :version))
    (sail_manifest (and (= :version) :build))
    (sail_ocaml_backend (and (= :version) :post))
    (sail_c_backend (and (= :version) :post))
    (sail_smt_backend (and (= :version) :post))
    (sail_sv_backend (and (= :version) :post))
    (sail_lem_backend (and (= :version) :post))
    (sail_coq_backend (and (= :version) :post))
    (sail_latex_backend (and (= :version) :post))
    (sail_doc_backend (and (= :version) :post))
    (sail_output (and (= :version) :post))
    (linenoise (>= 1.1.0))))
