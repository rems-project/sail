(lang dune 3.0)

(using menhir 2.1)
(using dune_site 0.1)

(name sail)
(version 0.15)

(generate_opam_files true)

(wrapped_executables false)

(source
  (github rems-project/sail))

(maintainers "Sail Devs <cl-sail-dev@lists.cam.ac.uk>")

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
    (sail_manifest :version)
    (ott (and (>= 0.28) :build))
    (lem (>= "2018-12-14"))
    (linksem (>= "0.3"))
    conf-gmp
    conf-zlib
    (yojson (>= 1.6.0))
    pprint))

(package
  (name sail_ocaml_backend)
  (synopsis "Sail to OCaml translation")
  (depends
    (libsail :version)
    (base64 (>= 3.1.0))))

(package
  (name sail_c_backend)
  (synopsis "Sail to C translation")
  (depends
    (libsail :version)))

(package
  (name sail_smt_backend)
  (synopsis "Sail to C translation")
  (depends
    (libsail :version)))    

(package
  (name sail_lem_backend)
  (synopsis "Sail to Lem translation")
  (depends
    (libsail :version)))

(package
  (name sail_coq_backend)
  (synopsis "Sail to Coq translation")
  (depends
    (libsail :version)))

(package
  (name sail_output)
  (synopsis "Example Sail output plugin")
  (depends
    (libsail :version)))

(package
  (name sail_latex_backend)
  (synopsis "Sail to LaTeX formating")
  (depends
    (libsail :version)
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
    (libsail :version)
    (linenoise (>= 1.1.0))))
