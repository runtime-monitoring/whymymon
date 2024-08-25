(lang dune 3.0)

(name whymymon)

(generate_opam_files true)

(source
 (github runtime-monitoring/whymymon))

(authors
 "Leonardo Lima <hi@nameless.computer>"
 "Dmitriy Traytel <traytel@di.ku.dk>")

(maintainers
 "Leonardo Lima <hi@nameless.computer>"
 "Dmitriy Traytel <traytel@di.ku.dk>")

(license LICENSE)

(documentation https://github.com/runtime-monitoring/whymymon)

(using menhir 2.0)

(package
 (name whymymon)
 (synopsis "")
 (description "")
 (depends
  (ocaml (>= 5.2.0))
  (dune (>= 3.0))
  (core_kernel (>= v0.17.0))
  (base (>= v0.17.1))
  (menhir (>= 20240715))
  (zarith (>= 1.14))
  (zarith_stubs_js (>= v0.17.0)))
 (tags
  (explainable "first-order" runtime monitoring)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project