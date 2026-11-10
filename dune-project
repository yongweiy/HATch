(lang dune 3.11)

(name coreeff)

(generate_opam_files true)

(source
 (github yongweiy/HATch))

(authors "Zhe Zhou" "Yongwei Yuan")

(maintainers "Yongwei Yuan")

(package
 (name coreeff)
 (synopsis "HATch: falsifying representation invariants with Hoare Automata Types")
 (description
  "Type-and-effect inference with Hoare Automata Types (HATs) and symbolic finite automata, used to find incorrectness witnesses for ADT implementations.")
 (allow_empty)
 ; language_utils (yongweiy's fork; not on opam-repository, and its opam file
 ; declares no dependencies) is vendored as a git submodule under vendor/ and
 ; built in this workspace, so its requirements (containers, dolog, ppx_here,
 ; yojson, ...) are listed here too.
 (depends
  (ocaml
   (and
    (>= 5.1)
    (< 5.5)))
  (core
   (and
    (>= v0.17)
    (< v0.18)))
  (core_unix
   (and
    (>= v0.17)
    (< v0.18)))
  (core_kernel
   (and
    (>= v0.17)
    (< v0.18)))
  (ppx_jane
   (and
    (>= v0.17)
    (< v0.18)))
  ppx_let
  ppx_inline_test
  ppx_assert
  ppx_optcomp
  ppx_compare
  ppx_sexp_conv
  ppx_hash
  ppx_here
  containers
  yojson
  dolog
  ocolor
  qcheck
  choice
  oseq
  ocamlgraph
  ; z3 4.15.2 answers `unknown` (incomplete quantifiers) on queries from
  ; FileSystem_KVStore/delete_buggy, losing that benchmark; 4.13.3 solves them.
  ; (z3 >= 4.16 also needs C++20 <format>, i.e. GCC >= 13.)
  (z3
   (< 4.14))))
