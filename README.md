This is the artifact of *Derivative-Guided Symbolic Execution* under
submission to POPL 2025. The derivative-guided symbolic execution engine
**HATch**, along with its derivative-free variant, are provided. Please
follow the instructions below for installation and reproduction of
experiment results.

# Requirement and Installation

We recommend the use of machines with at least 8 GB memory. The artifact
depends on [opam](https://opam.ocaml.org/doc/Install.html) (version 2.X)
to build, and [Emacs](https://www.gnu.org/software/emacs/download.html)
(version

1.  Lisp for producing experiment results. A VDI disk image file is

attached with the environment set up and can be opened in VirtualBox or
similar.

To install **HATch** manually, one may create an OCaml compiler switch,
activate the environment in the current shell, install dependencies, and
build the artifact, as follows:

``` shell
opam switch create hatch 4.14.0+flambda
eval $(opam env)
opam install core core_unix ppx_jane ppx_inline_test ppx_assert ppx_sexp_conv ppx_optcomp ppx_hash ppx_compare ppx_let yojson dolog ocolor z3 qcheck choice oseq ocamlgraph
dune build
```

# Falsify Individual ADT implementations

```{=org}
#+PROPERTY: header-args:shell :results verbatim code :prologue exec 2>&1
```
Folder `data/ri`{.verbatim} stores various benchmarks in its subfolders,
each corresponding to an abstract data type (ADT) and its underlying
stateful representation type. Specifically, Each subfolder contains

-   a safety property represented by a symbolic regular expression in
    \`ri.ml\`
-   the implementation of one or more methods of the ADT, both correct
    (without \`~buggy~\` postfix) and buggy (with \`~buggy~\` postfix)
-   the refinement-type-style specification that manifest the safety
    properties and accompany the implementation in the same file

See [*Experiments*]{.spurious-link target="*Experiments"} for the
complete list of methods associated with each pair of ADT and its
representation type.

One may run **HATch** on the implementation of buggy methods like
`Stack_LinkedList/remove_aux`{.verbatim} (in place of
`${bench}`{.verbatim}) as follows:

``` {#hatch .shell var="bench=\"\"" post="get_time(str=\"fail\", out=*this*)"}
timeout -v 1m dune exec -- bin/main.exe symb-exec meta-config.json data/ri/${bench}_buggy.ml -empty-aware -exec-bound 20 -eff-append-bound 5
```

In seconds, **HATch** falsifies the implementation by finding an
execution path with

-   \`Phi\` : the path condition collected along the execution path
-   \`Trace\` : the trace of symbolic events that witness the execution
    path
-   \`R~cont~\` : a symbolic regular expression accepting traces that
    the execution can produce without violating the safety property
-   \`expr\` : the term under execution

```{=org}
#+call: hatch[:post]("LinkedList_KVStore/remove_aux")
```
``` shell
Preemptive Hatch
Phi    = b_0:{v:Ptr.t | true}, a_0:{v:Ptr.t | true}, hd:{v:Ptr.t | ¬is_nullptr b_0}, vl:{v:Elem.t | true}, a_3:{v:Ptr.t | true}, next_2:{v:Ptr.t | v == a_3}, x_26_2:{v:bool | ¬v}, a_6:{v:Elem.t | true}, x_27_2:{v:Elem.t | v == a_6}, x_28_2:{v:bool | (v <=> x_27_2 == vl) ∧ v}, a_9:{v:Ptr.t | true}, x_29_2:{v:Ptr.t | v == a_9}
Trace  = ⟨putNext x_0 x_1 = vret | x_0 == a_0 ∧ x_1 == b_0 ∧ ¬(x_0 == hd ∧ x_1 == a_3) ∧ x_0 == next_2 ∧ x_1 == a_9⟩; ⟨putNext x_0 x_1 = vret | ¬(x_0 == a_0 ∧ x_1 == b_0) ∧ ¬x_0 == a_0 ∧ x_0 == hd ∧ x_1 == a_3 ∧ ¬(x_0 == next_2 ∧ x_1 == a_9) ∧ ¬x_0 == next_2⟩; ⟨putVal x_0 x_1 = vret | x_0 == next_2 ∧ x_1 == a_6⟩; ⟨getNext x_0 = vret | vret == a_3 ∧ x_0 == hd⟩; ⟨getVal x_0 = vret | vret == a_6 ∧ x_0 == next_2⟩; ⟨getNext x_0 = vret | vret == a_9 ∧ x_0 == next_2⟩; ⟨putNext x_0 x_1 = vret | x_0 == hd ∧ x_1 == x_29_2 ∧ ¬((¬(¬x_0 == a_0 ∧ x_1 == b_0) ∧ ¬(¬x_1 == b_0 ∧ x_0 == a_0)) ∨ (¬(¬x_0 == a_0 ∧ x_1 == b_0) ∧ ¬x_1 == b_0 ∧ x_0 == a_0))⟩
R_cont = ∅
expr   =
(let (f_1 : unit) = (() : unit) in (f_1 : unit) : unit)
DT(LinkedList)  Task 1(remove_aux): exec time 1.754225(s), check failed
```

In this case, \`Phi\` and \`Trace\` are satisfiable, e.g., the
associated state is reachable, and \`R~cont~\` is empty. Therefore,
**HATch** determines that the execution path is falsified.

The derivative-free variant of `HATch`{.verbatim} can be run as follows:

``` {#naive .shell var="bench=\"\"" post="get_time(str=\"fail\", out=*this*)"}
timeout -v 1m dune exec -- bin/main.exe symb-exec meta-config.json data/ri/${bench}_buggy.ml -no-deriv -exec-bound 20
```

And it

```{=org}
#+call: naive[:post]("ConnectedGraph_Set/add_node")
```
``` shell
timeout: sending signal TERM to command ‘dune’
```

```{=org}
#+call: naive[:post]("LinkedList_KVStore/remove_aux")
```
``` shell
timeout: sending signal TERM to command ‘dune’
```

The baseline verifier that is designed to check automata-augmented
refinement type can be run as follows:

``` {#verify .shell var="bench=\"\"" post="get_time(str=\"fail\", out=*this*)"}
timeout -v 1m dune exec -- bin/main.exe ri-type-check meta-config.json data/ri/${bench}_buggy.ml
```

The verifier times out after 1 minute.

```{=org}
#+call: verify[:post]("LinkedList_KVStore/remove_aux")
```
``` shell
timeout: sending signal TERM to command ‘dune’
```

# Experiments

The data of Table 1 in the paper is produced using [org-babel shipped
with Emacs](https://orgmode.org/worg/org-contrib/babel/) and shown
below.

  program                                 HATch   SpeedUp   SpeedUp   Naive   HAT
  --------------------------------------- ------- --------- --------- ------- -------
  Stack~LinkedList~/cons                  0.51     × 4.9     × 3.2    2.50    1.64
  Stack~LinkedList~/concat~aux~           0.25    O/M        × 13.2   O/M     3.29
  Stack~KVStore~/cons                     1.11    T/O        × 4.6    T/O     5.09
  Stack~KVStore~/concat~aux~              0.94    O/M        × 6.5    O/M     6.08
  Queue~LinkedList~/append                0.73     × 2.5     × 2.7    1.85    1.97
  Queue~Graph~/append                     1.75    T/O        × 7.4    T/O     12.89
  Set~KVStore~/insert                     0.87    T/O        × 1.4    T/O     1.25
  Set~Tree~/insert~aux~                   1.10     × 40.7    × 11.1   44.72   12.24
  Heap~LinkedList~/insert~aux~            0.11     × 12.9    × 13.2   1.42    1.45
  Heap~Tree~/insert~aux~                  1.00     × 2.4     × 2.5    2.44    2.50
  MinSet~Set~/minset~singleton~           1.14     × 1.3     × 1.3    1.48    1.50
  MinSet~Set~/minset~insert~              1.32     × 9.0     × 9.9    11.93   13.10
  MinSet~KVStore~/minset~singleton~       0.66    T/O        × 4.3    T/O     2.83
  MinSet~KVStore~/minset~insert~          1.95     × 10.7    × 14.9   20.79   29.04
  LazySet~Tree~/insert~aux~               1.09     × 4.8     × 11.5   5.25    12.58
  LazySet~Set~/lazy~insert~               0.49     × 1.2     × 1.3    0.60    0.65
  LazySet~KVStore~/insert~aux~            0.88     × 49.8    × 1.5    43.81   1.34
  DFA~KVStore~/add~transition~            0.66     × 29.9    × 29.9   19.73   19.72
  DFA~KVStore~/del~transition~            1.04     × 15.0    × 15.2   15.60   15.86
  DFA~Graph~/add~transition~              0.98     × 12.9    × 12.8   12.62   12.51
  DFA~Graph~/del~transition~              0.97     × 16.5    × 16.5   15.96   16.05
  ConnectedGraph~Set~/singleton           0.27    T/O        × 16.4   T/O     4.44
  ConnectedGraph~Set~/add~node~           1.31    O/M        × 9.9    O/M     12.96
  ConnectedGraph~Set~/add~transition~     1.44    O/M        × 11.2   O/M     16.07
  ConnectedGraph~Graph~/singleton         1.13     × 1.7     × 1.8    1.97    1.99
  ConnectedGraph~Graph~/add~node~         2.05     × 6.0     × 6.1    12.37   12.47
  ConnectedGraph~Graph~/add~transition~   2.38     × 20.0    × 16.2   47.58   38.53
  ColoredGraph~Graph~/add~edge~           3.68    T/O       T/O       T/O     T/O
  ColoredGraph~KVStore~/add~edge~         7.82    T/O       T/O       T/O     T/O
  LinkedList~KVStore~/remove              7.03    O/M       T/O       O/M     T/O

```{=org}
#+TBLFM: $5='(org-sbe "naive" (path $$1))::$2='(org-sbe "hatch" (path $$1))::$6='(org-sbe "verify" (path $$1))
```
```{=org}
#+TBLFM: $3='(org-sbe "ratio" (x $$5) (y $$2))::$4='(org-sbe "ratio" (x $$6) (y $$2))
```
One may regenerate the content of the table in place using the following
script assuming a recent installation of `Emacs`{.verbatim} and
`pandoc`{.verbatim}.

``` shell
emacs --batch -l ob -l ob-shell --eval "
  (let ((org-confirm-babel-evaluate nil))
    (dolist (file command-line-args-left)
      (with-current-buffer (find-file-noselect file)
        (org-table-recalculate-buffer-tables)
        (save-buffer))))
" README.org
pandoc -s README.org -o README.md
```
