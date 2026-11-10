# Developer entry points.  Prerequisites (Homebrew):
#
#   brew install opam gmp pkgconf
#   opam init --bare --no-setup        # once per machine
#
# The OCaml toolchain lives in a project-local opam switch (./_opam), pinned by
# coreeff.opam.locked.  `opam` auto-selects it inside this directory; the
# .envrc loads it into the shell for direnv users.

OPAM_EXEC := opam exec --
BENCH_ARGS ?=

# Homebrew's gmp.pc reports the versioned Cellar path; point pkg-config at the
# stable opt/ symlink instead so zarith's recorded -L/-rpath survive
# `brew upgrade gmp`.
BREW_GMP := $(shell brew --prefix gmp 2>/dev/null)
ifneq ($(BREW_GMP),)
export PKG_CONFIG_GMP_PREFIX := $(BREW_GMP)
export PKG_CONFIG_GMP_LIBDIR := $(BREW_GMP)/lib
endif

.PHONY: all switch deps lock build bench clean

all: build

# Create ./_opam and install the exact locked dependency set (incl. compiler).
# gmp comes from Homebrew (found via pkg-config by conf-gmp/zarith), so skip
# opam's yum/dnf check for the gmp-devel system package.
switch:
	opam switch create . --empty --yes
	opam option --switch . 'depext-bypass=["gmp-devel"]'
	$(MAKE) deps

# (Re)install dependencies from the lock file into the existing switch.
deps:
	opam install . --deps-only --locked --yes

# Refresh coreeff.opam.locked after editing dependencies in dune-project.
lock:
	$(OPAM_EXEC) dune build coreeff.opam
	opam install . --deps-only --yes
	opam lock . --yes

build:
	$(OPAM_EXEC) dune build --profile release

# Paper evaluation table; outputs go to benchmark_results/.
# Pass options via BENCH_ARGS, e.g. make bench BENCH_ARGS='--only Set --no-hatch'
bench: build
	python3 scripts/run_paper_benchmarks.py $(BENCH_ARGS)

clean:
	$(OPAM_EXEC) dune clean
