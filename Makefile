# idris2-native: Idris 2, as the submodule `Idris2` pins it, with the native
# code generator.
#
#   make upstream   build the pinned Idris 2, its libraries and its API
#                   package into build/prefix, with the `idris2` in PATH
#                   bootstrapping it (once, and after moving the pin)
#   make            build idris2-native, install its modules as the package
#                   `idris2-native`, and build with it the runtime, the
#                   package `idris2-native-runtime`, into build/prefix; each
#                   only when its sources changed since
#   make test       run the tests; `only=native/term001` runs some
#   make lint       the product's code against the linter's rules
#                   (tools/lint), and its architectural health
#   make gate       what a change must pass: the tests and the lint, run at
#                   once, after one build
#   make release    idris2-native compiled as one whole program, into
#                   build/release/exec: what to measure compile times with
#
# The build of idris2-native is incremental: each module is compiled to its
# own Chez object as it is checked, and the executable links them, so a
# change rebuilds what it changed, in seconds. The executable runs slower
# than one compiled as one whole program, since Chez cannot inline across
# the objects; `make release` builds that one, for measurements.
#   make health     the architectural health with what costs it most,
#                   under each component; `offenders=20` lists more
#   make scaling    the backend's phases against the size of the program;
#                   `sizes="64 128"` chooses the sizes
#
# The submodule is never edited: building it writes only files that it
# ignores.

PREFIX := $(CURDIR)/build/prefix
UPSTREAM_IDRIS2 := $(PREFIX)/bin/idris2
TARGET := $(CURDIR)/build/exec/idris2-native
NAME_VERSION := idris2-0.8.0
threads ?= $(shell nproc 2>/dev/null || echo 1)

# The libraries the bootstrapping `idris2` finds are its own; everything
# after uses the pinned Idris 2's, in the prefix.
WITH_PREFIX := IDRIS2_PREFIX=$(PREFIX)

.PHONY: all upstream native release linter testbin test lint gate health check-source scaling clean

all: native

# The API package is built incrementally, as the libraries are, so that
# idris2-native's incremental build links its objects.
upstream:
	$(MAKE) -C Idris2 PREFIX=$(PREFIX)
	$(MAKE) -C Idris2 install PREFIX=$(PREFIX)
	$(WITH_PREFIX) IDRIS2_INC_CGS=chez $(MAKE) -C Idris2 install-api PREFIX=$(PREFIX) IDRIS2_BOOT=$(UPSTREAM_IDRIS2)

# What a build depends on: its sources, and the pinned Idris it is built by.
NATIVE_SOURCES := $(shell find src -name '*.idr') idris2-native.ipkg
RUNTIME_SOURCES := $(shell find runtime/Native -name '*.idr') runtime/idris2-native-runtime.ipkg

native: build/runtime.stamp

build/native.stamp: $(NATIVE_SOURCES) $(UPSTREAM_IDRIS2)
	$(WITH_PREFIX) IDRIS2_INC_CGS=chez $(UPSTREAM_IDRIS2) --install idris2-native.ipkg
	touch $@

# The runtime is built by idris2-native itself, so that its flat functions
# are checked as its modules are built.
build/runtime.stamp: build/native.stamp $(RUNTIME_SOURCES)
	cd runtime && $(WITH_PREFIX) $(TARGET) --install idris2-native-runtime.ipkg
	touch $@

release:
	$(WITH_PREFIX) $(UPSTREAM_IDRIS2) --build-dir build/release --output-dir build/release/exec --build idris2-native.ipkg

# The linter is an Idris program of its own, on the API of the pinned Idris.
LINTER := $(CURDIR)/tools/lint/build/exec/idris2-native-lint

linter:
	cd tools/lint && $(WITH_PREFIX) $(UPSTREAM_IDRIS2) --build idris2-native-lint.ipkg

testbin:
	cd tests && $(WITH_PREFIX) $(UPSTREAM_IDRIS2) --build tests.ipkg

test: native linter testbin
	cd tests && $(WITH_PREFIX) NAME_VERSION=$(NAME_VERSION) ./build/exec/runtests $(TARGET) \
	  --timing --failure-file failures --threads $(threads) --only "$(only)" < /dev/null

# The tests and the lint at once, after one build: the lint reads the
# build's TTCs and runs nothing the tests do.
gate:
	$(MAKE) --no-print-directory --output-sync=target -j2 test lint

# Findings with their positions, then the health score; fails on a finding
# or a score under the gate's minimum. The rules over what the modules use
# read the TTCs of their build, so the product is built first.
lint: native linter
	$(WITH_PREFIX) $(LINTER) --resolved src runtime tools/lint/src --programs tests/native tests/flat tests/Main.idr
	$(WITH_PREFIX) $(LINTER) --resolved --health --minimum 80 src runtime

# The architectural health, each component with the offenders that cost it
# most: what to change to raise it.
offenders ?= 10
health: native linter
	$(WITH_PREFIX) $(LINTER) --resolved --health --offenders $(offenders) src runtime

# One source file type checked as its package builds it, quietly, failing
# if it does not check: `SOURCE=src/...`, `runtime/...` (by idris2-native,
# which checks the flat functions) or `tools/lint/src/...`. What a
# refactoring checks each change by: `--check 'make -s check-source
# SOURCE={}'`. Ten minutes at most, against a runaway elaboration.
check-source:
	@case "$(SOURCE)" in \
	  runtime/*) cd runtime && $(WITH_PREFIX) timeout 600 $(TARGET) --find-ipkg --check $(SOURCE:runtime/%=%) ;; \
	  tools/lint/*) cd tools/lint && $(WITH_PREFIX) timeout 600 $(UPSTREAM_IDRIS2) --find-ipkg --check $(SOURCE:tools/lint/%=%) ;; \
	  *) $(WITH_PREFIX) timeout 600 $(UPSTREAM_IDRIS2) --find-ipkg --check $(SOURCE) ;; \
	esac > /dev/null 2>&1

# The backend's phases against the size of the program: fails when one
# grows faster than the program (tests/scaling/scaling.sh). On demand, not
# part of `test`, since it measures time; `make scaling sizes="64 128"`
# chooses the sizes.
scaling: native
	cd tests/scaling && $(WITH_PREFIX) sh ./scaling.sh $(TARGET) $(sizes)

clean:
	$(RM) -r build runtime/build tools/lint/build tests/build tests/failures
	find tests -name build -type d -prune -exec $(RM) -r {} +
	find tests -name output -type f -delete
