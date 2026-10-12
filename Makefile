# idris2-native: Idris 2, as the submodule `Idris2` pins it, with the native
# code generator.
#
#   make upstream   build the pinned Idris 2, its libraries and its API
#                   package into build/prefix, with the `idris2` in PATH
#                   bootstrapping it (once, and after moving the pin)
#   make            build idris2-native, install its modules as the package
#                   `idris2-native`, and build with it the runtime, the
#                   package `idris2-native-runtime`, into build/prefix
#   make test       run the tests; `only=native/term001` runs some
#   make lint       the product's code against the linter's rules
#                   (tools/lint), and its architectural health
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

.PHONY: all upstream native linter testbin test lint health scaling clean

all: native

upstream:
	$(MAKE) -C Idris2 PREFIX=$(PREFIX)
	$(MAKE) -C Idris2 install PREFIX=$(PREFIX)
	$(WITH_PREFIX) $(MAKE) -C Idris2 install-api PREFIX=$(PREFIX) IDRIS2_BOOT=$(UPSTREAM_IDRIS2)

# The runtime is built by idris2-native itself, so that its flat functions
# are checked as its modules are built.
native:
	$(WITH_PREFIX) $(UPSTREAM_IDRIS2) --install idris2-native.ipkg
	cd runtime && $(WITH_PREFIX) $(TARGET) --install idris2-native-runtime.ipkg

# The linter is an Idris program of its own, on the API of the pinned Idris.
LINTER := $(CURDIR)/tools/lint/build/exec/idris2-native-lint

linter:
	cd tools/lint && $(WITH_PREFIX) $(UPSTREAM_IDRIS2) --build idris2-native-lint.ipkg

testbin:
	cd tests && $(WITH_PREFIX) $(UPSTREAM_IDRIS2) --build tests.ipkg

test: native linter testbin
	cd tests && $(WITH_PREFIX) NAME_VERSION=$(NAME_VERSION) ./build/exec/runtests $(TARGET) \
	  --timing --failure-file failures --threads $(threads) --only "$(only)" < /dev/null

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
