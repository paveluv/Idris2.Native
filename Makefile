# idris2-native: Idris 2, as the submodule `Idris2` pins it, with the native
# code generator.
#
#   make upstream   build the pinned Idris 2, its libraries and its API
#                   package into build/prefix, with the `idris2` in PATH
#                   bootstrapping it (once, and after moving the pin)
#   make            build idris2-native, and install its modules as the
#                   package `idris2-native` into build/prefix
#   make test       run the tests; `only=native/term001` runs some
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

.PHONY: all upstream native testbin test clean

all: native

upstream:
	$(MAKE) -C Idris2 PREFIX=$(PREFIX)
	$(MAKE) -C Idris2 install PREFIX=$(PREFIX)
	$(WITH_PREFIX) $(MAKE) -C Idris2 install-api PREFIX=$(PREFIX) IDRIS2_BOOT=$(UPSTREAM_IDRIS2)

native:
	$(WITH_PREFIX) $(UPSTREAM_IDRIS2) --install idris2-native.ipkg

testbin:
	cd tests && $(WITH_PREFIX) $(UPSTREAM_IDRIS2) --build tests.ipkg

test: native testbin
	cd tests && $(WITH_PREFIX) NAME_VERSION=$(NAME_VERSION) ./build/exec/runtests $(TARGET) \
	  --timing --failure-file failures --threads $(threads) --only "$(only)" < /dev/null

clean:
	$(RM) -r build tests/build tests/failures
	find tests -name build -type d -prune -exec $(RM) -r {} +
	find tests -name output -type f -delete
