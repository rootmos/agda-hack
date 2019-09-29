ROOT := $(realpath $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
STACK ?= stack

setup: $(HOME)/.agda
	$(STACK) install Agda-2.6.0.1 ieee754

$(HOME)/.agda: $(ROOT)/.agda
	ln -s "$<" "$@"

$(ROOT)/.agda:
	mkdir "$@"
	echo "$(ROOT)/agda-stdlib/standard-library.agda-lib" > "$@/libraries"

.PHONY: setup