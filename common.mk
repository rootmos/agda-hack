AGDA ?= agda
ROOT := $(realpath $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
BUILD := $(shell pwd)/build

$(BUILD)/%: src/%.agda
	$(AGDA) --compile --compile-dir=$(BUILD) $^

.PHONY: .clean
.clean:
	rm -rf $(BUILD)
