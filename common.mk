AGDA ?= agda
ROOT := $(realpath $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
BUILD := $(shell pwd)/build

$(BUILD)/Main: src/Main.agda
	mkdir -p $(dir $(BUILD))
	$(AGDA) --compile --compile-dir=$(BUILD) $^

.PHONY: .clean
.clean:
	rm -rf $(BUILD)
