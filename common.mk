AGDA ?= agda
ROOT := $(realpath $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
BUILD := $(shell pwd)/build

TEST_RUNNER := $(ROOT)/test-runner.sh

.PHONY: .clean
.clean:
	rm -rf $(BUILD)

define exe
.PHONY: $$(BUILD)/$(strip $(1))
$$(BUILD)/$(strip $(1)):
	@mkdir -p $$(dir $$(BUILD))
	$$(AGDA) --compile --compile-dir=$$(BUILD) $(2)

.PHONY: run
run: $$(BUILD)/$(strip $(1))
ifeq ($$(wildcard .args),)
	$$(BUILD)/$(strip $(1))
else
	$$(BUILD)/$(strip $(1)) $$(shell cat .args)
endif
endef

define check
.PHONY: $(strip $(1))
$(strip $(1)):
	@mkdir -p $$(dir $$(BUILD))
	$$(AGDA) --compile --compile-dir=$$(BUILD) --no-main $(2)
endef
