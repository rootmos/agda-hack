include ../common.mk

test: $(BUILD)/bf
	@"$(TEST_RUNNER)" -e "$<"

$(eval $(call exe, bf, src/bf.agda))

.PHONY: clean
clean: .clean

.PHONY: test
