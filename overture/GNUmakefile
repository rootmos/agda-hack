include ../common.mk

all: check test

$(eval $(call check, check, src/Overture.agda))

test:
	@$(TEST_RUNNER) -e "$(RUN)"

.PHONY: clean
clean: .clean

.PHONY: all tests
