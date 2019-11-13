all:
	$(MAKE) -C agt
	$(MAKE) -C hello
	$(MAKE) -C fm
	$(MAKE) -C bf

DOCKER ?= docker
DOCKER_REPO ?= 676237474471.dkr.ecr.eu-central-1.amazonaws.com/agda-hack
DOCKER_TAG ?= latest
BASE_IMAGE_DIGEST_FILE = .base-image.digest
BASE_IMAGE_FILE = .base-image

docker: .docker-image
	$(DOCKER) run --rm $(shell cat $<)

.PHONY: .docker-image
.docker-image:
	$(DOCKER) build \
		--build-arg=BASE=$(shell cat $(BASE_IMAGE_FILE)) \
		--iidfile="$@" \
		.

build-base:
	$(DOCKER) build --file=base.dockerfile \
		--iidfile="$(BASE_IMAGE_DIGEST_FILE)" \
		--tag=$(DOCKER_REPO):$(DOCKER_TAG) .
	$(DOCKER) push $(DOCKER_REPO):$(DOCKER_TAG)
	$(DOCKER) inspect $(DOCKER_REPO):$(DOCKER_TAG) \
		| jq -r .[0].RepoDigests[] > $(BASE_IMAGE_FILE)

AWS ?= aws
AWS_PROFILE ?= ecr
AWS_CONFIG_FILE ?= .aws/config

ecr-login: $(AWS_CONFIG_FILE)
	env AWS_CONFIG_FILE=$(AWS_CONFIG_FILE) $(AWS) ecr get-login \
					--profile=$(AWS_PROFILE) | sed 's/-e none//' | sh -

.aws/config:
	mkdir -p "$(dir $@)"
	echo >  "$@" "[default]"
	echo >> "$@" "aws_access_key_id=$$AWS_ACCESS_KEY_ID"
	echo >> "$@" "aws_secret_access_key=$$AWS_SECRET_ACCESS_KEY"
	echo >> "$@" "[profile $(AWS_PROFILE)]"
	echo >> "$@" "source_profile = default"
ifneq ($(AWS_ROLE_ARN),)
	echo >> "$@" "role_arn = $(AWS_ROLE_ARN)"
endif

.PHONY: all docker push-base build-base
