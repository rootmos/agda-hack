FROM haskell:8.6.5

WORKDIR /agda-hack
ADD Makefile stack.yaml stack.yaml.lock ./
RUN make setup
