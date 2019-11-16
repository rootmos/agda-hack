ARG HASKELL_VERSION=8.6.5
FROM haskell:$HASKELL_VERSION

ARG AGDA_VERSION=2.6.0.1
ARG AGDA_STDLIB_VERSION=v1.2

RUN cabal update \
    && cabal install alex happy \
    && cabal install Agda-$AGDA_VERSION

RUN git clone --depth=1 --branch=${AGDA_STDLIB_VERSION} https://github.com/agda/agda-stdlib /agda-stdlib
RUN mkdir -p ~/.agda && echo /agda-stdlib/standard-library.agda-lib > ~/.agda/libraries

WORKDIR /agda-hack
