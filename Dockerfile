ARG BASE
FROM $BASE
ADD GNUmakefile common.mk test-runner.sh run.sh ./
ADD overture overture
RUN echo "$(pwd)/overture/overture.agda-lib" >> "$HOME/.agda/libraries"
ADD agt agt
ADD bf bf
ENV BUILD /tmp/build
ENTRYPOINT ["make"]
