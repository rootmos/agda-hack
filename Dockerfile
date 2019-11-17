ARG BASE
FROM $BASE
ADD GNUmakefile common.mk test-runner.sh run.sh ./
ADD overture overture
RUN echo $(pwd)/overture/overture.agda-lib >> ~/.agda/libraries
ADD agt agt
ADD fm fm
ADD bf bf
ADD hello hello
ENV BUILD /tmp/build
ENTRYPOINT ["make"]
