ARG BASE
FROM $BASE
ADD GNUmakefile common.mk test-runner.sh ./
ADD agt agt
ADD fm fm
ADD bf bf
ADD hello hello
ENTRYPOINT ["make"]
