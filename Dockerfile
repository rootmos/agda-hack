ARG BASE
FROM $BASE
ADD GNUmakefile common.mk ./
ADD agt agt
ADD fm fm
ADD hello hello
ENTRYPOINT ["make"]
