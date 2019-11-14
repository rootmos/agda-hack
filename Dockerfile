ARG BASE
FROM $BASE
ADD GNUmakefile common.mk ./
ADD agt agt
ADD fm fm
ADD bf bf
ADD hello hello
ENTRYPOINT ["make"]
