# Fstar build container
FROM everest_base_image:1

ARG BUILDLOGFILE="buildlogfile.txt"
ARG MAXTHREADS=8

#BUILD FSTAR
RUN mkdir ${MYHOME}/FStar
COPY --chown=everest / ${MYHOME}/FStar/
RUN rm -rf  ${MYHOME}/FStar/.git
WORKDIR ${MYHOME}/FStar
RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}

RUN make -C src -j ${MAXTHREADS} utest-prelude >> ${BUILDLOGFILE} && echo "success" > "result.txt" || echo "failed" > "result.txt"

RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}
