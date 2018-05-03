# Fstar build container
FROM everest_base_image:1

ARG BUILDLOGFILE
ARG MAXTHREADS

#BUILD FSTAR
RUN mkdir ${MYHOME}/FStar
COPY --chown=everest / ${MYHOME}/FStar/
RUN rm -rf  ${MYHOME}/FStar/.git
WORKDIR ${MYHOME}/FStar
RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}

# For anything printed on stdout or stderr, gather everything and
# get everything printed to both the log file and stderr
RUN { make -C src -j ${MAXTHREADS} utest-prelude && echo "success" > "result.txt" || echo "failed" > "result.txt" ; } 2>&1 | tee --append ${BUILDLOGFILE} >&2

RUN echo $(date -u '+%Y-%m-%d %H:%M:%S') >> ${BUILDLOGFILE}


