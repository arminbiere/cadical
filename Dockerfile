# -----------------------------------------------------------------------------
# Builder container
# -----------------------------------------------------------------------------
FROM ubuntu:22.04 as builder

ENV DEBIAN_FRONTEND "noninteractive"
ENV TZ "Europe/Berlin"

# Install compiler, build tools and required libraries
RUN apt-get update \
  && apt-get install -y --no-install-recommends build-essential g++ \
  && apt-get clean

COPY . /work

WORKDIR /work
RUN ./configure \
  && make

# -----------------------------------------------------------------------------
# Runtime container
# -----------------------------------------------------------------------------

FROM ubuntu:22.04 as runner

ENV DEBIAN_FRONTEND "noninteractive"
ENV TZ "Europe/Berlin"

COPY --from=builder /work/build/cadical /cadical/cadical
COPY --from=builder /work/build/mobical /cadical/mobical

WORKDIR /cadical
ENTRYPOINT ["/cadical/cadical"]
CMD ["--help"]
