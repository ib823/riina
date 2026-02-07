# RIINA Compiler — Production Dockerfile
# Multi-stage build: builder → minimal runtime (~50MB)
# Verification gate: riinac verify [--fast|--full]

# Stage 1: Build
FROM rust:1.84-bookworm AS builder

WORKDIR /build

# Copy only what's needed for compilation
COPY 03_PROTO/ 03_PROTO/

WORKDIR /build/03_PROTO

# Build release binary
RUN cargo build --release && \
    cp target/release/riinac /riinac

# Stage 2: Minimal runtime
FROM debian:bookworm-slim

RUN apt-get update && \
    apt-get install -y --no-install-recommends ca-certificates && \
    rm -rf /var/lib/apt/lists/*

COPY --from=builder /riinac /usr/local/bin/riinac

LABEL maintainer="RIINA Team <security@riina.my>"
LABEL version="0.2.0"
LABEL description="RIINA compiler — formally verified, zero-trust"
LABEL license="Proprietary"

ENTRYPOINT ["riinac"]
