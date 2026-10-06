# Replay image: this verified certificate checker, the certificate generator
# lrs-postprocess, lrs, and the benchmark driver. The checker and the driver
# come from the build context, the root of this repository. Every other
# source is fetched from GitHub at a pinned commit.
#
#   docker build -f benchmarks/Dockerfile -t replay .
#   docker run --rm -v "$PWD/results:/results" replay quick
#
# Build stages, in order of cost: the opam switch with Coq and the pinned
# libraries (the slow part, cached across source changes), then lrs and the
# Rust generator, then the Rocq development itself, whose successful
# compilation is the proof check.

FROM debian:bookworm-slim@sha256:88200866dfff7ea7f5cbcb6ec7c8a701889efe6fe859fe64d6990e4b07ea4171

# Pinned revisions of the sources fetched from GitHub.
ARG BIGNUMS_COMMIT=1c479360ebe65e9e005446768227642391dfb758
ARG BINREADER_COMMIT=9d36972d7c5032d41189f0c80f8c0da25e748ac2
ARG MATHCOMP_COMMIT=b4206e1459adb7f219d595f02b5bb23be3a11951
ARG FINMAP_COMMIT=aee2739d7fdd6179865dc21c18f7f23ca6cec4e9
ARG BIGENOUGH_COMMIT=596834243018593f1855201d2ff7228d09f1afde
ARG POLYHEDRA_COMMIT=3c0ecbf5828ad646014079fa67e8c5dc080af181
ARG LRSLIB_COMMIT=497d40179d635f43ec9e9701d85dad564ac7598e
ARG LRS_POSTPROCESS_COMMIT=c483277026687a0cf890a96e76e93ce34efccbc0

RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential m4 pkg-config libgmp-dev diffutils patch \
        curl ca-certificates git rsync unzip bubblewrap \
        python3 opam \
    && rm -rf /var/lib/apt/lists/*

ENV OPAMROOT=/opt/opam OPAMYES=1 OPAMCOLOR=never
RUN opam init --disable-sandboxing --bare --no-setup \
    && opam switch create bench ocaml-base-compiler.4.14.4 \
    && opam repository add coq-released https://coq.inria.fr/opam/released \
    && opam repository add rocq-released https://rocq-prover.org/opam/released
ENV PATH=/opt/opam/bench/bin:$PATH \
    OPAM_SWITCH_PREFIX=/opt/opam/bench \
    CAML_LD_LIBRARY_PATH=/opt/opam/bench/lib/stublibs \
    OCAMLPATH=/opt/opam/bench/lib

# Public packages at the versions of the reference runs, then the Coq
# libraries pinned to their GitHub repositories at fixed commits.
RUN opam install coq.8.20.1 dune.3.23.1 zarith.1.14 elpi.3.4.2 coq-elpi.3.2.0 \
        rocq-hierarchy-builder.1.10.1 \
    && opam pin add -y -n coq-bignums https://github.com/rocq-community/bignums.git#${BIGNUMS_COMMIT} \
    && opam pin add -y -n coq-binreader https://github.com/Coq-Polyhedra/coq-binreader.git#${BINREADER_COMMIT} \
    && opam pin add -y -n coq-mathcomp-ssreflect https://github.com/Coq-Polyhedra/mathcomp.git#${MATHCOMP_COMMIT} \
    && opam pin add -y -n coq-mathcomp-fingroup https://github.com/Coq-Polyhedra/mathcomp.git#${MATHCOMP_COMMIT} \
    && opam pin add -y -n coq-mathcomp-algebra https://github.com/Coq-Polyhedra/mathcomp.git#${MATHCOMP_COMMIT} \
    && opam pin add -y -n coq-mathcomp-finmap https://github.com/Coq-Polyhedra/finmap.git#${FINMAP_COMMIT} \
    && opam pin add -y -n coq-mathcomp-bigenough https://github.com/math-comp/bigenough.git#${BIGENOUGH_COMMIT} \
    && opam pin add -y -n coq-polyhedra https://github.com/Coq-Polyhedra/Coq-Polyhedra.git#${POLYHEDRA_COMMIT} \
    && opam install coq-bignums coq-binreader coq-mathcomp-ssreflect coq-mathcomp-fingroup \
        coq-mathcomp-algebra coq-mathcomp-finmap coq-mathcomp-bigenough coq-polyhedra \
    && opam clean -a -c

# Rust, pinned. Cargo fetches the generator's crates at the versions of
# Cargo.lock.
RUN curl -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal --default-toolchain 1.89.0
ENV PATH=/root/.cargo/bin:$PATH

# lrs (patched: commondenom option) and the certificate generator.
RUN git clone https://github.com/Coq-Polyhedra/lrslib.git /work/lrslib \
    && git -C /work/lrslib checkout --detach ${LRSLIB_COMMIT} \
    && make -C /work/lrslib lrsgmp
RUN git clone https://github.com/Coq-Polyhedra/lrs-postprocess.git /work/lrs-postprocess \
    && git -C /work/lrs-postprocess checkout --detach ${LRS_POSTPROCESS_COMMIT} \
    && cd /work/lrs-postprocess && cargo build --release

# The verified checker: Rocq proofs (this is the proof check), extraction,
# and the OCaml runtime. The benchmark driver and instances come with it.
COPY . /work/homology-checker
RUN cd /work/homology-checker && make

WORKDIR /work/homology-checker/benchmarks
ENTRYPOINT ["/work/homology-checker/benchmarks/replay"]
CMD ["quick"]
