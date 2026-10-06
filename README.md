# homology-checker

A verified checker, written in Rocq (Coq 8.20.1), for vertex enumeration
certificates. Given a polytope described by linear inequalities and a
certificate built from the output of the vertex enumeration library lrs,
the checker establishes that the certified points are exactly the vertices
of the polytope and that the certified graph is exactly its vertex-edge
graph. From a distance certificate, it also establishes the eccentricity
of a chosen vertex in that graph. The method and its proofs are described
in the companion paper, and the certificates are produced by the sibling
repository `lrs-postprocess`.

## Layout

- `src/HighLevelCertificate.v`, `src/CertificateCorrectness.v`,
  `src/CoveringCriterion.v`, `src/VertexCriterion.v`,
  `src/OddCoveringTheorem.v`: the proof-oriented side, with the conditions
  of the certification method and their correctness proofs down to the
  odd covering theorem.
- `src/LowLevelChecker.v`, `src/CertificateSchema.v`, `src/BigArray.v`:
  the computation-oriented checker over primitive integers, primitive and
  chunked persistent arrays, and arbitrary-precision rationals, together
  with the binary certificate format.
- `src/GraphDistance.v`: distance labellings of a graph and the
  eccentricity criterion.
- `src/Refinement.v`, `src/RefinementBridges.v`: the refinement proof
  relating the two sides.
- `src/ExtractChecker.v`, `ocaml/`: the extraction to OCaml and the
  runtime of the extracted checker.
- `benchmarks/`: the benchmark driver, the benchmark instances and the
  replay image.

## Build

The development builds with Coq 8.20.1 and the library versions pinned in
the artifact (a MathComp 1.x line ported to 8.20, Coq-Polyhedra, finmap,
bigenough, bignums and binreader).

- `make rocq` compiles the Rocq development, proofs included.
- `make extract` builds the extracted checker,
  `_build/default/ocaml/homology_checker.exe`.
- `make` does both.

## Running the checker

```
homology_checker.exe CERT.bin [DIST.bin]
```

checks the binary certificate `CERT.bin`, and, when the distance
certificate `DIST.bin` is given, prints the certified eccentricity of its
source vertex. The same checks run inside Rocq by `vm_compute` through the
template `src/CheckCert.v.in`. The benchmark driver `benchmarks/bench.py`
automates both routes (see Benchmarks).

## Benchmarks

The `benchmarks/` directory holds the benchmark driver `bench.py`, the
benchmark instances (`benchmarks/data/*.ine`, with the source vertices of
the distance certificates in `benchmarks/data/sources.json`), and a Docker
image that replays the whole pipeline at pinned revisions.

### Pipeline script

`benchmarks/bench.py` drives the whole pipeline, one stage per command:

```text
lrs     lrsgmp BASE.ine -> BASE.ext
cert    lrs-postprocess postprocess --bin -> BASE-cert.bin (the source vertex
        of the distance certificate is read from the sources file)
check   the extracted checker on BASE-cert.bin (and BASE-dist.bin if present)
rocq    the same check run by vm_compute inside Rocq
run     lrs, cert and check in sequence
report  tabulate the measurements of the selected instances (TSV)
clean   remove the generated files of an instance
```

It needs the `lrsgmp` binary of lrslib and the `lrs-postprocess` binary,
which it looks for by default in a checkout of `lrs-postprocess` next to
this repository (`../lrs-postprocess/target/release/lrs-postprocess`). The
data directory and the sources file default to `data` and
`data/sources.json` relative to the current directory, so the driver is run
from `benchmarks/` or given `--data-dir` and `--sources` explicitly.

Instances are selected by regular expressions matched against the complete
basename of the `.ine` files in the data directory, so `cross3` selects
exactly `cross3.ine` and `'cube(20|21)'` selects both cubes. A stage is
skipped when its output is newer than its inputs and than the tool producing
it. `--force` recomputes it. Outputs are staged in a `.tmp` file and moved
into place on success.

Every stage writes what it measured to `BASE-<stage>-timings.json`: the
wall-clock time and the peak memory of the process, measured in Python, plus
the wall-clock phase timings reported by the tool itself (certificate
construction and encoding for `cert`, loading and the three checks for
`check`, loading, decoding and the three checks for `rocq`, from Rocq's
`Time`). The tool's raw output is kept in `BASE-<stage>.log`. `report` builds
a tab-separated table from these records, one row per instance with blank
cells for stages that have not run, and writes it to standard output or to
`-o FILE`. Its columns are the lrs and certificate-generation wall times, the
three generation phases, and for each of the two checkers its loading time
(plus decoding for Rocq), the cumulative check times T1-T5 (vertex
containment), T1-T6 (plus vertex equality) and T1-T7 (plus graph equality),
the verdict, and, for the instances with a distance certificate, the
certified eccentricity of its source vertex with its time (`ecc`, `ecc_s`).
With `--relative` every time but the lrs one is divided by the instance's
lrs time. The `rocq` stage instantiates `src/CheckCert.v.in` with the
certificate path and runs it through `coqtop -batch`. Each Rocq check
decodes the certificate itself, so the decoding time is included in each of
the three check times and is also reported on its own.

```bash
cd benchmarks
./bench.py run cross3
./bench.py --force lrs 'cross(8|9|10)'
./bench.py cert 'dual_cyclic_d1[5-8]_n.*'
./bench.py check cube20
./bench.py rocq cube15
./bench.py report -o results.tsv
./bench.py report --relative 'cube.*'
./bench.py clean cross3
```

Options:

```text
--data-dir DIR   directory of the .ine inputs and generated files (default: data)
--lrsgmp CMD     lrs vertex enumerator (default: lrsgmp, from the PATH)
--bin CMD        lrs-postprocess binary (default:
                 ../lrs-postprocess/target/release/lrs-postprocess, relative
                 to the root of this repository)
--checker CMD    extracted checker (default: homology_checker.exe, from the PATH)
--rocq-dir DIR   checker development with src/CheckCert.v.in and its compiled
                 modules (default: the root of this repository)
--coqtop CMD     Rocq toplevel (default: coqtop, from the PATH)
--rocq-timeout S kill a Rocq check after S seconds (default: 3600)
--sources FILE   JSON object mapping instances to the source vertex of their
                 distance certificate, a position in the coordinate order of
                 the vertices (default: data/sources.json, others use 0)
-o FILE          report: write the table to FILE instead of standard output
--force          recompute stages whose output is fresh
```

### Replaying the benchmarks

`benchmarks/Dockerfile` builds an image with this checker, the certificate
generator `lrs-postprocess`, the patched `lrs`, and the Coq libraries the
checker depends on, all at pinned revisions. The checker and the benchmark
driver come from the build context, the root of this repository. A
successful build is also the proof check: it compiles the whole Rocq
development, proofs included. The build takes about an hour and needs at
least 6 GB of memory for the Docker engine. On macOS and Windows, the engine
runs in a virtual machine whose default memory is often too small, and the
opam stage then fails silently.

```bash
docker build -f benchmarks/Dockerfile -t replay .
mkdir results
docker run --rm -v "$PWD/results:/results" replay quick
```

The container writes everything it produces under `/results`, and its own
files are discarded when it exits. Mounting a host directory there keeps the
results, and reusing the same directory lets a later run skip the
enumerations and certificates already present.

| replay     | engine memory | disk  | duration           |
|------------|---------------|-------|--------------------|
| `quick`    | 2 GB          | 1 GB  | about half an hour |
| `standard` | 8 GB          | 10 GB | two to three hours |
| `full`     | 24 GB         | 60 GB | several hours      |

`quick` covers the small instances of every family, including the two
counterexamples to the Hirsch conjecture (poly20dim21 and poly23dim24). For
each instance, it runs the lrs enumeration, generates the certificate, and
checks it with the extracted checker and with `vm_compute` inside Rocq. On
the two counterexamples, the checker also returns the certified eccentricity
of the start vertex, 21 and 24. The other commands take the same `-v`
argument:

- `standard`: `quick` plus every instance whose enumeration takes up to
  about 100 s, with the Rocq check on the `quick` instances only.
- `full`: all the instances of the paper's tables, with the extracted
  checker only.
- `rocq PATTERN...`: the Rocq check on the matching instances, for instance
  `rocq 'cube(15|16)'`.
- `proofs`: print the assumptions of the two main theorems.
- `report`: regenerate the result tables from the records in `/results`.

`results/bench-results.tsv` and `results/bench-results-relative.tsv` are the
two `report` tables described above, the first in seconds and the second in
multiples of the lrs time. The per-stage records and logs are under
`results/data`.

Each cumulative time is a self-contained evaluation that redoes the
certificate decoding and the earlier checks, so the Rocq runs take longer
than the single evaluation reported in the paper. Absolute times depend on
the machine. The claims of the paper are about the ratios to lrs, measured
on the same machine in the same run.

## License

CeCILL-B, see LICENSE.
