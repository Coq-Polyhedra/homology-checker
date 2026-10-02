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
template `src/CheckCert.v.in`. The benchmark driver of `lrs-postprocess`
automates both routes.

## License

CeCILL-B, see LICENSE.
