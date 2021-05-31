Slashing Proofs
===============

This is a formalisation of two minification algorithms for
Ethereum slashing protection data as defined in [EIP-3076][].

The main results are `minify_synth_correct` and `minify_max_correct`,
which state that if a new attestation is safe to sign with respect
to the minification, then it is not slashable with respect to the
attestations that were minified.

Interestingly, the preconditions for `minify_max` are stronger than
those for `minify_synth`: `minify_max` requires that the attestations
being minified are not mutually slashable with respect to each other. Checking
this property can be quite computationally expensive (naïvely O(n²)), so
`minify_synth` is recommended to implementers.

## Proof Guide

These proofs have been checked with [Isabelle 2021][isabelle].

* `MinMaxByKey.thy`: this helper theory contains implementations of `argmin` & `argmax`
   operating on lists. I got frustrated trying to prove things about Isabelle's non-computational
   `argmax` (which uses the axiom of choice), and wanted something I could have the option of
   executing. The name is inspired by Rust's [`max_by_key`][max_by_key].
* `SlashingProofs.thy`: this is the main theory; with definitions of attestations,
  slashing conditions, etc, and proofs about the two minification algorithms.

## Future Plans

* Verify a faster-than-quadratic algorithm for proving that a list of attestations
  are not mutually slashable. It could be based on the min-max algorithm used by
  slashers, or could be a simpler property that is sufficient to imply
  non-slashability, but not necessary.
* Extract an executable implementation of the minification algorithms to Haskell, and
  wrap it in some JSON parsing code to build a tool for manipulating EIP-3076 files.

[EIP-3076]: https://eips.ethereum.org/EIPS/eip-3076
[isabelle]: https://isabelle.in.tum.de/
[max_by_key]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.max_by_key
