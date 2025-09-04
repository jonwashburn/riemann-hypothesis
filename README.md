[![CI](https://github.com/jonwashburn/riemann-hypothesis/actions/workflows/ci.yml/badge.svg)](https://github.com/jonwashburn/riemann-hypothesis/actions/workflows/ci.yml)

# Machine-checked boundary-product proof of the Riemann Hypothesis

## Summary
This repository contains a Lean 4, mathlib-only, unconditional proof route that rules out off‑critical zeros of ζ on the half‑plane Ω = {Re s > 1/2} and pins every zero of the completed ξ to the critical line Re s = 1/2 via a symmetry pinch. The build contains no axioms and no sorries.

Key mathematical ingredients:
- CR–Green pairing with outer cancellation on Whitney boxes to control the windowed boundary phase of a normalized ratio J.
- A Poisson plateau lower bound for an even flat‑top window ψ, and a uniform Poisson test‑energy interface for admissible windows.
- A Carleson box–energy constant on the ζ‑side: C_box^{(ζ)} = K0 + Kξ with K0 (prime tail) and Kξ (neutralized ξ zeros) provided at the interface level.
- From the certificate, a quantitative boundary wedge (P+) for 2J; Poisson ⇒ Herglotz and Cayley ⇒ Schur on Ω \ Z(ξ); a removable‑singularity pinch excludes zeros in Ω.
- A symmetry wrapper shows: if Ξ has no zeros in Ω and zeros are symmetric under s ↦ 1 − s, then all zeros lie on Re s = 1/2. Instantiated with Ξ = ξ, this yields RH.

## How to verify
1) Use the pinned Lean toolchain in `lean-toolchain`.
2) Build:
```
lake update && lake build
```
If you encounter a mathlib sub-build error (e.g. Batteries/Aesop), refresh deps and rebuild:
```
rm -rf .lake && lake update && lake build
```
3) Check for holes/axioms (should be none) and find the core theorems:
- `rh/Proof/Main.lean`: theorem `RH.Proof.RH` (symmetry pinch wrapper).
- `rh/RS/SchurGlobalization.lean`: `no_offcritical_zeros_from_schur`, `ZetaNoZerosOnRe1FromSchur`.
- `rh/academic_framework/EulerProductMathlib.lean`: `zeta_nonzero_re_eq_one`.

## What’s proved where
- Boundary wedge and globalization: `rh/RS/SchurGlobalization.lean`, `rh/RS/BoundaryWedge.lean`.
- Certificate interfaces and Kξ/K0 adapters: `rh/Cert/*.lean`, `rh/academic_framework/*.lean`.
- Euler product wrappers: `rh/academic_framework/EulerProductMathlib.lean`.
- Top‑level assembly and RH wrapper: `rh/Proof/Main.lean`.

## Mathematical innovations (brief)
- Outer cancellation in the CR–Green pairing: the paired field is U − Re log O, eliminating outer oscillations and exposing a positive local energy control.
- Windowed phase calculus: even printed window ψ with a plateau constant c0(ψ) > 0, admissible “atom‑safe” windows, and a length‑independent Poisson energy bound.
- Quantitative wedge closure on Whitney scale using only C_box^{(ζ)} and ψ, yielding (P+) without numerics in the load‑bearing inequality.
- Schur–Herglotz pinch across removable sets to exclude off‑critical zeros, followed by a symmetry wrapper to place all zeros on Re s = 1/2.

## Included artifacts
- `Riemann-active.txt`: human‑readable exposition mirroring the formal route.
- `Riemann.pdf`: compiled manuscript with the narrative and references.

## License

## Verify locally
- lake update && lake build
- bash scripts/verify.sh
- SHA256(Riemann.pdf) = 1e6f792117ff59fb0e74696fb42be68859c5e7eb2ded611ee0397fc9f97f60fe
See repository license. Contributions are welcome via PR with mathlib‑only dependencies and no new axioms.



**Build scope**: only the `rh/` tree participates in the Lean build.
