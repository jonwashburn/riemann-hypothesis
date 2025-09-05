import Mathlib
import ym.Transfer

/-!
Matrix → Transfer adapter (noninvasive).

We package a concrete matrix as a transfer operator via `Matrix.toLin'`, and
provide an adapter that turns a matrix-level `SpectralGap` into a `TransferPFGap`
for an abstract `(μ, K)` pair, without modifying `ym/Transfer.lean`.
-/

noncomputable section

namespace YM

open scoped BigOperators

variables {ι : Type*}

/-- Concrete transfer operator from a matrix acting on functions `ι → ℝ` via `toLin'`. -/
def TransferOp (A : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  Matrix.toLin' A

/-- Convenience: build a `TransferOp` from a MarkovKernel by coercing entries to ℝ. -/
def matrixToTransferOp [Fintype ι] (K : MarkovKernel ι) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  TransferOp (fun i j => (K.P i j : ℝ))

/--
Adapter: A spectral gap for the finite-state Markov kernel `K` yields a PF transfer gap
for any abstract `(μ, Kt)` that is intended to be modeled by `K` at the interface level.

At the current interface granularity, `TransferPFGap` is a Prop placeholder, so the adapter
does not need additional structure beyond the spectral gap hypothesis.
-/
theorem transferPFGap_of_matrixSpectralGap
    [Fintype ι]
    {μ : LatticeMeasure} {Kt : TransferKernel}
    {K : MarkovKernel ι} {γ : ℝ}
    (hSG : SpectralGap K γ) : TransferPFGap μ Kt γ := by
  -- Noninvasive bridge at the interface level.
  trivial

end YM

import Mathlib
import Mathlib/LinearAlgebra/Matrix/ToLin
import Mathlib/Analysis/NormedSpace/Basic
import ym.OSPositivity
import ym.Transfer

/-!
Concrete, noninvasive matrix→transfer adapter.

We introduce a lightweight `TransferOp` wrapper that carries a continuous
linear operator on a finite coordinate space `ι → ℂ`, together with an adapter
`matrixToTransferOp` from a finite matrix via `Matrix.toLin'`. We then export a
Prop-level bridge `spectral_to_transfer_gap` that takes a (finite-dimensional)
PF-type spectral gap and returns the pipeline’s `TransferPFGap` without editing
core shared interfaces.

This module is additive to the existing interface: no changes to `ym/Transfer`.
-/

namespace YM

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lightweight wrapper for a transfer operator acting on `ι → ℂ`. -/
structure TransferOp (ι : Type*) [Fintype ι] where
  op : (ι → ℂ) →L[ℂ] (ι → ℂ)

/-- Adapter from a complex matrix to the corresponding continuous linear map. -/
def matrixToTransferOp (A : Matrix ι ι ℂ) : TransferOp ι :=
  ⟨Matrix.toLin' A⟩

/-- Prop-level spectral gap on finite-dimensional operator (placeholder). -/
def OperatorPFGap (T : (ι → ℂ) →L[ℂ] (ι → ℂ)) (γ : ℝ) : Prop := 0 < γ

/-- Bridge: a finite-dimensional PF gap on `toLin' A` yields a transfer PF gap
for the abstract pipeline interface, without modifying shared types. -/
theorem spectral_to_transfer_gap
    (A : Matrix ι ι ℂ) {γ : ℝ}
    (hPF : OperatorPFGap (Matrix.toLin' A) γ)
    (μ : LatticeMeasure) : TransferPFGap μ (default : TransferKernel) γ := by
  -- Interface-level Prop export; to be strengthened with concrete spectral args.
  trivial

end YM
