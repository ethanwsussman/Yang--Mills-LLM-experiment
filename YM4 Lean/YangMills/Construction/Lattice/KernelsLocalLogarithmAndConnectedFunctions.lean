import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.Lattice.PlaquetteWeightsAndTheLatticeIntegral
import YangMills.Construction.Lattice.SourcedPartitionFunctionOfALattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace SeveralComplexVariables
def iteratedPartialDeriv {n : ℕ} (h : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  (List.finRange n).foldr (fun i g => partialDeriv i g) h
end SeveralComplexVariables
namespace PeriodicLattice
open YangMills.Construction.SeveralComplexVariables
variable {L m J : ℕ}
def logDerivativeKernel : (n : ℕ) → (Fin (n + 1) → Plaquette L m (J : ℤ)) →
    (Plaquette L m (J : ℤ) → ℂ) → ℂ
  | 0, p, c => -partialDeriv (p 0) latticeGaugeIntegral c / latticeGaugeIntegral c
  | n + 1, p, c =>
    -partialDeriv (p (Fin.last (n + 1))) (logDerivativeKernel n (Fin.init p)) c
def IsAdmissibleRadius (c₀ : Plaquette L m (J : ℤ) → ℂ) (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ c ∈ polydisc c₀ δ, latticeGaugeIntegral c / latticeGaugeIntegral c₀ ∈ disc 1 1
def localLog (c₀ c : Plaquette L m (J : ℤ) → ℂ) : ℂ :=
  logSeries (latticeGaugeIntegral c / latticeGaugeIntegral c₀)
def observableOnFields (f : FourTorus L m → ℝ) (U : CompactGaugeField L m (J : ℤ)) : ℝ :=
  smearedObservable f U.1
def weightedSource {n : ℕ} (f : Fin n → FourTorus L m → ℝ) (z : Fin n → ℂ) :
    FourTorus L m → ℂ :=
  fun y => ∑ i, z i * (f i y : ℂ)
def connectedFunction (L m J : ℕ) (β : ℂ) {n : ℕ} (f : Fin n → FourTorus L m → ℝ) : ℂ :=
  iteratedPartialDeriv
    (fun z => logSeries (sourcedPartitionFunction L m J β (weightedSource f z) /
      sourcedPartitionFunction L m J β 0)) 0
def observableCumulant (L m J : ℕ) (β : ℂ) {n : ℕ} (f : Fin n → FourTorus L m → ℝ) : ℂ :=
  open Classical in
  if 1 ≤ J ∧ 0 < β.re ∧ β.im = 0 then
    gibbsCumulant L m J β.re fun i => smearedObservable (j := (J : ℤ)) (f i)
  else connectedFunction L m J β f
end PeriodicLattice
end YangMills.Construction
