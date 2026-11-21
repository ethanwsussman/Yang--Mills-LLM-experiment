import YangMills.Construction.Lattice.KernelsLocalLogarithmAndConnectedFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace SeveralComplexVariables
def iteratedPartialDerivAlong {I : Type*} {k : ℕ} (v : Fin k → I) (F : (I → ℂ) → ℂ) :
    (I → ℂ) → ℂ :=
  (List.ofFn v).foldr (fun j G => partialDeriv j G) F
end SeveralComplexVariables
namespace PeriodicLattice
def normalizedActionMeasure (L m J : ℕ) (β : ℝ) : Measure (CompactGaugeField L m (J : ℤ)) :=
  (ENNReal.ofReal (sourcedPartitionFunction L m J β 0).re)⁻¹ •
    (gaugeFieldMeasure L m (J : ℤ)).withDensity fun U =>
      ENNReal.ofReal (Complex.exp (-barycenterWeightedEnergy (fun _ => (β : ℂ)) U.1)).re
end PeriodicLattice
namespace ConnectedFunctionExpansion
open SeveralComplexVariables PeriodicLattice
def IsBoundedOnTorus {L m : ℕ} (f : FourTorus L m → ℝ) : Prop := torusSupNorm f ≠ ⊤
def LogarithmBranchIndependence (L m J : ℕ) : Prop :=
  (∀ (W : Set (Plaquette L m (J : ℤ) → ℂ)) (F : (Plaquette L m (J : ℤ) → ℂ) → ℂ),
    IsOpen W → ContinuousOn F W → (∀ c ∈ W, Complex.exp (F c) = latticeGaugeIntegral c) →
      W ⊆ partitionFunctionNonvanishing L m (J : ℤ) ∧ IsHolomorphicOnOpen W F ∧
        ∀ (n : ℕ) (p : Fin (n + 1) → Plaquette L m (J : ℤ)), ∀ c ∈ W,
          (-1 : ℂ) ^ (n + 1) * iteratedPartialDerivAlong p F c = logDerivativeKernel n p c) ∧
  ∀ (c₀ : Plaquette L m (J : ℤ) → ℂ) (δ : ℝ), c₀ ∈ partitionFunctionNonvanishing L m (J : ℤ) →
    IsAdmissibleRadius c₀ δ →
      polydisc c₀ δ ⊆ partitionFunctionNonvanishing L m (J : ℤ) ∧
        IsHolomorphicOnOpen (polydisc c₀ δ) (localLog c₀) ∧
        ∀ (n : ℕ) (p : Fin (n + 1) → Plaquette L m (J : ℤ)), ∀ c ∈ polydisc c₀ δ,
          (-1 : ℂ) ^ (n + 1) * iteratedPartialDerivAlong p (localLog c₀) c =
            logDerivativeKernel n p c
def KernelRegularity (L m J : ℕ) : Prop :=
  ∀ (n : ℕ) (p : Fin (n + 1) → Plaquette L m (J : ℤ)),
    IsHolomorphicOnOpen (partitionFunctionNonvanishing L m (J : ℤ)) (logDerivativeKernel n p) ∧
      (∀ (σ : Equiv.Perm (Fin (n + 1))), ∀ c ∈ partitionFunctionNonvanishing L m (J : ℤ),
        logDerivativeKernel n (p ∘ σ) c = logDerivativeKernel n p c) ∧
      ∀ x : Plaquette L m (J : ℤ) → ℝ, (logDerivativeKernel n p fun q => (x q : ℂ)).im = 0
def IsContinuousLogOfSourced (L m J : ℕ) (β : ℂ) {n : ℕ} (f : Fin n → FourTorus L m → ℝ)
    (N : Set (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ) : Prop :=
  IsOpen N ∧ (0 : Fin n → ℂ) ∈ N ∧ ContinuousOn F N ∧
    ∀ z ∈ N, Complex.exp (F z) = sourcedPartitionFunction L m J β (weightedSource f z)
def kernelPlaquetteSum (L m J : ℕ) (β : ℂ) {n : ℕ} (f : Fin (n + 1) → FourTorus L m → ℝ) : ℂ :=
  ∑ᶠ p : Fin (n + 1) → Plaquette L m (J : ℤ),
    logDerivativeKernel n p (β • constantOneWeights) * ∏ i, (f i (p i).barycenter : ℂ)
def ConnectedFunctionEqKernelSum (L m J : ℕ) : Prop :=
  ∀ (n : ℕ) (β : ℂ) (f : Fin (n + 1) → FourTorus L m → ℝ), β ∈ nonvanishingCouplings L m J →
    (∀ i, IsBoundedOnTorus (f i)) →
      (∀ (N : Set (Fin (n + 1) → ℂ)) (F : (Fin (n + 1) → ℂ) → ℂ),
        IsContinuousLogOfSourced L m J β f N F →
          (∃ N' ⊆ N, (0 : Fin (n + 1) → ℂ) ∈ N' ∧ IsHolomorphicOnOpen N' F) ∧
            iteratedPartialDeriv F 0 = connectedFunction L m J β f ∧
            connectedFunction L m J β f = kernelPlaquetteSum L m J β f) ∧
      (∃ (N : Set (Fin (n + 1) → ℂ)) (F : (Fin (n + 1) → ℂ) → ℂ),
        IsContinuousLogOfSourced L m J β f N F) ∧
      connectedFunction L m J β f = kernelPlaquetteSum L m J β f
def ConnectedFunctionAnalyticMultilinear (L m J : ℕ) : Prop :=
  ∀ n : ℕ,
    (∀ f : Fin (n + 1) → FourTorus L m → ℝ, (∀ i, IsBoundedOnTorus (f i)) →
      DifferentiableOn ℂ (fun β => connectedFunction L m J β f)
          (nonvanishingCouplings L m J) ∧
        ∀ b : ℝ, (connectedFunction L m J (b : ℂ) f).im = 0) ∧
    ∀ β ∈ nonvanishingCouplings L m J,
      (∀ (f : Fin (n + 1) → FourTorus L m → ℝ) (i : Fin (n + 1)) (g g' : FourTorus L m → ℝ)
          (a a' : ℝ),
        (∀ k, IsBoundedOnTorus (f k)) → IsBoundedOnTorus g → IsBoundedOnTorus g' →
          connectedFunction L m J β (Function.update f i (a • g + a' • g')) =
            (a : ℂ) * connectedFunction L m J β (Function.update f i g) +
              (a' : ℂ) * connectedFunction L m J β (Function.update f i g')) ∧
      ∀ (f : Fin (n + 1) → FourTorus L m → ℝ) (σ : Equiv.Perm (Fin (n + 1))),
        (∀ k, IsBoundedOnTorus (f k)) →
          connectedFunction L m J β (f ∘ σ) = connectedFunction L m J β f
def ConnectedFunctionEqCumulant (L m J : ℕ) : Prop :=
  (∀ b : ℝ,
    0 < (sourcedPartitionFunction L m J b 0).re ∧
      (sourcedPartitionFunction L m J b 0).im = 0 ∧
      IsProbabilityMeasure (normalizedActionMeasure L m J b) ∧
      (∀ (n : ℕ) (f : Fin (n + 1) → FourTorus L m → ℝ), (∀ i, IsBoundedOnTorus (f i)) →
        (∀ i, Measurable (observableOnFields (J := J) (f i)) ∧
          ∃ C : ℝ, ∀ U, |observableOnFields (J := J) (f i) U| ≤ C) ∧
        connectedFunction L m J b f =
          Cumulants.mixedCumulant (normalizedActionMeasure L m J b)
            fun i => observableOnFields (J := J) (f i)) ∧
      (1 ≤ J → 0 < b →
        sourcedPartitionFunction L m J b 0 = (partitionFunction L m J b : ℂ) ∧
          (normalizedActionMeasure L m J b).map (fun U => U.1) = wilsonGibbsMeasure L m J b)) ∧
  ∀ (n : ℕ) (β : ℂ) (f : Fin (n + 1) → FourTorus L m → ℝ), β ∈ nonvanishingCouplings L m J →
    (∀ i, IsBoundedOnTorus (f i)) →
      observableCumulant L m J β f = connectedFunction L m J β f
def Statement : Prop :=
  ∀ L m J : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    LogarithmBranchIndependence L m J ∧ KernelRegularity L m J ∧
      ConnectedFunctionEqKernelSum L m J ∧
      ConnectedFunctionAnalyticMultilinear L m J ∧
      ConnectedFunctionEqCumulant L m J
end ConnectedFunctionExpansion
end YangMills.Construction
