import YangMills.Construction.ResponseInTheExpansion.KernelOfTheCurvature
import YangMills.Construction.ResponseInTheExpansion.TheStepsAddUpToTheMaxwellCovariance
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages LumpContours ColdStepAtMirrorFrames WeightedResponses RenormalizationStepParameters TorusFields TorusLumps LinearResponse
open Classical
open MeasureTheory
variable (Tb : ParameterAssignment) (y : ℝ)
def dualMomentum {N : ℕ} (j : TorusSite N) : Fin 4 → ℝ :=
  fun i => 2 * Real.pi * ((j i).valMinAbs : ℝ) / (N : ℝ)
def maxwellSymbol (a : ℝ) (L k N : ℕ) [NeZero N] (p : Fin 4 → ℝ) (μ ν : Fin 4) : ℂ :=
  ∑ x : TorusSite N, (maxwellKernel a L k ((0 : TorusSite N), μ) (x, ν) : ℂ) * Complex.exp (Complex.I * (∑ i, p i *
    (torusDisplacement (0 : TorusSite N) x i + ((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2) : ℝ))
def periodShiftSign (i μ ν : Fin 4) : ℂ := (-1) ^ ((if i = μ then 1 else 0) + (if i = ν then 1 else 0))
def latticeMomentum (p : Fin 4 → ℝ) (i : Fin 4) : ℝ := 2 * Real.sin (p i / 2)
def symbolWithGradient (S : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ ν => S p μ ν + (latticeMomentum p μ * latticeMomentum p ν : ℝ)
def curlSymbol (p : Fin 4 → ℝ) (μ ν m : Fin 4) : ℂ :=
  Complex.I * (((if m = ν then latticeMomentum p μ else 0) - (if m = μ then latticeMomentum p ν else 0) : ℝ) : ℂ)
def inverseSymbolFourierSum (N : ℕ) [NeZero N] (S : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (μ ν ρ τ : Fin 4)
    (z : Fin 4 → ℝ) : ℂ :=
  ((N : ℂ) ^ 4)⁻¹ * ∑ j ∈ (Finset.univ : Finset (TorusSite N)).erase 0,
    (∑ m, ∑ m', (starRingEnd ℂ) (curlSymbol (dualMomentum j) μ ν m) *
        (symbolWithGradient S (dualMomentum j))⁻¹ m m' * curlSymbol (dualMomentum j) ρ τ m') *
      Complex.exp (Complex.I * (∑ i, dualMomentum j i * z i : ℝ))
def MaxwellSymbolBoundsAt : Prop :=
  ∃ (B : ℕ → ℝ) (C c : ℝ), 0 < c ∧ ∀ (k N : ℕ) [NeZero N], Tb.n₀ ≤ N →
    (∀ (r : ℕ) (μ ν : Fin 4) (p : Fin 4 → ℝ),
      ContDiff ℝ r (fun p => maxwellSymbol Tb.toChainParameters.coupling (Tb.stepParameters y).side k N p μ ν) ∧
      ‖iteratedFDeriv ℝ r
          (fun p => maxwellSymbol Tb.toChainParameters.coupling (Tb.stepParameters y).side k N p μ ν) p‖ ≤ B r) ∧
    (∀ (p : Fin 4 → ℝ) (i μ ν : Fin 4),
      maxwellSymbol Tb.toChainParameters.coupling (Tb.stepParameters y).side k N (p + Pi.single i (2 * Real.pi)) μ ν =
        periodShiftSign i μ ν * maxwellSymbol Tb.toChainParameters.coupling (Tb.stepParameters y).side k N p μ ν) ∧
    (∀ (p : Fin 4 → ℝ) (μ ν : Fin 4),
      ‖maxwellSymbol Tb.toChainParameters.coupling (Tb.stepParameters y).side k N p μ ν -
          ((sqNorm p * (if μ = ν then 1 else 0) - p μ * p ν : ℝ) : ℂ)‖ ≤
        C * (sqNorm p ^ 2 + Real.exp (-(c * (N : ℝ))))) ∧
    (∀ (p : Fin 4 → ℝ) (v : Fin 4 → ℂ),
      c * sqNorm (latticeMomentum p) * ∑ m, ‖v m‖ ^ 2 - C * Real.exp (-(c * (N : ℝ))) * ∑ m, ‖v m‖ ^ 2 ≤
        (∑ m, ∑ m', (starRingEnd ℂ) (v m) *
          symbolWithGradient (maxwellSymbol Tb.toChainParameters.coupling (Tb.stepParameters y).side k N) p m m' *
            v m').re) ∧
    ∀ Tt : TorusPlaquette N → TorusPlaquette N → ℝ,
      IsMaxwellCovariance Tb.toChainParameters.coupling (Tb.stepParameters y).side k Tt →
      ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)), ∀ p' ∈ plaquettesIn (Finset.univ : Finset (TorusSite N)),
        (Tt p p' : ℂ) = inverseSymbolFourierSum N
          (maxwellSymbol Tb.toChainParameters.coupling (Tb.stepParameters y).side k N)
          p.2.1 p.2.2 p'.2.1 p'.2.2 (plaquetteCentreDisplacement p p')
def maxwellSymbolStatement : Prop := HoldsOnParameterFamilies MaxwellSymbolBoundsAt
end YangMills.Construction.ResponseInTheExpansion
end
