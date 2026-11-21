import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.MeanInTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames FamilyNorms Estimates
namespace BlockMeans
def segmentAveragedMean (a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (φ h : LocalFamily) : TopLevelFamily :=
  fun F Y V => ∫ θ in (0 : ℝ)..1, conditionalExpansionMean true a ρA ρ x m p (φ + θ • h) h F Y V
structure SegmentMeanBounds (a ρA σ x κ δ ε ε₃ CE : ℝ) (L t n₀ m : ℕ) (p : ℝ → ℝ) (φ h : LocalFamily) :
    Prop where
  density : IsLocalDensity L t n₀ (5 / 4 * σ) (segmentAveragedMean a ρA (σ / 64) x m p φ h)
  decay : DerivDecay L t n₀ (5 / 4 * σ) (segmentAveragedMean a ρA (σ / 64) x m p φ h) fun k n =>
    2⁻¹ ^ 6 * (if k = 3 then ε₃ else ε) / torusDecayFactor L δ n +
      CE * ε * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(κ / 2 ^ 6 * n))
  locality : IsLocalOnTori L t n₀ (9 / 8 * σ) (centredFamily (segmentAveragedMean a ρA (σ / 64) x m p φ h))
    fun r => 2⁻¹ ^ 4 * ε / torusDecayFactor L δ r
  flat_form : ∃ q : BondBilinearForm,
    (∀ b b' X X', Filter.Tendsto (fun n => secondDerivAtUniform (segmentAveragedMean a ρA (σ / 64) x m p φ h)
      L t n b b' X X') Filter.atTop (nhds (q b b' X X'))) ∧
    ∀ (X : imaginaryQuaternions) (μ ν : Fin 4) (B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
      ‖X‖ = 1 → μ < ν → IsLinearPotential (constantPlaneCurvature X μ ν) B →
      ∃ v : ℝ, HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        q e.1 e.2 (B e.1) (B e.2)) v ∧ |v| ≤ CE * ε * x ^ (-(1 / 2 : ℝ))
def SegmentMeanBoundsAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (φ h : LocalFamily) (ε : ℝ), T.coupling ≤ x → 0 < ε →
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E (T.E / T.η₃) (φ + θ • h)) →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate ε (ε / T.η₃) h →
    SegmentMeanBounds T.a T.chainParams.ρA T.σ x T.κ T.decayRate ε (ε / T.η₃) T.CE T.L t T.n₀
      (frameRadius x) T.p φ h
def segmentMeanStatement : Prop := EventuallyInParameters SegmentMeanBoundsAt
end BlockMeans
end YangMills.Construction
end
