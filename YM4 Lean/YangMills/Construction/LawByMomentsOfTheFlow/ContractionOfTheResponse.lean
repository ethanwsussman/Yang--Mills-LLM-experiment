import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def responseContractionStatement : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ Cw : ℝ, 0 < Cw ∧ ∃ (L₀ : ℕ) (rt₀ : RenormalizationStepParameters.ChainParameters → ℝ) (C₀ : ℝ), (∀ c, 0 < rt₀ c) ∧
    ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ Tb : RenormalizationStepParameters.ParameterAssignment, Tb.coupling = a → Tb.side = L → Tb.Admissible → Tb.ColdStepHolds →
      Tb.HoldsFrom WeightedResponses.ColdRegimeEstimatesAt →
      Tb.rt ≤ rt₀ Tb.toChainParameters → C₀ ≤ Tb.derivBound →
      Cw * (L : ℝ) ^ (-(1 / 2) : ℝ) ≤ 2⁻¹ ^ 10 * (L : ℝ) ^ (-(1 / 4) : ℝ) ∧
      ∃ y₀ : ℝ, ∀ z : ℝ, y₀ ≤ z → StepReturn.ExpansionReturnsAt (Tb.stepParameters z) →
        (∀ β : ℝ, z ≤ β → TorusLumps.HasExpansion (Tb.stepParameters z) 0 β (TorusLumps.wilsonWeight β)) →
        ∀ (u n : ℕ) [NeZero n], 64 ≤ n →
        ∀ (ω : TorusFields.TorusPlaquette (n * (Tb.stepParameters z).side) → ℝ) (ω' : TorusFields.TorusPlaquette n → ℝ),
          (∀ p, 0 < ω p) → (∀ p, 0 < ω' p) →
        IsSlowlyVaryingPair (Tb.stepParameters z).side ((Tb.stepParameters z).weightRate / 8) ω ω' →
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ColourForm n) (q : ENNReal), 1 ≤ q → Measurable X →
          weightedCurvatureNorm μ ω q (fun e => pushColours Tb.coupling Tb.ρA (Tb.stepParameters z).side u (X e)) ≤
            ENNReal.ofReal (Cw * (L : ℝ) ^ (-(1 / 2) : ℝ)) * weightedCurvatureNorm μ ω' q X
end YangMills.Construction.MomentLaw
end
