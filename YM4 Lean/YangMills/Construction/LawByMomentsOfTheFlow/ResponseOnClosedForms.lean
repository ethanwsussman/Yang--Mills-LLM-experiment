import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses ResponseInTheExpansion TorusLumps
def responseMapClosedFormsStatement : Prop :=
  HoldsOnParameterFamilies fun Tb y => ∀ (u n : ℕ) [NeZero n], 64 ≤ n →
    (∀ φ : TorusSite n → ℝ,
      responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u (latticeGradient φ) =
        latticeGradient fun x => φ (parentBlock (Tb.stepParameters y).side x)) ∧
    (∀ (v : Fin 4 → ℝ) (p : TorusPlaquette (n * (Tb.stepParameters y).side)),
      curl (responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u (constantOneForm v)) p = 0) ∧
    ∀ A A' : TorusBond n → ℝ, (∀ p, curl A p = curl A' p) → ∀ p,
      curl (responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u A) p =
        curl (responseMap Tb.coupling Tb.ρA (Tb.stepParameters y).side u A') p
end YangMills.Construction.MomentLaw
end
