import YangMills.Construction.LawInAState.DataOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
def separationLevelStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun T t => ∀ Ξ : ℝ,
    (T.stepParameters t).y₁ + 2 * (T.stepParameters t).B ≤ Ξ → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ (K : ℕ) (β : ℝ), IsFlowDatum (T.stepParameters t) Ξ K β → minimalCutoff (T.stepParameters t) Ξ δ ≤ K →
      IsSeparatedAt (T.stepParameters t) β K δ (separationLevel (T.stepParameters t) β K δ) ∧
      separationLevel (T.stepParameters t) β K δ < K ∧
      lengthInSites (T.stepParameters t).side K (separationLevel (T.stepParameters t) β K δ) δ ≤
        2 ^ 13 * ((T.stepParameters t).side : ℝ) *
          (TorusLumps.clusterRange (couplingAtSeparation (T.stepParameters t) β K δ) : ℝ)
end YangMills.Construction.StateLaws
end
