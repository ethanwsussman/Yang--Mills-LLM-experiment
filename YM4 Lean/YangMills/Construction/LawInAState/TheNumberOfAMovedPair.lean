import YangMills.Construction.LawInAState.DataOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
def covarianceTranslationInvariantStatement : Prop :=
  ∀ (L K k : ℕ) (β δ ν : ℝ) (v : Fin 4 → ℤ) (f g : InfiniteLattice.AmbientSpace → ℝ), Odd L → 13 ≤ L → 0 < K →
    k ≤ K → 0 < β → 0 < δ → 0 < ν → ν ≤ 1 → IsNormalizedTestPair δ ν f g →
    unitTorusCovariance L K β (translateBy L K k v f) (translateBy L K k v g) = unitTorusCovariance L K β f g
end YangMills.Construction.StateLaws
end
