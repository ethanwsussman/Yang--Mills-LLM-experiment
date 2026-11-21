import YangMills.Construction.LawInAState.MarksOnABox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
def siteNearPairStatement : Prop :=
  ∀ (L K k m : ℕ) [NeZero L] (c : InfiniteLattice.AmbientSpace) (ρ : ℝ), Odd L → k ≤ K → 0 ≤ ρ →
    ∃ o : TorusFields.TorusSite (BoxResponses.boxSide L K k),
      ∀ g : InfiniteLattice.AmbientSpace → ℝ, (∀ x ∈ tsupport g, ∀ i, |x i - c i| ≤ ρ) →
      ∀ v ∈ StateLaws.shiftSet m, BoxMarks.weightSitesOf L K k (StateLaws.translateBy L K k v g) ⊆
        ResponseInTheExpansion.supBall o ((L : ℝ) ^ (K - k) * ρ + m + 4)
end YangMills.Construction.StateLaws
end
