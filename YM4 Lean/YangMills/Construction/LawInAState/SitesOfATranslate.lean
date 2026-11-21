import YangMills.Construction.LawInAState.MarksOnABox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
def translateSitesStatement : Prop :=
  ∀ (L K k : ℕ) [NeZero L], Odd L → k ≤ K → ∀ (d : ℝ) (c : InfiniteLattice.AmbientSpace)
    (f : InfiniteLattice.AmbientSpace → ℝ), 0 < d → tsupport f ⊆ TestFunctions.closedBallR4 c d →
    ∃ z : TorusFields.TorusSite (BoxResponses.boxSide L K k), ∀ v : Fin 4 → ℤ,
      BoxMarks.weightSitesOf L K k (StateLaws.translateBy L K k v f) ⊆
        ResponseInTheExpansion.supBall (z + TorusFields.siteOfInt v) (StateLaws.lengthInSites L K k d + 4)
end YangMills.Construction.StateLaws
end
