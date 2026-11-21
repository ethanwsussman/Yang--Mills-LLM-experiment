import YangMills.Construction.Continuum.FormsBoundedOnSeparatedBalls
import YangMills.Construction.Continuum.FourierSeriesOfASystemDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ConfigSpace
def ModeCostOfSeparated : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (Q : PointSystem n), Q.IsSeparated →
    ∀ (c : ℝ) (a : ℕ) (G : ℝ) (T : smoothRealTupleSet n → ℝ),
      SeparatedBallBound c a G T → Q.ModeBounds c a G T
end ConfigSpace
end YangMills.Construction
end
