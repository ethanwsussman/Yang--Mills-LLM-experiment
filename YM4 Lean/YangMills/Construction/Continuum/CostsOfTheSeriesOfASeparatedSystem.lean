import YangMills.Construction.Continuum.FormsBoundedOnSeparatedBalls
import YangMills.Construction.Continuum.FourierSeriesOfASystemDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
def SeparatedSystemCostsSummable : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (Q : PointSystem n), Q.IsSeparated → ∀ Φ ∈ Q.supportedClass,
    ∀ (c : ℝ) (a : ℕ) (G : ℝ) (T : smoothRealTupleSet n → ℝ),
      SeparatedBallBound c a G T → Q.CoeffCostSummable Φ c a G T
end YangMills.Construction.ConfigSpace
