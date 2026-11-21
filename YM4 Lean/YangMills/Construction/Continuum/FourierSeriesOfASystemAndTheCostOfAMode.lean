import YangMills.Construction.Continuum.FormsBoundedOnSeparatedBalls
import YangMills.Construction.Continuum.FourierSeriesOfASystemDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
def FourierExpansionAndModeCosts : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Q : PointSystem n), ∀ Φ ∈ Q.supportedClass,
    Q.CoeffDecay Φ ∧ Q.ModesLocalCharacters ∧ Q.HasFourierExpansion Φ ∧
      Q.TruncationsConverge Φ ∧ IntegerLatticeSumBound n ∧
      (2 ≤ n → Q.IsSeparated → ∀ (c : ℝ) (a : ℕ) (G : ℝ) (T : smoothRealTupleSet n → ℝ),
        SeparatedBallBound c a G T →
          Q.ModeBounds c a G T ∧ Q.CoeffCostSummable Φ c a G T)
end YangMills.Construction.ConfigSpace
