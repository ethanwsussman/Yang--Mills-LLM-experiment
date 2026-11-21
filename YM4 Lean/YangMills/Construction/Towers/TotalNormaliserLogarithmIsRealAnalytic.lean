import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def LogTotalNormaliserAnalytic : Prop :=
  ∀ L m k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    ∃ N : Set (Edge L m (k + 1) (k + 1) → Matrices.ComplexMatrix2), IsOpenNhdOfOne N ∧
      IsAnalyticFieldFunction N (logTotalNormaliserRatio L m (k + 1))
end YangMills.Construction.Tower
end
