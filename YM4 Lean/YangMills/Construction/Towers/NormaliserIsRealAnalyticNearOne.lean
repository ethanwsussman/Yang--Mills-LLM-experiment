import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower
def GaussianNormaliserAnalyticNearIdentity : Prop :=
  ∀ L m k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ a : ℕ, a + 1 ≤ k →
    ∃ O : Set (Edge L m k (a + 1) → Matrices.ComplexMatrix2), IsOpenNhdOfOne O ∧
      IsAnalyticFieldFunction O (gaussianNormaliser L m k a)
end YangMills.Construction.Tower
