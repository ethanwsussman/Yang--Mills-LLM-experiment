import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Tower
def LogNormaliserAnalyticNearOne : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → ∀ i : ℕ, i + 1 ≤ k →
    ∃ U : Set (Edge L n k (i + 1) → Matrices.ComplexMatrix2), IsOpenNhdOfOne U ∧
      IsAnalyticFieldFunction U (logNormaliserRatio L n k i)
end YangMills.Construction.Tower
