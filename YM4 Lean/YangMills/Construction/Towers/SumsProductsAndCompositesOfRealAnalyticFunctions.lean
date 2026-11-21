import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
def AnalyticFieldFunctionsClosed : Prop :=
  ∀ L n k j j' : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k → j' ≤ k →
    (∀ (U : Set (Edge L n k j → Matrices.ComplexMatrix2)) (c : ℝ),
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup U →
      IsAnalyticFieldFunction U fun _ => c) ∧
    (∀ (U : Set (Edge L n k j → Matrices.ComplexMatrix2))
      (F G : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ),
      IsAnalyticFieldFunction U F → IsAnalyticFieldFunction U G →
        (IsAnalyticFieldFunction U fun V => F V + G V) ∧
        IsAnalyticFieldFunction U fun V => F V * G V) ∧
    (∀ (U U' : Set (Edge L n k j → Matrices.ComplexMatrix2))
      (F : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ),
      IsAnalyticFieldFunction U F → IsOpenFieldSet PeriodicLattice.compactGaugeGroup U' → U' ⊆ U →
        IsAnalyticFieldFunction U' F) ∧
    (∀ (U : Set (Edge L n k j → Matrices.ComplexMatrix2))
      (F G : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ),
      IsAnalyticFieldFunction U F → EqOn F G U → IsAnalyticFieldFunction U G) ∧
    ∀ (U : Set (Edge L n k j → Matrices.ComplexMatrix2))
      (U' : Set (Edge L n k j' → Matrices.ComplexMatrix2))
      (φ : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2)
      (F : (Edge L n k j' → Matrices.ComplexMatrix2) → ℝ),
      IsAnalyticFieldMap U φ → IsAnalyticFieldFunction U' F →
        IsAnalyticFieldFunction (U ∩ φ ⁻¹' U') (F ∘ φ)
end YangMills.Construction.Tower
end
