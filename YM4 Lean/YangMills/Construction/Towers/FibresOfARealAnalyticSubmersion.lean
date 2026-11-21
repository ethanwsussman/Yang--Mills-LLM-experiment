import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def SubmersionFibresAreSubmanifolds : Prop :=
  ∀ L n k a b : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → a ≤ k → b ≤ k →
    ∀ (𝒰 : Set (Edge L n k a → Matrices.ComplexMatrix2))
      (m : (Edge L n k a → Matrices.ComplexMatrix2) → Edge L n k b → Matrices.ComplexMatrix2),
      IsAnalyticFieldMap 𝒰 m →
      (∀ V ∈ 𝒰, ∀ B' ∈ edgeFormSpace L n k b, ∃ B ∈ edgeFormSpace L n k a, leftDifferential m V B = B') →
      ∀ W : Edge L n k b → Matrices.ComplexMatrix2,
        IsAnalyticFieldSubmanifold {V | V ∈ 𝒰 ∧ m V = W} ∧
        ∀ V, V ∈ 𝒰 → m V = W → ∀ B : Edge L n k a → Matrices.ComplexMatrix2,
          B ∈ (fieldCurveData L n k a).tangentSpan {V | V ∈ 𝒰 ∧ m V = W} V ↔
            B ∈ edgeFormSpace L n k a ∧ leftDifferential m V B = 0
end YangMills.Construction.Tower
end
