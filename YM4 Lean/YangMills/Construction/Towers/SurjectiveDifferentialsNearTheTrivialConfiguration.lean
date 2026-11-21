import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def DifferentialSurjectiveNearIdentity : Prop :=
  ∀ L n k a b : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → a ≤ k → b ≤ k →
    ∀ (U : Set (Edge L n k a → Matrices.ComplexMatrix2))
      (m : (Edge L n k a → Matrices.ComplexMatrix2) → Edge L n k b → Matrices.ComplexMatrix2),
      IsOpenNhdOfOne U → IsAnalyticFieldMap U m →
      (∀ Y ∈ edgeFormSpace L n k b, ∃ X ∈ edgeFormSpace L n k a,
        leftDifferential m (trivialField L n k a) X = Y) →
      ∃ U' : Set (Edge L n k a → Matrices.ComplexMatrix2), U' ⊆ U ∧ IsOpenNhdOfOne U' ∧
        EventuallyNearIdentity (fieldSpace L n k a) (fun V => V ∈ U') ∧
        IsAnalyticFieldMap U' m ∧
        ∀ V ∈ U', ∀ Y ∈ edgeFormSpace L n k b, ∃ X ∈ edgeFormSpace L n k a,
          leftDifferential m V X = Y
end YangMills.Construction.Tower
end
