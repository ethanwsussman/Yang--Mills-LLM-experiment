import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def CompositeSecondOrderAtIdentity : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    ∀ (U : Set (Edge L n k i → Matrices.ComplexMatrix2))
      (W : Set (Edge L n k (i + 1) → Matrices.ComplexMatrix2))
      (F : (Edge L n k i → Matrices.ComplexMatrix2) → ℝ)
      (p : (Edge L n k (i + 1) → Matrices.ComplexMatrix2) → Edge L n k i → Matrices.ComplexMatrix2),
      IsOpenNhdOfOne U → IsAnalyticFieldFunction U F →
      IsOpenNhdOfOne W → IsAnalyticFieldMap W p →
      p (trivialField L n k (i + 1)) = trivialField L n k i →
      leftGradient (fieldSpace L n k i) (fun V => (F V : ℂ)) (trivialField L n k i) = 0 →
        (∃ W' : Set (Edge L n k (i + 1) → Matrices.ComplexMatrix2), IsOpenNhdOfOne W' ∧
          IsAnalyticFieldFunction W' fun V => F (p V)) ∧
        (∀ P : (Edge L n k i → Matrices.ComplexMatrix2) → Prop,
          EventuallyNearIdentity (fieldSpace L n k i) P →
          EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun V => P (p V)) ∧
        leftGradient (fieldSpace L n k (i + 1)) (fun V => (F (p V) : ℂ))
          (trivialField L n k (i + 1)) = 0 ∧
        ∀ X ∈ edgeFormSpace L n k (i + 1), ∀ Y ∈ edgeFormSpace L n k (i + 1),
          leftSecondDeriv (fun V => F (p V)) (trivialField L n k (i + 1)) X Y =
            leftSecondDeriv F (trivialField L n k i)
              (leftDifferential p (trivialField L n k (i + 1)) X)
              (leftDifferential p (trivialField L n k (i + 1)) Y)
end YangMills.Construction.Tower
end
