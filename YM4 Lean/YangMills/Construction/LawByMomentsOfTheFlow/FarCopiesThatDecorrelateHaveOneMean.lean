import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldOfCopies
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace YangMills.Construction.MomentMethod
def decorrelatedTranslatesMeanStatement : Prop :=
  ∀ (T : TranslatedLaws) (J : Type) [Countable J] (X : J → T.Family) (P : Measure (TranslateValues J)), T.IsPreserving →
    (∀ j, TranslatedLaws.HasBoundedMoments (X j)) → IsJointLimitLaw T X P → ∀ jR jX jE : J,
    (∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∃ i₀ : ℕ, ∀ i, i₀ ≤ i →
      |∫ ω, (X jR i ω * (X jX i ω - X jE i ω)) *
          (TranslatedLaws.translate (X jR) k i ω * (TranslatedLaws.translate (X jX) k i ω - TranslatedLaws.translate (X jE) k i ω)) ∂(T.μ i)| ≤ ε) →
    invariantCondExp P (fun v => v (jR, 0) * v (jX, 0)) =ᵐ[P] invariantCondExp P (fun v => v (jR, 0) * v (jE, 0))
end YangMills.Construction.MomentMethod
end
