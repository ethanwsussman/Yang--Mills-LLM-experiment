import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldOfCopies
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace YangMills.Construction.MomentMethod
def leftValues {J J' : Type} (v : TranslateValues (J ⊕ J')) : TranslateValues J := fun a => v (Sum.inl a.1, a.2)
def jointLimitExtendStatement : Prop :=
  ∀ (T : TranslatedLaws) (J J' : Type) [Countable J] [Countable J'] (X : J → T.Family) (X' : J' → T.Family) (P : Measure (TranslateValues J)),
    T.IsPreserving → (∀ j, TranslatedLaws.HasBoundedMoments (X j)) → (∀ j, TranslatedLaws.HasBoundedMoments (X' j)) → IsJointLimitLaw T X P →
    ∃ (sub : ℕ → ℕ) (P' : Measure (TranslateValues (J ⊕ J'))), StrictMono sub ∧
      IsJointLimitLaw (T.subsequence sub) (fun j i => Sum.elim X X' j (sub i)) P' ∧ P'.map leftValues = P ∧
      ∀ (Y : TranslateValues J → ℝ) (b₁ b₂ : ℝ), Integrable Y P →
        (∀ᵐ v ∂P', b₁ ≤ invariantCondExp P' (Y ∘ leftValues) v ∧ invariantCondExp P' (Y ∘ leftValues) v ≤ b₂) →
        ∀ᵐ v ∂P, b₁ ≤ invariantCondExp P Y v ∧ invariantCondExp P Y v ≤ b₂
end YangMills.Construction.MomentMethod
end
