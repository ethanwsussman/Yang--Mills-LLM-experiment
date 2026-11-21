import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldOfCopies
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace YangMills.Construction
namespace MomentMethod
def exists_jointLimitLaw_statement : Prop :=
  ∀ (T : TranslatedLaws) (J : Type) [Countable J] (X : J → T.Family), T.IsPreserving →
    (∀ j, TranslatedLaws.HasBoundedMoments (X j)) →
    ∃ (sub : ℕ → ℕ) (P : Measure (TranslateValues J)), StrictMono sub ∧
      IsJointLimitLaw (T.subsequence sub) (fun j i => X j (sub i)) P
end MomentMethod
end YangMills.Construction
end
