import YangMills.Construction.HilbertSpace.FormsAndOperators
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PositiveOperators
def CommutingPositiveProduct : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : ℕ) (_ : 1 ≤ J) (A : Fin J → H →L[ℂ] H),
    Pairwise (fun i j => Commute (A i) (A j)) →
    (∀ i, YangMills.Construction.HilbertSpaceBasics.IsPositiveOp (A i)) →
    YangMills.Construction.HilbertSpaceBasics.IsPositiveOp (List.ofFn A).prod
end YangMills.Construction.PositiveOperators
