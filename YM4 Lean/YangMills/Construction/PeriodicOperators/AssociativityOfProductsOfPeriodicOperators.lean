import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.CompAssoc
def Claim : Prop :=
  ∀ A B C D : PeriodicData, IsPeriodic A → IsPeriodic B →
    IsPeriodic C → IsPeriodic D →
    ∀ (T : B.Carrier → A.Carrier → ℂ) (S : A.Carrier → C.Carrier → ℂ) (R : C.Carrier → D.Carrier → ℂ),
      IsPeriodicKernel A B T → IsPeriodicKernel C A S → IsPeriodicKernel D C R →
        (∀ x z, CompSummableAt T S x z) ∧ IsPeriodicKernel C B (compKernel T S) ∧
        (∀ y w, CompSummableAt S R y w) ∧
        IsPeriodicKernel D A (compKernel S R) ∧
        (∀ x w, CompSummableAt (compKernel T S) R x w) ∧
        IsPeriodicKernel D B (compKernel (compKernel T S) R) ∧
        (∀ x w, CompSummableAt T (compKernel S R) x w) ∧
        IsPeriodicKernel D B (compKernel T (compKernel S R)) ∧
        compKernel (compKernel T S) R = compKernel T (compKernel S R)
end YangMills.Construction.PeriodicOperators.CompAssoc
end
