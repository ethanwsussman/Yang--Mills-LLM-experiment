import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRange
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.PeriodicOperators
def ReadsKernel {I I' : PeriodicData} {J J' : Type} (q : I.Carrier → J) (q' : I'.Carrier → J') (s : ℕ)
    (T : I'.Carrier → I.Carrier → ℂ) (M : J' → J → ℂ) : Prop :=
  ∀ i' i, M (q' i') (q i) = periodization I I' T s i' i
structure IsPeriodicQuotient (I : PeriodicData) {J : Type} (q : I.Carrier → J) (s : ℕ) : Prop where
  surjective : Function.Surjective q
  eq_iff_exists_translate : ∀ i i', q i = q i' ↔ ∃ m : Fin 4 → ℤ, i' = I.translate (s • m) i
def KernelMatricesOnSide : Prop :=
  ∀ (I I' I'' : PeriodicData), IsPeriodic I → IsPeriodic I' → IsPeriodic I'' →
    ∀ {J J' J'' : Type} (q : I.Carrier → J) (q' : I'.Carrier → J') (q'' : I''.Carrier → J'') (s : ℕ),
      0 < s → IsPeriodicQuotient I q s → IsPeriodicQuotient I' q' s → IsPeriodicQuotient I'' q'' s →
      (∀ (T : I'.Carrier → I.Carrier → ℂ) (S : I.Carrier → I''.Carrier → ℂ) (M : J' → J → ℂ)
        (N : J → J'' → ℂ), IsPeriodicKernel I I' T → IsPeriodicKernel I'' I S →
          ReadsKernel q q' s T M → ReadsKernel q'' q s S N →
          ReadsKernel q'' q' s (compKernel T S) (compKernel M N)) ∧
      (∀ T : I'.Carrier → I.Carrier → ℂ, IsPeriodicKernel I I' T → ∃ M : J' → J → ℂ, ReadsKernel q q' s T M) ∧
      (∀ [DecidableEq J], ReadsKernel q q s (idKernel I) fun j j' => if j = j' then 1 else 0)
end YangMills.Construction.RunningCouplingSlope
end
