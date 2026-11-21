import YangMills.Construction.LawInAState.WilsonsLawOnTheLeastTorusInTheExpansionProof
import YangMills.Construction.LatticeForms.UnitDifferencesLatticeLaplacianAndTheTwoGreensFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.DiscreteTorusData
open YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint
section Periodic
variable {n : ℕ} {R : Type*}
def periodicExtension (f : IntegerTorus n → R) : (Fin 4 → ℤ) → R := fun N => f (zmodClass n N)
def IsPeriodicModulo (n : ℕ) (g : (Fin 4 → ℤ) → R) : Prop :=
  ∀ N w : Fin 4 → ℤ, g (N + (n : ℤ) • w) = g N
theorem zmodClass_residueLift [NeZero n] (z : IntegerTorus n) : zmodClass n (residueLift z) = z := by apply _root_.YangMills.DeltaSharedProofs.p501176 <;> assumption
theorem isPeriodicModulo_iff [NeZero n] (g : (Fin 4 → ℤ) → R) :
    IsPeriodicModulo n g ↔ ∃ f : IntegerTorus n → R, g = periodicExtension f := by
  constructor
  · intro hper
    refine ⟨fun z => g (residueLift z), funext fun N => ?_⟩
    have hsplit : N = residueLift (zmodClass n N) + (n : ℤ) • fun μ => N μ / n := by
      funext μ
      simp only [residueLift, zmodClass, ZMod.val_intCast, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact (Int.emod_add_mul_ediv _ _).symm
    simp only [periodicExtension]
    conv_lhs => rw [hsplit]
    exact hper _ _
  · rintro ⟨f, rfl⟩ N w
    simp only [periodicExtension]
    congr 1
    funext μ
    simp [zmodClass]
variable [AddCommGroup R]
end Periodic
section NormAndSum
variable {n : ℕ} [NeZero n]
def torusSum {R : Type*} [AddCommMonoid R] (f : IntegerTorus n → R) : R := ∑ z, f z
end NormAndSum
end YangMills.Construction.PeriodicLattice.DiscreteTorusData
end
