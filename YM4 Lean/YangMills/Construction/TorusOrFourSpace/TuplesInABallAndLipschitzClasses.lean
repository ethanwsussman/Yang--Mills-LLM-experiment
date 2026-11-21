import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (D : Params) (E : Kind)
def IsMultilinearProd {n : ℕ} {V : Fin n → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℝ (V i)] (Φ : (∀ i, V i) → ℝ) : Prop :=
  ∀ (x : ∀ i, V i) (i : Fin n), IsLinearMap ℝ fun u : V i => Φ (Function.update x i u)
def permuteComponents {n : ℕ} (f : FnTuple D E n) (σ : Equiv.Perm (Fin n)) : FnTuple D E n :=
  fun i => f (σ i)
def IsPermSymmetricOn {n : ℕ} (K : Set (FnTuple D E n)) (Ψ : K → ℝ) : Prop :=
  ∀ (f : K) (σ : Equiv.Perm (Fin n)) (hσ : permuteComponents D E f.1 σ ∈ K),
    Ψ ⟨_, hσ⟩ = Ψ f
def sepC1TuplesInBall (n : ℕ) (ρ : ℝ≥0∞) : Set (FnTuple D E n) :=
  sepC1TuplesWithin D E n (centredBall D E ρ)
theorem mem_sepC1TuplesInBall_iff {n : ℕ} {ρ : ℝ≥0∞} {f : FnTuple D E n} :
    f ∈ sepC1TuplesInBall D E n ρ ↔
      f ∈ sepC1Tuples D E n ∧ ∀ i, supportQ D E (f i) ⊆ centredBall D E ρ :=
  Iff.rfl
theorem allowedRadii_euclidean : allowedRadii D euclidean = Set.Ioi 0 := rfl
theorem allowedRadii_torus : allowedRadii D torus = Set.Ioo 0 (D.side / 4) := rfl
theorem allowedRadii_torus_eq_Ioo_half_pow :
    allowedRadii D torus = Set.Ioo 0 ((D.L : ℝ) ^ (D.m : ℕ) / 2) := by
  rw [allowedRadii_torus, Params.side, PeriodicLattice.torusSide]
  congr 1
  ring
end YangMills.Construction.PeriodicSpace.Kind
