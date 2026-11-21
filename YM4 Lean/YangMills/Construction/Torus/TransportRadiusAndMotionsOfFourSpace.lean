import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.Lattice.Worlds
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction
namespace TorusPeriodization
open TorusMetric PeriodicLattice TestFunctions
section Motions
open PeriodicLattice.CutoffTorus
theorem signedPermEuclidean_add (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℤˣ)
    (x y : Fin 4 → ℝ) :
    signedPermEuclidean σ ε (x + y) =
      signedPermEuclidean σ ε x + signedPermEuclidean σ ε y := by
  funext μ
  simp [signedPermEuclidean, mul_add]
theorem signedPermEuclidean_comp (σ σ' : Equiv.Perm (Fin 4)) (ε ε' : Fin 4 → ℤˣ)
    (x : Fin 4 → ℝ) :
    signedPermEuclidean σ ε (signedPermEuclidean σ' ε' x) =
      signedPermEuclidean (σ' * σ) (fun μ => ε μ * ε' (σ μ)) x := by
  funext μ
  simp [signedPermEuclidean, mul_assoc]
theorem signedPermEuclidean_inv (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℤˣ)
    (x : Fin 4 → ℝ) :
    signedPermEuclidean σ ε
        (signedPermEuclidean σ⁻¹ (fun ν => ε (σ.symm ν)) x) = x := by
  funext μ
  have h : ((ε μ : ℤ) : ℝ) * ((ε μ : ℤ) : ℝ) = 1 := by
    rcases Int.units_eq_one_or (ε μ) with h | h <;> simp [h]
  simp [signedPermEuclidean, ← mul_assoc, h]
def euclideanMotions : Subgroup (Equiv.Perm (Fin 4 → ℝ)) where
  carrier := {r | ∃ (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℤˣ) (v : Fin 4 → ℝ),
    ∀ x, r x = signedPermEuclidean σ ε x + v}
  mul_mem' := by
    rintro r r' ⟨σ, ε, v, h⟩ ⟨σ', ε', v', h'⟩
    refine ⟨σ' * σ, fun μ => ε μ * ε' (σ μ), signedPermEuclidean σ ε v' + v, fun x => ?_⟩
    rw [Equiv.Perm.mul_apply, h, h', signedPermEuclidean_add,
      signedPermEuclidean_comp, add_assoc]
  one_mem' := ⟨1, fun _ => 1, 0, fun x => by
    funext μ
    simp [signedPermEuclidean]⟩
  inv_mem' := by
    rintro r ⟨σ, ε, v, h⟩
    refine ⟨σ⁻¹, fun ν => ε (σ.symm ν),
      -signedPermEuclidean σ⁻¹ (fun ν => ε (σ.symm ν)) v, fun x => ?_⟩
    rw [Equiv.Perm.inv_eq_iff_eq, h, ← sub_eq_add_neg]
    have hs : signedPermEuclidean σ⁻¹ (fun ν => ε (σ.symm ν)) x =
        signedPermEuclidean σ⁻¹ (fun ν => ε (σ.symm ν)) (x - v) +
          signedPermEuclidean σ⁻¹ (fun ν => ε (σ.symm ν)) v := by
      rw [← signedPermEuclidean_add, sub_add_cancel]
    rw [hs, add_sub_cancel_right, signedPermEuclidean_inv, sub_add_cancel]
def inducedTorusMap (ℓ : ℝ) (r : Equiv.Perm (Fin 4 → ℝ)) (u : Torus4 ℓ) : Torus4 ℓ :=
  torusProj ℓ (r (liftPoint u))
theorem inducedTorusMap_torusProj (ℓ : ℝ) {r : Equiv.Perm (Fin 4 → ℝ)}
    (hr : r ∈ euclideanMotions) (x : Fin 4 → ℝ) :
    inducedTorusMap ℓ r (torusProj ℓ x) = torusProj ℓ (r x) := by
  obtain ⟨σ, ε, v, h⟩ := hr
  obtain ⟨k, hk⟩ := exists_latticeTranslate_of_torusProj_eq (torusProj_liftPoint (torusProj ℓ x))
  have hp : signedPermEuclidean σ ε (latticeTranslate ℓ k) =
      latticeTranslate ℓ (fun μ => (ε μ : ℤ) * k (σ μ)) := by
    funext μ
    simp only [signedPermEuclidean, latticeTranslate]
    push_cast
    ring
  rw [inducedTorusMap, hk, h, h, signedPermEuclidean_add, hp, add_right_comm,
    torusProj_add_latticeTranslate]
def torusMotion (ℓ : ℝ) (r : euclideanMotions) : Equiv.Perm (Torus4 ℓ) where
  toFun := inducedTorusMap ℓ r
  invFun := inducedTorusMap ℓ (r⁻¹ : euclideanMotions)
  left_inv u := by
    obtain ⟨x, rfl⟩ := torusProj_surjective ℓ u
    rw [inducedTorusMap_torusProj ℓ r.2, inducedTorusMap_torusProj ℓ (r⁻¹ : euclideanMotions).2]
    simp
  right_inv u := by
    obtain ⟨x, rfl⟩ := torusProj_surjective ℓ u
    rw [inducedTorusMap_torusProj ℓ (r⁻¹ : euclideanMotions).2, inducedTorusMap_torusProj ℓ r.2]
    simp
theorem torusMotion_torusProj (ℓ : ℝ) (r : euclideanMotions) (x : Fin 4 → ℝ) :
    torusMotion ℓ r (torusProj ℓ x) = torusProj ℓ ((r : Equiv.Perm (Fin 4 → ℝ)) x) :=
  inducedTorusMap_torusProj ℓ r.2 x
end Motions
end TorusPeriodization
end YangMills.Construction
