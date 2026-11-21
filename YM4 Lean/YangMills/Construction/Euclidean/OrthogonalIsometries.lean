import Mathlib
open Matrix Set
noncomputable section
namespace YangMills.Construction.Euclidean
abbrev EuclidSpace4 : Type := Fin 4 → ℝ
abbrev RealMatrix4 : Type := Matrix (Fin 4) (Fin 4) ℝ
abbrev O4 := Matrix.orthogonalGroup (Fin 4) ℝ
def orthAct (R : O4) (x : EuclidSpace4) : EuclidSpace4 := (R : RealMatrix4) *ᵥ x
def signedPermMatrix (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) : RealMatrix4 :=
  Matrix.of fun μ ν => if ν = π μ then (((s μ : ℤˣ) : ℤ) : ℝ) else 0
theorem signedPermMatrix_mulVec (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) (x : EuclidSpace4)
    (μ : Fin 4) : (signedPermMatrix π s *ᵥ x) μ = (((s μ : ℤˣ) : ℤ) : ℝ) * x (π μ) := by
  simp [signedPermMatrix, Matrix.mulVec, dotProduct]
theorem signedPermMatrix_mul (π σ : Equiv.Perm (Fin 4)) (s t : Fin 4 → ℤˣ) :
    signedPermMatrix π s * signedPermMatrix σ t =
      signedPermMatrix (σ * π) fun μ => s μ * t (π μ) := by
  apply Matrix.mulVec_injective
  funext x
  funext μ
  rw [← Matrix.mulVec_mulVec, signedPermMatrix_mulVec, signedPermMatrix_mulVec,
    signedPermMatrix_mulVec]
  simp [mul_assoc]
theorem signedPermMatrix_one : signedPermMatrix 1 (fun _ => 1) = 1 := by
  apply Matrix.mulVec_injective
  funext x
  funext μ
  simp [signedPermMatrix_mulVec]
theorem signedPermMatrix_transpose (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) :
    (signedPermMatrix π s)ᵀ = signedPermMatrix π⁻¹ fun ν => s (π⁻¹ ν) := by
  ext μ ν
  simp only [signedPermMatrix, Matrix.transpose_apply, Matrix.of_apply]
  by_cases h : μ = π ν
  · subst h
    simp
  · have h' : ν ≠ π⁻¹ μ := fun e => h (by rw [e]; simp)
    rw [if_neg h, if_neg h']
theorem signedPermMatrix_mem_O4 (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) :
    signedPermMatrix π s ∈ O4 := by
  rw [Matrix.mem_orthogonalGroup_iff]
  change signedPermMatrix π s * (signedPermMatrix π s)ᵀ = 1
  rw [signedPermMatrix_transpose, signedPermMatrix_mul, ← signedPermMatrix_one]
  congr 1
  · simp
  · funext μ
    simp
def signedPermO4 (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) : O4 :=
  ⟨signedPermMatrix π s, signedPermMatrix_mem_O4 π s⟩
def hyperoctahedral4 : Subgroup O4 where
  carrier := {R | ∃ π s, R = signedPermO4 π s}
  mul_mem' := by
    rintro _ _ ⟨π, s, rfl⟩ ⟨σ, t, rfl⟩
    exact ⟨σ * π, fun μ => s μ * t (π μ), Subtype.ext (signedPermMatrix_mul π σ s t)⟩
  one_mem' := ⟨1, fun _ => 1, Subtype.ext signedPermMatrix_one.symm⟩
  inv_mem' := by
    rintro _ ⟨π, s, rfl⟩
    refine ⟨π⁻¹, fun ν => s (π⁻¹ ν), Subtype.ext ?_⟩
    exact signedPermMatrix_transpose π s
structure RigidMotion where
  linearPart : O4
  offset : EuclidSpace4
namespace RigidMotion
def ofO4 (R : O4) : RigidMotion := ⟨R, 0⟩
def actFun {E : Type*} (r : RigidMotion) (f : EuclidSpace4 → E) : EuclidSpace4 → E :=
  fun x => f (orthAct r.linearPart⁻¹ (x - r.offset))
theorem ofO4_actFun {E : Type*} (R : O4) (f : EuclidSpace4 → E)
    (x : EuclidSpace4) : (ofO4 R).actFun f x = f (orthAct R⁻¹ x) := by
  simp [actFun, ofO4]
end RigidMotion
end YangMills.Construction.Euclidean
