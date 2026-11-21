import YangMills.Construction.TestSpaces.PointsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
universe u
noncomputable section
namespace YangMills.Construction
namespace Motions
def IsRigidMotion (r : (Fin 4 → ℝ) → Fin 4 → ℝ) : Prop :=
  ∃ A ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∃ b : Fin 4 → ℝ, ∀ u, r u = A.mulVec u + b
structure RigidMotion where
  mat : Matrix (Fin 4) (Fin 4) ℝ
  mat_mem : mat ∈ Matrix.orthogonalGroup (Fin 4) ℝ
  shift : Fin 4 → ℝ
namespace RigidMotion
def toFun (r : RigidMotion) (u : Fin 4 → ℝ) : Fin 4 → ℝ := r.mat.mulVec u + r.shift
def invFun (r : RigidMotion) (u : Fin 4 → ℝ) : Fin 4 → ℝ := r.mat⁻¹.mulVec (u - r.shift)
theorem exists_toFun_eq {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsRigidMotion s) :
    ∃ r : RigidMotion, r.toFun = s := by
  obtain ⟨A, hA, b, hsb⟩ := hs
  exact ⟨⟨A, hA, b⟩, funext fun u => (hsb u).symm⟩
theorem inv_mul_mat (r : RigidMotion) : r.mat⁻¹ * r.mat = 1 := by
  have h₁ : r.mat * r.mat.transpose = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).1 r.mat_mem
  rw [Matrix.inv_eq_right_inv h₁]
  exact mul_eq_one_comm.1 h₁
theorem mat_mul_inv (r : RigidMotion) : r.mat * r.mat⁻¹ = 1 := mul_eq_one_comm.1 r.inv_mul_mat
theorem invFun_toFun (r : RigidMotion) (u : Fin 4 → ℝ) : r.invFun (r.toFun u) = u := by
  simp [invFun, toFun, Matrix.mulVec_mulVec, r.inv_mul_mat]
theorem toFun_invFun (r : RigidMotion) (u : Fin 4 → ℝ) : r.toFun (r.invFun u) = u := by
  simp [invFun, toFun, Matrix.mulVec_mulVec, r.mat_mul_inv]
def timeReflection : RigidMotion where
  mat := Matrix.diagonal ![1, 1, 1, -1]
  mat_mem := by
    rw [Matrix.mem_orthogonalGroup_iff, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  shift := 0
theorem timeReflection_toFun : timeReflection.toFun = TestSpaces.timeReflect := by
  funext u i
  fin_cases i <;> simp [toFun, timeReflection, TestSpaces.timeReflect, Matrix.mulVec_diagonal]
theorem timeReflect_timeReflect (u : Fin 4 → ℝ) :
    TestSpaces.timeReflect (TestSpaces.timeReflect u) = u := by
  funext i
  fin_cases i <;> simp [TestSpaces.timeReflect]
theorem timeReflection_invFun : timeReflection.invFun = TestSpaces.timeReflect := by
  funext u
  have h := timeReflection.invFun_toFun (TestSpaces.timeReflect u)
  rwa [timeReflection_toFun, timeReflect_timeReflect] at h
end RigidMotion
open RigidMotion
section Functions
variable {n : ℕ} {F : Type*}
def actOnFun (r : RigidMotion) (φ : TestSpaces.PointTuple n → F) : TestSpaces.PointTuple n → F :=
  fun x => φ fun i => r.invFun (x i)
def permuteArgs (σ : Equiv.Perm (Fin n)) (φ : TestSpaces.PointTuple n → F) :
    TestSpaces.PointTuple n → F :=
  fun x => φ fun i => x (σ i)
def reflectConj (φ : TestSpaces.PointTuple n → ℂ) : TestSpaces.PointTuple n → ℂ :=
  fun x => conj (φ (TestSpaces.timeReflectTuple x))
end Functions
def reflectConjScalar (c : ℂ) : ℂ := conj c
def TensorVal (R : Type u) : ℕ → Type u
  | 0 => R
  | q + 1 => TestSpaces.PointTuple (q + 1) → R
def reflectConjVal : {q : ℕ} → TensorVal ℂ q → TensorVal ℂ q
  | 0, c => reflectConjScalar c
  | _ + 1, φ => reflectConj φ
section Tuples
variable {F : Type*} {q q' : ℕ}
def actOnPointFun (r : RigidMotion) (f : (Fin 4 → ℝ) → F) : (Fin 4 → ℝ) → F :=
  f ∘ r.invFun
def reflectFun (f : (Fin 4 → ℝ) → F) : (Fin 4 → ℝ) → F :=
  actOnPointFun timeReflection f
theorem reflectFun_eq (f : (Fin 4 → ℝ) → F) :
    reflectFun f = f ∘ TestSpaces.timeReflect := by
  rw [reflectFun, actOnPointFun, timeReflection_invFun]
def actOnTuple (r : RigidMotion) (X : Fin q → (Fin 4 → ℝ) → F) :
    Fin q → (Fin 4 → ℝ) → F :=
  fun i => actOnPointFun r (X i)
def reflectTuple (X : Fin q → (Fin 4 → ℝ) → F) : Fin q → (Fin 4 → ℝ) → F :=
  fun i => reflectFun (X i)
def concatTuple (X : Fin q → (Fin 4 → ℝ) → F) (Y : Fin q' → (Fin 4 → ℝ) → F) :
    Fin (q + q') → (Fin 4 → ℝ) → F :=
  Fin.append X Y
theorem concatTuple_castAdd (X : Fin q → (Fin 4 → ℝ) → F) (Y : Fin q' → (Fin 4 → ℝ) → F)
    (i : Fin q) : concatTuple X Y (Fin.castAdd q' i) = X i :=
  Fin.append_left X Y i
theorem concatTuple_natAdd (X : Fin q → (Fin 4 → ℝ) → F) (Y : Fin q' → (Fin 4 → ℝ) → F)
    (i : Fin q') : concatTuple X Y (Fin.natAdd q i) = Y i :=
  Fin.append_right X Y i
def tupleTensor {R : Type u} [CommMonoid R] :
    {q : ℕ} → (Fin q → (Fin 4 → ℝ) → R) → TensorVal R q
  | 0, _ => (1 : R)
  | _ + 1, X => TestSpaces.tensorProd X
end Tuples
end Motions
end YangMills.Construction
