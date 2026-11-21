import YangMills.Construction.TestSpaces.PointsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
open Complex Matrix
noncomputable section
namespace YangMills.Construction
namespace MinkowskiSpace
abbrev ComplexVec4 : Type := Fin 4 → ℂ
abbrev RealVec4 : Type := Fin 4 → ℝ
abbrev ComplexMat4 : Type := Matrix (Fin 4) (Fin 4) ℂ
abbrev RealMat4 : Type := Matrix (Fin 4) (Fin 4) ℝ
def spacePart {α : Type*} (ζ : Fin 4 → α) : Fin 3 → α := fun i => ζ i.succ
def mkTimeSpace {α : Type*} (t : α) (v : Fin 3 → α) : Fin 4 → α := Fin.cons t v
def toComplex (x : RealVec4) : ComplexVec4 := fun μ => (x μ : ℂ)
def tupleToComplex {n : ℕ} (x : TestSpaces.PointTuple n) : Fin n → ComplexVec4 :=
  fun i => toComplex (x i)
def timeUnit : RealVec4 := mkTimeSpace 1 0
def ofSpaceVector (v : Fin 3 → ℝ) : RealVec4 := mkTimeSpace 0 v
def spaceBilin (v w : Fin 3 → ℂ) : ℂ := ∑ i, v i * w i
def minkowskiForm (ζ ζ' : ComplexVec4) : ℂ :=
  ζ 0 * ζ' 0 - spaceBilin (spacePart ζ) (spacePart ζ')
def rePart (ζ : ComplexVec4) : RealVec4 := fun μ => (ζ μ).re
def imPart (ζ : ComplexVec4) : RealVec4 := fun μ => (ζ μ).im
theorem eq_rePart_add_I_smul_imPart (ζ : ComplexVec4) :
    ζ = toComplex (rePart ζ) + I • toComplex (imPart ζ) := by
  funext μ
  simp [toComplex, rePart, imPart, mul_comm I]
def conjPoint (ζ : ComplexVec4) : ComplexVec4 :=
  toComplex (rePart ζ) - I • toComplex (imPart ζ)
def spaceNorm (v : Fin 3 → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)
def l1Norm (ζ : ComplexVec4) : ℝ :=
  |rePart ζ 0| + spaceNorm (spacePart (rePart ζ)) +
    |imPart ζ 0| + spaceNorm (spacePart (imPart ζ))
def coneGap (y : RealVec4) : ℝ := y 0 - spaceNorm (spacePart y)
def futureCone : Set RealVec4 := {y | coneGap y > 0}
def closedFutureCone : Set RealVec4 := {y | coneGap y ≥ 0}
def futureTube : Set ComplexVec4 := {ζ | imPart ζ ∈ futureCone}
def tubeGap (ζ : ComplexVec4) : ℝ := coneGap (imPart ζ)
def IsSpacelikeVec (x : RealVec4) : Prop := (minkowskiForm (toComplex x) (toComplex x)).re < 0
theorem isSpacelikeVec_iff (x : RealVec4) :
    IsSpacelikeVec x ↔ spaceNorm (spacePart x) > |x 0| := by
  have hq : (minkowskiForm (toComplex x) (toComplex x)).re = x 0 ^ 2 - ∑ i, spacePart x i ^ 2 := by
    simp only [minkowskiForm, spaceBilin, spacePart, toComplex, Fin.sum_univ_three,
      ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_sub, Complex.ofReal_re]
    ring
  unfold IsSpacelikeVec spaceNorm
  rw [hq, gt_iff_lt, Real.lt_sqrt (abs_nonneg _), sq_abs, sub_neg]
def spacelikeSet : Set RealVec4 := {x | IsSpacelikeVec x}
def successiveDiffs {n : ℕ} (z : Fin (n + 1) → ComplexVec4) : Fin n → ComplexVec4 :=
  fun i => z i.succ - z i.castSucc
def diffCoords {n : ℕ} (z : Fin (n + 1) → ComplexVec4) : Fin (n + 1) → ComplexVec4 :=
  Fin.cons (z 0) (successiveDiffs z)
def cumulativeSums {n : ℕ} (Y : TestSpaces.PointTuple (n + 1)) : TestSpaces.PointTuple (n + 1) :=
  fun k => ∑ j ∈ Finset.Iic k, Y j
theorem minkowskiForm_add_left (a b c : ComplexVec4) :
    minkowskiForm (a + b) c = minkowskiForm a c + minkowskiForm b c := by
  simp only [minkowskiForm, spaceBilin, spacePart, Pi.add_apply, Fin.sum_univ_three]
  ring
theorem minkowskiForm_add_right (a b c : ComplexVec4) :
    minkowskiForm a (b + c) = minkowskiForm a b + minkowskiForm a c := by
  simp only [minkowskiForm, spaceBilin, spacePart, Pi.add_apply, Fin.sum_univ_three]
  ring
theorem minkowskiForm_smul_left (t : ℂ) (a b : ComplexVec4) :
    minkowskiForm (t • a) b = t * minkowskiForm a b := by
  simp only [minkowskiForm, spaceBilin, spacePart, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring
theorem minkowskiForm_smul_right (t : ℂ) (a b : ComplexVec4) :
    minkowskiForm a (t • b) = t * minkowskiForm a b := by
  simp only [minkowskiForm, spaceBilin, spacePart, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring
def lorentzGroupC : Set ComplexMat4 :=
  {Λ | ∀ ζ ζ' : ComplexVec4, minkowskiForm (Λ *ᵥ ζ) (Λ *ᵥ ζ') = minkowskiForm ζ ζ'}
def lorentzAlgebraC : Submodule ℂ ComplexMat4 where
  carrier := {Z | ∀ ζ ζ' : ComplexVec4, minkowskiForm (Z *ᵥ ζ) ζ' + minkowskiForm ζ (Z *ᵥ ζ') = 0}
  add_mem' := by
    intro A B hA hB ζ ζ'
    have h := hA ζ ζ'
    have k := hB ζ ζ'
    rw [Matrix.add_mulVec, Matrix.add_mulVec, minkowskiForm_add_left, minkowskiForm_add_right]
    linear_combination h + k
  zero_mem' := by
    intro ζ ζ'
    have h0 : ∀ a : ComplexVec4, minkowskiForm 0 a = 0 := fun a => by
      simpa using minkowskiForm_smul_left 0 0 a
    have h1 : ∀ a : ComplexVec4, minkowskiForm a 0 = 0 := fun a => by
      simpa using minkowskiForm_smul_right 0 a 0
    simp [h0, h1]
  smul_mem' := by
    intro t A hA ζ ζ'
    have h := hA ζ ζ'
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, minkowskiForm_smul_left, minkowskiForm_smul_right]
    linear_combination t * h
def toComplexMatrix (Λ : RealMat4) : ComplexMat4 := Λ.map fun r => (r : ℂ)
def restrictedLorentz : Set RealMat4 :=
  {Λ | toComplexMatrix Λ ∈ lorentzGroupC ∧ Λ.det = 1 ∧
    (minkowskiForm (toComplex timeUnit) (toComplexMatrix Λ *ᵥ toComplex timeUnit)).re ≥ 1}
def restrictedPoincare : Set (RealVec4 × RealMat4) :=
  (Set.univ : Set RealVec4) ×ˢ restrictedLorentz
def poincareMul (g g' : RealVec4 × RealMat4) : RealVec4 × RealMat4 :=
  (g.1 + g.2 *ᵥ g'.1, g.2 * g'.2)
def poincareSMul (g : RealVec4 × RealMat4) (x : RealVec4) : RealVec4 := g.2 *ᵥ x + g.1
def mulVecTuple {n : ℕ} (M : ComplexMat4) (z : Fin n → ComplexVec4) :
    Fin n → ComplexVec4 := fun i => M *ᵥ z i
def poincarePullback {n : ℕ} {F : Type*} (g : RealVec4 × RealMat4)
    (φ : TestSpaces.PointTuple n → F) : TestSpaces.PointTuple n → F :=
  fun x => φ fun i => g.2⁻¹ *ᵥ (x i - g.1)
def poincareScalar (_g : RealVec4 × RealMat4) (c : ℂ) : ℂ := c
def rotationLinearMap (R : Matrix.orthogonalGroup (Fin 3) ℝ) : ComplexVec4 →ₗ[ℂ] ComplexVec4 where
  toFun ζ := mkTimeSpace (ζ 0) (((R : Matrix (Fin 3) (Fin 3) ℝ).map fun r => (r : ℂ)) *ᵥ spacePart ζ)
  map_add' a b := by
    funext μ
    refine Fin.cases ?_ (fun i => ?_) μ
    · simp [mkTimeSpace]
    · have h : spacePart (a + b) = spacePart a + spacePart b := rfl
      simp [mkTimeSpace, h, Matrix.mulVec_add]
  map_smul' t a := by
    funext μ
    refine Fin.cases ?_ (fun i => ?_) μ
    · simp [mkTimeSpace]
    · have h : spacePart (t • a) = t • spacePart a := rfl
      simp [mkTimeSpace, h, Matrix.mulVec_smul]
def rotationMatrix (R : Matrix.orthogonalGroup (Fin 3) ℝ) : ComplexMat4 :=
  LinearMap.toMatrix' (rotationLinearMap R)
def unitSphere3 : Set (Fin 3 → ℝ) := {v | spaceNorm v = 1}
def axisDot (v : Fin 3 → ℝ) (ζ : ComplexVec4) : ℂ :=
  spaceBilin (fun i => (v i : ℂ)) (spacePart ζ)
def boostLinearMap (v : unitSphere3) (β : ℂ) : ComplexVec4 →ₗ[ℂ] ComplexVec4 where
  toFun ζ := ζ +
    (Complex.cosh β - 1) •
      (ζ 0 • toComplex timeUnit + axisDot v ζ • toComplex (ofSpaceVector v)) +
    Complex.sinh β •
      (axisDot v ζ • toComplex timeUnit + ζ 0 • toComplex (ofSpaceVector v))
  map_add' a b := by
    have h : axisDot v (a + b) = axisDot v a + axisDot v b := by
      simp only [axisDot, spaceBilin, spacePart, Pi.add_apply, Fin.sum_univ_three]
      ring
    funext μ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h]
    ring
  map_smul' t a := by
    have h : axisDot v (t • a) = t * axisDot v a := by
      simp only [axisDot, spaceBilin, spacePart, Pi.smul_apply, smul_eq_mul,
        Fin.sum_univ_three]
      ring
    funext μ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h, RingHom.id_apply]
    ring
def boostMatrix (v : unitSphere3) (β : ℂ) : ComplexMat4 := LinearMap.toMatrix' (boostLinearMap v β)
theorem rotationMatrix_mulVec (R : Matrix.orthogonalGroup (Fin 3) ℝ) (ζ : ComplexVec4) :
    rotationMatrix R *ᵥ ζ = rotationLinearMap R ζ :=
  LinearMap.toMatrix'_mulVec _ _
theorem boostMatrix_mulVec (v : unitSphere3) (β : ℂ) (ζ : ComplexVec4) :
    boostMatrix v β *ᵥ ζ = boostLinearMap v β ζ :=
  LinearMap.toMatrix'_mulVec _ _
def wickMap : ComplexVec4 ≃ₗ[ℂ] ComplexVec4 where
  toFun x := ![I * x 3, x 0, x 1, x 2]
  invFun y := ![y 1, y 2, y 3, -I * y 0]
  map_add' a b := by
    funext μ
    fin_cases μ <;> simp [mul_add]
  map_smul' t a := by
    funext μ
    fin_cases μ <;> simp [mul_left_comm]
  left_inv x := by
    funext μ
    fin_cases μ <;> simp [← mul_assoc]
  right_inv y := by
    funext μ
    fin_cases μ <;> simp [← mul_assoc]
theorem wickMap_apply_zero (x : ComplexVec4) : wickMap x 0 = I * x 3 := rfl
theorem spacePart_wickMap (x : ComplexVec4) :
    spacePart (wickMap x) = ![x 0, x 1, x 2] := by
  funext i
  fin_cases i <;> rfl
def wickMapTuple {n : ℕ} (z : Fin n → ComplexVec4) : Fin n → ComplexVec4 :=
  fun i => wickMap (z i)
theorem diffCoords_cumulativeSums {n : ℕ} (Y : TestSpaces.PointTuple (n + 1)) :
    diffCoords (tupleToComplex (cumulativeSums Y)) = tupleToComplex Y := by
  have hsucc : ∀ i : Fin n,
      cumulativeSums Y i.succ = cumulativeSums Y i.castSucc + Y i.succ := by
    intro i
    have hI : Finset.Iic i.succ = insert i.succ (Finset.Iic i.castSucc) := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_insert]
      constructor
      · intro h
        rcases eq_or_lt_of_le h with h | h
        · exact Or.inl h
        · exact Or.inr (Fin.le_castSucc_iff.mpr h)
      · rintro (h | h)
        · exact h.le
        · exact h.trans (Fin.castSucc_lt_succ).le
    have hnot : i.succ ∉ Finset.Iic i.castSucc := by
      simp
    unfold cumulativeSums
    rw [hI, Finset.sum_insert hnot, add_comm]
  have hzero : cumulativeSums Y 0 = Y 0 := by
    have hI : Finset.Iic (0 : Fin (n + 1)) = {0} := by
      ext j
      simp
    simp [cumulativeSums, hI]
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · simp [diffCoords, tupleToComplex, hzero]
  · funext μ
    simp [diffCoords, successiveDiffs, tupleToComplex, toComplex, hsucc]
end MinkowskiSpace
end YangMills.Construction

namespace YangMills.Construction.WightmanTheory
open MinkowskiSpace
theorem continuous_coneGap : Continuous coneGap := by
  unfold coneGap spaceNorm spacePart
  fun_prop
def closedFutureConeBorel : {S : Set (Fin 4 → ℝ) // MeasurableSet S} :=
  ⟨closedFutureCone, (isClosed_le continuous_const continuous_coneGap).measurableSet⟩
end YangMills.Construction.WightmanTheory
