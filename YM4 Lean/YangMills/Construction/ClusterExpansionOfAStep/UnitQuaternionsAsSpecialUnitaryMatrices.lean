import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import YangMills.Construction.SoftAverages.QuaternionsAsMatrices
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open BlockAverages SoftAverages Matrices
theorem quaternionToMatrix_star (q : ℍ[ℝ]) :
    quaternionToMatrix (star q) = star (quaternionToMatrix q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionToMatrix]
theorem det_quaternionToMatrix (q : ℍ[ℝ]) :
    (quaternionToMatrix q).det = ((Quaternion.normSq q : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two, Quaternion.normSq_def', Complex.ext_iff]
  constructor
  · rw [Complex.ofReal_re]
    simp [quaternionToMatrix]
    ring
  · rw [Complex.ofReal_im]
    simp [quaternionToMatrix]
    ring
theorem quaternionToMatrix_injective : Function.Injective quaternionToMatrix := by
  intro p q hpq
  have h00 := congrFun (congrFun hpq 0) 0
  have h01 := congrFun (congrFun hpq 0) 1
  simp [quaternionToMatrix, Complex.ext_iff] at h00 h01
  exact Quaternion.ext _ _ h00.1 h00.2 h01.1 h01.2
theorem normSq_unitQuaternion (u : UnitQuaternion) : Quaternion.normSq (u : ℍ[ℝ]) = 1 := by
  have h2 := (Unitary.mem_iff.mp u.2).1
  rw [Quaternion.star_mul_self] at h2
  simpa using congrArg (fun z : ℍ[ℝ] => z.re) h2
theorem quaternionToMatrix_mem_specialUnitary (u : UnitQuaternion) :
    quaternionToMatrix (u : ℍ[ℝ]) ∈ ComplexMatrix2.specialUnitary := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · rw [← quaternionToMatrix_star, ← quaternionToMatrix_mul, (Unitary.mem_iff.mp u.2).2,
      quaternionToMatrix_one]
  · rw [det_quaternionToMatrix, normSq_unitQuaternion]
    simp
def unitQuaternionToSpecialUnitary : UnitQuaternion →* ComplexMatrix2.specialUnitary where
  toFun u := ⟨quaternionToMatrix (u : ℍ[ℝ]), quaternionToMatrix_mem_specialUnitary u⟩
  map_one' := Subtype.ext quaternionToMatrix_one
  map_mul' _ _ := Subtype.ext (quaternionToMatrix_mul _ _)
theorem unitQuaternionToSpecialUnitary_bijective :
    Function.Bijective unitQuaternionToSpecialUnitary := by
  constructor
  · intro u v huv
    exact Subtype.ext (quaternionToMatrix_injective (congrArg Subtype.val huv))
  · intro U
    obtain ⟨hU, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp U.2
    have hU' : star (U : ComplexMatrix2) * (U : ComplexMatrix2) = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp hU
    have hadj : star (U : ComplexMatrix2) = (U : ComplexMatrix2).adjugate := by
      have h1 : (U : ComplexMatrix2) * (U : ComplexMatrix2).adjugate = 1 := by
        rw [Matrix.mul_adjugate, hdet, one_smul]
      calc star (U : ComplexMatrix2)
          = star (U : ComplexMatrix2) * ((U : ComplexMatrix2) * (U : ComplexMatrix2).adjugate) := by
            rw [h1, mul_one]
        _ = (U : ComplexMatrix2).adjugate := by rw [← mul_assoc, hU', one_mul]
    have e00 := congrFun (congrFun hadj 0) 0
    have e10 := congrFun (congrFun hadj 1) 0
    rw [Matrix.adjugate_fin_two] at e00 e10
    simp at e00 e10
    have h10 : (U : ComplexMatrix2) 1 0 = -(starRingEnd ℂ) ((U : ComplexMatrix2) 0 1) := by
      rw [e10]; simp
    let q : ℍ[ℝ] := ⟨((U : ComplexMatrix2) 0 0).re, ((U : ComplexMatrix2) 0 0).im,
      ((U : ComplexMatrix2) 0 1).re, ((U : ComplexMatrix2) 0 1).im⟩
    have hq : quaternionToMatrix q = (U : ComplexMatrix2) := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [quaternionToMatrix, q, Complex.ext_iff]
      · simp [quaternionToMatrix, q, Complex.ext_iff]
      · simp [quaternionToMatrix, q, h10, Complex.ext_iff]
      · simp [quaternionToMatrix, q, ← e00, Complex.ext_iff]
    have hn : Quaternion.normSq q = 1 := by
      have := det_quaternionToMatrix q
      rw [hq, hdet] at this
      exact_mod_cast this.symm
    have hm : q ∈ unitary ℍ[ℝ] := by
      rw [Unitary.mem_iff, Quaternion.star_mul_self, Quaternion.self_mul_star, hn]
      simp
    exact ⟨⟨q, hm⟩, Subtype.ext hq⟩
def unitQuaternionEquivSpecialUnitary : UnitQuaternion ≃ₜ* ComplexMatrix2.specialUnitary :=
  let e := MulEquiv.ofBijective unitQuaternionToSpecialUnitary
    unitQuaternionToSpecialUnitary_bijective
  have hc : Continuous e := by
    refine Continuous.subtype_mk (continuous_quaternionToMatrix.comp continuous_subtype_val) _
  { e with
    continuous_toFun := hc
    continuous_invFun := (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) hc).symm.continuous }
theorem coe_unitQuaternionEquivSpecialUnitary (u : UnitQuaternion) :
    ((unitQuaternionEquivSpecialUnitary u : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      quaternionToMatrix (u : ℍ[ℝ]) := rfl
end ClusterExpansionOfAStep
end YangMills.Construction
end
