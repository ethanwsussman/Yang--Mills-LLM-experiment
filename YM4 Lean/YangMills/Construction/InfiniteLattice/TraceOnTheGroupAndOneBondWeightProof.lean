import YangMills.Construction.ChessboardTori.AssertionsOfTheTransferPictureProof
import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.TraceOnTheGroupAndOneBondWeight
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace SUTwoTrace
open YangMills.Construction.Matrices
open YangMills.Construction.Matrices.ComplexMatrix2
theorem star_eq_adjugate (g : specialUnitary) :
    star (g : ComplexMatrix2) = Matrix.adjugate (g : ComplexMatrix2) := by
  have hunit : star (g : ComplexMatrix2) * (g : ComplexMatrix2) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
  have hdet : (g : ComplexMatrix2).det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
  calc star (g : ComplexMatrix2)
        = star (g : ComplexMatrix2) * ((g : ComplexMatrix2) * Matrix.adjugate (g : ComplexMatrix2)) := by
        rw [Matrix.mul_adjugate, hdet, one_smul, mul_one]
    _ = Matrix.adjugate (g : ComplexMatrix2) := by rw [← mul_assoc, hunit, one_mul]
theorem star_entry_relations (g : specialUnitary) :
    star ((g : ComplexMatrix2) 0 0) = (g : ComplexMatrix2) 1 1 ∧
      star ((g : ComplexMatrix2) 1 0) = -(g : ComplexMatrix2) 0 1 ∧
      star ((g : ComplexMatrix2) 0 1) = -(g : ComplexMatrix2) 1 0 ∧
      star ((g : ComplexMatrix2) 1 1) = (g : ComplexMatrix2) 0 0 := by
  have hadj := star_eq_adjugate g
  rw [Matrix.adjugate_fin_two] at hadj
  have hentry : ∀ i j, star ((g : ComplexMatrix2) j i) =
      (!![(g : ComplexMatrix2) 1 1, -(g : ComplexMatrix2) 0 1;
        -(g : ComplexMatrix2) 1 0, (g : ComplexMatrix2) 0 0] : ComplexMatrix2) i j := by
    intro i j
    rw [← hadj, Matrix.star_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hentry 0 0
  · simpa using hentry 0 1
  · simpa using hentry 1 0
  · simpa using hentry 1 1
theorem coe_inv_eq (g : specialUnitary) : ((g⁻¹ : specialUnitary) : ComplexMatrix2) =
    !![(g : ComplexMatrix2) 1 1, -(g : ComplexMatrix2) 0 1;
      -(g : ComplexMatrix2) 1 0, (g : ComplexMatrix2) 0 0] := by
  have hstar : ((g⁻¹ : specialUnitary) : ComplexMatrix2) = star (g : ComplexMatrix2) := rfl
  rw [hstar, star_eq_adjugate, Matrix.adjugate_fin_two]
theorem conjEntries_eq (g : specialUnitary) : conjEntries (g : ComplexMatrix2) =
    !![(g : ComplexMatrix2) 1 1, -(g : ComplexMatrix2) 1 0;
      -(g : ComplexMatrix2) 0 1, (g : ComplexMatrix2) 0 0] := by
  obtain ⟨e₀, e₁, e₂, e₃⟩ := star_entry_relations g
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjEntries, Matrix.map_apply]
  · exact e₀
  · exact e₂
  · exact e₁
  · exact e₃
theorem symplecticUnit_inv : symplecticUnit⁻¹ = !![0, -1; 1, 0] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symplecticUnit, Matrix.mul_apply, Fin.sum_univ_two]
theorem symplecticUnit_mem : symplecticUnit ∈ specialUnitary := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symplecticUnit, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  · simp [symplecticUnit, Matrix.det_fin_two]
theorem fullTrace_eq (g : specialUnitary) :
    fullTrace (g : ComplexMatrix2) = (g : ComplexMatrix2) 0 0 + star ((g : ComplexMatrix2) 0 0) := by
  rw [(star_entry_relations g).1]
  simp [fullTrace, Matrix.trace, Fin.sum_univ_two]
theorem fullTrace_im (g : specialUnitary) : (fullTrace (g : ComplexMatrix2)).im = 0 := by
  rw [fullTrace_eq]
  simp
theorem ofReal_re_fullTrace (g : specialUnitary) :
    (((fullTrace (g : ComplexMatrix2)).re : ℝ) : ℂ) = fullTrace (g : ComplexMatrix2) :=
  Complex.ext (by simp) (by simp [fullTrace_im])
theorem fullTrace_inv (g : specialUnitary) :
    fullTrace ((g⁻¹ : specialUnitary) : ComplexMatrix2) = fullTrace (g : ComplexMatrix2) := by apply _root_.YangMills.Construction.ChessboardTori.TransferSetup.fullTrace_inv <;> assumption
theorem norm_fullTrace_le (g : specialUnitary) : ‖fullTrace (g : ComplexMatrix2)‖ ≤ 2 := by
  have hcorner : ‖(g : ComplexMatrix2) 0 0‖ ≤ 1 :=
    entry_norm_bound_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup g.2) 0 0
  rw [fullTrace_eq]
  calc ‖(g : ComplexMatrix2) 0 0 + star ((g : ComplexMatrix2) 0 0)‖
      ≤ ‖(g : ComplexMatrix2) 0 0‖ + ‖star ((g : ComplexMatrix2) 0 0)‖ := norm_add_le _ _
    _ = ‖(g : ComplexMatrix2) 0 0‖ + ‖(g : ComplexMatrix2) 0 0‖ := by rw [norm_star]
    _ ≤ 2 := by linarith
theorem re_fullTrace_mem_Icc (g : specialUnitary) :
    -2 ≤ (fullTrace (g : ComplexMatrix2)).re ∧ (fullTrace (g : ComplexMatrix2)).re ≤ 2 := by
  have habs := (Complex.abs_re_le_norm (fullTrace (g : ComplexMatrix2))).trans (norm_fullTrace_le g)
  exact abs_le.mp habs
theorem singleBondWeight_eq_exp (β : ℝ) (g : specialUnitary) : singleBondWeight β g =
    ((Real.exp (-β * (1 - (1 / 2) * (fullTrace (g : ComplexMatrix2)).re)) : ℝ) : ℂ) := by
  rw [singleBondWeight, ← ofReal_re_fullTrace g]
  push_cast
  simp
theorem fullTrace_conj (h g : specialUnitary) :
    fullTrace ((h * g * h⁻¹ : specialUnitary) : ComplexMatrix2) = fullTrace (g : ComplexMatrix2) := by
  have hcoe : ((h * g * h⁻¹ : specialUnitary) : ComplexMatrix2) =
      (h : ComplexMatrix2) * (g : ComplexMatrix2) * ((h⁻¹ : specialUnitary) : ComplexMatrix2) := rfl
  have hcancel : ((h⁻¹ : specialUnitary) : ComplexMatrix2) * (h : ComplexMatrix2) = 1 := by
    have : ((h⁻¹ * h : specialUnitary) : ComplexMatrix2) = 1 := by rw [inv_mul_cancel]; rfl
    exact this
  rw [hcoe, fullTrace, Matrix.trace_mul_comm, ← mul_assoc, hcancel, one_mul]
theorem specialUnitaryTraceFacts_holds : SpecialUnitaryTraceFacts := by
  refine ⟨symplecticUnit_mem, fun g => ?_⟩
  obtain ⟨e₀, e₁, e₂, e₃⟩ := star_entry_relations g
  refine ⟨e₀.symm, ?_, ?_, ?_, ?_, fullTrace_im g, fullTrace_inv g, norm_fullTrace_le g⟩
  · rw [e₂, neg_neg]
  · intro i j
    rw [coe_inv_eq]
    fin_cases i <;> fin_cases j
    · exact ⟨1, 1, Or.inl (by simp)⟩
    · exact ⟨0, 1, Or.inr (by simp)⟩
    · exact ⟨1, 0, Or.inr (by simp)⟩
    · exact ⟨0, 0, Or.inl (by simp)⟩
  · intro i j
    rw [conjEntries_eq]
    fin_cases i <;> fin_cases j
    · exact ⟨1, 1, Or.inl (by simp)⟩
    · exact ⟨1, 0, Or.inr (by simp)⟩
    · exact ⟨0, 1, Or.inr (by simp)⟩
    · exact ⟨0, 0, Or.inl (by simp)⟩
  · rw [conjEntries_eq, symplecticUnit_inv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symplecticUnit, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
theorem singleBondWeight_realClassFunction (β : ℝ) : SingleBondWeightRealClassFunction β := by
  refine ⟨fun g => ?_, ?_, fun h g => ?_, fun g => ?_⟩
  · rw [singleBondWeight_eq_exp]
    exact Complex.ofReal_im _
  · have hcont : Continuous fun g : specialUnitary => singleBondWeight β g := by
      unfold singleBondWeight
      fun_prop
    exact Complex.continuous_re.comp hcont
  · simp only [singleBondWeight, fullTrace_conj]
  · simp only [singleBondWeight, fullTrace_inv]
theorem singleBondWeight_bounds {β : ℝ} (hβ : 0 < β) : SingleBondWeightBounds β := by
  intro g
  obtain ⟨hlow, hupp⟩ := re_fullTrace_mem_Icc g
  rw [singleBondWeight_eq_exp, Complex.ofReal_re]
  constructor
  · apply Real.exp_le_exp.mpr
    nlinarith
  · apply Real.exp_le_one_iff.mpr
    nlinarith
theorem faceFactor_eq_singleBondWeight (hfaces : PlaquetteProperties 1) (β : ℝ) :
    FaceFactorEqSingleBondWeight β := by
  refine ⟨fun p U => ?_, fun p U l₀ l₁ l₂ l₃ hcorner h₀ h₁ h₂ h₃ => ?_⟩
  · rw [singleBondWeight_eq_exp, faceEnergy]
  · have hface := hfaces.2.1 p U l₀ l₁ l₂ l₃ hcorner h₀ h₁ h₂ h₃
    rw [singleBondWeight_eq_exp, faceEnergy, hface]
end SUTwoTrace
theorem traceAndSingleBondWeight_holds (hE : ElementaryLatticeFacts) :
    TraceAndSingleBondWeight :=
  ⟨SUTwoTrace.specialUnitaryTraceFacts_holds, fun β hβ =>
    ⟨SUTwoTrace.singleBondWeight_realClassFunction β,
      SUTwoTrace.singleBondWeight_bounds hβ,
      SUTwoTrace.faceFactor_eq_singleBondWeight (hE 1 β one_pos hβ).2.1 β⟩⟩
end YangMills.Construction.InfiniteLattice
end
