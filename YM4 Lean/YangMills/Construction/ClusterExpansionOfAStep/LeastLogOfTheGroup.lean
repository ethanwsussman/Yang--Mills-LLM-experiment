import YangMills.Construction.ColdChainAtEveryLevel.SecondDifferenceOfAPlaquette
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.QuaternionLog
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.GaugeFixing
instance : SecondCountableTopology UnitQuaternion := TopologicalSpace.Subtype.secondCountableTopology _
theorem arccos_re_eq_norm_minimalLog_and_lt_pi (g : UnitQuaternion) (hg : g ≠ -1) :
    Real.arccos (g : ℍ[ℝ]).re = ‖((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])‖ ∧
      ‖((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])‖ < Real.pi := by
  obtain ⟨hexp, -⟩ := minimalLog_spec g
  set X := minimalLog g with hX
  have hle := norm_minimalLog_le_pi g
  rw [← hX] at hle
  have hcoe := congrArg (fun g : UnitQuaternion => (g : ℍ[ℝ])) hexp
  simp only [coe_expUnit_eq] at hcoe
  have hre : (g : ℍ[ℝ]).re = Real.cos ‖(X : ℍ[ℝ])‖ := by
    rw [← hcoe]
    have hX0 : (X : ℍ[ℝ]).re = 0 := X.2
    simp [hX0]
  refine ⟨by rw [hre]; exact Real.arccos_cos (norm_nonneg _) hle, lt_of_le_of_ne hle fun hpi => hg ?_⟩
  have hneg : (g : ℍ[ℝ]) = -1 := by
    rw [← hcoe, hpi]
    simp
  exact Subtype.ext hneg
theorem coe_minimalLog_eq_smul_im (g : UnitQuaternion) (hg : g ≠ -1) :
    ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]) =
      (1 / Real.sinc (Real.arccos (g : ℍ[ℝ]).re)) • (g : ℍ[ℝ]).im := by
  obtain ⟨hexp, -⟩ := minimalLog_spec g
  set X := minimalLog g with hX
  have hle := norm_minimalLog_le_pi g
  rw [← hX] at hle
  have hcoe := congrArg (fun g : UnitQuaternion => (g : ℍ[ℝ])) hexp
  simp only [coe_expUnit_eq] at hcoe
  have hre : (g : ℍ[ℝ]).re = Real.cos ‖(X : ℍ[ℝ])‖ := by
    rw [← hcoe]
    have hX0 : (X : ℍ[ℝ]).re = 0 := X.2
    simp [hX0]
  have hangle : Real.arccos (g : ℍ[ℝ]).re = ‖(X : ℍ[ℝ])‖ := by
    rw [hre]
    exact Real.arccos_cos (norm_nonneg _) hle
  have him : (g : ℍ[ℝ]).im = (Real.sin ‖(X : ℍ[ℝ])‖ / ‖(X : ℍ[ℝ])‖) • (X : ℍ[ℝ]) := by
    rw [← hcoe]
    have hXim : (X : ℍ[ℝ]).im = (X : ℍ[ℝ]) := by
      ext <;> simp [show (X : ℍ[ℝ]).re = 0 from X.2]
    simp [hXim]
  rw [hangle, him]
  by_cases hzero : ‖(X : ℍ[ℝ])‖ = 0
  · rw [norm_eq_zero.mp hzero]
    simp
  · have hpos : 0 < ‖(X : ℍ[ℝ])‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    have hlt : ‖(X : ℍ[ℝ])‖ < Real.pi := by
      refine lt_of_le_of_ne hle fun hpi => hg ?_
      have hneg : (g : ℍ[ℝ]) = -1 := by
        rw [← hcoe, hpi]
        simp
      exact Subtype.ext hneg
    have hsin := Real.sin_pos_of_pos_of_lt_pi hpos hlt
    rw [Real.sinc_of_ne_zero hzero, smul_smul]
    have hone : 1 / (Real.sin ‖(X : ℍ[ℝ])‖ / ‖(X : ℍ[ℝ])‖) * (Real.sin ‖(X : ℍ[ℝ])‖ / ‖(X : ℍ[ℝ])‖) = 1 := by
      field_simp
    rw [hone, one_smul]
theorem continuousOn_coe_minimalLog :
    ContinuousOn (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]))
      {(-1 : UnitQuaternion)}ᶜ := by
  have hF : ContinuousOn
      (fun g : UnitQuaternion => (1 / Real.sinc (Real.arccos (g : ℍ[ℝ]).re)) • (g : ℍ[ℝ]).im)
      {(-1 : UnitQuaternion)}ᶜ := by
    have hsinc : Continuous fun g : UnitQuaternion => Real.sinc (Real.arccos (g : ℍ[ℝ]).re) :=
      Real.continuous_sinc.comp
        (Real.continuous_arccos.comp (Quaternion.continuous_re.comp continuous_subtype_val))
    have him : Continuous fun g : UnitQuaternion => (g : ℍ[ℝ]).im :=
      Quaternion.continuous_im.comp continuous_subtype_val
    have hinv : ContinuousOn (fun g : UnitQuaternion => 1 / Real.sinc (Real.arccos (g : ℍ[ℝ]).re))
        {(-1 : UnitQuaternion)}ᶜ := by
      refine ContinuousOn.div continuousOn_const hsinc.continuousOn fun g hg => ?_
      obtain ⟨hangle, hlt⟩ := arccos_re_eq_norm_minimalLog_and_lt_pi g hg
      rw [hangle]
      by_cases hzero : ‖((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])‖ = 0
      · rw [hzero]
        simp
      · have hpos : 0 < ‖((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])‖ :=
          lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
        rw [Real.sinc_of_ne_zero hzero]
        exact (div_pos (Real.sin_pos_of_pos_of_lt_pi hpos hlt) hpos).ne'
    exact hinv.smul him.continuousOn
  exact hF.congr fun g hg => coe_minimalLog_eq_smul_im g hg
theorem norm_minimalLog_neg_one :
    ‖((minimalLog (-1 : UnitQuaternion) : imaginaryQuaternions) : ℍ[ℝ])‖ = Real.pi := by
  obtain ⟨hexp, -⟩ := minimalLog_spec (-1 : UnitQuaternion)
  have hcos : Real.cos ‖((minimalLog (-1 : UnitQuaternion) : imaginaryQuaternions) : ℍ[ℝ])‖ =
      Real.cos Real.pi := by
    rw [← re_coe_expUnit, hexp, Real.cos_pi]
    show ((-1 : ℍ[ℝ])).re = -1
    simp
  exact Real.injOn_cos ⟨norm_nonneg _, norm_minimalLog_le_pi _⟩ ⟨Real.pi_pos.le, le_rfl⟩ hcos
theorem norm_conj_unit (u : UnitQuaternion) (a : ℍ[ℝ]) :
    ‖(u : ℍ[ℝ]) * a * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖a‖ := by apply _root_.YangMills.Construction.PlaquetteSecondDifference.norm_conj <;> assumption
theorem re_conj_unit (u : UnitQuaternion) (q : ℍ[ℝ]) :
    ((u : ℍ[ℝ]) * q * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = q.re := by apply _root_.YangMills.Construction.GaugedCriticality.re_conj_unit <;> assumption
theorem coe_mul_coe_inv_unit (u : UnitQuaternion) :
    (u : ℍ[ℝ]) * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_mul_coe_inv <;> assumption
theorem im_conj_unit (u : UnitQuaternion) (q : ℍ[ℝ]) :
    ((u : ℍ[ℝ]) * q * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])).im =
      (u : ℍ[ℝ]) * q.im * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  set t := (u : ℍ[ℝ]) * q.im * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) with ht
  have htre : t.re = 0 := by
    rw [ht, re_conj_unit]
    simp
  have hsplit : (u : ℍ[ℝ]) * q * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) = ((q.re : ℝ) : ℍ[ℝ]) + t := by
    conv_lhs => rw [← Quaternion.re_add_im q]
    rw [mul_add, add_mul]
    congr 1
    rw [← Quaternion.coe_commutes, mul_assoc, coe_mul_coe_inv_unit, mul_one]
  rw [hsplit]
  ext <;> simp [htre]
theorem coe_minimalLog_conj (u γ : UnitQuaternion) (hγ : γ ≠ -1) :
    ((minimalLog (u * γ * u⁻¹) : imaginaryQuaternions) : ℍ[ℝ]) =
      (u : ℍ[ℝ]) * ((minimalLog γ : imaginaryQuaternions) : ℍ[ℝ]) * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  have hne : u * γ * u⁻¹ ≠ -1 := by
    intro h
    apply hγ
    have hγeq : γ = u⁻¹ * (-1) * u := by
      rw [← h]
      group
    rw [hγeq]
    simp
  rw [coe_minimalLog_eq_smul_im _ hne, coe_minimalLog_eq_smul_im _ hγ]
  have hcoe : (((u * γ * u⁻¹ : UnitQuaternion)) : ℍ[ℝ]) =
      (u : ℍ[ℝ]) * (γ : ℍ[ℝ]) * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    simp only [Submonoid.coe_mul]
  rw [hcoe, re_conj_unit, im_conj_unit, mul_smul_comm, smul_mul_assoc]
end YangMills.Construction.QuaternionLog
end
