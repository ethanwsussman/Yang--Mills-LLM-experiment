import YangMills.Construction.ClusterExpansionOfAStep.CumulantsOfTheKernelsInMassProofForm
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ClusterExpansionOfAStep.TheKernelOfABond
import YangMills.Construction.ColdChainAtEveryLevel.FactsOfTheLogarithm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open BlockAverages LumpContours TorusFields
theorem continuous_re_unitQuaternion :
    Continuous fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ]).re :=
  Quaternion.continuous_re.comp continuous_subtype_val
theorem integrable_of_continuous_unitQuaternion {f : UnitQuaternion → ℝ} (hf : Continuous f) :
    Integrable f haarUnit :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
theorem re_unitQuaternion_le_one (g : UnitQuaternion) : ((g : UnitQuaternion) : ℍ[ℝ]).re ≤ 1 := by apply _root_.YangMills.Construction.BlockAverages.re_coe_le_one <;> assumption
theorem partitionFn_pos (s : ℝ) : 0 < partitionFn s := by apply _root_.YangMills.Construction.TorusLumps.KernelMass.zero_lt_partitionFn <;> assumption
def negOneUnit : UnitQuaternion := ⟨-1, by
  rw [Unitary.mem_iff]
  simp⟩
theorem integral_re_eq_zero : ∫ g : UnitQuaternion, ((g : UnitQuaternion) : ℍ[ℝ]).re ∂haarUnit = 0 := by
  have hinv := integral_mul_left_eq_self (μ := haarUnit)
    (fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ]).re) negOneUnit
  have hneg : ∀ g : UnitQuaternion,
      ((negOneUnit * g : UnitQuaternion) : ℍ[ℝ]).re = -((g : UnitQuaternion) : ℍ[ℝ]).re := by
    intro g
    simp [negOneUnit]
  simp only [hneg, integral_neg] at hinv
  linarith
theorem one_le_partitionFn (s : ℝ) : 1 ≤ partitionFn s := by
  have hint := integrable_of_continuous_unitQuaternion
    (f := fun g : UnitQuaternion => s * ((g : UnitQuaternion) : ℍ[ℝ]).re + 1)
    ((continuous_const.mul continuous_re_unitQuaternion).add continuous_const)
  have hle : ∫ g : UnitQuaternion, (s * ((g : UnitQuaternion) : ℍ[ℝ]).re + 1) ∂haarUnit ≤
      partitionFn s := by
    refine integral_mono hint
      (integrable_of_continuous_unitQuaternion
        (Real.continuous_exp.comp (continuous_const.mul continuous_re_unitQuaternion))) fun g => ?_
    exact Real.add_one_le_exp _
  have hcalc : ∫ g : UnitQuaternion, (s * ((g : UnitQuaternion) : ℍ[ℝ]).re + 1) ∂haarUnit = 1 := by
    have hlin : Integrable (fun g : UnitQuaternion => s * ((g : UnitQuaternion) : ℍ[ℝ]).re) haarUnit :=
      integrable_of_continuous_unitQuaternion (continuous_const.mul continuous_re_unitQuaternion)
    rw [integral_add hlin (integrable_const (1 : ℝ)), integral_const_mul, integral_re_eq_zero]
    simp
  linarith
theorem partitionFn_le_exp {s : ℝ} (hs : 0 ≤ s) : partitionFn s ≤ Real.exp s := by
  have hbound : partitionFn s ≤ ∫ _ : UnitQuaternion, Real.exp s ∂haarUnit := by
    refine integral_mono (integrable_of_continuous_unitQuaternion
        (Real.continuous_exp.comp (continuous_const.mul continuous_re_unitQuaternion)))
      (integrable_const _) fun g => ?_
    exact Real.exp_le_exp.mpr (by nlinarith [re_unitQuaternion_le_one g])
  simpa using hbound
theorem logPartitionGap_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ logPartitionGap s := by
  unfold logPartitionGap
  have hlog := Real.log_le_log (partitionFn_pos s) (partitionFn_le_exp hs)
  rw [Real.log_exp] at hlog
  linarith
theorem integral_exp_re_mul_inv (q : ℍ[ℝ]) (t : ℝ) :
    ∫ g : UnitQuaternion, Real.exp (t * (q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) ∂haarUnit =
      partitionFn (t * ‖q‖) := by
  by_cases hq : q = 0
  · subst hq
    simp [partitionFn]
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  let u : UnitQuaternion := ⟨(‖q‖⁻¹ : ℝ) • q, by
    rw [Unitary.mem_iff]
    constructor
    · have hprod : star ((‖q‖⁻¹ : ℝ) • q) * ((‖q‖⁻¹ : ℝ) • q) =
          (‖q‖⁻¹ * ‖q‖⁻¹ : ℝ) • (star q * q) := by
        ext <;> simp <;> ring
      rw [hprod, Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self]
      ext <;> simp <;> field_simp
    · have hprod : ((‖q‖⁻¹ : ℝ) • q) * star ((‖q‖⁻¹ : ℝ) • q) =
          (‖q‖⁻¹ * ‖q‖⁻¹ : ℝ) • (q * star q) := by
        ext <;> simp <;> ring
      rw [hprod, Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self]
      ext <;> simp <;> field_simp⟩
  have hqu : q = (‖q‖ : ℝ) • (u : ℍ[ℝ]) := by
    show q = (‖q‖ : ℝ) • ((‖q‖⁻¹ : ℝ) • q)
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hre : ∀ g : UnitQuaternion,
      (q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = ‖q‖ * ((u⁻¹ * g : UnitQuaternion) : ℍ[ℝ]).re := by
    intro g
    have hcoe : ((u⁻¹ * g : UnitQuaternion) : ℍ[ℝ]) = star (u : ℍ[ℝ]) * (g : ℍ[ℝ]) := by
      rw [Submonoid.coe_mul, coe_inv_unitQuaternion]
    rw [hcoe, coe_inv_unitQuaternion]
    conv_lhs => rw [hqu]
    simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
      Quaternion.imK_star, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
      Quaternion.imK_smul, smul_eq_mul]
    ring
  have htrans := integral_mul_left_eq_self (μ := haarUnit)
    (fun g : UnitQuaternion => Real.exp (t * ‖q‖ * ((g : UnitQuaternion) : ℍ[ℝ]).re)) u⁻¹
  simp only [hre]
  unfold partitionFn
  rw [← htrans]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [mul_assoc]
theorem bondKernelProperties_holds : BondKernelProperties := by
  refine ⟨fun s hs => ⟨one_le_partitionFn s, logPartitionGap_nonneg hs⟩, fun ℓ x n W V b c => ⟨?_, ?_, ?_⟩⟩
  · unfold bondKernel
    exact div_pos (Real.exp_pos _) (partitionFn_pos _)
  · unfold bondKernel contourFit logPartitionGap
    simp only
    rw [Real.log_div (Real.exp_pos _).ne' (partitionFn_pos _).ne', Real.log_exp]
    ring
  · unfold bondKernel
    simp only
    have hV : ∀ g : UnitQuaternion, updateBond V c g c.1 c.2 = g := by
      intro g
      simp [updateBond]
    simp only [hV]
    rw [integral_div, integral_exp_re_mul_inv]
    exact div_self (partitionFn_pos _).ne'
end YangMills.Construction.TorusLumps
end
