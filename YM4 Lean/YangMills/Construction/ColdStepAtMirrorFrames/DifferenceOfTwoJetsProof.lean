import YangMills.Construction.ColdStepAtMirrorFrames.DifferenceOfTwoJets
import YangMills.Construction.ColdStepAtMirrorFrames.JetOfAFunctionOfAFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
namespace JetDifferenceLemmas
variable {F : BlockFrame}
theorem sum_singleBondForm' {j : ℕ} {B : Finset (F.Site j × Fin 4)} (Z : ↥B → imaginaryQuaternions) :
    ∑ b, singleBondForm b (Z b) = Z := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.sum_singleBondForm <;> assumption
theorem singleBondForm_smul' {j : ℕ} {B : Finset (F.Site j × Fin 4)} (b : ↥B) (r : ℝ) (X : imaginaryQuaternions) :
    singleBondForm b (r • X) = r • singleBondForm b X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.singleBondForm_smul <;> assumption
theorem singleBondForm_zero' {j : ℕ} {B : Finset (F.Site j × Fin 4)} (b : ↥B) :
    singleBondForm b (0 : imaginaryQuaternions) = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.singleBondForm_zero <;> assumption
end JetDifferenceLemmas
open JetDifferenceLemmas
theorem jetDifferenceBound_of_formCompositionJet (hjet : FormCompositionJet) : JetDifferenceBound := by
  intro E _ _ F j B G G' W W' k e hG hG' hk he0 he Z
  classical
  obtain ⟨-, hE, -⟩ := hjet E F j B G W hG
  obtain ⟨-, hE', -⟩ := hjet E F j B G' W' hG'
  let m := iteratedFDeriv ℝ k (formComposition B G W) 0 - iteratedFDeriv ℝ k (formComposition B G' W') 0
  have hm : ∀ Z', iteratedFDeriv ℝ k (formComposition B G W) 0 Z' -
      iteratedFDeriv ℝ k (formComposition B G' W') 0 Z' = m Z' :=
    fun Z' => rfl
  rw [hm]
  have hZ : Z = fun l => ∑ b, singleBondForm b (Z l b) := by
    funext l
    rw [sum_singleBondForm']
  have hsum : m Z = ∑ c : Fin k → ↥B, m (fun l => singleBondForm (c l) (Z l (c l))) := by
    conv_lhs => rw [hZ]
    exact m.toMultilinearMap.map_sum (fun l b => singleBondForm b (Z l b))
  rw [hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  have hec : 0 ≤ e c := he0 c
  by_cases hz : ∃ l, Z l (c l) = 0
  · obtain ⟨l, hl⟩ := hz
    have h0 : m (fun l => singleBondForm (c l) (Z l (c l))) = 0 :=
      m.map_coord_zero l (by simp only [hl, singleBondForm_zero'])
    rw [h0, norm_zero]
    exact mul_nonneg hec (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  · push Not at hz
    let X : Fin k → imaginaryQuaternions := fun l => ‖Z l (c l)‖⁻¹ • Z l (c l)
    have hX : AreUnitVectors X := fun l => by
      simp only [X, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hz l))
    have hform : (fun l => singleBondForm (c l) (Z l (c l))) =
        fun l => ‖Z l (c l)‖ • singleBondForm (c l) (X l) := by
      funext l
      rw [← singleBondForm_smul']
      simp only [X, smul_smul]
      rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hz l)), one_smul]
    have hmX : m (fun l => singleBondForm (c l) (X l)) =
        bondDeriv G W (fun l => (c l).1) X - bondDeriv G' W' (fun l => (c l).1) X := by
      rw [← hm, hE k c X hk, hE' k c X hk]
    rw [hform, m.map_smul_univ, hmX, norm_smul, mul_comm]
    have hp : ‖∏ l, ‖Z l (c l)‖‖ = ∏ l, ‖Z l (c l)‖ :=
      Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    rw [hp]
    exact mul_le_mul_of_nonneg_right (he c X hX) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
