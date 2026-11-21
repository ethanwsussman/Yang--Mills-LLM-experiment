import YangMills.Construction.ColdChainAtEveryLevel.AnalyticSharesOfAColdTopProof
import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainOfAColdTop
import YangMills.Construction.ColdChainAtEveryLevel.SizeNearACellOfASplitProof
import YangMills.Construction.ColdChainAtEveryLevel.SizesOfTheMinimalChain
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace MinimalChartSizes
variable {F : BlockFrame}
theorem localNorm_le_add (S : Finset F.Cell) (R : F.FieldChain) (U A B : ChainChart F) (z : F.Cell)
    (hs : ChartEqOnBonds S U (chartSum A B)) :
    localNorm S R U (oneSiteWeights F) z ≤
      localNorm S R A (oneSiteWeights F) z + localNorm S R B (oneSiteWeights F) z := by apply _root_.YangMills.Construction.BlockAverages.SplitChartNearCell.localNorm_le_add <;> assumption
theorem localNorm_le_exp_mul_decayWeights (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (del : ℝ) (hd : 0 ≤ del) (p : F.Site 0) (z : F.Cell) :
    localNorm S R U (oneSiteWeights F) z ≤
      Real.exp (3 * del) * localNorm S R U (decayWeights F del 0 p z) z := by apply _root_.YangMills.Construction.BlockAverages.SplitChartNearCell.localNorm_le_exp_mul_decayWeights <;> assumption
theorem localNorm_le_weightedNorm (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (w : F.SiteWeights) {z : F.Cell} (hz : z ∈ S) : localNorm S R U w z ≤ weightedNorm S R U w := by apply _root_.YangMills.Construction.BlockWeights.localNorm_le_weightedNorm <;> assumption
theorem exp_three_mul_le_two {del : ℝ} (hd : del ≤ 1 / 8) : Real.exp (3 * del) ≤ 2 := by apply _root_.YangMills.Construction.BlockAverages.SplitChartNearCell.exp_three_mul_le_two <;> assumption
theorem rotatedField_zero (V : F.GaugeField F.top) :
    rotatedField (fun _ _ => (0 : imaginaryQuaternions)) V = V := by apply _root_.YangMills.Construction.BlockAverages.AnalyticCellShares.rotatedField_zero <;> assumption
end MinimalChartSizes
open MinimalChartSizes in
theorem minimalChartSizes (hC : coldTopCriticalChainStatement)
    (hV : criticalValueEqMinimalActionStatement) : minimalChartSizesStatement := by
  intro a ha
  obtain ⟨θ, del, Ca, hθ, hθ8, hd, hd8, hCa, L₁, h1⟩ := hC a ha
  obtain ⟨L₂, h2⟩ := hV a θ del Ca ha hθ hθ8 hd hd8 hCa
  refine ⟨θ, del, 2 * Ca, hθ, hθ8, hd, hd8, by positivity, max L₁ L₂, fun L hL hge => ?_⟩
  obtain ⟨rL, sL, CL, hr, hs, hCL, h⟩ := h1 L hL (le_of_max_le_left hge)
  obtain ⟨σ, hσ, h3⟩ := h2 L hL (le_of_max_le_right hge) CL hCL
  refine ⟨2 * CL, min (min sL σ) (Ca / CL), by positivity,
    lt_min (lt_min hs hσ) (div_pos hCa hCL), ?_⟩
  intro F m S hFL hamb hm hreg r V hr0 hrle hcold
  have hrs : r ≤ sL := hrle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrσ : r ≤ σ := hrle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrc : r ≤ Ca / CL := hrle.trans (min_le_right _ _)
  obtain ⟨U, hin, _, hcr, _, hsplit, _, _, hq, hcm, hmis⟩ := h F m S hFL hamb hm hreg r V hr0 hrs hcold
  subst hFL
  have hIs : IsCriticalChainOverTop a θ del Ca CL r S V
      (rotatedField (fun _ _ => (0 : imaginaryQuaternions)) V) U := by
    rw [rotatedField_zero]
    exact ⟨hcr, hsplit, hq, hcm, hmis⟩
  have hval := (h3 F m S rfl hamb hm hreg r V (fun _ _ => (0 : imaginaryQuaternions)) hr0 hrσ hcold
    (fun _ _ => by simpa using hr0.le) U hIs).1
  rw [rotatedField_zero] at hval
  obtain ⟨Ul, Ur, hsame, hbd⟩ := hsplit
  have hnear : ∀ z ∈ S, localNorm S (referenceFieldChain S V) U (oneSiteWeights F) z ≤
      2 * Ca * r + 2 * CL * r ^ 2 := by
    intro z hz
    have hb := hbd 0 z 0 (Or.inr rfl)
    have e1 := localNorm_le_exp_mul_decayWeights S (referenceFieldChain S V) Ul del hd.le 0 z
    have e2 := localNorm_le_exp_mul_decayWeights S (referenceFieldChain S V) Ur del hd.le 0 z
    have f1 := (localNorm_le_weightedNorm S (referenceFieldChain S V) Ul
      (decayWeights F del 0 0 z) hz).trans hb.1
    have f2 := (localNorm_le_weightedNorm S (referenceFieldChain S V) Ur
      (decayWeights F del 0 0 z) hz).trans hb.2
    have hE := exp_three_mul_le_two hd8
    have hE0 : 0 ≤ Real.exp (3 * del) := (Real.exp_pos _).le
    have g1 : Real.exp (3 * del) *
        localNorm S (referenceFieldChain S V) Ul (decayWeights F del 0 0 z) z ≤ 2 * (Ca * r) :=
      mul_le_mul hE f1 (Real.sqrt_nonneg _) (by norm_num)
    have g2 : Real.exp (3 * del) *
        localNorm S (referenceFieldChain S V) Ur (decayWeights F del 0 0 z) z ≤ 2 * (CL * r ^ 2) :=
      mul_le_mul hE f2 (Real.sqrt_nonneg _) (by norm_num)
    have := localNorm_le_add S (referenceFieldChain S V) U Ul Ur z hsame
    linarith
  refine ⟨U, hin, hcr, hval.symm, ⟨Ul, Ur, hsame, fun p y0 θ' h' => ?_⟩, hnear, ?_⟩
  · have hb := hbd p y0 θ' h'
    constructor
    · refine hb.1.trans ?_
      nlinarith [mul_pos hCa hr0]
    · refine hb.2.trans ?_
      nlinarith [mul_pos hCL (pow_pos hr0 2)]
  · intro z hz
    refine (hnear z hz).trans ?_
    have h5 : CL * r ≤ Ca := by
      rw [le_div_iff₀ hCL] at hrc
      linarith
    have : CL * r ^ 2 ≤ Ca * r := by
      calc CL * r ^ 2 = (CL * r) * r := by ring
        _ ≤ Ca * r := mul_le_mul_of_nonneg_right h5 hr0.le
    linarith
end YangMills.Construction.BlockAverages
end
