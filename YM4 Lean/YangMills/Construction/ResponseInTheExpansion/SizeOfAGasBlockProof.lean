import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ResponseInTheExpansion.ResponseOfTheGas
import YangMills.Construction.ResponseInTheExpansion.SizeOfAGasBlock
import YangMills.Construction.ResponseInTheExpansion.WeightsNearTheirMeans
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages BlockOffsets StepSettings WeightedResponses
theorem gasBlockMeanBound (hGas : GasResponseBounds) (hNear : WeightsCloseToBlockMeans) :
    gasBlockMeanBoundStatement := by
  obtain ⟨r₁, p₁, g₁⟩ := hGas
  refine ⟨r₁, p₁, fun T hT hrt K => ?_⟩
  obtain ⟨y₁, G₁⟩ := g₁ T hT hrt K
  refine ⟨max y₁ T.floorMin, fun y hy R A hK hAt => ?_⟩
  have hy₁ : y₁ ≤ y := (le_max_left _ _).trans hy
  have hyMin : T.floorMin ≤ y := (le_max_right _ _).trans hy
  have hR := hAt.onFamily
  have hadm : R.params.Admissible := hR.params_eq ▸ hT.fits y hyMin
  have hodd := hadm.L_odd
  obtain ⟨c₀, -⟩ := G₁ y hy₁ R A hK hAt
  intro n _ G Y h hG
  obtain ⟨c₁, c₂⟩ := c₀ n G hG
  set e := Real.exp (-(6 * T.gasRate * R.coupling)) with he
  have he₀ : 0 < e := Real.exp_pos _
  set S := weightNorm R.params.side R.depth h with hS
  have hS₀ : 0 ≤ S := le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
  have hcard : (∑ _o ∈ centredCube R.params.side, (1 : ℝ)) = (R.params.side : ℝ) ^ 4 := by
    rw [Finset.sum_const, card_centredCube hodd, nsmul_eq_mul]
    push_cast
    ring
  have hsum : |∑ o ∈ centredCube R.params.side, G.expectation ∅
        (fun σ => chartResponse A (configSetting G σ) (fineSite R.params.side Y 0 o) h)| ≤
      ((R.params.side : ℝ) ^ 4 * (A.responseParams.C₀ + e) +
        ∑ o ∈ centredCube R.params.side, recordedSiteScore A G (fineSite R.params.side Y 0 o)) * S := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun o _ => (c₁ _ h).2).trans (le_of_eq ?_))
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, add_right_comm]
    simp only [Finset.sum_const, nsmul_eq_mul, card_centredCube hodd]
    push_cast
    ring
  have hbonds : |∑ i : Fin 4, (G.expectation ∅ (fun σ => chartBondScore (configSetting G σ) (Y, i)) +
      G.expectation ∅ (fun σ => chartBondScore (configSetting G σ) (Y - TorusFields.unitStep n i, i)))| ≤
      8 * (2 + e) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have each : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
        |G.expectation ∅ (fun σ => chartBondScore (configSetting G σ) (Y, i)) +
          G.expectation ∅ (fun σ => chartBondScore (configSetting G σ) (Y - TorusFields.unitStep n i, i))| ≤
          2 * (2 + e) := by
      intro i _
      have b₁ := (c₂ (Y, i)).2
      have b₂ := (c₂ (Y - TorusFields.unitStep n i, i)).2
      refine (abs_add_le _ _).trans ?_
      linarith
    refine (Finset.sum_le_sum each).trans (le_of_eq ?_)
    simp
    ring
  have hsup : |blockMean R.params.side (R.depth + 1) n Y h| ≤ S :=
    ((hNear R.params.side hodd (R.depth + 1) n Y).1 h).trans (le_max_left _ _)
  have hcoeff : |A.coeff| ≤ 2 := hAt.admissible.abs_coeff_le
  have hcoup := hadm.a_ge
  have hterm : |R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h| ≤
      R.params.coupling * S := by
    rw [abs_mul, abs_mul, abs_div, abs_of_pos (by linarith : (0 : ℝ) < R.params.coupling)]
    have htwo : |(2 : ℝ)| = 2 := by norm_num
    rw [htwo]
    calc R.params.coupling / 2 * |A.coeff| * |blockMean R.params.side (R.depth + 1) n Y h|
          ≤ R.params.coupling / 2 * 2 * S := by
          have : 0 ≤ R.params.coupling / 2 := by linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_left hcoeff this) hsup (abs_nonneg _) (by positivity)
      _ = R.params.coupling * S := by ring
  unfold gasBlockMean
  rw [sum_sitesInBlocks hodd Y]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  calc _ ≤ ((R.params.side : ℝ) ^ 4 * (A.responseParams.C₀ + e) +
        ∑ o ∈ centredCube R.params.side, recordedSiteScore A G (fineSite R.params.side Y 0 o)) * S +
        R.params.coupling * S * (8 * (2 + e)) :=
        add_le_add hsum (mul_le_mul hterm hbonds (abs_nonneg _) (by positivity))
    _ = _ := by ring
end YangMills.Construction.ResponseInTheExpansion
end
