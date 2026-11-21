import YangMills.Construction.Matrices.CompositesOfDifferentiableMapsOnPowersOfGProof
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Towers.ChartAtTheTrivialConfigurationDefs
import Mathlib
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction
namespace IdentityExpChart
def ChartAndBallImages.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] [Nonempty σ], ExpChartAtOne σ ∧ ExpImagesOfBalls σ
end IdentityExpChart
end YangMills.Construction
end

open Set
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction
open Matrices Matrices.GroupLieProduct Matrices.PowerExpCharts
namespace IdentityExpChart
namespace BallImages
variable {σ : Type}
theorem mem_lieBall_iff [Finite σ] [Nonempty σ] (ε : ℝ) (Y : σ → ComplexMatrix2.LieElement) :
    Y ∈ lieBall σ ε ↔ ∀ s, ComplexMatrix2.operatorNorm (Y s).toMatrix < ε := by
  change (⨆ s, ComplexMatrix2.operatorNorm (toMatrices Y s)) < ε ↔ _
  constructor
  · intro h s
    exact lt_of_le_of_lt
      (le_ciSup (f := fun s => ComplexMatrix2.operatorNorm (toMatrices Y s))
        (Set.finite_range _).bddAbove s) h
  · intro h
    obtain ⟨s, hs⟩ := exists_eq_ciSup_of_finite
      (f := fun s => ComplexMatrix2.operatorNorm (toMatrices Y s))
    rw [← hs]
    exact h s
theorem smallBall_eq_lieBall [Finite σ] [Nonempty σ] (ε : ℝ) :
    smallBall σ ε = lieBall σ ε := by
  ext Y
  exact (mem_lieBall_iff ε Y).symm
theorem oneFamily_mem : oneFamily σ ∈ specialUnitaryPower σ :=
  fun _ => ComplexMatrix2.specialUnitary.one_mem
theorem exp_half_le : Real.exp (1 / 2) ≤ 19 / 10 := by apply _root_.YangMills.Construction.Matrices.specialUnitaryPower.Composition.exp_half_le_nineteen_tenths <;> assumption
theorem logChart_oneFamily :
    PowerExpCharts.logChart (oneFamily σ) = logFamily (σ := σ) := by
  funext X s
  simp [PowerExpCharts.logChart, logFamily, oneFamily]
theorem toLieFamily_toMatrices (Y : σ → ComplexMatrix2.LieElement) :
    toLieFamily (toMatrices Y) = Y := by
  funext s
  unfold toLieFamily
  exact dif_pos (show toMatrices Y s ∈ ComplexMatrix2.hermitianTraceless from (Y s).2)
section Chart
variable [Fintype σ]
theorem expChartI_oneFamily (hc : PowerCharts σ) (Y : σ → ComplexMatrix2.LieElement) :
    expChartI (oneFamily σ) Y = expFamily Y := by
  rw [((hc _ oneFamily_mem).2.1 Y).2.1]
  funext s
  simp [expFamily, oneFamily]
theorem expFamily_mem (hc : PowerCharts σ) (Y : σ → ComplexMatrix2.LieElement) :
    expFamily Y ∈ specialUnitaryPower σ := by
  rw [← expChartI_oneFamily hc]
  exact ((hc _ oneFamily_mem).2.1 Y).2.2
theorem isEmbedding_toMatrix : Topology.IsEmbedding ComplexMatrix2.LieElement.toMatrix :=
  (LinearMap.isClosedEmbedding_of_injective
    (f := (⟨⟨ComplexMatrix2.LieElement.toMatrix, fun _ _ => rfl⟩, fun _ _ => rfl⟩ :
      ComplexMatrix2.LieElement →ₗ[ℝ] ComplexMatrix2))
    (LinearMap.ker_eq_bot.mpr fun _ _ h => Subtype.ext h)).isEmbedding
theorem expChartAtOne_holds [Nonempty σ] (hc : PowerCharts σ) : ExpChartAtOne σ := by
  have H := (hc _ oneFamily_mem).2.2 (1 / 2) (by norm_num) exp_half_le
  have e₁ : expChartI (oneFamily σ) = expFamily := funext (expChartI_oneFamily hc)
  rw [e₁, smallBall_eq_lieBall, logChart_oneFamily] at H
  obtain ⟨hinj, hopen, -, hcd, -, hlcd, hsub, hleft, c, ν, hdom, hpar⟩ := H
  have hinv : ∀ Y ∈ lieBall σ (1 / 2), IdentityExpChart.logChart (expFamily Y) = Y := by
    intro Y hY
    unfold IdentityExpChart.logChart
    rw [show logFamily (expFamily Y) = toMatrices Y from hleft Y hY]
    exact toLieFamily_toMatrices Y
  have hmat : ∀ X ∈ expImage σ, toMatrices (IdentityExpChart.logChart X) = logFamily X := by
    rintro X ⟨Y, hY, rfl⟩
    rw [hinv Y hY]
    exact (hleft Y hY).symm
  refine ⟨hinj, hopen, hinv, hmat, hcd.continuousOn, ?_, c, ν, hdom, fun u hu => ?_⟩
  · refine continuousOn_pi.mpr fun s => ?_
    refine isEmbedding_toMatrix.isInducing.continuousOn_iff.mpr ?_
    have hl : ContinuousOn (fun X => logFamily X s) (expImage σ) :=
      (continuous_apply s).comp_continuousOn (hlcd.continuousOn.mono hsub)
    exact hl.congr fun X hX => congrFun (hmat X hX) s
  · exact (hpar u hu).trans (expChartI_oneFamily hc _)
end Chart
section Images
theorem operatorNorm_I_smul (Z : ComplexMatrix2) :
    ComplexMatrix2.operatorNorm (Complex.I • Z) = ComplexMatrix2.operatorNorm Z := by
  simp [ComplexMatrix2.operatorNorm, norm_smul]
theorem half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith
theorem operatorNorm_exp_sub_one (hEL : ComplexMatrix2.ExpLogEstimates)
    {Y : ComplexMatrix2.LieElement} (hY : ComplexMatrix2.operatorNorm Y.toMatrix < 1 / 2)
    (hA : ComplexMatrix2.matExp (Complex.I • Y.toMatrix) ∈ ComplexMatrix2.specialUnitary) :
    ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp (Complex.I • Y.toMatrix) - 1) =
      2 * Real.sin (ComplexMatrix2.operatorNorm Y.toMatrix / 2) := by
  obtain ⟨-, -, -, -, h5, -, -, h8, -, -⟩ := hEL
  have hZ : ComplexMatrix2.operatorNorm (Complex.I • Y.toMatrix) < Real.log 2 := by
    rw [operatorNorm_I_smul]
    exact hY.trans half_lt_log_two
  obtain ⟨hlt, hlog⟩ := h5 _ hZ
  obtain ⟨H, -, hlogH, -, -, hnorm, -⟩ :=
    h8 _ (Matrix.specialUnitaryGroup_le_unitaryGroup hA) hlt
  have hH : H = Y.toMatrix :=
    smul_right_injective ComplexMatrix2 Complex.I_ne_zero (hlogH.symm.trans hlog)
  rw [hnorm, hH]
theorem exists_small_log (hEL : ComplexMatrix2.ExpLogEstimates) {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.specialUnitary) {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 2)
    (hclose : ComplexMatrix2.operatorNorm (A - 1) < 2 * Real.sin (ε / 2)) :
    ∃ Y : ComplexMatrix2.LieElement, ComplexMatrix2.operatorNorm Y.toMatrix < ε ∧
      ComplexMatrix2.matExp (Complex.I • Y.toMatrix) = A := by
  obtain ⟨-, -, -, -, -, -, -, h8, -, -⟩ := hEL
  have hsin : Real.sin (ε / 2) < ε / 2 := Real.sin_lt (by linarith)
  have hone : ComplexMatrix2.operatorNorm (A - 1) < 1 := by linarith
  have hmem := Matrix.mem_specialUnitaryGroup_iff.mp hA
  obtain ⟨H, -, -, hHpi, hexp, hnorm, hdet⟩ := h8 A hmem.1 hone
  obtain ⟨-, hsu, -, -⟩ := hdet hmem.2
  refine ⟨(⟨H, hsu⟩ : ComplexMatrix2.hermitianTraceless), ?_, hexp⟩
  change ComplexMatrix2.operatorNorm H < ε
  have hpi := Real.pi_gt_three
  have hnn : 0 ≤ ComplexMatrix2.operatorNorm H := norm_nonneg _
  have hlt : Real.sin (ComplexMatrix2.operatorNorm H / 2) < Real.sin (ε / 2) := by
    rw [hnorm] at hclose
    linarith
  have := (Real.strictMonoOn_sin.lt_iff_lt
    (a := ComplexMatrix2.operatorNorm H / 2) (b := ε / 2)
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩).mp hlt
  linarith
variable [Fintype σ] [Nonempty σ]
theorem expFamily_image_lieBall (hc : PowerCharts σ) (hEL : ComplexMatrix2.ExpLogEstimates)
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    expFamily '' lieBall σ ε =
      {X | X ∈ specialUnitaryPower σ ∧
        ∀ s, ComplexMatrix2.operatorNorm (X s - 1) < 2 * Real.sin (ε / 2)} := by
  ext X
  constructor
  · rintro ⟨Y, hY, rfl⟩
    have hmem := expFamily_mem hc Y
    refine ⟨hmem, fun s => ?_⟩
    have hYs := (mem_lieBall_iff ε Y).mp hY s
    rw [show expFamily Y s = ComplexMatrix2.matExp (Complex.I • (Y s).toMatrix) from rfl,
      operatorNorm_exp_sub_one hEL (lt_of_lt_of_le hYs h1) (hmem s)]
    have hpi := Real.pi_gt_three
    have hnn : 0 ≤ ComplexMatrix2.operatorNorm (Y s).toMatrix := norm_nonneg _
    have := Real.strictMonoOn_sin
      (a := ComplexMatrix2.operatorNorm (Y s).toMatrix / 2) (b := ε / 2)
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    linarith
  · rintro ⟨hX, hclose⟩
    choose Y hY hexp using fun s => exists_small_log hEL (hX s) h0 h1 (hclose s)
    exact ⟨Y, (mem_lieBall_iff ε Y).mpr hY, funext hexp⟩
theorem expImagesOfBalls_holds (hc : PowerCharts σ)
    (hEL : ComplexMatrix2.ExpLogEstimates) : ExpImagesOfBalls σ := by
  refine ⟨fun ε h0 h1 => expFamily_image_lieBall hc hEL h0 h1, fun N hN => ?_⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp hN
  have h0 : 0 < min δ (1 / 2) := lt_min hδ (by norm_num)
  have h1 : min δ (1 / 2) ≤ 1 / 2 := min_le_right _ _
  refine ⟨min δ (1 / 2), h0, h1, ?_⟩
  intro X hX
  rw [expFamily_image_lieBall hc hEL h0 h1] at hX
  refine hball ⟨?_, hX.1⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hδ]
  intro s
  have hsin : Real.sin (min δ (1 / 2) / 2) < min δ (1 / 2) / 2 := Real.sin_lt (by linarith)
  have hle : min δ (1 / 2) ≤ δ := min_le_left _ _
  have := hX.2 s
  rw [dist_eq_norm]
  change ComplexMatrix2.operatorNorm (X s - 1) < δ
  linarith
end Images
theorem chartAndBallImages (h₁ : PowerExpCharts.ExpChartsStatement)
    (h₂ : ComplexMatrix2.ExpLogEstimates) :
    ChartAndBallImages.Statement := by
  intro σ _ _
  have hc : PowerCharts σ := (h₁ σ σ).1
  exact ⟨expChartAtOne_holds hc, expImagesOfBalls_holds hc h₂⟩
end BallImages
end IdentityExpChart
end YangMills.Construction
end
