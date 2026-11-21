import YangMills.Construction.ColdChainAtEveryLevel.CellNorms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.CellSecondDifferences
open ComplexifiedQuaternions BlockAverages ComplexDifferences ComplexLevels ComplexCells CellSources
  CellNormBounds LevelRecursion ComplexPlaquettes CellBounds HullBounds PlaquettesNearCell BlockLines
  FiniteDifferences LatticeFractionalIntegration WeightedAverages.Chains
variable {F : BlockFrame}
def cellSecondDiffSum (a : ℝ) (S : Finset F.Cell) (z : F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top)
    (W₀ W₁ W₂ W₃ : ComplexChainChart F) : ℝ :=
  ∑ q ∈ plaquettesOver S {z} 0,
      ‖complexPlaquetteTerm (complexChartField R W₃ 0) q - complexPlaquetteTerm (complexChartField R W₁ 0) q -
        complexPlaquetteTerm (complexChartField R W₂ 0) q + complexPlaquetteTerm (complexChartField R W₀ 0) q‖ +
    |a| * ∑ x ∈ lowerBonds (cellBall S z 1), ‖complexBondTerm R W₃ V x.1 x.2 - complexBondTerm R W₁ V x.1 x.2 -
      complexBondTerm R W₂ V x.1 x.2 + complexBondTerm R W₀ V x.1 x.2‖
theorem cellSecondDiffSum_le_add (a : ℝ) (S : Finset F.Cell) (z : F.Cell) (R : F.FieldChain)
    (V : F.GaugeField F.top) (W₀ W₁ W₂ W₃ : ComplexChainChart F) {T : ℝ} (hT : 0 ≤ T) :
    cellSecondDiffSum a S z R V W₀ W₁ W₂ W₃ ≤ ∑ q ∈ plaquettesOver S {z} 0,
        ‖complexPlaquetteTerm (complexChartField R W₃ 0) q - complexPlaquetteTerm (complexChartField R W₁ 0) q -
          complexPlaquetteTerm (complexChartField R W₂ 0) q + complexPlaquetteTerm (complexChartField R W₀ 0) q‖ +
      |a| * (∑ x ∈ lowerBonds (cellBall S z 1), ‖complexBondTerm R W₃ V x.1 x.2 - complexBondTerm R W₁ V x.1 x.2 -
        complexBondTerm R W₂ V x.1 x.2 + complexBondTerm R W₀ V x.1 x.2‖ + T) := by
  unfold cellSecondDiffSum
  have := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (a := ∑ x ∈ lowerBonds (cellBall S z 1),
    ‖complexBondTerm R W₃ V x.1 x.2 - complexBondTerm R W₁ V x.1 x.2 - complexBondTerm R W₂ V x.1 x.2 +
      complexBondTerm R W₀ V x.1 x.2‖) hT)
    (abs_nonneg a)
  linarith
set_option maxHeartbeats 4000000 in
theorem cellSecondDiffSum_le_of_fourDeviationBalls (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (a : ℝ) {S : Finset F.Cell} {z : F.Cell}
    {R : F.FieldChain} (V : F.GaugeField F.top) {W₀ W₁ W₂ W₃ : ComplexChainChart F} {C₀ s η B ε σ₀ : ℝ}
    (h : FourDeviationBalls R (cellBall S z 1) W₀ W₁ W₂ W₃ C₀ s η B)
    (s₀ : SourcesSmall (cellBall S z 1) W₀) (s₁ : SourcesSmall (cellBall S z 1) W₁)
    (s₂ : SourcesSmall (cellBall S z 1) W₂) (s₃ : SourcesSmall (cellBall S z 1) W₃)
    (par : SourceParallelogram W₀ W₁ W₂ W₃) {θ : ℝ} (hθ : |θ| ≤ 1 / 8) (p : F.Site 0)
    (hB0 : 0 ≤ B) (hfac1 : 568 * firstDiffFactor F.blockSide C₀ s B * hullFactor F.blockSide ≤ 1)
    (hfac2 : 568 * secondDiffFactor F.blockSide C₀ s η * hullFactor F.blockSide ≤ 1)
    (hε0 : 0 < ε) (hε : 3 * (ε + C₀ * s) < hullBallRadius F.blockSide)
    (hK : 200000 * (F.blockSide : ℝ) ^ 2 * (ε + C₀ * s) ≤ 1)
    (htε : 3 * (2 * (hullBondCount F.blockSide * η)) ≤ ε / 48) (hσ₀ : 0 < σ₀)
    (hcurv : ∀ q ∈ plaquettesOver S {z} 0, ‖ofUnit (basePlaquetteHolonomy (R 0) q) - 1‖ ≤ σ₀)
    (hsmq : ∀ q ∈ plaquettesOver S {z} 0,
      24 * (3 * (plaquetteSourceNorm q (baseSource W₀) + plaquetteSourceNorm q (baseSourceDiff W₀ W₁) +
        plaquetteSourceNorm q (baseSourceDiff W₀ W₂)) + σ₀) < 1 / 256)
    (hTs : finsetLpNorm 4 (plaquettesOver S {z} 0) (fun q => 12 * 173 *
      (3 * (plaquetteSourceNorm q (baseSource W₀) + plaquetteSourceNorm q (baseSourceDiff W₀ W₁) +
        plaquetteSourceNorm q (baseSourceDiff W₀ W₂)) + σ₀)) ≤ 1)
    (hYs : finsetLpNorm 2 (plaquettesOver S {z} 0) (fun q => ‖plaquetteGap (R 0) q (baseSource W₀)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₁)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₂)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₁ + baseSourceDiff W₀ W₂)‖) ≤ 1)
    (hY : finsetLpNorm 2 (lowerBonds (cellBall S z 1)) (lowerBondSize R W₀ W₁ W₂) ≤ 1)
    (hy1 : ∀ x ∈ lowerBonds (cellBall S z 1), lowerBondSize R W₀ W₁ W₂ x + ‖levelSource W₃ x.1 x.2.1 x.2.2 -
      levelSource W₁ x.1 x.2.1 x.2.2 - levelSource W₂ x.1 x.2.1 x.2.2 + levelSource W₀ x.1 x.2.1 x.2.2‖ ≤ 1) :
    cellSecondDiffSum a S z R V W₀ W₁ W₂ W₃ ≤
      cellSecondDiffConst (hullFactor F.blockSide) (200000 * (F.blockSide : ℝ) ^ 2) ε a *
        ((weightedScaleNorm (cellBall S z 1) p θ 4 0 (fun x i => ‖baseSource W₁ x i - baseSource W₀ x i‖) +
            finsetLpNorm 2 (lowerBonds (cellBall S z 1))
              (fun x => lowerScaleWeight p θ x * ‖upperSource W₁ x - upperSource W₀ x‖) +
            finsetLpNorm 2 (plaquettesOver S {z} 0)
              (fun q => scaleWeight p θ 0 q.1 * ‖covariantCurl (R 0) q (baseSourceDiff W₀ W₁)‖)) *
          (weightedScaleNorm (cellBall S z 1) p (-θ) 4 0 (fun x i => ‖baseSource W₂ x i - baseSource W₀ x i‖) +
            finsetLpNorm 2 (lowerBonds (cellBall S z 1))
              (fun x => lowerScaleWeight p (-θ) x * ‖upperSource W₂ x - upperSource W₀ x‖) +
            finsetLpNorm 2 (plaquettesOver S {z} 0)
              (fun q => scaleWeight p (-θ) 0 q.1 * ‖covariantCurl (R 0) q (baseSourceDiff W₀ W₂)‖))) := by
  have hθ' : |(-θ)| ≤ 1 / 8 := by rwa [abs_neg]
  have hD : (cellBall S z 1).card ≤ 81 := card_cellBall_one_le S z
  set D := cellBall S z 1 with hDd
  set u₁ := weightedScaleNorm D p θ 4 0 (fun x i => ‖baseSource W₁ x i - baseSource W₀ x i‖) with hu₁
  set u₂ := weightedScaleNorm D p (-θ) 4 0 (fun x i => ‖baseSource W₂ x i - baseSource W₀ x i‖) with hu₂
  set A₁ := finsetLpNorm 2 (lowerBonds D)
    (fun x => lowerScaleWeight p θ x * ‖upperSource W₁ x - upperSource W₀ x‖) with hA₁
  set A₂ := finsetLpNorm 2 (lowerBonds D)
    (fun x => lowerScaleWeight p (-θ) x * ‖upperSource W₂ x - upperSource W₀ x‖) with hA₂
  have hu₁0 : 0 ≤ u₁ := finsetLpNorm_nonneg _ _ _
  have hu₂0 : 0 ≤ u₂ := finsetLpNorm_nonneg _ _ _
  have hA₁0 : 0 ≤ A₁ := finsetLpNorm_nonneg _ _ _
  have hA₂0 : 0 ≤ A₂ := finsetLpNorm_nonneg _ _ _
  set T₁ := 2 * (20000 * (2 * u₁) + 284 * (4 * A₁)) with hT₁d
  set T₂ := 2 * (20000 * (2 * u₂) + 284 * (4 * A₂)) with hT₂d
  have hT₁0 : 0 ≤ T₁ := by positivity
  have hT₂0 : 0 ≤ T₂ := by positivity
  have hη : η < 1 := by
    have := h.nine_radius_le_one
    linarith
  have hsm3 : 3 * (2 * (hullBondCount F.blockSide * η) + C₀ * s) < hullBallRadius F.blockSide := by
    have := h.lt_hullBallRadius
    linarith
  have hT₁ : ∀ m, m < F.top → weightedScaleNorm D p θ 4 m (deviationFirstDiff R W₀ W₁ m) ≤ T₁ := fun m hm =>
    weightedScaleNorm_deviationFirstDiff_le hodd h2 hD p hθ h.const_pos h.scale_pos h.near h.ball₀ h.ball₁ s₀ s₁
      h.radius_nonneg hη hB0 h.spread_le hsm3 hfac1 m hm
  have hT₂ : ∀ m, m < F.top → weightedScaleNorm D p (-θ) 4 m (deviationFirstDiff R W₀ W₂ m) ≤ T₂ := fun m hm =>
    weightedScaleNorm_deviationFirstDiff_le hodd h2 hD p hθ' h.const_pos h.scale_pos h.near h.ball₀ h.ball₂ s₀ s₂
      h.radius_nonneg hη hB0 h.spread_le hsm3 hfac1 m hm
  set Hf := hullFactor F.blockSide with hHf
  have hHf0 : 0 ≤ Hf := hullFactor_nonneg _
  set K := 200000 * (F.blockSide : ℝ) ^ 2 with hKd
  have hK0 : 0 ≤ K := by positivity
  set T₁₂ := 2 * (142 * (8256 * (u₁ * u₂)) + 284 * (128 * K * ((Hf * T₁) * (Hf * T₂)) + 6 * 8256 * (A₁ * A₂) +
      4 * (A₁ * (Hf * T₂)) + 4 * (A₂ * (Hf * T₁)))) with hT₁₂d
  have hT₁₂0 : 0 ≤ T₁₂ := by positivity
  have hT₁₂ : ∀ m, m < F.top → weightedScaleNorm D p 0 2 m (deviationSecondDiff R W₀ W₁ W₂ W₃ m) ≤ T₁₂ :=
    fun m hm => weightedScaleNorm_deviationSecondDiff_le h hodd h2 s₀ s₁ s₂ s₃ par hθ p hT₁0 hT₂0 hT₁ hT₂ hfac2 m hm
  have hTb0 : 0 ≤ 4 * (240 * (Hf * T₁₂) + 30720 / ε * ((Hf * T₁) * (Hf * T₂))) := by positivity
  have hsum := cellSecondDiffSum_le_add a S z R V W₀ W₁ W₂ W₃ hTb0
  refine hsum.trans ?_
  have e₁ : baseSource W₁ = baseSource W₀ + baseSourceDiff W₀ W₁ := by
    simp only [baseSourceDiff]
    abel
  have e₂ : baseSource W₂ = baseSource W₀ + baseSourceDiff W₀ W₂ := by
    simp only [baseSourceDiff]
    abel
  have e₃ : baseSource W₃ = baseSource W₀ + baseSourceDiff W₀ W₁ + baseSourceDiff W₀ W₂ := by
    funext x i
    simp only [Pi.add_apply, baseSourceDiff, Pi.sub_apply, par.base x i]
    abel
  have hplaq := sum_norm_complexPlaquetteTerm_second_diff_le (S := S) (z := z) hamb hodd (R 0)
    (ξ := baseSource W₀) (e₁ := baseSourceDiff W₀ W₁) (e₂ := baseSourceDiff W₀ W₂) hσ₀ hcurv p hθ hsmq
  have hpe : ∀ q, complexPlaquetteTerm (complexChartField R W₃ 0) q -
      complexPlaquetteTerm (complexChartField R W₁ 0) q -
      complexPlaquetteTerm (complexChartField R W₂ 0) q + complexPlaquetteTerm (complexChartField R W₀ 0) q =
      complexPlaquetteTerm (expField (R 0) (baseSource W₀ + baseSourceDiff W₀ W₁ + baseSourceDiff W₀ W₂)) q -
      complexPlaquetteTerm (expField (R 0) (baseSource W₀ + baseSourceDiff W₀ W₁)) q -
      complexPlaquetteTerm (expField (R 0) (baseSource W₀ + baseSourceDiff W₀ W₂)) q +
      complexPlaquetteTerm (expField (R 0) (baseSource W₀)) q := by
    intro q
    rw [complexChartField_zero, complexChartField_zero, complexChartField_zero, complexChartField_zero,
      ← e₃, ← e₁, ← e₂]
  simp only [hpe]
  have eu₁ : weightedScaleNorm D p θ 4 0 (fun x i => ‖baseSourceDiff W₀ W₁ x i‖) = u₁ := rfl
  have eu₂ : weightedScaleNorm D p (-θ) 4 0 (fun x i => ‖baseSourceDiff W₀ W₂ x i‖) = u₂ := rfl
  rw [eu₁, eu₂] at hplaq
  have hss : ∀ x ∈ lowerBonds D, ‖upperSource W₀ x‖ ≤ 1 / 8000 ∧ ‖upperSource W₁ x‖ ≤ 1 / 8000 ∧
      ‖upperSource W₂ x‖ ≤ 1 / 8000 :=
    fun x hx => ⟨s₀.upper_le x hx, s₁.upper_le x hx, s₂.upper_le x hx⟩
  have hmid := sum_norm_complexBondTerm_second_diff_le h hodd V hθ p hT₁0 hT₂0 hT₁₂0 hA₁0 hA₂0
    (finsetLpNorm_nonneg 2 (lowerBonds D) (lowerBondSize R W₀ W₁ W₂)) hT₁ hT₂ hT₁₂
    (fun x => ‖upperSource W₁ x - upperSource W₀ x‖) (fun x => ‖upperSource W₂ x - upperSource W₀ x‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (fun x hx => norm_unitExp_sub_le (((hss x hx).1).trans (by norm_num)) (((hss x hx).2.1).trans (by norm_num)))
    (fun x hx => norm_unitExp_sub_le (((hss x hx).1).trans (by norm_num)) (((hss x hx).2.2).trans (by norm_num)))
    (fun x hx => norm_unitExp_parallelogram_le (par.upper x) (hss x hx).1 (hss x hx).2.1 (hss x hx).2.2)
    (lowerBondSize R W₀ W₁ W₂) (fun _ _ => rfl) hy1 le_rfl le_rfl le_rfl
  set Y := finsetLpNorm 2 (lowerBonds D) (lowerBondSize R W₀ W₁ W₂) with hYd
  have hY0 : 0 ≤ Y := finsetLpNorm_nonneg _ _ _
  set C₁ := finsetLpNorm 2 (plaquettesOver S {z} 0)
    (fun q => scaleWeight p θ 0 q.1 * ‖covariantCurl (R 0) q (baseSourceDiff W₀ W₁)‖) with hC₁
  set C₂ := finsetLpNorm 2 (plaquettesOver S {z} 0)
    (fun q => scaleWeight p (-θ) 0 q.1 * ‖covariantCurl (R 0) q (baseSourceDiff W₀ W₂)‖) with hC₂
  set Ts := finsetLpNorm 4 (plaquettesOver S {z} 0) (fun q => 12 * 173 *
      (3 * (plaquetteSourceNorm q (baseSource W₀) + plaquetteSourceNorm q (baseSourceDiff W₀ W₁) +
        plaquetteSourceNorm q (baseSourceDiff W₀ W₂)) + σ₀)) with hTsd
  set Ys := finsetLpNorm 2 (plaquettesOver S {z} 0) (fun q => ‖plaquetteGap (R 0) q (baseSource W₀)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₁)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₂)‖ +
      ‖plaquetteGap (R 0) q (baseSource W₀ + baseSourceDiff W₀ W₁ + baseSourceDiff W₀ W₂)‖) with hYsd
  have harith := cellSecondDiff_le_const (a := a) (Y := Y) (Ts := Ts) (Ys := Ys) (C₁ := C₁) (C₂ := C₂)
    hu₁0 hu₂0 hA₁0 hA₂0 (finsetLpNorm_nonneg _ _ _) (finsetLpNorm_nonneg _ _ _)
    hHf0 hK0 hε0 hY0 hY (finsetLpNorm_nonneg _ _ _) hTs (finsetLpNorm_nonneg _ _ _) hYs hT₁d hT₂d hT₁₂d
  have habs := mul_le_mul_of_nonneg_left (add_le_add hmid (le_refl (4 * (240 * (Hf * T₁₂) +
    30720 / ε * ((Hf * T₁) * (Hf * T₂)))))) (abs_nonneg a)
  refine le_trans (add_le_add hplaq habs) ?_
  exact harith
set_option maxHeartbeats 4000000 in
theorem cellSecondDiffSum_le_of_sourceBounds (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (a : ℝ) {S : Finset F.Cell} {z : F.Cell}
    {R : F.FieldChain} (V : F.GaugeField F.top) {W₀ W₁ W₂ W₃ : ComplexChainChart F} {C₀ s y : ℝ}
    (par : SourceParallelogram W₀ W₁ W₂ W₃) (hy : SmallParameter F.blockSide y) (hC : 0 < C₀) (hs : 0 < s)
    (hCs : C₀ * s ≤ y)
    (hnear : ContoursNearUnit R (cellBall S z 1) C₀ s)
    (hmis : finsetLpNorm 2 (lowerBonds (cellBall S z 1))
      (fun x => ‖ofUnit (referenceDefect R x.1 x.2) - 1‖) ≤ y)
    (hcurv : ∀ q ∈ plaquettesOver S {z} 0, ‖ofUnit (basePlaquetteHolonomy (R 0) q) - 1‖ ≤
      C₀ * s / ((F.blockSide : ℝ) ^ F.top) ^ 2)
    (z₀ : SourceBounds S z R W₀ y) (z₁ : SourceBounds S z R W₁ y) (z₂ : SourceBounds S z R W₂ y)
    (z₃ : SourceBounds S z R W₃ y)
    (hcl : ∀ W : ComplexChainChart F,
      Real.sqrt (Real.sqrt (∑ b ∈ innerBonds (cellBall S z 1) 0, ‖levelDeviation R W 0 b.1 b.2‖ ^ 4)) ≤ 2 * y →
      (∀ j, j + 1 < F.top →
        Real.sqrt (∑ c ∈ innerBonds (cellBall S z 1) (j + 1), ‖levelSource W j c.1 c.2 - 1‖ ^ 2) ≤ 2 * y) →
      ∀ j, j < F.top →
        Real.sqrt (Real.sqrt (∑ b ∈ innerBonds (cellBall S z 1) j, ‖levelDeviation R W j b.1 b.2‖ ^ 4)) ≤
          4 * (2 * y))
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) (p : F.Site 0) :
    cellSecondDiffSum a S z R V W₀ W₁ W₂ W₃ ≤
      cellSecondDiffConst (hullFactor F.blockSide) (200000 * (F.blockSide : ℝ) ^ 2)
          (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) a *
        ((weightedScaleNorm (cellBall S z 1) p θ 4 0 (fun x i => ‖baseSource W₁ x i - baseSource W₀ x i‖) +
            finsetLpNorm 2 (lowerBonds (cellBall S z 1))
              (fun x => lowerScaleWeight p θ x * ‖upperSource W₁ x - upperSource W₀ x‖) +
            finsetLpNorm 2 (plaquettesOver S {z} 0)
              (fun q => scaleWeight p θ 0 q.1 * ‖covariantCurl (R 0) q (baseSourceDiff W₀ W₁)‖)) *
          (weightedScaleNorm (cellBall S z 1) p (-θ) 4 0 (fun x i => ‖baseSource W₂ x i - baseSource W₀ x i‖) +
            finsetLpNorm 2 (lowerBonds (cellBall S z 1))
              (fun x => lowerScaleWeight p (-θ) x * ‖upperSource W₂ x - upperSource W₀ x‖) +
            finsetLpNorm 2 (plaquettesOver S {z} 0)
              (fun q => scaleWeight p (-θ) 0 q.1 * ‖covariantCurl (R 0) q (baseSourceDiff W₀ W₂)‖))) := by
  apply CellNormBounds.sourceBounds_to_deviationEstimates hamb hodd h2 par hy hC hs hCs hnear hmis hcurv
    z₀ z₁ z₂ z₃ hcl hθ p
  intro η B ε σ₀ hεValue h s₀ s₁ s₂ s₃ hB0 hfac1 hfac2 hε0 hε hK htε hσ₀ hcurv' hsmq hTs hYs hY hy1
  subst ε
  exact cellSecondDiffSum_le_of_fourDeviationBalls hamb hodd h2 a V h s₀ s₁ s₂ s₃ par hθ p hB0
    hfac1 hfac2 hε0 hε hK htε hσ₀ hcurv' hsmq hTs hYs hY hy1
end YangMills.Construction.CellSecondDifferences
end
