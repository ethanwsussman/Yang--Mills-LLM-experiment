import YangMills.Construction.ColdChainAtEveryLevel.SmallMultiplesOfTwoDirections
import YangMills.Construction.ColdChainAtEveryLevel.TermsAtTheTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.SmallMultiples
open BlockAverages ComplexDifferences ComplexLevels ComplexContours LowerLevelTerms TopLevelTerms RealChartTerms
  LinearLevels RealDirections HullBounds ComplexRemainders LevelRecursion
variable {F : BlockFrame}
theorem weightedScaleNorm_levelDeviation_sub_le_of_scaled (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    {D : Finset F.Cell} (hD : D.card ≤ 81) (p : F.Site 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {W W' X : ChainChart F} {C₀ s η ε B : ℝ}
    (hC : 0 < C₀) (hs : 0 < s) (hnear : ContoursNearUnit R D C₀ s) (hb : DeviationBall R D (realChart W) η η)
    (hb' : DeviationBall R D (realChart W') η η) (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hσ : C₀ * s ≤ 1 / 64) (hsm : 3 * (2 * (hullBondCount F.blockSide * η) + C₀ * s) < hullBallRadius F.blockSide)
    (hfac : 568 * firstDiffFactor F.blockSide C₀ s η * hullFactor F.blockSide ≤ 1)
    (hu : ∀ b ∈ innerBonds D 0, ‖(W.fine b.1 b.2 : ℍ[ℝ])‖ ≤ 1 / 4000 ∧ ‖(W'.fine b.1 b.2 : ℍ[ℝ])‖ ≤ 1 / 4000)
    (hmu : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1), ‖(W.coarse m c.1 c.2 : ℍ[ℝ])‖ ≤ 1 / 4000 ∧
      ‖(W'.coarse m c.1 c.2 : ℍ[ℝ])‖ ≤ 1 / 4000)
    (hdu : ∀ x i, W'.fine x i - W.fine x i = ε • X.fine x i)
    (hdm : ∀ m y i, W'.coarse m y i - W.coarse m y i = ε • X.coarse m y i)
    (h0 : weightedScaleNorm D p θ 4 0 (fun x i => ‖(X.fine x i : ℍ[ℝ])‖) ≤ B)
    (h1 : ∀ m, m + 1 < F.top → weightedScaleNorm D p θ 2 (m + 1) (fun y d => ‖(X.coarse m y d : ℍ[ℝ])‖) ≤ B)
    (m : ℕ) (hm : m < F.top) :
    weightedScaleNorm D p θ 4 m
      (fun z d => ‖(levelDeviation R (realChart W') m - levelDeviation R (realChart W) m) z d‖) ≤ 82272 * (ε * B) :=
  weightedScaleNorm_realChart_first_diff_le hodd h2 hD p hθ hC hs hnear hb hb' hη0 hη1 hη0 (by positivity) hσ hsm
    hfac hu hmu
    (weightedScaleNorm_le_of_abs_le hodd p θ (by norm_num) 0 hε (fun b _ => by
      rw [abs_of_nonneg (norm_nonneg _), hdu, norm_coe_smul_imaginary ε hε]) (fun _ _ => norm_nonneg _) h0)
    (fun m hm => weightedScaleNorm_le_of_abs_le hodd p θ (by norm_num) (m + 1) hε (fun b _ => by
      rw [abs_of_nonneg (norm_nonneg _), hdm, norm_coe_smul_imaginary ε hε]) (fun _ _ => norm_nonneg _) (h1 m hm))
    m hm
set_option maxHeartbeats 4000000 in
theorem smallDirectionTriple_scaledChart (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide) {D : Finset F.Cell}
    (hD : D.card ≤ 81) {p : F.Site 0}
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {U A : ChainChart F} {C₀ s Bu Ba c ε M : ℝ}
    (hC : 0 < C₀) (hs : 0 < s) (hs1 : s ≤ 1) (hx : C₀ * s ≤ smallnessThreshold F.blockSide)
    (ref : ReferenceNear D R C₀ s)
    (hcb : ∀ (W : ChainChart F) (B : ℝ), 0 ≤ B → B ≤ c →
      finsetLpNorm 4 (innerBonds D 0) (fun b => ‖(W.fine b.1 b.2 : ℍ[ℝ])‖) ≤ B →
      (∀ j, j + 1 < F.top → finsetLpNorm 2 (innerBonds D (j + 1)) (fun b => ‖(W.coarse j b.1 b.2 : ℍ[ℝ])‖) ≤ B) →
      DeviationBall R D (realChart W) (4 * B) (4 * B))
    (nm : PairWeightedNorms D p θ U A Bu Ba) (hBu : 0 ≤ Bu) (hBa : 0 ≤ Ba) (hε : 0 < ε)
    (hM : pairSize D U A + 8 * (hullBondCount F.blockSide * pairSize D U A) + Bu + Ba +
      ∑ c ∈ innerBonds D (F.depth + 1), (topLinearSize R U c.1 c.2 + topLinearSize R A c.1 c.2) ≤ M)
    (hεM : ε * M ≤ smallnessThreshold F.blockSide) (hεM2 : 4 * (ε * M) ≤ 1 / 4000)
    (hεQ : (4 * (ε * pairSize D U A)) * (1 + hullBondCount F.blockSide + hullFactor F.blockSide) ≤
      smallnessThreshold F.blockSide)
    (hεc : ε * pairSize D U A ≤ c) :
    SmallDirectionTriple D p θ R (scaledChart U ε) (scaledChart A ε) (scaledSumChart U A ε) C₀ s (ε * M) (ε * Bu)
      (ε * Ba) ∧
    TopDirectionBounds D p θ R (scaledChart U ε) (scaledChart A ε) (ε * M) (ε * Bu) (ε * Ba)
      (linearPartError F.blockSide ((F.blockSide : ℝ) ^ F.top) (C₀ * s) (ε * M) (ε * Bu))
      (linearPartError F.blockSide ((F.blockSide : ℝ) ^ F.top) (C₀ * s) (ε * M) (ε * Ba)) := by
  have hθ' : |(-θ)| ≤ 1 / 8 := by rwa [abs_neg]
  have hε0 : 0 ≤ ε := hε.le
  set Q := pairSize D U A with hQ
  have hQ0 : 0 ≤ Q := pairSize_nonneg D U A
  have hH0 := hullBondCount_nonneg F.blockSide
  have hx0 : 0 ≤ C₀ * s := by positivity
  have hsum0 : 0 ≤ ∑ c ∈ innerBonds D (F.depth + 1), (topLinearSize R U c.1 c.2 + topLinearSize R A c.1 c.2) :=
    Finset.sum_nonneg fun c _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hM0 : 0 ≤ M := le_trans (by positivity) hM
  set T := ε * M with hT
  have hT0 : 0 ≤ T := by positivity
  set η := 4 * (ε * Q) with hη
  have hη0 : 0 ≤ η := by positivity
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14⟩ :=
    smallness_bounds hodd hx0 hx hη0 hεQ hT0 hεM
  have ball : ∀ W : ChainChart F, DominatedBy U A ε W → DeviationBall R D (realChart W) η η := fun W d =>
    hcb W (ε * Q) (by positivity) hεc (d.finsetLpNorm_fine_le hε0 D)
      (fun j hj => d.finsetLpNorm_coarse_le hε0 D (by omega))
  have d₀ := dominatedBy_zeroChart U A hε0
  have d₁ := dominatedBy_scaledChart_left U A hε0
  have d₂ := dominatedBy_scaledChart_right U A hε0
  have d₃ := dominatedBy_scaledSumChart U A hε0
  have b₀ := ball _ d₀
  have b₁ := ball _ d₁
  have b₂ := ball _ d₂
  have b₃ := ball _ d₃
  have hQT : ε * Q ≤ T := by
    have : Q ≤ M := le_trans (by nlinarith) hM
    exact mul_le_mul_of_nonneg_left this hε0
  have hT4 : T ≤ 1 / 4000 := by linarith
  have hsu : ∀ {W : ChainChart F}, DominatedBy U A ε W → ∀ b ∈ innerBonds D 0,
      ‖(W.fine b.1 b.2 : ℍ[ℝ])‖ ≤ 1 / 4000 :=
    fun d b hb => ((d.norm_fine_le hε0 hb).trans hQT).trans hT4
  have hsm : ∀ {W : ChainChart F}, DominatedBy U A ε W → ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1),
      ‖(W.coarse m c.1 c.2 : ℍ[ℝ])‖ ≤ 1 / 4000 :=
    fun d m hm c hc => ((d.norm_coarse_le hε0 (by omega) hc).trans hQT).trans hT4
  have e0u : ∀ (W : ChainChart F) x i, W.fine x i - (zeroChart F).fine x i = W.fine x i :=
    fun W x i => sub_zero _
  have e0m : ∀ (W : ChainChart F) m y i, W.coarse m y i - (zeroChart F).coarse m y i = W.coarse m y i :=
    fun W m y i => sub_zero _
  have g₁' := fun m hm => weightedScaleNorm_levelDeviation_sub_le_of_scaled (W := zeroChart F)
    (W' := scaledChart U ε) (X := U) hodd h2 hD p hθ hC hs
    ref.contours b₀ b₁ hη0 f14 hε0 hBu f1 f3 f8 (fun b hb => ⟨hsu d₀ b hb, hsu d₁ b hb⟩)
    (fun m hm c hc => ⟨hsm d₀ m hm c hc, hsm d₁ m hm c hc⟩)
    (fun x i => by rw [e0u, scaledChart_fine]) (fun m y i => by rw [e0m, scaledChart_coarse]) nm.fine_le
    nm.coarse_le m hm
  have g₂' := fun m hm => weightedScaleNorm_levelDeviation_sub_le_of_scaled (W := zeroChart F)
    (W' := scaledChart A ε) (X := A) hodd h2 hD p hθ' hC hs
    ref.contours b₀ b₂ hη0 f14 hε0 hBa f1 f3 f8 (fun b hb => ⟨hsu d₀ b hb, hsu d₂ b hb⟩)
    (fun m hm c hc => ⟨hsm d₀ m hm c hc, hsm d₂ m hm c hc⟩)
    (fun x i => by rw [e0u, scaledChart_fine]) (fun m y i => by rw [e0m, scaledChart_coarse]) nm.fine_inv_le
    nm.coarse_inv_le m hm
  have g₁₃ := fun m hm => weightedScaleNorm_levelDeviation_sub_le_of_scaled (W := scaledChart U ε)
    (W' := scaledSumChart U A ε) (X := A) hodd h2 hD p hθ' hC hs
    ref.contours b₁ b₃ hη0 f14 hε0 hBa f1 f3 f8 (fun b hb => ⟨hsu d₁ b hb, hsu d₃ b hb⟩)
    (fun m hm c hc => ⟨hsm d₁ m hm c hc, hsm d₃ m hm c hc⟩)
    (fun x i => by rw [scaledSumChart_fine, add_sub_cancel_left, scaledChart_fine])
    (fun m y i => by rw [scaledSumChart_coarse, add_sub_cancel_left, scaledChart_coarse]) nm.fine_inv_le
    nm.coarse_inv_le m hm
  have g₂₃ := fun m hm => weightedScaleNorm_levelDeviation_sub_le_of_scaled (W := scaledChart A ε)
    (W' := scaledSumChart U A ε) (X := U) hodd h2 hD p hθ hC hs
    ref.contours b₂ b₃ hη0 f14 hε0 hBu f1 f3 f8 (fun b hb => ⟨hsu d₂ b hb, hsu d₃ b hb⟩)
    (fun m hm c hc => ⟨hsm d₂ m hm c hc, hsm d₃ m hm c hc⟩)
    (fun x i => by rw [scaledSumChart_fine, add_sub_cancel_right, scaledChart_fine])
    (fun m y i => by rw [scaledSumChart_coarse, add_sub_cancel_right, scaledChart_coarse]) nm.fine_le
    nm.coarse_le m hm
  have g₁ : ∀ m, m < F.top → weightedScaleNorm D p θ 4 m
      (fun z d => ‖levelDeviation R (realChart (scaledChart U ε)) m z d‖) ≤ 82272 * (ε * Bu) := by
    intro m hm
    have := g₁' m hm
    simpa only [levelDeviation_zeroChart hodd, sub_zero] using this
  have g₂ : ∀ m, m < F.top → weightedScaleNorm D p (-θ) 4 m
      (fun z d => ‖levelDeviation R (realChart (scaledChart A ε)) m z d‖) ≤ 82272 * (ε * Ba) := by
    intro m hm
    have := g₂' m hm
    simpa only [levelDeviation_zeroChart hodd, sub_zero] using this
  have hB₁ : 0 ≤ ε * Bu := by positivity
  have hB₂ : 0 ≤ ε * Ba := by positivity
  have h01 : weightedScaleNorm D p θ 4 0 (fun x i => ‖((scaledChart U ε).fine x i : ℍ[ℝ])‖) ≤ ε * Bu :=
    weightedScaleNorm_le_of_abs_le hodd p θ (by norm_num) 0 hε0 (fun b _ => by
      rw [abs_of_nonneg (norm_nonneg _), scaledChart_fine, norm_coe_smul_imaginary ε hε0])
      (fun _ _ => norm_nonneg _) nm.fine_le
  have h02 : weightedScaleNorm D p (-θ) 4 0 (fun x i => ‖((scaledChart A ε).fine x i : ℍ[ℝ])‖) ≤ ε * Ba :=
    weightedScaleNorm_le_of_abs_le hodd p (-θ) (by norm_num) 0 hε0 (fun b _ => by
      rw [abs_of_nonneg (norm_nonneg _), scaledChart_fine, norm_coe_smul_imaginary ε hε0])
      (fun _ _ => norm_nonneg _) nm.fine_inv_le
  have h11 : ∀ m, m + 1 < F.top → weightedScaleNorm D p θ 2 (m + 1)
      (fun y d => ‖((scaledChart U ε).coarse m y d : ℍ[ℝ])‖) ≤ ε * Bu := fun m hm =>
    weightedScaleNorm_le_of_abs_le hodd p θ (by norm_num) (m + 1) hε0 (fun b _ => by
      rw [abs_of_nonneg (norm_nonneg _), scaledChart_coarse, norm_coe_smul_imaginary ε hε0])
      (fun _ _ => norm_nonneg _) (nm.coarse_le m hm)
  have h12 : ∀ m, m + 1 < F.top → weightedScaleNorm D p (-θ) 2 (m + 1)
      (fun y d => ‖((scaledChart A ε).coarse m y d : ℍ[ℝ])‖) ≤ ε * Ba := fun m hm =>
    weightedScaleNorm_le_of_abs_le hodd p (-θ) (by norm_num) (m + 1) hε0 (fun b _ => by
      rw [abs_of_nonneg (norm_nonneg _), scaledChart_coarse, norm_coe_smul_imaginary ε hε0])
      (fun _ _ => norm_nonneg _) (nm.coarse_inv_le m hm)
  have sec : ∀ m, m < F.top → weightedScaleNorm D p 0 2 m
      (fun z d => ‖(levelDeviation R (realChart (scaledSumChart U A ε)) m -
      (levelDeviation R (realChart (scaledChart U ε)) m + levelDeviation R (realChart (scaledChart A ε)) m)) z d‖) ≤
      2 * (142 * 8256 + 284 * secondSourceConst F.blockSide) * (ε * Bu * (ε * Ba)) := by
    intro m hm
    have := weightedScaleNorm_realChart_second_diff_le hodd h2 hD p hθ hC hs ref.contours b₀ b₁ b₂ b₃ hη0 f6
      hB₁ hB₂ f1 f2 f3 f4 f5 f7 f8
      (hsu d₁) (hsu d₂) (fun b _ => scaledSumChart_fine U A ε b.1 b.2) (hsm d₁) (hsm d₂)
      (fun m _ c _ => scaledSumChart_coarse U A ε m c.1 c.2) h01 h11 h02 h12 m hm
    have e : (fun z d => ‖(levelDeviation R (realChart (scaledSumChart U A ε)) m -
        (levelDeviation R (realChart (scaledChart U ε)) m +
          levelDeviation R (realChart (scaledChart A ε)) m)) z d‖) =
        fun z d => ‖(levelDeviation R (realChart (scaledSumChart U A ε)) m -
          levelDeviation R (realChart (scaledChart U ε)) m -
          levelDeviation R (realChart (scaledChart A ε)) m + levelDeviation R (realChart (zeroChart F)) m) z d‖ := by
      funext z d
      rw [levelDeviation_zeroChart hodd, add_zero, sub_add_eq_sub_sub]
    rw [e]
    exact this
  have hHQ : hullBondCount F.blockSide * η ≤ T / 2 := by
    have h1 : 8 * (hullBondCount F.blockSide * Q) ≤ M := le_trans (by nlinarith) hM
    have h2 : ε * (8 * (hullBondCount F.blockSide * Q)) ≤ ε * M := mul_le_mul_of_nonneg_left h1 hε0
    have e : hullBondCount F.blockSide * η = ε * (8 * (hullBondCount F.blockSide * Q)) / 2 := by
      rw [hη]
      ring
    rw [e]
    linarith
  have hull : ∀ {W : ChainChart F}, DeviationBall R D (realChart W) η η → ∀ m, m < F.top →
      ∀ c ∈ innerBonds D (m + 1), bondHullNorm c (levelDeviation R (realChart W) m) ≤ T / 2 :=
    fun b m hm c hc => (b.bondHullNorm_le hodd hη0 hm hc).trans hHQ
  have hT1 : T ≤ 1 := by linarith
  have hY1 : 0 ≤ 82272 * (ε * Bu) := by positivity
  have hY2 : 0 ≤ 82272 * (ε * Ba) := by positivity
  have hBuM : Bu ≤ M := le_trans (by nlinarith) hM
  have hBaM : Ba ≤ M := le_trans (by nlinarith) hM
  have hSumM : ∑ c ∈ innerBonds D (F.depth + 1), (topLinearSize R U c.1 c.2 + topLinearSize R A c.1 c.2) ≤ M :=
    le_trans (by nlinarith) hM
  have hlin : ∀ (X : ChainChart F), (∀ c ∈ innerBonds D (F.depth + 1), topLinearSize R X c.1 c.2 ≤
      ∑ c ∈ innerBonds D (F.depth + 1), (topLinearSize R U c.1 c.2 + topLinearSize R A c.1 c.2)) →
      ∀ c ∈ innerBonds D (F.depth + 1), topLinearSize R (scaledChart X ε) c.1 c.2 ≤ T := by
    intro X hX c hc
    have e : topLinearSize R (scaledChart X ε) c.1 c.2 = ε * topLinearSize R X c.1 c.2 := by
      simp only [topLinearSize]
      rw [linearPart_scaledChart, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    rw [e]
    exact mul_le_mul_of_nonneg_left ((hX c hc).trans hSumM) hε0
  have hpart₁ : ∀ c ∈ innerBonds D (F.depth + 1), topLinearSize R U c.1 c.2 ≤
      ∑ c ∈ innerBonds D (F.depth + 1), (topLinearSize R U c.1 c.2 + topLinearSize R A c.1 c.2) := fun c hc =>
    le_trans (by linarith [show 0 ≤ topLinearSize R A c.1 c.2 from norm_nonneg _])
      (Finset.single_le_sum
        (f := fun c : F.Site (F.depth + 1) × Fin 4 => topLinearSize R U c.1 c.2 + topLinearSize R A c.1 c.2)
        (fun c _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) hc)
  have hpart₂ : ∀ c ∈ innerBonds D (F.depth + 1), topLinearSize R A c.1 c.2 ≤
      ∑ c ∈ innerBonds D (F.depth + 1), (topLinearSize R U c.1 c.2 + topLinearSize R A c.1 c.2) := fun c hc =>
    le_trans (by linarith [show 0 ≤ topLinearSize R U c.1 c.2 from norm_nonneg _])
      (Finset.single_le_sum
        (f := fun c : F.Site (F.depth + 1) × Fin 4 => topLinearSize R U c.1 c.2 + topLinearSize R A c.1 c.2)
        (fun c _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) hc)
  have hN₁ : ∀ m, m < F.top → ∀ c ∈ innerBonds D (m + 1),
      bondHullNorm c (levelDeviation R (realChart (scaledChart U ε)) m) ≤ T :=
    fun m hm c hc => (hull b₁ m hm c hc).trans (by linarith)
  have hN₂ : ∀ m, m < F.top → ∀ c ∈ innerBonds D (m + 1),
      bondHullNorm c (levelDeviation R (realChart (scaledChart A ε)) m) ≤ T :=
    fun m hm c hc => (hull b₂ m hm c hc).trans (by linarith)
  have hN₃ : ∀ m, m < F.top → ∀ c ∈ innerBonds D (m + 1),
      bondHullNorm c (levelDeviation R (realChart (scaledSumChart U A ε)) m) ≤ T :=
    fun m hm c hc => (hull b₃ m hm c hc).trans (by linarith)
  have hu₁ : ∀ b ∈ innerBonds D 0, ‖((scaledChart U ε).fine b.1 b.2 : ℍ[ℝ])‖ ≤ T :=
    fun b hb => (d₁.norm_fine_le hε0 hb).trans hQT
  have hu₂ : ∀ b ∈ innerBonds D 0, ‖((scaledChart A ε).fine b.1 b.2 : ℍ[ℝ])‖ ≤ T :=
    fun b hb => (d₂.norm_fine_le hε0 hb).trans hQT
  have hm₁ : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1), ‖((scaledChart U ε).coarse m c.1 c.2 : ℍ[ℝ])‖ ≤ T :=
    fun m hm c hc => (d₁.norm_coarse_le hε0 (by omega) hc).trans hQT
  have hm₂ : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1), ‖((scaledChart A ε).coarse m c.1 c.2 : ℍ[ℝ])‖ ≤ T :=
    fun m hm c hc => (d₂.norm_coarse_le hε0 (by omega) hc).trans hQT
  refine ⟨⟨hC, hs, hs1, f1, hT0, hT4, hB₁, hB₂, f9, f10, g₁, g₂, g₁₃, g₂₃, sec, hN₁, hN₂, hN₃, ?_, ?_, hm₁, hm₂,
    fun m _ c _ => scaledSumChart_coarse U A ε m c.1 c.2, h11, h12⟩,
    ⟨mul_le_mul_of_nonneg_left hBuM hε0, mul_le_mul_of_nonneg_left hBaM hε0, hlin U hpart₁, hlin A hpart₂,
      weightedScaleNorm_linearPart_top_le hodd h2 hD p hθ hB₁ h01 h11,
      weightedScaleNorm_linearPart_top_le hodd h2 hD p hθ' hB₂ h02 h12, ?_, ?_⟩⟩
  · intro m hm c hc
    have := bondHullNorm_sub_le c (levelDeviation R (realChart (scaledSumChart U A ε)) m)
      (levelDeviation R (realChart (scaledChart U ε)) m)
    have a1 := hull b₃ m hm c hc
    have a2 := hull b₁ m hm c hc
    linarith
  · intro m hm c hc
    have := bondHullNorm_sub_le c (levelDeviation R (realChart (scaledSumChart U A ε)) m)
      (levelDeviation R (realChart (scaledChart A ε)) m)
    have a1 := hull b₃ m hm c hc
    have a2 := hull b₂ m hm c hc
    linarith
  · have hA := weightedScaleNorm_levelDeviation_sub_linearPart_le hodd h2 hD p hθ (V := scaledChart U ε) (T := T)
      (Bd := ε * Bu) (Y := 82272 * (ε * Bu))
      hC.le hs.le ref.contours f1 hT0 f11 f12 hT1 ref.defect hu₁ hm₁ hN₁ hB₁ hY1 h01 h11 g₁ F.depth
      (depth_lt_top F)
    exact weightedScaleNorm_unit_sub_linearPart_top_le hodd hD p hθ hC.le hs.le ref.contours f1 hT0 f12
      (hN₁ F.depth (depth_lt_top F)) (g₁ F.depth (depth_lt_top F)) hA
  · have hA := weightedScaleNorm_levelDeviation_sub_linearPart_le hodd h2 hD p hθ' (V := scaledChart A ε) (T := T)
      (Bd := ε * Ba) (Y := 82272 * (ε * Ba))
      hC.le hs.le ref.contours f1 hT0 f11 f12 hT1 ref.defect hu₂ hm₂ hN₂ hB₂ hY2 h02 h12 g₂ F.depth
      (depth_lt_top F)
    exact weightedScaleNorm_unit_sub_linearPart_top_le hodd hD p hθ' hC.le hs.le ref.contours f1 hT0 f12
      (hN₂ F.depth (depth_lt_top F)) (g₂ F.depth (depth_lt_top F)) hA
end YangMills.Construction.SmallMultiples
end
