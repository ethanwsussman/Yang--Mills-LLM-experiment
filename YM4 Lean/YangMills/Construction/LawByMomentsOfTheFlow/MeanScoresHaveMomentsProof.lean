import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresInALimitFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
section Numbers
private theorem prod_le_sum_inv_mul_pow {p : ℕ} (hp : 1 ≤ p) (a : Fin p → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∏ i, a i ≤ ∑ i, (p : ℝ)⁻¹ * a i ^ p := by apply _root_.YangMills.SharedProofs.p66653 <;> assumption
private theorem one_add_mean_pow_le {ι : Type} (B : Finset ι) (s : ι → ℝ) (hs : ∀ y, 0 ≤ s y) (p : ℕ) :
    (1 + (B.card : ℝ)⁻¹ * ∑ y ∈ B, s y) ^ p ≤ 1 + ∑ y ∈ B, (B.card : ℝ)⁻¹ * (2 ^ p * (1 + s y ^ p)) := by apply _root_.YangMills.SharedProofs.p14810 <;> assumption
private theorem one_add_two_pow_mul_le {C F : ℝ} (hC : 1 ≤ C) (hF : 1 ≤ F) {p : ℕ} (hp : 1 ≤ p) :
    1 + 2 ^ p * (1 + C ^ p * F) ≤ (8 * C) ^ p * F := by apply _root_.YangMills.SharedProofs.p9521 <;> assumption
private theorem integrable_prod_means_and_lintegral_le {Ω ι : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (s : ι → Ω → ℝ) (hs : ∀ z w, 0 ≤ s z w) (hm : ∀ z, AEStronglyMeasurable (s z) μ) {p : ℕ} (hp : 1 ≤ p) {A : ℝ}
    (hA : 0 ≤ A) (hint : ∀ z, Integrable (fun w => s z w ^ p) μ) (hle : ∀ z, ∫ w, s z w ^ p ∂μ ≤ A)
    (B : Fin p → Finset ι) :
    Integrable (fun w => ∏ i, (1 + ((B i).card : ℝ)⁻¹ * ∑ y ∈ B i, s y w)) μ ∧
      ∫⁻ w, ENNReal.ofReal (∏ i, (1 + ((B i).card : ℝ)⁻¹ * ∑ y ∈ B i, s y w)) ∂μ ≤
        ENNReal.ofReal (1 + 2 ^ p * (1 + A)) := by
  set A' : ℝ := 2 ^ p * (1 + A) with hA'
  have hA0 : 0 ≤ A' := by positivity
  have hone : ∫ _w, (1 : ℝ) ∂μ = 1 := by simp
  have hsite : ∀ z, Integrable (fun w => (2 : ℝ) ^ p * (1 + s z w ^ p)) μ ∧
      ∫ w, (2 : ℝ) ^ p * (1 + s z w ^ p) ∂μ ≤ A' := by
    intro z
    have hint1 : Integrable (fun w => (1 : ℝ) + s z w ^ p) μ := (integrable_const _).add (hint z)
    refine ⟨hint1.const_mul _, ?_⟩
    rw [integral_const_mul, integral_add (integrable_const _) (hint z), hone, hA']
    exact mul_le_mul_of_nonneg_left (by linarith [hle z]) (by positivity)
  have hin : ∀ i : Fin p, Integrable (fun w => ∑ z ∈ B i, ((B i).card : ℝ)⁻¹ * ((2 : ℝ) ^ p * (1 + s z w ^ p))) μ :=
    fun i => integrable_finsetSum _ fun z _ => (hsite z).1.const_mul _
  have hinner : ∀ i : Fin p, ∫ w, ∑ z ∈ B i, ((B i).card : ℝ)⁻¹ * ((2 : ℝ) ^ p * (1 + s z w ^ p)) ∂μ ≤ A' := by
    intro i
    rw [integral_finsetSum _ fun z _ => (hsite z).1.const_mul _]
    rcases (B i).eq_empty_or_nonempty with h0 | hB
    · simp [h0, hA0]
    have hc : ((B i).card : ℝ) ≠ 0 := by
      have := hB.card_pos
      positivity
    calc ∑ z ∈ B i, ∫ w, ((B i).card : ℝ)⁻¹ * ((2 : ℝ) ^ p * (1 + s z w ^ p)) ∂μ
        ≤ ∑ _z ∈ B i, ((B i).card : ℝ)⁻¹ * A' := by
          refine Finset.sum_le_sum fun z _ => ?_
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (hsite z).2 (by positivity)
      _ = A' := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  let G : Ω → ℝ := fun w =>
    ∑ i : Fin p, (p : ℝ)⁻¹ * (1 + ∑ z ∈ B i, ((B i).card : ℝ)⁻¹ * ((2 : ℝ) ^ p * (1 + s z w ^ p)))
  have hterm : ∀ i : Fin p, Integrable (fun w => (1 : ℝ) + ∑ z ∈ B i, ((B i).card : ℝ)⁻¹ *
      ((2 : ℝ) ^ p * (1 + s z w ^ p))) μ := fun i => (integrable_const _).add (hin i)
  have hGint : Integrable G μ := integrable_finsetSum _ fun i _ => (hterm i).const_mul _
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hGle : ∫ w, G w ∂μ ≤ 1 + A' := by
    show ∫ w, ∑ i : Fin p, (p : ℝ)⁻¹ * (1 + ∑ z ∈ B i, ((B i).card : ℝ)⁻¹ *
      ((2 : ℝ) ^ p * (1 + s z w ^ p))) ∂μ ≤ _
    rw [integral_finsetSum _ fun i _ => (hterm i).const_mul _]
    calc ∑ i : Fin p, ∫ w, (p : ℝ)⁻¹ * (1 + ∑ z ∈ B i, ((B i).card : ℝ)⁻¹ *
          ((2 : ℝ) ^ p * (1 + s z w ^ p))) ∂μ
        ≤ ∑ _i : Fin p, (p : ℝ)⁻¹ * (1 + A') := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [integral_const_mul, integral_add (integrable_const _) (hin i), hone]
          exact mul_le_mul_of_nonneg_left (by linarith [hinner i]) (by positivity)
      _ = 1 + A' := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, ← mul_assoc,
            mul_inv_cancel₀ hp0, one_mul]
  have hmean0 : ∀ (w : Ω) (i : Fin p), 0 ≤ 1 + ((B i).card : ℝ)⁻¹ * ∑ y ∈ B i, s y w := fun w i =>
    add_nonneg zero_le_one (mul_nonneg (by positivity) (Finset.sum_nonneg fun z _ => hs z w))
  have hpoint : ∀ w, ∏ i, (1 + ((B i).card : ℝ)⁻¹ * ∑ y ∈ B i, s y w) ≤ G w := by
    intro w
    refine (prod_le_sum_inv_mul_pow hp _ (hmean0 w)).trans ?_
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact one_add_mean_pow_le (B i) (fun z => s z w) (fun z => hs z w) p
  have hprod0 : ∀ w, 0 ≤ ∏ i, (1 + ((B i).card : ℝ)⁻¹ * ∑ y ∈ B i, s y w) := fun w =>
    Finset.prod_nonneg fun i _ => hmean0 w i
  have hG0 : ∀ w, 0 ≤ G w := fun w => (hprod0 w).trans (hpoint w)
  have hmeas : AEStronglyMeasurable (fun w => ∏ i, (1 + ((B i).card : ℝ)⁻¹ * ∑ y ∈ B i, s y w)) μ := by
    refine Finset.aestronglyMeasurable_fun_prod _ fun i _ => ?_
    refine aestronglyMeasurable_const.add (aestronglyMeasurable_const.mul ?_)
    exact Finset.aestronglyMeasurable_fun_sum _ fun z _ => hm z
  refine ⟨hGint.mono' hmeas (Filter.Eventually.of_forall fun w => ?_), ?_⟩
  · rw [Real.norm_of_nonneg (hprod0 w)]
    exact hpoint w
  · calc ∫⁻ w, ENNReal.ofReal (∏ i, (1 + ((B i).card : ℝ)⁻¹ * ∑ y ∈ B i, s y w)) ∂μ
        ≤ ∫⁻ w, ENNReal.ofReal (G w) ∂μ :=
          lintegral_mono fun w => ENNReal.ofReal_le_ofReal (hpoint w)
      _ = ENNReal.ofReal (∫ w, G w ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hGint (Filter.Eventually.of_forall hG0)).symm
      _ ≤ ENNReal.ofReal (1 + A') := ENNReal.ofReal_le_ofReal hGle
end Numbers
section Tower
variable {ℓ : TorusLumps.StepParameters}
private theorem fineSide_eq_mul_pow (L : ℕ) : ∀ k n : ℕ, WeightedResponses.fineSide L k n = n * L ^ k
  | 0, n => by simp [WeightedResponses.fineSide]
  | k + 1, n => by
    rw [WeightedResponses.fineSide, fineSide_eq_mul_pow L k (n * L), pow_succ]
    ring
private theorem siteSize_nonneg (T : WeightedResponses.StageTower ℓ) {s₁ : ℝ} (h₁ : 0 ≤ s₁) (u n : ℕ) [NeZero n]
    (w : WeightedResponses.MarkedSample ℓ u n) (y : TorusFields.TorusSite n) :
    0 ≤ HullTrees.siteSize T s₁ u n w y := by apply _root_.YangMills.SharedProofs.p9879 <;> assumption
private theorem hullDecayRate_nonneg {Tb : RenormalizationStepParameters.ParameterAssignment} (h : Tb.Admissible) :
    0 ≤ HullTrees.hullDecayRate Tb := by apply _root_.YangMills.SharedProofs.p10157 <;> assumption
end Tower
section Point
variable {Λ : MomentParameters} (S : MomentPoint Λ)
private theorem stageOnFlow {j : ℕ} (hj : j ≤ S.data.windowLevel) :
    ResponseInTheExpansion.StageOnFlow Λ.table Λ.response Λ.floor S.β j ⟨S.tower.stage j, S.resp j⟩ := by apply _root_.YangMills.SharedProofs.p6811 <;> assumption
private theorem nextStage_of_point {j : ℕ} (hj : j + 1 ≤ S.data.windowLevel) :
    S.tower.densities j = (S.tower.stage j).toStepSetup.renormalizedDensity Λ.table.lam ∧
      S.tower.siteDensities (S.tower.stage j).toStepSetup =
        (S.tower.stage j).toStepSetup.stateDensity Λ.table.lam ∧
      ∀ ω, (S.resp (j + 1)).score ω =
        WeightedResponses.coarseLabelScore (S.resp j).responseParams.s₁ (S.resp j).score ω := by apply _root_.YangMills.SharedProofs.p36968 <;> assumption
private theorem score_eq_labelSize (u : ℕ) (hu : u ≤ S.data.windowLevel) :
    (S.resp u).score = HullTrees.labelSize S.tower Λ.response.s₁ u := by apply _root_.YangMills.SharedProofs.p9388 <;> assumption
private theorem towerFollowsFlow_of_point : WeightedResponses.TowerFollowsFlow S.tower S.β S.data.windowLevel := by apply _root_.YangMills.SharedProofs.p11317 <;> assumption
private theorem hullChainAtLevel_of_point (hg : 0 < Λ.g) (hfl : Λ.floor ≤ (Λ.g ^ 2)⁻¹) {u : ℕ}
    (hu : u ≤ S.data.windowLevel) :
    HullTrees.HullChainAtLevel Λ.table Λ.floor Λ.g S.β S.data.windowLevel S.data.sideExponent S.tower u
      (S.levelSide u) where
  chain :=
    { g_pos := hg
      le_inv_sq := hfl
      upper_le := S.window_le
      isFirst := S.passage
      volume_le := S.side_le
      follows := towerFollowsFlow_of_point S
      depth_bottom := S.startsAtWilson.depth_eq
      functional_bottom := S.startsAtWilson.functional_eq
      anchor_bottom := (stageOnFlow S (Nat.zero_le _)).onFamily.onFamily.anchorRadius_eq
      cutoff_bottom := S.isCutoff
      marks := S.marksMeasurable
      expansions := fun j hj => (stageOnFlow S hj).onFamily.onFamily.isStep.1
      reads_flow :=
        { startsAtWilson := S.startsAtWilson
          coupling_eq := towerFollowsFlow_of_point S
          onFamily := fun j hj => (stageOnFlow S hj).onFamily.onFamily
          siteDensities_eq := fun j hj => (nextStage_of_point S hj).2.1
          densities_eq := fun j hj => (nextStage_of_point S hj).1 } }
  le := hu
  side_eq := by
    show S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - u) =
      WeightedResponses.fineSide _ _ _
    rw [fineSide_eq_mul_pow]
    rfl
private theorem moment_bound_at_point (hg : 0 < Λ.g) (hfl : Λ.floor ≤ (Λ.g ^ 2)⁻¹) (hy : 0 ≤ Λ.floor)
    (hDr : Λ.table.Admissible) (hfits : Λ.stepParams.Admissible) (hs₁ : 0 ≤ Λ.response.s₁)
    (hD : WeightedResponses.forgetLastStepStatement)
    {C₀ : ℝ} (hC₀ : 1 ≤ C₀)
    (hC : ∀ (β : ℝ) (K m : ℕ) (T : WeightedResponses.StageTower Λ.stepParams) (u n : ℕ) [NeZero n],
      HullTrees.HullChainAtLevel Λ.table Λ.floor Λ.g β K m T u n → ∀ (z : TorusFields.TorusSite n) (k : ℕ), 1 ≤ k →
        Integrable (fun w => HullTrees.siteSize T Λ.response.s₁ u n w z ^ k)
          (WeightedResponses.markedSampleLaw T β u n) ∧
        ∫ w, HullTrees.siteSize T Λ.response.s₁ u n w z ^ k ∂(WeightedResponses.markedSampleLaw T β u n) ≤
          C₀ ^ k * (k.factorial : ℝ) ^ 6 *
            Real.exp (-(HullTrees.hullDecayRate Λ.table * HullTrees.stageCoupling T u / 4)))
    (p : ℕ) (hp : 1 ≤ p) (J : List (Fin Λ.k)) (hJ : J.length = p) :
    Integrable (fun w => (J.map fun i => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)).prod)
      (S.law S.lastSeparated (S.levelSide S.lastSeparated)) ∧
    ∫⁻ w, ENNReal.ofReal (J.map fun i => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)).prod
      ∂(S.law S.lastSeparated (S.levelSide S.lastSeparated)) ≤
      ENNReal.ofReal ((8 * C₀) ^ p * (p.factorial : ℝ) ^ 6) := by
  subst hJ
  have hts : S.lastSeparated ≤ S.data.scaleLevel := by
    classical
    unfold MomentPoint.lastSeparated
    exact Nat.findGreatest_le _
  have hu : S.lastSeparated ≤ S.data.windowLevel := hts.trans S.supAdmissible.scaleLevel_le
  have hAt := hullChainAtLevel_of_point S hg hfl hu
  have hprob : IsProbabilityMeasure
      (WeightedResponses.markedSampleLaw S.tower S.β S.lastSeparated (S.levelSide S.lastSeparated)) :=
    (hD Λ.stepParams hfits hfits.depth_lt S.tower hAt.chain.cutoff_bottom hAt.chain.marks S.β S.lastSeparated
      (S.levelSide S.lastSeparated)).1
  have hF : (1 : ℝ) ≤ (J.length.factorial : ℝ) ^ 6 :=
    one_le_pow₀ (by exact_mod_cast Nat.succ_le_of_lt J.length.factorial_pos)
  have hexp : Real.exp (-(HullTrees.hullDecayRate Λ.table * HullTrees.stageCoupling S.tower S.lastSeparated / 4)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hx : Λ.floor ≤ HullTrees.stageCoupling S.tower S.lastSeparated :=
      (stageOnFlow S hu).onFamily.onFamily.le_coupling
    have := mul_nonneg (hullDecayRate_nonneg hDr) (hy.trans hx)
    linarith
  have hCF : 0 ≤ C₀ ^ J.length * (J.length.factorial : ℝ) ^ 6 := by positivity
  have hle : ∀ z, ∫ w, HullTrees.siteSize S.tower Λ.response.s₁ S.lastSeparated (S.levelSide S.lastSeparated) w z ^ J.length
      ∂(WeightedResponses.markedSampleLaw S.tower S.β S.lastSeparated (S.levelSide S.lastSeparated)) ≤
        C₀ ^ J.length * (J.length.factorial : ℝ) ^ 6 := fun z =>
    (hC S.β S.data.windowLevel S.data.sideExponent S.tower S.lastSeparated (S.levelSide S.lastSeparated) hAt z
      J.length hp).2.trans (mul_le_of_le_one_right hCF hexp)
  have hm : ∀ z, AEStronglyMeasurable
      (fun w => HullTrees.siteSize S.tower Λ.response.s₁ S.lastSeparated (S.levelSide S.lastSeparated) w z)
      (WeightedResponses.markedSampleLaw S.tower S.β S.lastSeparated (S.levelSide S.lastSeparated)) := fun z => by
    simpa only [pow_one] using (hC S.β S.data.windowLevel S.data.sideExponent S.tower S.lastSeparated
      (S.levelSide S.lastSeparated) hAt z 1 le_rfl).1.aestronglyMeasurable
  have hmain := integrable_prod_means_and_lintegral_le
    (μ := WeightedResponses.markedSampleLaw S.tower S.β S.lastSeparated (S.levelSide S.lastSeparated))
    (fun z w => HullTrees.siteSize S.tower Λ.response.s₁ S.lastSeparated (S.levelSide S.lastSeparated) w z)
    (fun z w => siteSize_nonneg S.tower hs₁ S.lastSeparated (S.levelSide S.lastSeparated) w z) hm hp hCF
    (fun z => (hC S.β S.data.windowLevel S.data.sideExponent S.tower S.lastSeparated (S.levelSide S.lastSeparated)
      hAt z J.length hp).1) hle
    (fun i : Fin J.length => S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) (J.get i))
  have hprod : ∀ w : WeightedResponses.MarkedSample Λ.stepParams S.lastSeparated (S.levelSide S.lastSeparated),
      (J.map fun i => S.meanScore S.lastSeparated (S.levelSide S.lastSeparated) i
        (S.state S.lastSeparated (S.levelSide S.lastSeparated) w)).prod =
        ∏ i : Fin J.length, (1 + ((S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) (J.get i)).card : ℝ)⁻¹ *
          ∑ y ∈ S.supportAt S.lastSeparated (S.levelSide S.lastSeparated) (J.get i),
            HullTrees.siteSize S.tower Λ.response.s₁ S.lastSeparated (S.levelSide S.lastSeparated) w y) := by
    intro w
    rw [← Fin.prod_univ_fun_getElem]
    refine Finset.prod_congr rfl fun i _ => ?_
    show ResponseInTheExpansion.meanSiteScore (S.resp S.lastSeparated).score _ _ _ = _
    rw [score_eq_labelSize S S.lastSeparated hu]
    rfl
  refine ⟨?_, ?_⟩
  · simp only [hprod]
    exact hmain.1
  · simp only [hprod]
    refine hmain.2.trans (ENNReal.ofReal_le_ofReal ?_)
    exact one_add_two_pow_mul_le hC₀ hF hp
end Point
theorem meanScoreMomentBound (hM : HullTrees.siteSizeMomentStatement)
    (hD : WeightedResponses.forgetLastStepStatement) : meanScoreMomentBoundStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₁, hrt, hL⟩ := hM a ha
  refine ⟨L₀, rt₀, C₁, hrt, fun L hodd hL₀ Tb hTa hTL hDr hCold hHalf hrtle hCder => ?_⟩
  obtain ⟨Mc, hMc⟩ := hL L hodd hL₀ Tb hTa hTL hDr hCold hHalf hrtle hCder
  refine ⟨Mc, fun Kr hKc hη hN hfit hret => ?_⟩
  obtain ⟨y₀, hy₀⟩ := hMc Kr hKc hη hN hfit hret
  refine ⟨max y₀ (max Tb.floorMin 0), fun y hy hRet hWil g hg hgy k _ _ _ R d _ => ?_⟩
  obtain ⟨C₀, hC₀, hC⟩ := hy₀ y (le_trans (le_max_left _ _) hy) hRet hWil g
  have hy1 : Tb.floorMin ≤ y := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hy
  have hy2 : (0 : ℝ) ≤ y := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hy
  have hfits : (Tb.stepParameters y).Admissible := hDr.fits y hy1
  have hs₁ : 0 ≤ Kr.s₁ := by
    have hk := hfit y
    have ha1 : 1 ≤ (Tb.stepParameters y).coupling := hfits.a_ge
    have hC0 : 0 ≤ Kr.C₀ + 2 := by
      have := hk.Kc_ge
      have := hk.N₀_nonneg
      rw [hk.C₀_eq]
      linarith
    rw [hk.s₁_eq]
    exact add_nonneg (mul_nonneg (by positivity) hC0) (by linarith)
  refine ⟨fun _ => 8 * C₀, 1, y, one_pos, le_rfl, fun S p hp J hJ => ?_⟩
  exact moment_bound_at_point (Λ := ⟨Tb, Kr, y, g, k, R, d⟩) S hg hgy hy2 hDr hfits hs₁ hD hC₀ hC p hp J hJ
end YangMills.Construction.MomentLaw
end
