import YangMills.Construction.ClusterExpansionOfAStep.SlopeAtTheFrames
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages StepSettings TorusFields TorusLumps TorusContours WideCharts FreeBondMoves
namespace FrameSlope
variable {R : StepSetup} {n : ℕ} [NeZero n] {s : ChartSetting R n} {δ lam σA cg : ℝ} {N : ℕ → ℝ}
variable {CA Cm Kf σ' : ℝ} {w : (topFrame R n).Site (topFrame R n).depth → Fin 4 → imaginaryQuaternions}
theorem exists_minimizerData_frame_close (c : s.ChainContext δ lam σA cg N) :
    ∃ σ' w, s.MinimizerData lam σA (N 0) σ' w ∧ ∀ b ∈ s.free,
      ‖((s.frame b : imaginaryQuaternions) : ℍ[ℝ]) - ((w (topSite R n b.1) b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        N 0 * (2 * R.params.threshold) * Real.exp (-(δ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) := by
  obtain ⟨C, σ', hsit, hoff⟩ := ChartSetting.exists_stepSituation c.admissible c.n₀_le
  obtain ⟨hσ0, hσ2, -, hF⟩ := TopLevelSites.stepSituation_regular_and_cold c.complement_regular c.params_admissible hsit
  obtain ⟨hreg, hcold⟩ := hF (topFrame R n) (topFrame_extent R n)
  have hchain := c.chain
  obtain ⟨hδ, hδ8, hlam, hρ, hρ1, hσA, hcg, hN, hch⟩ := hchain
  have hL := c.params_admissible.L_odd
  have h2 := c.two_le
  have hs : ∀ i, 2 ≤ (topFrame R n).extent i := fun _ => h2
  have hσle : σ' ≤ σA := hσ2.trans c.threshold_le
  have hamb : IsAdmissibleAmbient (topFrame R n) := by
    refine Or.inr fun i => ?_
    have := c.params_admissible.n₀_ge
    have := c.n₀_le
    show 64 ≤ n
    omega
  obtain ⟨H1, H2, -⟩ := hch (topFrame R n) 2047 s.regionCells rfl hamb (by norm_num) hreg σ' _ hσ0 hσle hcold
  have hπ : R.anchorRadius < Real.pi := by
    have := Real.pi_gt_three
    linarith
  obtain ⟨w, hw, hwc, hlc⟩ := TopLevelSites.minimizingCoordinates_eq (F := topFrame R n) hL hs hπ le_rfl H1
  have key : ∀ b ∈ StepCosts.chartBonds R.params.side n, (∃ b₀ ∈ s.free, _root_.YangMills.Construction.TorusFields.supDist b₀.1 b.1 ≤ 3 * R.range) →
      ‖((s.frame b : imaginaryQuaternions) : ℍ[ℝ]) - ((w (topSite R n b.1) b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        N 0 * σ' * Real.exp (-(δ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) := by
    intro b hb hnear
    obtain ⟨b₀, hb₀, hd⟩ := hnear
    have hfr := ((c.frame_near R.params δ lam R.anchorRadius σA cg N c.params_admissible c.chain c.threshold_le).2
      R.depth R.range R.nextRange n s.coarse s.region C σ' c.rangesAdmissible hsit b hb
      (FreeBonds.parentBlock_not_mem_of_near_free c.large_range hoff hb₀ hd)).2
    have hl : StepMarks.minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth s.region s.coarse b =
        w (topSite R n b.1) b.2 := by
      unfold StepMarks.minimizerCoord minimizingBondCoordinate
      rw [hlc]
    rw [hl] at hfr
    exact hfr
  have hN0 := hN 0
  have he : 0 < Real.exp (-(δ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) := Real.exp_pos _
  have h3 : N 0 * σ' * Real.exp (-(δ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤
      N 0 * (2 * R.params.threshold) * Real.exp (-(δ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) := by gcongr
  exact ⟨σ', w, ⟨hw, hwc, H2, hσ0, hσ2, hreg, fun b hb hnear => ((key b hb hnear).trans h3).trans c.ballRadius_ge⟩,
    fun b hb => (key b (c.admissible.subset_chart hb) ⟨b, hb, by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega⟩).trans h3⟩
theorem toImaginary_toCoords (v : imaginaryQuaternions) :
    ColdStepAtMirrorFrames.toImaginary (toCoords v) = v := by apply _root_.YangMills.Construction.BlockTrees.toImaginary_toCoords <;> assumption
open Classical in
def shiftToMinimizer (s : ChartSetting R n)
    (w : (topFrame R n).Site (topFrame R n).depth → Fin 4 → imaginaryQuaternions) (B : Finset s.free) :
    FreeCoords s.free :=
  fun b => if b ∈ B then toCoords (minimizerOnTorus R n w b.1 - s.frame b.1) else 0
theorem coordinates_shiftToMinimizer {B : Finset s.free} {b : s.free} (hb : b ∈ B) :
    s.coordinates (shiftToMinimizer s w B) b.1 = minimizerOnTorus R n w b.1 := by
  classical
  unfold ChartSetting.coordinates
  rw [dif_pos b.2]
  have e : shiftToMinimizer s w B ⟨b.1, b.2⟩ = toCoords (minimizerOnTorus R n w b.1 - s.frame b.1) := if_pos hb
  rw [e, toImaginary_toCoords]
  abel
theorem norm_shiftToMinimizer_le {B : Finset s.free} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ b ∈ s.free, ‖((s.frame b : imaginaryQuaternions) : ℍ[ℝ]) -
      ((w (topSite R n b.1) b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ε) (b : s.free) :
    ‖shiftToMinimizer s w B b‖ ≤ ε := by
  classical
  unfold shiftToMinimizer
  split_ifs
  · rw [← norm_toImaginary, toImaginary_toCoords]
    have e : ((minimizerOnTorus R n w b.1 - s.frame b.1 : imaginaryQuaternions) : ℍ[ℝ]) =
        -(((s.frame b.1 : imaginaryQuaternions) : ℍ[ℝ]) -
          ((w (topSite R n b.1.1) b.1.2 : imaginaryQuaternions) : ℍ[ℝ])) := by
      unfold minimizerOnTorus
      push_cast
      abel
    rw [e, norm_neg]
    exact h b.1 b.2
  · simpa using hε
theorem inBalls_smul {η : FreeCoords s.free} (hη : ∀ b, ‖η b‖ ≤ R.ballRadius) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) : s.InBalls (θ • η) := by
  intro b
  show ‖((ColdStepAtMirrorFrames.toImaginary ((θ • η) b) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ R.ballRadius
  rw [norm_toImaginary, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
  have h1 := hη b
  have h2 := norm_nonneg (η b)
  nlinarith [hθ.2]
theorem abs_fderiv_costSum_sub_le (hS : StepCosts.SharesSumToAction) (c : s.ChainContext δ lam σA cg N)
    (hF : CostDerivatives.ActionDerivativeBounds R.params.coupling δ σA CA R.params.side) (hCA : 0 ≤ CA)
    (hK : CostDerivatives.AlignmentDerivativeBounds R.params.side Kf) (hKf : 0 ≤ Kf)
    (d : s.MinimizerData lam σA (N 0) σ' w) (hM : ChartTranslateBounds Cm) (hCm : 0 ≤ Cm) {η : FreeCoords s.free}
    (hη : ∀ b, ‖η b‖ ≤ R.ballRadius) (b : s.free) (X : QuaternionLogarithm.ImaginaryCoord) (hX : ‖X‖ = 1) {E : ℝ}
    (hE : ∀ b', costEntryBound s δ CA Cm Kf b' b ≤ E) :
    |fderiv ℝ s.costSum η (Pi.single b X) - fderiv ℝ s.costSum 0 (Pi.single b X)| ≤ E * ∑ b', ‖η b'‖ := by
  classical
  have hder : ∀ θ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun θ : ℝ => fderiv ℝ s.costSum (θ • η) (Pi.single b X))
      (fderiv ℝ (fderiv ℝ s.costSum) (θ • η) η (Pi.single b X)) (Set.Icc 0 1) θ := by
    intro θ hθ
    have hc := contDiffAt_costSum hS c hF (inBalls_smul (s := s) hη hθ)
    have h2 : DifferentiableAt ℝ (fderiv ℝ s.costSum) (θ • η) :=
      (hc.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
    have hline : HasDerivAt (fun θ : ℝ => θ • η) η θ := by
      simpa using (hasDerivAt_id θ).smul_const η
    have h3 := h2.hasFDerivAt.comp_hasDerivAt θ hline
    have h4 := h3.clm_apply (hasDerivAt_const θ (Pi.single b X : FreeCoords s.free))
    simp only [map_zero, add_zero] at h4
    exact h4.hasDerivWithinAt
  have hbound : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ s.costSum) (θ • η) η (Pi.single b X)‖ ≤ E * ∑ b', ‖η b'‖ := by
    intro θ hθ
    have hin := inBalls_smul (s := s) hη hθ
    set H := fderiv ℝ (fderiv ℝ s.costSum) (θ • η) with hH
    have e : H η (Pi.single b X) = ∑ b', H (Pi.single b' (η b')) (Pi.single b X) := by
      conv_lhs => rw [← Finset.univ_sum_single η]
      simp [map_sum, ContinuousLinearMap.sum_apply]
    rw [e, Real.norm_eq_abs, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
    have h1 := CostDerivatives.abs_bilinear_single_le H b' b
      (fun u u' hu hu' => abs_second_fderiv_costSum_single_le hS c hF hCA hK hKf d hM hCm hin b' b u u' hu hu')
      (η b') X
    rw [hX, mul_one] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (hE b') (norm_nonneg _))
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp) (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
  simpa [Real.norm_eq_abs] using h
theorem sum_norm_le_of_support {B : Finset s.free} {b : s.free} {η : FreeCoords s.free} {ε β : ℝ} {q : ℕ}
    (hε : 0 ≤ ε) (hβ : 0 < β)
    (hB : ∀ b' ∈ B, _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1 ≤ q) (h0 : ∀ b', b' ∉ B → η b' = 0) (h1 : ∀ b', ‖η b'‖ ≤ ε) :
    ∑ b', ‖η b'‖ ≤ ε * Real.exp (β * q) * (4 * (2 / (1 - Real.exp (-β / 4))) ^ 4) := by
  classical
  have hterm : ∀ b' : s.free, ‖η b'‖ ≤ ε * Real.exp (β * q) * Real.exp (-β * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1) := by
    intro b'
    by_cases hb : b' ∈ B
    · have h2 : (_root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1 : ℝ) ≤ q := by exact_mod_cast hB b' hb
      have h3 : 1 ≤ Real.exp (β * q) * Real.exp (-β * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith
      calc _ ≤ ε := h1 b'
        _ = ε * 1 := by ring
        _ ≤ ε * (Real.exp (β * q) * Real.exp (-β * _root_.YangMills.Construction.TorusFields.supDist b.1.1 b'.1.1)) := mul_le_mul_of_nonneg_left h3 hε
        _ = _ := by ring
    · rw [h0 b' hb, norm_zero]
      positivity
  refine (Finset.sum_le_sum fun b' _ => hterm b').trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_exp_neg_mul_supDist_subtype_le hβ b.1.1 s.free) (by positivity)
theorem isColdOn_minimizerChart (c : s.ChainContext δ lam σA cg N) (d : s.MinimizerData lam σA (N 0) σ' w) :
    LevelAction.IsColdOn σA s.sitesUnderRegion
      (TorusCharts.torusChart R.params.side (minimizerOnTorus R n w) s.coarse) := fun _ hp => by
  have hP := topFrame_period R n
  have h := d.cold _ (WideChartFloor.mem_innerPlaquettes_of_mem_plaquettesIn c hp)
  rw [WideChartFloor.chartedField_minimizer_eq c w, TopLevelSites.plaquetteDefect_readAtLevel_eq hP,
    TopLevelSites.toTorusSite_torusSiteInFrame hP] at h
  have hσ := c.params_admissible.σ_pos
  have hle := d.le_two_mul
  have hsig := c.threshold_le
  linarith
def regionBonds (s : ChartSetting R n) : Finset (TorusBond n) := open Classical in
  Finset.univ.filter fun e => e.1 ∈ s.region ∧ e.1 + TorusFields.unitStep n e.2 ∈ s.region
theorem nearBonds_subset_regionBonds (c : s.ChainContext δ lam σA cg N) : s.nearBonds ⊆ regionBonds s := by
  classical
  have hfit := c.params_admissible
  intro e he
  obtain ⟨b₀, hb₀, hbe⟩ := NearFits.mem_nearBonds.mp he
  have hbig := c.large_range.range_large
  have k1 : parentBlock R.params.side (TorusBlocks.blockCentreSite R.params.side e.1) ∈ s.region := by
    refine FreeBonds.parentBlock_mem_region_of_near_free c.admissible c.large_range hb₀ ?_
    have := NearFits.supDist_le_of_near_block c (b₀ := b₀) (Y := e.1) (by omega)
      (x := TorusBlocks.blockCentreSite R.params.side e.1) (by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega)
    omega
  have he2 : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b₀.1) (e.1 + TorusFields.unitStep n e.2) ≤ 17 := by
    have e1 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le e.1 e.2
    have e2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side b₀.1) e.1 (e.1 + TorusFields.unitStep n e.2)
    omega
  have k2 : parentBlock R.params.side (TorusBlocks.blockCentreSite R.params.side (e.1 + TorusFields.unitStep n e.2)) ∈ s.region := by
    refine FreeBonds.parentBlock_mem_region_of_near_free c.admissible c.large_range hb₀ ?_
    have := NearFits.supDist_le_of_near_block c (b₀ := b₀) (Y := e.1 + TorusFields.unitStep n e.2) (by omega)
      (x := TorusBlocks.blockCentreSite R.params.side (e.1 + TorusFields.unitStep n e.2)) (by rw [_root_.YangMills.Construction.TorusFields.supDist_self]; omega)
    omega
  rw [TorusBlocks.parentBlock_blockCentreSite hfit.L_odd] at k1 k2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k1, k2⟩
theorem blockEnergy_eq_action_add_alignment (hC : LumpContours.WholeCellCostEqualsMinimalAction)
    (hA : LumpContours.ActionAtLevelIsCutAction) (c : s.ChainContext δ lam σA cg N)
    (W : TorusField (n * R.params.side)) :
    blockEnergy R.params.coupling s.regionCells (topFrame R n).depth
        (readAtLevel (topFrame R n) (topFrame R n).depth W) s.topGaugeField =
      actionAtLevel R.params.coupling R.params.side R.depth s.sitesUnderRegion W +
        R.params.coupling * ∑ e ∈ regionBonds s,
          PlainAlignment.plainAlignmentDefect R.params.side e.1 e.2 (s.coarse e.1 e.2) W := by
  classical
  have hfit := c.params_admissible
  have hL : Odd (topFrame R n).blockSide := hfit.L_odd
  have ha : 0 ≤ R.params.coupling := by linarith [hfit.a_ge]
  have hn := topFrame_extent R n
  obtain ⟨h1, -, h3⟩ := hC (topFrame R n) R.params.coupling s.regionCells hL ha
  rw [← h3]
  unfold LumpContours.plainBlockEnergy
  rw [h1 (topFrame R n).depth (by simp [BlockFrame.top]), StepCostLocality.sitesOfCells_regionCells c]
  have hact := (hA R.params.coupling ha R.params.side hL n (topFrame R n) rfl hn).2 s.sitesUnderRegion W
  rw [hact]
  have hbonds : LumpContours.cutBonds s.regionCells =
      (regionBonds s).image fun e : TorusBond n =>
        (StepCosts.torusSiteInFrame (topFrame R n) (topFrame R n).top e.1, e.2) := by
    ext ⟨y, i⟩
    simp only [LumpContours.cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      Finset.mem_image, regionBonds, true_and, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨toTorusSite n y, i, ⟨(TopLevelSites.mem_cellsOfSites_iff hn).mp h1, ?_⟩,
        TopLevelSites.torusSiteInFrame_toTorusSite (TopLevelSites.period_top_of_extent hn) y, rfl⟩
      have := (TopLevelSites.mem_cellsOfSites_iff hn).mp h2
      rwa [TopLevelSites.toTorusSite_add (TopLevelSites.period_top_of_extent hn),
        TopLevelSites.toTorusSite_unitStep (TopLevelSites.period_top_of_extent hn)] at this
    · rintro ⟨Y, i', ⟨k1, k2⟩, rfl, rfl⟩
      refine ⟨(TopLevelSites.torusSiteInFrame_mem_cellsOfSites_iff hn).mpr k1, ?_⟩
      rw [TopLevelSites.mem_cellsOfSites_iff hn, TopLevelSites.toTorusSite_add (TopLevelSites.period_top_of_extent hn),
        TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn),
        TopLevelSites.toTorusSite_unitStep (TopLevelSites.period_top_of_extent hn)]
      exact k2
  have hinj : Set.InjOn (fun e : TorusBond n =>
      ((StepCosts.torusSiteInFrame (topFrame R n) (topFrame R n).top e.1, e.2) :
        (topFrame R n).Cell × Fin 4)) (regionBonds s) := by
    rintro ⟨Y, i⟩ _ ⟨Y', i'⟩ _ h
    have e1 : StepCosts.torusSiteInFrame (topFrame R n) (topFrame R n).top Y =
        StepCosts.torusSiteInFrame (topFrame R n) (topFrame R n).top Y' := congrArg Prod.fst h
    have e2 : i = i' := congrArg Prod.snd h
    have e3 := congrArg (toTorusSite n) e1
    rw [TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn),
      TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn)] at e3
    exact Prod.ext e3 e2
  rw [hbonds, Finset.sum_image hinj]
  have hfit1 : ∀ e : TorusBond n, blockFit (readAtLevel (topFrame R n) (topFrame R n).depth W) s.topGaugeField
      (StepCosts.torusSiteInFrame (topFrame R n) (topFrame R n).top e.1, e.2) =
        PlainAlignment.plainAlignmentDefect R.params.side e.1 e.2 (s.coarse e.1 e.2) W :=
    fun e => blockFit_readAtLevel hn W s.coarse e.1 e.2
  simp only [hfit1]
  rfl
theorem leftMovesAt_single_of_ne (b : s.free) (p : QuaternionLogarithm.ImaginaryCoord) (τ : ℝ)
    (W : TorusField (n * R.params.side)) {x : TorusSite (n * R.params.side)} {i : Fin 4}
    (hne : (x, i) ≠ b.1) : leftMovesAt s.free (τ • Pi.single b p) W x i = W x i := by
  classical
  rw [leftMovesAt_eq, moveAt_smul, moveAt_single, if_neg (Ne.symm hne), smul_zero, toImaginary_zero, expUnit_zero,
    one_mul]
theorem leftMovesAt_single_congr (b : s.free) (p : QuaternionLogarithm.ImaginaryCoord) (τ : ℝ)
    {W W' : TorusField (n * R.params.side)} {x : TorusSite (n * R.params.side)} {i : Fin 4}
    (h : W x i = W' x i) :
    leftMovesAt s.free (τ • Pi.single b p) W x i = leftMovesAt s.free (τ • Pi.single b p) W' x i := by
  rw [leftMovesAt_eq, leftMovesAt_eq, h]
theorem leftMovesAt_zero (W : TorusField (n * R.params.side)) :
    leftMovesAt s.free (0 : FreeCoords s.free) W = W := by
  funext x i
  rw [leftMovesAt_eq]
  unfold moveAt
  split_ifs <;> simp [toImaginary_zero, expUnit_zero]
theorem exists_alignment_along_single (c : s.ChainContext δ lam σA cg N) (b : s.free)
    (p : QuaternionLogarithm.ImaginaryCoord) {F W : TorusField (n * R.params.side)}
    (hbox : ∀ x i, _root_.YangMills.Construction.TorusFields.supDist x b.1.1 ≤ 10 * R.params.side → F x i = W x i) :
    ∃ K : ℝ, ∀ τ : ℝ, R.params.coupling * ∑ e ∈ regionBonds s,
        PlainAlignment.plainAlignmentDefect R.params.side e.1 e.2 (s.coarse e.1 e.2)
          (leftMovesAt s.free (τ • Pi.single b p) W) =
        K + s.nearFitSum (leftMovesAt s.free (τ • Pi.single b p) F) := by
  classical
  have hterm : ∀ e : TorusBond n, ∃ k : ℝ, ∀ τ : ℝ,
      PlainAlignment.plainAlignmentDefect R.params.side e.1 e.2 (s.coarse e.1 e.2)
        (leftMovesAt s.free (τ • Pi.single b p) W) =
      k + if e ∈ s.nearBonds then PlainAlignment.plainAlignmentDefect R.params.side e.1 e.2 (s.coarse e.1 e.2)
        (leftMovesAt s.free (τ • Pi.single b p) F) else 0 := by
    intro e
    by_cases ht : ∃ f ∈ contourIndex R.params.side, ∃ x ∈ contourWord R.params.side e.1 e.2 f, x.1 = b.1
    · obtain ⟨f₀, hf₀, x₀, hx₀, hxb⟩ := ht
      have h1 := NearFits.supDist_le_of_mem_contourWord c hf₀ hx₀
      rw [hxb] at h1
      have hnear : e ∈ s.nearBonds := by
        refine NearFits.mem_nearBonds.mpr ⟨b.1, b.2, ?_⟩
        have := NearFits.supDist_parentBlock_le_of_near c (Y := e.1) (x := b.1.1) (by omega)
        omega
      refine ⟨0, fun τ => ?_⟩
      rw [if_pos hnear, zero_add]
      have hm : plainContourAverage R.params.side e.1 e.2 (leftMovesAt s.free (τ • Pi.single b p) W) =
          plainContourAverage R.params.side e.1 e.2 (leftMovesAt s.free (τ • Pi.single b p) F) :=
        PlainAlignment.plainContourAverage_congr fun f hf x hx => by
          refine leftMovesAt_single_congr b p τ (hbox _ _ ?_).symm
          have h2 := NearFits.supDist_le_of_mem_contourWord c hf hx
          have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle x.1.1 (TorusBlocks.blockCentreSite R.params.side e.1) b.1.1
          have h4 := _root_.YangMills.Construction.TorusFields.supDist_comm x.1.1 (TorusBlocks.blockCentreSite R.params.side e.1)
          omega
      unfold PlainAlignment.plainAlignmentDefect
      rw [hm]
    · have hoff : ∀ (V : TorusField (n * R.params.side)) (τ : ℝ),
          plainContourAverage R.params.side e.1 e.2 (leftMovesAt s.free (τ • Pi.single b p) V) =
            plainContourAverage R.params.side e.1 e.2 V := fun V τ =>
          PlainAlignment.plainContourAverage_congr fun f hf x hx =>
            leftMovesAt_single_of_ne b p τ V fun h => ht ⟨f, hf, x, hx, h⟩
      by_cases hd : e ∈ s.nearBonds
      · refine ⟨PlainAlignment.plainAlignmentDefect R.params.side e.1 e.2 (s.coarse e.1 e.2) W -
          PlainAlignment.plainAlignmentDefect R.params.side e.1 e.2 (s.coarse e.1 e.2) F, fun τ => ?_⟩
        rw [if_pos hd]
        unfold PlainAlignment.plainAlignmentDefect
        rw [hoff W, hoff F]
        ring
      · refine ⟨PlainAlignment.plainAlignmentDefect R.params.side e.1 e.2 (s.coarse e.1 e.2) W, fun τ => ?_⟩
        rw [if_neg hd, add_zero]
        unfold PlainAlignment.plainAlignmentDefect
        rw [hoff W]
  choose k hk using hterm
  refine ⟨R.params.coupling * ∑ e ∈ regionBonds s, k e, fun τ => ?_⟩
  unfold ChartSetting.nearFitSum
  simp only [hk]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.mpr (nearBonds_subset_regionBonds c)]
  ring
theorem hasDerivAt_smul_line {f : FreeCoords s.free → ℝ} (hf : DifferentiableAt ℝ f 0) (v : FreeCoords s.free) :
    HasDerivAt (fun τ : ℝ => f (τ • v)) (fderiv ℝ f 0 v) 0 := by
  have hl : HasDerivAt (fun τ : ℝ => τ • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hf' : HasFDerivAt f (fderiv ℝ f 0) ((fun τ : ℝ => τ • v) 0) := by
    simpa using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt (0 : ℝ) hl
theorem abs_fderiv_costSum_le_of_minimizer_chart (hS : StepCosts.SharesSumToAction)
    (hC : LumpContours.WholeCellCostEqualsMinimalAction) (hA : LumpContours.ActionAtLevelIsCutAction)
    (c : s.ChainContext δ lam σA cg N)
    (hF : CostDerivatives.ActionDerivativeBounds R.params.coupling δ σA CA R.params.side)
    (hCA : 0 ≤ CA) (d : s.MinimizerData lam σA (N 0) σ' w) (hM : ChartTranslateBounds Cm) (hCm : 0 ≤ Cm)
    {η : FreeCoords s.free} (hη : s.InBalls η) (b : s.free) (X : QuaternionLogarithm.ImaginaryCoord) (hX : ‖X‖ = 1)
    {m : ℕ} (hm4 : 4 ≤ m) (hm10 : 10 * R.params.side ≤ 2 * m) (hmr : 2 * m ≤ 2 * R.range)
    (hbox : ∀ y i, _root_.YangMills.Construction.TorusFields.supDist y b.1.1 ≤ 2 * m →
      s.wideChartAt w η y i = TorusCharts.torusChart R.params.side (minimizerOnTorus R n w) s.coarse y i) {ε : ℝ}
    (hε : 3 * CA * Real.exp 1 * ((R.range : ℝ) + 1) ^ 4 * Real.exp (-δ * R.range / 16) ≤ ε) :
    |fderiv ℝ s.costSum η (Pi.single b X)| ≤ (ε + CA * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8)) * Cm := by
  classical
  have hε0 : 0 ≤ ε := le_trans (by positivity) hε
  set Wl := TorusCharts.torusChart R.params.side (minimizerOnTorus R n w) s.coarse with hWl
  obtain ⟨K, hu⟩ := costSum_eventuallyEq_moves hS c hη
  have h1 := (contDiffAt_regionActionMoves c hF hη).differentiableAt (by norm_num)
  have h3 := (contDiffAt_nearFitMoves c hη).differentiableAt (by norm_num)
  have hl := (FreeBondCharts.contDiffAt_leftMoveCoords s.free (s.coordinates η) η).differentiableAt (by norm_num)
  rw [fderiv_apply_of_eventuallyEq_sum hu (FreeBondCharts.leftMoveCoords_self _ _ η) h1 h3 hl,
    fderiv_leftMoveCoords_single]
  set x := fderiv ℝ (QuaternionLogarithm.chartTranslate (s.coordinates η b.1)) 0 X with hx
  have hx1 : ‖x‖ ≤ Cm := by
    have := (hM _ (norm_coordinates_le_one c d hη b)).1 X
    rwa [hX, mul_one] at this
  have hreg := FreeBonds.isRegularRegion_sitesUnderRegion c.params_admissible s (topFrame_extent R n) d.regular
  have hc3 : ContDiffThreeAt (actionAtLevel R.params.coupling R.params.side R.depth s.sitesUnderRegion) Wl :=
    (hF R.depth (n * R.params.side) c.sixtyFour_le_mul_side s.sitesUnderRegion _ hreg
      (isColdOn_minimizerChart c d)).1
  have hd3 : DifferentiableAt ℝ
      (alongMoves s.free (actionAtLevel R.params.coupling R.params.side R.depth s.sitesUnderRegion) Wl) 0 :=
    (contDiffAt_alongMoves s.free hc3).differentiableAt (by norm_num)
  set T₁ := fderiv ℝ (s.regionActionMoves η) 0 with hT₁
  set T₂ := fderiv ℝ (s.coreActionMoves w η) 0 with hT₂
  set T₃ := fderiv ℝ (alongMoves s.free (actionAtLevel R.params.coupling R.params.side R.depth s.sitesUnderRegion) Wl) 0
    with hT₃
  set Tf := fderiv ℝ (s.nearFitMoves η) 0 with hTf
  have hcrit : T₃ (Pi.single b x) + Tf (Pi.single b x) = 0 := by
    set v : FreeCoords s.free := Pi.single b x with hv
    have hA' := hasDerivAt_smul_line hd3 v
    have hL' := hasDerivAt_smul_line h3 v
    have hnear : ∀ y i, _root_.YangMills.Construction.TorusFields.supDist y b.1.1 ≤ 10 * R.params.side → s.chartedFieldAt η y i = Wl y i := by
      intro y i hy
      rw [← hbox y i (by omega)]
      exact (torusChart_wideCoords c w η (isNearFree_of_supDist_le b.2 (by omega))).symm
    obtain ⟨K₂, hfit⟩ := exists_alignment_along_single c b x hnear
    have hq : ∀ τ : ℝ, blockEnergy R.params.coupling s.regionCells (topFrame R n).depth
        (readAtLevel (topFrame R n) (topFrame R n).depth (leftMovesAt s.free (τ • Pi.single b x) Wl)) s.topGaugeField =
        actionAtLevel R.params.coupling R.params.side R.depth s.sitesUnderRegion
            (leftMovesAt s.free (τ • Pi.single b x) Wl) +
          (K₂ + s.nearFitSum (leftMovesAt s.free (τ • Pi.single b x) (s.chartedFieldAt η))) := by
      intro τ
      rw [blockEnergy_eq_action_add_alignment hC hA c, hfit τ]
    have hmin : IsLocalMin (fun τ : ℝ => actionAtLevel R.params.coupling R.params.side R.depth s.sitesUnderRegion
        (leftMovesAt s.free (τ • Pi.single b x) Wl) +
        (K₂ + s.nearFitSum (leftMovesAt s.free (τ • Pi.single b x) (s.chartedFieldAt η)))) 0 := by
      refine Filter.Eventually.of_forall fun τ => ?_
      have e := hq 0
      have e0 : (0 : ℝ) • (Pi.single b x : FreeCoords s.free) = 0 := zero_smul _ _
      simp only [e0, leftMovesAt_zero] at e
      simp only [e0, leftMovesAt_zero]
      rw [← e, ← hq τ, ← WideChartFloor.chartedField_minimizer_eq c w]
      exact d.isMinimizing.2.2 _
    have hsum : HasDerivAt (fun τ : ℝ => actionAtLevel R.params.coupling R.params.side R.depth s.sitesUnderRegion
        (leftMovesAt s.free (τ • Pi.single b x) Wl) +
        (K₂ + s.nearFitSum (leftMovesAt s.free (τ • Pi.single b x) (s.chartedFieldAt η)))) (T₃ v + (0 + Tf v)) 0 :=
      hA'.add ((hasDerivAt_const _ K₂).add hL')
    have := hmin.hasDerivAt_eq_zero hsum
    rw [zero_add] at this
    exact this
  have t12 : |(T₁ - T₂) (Pi.single b x)| ≤ ε * ‖x‖ :=
    CostDerivatives.abs_linear_single_le (T₁ - T₂) b (fun u hu => abs_fderiv_sub_le c hF hCA d hη hε b u hu) x
  have t23 : |(T₂ - T₃) (Pi.single b x)| ≤ CA * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8) * ‖x‖ := by
    refine CostDerivatives.abs_linear_single_le (T₂ - T₃) b (fun u hu => ?_) x
    simp only [ContinuousLinearMap.sub_apply]
    rw [hT₂, hT₃, fderiv_alongMoves (CostDerivatives.contDiffThreeAt_action_sitesUnderRegion c hF d hη),
      fderiv_alongMoves hc3]
    by_cases hsm : 2 * m + 2 < n * R.params.side
    · exact (hF R.depth (n * R.params.side) c.sixtyFour_le_mul_side s.sitesUnderRegion _ hreg
        (WideChartFloor.isColdOn_wideChartAt c d hη)).2.2 s.sitesUnderRegion Wl b.1.1 m hreg
        (isColdOn_minimizerChart c d) hsm (fun y _ => Iff.rfl) (fun y i hy _ => hbox y i hy) 1
        ![(b : TorusBond (n * R.params.side))]
        ![ColdStepAtMirrorFrames.toImaginary u] le_rfl (by norm_num) (areUnitVectors_single hu) (fun l => by
          fin_cases l
          simp only [Fin.zero_eta, Matrix.cons_val_zero, _root_.YangMills.Construction.TorusFields.supDist_self]
          omega)
    · have e : s.wideChartAt w η = Wl := by
        funext y i
        refine hbox y i ?_
        have h4 := _root_.YangMills.Construction.ClusterExpansionOfAStep.supDist_le_half_card y b.1.1
        omega
      rw [e, sub_self, abs_zero]
      positivity
  have e : T₁ (Pi.single b x) + Tf (Pi.single b x) =
      (T₁ - T₂) (Pi.single b x) + (T₂ - T₃) (Pi.single b x) + (T₃ (Pi.single b x) + Tf (Pi.single b x)) := by
    simp only [ContinuousLinearMap.sub_apply]
    ring
  rw [e, hcrit, add_zero]
  refine (abs_add_le _ _).trans ?_
  have hpos : 0 ≤ ε + CA * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8) := by positivity
  calc _ ≤ ε * ‖x‖ + CA * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8) * ‖x‖ := add_le_add t12 t23
    _ = (ε + CA * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8)) * ‖x‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hx1 hpos
theorem wideChartAt_shiftToMinimizer (c : s.ChainContext δ lam σA cg N) {st : SettingCore R n} {Y : TorusSite n}
    (hst : s.IsCoreOf st) (hoff : s.AwayFromCore st Y) (b : s.free) {m : ℕ} (hmr : m ≤ R.range)
    (hgeom : 8 * (R.params.side * (supDist Y (parentBlock R.params.side b.1.1) + 1) + 2 * m) ≤ R.range)
    {B : Finset s.free} (hB : ∀ b' : s.free, _root_.YangMills.Construction.TorusFields.supDist b'.1.1 b.1.1 ≤ 2 * m → b' ∈ B)
    (y : TorusSite (n * R.params.side)) (i : Fin 4) (hy : _root_.YangMills.Construction.TorusFields.supDist y b.1.1 ≤ 2 * m) :
    s.wideChartAt w (shiftToMinimizer s w B) y i =
      TorusCharts.torusChart R.params.side (minimizerOnTorus R n w) s.coarse y i := by
  classical
  have hL := c.params_admissible.L_odd
  show TorusCharts.torusChart R.params.side (s.wideCoords w (shiftToMinimizer s w B)) s.coarse y i =
    TorusCharts.torusChart R.params.side (minimizerOnTorus R n w) s.coarse y i
  by_cases ht : TorusCharts.IsBlockTreeBond R.params.side y i
  · have hc : ¬ TorusCharts.IsBlockEndBond R.params.side y i := fun h => ht.1 h
    unfold TorusCharts.torusChart
    rw [if_neg hc, if_neg hc, if_pos ht, if_pos ht]
  · refine TorusCharts.torusChart_congr s.coarse ?_
    have hn : s.IsNearFree (y, i) := isNearFree_of_supDist_le b.2 (by omega)
    obtain ⟨h1, h2⟩ := mem_chordBonds_of_isNearFree c hn ht
    unfold ChartSetting.wideCoords
    rw [if_pos ⟨h1, h2, hn⟩]
    have hnot : parentBlock R.params.side y ∉ s.storedBlockSet st := by
      intro hz
      have hcent : TorusBlocks.blockCentreSite R.params.side Y ∈ sitesInBlocks R.params.side {Y} := by
        unfold sitesInBlocks
        simp [TorusBlocks.parentBlock_blockCentreSite hL]
      have hyz : y ∈ sitesInBlocks R.params.side {parentBlock R.params.side y} := by
        unfold sitesInBlocks
        simp
      have h3 := hoff _ hz _ hcent _ hyz
      have h4 := TorusBlocks.supDist_le_mul_supDist_parentBlock_add_one hL
        (TorusBlocks.blockCentreSite R.params.side Y) b.1.1
      rw [TorusBlocks.parentBlock_blockCentreSite hL] at h4
      have h5 := _root_.YangMills.Construction.TorusFields.supDist_triangle (TorusBlocks.blockCentreSite R.params.side Y) b.1.1 y
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm b.1.1 y] at h5
      have h6 : 8 * _root_.YangMills.Construction.TorusFields.supDist (TorusBlocks.blockCentreSite R.params.side Y) y ≤ R.range := by omega
      have h7 : (8 : ℝ) * _root_.YangMills.Construction.TorusFields.supDist (TorusBlocks.blockCentreSite R.params.side Y) y ≤ R.range := by exact_mod_cast h6
      linarith
    have hfree : (y, i) ∈ s.free := by
      rw [hst.free_eq]
      unfold ChartSetting.freeBondsLeft
      refine Finset.mem_filter.mpr ⟨(mem_chartBonds_iff c _).mpr ht, fun h => hnot ?_, fun h => hnot h.1⟩
      unfold ChartSetting.storedBlockSet
      exact Finset.mem_union_left _ h
    exact coordinates_shiftToMinimizer (s := s) (w := w) (B := B) (b := ⟨(y, i), hfree⟩) (hB _ hy)
theorem abs_fderiv_costSum_zero_le (hS : StepCosts.SharesSumToAction)
    (hC : LumpContours.WholeCellCostEqualsMinimalAction) (hA : LumpContours.ActionAtLevelIsCutAction)
    (c : s.ChainContext δ lam σA cg N)
    (hF : CostDerivatives.ActionDerivativeBounds R.params.coupling δ σA CA R.params.side)
    (hCA : 0 ≤ CA) (hK : CostDerivatives.AlignmentDerivativeBounds R.params.side Kf) (hKf : 0 ≤ Kf)
    (hM : ChartTranslateBounds Cm) (hCm : 0 ≤ Cm)
    {st : SettingCore R n} {Y : TorusSite n} (hst : s.IsCoreOf st) (hoff : s.AwayFromCore st Y) (b : s.free)
    (X : QuaternionLogarithm.ImaginaryCoord) (hX : ‖X‖ = 1) {m : ℕ} (hm4 : 4 ≤ m)
    (hm10 : 10 * R.params.side ≤ 2 * m) (hmr : m ≤ R.range)
    (hgeom : 8 * (R.params.side * (supDist Y (parentBlock R.params.side b.1.1) + 1) + 2 * m) ≤ R.range)
    {ε ε₁ E β : ℝ}
    (hε : 3 * CA * Real.exp 1 * ((R.range : ℝ) + 1) ^ 4 * Real.exp (-δ * R.range / 16) ≤ ε)
    (hε₁ : N 0 * (2 * R.params.threshold) * Real.exp (-(δ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤ ε₁)
    (hε₁ρ : ε₁ ≤ R.ballRadius) (hβ : 0 < β)
    (hE : ∀ b', costEntryBound s δ CA Cm Kf b' b ≤ E) (hE0 : 0 ≤ E) :
    |fderiv ℝ s.costSum 0 (Pi.single b X)| ≤
      E * (ε₁ * Real.exp (β * ((2 * m : ℕ) : ℝ)) * (4 * (2 / (1 - Real.exp (-β / 4))) ^ 4)) +
        (ε + CA * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8)) * Cm := by
  classical
  obtain ⟨σ', w, d, htight⟩ := exists_minimizerData_frame_close c
  have hε₁0 : 0 ≤ ε₁ := by
    refine le_trans ?_ hε₁
    have hN0 := c.chain.2.2.2.2.2.2.2.1 0
    have hσ := c.params_admissible.σ_pos
    positivity
  set B : Finset s.free := Finset.univ.filter fun b' => _root_.YangMills.Construction.TorusFields.supDist b'.1.1 b.1.1 ≤ 2 * m with hB
  set η : FreeCoords s.free := shiftToMinimizer s w B with hη
  have hsize : ∀ b', ‖η b'‖ ≤ ε₁ := fun b' =>
    norm_shiftToMinimizer_le hε₁0 (fun b₁ hb₁ => (htight b₁ hb₁).trans hε₁) b'
  have hsmall : ∀ b', ‖η b'‖ ≤ R.ballRadius := fun b' => (hsize b').trans hε₁ρ
  have hin : s.InBalls η := by
    have := inBalls_smul (s := s) hsmall (θ := 1) (by simp)
    simpa using this
  have h1 := abs_fderiv_costSum_sub_le hS c hF hCA hK hKf d hM hCm hsmall b X hX hE
  have h2 := abs_fderiv_costSum_le_of_minimizer_chart hS hC hA c hF hCA d hM hCm hin b X hX hm4 hm10 (by omega)
    (wideChartAt_shiftToMinimizer c hst hoff b hmr hgeom
      (fun b' hb' => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'⟩)) hε
  have h3 : ∑ b', ‖η b'‖ ≤
      ε₁ * Real.exp (β * ((2 * m : ℕ) : ℝ)) * (4 * (2 / (1 - Real.exp (-β / 4))) ^ 4) := by
    refine sum_norm_le_of_support (B := B) (b := b) hε₁0 hβ (fun b' hb' => ?_) (fun b' hb' => ?_) hsize
    · rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
      exact (Finset.mem_filter.mp hb').2
    · show (if b' ∈ B then _ else 0) = 0
      rw [if_neg hb']
  have h4 := mul_le_mul_of_nonneg_left h3 hE0
  have h5 := abs_sub_abs_le_abs_sub (fderiv ℝ s.costSum 0 (Pi.single b X)) (fderiv ℝ s.costSum η (Pi.single b X))
  rw [abs_sub_comm (fderiv ℝ s.costSum 0 (Pi.single b X))] at h5
  linarith
theorem le_clusterRange_pow {x : ℝ} (hx : 0 ≤ x) : x ≤ (clusterRange x : ℝ) ^ 100 := by
  have h1 : x ^ ((1 : ℝ) / 100) ≤ (clusterRange x : ℝ) := by
    unfold clusterRange
    exact Nat.le_ceil _
  have h2 : (x ^ ((1 : ℝ) / 100)) ^ 100 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  calc x = (x ^ ((1 : ℝ) / 100)) ^ 100 := h2.symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) h1 100
theorem le_clusterRange_of_pow_le {q : ℕ} {x : ℝ} (hx : (q : ℝ) ^ 100 ≤ x) : q ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.le_clusterRange <;> assumption
theorem exists_pow_mul_exp_neg_le_one {k : ℝ} (A : ℝ) (hk : 0 < k) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → ((r : ℝ) + 1) ^ 104 * (A * Real.exp (-(k * r))) ≤ 1 := by
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 104
  have hx : Filter.Tendsto (fun r : ℕ => k * ((r : ℝ) + 1)) Filter.atTop Filter.atTop := by
    have h2 : Filter.Tendsto (fun r : ℕ => (r : ℝ) + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact h2.const_mul_atTop hk
  have h4 := h1.comp hx
  have h5 := h4.const_mul (A * (1 / k) ^ 104 * Real.exp k)
  rw [mul_zero] at h5
  have h6 : ∀ᶠ r : ℕ in Filter.atTop, (A * (1 / k) ^ 104 * Real.exp k) *
      (((fun x : ℝ => x ^ 104 * Real.exp (-x)) ∘ fun r : ℕ => k * ((r : ℝ) + 1)) r) < 1 :=
    (tendsto_order.1 h5).2 1 one_pos
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp h6
  refine ⟨r₀, fun r hr => ?_⟩
  have h7 := hr₀ r hr
  simp only [Function.comp] at h7
  have e : (A * (1 / k) ^ 104 * Real.exp k) * ((k * ((r : ℝ) + 1)) ^ 104 * Real.exp (-(k * ((r : ℝ) + 1)))) =
      ((r : ℝ) + 1) ^ 104 * (A * Real.exp (-(k * r))) := by
    have h8 : Real.exp k * Real.exp (-(k * ((r : ℝ) + 1))) = Real.exp (-(k * r)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h9 : (1 / k) ^ 104 * (k * ((r : ℝ) + 1)) ^ 104 = ((r : ℝ) + 1) ^ 104 := by
      rw [← mul_pow]
      congr 1
      field_simp
    calc _ = A * ((1 / k) ^ 104 * (k * ((r : ℝ) + 1)) ^ 104) *
          (Real.exp k * Real.exp (-(k * ((r : ℝ) + 1)))) := by ring
      _ = _ := by rw [h8, h9]; ring
  rw [e] at h7
  exact h7.le
theorem exists_mul_exp_neg_le {k A τ : ℝ} (hk : 0 < k) (hτ : 0 < τ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → A * Real.exp (-(k * (q : ℝ))) ≤ τ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.exists_exp_tail_le <;> assumption
end FrameSlope
set_option maxHeartbeats 2000000 in
open FrameSlope in
theorem frameSlopeBound_holds (hS : StepCosts.SharesSumToAction)
    (hC : LumpContours.WholeCellCostEqualsMinimalAction) (hA : LumpContours.ActionAtLevelIsCutAction)
    (hAct : LevelAction.ActionSmoothAlongMoves) (hReg : LumpContours.ComplementOfThickenedLumpsRegular)
    (hFr : StepFrames.FrameNearMinimizer) :
    FrameSlopeBound := by
  classical
  obtain ⟨Cm₀, hCm₀, hM₀⟩ := QuaternionLogarithm.exists_chartTranslate_deriv_bounds
  intro T hT
  have hchain := hT.chain
  have hδ : 0 < T.δ₁ := hchain.1
  have hN0 := hchain.2.2.2.2.2.2.2.1 0
  have hσ := hT.σ_pos
  have ha0 : 0 ≤ T.coupling := by linarith [hT.a_ge]
  obtain ⟨CA, hCA, hF⟩ := hAct T.coupling T.δ₁ T.side T.lam T.ρA T.σA T.cg T.N (by linarith [hT.a_ge]) hT.L_odd hchain
  obtain ⟨Kf, hKf, hK⟩ := PlainAlignment.exists_mixedDeriv_plainAlignmentDefect_bound hT.L_odd
  set Ef := T.coupling * (4 * 13 ^ 4 * Kf) with hEf
  have hEf0 : 0 ≤ Ef := by positivity
  set E := Cm₀ ^ 2 * (CA + Ef) + Cm₀ * (CA + Ef) with hE
  have hE0 : 0 ≤ E := by positivity
  set β := T.δ₁ / 32 with hβ
  have hβ0 : 0 < β := by positivity
  set Kβ := 4 * (2 / (1 - Real.exp (-β / 4)) : ℝ) ^ 4 with hKβ
  have hKβ0 : 0 ≤ Kβ := by
    have hx : Real.exp (-β / 4) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have hx' : 0 < 1 - Real.exp (-β / 4) := by linarith
    rw [hKβ]
    positivity
  set A₀ := E * (T.N 0 * (2 * T.threshold) * Real.exp T.δ₁ * Kβ) +
    (3 * CA * Real.exp 1 + CA * Real.exp T.δ₁) * Cm₀ with hA₀
  have hA₀0 : 0 ≤ A₀ := by positivity
  set k := T.δ₁ / 2 ^ 12 with hk
  have hk0 : 0 < k := by positivity
  obtain ⟨r₁, hr₁⟩ := exists_pow_mul_exp_neg_le_one A₀ hk0
  obtain ⟨q₀, hq₀⟩ := exists_mul_exp_neg_le (k := T.δ₁) (A := T.N 0 * (2 * T.threshold)) (τ := T.threshold / 64) hδ
    (by positivity)
  set r₀ : ℕ := r₁ + 2 ^ 11 * q₀ + 2 ^ 12 * T.side + 2 ^ 16 with hr₀
  refine ⟨1, max T.floorMin ((r₀ : ℝ) ^ 100), one_pos, fun y hy R hR n _ hn s hs st Y hst _ hoff b X hX hbY => ?_⟩
  have hyT : T.floorMin ≤ y := (le_max_left _ _).trans hy
  have hyr : (r₀ : ℝ) ^ 100 ≤ R.coupling := ((le_max_right _ _).trans hy).trans hR.le_coupling
  have hrr : r₀ ≤ R.range := le_clusterRange_of_pow_le hyr
  have hx0 : 0 ≤ R.coupling := le_trans (by positivity) hyr
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hT.fits y hyT
  have hσR : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hLR : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have haR : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
  have hnR : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have hρR : R.ballRadius = T.threshold / 64 := by
    unfold StepSetup.ballRadius
    rw [hσR]
  have hgap : T.N 0 * (2 * T.threshold) * Real.exp (-(T.δ₁ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤ T.threshold / 64 :=
    hq₀ _ ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega))
  have hctx : s.ChainContext T.δ₁ T.lam T.σA T.cg T.N :=
    { admissible := hs
      params_admissible := hfit
      large_range := ⟨by rw [hLR]; omega, hR.isStep.2.2⟩
      n₀_le := by rw [hnR]; exact hn
      chain := by
        rw [hR.params_eq, hR.anchorRadius_eq]
        exact hchain
      baseDepth_pos := by
        have := hT.J₀_ge
        have h2 : R.params.baseDepth = T.baseDepth := by rw [hR.params_eq]; rfl
        omega
      threshold_le := by
        rw [hσR]
        exact hT.σ_le
      anchor_ge := by
        have h1 := hT.ρ_le
        rw [hR.anchorRadius_eq, hρR, hσR]
        have h2 : T.ballRadius = T.threshold / 64 := rfl
        rw [h2] at h1
        linarith
      ballRadius_ge := by
        rw [hρR, hσR]
        exact hgap
      complement_regular := hReg
      frame_near := hFr }
  have hF' : CostDerivatives.ActionDerivativeBounds R.params.coupling T.δ₁ T.σA CA R.params.side := by
    rw [hR.params_eq]
    exact hF
  have hK' : CostDerivatives.AlignmentDerivativeBounds R.params.side Kf := by
    rw [hLR]
    exact hK
  have hentry : ∀ b', costEntryBound s T.δ₁ CA Cm₀ Kf b' b ≤ E := by
    intro b'
    have he : Real.exp (-T.δ₁ * TorusFields.supDist b'.1.1 b.1.1) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h0 : (0 : ℝ) ≤ TorusFields.supDist b'.1.1 b.1.1 := Nat.cast_nonneg _
      have h1 := mul_nonneg hδ.le h0
      linarith
    have hrow : CostDerivatives.alignmentExpansionBound R.params.side R.params.coupling Kf
        (b' : TorusFields.TorusBond (n * R.params.side)) b ≤ Ef := by
      unfold CostDerivatives.alignmentExpansionBound
      split_ifs
      · rw [haR]
      · exact hEf0
    unfold costEntryBound
    have h1 : CA * Real.exp (-T.δ₁ * TorusFields.supDist b'.1.1 b.1.1) ≤ CA := mul_le_of_le_one_right hCA.le he
    have h2 : Cm₀ ^ 2 * (CA * Real.exp (-T.δ₁ * TorusFields.supDist b'.1.1 b.1.1) +
        CostDerivatives.alignmentExpansionBound R.params.side R.params.coupling Kf
          (b' : TorusFields.TorusBond (n * R.params.side)) b) ≤ Cm₀ ^ 2 * (CA + Ef) := by gcongr
    have h3 : (if b' = b then Cm₀ * (CA + R.params.coupling * (4 * 13 ^ 4 * Kf)) else 0) ≤ Cm₀ * (CA + Ef) := by
      split_ifs
      · rw [haR]
      · positivity
    rw [hE]
    exact add_le_add h2 h3
  set m : ℕ := R.range / 2 ^ 8 with hm
  set m₀ : ℕ := R.range / 2 ^ 11 with hm₀
  have hm1 : R.range < 2 ^ 8 * (m + 1) := by omega
  have hm2 : 2 ^ 8 * m ≤ R.range := by omega
  have hm01 : R.range < 2 ^ 11 * (m₀ + 1) := by omega
  have hLr : 2 ^ 12 * R.params.side + 2 ^ 16 ≤ R.range := by
    rw [hLR]
    omega
  have hm4 : 4 ≤ m := by omega
  have hm10 : 10 * R.params.side ≤ 2 * m := by omega
  have hdY : 16 * (R.params.side * TorusFields.supDist Y (parentBlock R.params.side b.1.1)) ≤ R.range := by
    have h1 : (16 * R.params.side : ℝ) * TorusFields.supDist (parentBlock R.params.side b.1.1) Y ≤ R.range := hbY
    rw [TorusFields.supDist_comm (parentBlock R.params.side b.1.1) Y] at h1
    have h2 : ((16 * (R.params.side * TorusFields.supDist Y (parentBlock R.params.side b.1.1)) : ℕ) : ℝ) ≤
        R.range := by
      push_cast
      linarith
    exact_mod_cast h2
  have hgeom : 8 * (R.params.side * (TorusFields.supDist Y (parentBlock R.params.side b.1.1) + 1) + 2 * m) ≤
      R.range := by
    have e : R.params.side * (TorusFields.supDist Y (parentBlock R.params.side b.1.1) + 1) =
        R.params.side * TorusFields.supDist Y (parentBlock R.params.side b.1.1) + R.params.side := by ring
    rw [e]
    omega
  have hcore := abs_fderiv_costSum_zero_le hS hC hA hctx hF' hCA.le hK' hKf hM₀ hCm₀.le hst hoff b X hX hm4 hm10
    (by omega) hgeom le_rfl le_rfl hctx.ballRadius_ge hβ0 hentry hE0
  rw [hσR, ← hKβ] at hcore
  have hρ0 : 0 ≤ R.ballRadius := by
    rw [hρR]
    positivity
  have hz : s.InBalls (0 : StepSettings.FreeCoords s.free) := by
    have := inBalls_smul (s := s) (η := (0 : StepSettings.FreeCoords s.free)) (fun b' => by simpa using hρ0)
      (θ := 0) (by simp)
    simpa using this
  have hcd : DifferentiableAt ℝ s.costSum 0 := (contDiffAt_costSum hS hctx hF' hz).differentiableAt (by norm_num)
  have hline := hasDerivAt_smul_line hcd (Pi.single b X)
  have eline : (fun τ : ℝ => s.totalCost (Function.update 0 b (τ • X))) =
      fun τ : ℝ => s.costSum (τ • Pi.single b X) := by
    funext τ
    have e : (τ • Pi.single b X : StepSettings.FreeCoords s.free) =
        Function.update (0 : StepSettings.FreeCoords s.free) b (τ • X) := by
      rw [← Pi.single_smul]
      rfl
    rw [e]
    simp only [StepSettings.ChartSetting.totalCost, StepSettings.ChartSetting.blockCostAt,
      StepSettings.ChartSetting.costSum]
  rw [eline, hline.deriv]
  set D := |fderiv ℝ s.costSum 0 (Pi.single b X)| with hD
  set u : ℝ := (R.range : ℝ) with hu
  have hu0 : 0 ≤ u := by positivity
  have hm1' : u < 2 ^ 8 * ((m : ℝ) + 1) := by
    have : ((R.range : ℕ) : ℝ) < ((2 ^ 8 * (m + 1) : ℕ) : ℝ) := by exact_mod_cast hm1
    push_cast at this
    norm_num at this ⊢
    exact this
  have hm2' : 2 ^ 8 * (m : ℝ) ≤ u := by
    have : ((2 ^ 8 * m : ℕ) : ℝ) ≤ ((R.range : ℕ) : ℝ) := by exact_mod_cast hm2
    push_cast at this
    norm_num at this ⊢
    exact this
  have hm01' : u < 2 ^ 11 * ((m₀ : ℝ) + 1) := by
    have : ((R.range : ℕ) : ℝ) < ((2 ^ 11 * (m₀ + 1) : ℕ) : ℝ) := by exact_mod_cast hm01
    push_cast at this
    norm_num at this ⊢
    exact this
  set G := Real.exp (-(k * u)) with hG
  have hG0 : 0 < G := Real.exp_pos _
  have hex1 : Real.exp (-(T.δ₁ * (m₀ : ℝ))) * Real.exp (β * ((2 * m : ℕ) : ℝ)) ≤ Real.exp T.δ₁ * G := by
    rw [hG, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have a1 : u / 2 ^ 11 - 1 ≤ (m₀ : ℝ) := by linarith
    have a2 : ((2 * m : ℕ) : ℝ) ≤ u / 2 ^ 7 := by
      push_cast
      linarith
    have b1 := mul_le_mul_of_nonneg_left a1 hδ.le
    have b2 := mul_le_mul_of_nonneg_left a2 hβ0.le
    rw [hβ] at b2 ⊢
    rw [hk]
    linarith
  have hex2 : Real.exp (-T.δ₁ * R.range / 16) ≤ G := by
    rw [hG]
    apply Real.exp_le_exp.mpr
    rw [hk]
    have : 0 ≤ T.δ₁ * u := by positivity
    show -T.δ₁ * u / 16 ≤ -(T.δ₁ / 2 ^ 12 * u)
    linarith
  have hex3 : Real.exp (-T.δ₁ * m / 8) ≤ Real.exp T.δ₁ * G := by
    rw [hG, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have a1 : u / 2 ^ 8 - 1 ≤ (m : ℝ) := by linarith
    have b1 := mul_le_mul_of_nonneg_left a1 hδ.le
    rw [hk]
    have : 0 ≤ T.δ₁ * u := by positivity
    linarith
  have hP : 1 ≤ (u + 1) ^ 4 := one_le_pow₀ (by linarith)
  have hmu : (m : ℝ) + 1 ≤ u + 1 := by
    have : (0 : ℝ) ≤ m := by positivity
    linarith
  have hmu4 : ((m : ℝ) + 1) ^ 4 ≤ (u + 1) ^ 4 := pow_le_pow_left₀ (by positivity) hmu 4
  have t1 : E * (T.N 0 * (2 * T.threshold) * Real.exp (-(T.δ₁ * (m₀ : ℝ))) * Real.exp (β * ((2 * m : ℕ) : ℝ)) * Kβ) ≤
      (u + 1) ^ 4 * (E * (T.N 0 * (2 * T.threshold) * Real.exp T.δ₁ * Kβ) * G) := by
    calc _ = (E * (T.N 0 * (2 * T.threshold) * Kβ)) *
          (Real.exp (-(T.δ₁ * (m₀ : ℝ))) * Real.exp (β * ((2 * m : ℕ) : ℝ))) := by ring
      _ ≤ (E * (T.N 0 * (2 * T.threshold) * Kβ)) * (Real.exp T.δ₁ * G) :=
        mul_le_mul_of_nonneg_left hex1 (by positivity)
      _ = 1 * (E * (T.N 0 * (2 * T.threshold) * Real.exp T.δ₁ * Kβ) * G) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hP (by positivity)
  have t2 : 3 * CA * Real.exp 1 * (u + 1) ^ 4 * Real.exp (-T.δ₁ * R.range / 16) * Cm₀ ≤
      (u + 1) ^ 4 * (3 * CA * Real.exp 1 * Cm₀ * G) := by
    calc _ = ((u + 1) ^ 4 * (3 * CA * Real.exp 1 * Cm₀)) * Real.exp (-T.δ₁ * R.range / 16) := by ring
      _ ≤ ((u + 1) ^ 4 * (3 * CA * Real.exp 1 * Cm₀)) * G :=
        mul_le_mul_of_nonneg_left hex2 (by positivity)
      _ = _ := by ring
  have t3 : CA * ((m : ℝ) + 1) ^ 4 * Real.exp (-T.δ₁ * m / 8) * Cm₀ ≤
      (u + 1) ^ 4 * (CA * Real.exp T.δ₁ * Cm₀ * G) := by
    calc _ = (CA * Cm₀) * (((m : ℝ) + 1) ^ 4 * Real.exp (-T.δ₁ * m / 8)) := by ring
      _ ≤ (CA * Cm₀) * ((u + 1) ^ 4 * (Real.exp T.δ₁ * G)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hmu4 hex3 (Real.exp_pos _).le (by positivity)) (by positivity)
      _ = _ := by ring
  have hDle : D ≤ (u + 1) ^ 4 * (A₀ * G) := by
    have e : (u + 1) ^ 4 * (A₀ * G) = (u + 1) ^ 4 * (E * (T.N 0 * (2 * T.threshold) * Real.exp T.δ₁ * Kβ) * G) +
        (u + 1) ^ 4 * (3 * CA * Real.exp 1 * Cm₀ * G) + (u + 1) ^ 4 * (CA * Real.exp T.δ₁ * Cm₀ * G) := by
      rw [hA₀]
      ring
    rw [e]
    have e2 : (3 * CA * Real.exp 1 * ((R.range : ℝ) + 1) ^ 4 * Real.exp (-T.δ₁ * R.range / 16) +
        CA * ((m : ℝ) + 1) ^ 4 * Real.exp (-T.δ₁ * m / 8)) * Cm₀ =
        3 * CA * Real.exp 1 * (u + 1) ^ 4 * Real.exp (-T.δ₁ * R.range / 16) * Cm₀ +
          CA * ((m : ℝ) + 1) ^ 4 * Real.exp (-T.δ₁ * m / 8) * Cm₀ := by ring
    rw [e2] at hcore
    have e3 : ((R.range / 2 ^ 11 : ℕ) : ℝ) = (m₀ : ℝ) := rfl
    rw [e3] at hcore
    linarith
  have hxr : R.coupling ≤ (u + 1) ^ 100 :=
    (le_clusterRange_pow hx0).trans (pow_le_pow_left₀ hu0 (by linarith) 100)
  have hD0 : 0 ≤ D := abs_nonneg _
  have hfin := hr₁ R.range (by omega)
  calc R.coupling * D ≤ (u + 1) ^ 100 * ((u + 1) ^ 4 * (A₀ * G)) :=
        mul_le_mul hxr hDle hD0 (by positivity)
    _ = (u + 1) ^ 104 * (A₀ * G) := by ring
    _ ≤ 1 := hfin
end YangMills.Construction.ClusterExpansionOfAStep
end
