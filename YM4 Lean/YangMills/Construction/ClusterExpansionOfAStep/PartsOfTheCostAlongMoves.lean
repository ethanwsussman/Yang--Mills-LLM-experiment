import YangMills.Construction.ClusterExpansionOfAStep.FloorAtAWideChart
import YangMills.Construction.ClusterExpansionOfAStep.SumsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages FiniteDifferences LumpContours HoleSavings TorusFields LevelAction StepSettings RenormalizationStepParameters
  TorusLumps TorusContours TorusBlocks PlainAlignment StepCosts WideCharts WideChartFloor FreeBonds SettingFits
  NearFits QuaternionLogarithm
def CostDerivatives.ActionDerivativeBounds (a δ σA C : ℝ) (L : ℕ) : Prop :=
  ∀ (t n : ℕ) [NeZero n], 64 ≤ n → ∀ (X : Finset (TorusSite n)) (W : TorusField n),
    IsRegularRegion X 1024 → IsColdOn σA X W →
      ContDiffThreeAt (actionAtLevel a L t X) W ∧
      (∀ (k : ℕ) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors Xs →
        |mixedDeriv (actionAtLevel a L t X) W c Xs| ≤ C * Real.exp (-δ * bondListSpread c)) ∧
      ∀ (X' : Finset (TorusSite n)) (W' : TorusField n) (z : TorusSite n) (m : ℕ),
        IsRegularRegion X' 1024 → IsColdOn σA X' W' →
        2 * m + 2 < n → (∀ y, _root_.YangMills.Construction.TorusFields.supDist y z ≤ 2 * m → (y ∈ X ↔ y ∈ X')) →
        (∀ y i, _root_.YangMills.Construction.TorusFields.supDist y z ≤ 2 * m → _root_.YangMills.Construction.TorusFields.supDist (y + TorusFields.unitStep n i) z ≤ 2 * m → W y i = W' y i) →
        ∀ (k : ℕ) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 2 →
          AreUnitVectors Xs →
          (∀ l, 4 * _root_.YangMills.Construction.TorusFields.supDist (c l).1 z + 4 ≤ m) →
          |mixedDeriv (actionAtLevel a L t X) W c Xs - mixedDeriv (actionAtLevel a L t X') W' c Xs| ≤
            C * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8)
def CostDerivatives.AlignmentDerivativeBounds (L : ℕ) (Kf : ℝ) : Prop :=
  ∀ (n : ℕ) [NeZero n] (Y : TorusSite n) (i : Fin 4) (v : UnitQuaternion) (W : TorusField (n * L)),
    1 / 2 ≤ ‖plainContourAverage L Y i W‖ →
    (∀ (c : Fin 1 → TorusBond (n * L)) (Xs : Fin 1 → imaginaryQuaternions), AreUnitVectors Xs →
      |mixedDeriv (plainAlignmentDefect L Y i v) W c Xs| ≤ Kf) ∧
    (∀ (c : Fin 2 → TorusBond (n * L)) (Xs : Fin 2 → imaginaryQuaternions), AreUnitVectors Xs →
      |mixedDeriv (plainAlignmentDefect L Y i v) W c Xs| ≤ Kf)
variable {R : StepSetup} {n : ℕ} [NeZero n] {s : ChartSetting R n} {δ lam σA cg : ℝ} {N : ℕ → ℝ}
theorem StepSettings.ChartSetting.ChainContext.sixtyFour_le_mul_side (c : s.ChainContext δ lam σA cg N) :
    64 ≤ n * R.params.side := by
  have h3 := c.params_admissible.n₀_ge
  have h4 := c.n₀_le
  have h5 := c.params_admissible.L_odd.pos
  nlinarith
namespace CostDerivatives
theorem contDiffThreeAt_action_coolRegion (c : s.ChainContext δ lam σA cg N) {CA : ℝ}
    (hF : ActionDerivativeBounds R.params.coupling δ σA CA R.params.side)
    {η₀ : FreeCoords s.free} (hη₀ : s.InBalls η₀) :
    ContDiffThreeAt (actionAtLevel R.params.coupling R.params.side R.depth s.coolRegion) (s.chartedFieldAt η₀) :=
  (hF R.depth (n * R.params.side) c.sixtyFour_le_mul_side s.coolRegion _
    (isRegularRegion_coolRegion c.complement_regular c.params_admissible s) (isColdOn_chartedFieldAt c hη₀)).1
theorem contDiffThreeAt_action_sitesUnderRegion (c : s.ChainContext δ lam σA cg N) {CA : ℝ}
    (hF : ActionDerivativeBounds R.params.coupling δ σA CA R.params.side) {σ' : ℝ}
    {w : (topFrame R n).Site (topFrame R n).depth → Fin 4 → imaginaryQuaternions}
    (hmin : s.MinimizerData lam σA (N 0) σ' w) {η₀ : FreeCoords s.free}
    (hη₀ : s.InBalls η₀) :
    ContDiffThreeAt (actionAtLevel R.params.coupling R.params.side R.depth s.sitesUnderRegion) (s.wideChartAt w η₀) :=
  (hF R.depth (n * R.params.side) c.sixtyFour_le_mul_side s.sitesUnderRegion _
    (isRegularRegion_sitesUnderRegion c.params_admissible s (topFrame_extent R n) hmin.regular)
    (isColdOn_wideChartAt c hmin hη₀)).1
theorem half_le_norm_plainContourAverage (c : s.ChainContext δ lam σA cg N) {η₀ : FreeCoords s.free}
    (hη₀ : s.InBalls η₀) {e : TorusBond n} (he : e ∈ s.nearBonds) :
    1 / 2 ≤ ‖plainContourAverage R.params.side e.1 e.2 (s.chartedFieldAt η₀)‖ := by
  classical
  have hadm := c.params_admissible
  have h2 := c.two_le
  have hbases : IsBaseChoice R.params.baseDepth (stepHotLumps R.params s.fine) s.bases :=
    c.admissible.isBaseChoice
  obtain ⟨b₀, hb₀, hbd⟩ := NearFits.mem_nearBonds.mp he
  have hsites : torusHotSites R.params (s.field η₀) = torusHotSites R.params s.fine := by
    unfold torusHotSites
    rw [c.admissible.hotLumps_eq η₀ hη₀]
  have hd2 : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b₀.1) (e.1 + TorusFields.unitStep n e.2) ≤ 17 := by
    have e1 := _root_.YangMills.Construction.TorusFields.supDist_add_unitStep_le e.1 e.2
    have e2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock R.params.side b₀.1) e.1 (e.1 + TorusFields.unitStep n e.2)
    omega
  have hd1 : _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side b₀.1) e.1 ≤ 17 := by omega
  have l1 := nearbyLumps_stepHotLumps_eq_empty hadm h2 c.admissible c.large_range hsites hb₀ hd1
  have l3 := nearbyLumps_stepHotLumps_eq_empty hadm h2 c.admissible c.large_range hsites hb₀ hd2
  have k1 := nearbyLumps_stepHotLumps_eq_empty hadm h2 c.admissible c.large_range rfl hb₀ hd1
  have k3 := nearbyLumps_stepHotLumps_eq_empty hadm h2 c.admissible c.large_range rfl hb₀ hd2
  have hb1 := (hbases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 e.1)).1 (Or.inl k1)
  have hb2 := (hbases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (e.1 + TorusFields.unitStep n e.2))).1 (Or.inl k3)
  have hm := contourMean_eq_plainContourAverage_gaugeAt hadm c.baseDepth_pos h2 s e.1 e.2 l1 l3 hb1 hb2
  rw [ChartSetting.gaugeTransform_field_eq_torusChart hadm.L_odd h2 s c.admissible.subset_chart η₀] at hm
  have hs := c.admissible.half_le_meanNorm η₀ hη₀ b₀ hb₀ e hbd
  unfold meanNorm at hs
  rw [hm] at hs
  exact hs
theorem plainContourAverage_ne_zero (c : s.ChainContext δ lam σA cg N) {η₀ : FreeCoords s.free}
    (hη₀ : s.InBalls η₀) {e : TorusBond n} (he : e ∈ s.nearBonds) :
    plainContourAverage R.params.side e.1 e.2 (s.chartedFieldAt η₀) ≠ 0 := fun h => by
  have := half_le_norm_plainContourAverage c hη₀ he
  rw [h, norm_zero] at this
  norm_num at this
theorem contDiffThreeAt_nearFitSum (c : s.ChainContext δ lam σA cg N) {η₀ : FreeCoords s.free}
    (hη₀ : s.InBalls η₀) : ContDiffThreeAt s.nearFitSum (s.chartedFieldAt η₀) := fun k cc Xs =>
  contDiffAt_const.mul (ContDiffAt.sum fun _ hd =>
    contDiffThreeAt_plainAlignmentDefect _ _ _ (plainContourAverage_ne_zero c hη₀ hd) k cc Xs)
theorem mixedDeriv_nearFitSum (c : s.ChainContext δ lam σA cg N) {η₀ : FreeCoords s.free}
    (hη₀ : s.InBalls η₀) {k : ℕ} (hk : k ≤ 3) (cc : Fin k → TorusBond (n * R.params.side))
    (Xs : Fin k → imaginaryQuaternions) :
    mixedDeriv s.nearFitSum (s.chartedFieldAt η₀) cc Xs =
      R.params.coupling * ∑ b ∈ s.nearBonds,
        mixedDeriv (plainAlignmentDefect R.params.side b.1 b.2 (s.coarse b.1 b.2)) (s.chartedFieldAt η₀) cc Xs := by
  classical
  unfold mixedDeriv
  have hs : ∀ b ∈ s.nearBonds, ContDiffAt ℝ k
      (fun σ => plainAlignmentDefect R.params.side b.1 b.2 (s.coarse b.1 b.2)
        (perturb cc Xs σ (s.chartedFieldAt η₀))) 0 := fun b hb =>
    (contDiffThreeAt_plainAlignmentDefect _ _ _ (plainContourAverage_ne_zero c hη₀ hb) k cc Xs).of_le
      (by exact_mod_cast hk)
  have hs' : ContDiffAt ℝ k
      (fun σ => ∑ b ∈ s.nearBonds, plainAlignmentDefect R.params.side b.1 b.2 (s.coarse b.1 b.2)
        (perturb cc Xs σ (s.chartedFieldAt η₀))) 0 :=
    ContDiffAt.sum hs
  have e : (fun σ => s.nearFitSum (perturb cc Xs σ (s.chartedFieldAt η₀))) = fun σ => R.params.coupling •
      ∑ b ∈ s.nearBonds, plainAlignmentDefect R.params.side b.1 b.2 (s.coarse b.1 b.2)
        (perturb cc Xs σ (s.chartedFieldAt η₀)) := by
    funext σ
    rw [smul_eq_mul]
    rfl
  rw [e, iteratedFDeriv_const_smul_apply' hs', iteratedFDeriv_fun_sum_apply hs]
  simp
theorem supDist_parentBlock_le_six (c : s.ChainContext δ lam σA cg N) {Y : TorusSite n}
    {x : TorusSite (n * R.params.side)}
    (hx : _root_.YangMills.Construction.TorusFields.supDist (blockCentreSite R.params.side Y) x ≤ 5 * R.params.side) :
    _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side x) Y ≤ 6 := by
  have hL := c.params_admissible.L_odd
  have hpos : 0 < R.params.side := hL.pos
  have h1 := mul_supDist_parentBlock_le hL (blockCentreSite R.params.side Y) x
  rw [parentBlock_blockCentreSite hL] at h1
  rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
  have h2 : R.params.side * _root_.YangMills.Construction.TorusFields.supDist Y (parentBlock R.params.side x) ≤ R.params.side * 6 := by omega
  exact Nat.le_of_mul_le_mul_left h2 hpos
theorem abs_sum_le_card_mul_of_support {ι : Type*} [DecidableEq ι] (M B : Finset ι) (f : ι → ℝ) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ i ∈ M, |f i| ≤ K) (hz : ∀ i ∈ M, i ∉ B → f i = 0) :
    |∑ i ∈ M, f i| ≤ B.card * K := by
  have h1 : ∑ i ∈ M, f i = ∑ i ∈ M ∩ B, f i := by
    rw [← Finset.sum_filter_add_sum_filter_not M (· ∈ B)]
    have h2 : ∑ i ∈ M.filter (· ∉ B), f i = 0 :=
      Finset.sum_eq_zero fun i hi => hz i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
    rw [h2, add_zero, Finset.filter_mem_eq_inter]
  rw [h1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ K fun i hi => hb i (Finset.mem_inter.mp hi).1).trans ?_
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card Finset.inter_subset_right) hK
def nearbyBonds (Y : TorusSite n) : Finset (TorusBond n) :=
  open Classical in Finset.univ.filter fun b => _root_.YangMills.Construction.TorusFields.supDist Y b.1 ≤ 6
theorem card_nearbyBonds_le (Y : TorusSite n) : ((nearbyBonds Y).card : ℝ) ≤ 4 * 13 ^ 4 := by
  classical
  have h1 : nearbyBonds Y ⊆ (Finset.univ.filter fun y : TorusSite n => _root_.YangMills.Construction.TorusFields.supDist y Y ≤ 6) ×ˢ Finset.univ := by
    intro b hb
    have := (Finset.mem_filter.mp hb).2
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm] at this
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩, Finset.mem_univ _⟩
  have h2 := Finset.card_le_card h1
  rw [Finset.card_product] at h2
  have h3 := card_supDist_ball_le Y 6
  have h4 : (nearbyBonds Y).card ≤ 13 ^ 4 * 4 := by
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    calc _ ≤ _ := h2
      _ ≤ (2 * 6 + 1) ^ 4 * 4 := Nat.mul_le_mul_right _ h3
  have h5 : ((nearbyBonds Y).card : ℝ) ≤ ((13 ^ 4 * 4 : ℕ) : ℝ) := by exact_mod_cast h4
  refine h5.trans ?_
  norm_num
theorem mem_nearbyBonds {Y : TorusSite n} {b : TorusBond n} : b ∈ nearbyBonds Y ↔ _root_.YangMills.Construction.TorusFields.supDist Y b.1 ≤ 6 := by
  classical
  unfold nearbyBonds
  simp
theorem abs_mixedDeriv_one_nearFitSum_le (c : s.ChainContext δ lam σA cg N) {Kf : ℝ}
    (hK : AlignmentDerivativeBounds R.params.side Kf) (hKf : 0 ≤ Kf) {η₀ : FreeCoords s.free}
    (hη₀ : s.InBalls η₀) (b : TorusBond (n * R.params.side)) (Xs : Fin 1 → imaginaryQuaternions)
    (hX : AreUnitVectors Xs) :
    |mixedDeriv s.nearFitSum (s.chartedFieldAt η₀) ![b] Xs| ≤ R.params.coupling * (4 * 13 ^ 4 * Kf) := by
  classical
  have ha : 0 ≤ R.params.coupling := by linarith [c.params_admissible.a_ge]
  rw [mixedDeriv_nearFitSum c hη₀ (by norm_num), abs_mul, abs_of_nonneg ha]
  refine mul_le_mul_of_nonneg_left ?_ ha
  have h := abs_sum_le_card_mul_of_support s.nearBonds (nearbyBonds (parentBlock R.params.side b.1))
    (fun d => mixedDeriv (plainAlignmentDefect R.params.side d.1 d.2 (s.coarse d.1 d.2)) (s.chartedFieldAt η₀) ![b] Xs)
    hKf
    (fun d hd => (hK n d.1 d.2 _ _ (half_le_norm_plainContourAverage c hη₀ hd)).1 _ _ hX)
    (fun d hd hoff => mixedDeriv_one_plainAlignmentDefect_eq_zero _ _ _ _ _ (plainContourAverage_ne_zero c hη₀ hd)
      fun e he x hx hb => hoff (by
        have h1 := _root_.YangMills.Construction.NearFits.supDist_le_of_mem_contourWord c he hx
        have h2 := _root_.YangMills.Construction.CostDerivatives.supDist_parentBlock_le_six c h1
        have h3 : b = x.1 := hb
        rw [mem_nearbyBonds, h3]
        exact h2))
  exact h.trans (mul_le_mul_of_nonneg_right (card_nearbyBonds_le _) hKf)
def alignmentExpansionBound (L : ℕ) (a Kf : ℝ) {m : ℕ} (b b' : TorusBond m) : ℝ :=
  if _root_.YangMills.Construction.TorusFields.supDist b.1 b'.1 ≤ 10 * L then a * (4 * 13 ^ 4 * Kf) else 0
theorem abs_mixedDeriv_two_nearFitSum_le (c : s.ChainContext δ lam σA cg N) {Kf : ℝ}
    (hK : AlignmentDerivativeBounds R.params.side Kf) (hKf : 0 ≤ Kf) {η₀ : FreeCoords s.free}
    (hη₀ : s.InBalls η₀) (b b' : TorusBond (n * R.params.side)) (Xs : Fin 2 → imaginaryQuaternions)
    (hX : AreUnitVectors Xs) :
    |mixedDeriv s.nearFitSum (s.chartedFieldAt η₀) ![b, b'] Xs| ≤
      alignmentExpansionBound R.params.side R.params.coupling Kf b b' := by
  classical
  have ha : 0 ≤ R.params.coupling := by linarith [c.params_admissible.a_ge]
  rw [mixedDeriv_nearFitSum c hη₀ (by norm_num), abs_mul, abs_of_nonneg ha]
  unfold alignmentExpansionBound
  split_ifs with hd
  · refine mul_le_mul_of_nonneg_left ?_ ha
    have h := abs_sum_le_card_mul_of_support s.nearBonds (nearbyBonds (parentBlock R.params.side b.1))
      (fun d => mixedDeriv (plainAlignmentDefect R.params.side d.1 d.2 (s.coarse d.1 d.2)) (s.chartedFieldAt η₀)
        ![b, b'] Xs) hKf
      (fun d hd => (hK n d.1 d.2 _ _ (half_le_norm_plainContourAverage c hη₀ hd)).2 _ _ hX)
      (fun d hd hoff => mixedDeriv_two_plainAlignmentDefect_eq_zero _ _ _ _ _
        (plainContourAverage_ne_zero c hη₀ hd) 0 fun e he x hx hb => hoff (by
          have h1 := _root_.YangMills.Construction.NearFits.supDist_le_of_mem_contourWord c he hx
          have h2 := _root_.YangMills.Construction.CostDerivatives.supDist_parentBlock_le_six c h1
          have h3 : b = x.1 := hb
          rw [mem_nearbyBonds, h3]
          exact h2))
    exact h.trans (mul_le_mul_of_nonneg_right (card_nearbyBonds_le _) hKf)
  · have h0 : ∑ d ∈ s.nearBonds, mixedDeriv (plainAlignmentDefect R.params.side d.1 d.2 (s.coarse d.1 d.2))
        (s.chartedFieldAt η₀) ![b, b'] Xs = 0 := by
      refine Finset.sum_eq_zero fun d hdn => ?_
      by_cases hoff : ∀ e ∈ contourIndex R.params.side, ∀ x ∈ contourWord R.params.side d.1 d.2 e,
          (![b, b'] : Fin 2 → _) 0 ≠ x.1
      · exact mixedDeriv_two_plainAlignmentDefect_eq_zero _ _ _ _ _ (plainContourAverage_ne_zero c hη₀ hdn) 0 hoff
      · refine mixedDeriv_two_plainAlignmentDefect_eq_zero _ _ _ _ _ (plainContourAverage_ne_zero c hη₀ hdn) 1
          fun e' he' x' hx' hb' => ?_
        push Not at hoff
        obtain ⟨e, he, x, hx, hb⟩ := hoff
        have h1 := _root_.YangMills.Construction.NearFits.supDist_le_of_mem_contourWord c he hx
        have h2 := _root_.YangMills.Construction.NearFits.supDist_le_of_mem_contourWord c he' hx'
        have h3 : b = x.1 := hb
        have h4 : b' = x'.1 := hb'
        apply hd
        rw [h3, h4]
        have h5 := _root_.YangMills.Construction.TorusFields.supDist_triangle x.1.1 (blockCentreSite R.params.side d.1) x'.1.1
        have h6 : _root_.YangMills.Construction.TorusFields.supDist x.1.1 (blockCentreSite R.params.side d.1) =
            _root_.YangMills.Construction.TorusFields.supDist (blockCentreSite R.params.side d.1) x.1.1 := _root_.YangMills.Construction.TorusFields.supDist_comm _ _
        omega
    rw [h0, abs_zero, mul_zero]
section Homogeneous
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem abs_le_mul_norm_mul_norm_of_homogeneous (B : ImaginaryCoord → ImaginaryCoord → ℝ)
    (hz1 : ∀ y, B 0 y = 0) (hz2 : ∀ x, B x 0 = 0)
    (hs1 : ∀ (r : ℝ) x y, B (r • x) y = r * B x y) (hs2 : ∀ (r : ℝ) x y, B x (r • y) = r * B x y) {M : ℝ}
    (hM : ∀ u u', ‖u‖ = 1 → ‖u'‖ = 1 → |B u u'| ≤ M) (x y : ImaginaryCoord) : |B x y| ≤ M * ‖x‖ * ‖y‖ := by
  by_cases hx : x = 0
  · simp [hx, hz1]
  by_cases hy : y = 0
  · simp [hy, hz2]
  have h1 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h2 : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have e : B x y = ‖x‖ * ‖y‖ * B (‖x‖⁻¹ • x) (‖y‖⁻¹ • y) := by
    rw [hs1, hs2]
    field_simp
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  have := hM (‖x‖⁻¹ • x) (‖y‖⁻¹ • y) (by simp [norm_smul, h1]) (by simp [norm_smul, h2])
  have h3 : 0 ≤ ‖x‖ * ‖y‖ := by positivity
  calc _ ≤ ‖x‖ * ‖y‖ * M := mul_le_mul_of_nonneg_left this h3
    _ = _ := by ring
theorem abs_le_mul_norm_of_homogeneous (B : ImaginaryCoord → ℝ) (hz : B 0 = 0)
    (hs : ∀ (r : ℝ) x, B (r • x) = r * B x) {M : ℝ}
    (hM : ∀ u, ‖u‖ = 1 → |B u| ≤ M) (x : ImaginaryCoord) : |B x| ≤ M * ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, hz]
  have h1 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have e : B x = ‖x‖ * B (‖x‖⁻¹ • x) := by
    rw [hs]
    field_simp
  rw [e, abs_mul, abs_of_nonneg (norm_nonneg _)]
  have := hM (‖x‖⁻¹ • x) (by simp [norm_smul, h1])
  calc _ ≤ ‖x‖ * M := mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := by ring
omit [Fintype ι] in
theorem abs_bilinear_single_le (H : (ι → ImaginaryCoord) →L[ℝ] (ι → ImaginaryCoord) →L[ℝ] ℝ) (b b' : ι) {M : ℝ}
    (hM : ∀ u u' : ImaginaryCoord, ‖u‖ = 1 → ‖u'‖ = 1 → |H (Pi.single b u) (Pi.single b' u')| ≤ M)
    (x y : ImaginaryCoord) :
    |H (Pi.single b x) (Pi.single b' y)| ≤ M * ‖x‖ * ‖y‖ := by
  refine abs_le_mul_norm_mul_norm_of_homogeneous (fun x y => H (Pi.single b x) (Pi.single b' y))
    (fun y => ?_) (fun x => ?_) (fun r x y => ?_) (fun r x y => ?_) hM x y
  · simp
  · simp
  · simp [Pi.single_smul]
  · simp [Pi.single_smul]
omit [Fintype ι] in
theorem abs_linear_single_le (H : (ι → ImaginaryCoord) →L[ℝ] ℝ) (b : ι) {M : ℝ}
    (hM : ∀ u : ImaginaryCoord, ‖u‖ = 1 → |H (Pi.single b u)| ≤ M) (x : ImaginaryCoord) :
    |H (Pi.single b x)| ≤ M * ‖x‖ := by
  refine abs_le_mul_norm_of_homogeneous (fun x => H (Pi.single b x)) ?_ (fun r x => ?_) hM x
  · simp
  · simp [Pi.single_smul]
theorem bilinear_eq_sum_single (H : (ι → ImaginaryCoord) →L[ℝ] (ι → ImaginaryCoord) →L[ℝ] ℝ)
    (x y : ι → ImaginaryCoord) :
    H x y = ∑ b, ∑ b', H (Pi.single b (x b)) (Pi.single b' (y b')) := by
  conv_lhs => rw [← Finset.univ_sum_single x, ← Finset.univ_sum_single y]
  simp only [map_sum, _root_.sum_apply]
  exact Finset.sum_comm
theorem linear_eq_sum_single (H : (ι → ImaginaryCoord) →L[ℝ] ℝ) (x : ι → ImaginaryCoord) :
    H x = ∑ b, H (Pi.single b (x b)) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  simp [map_sum]
omit [DecidableEq ι] in
theorem sum_sum_mul_le_rowBound_mul_sum_sq (e : ι → ι → ℝ) (he : ∀ b b', 0 ≤ e b b')
    (hsym : ∀ b b', e b b' = e b' b) {E : ℝ}
    (hrow : ∀ b, ∑ b', e b b' ≤ E) (f : ι → ℝ) :
    ∑ b, ∑ b', e b b' * f b * f b' ≤ E * ∑ b, f b ^ 2 := by
  have h1 : ∀ b b', e b b' * f b * f b' ≤ e b b' * (f b ^ 2 / 2) + e b b' * (f b' ^ 2 / 2) := by
    intro b b'
    have := mul_nonneg (he b b') (sq_nonneg (f b - f b'))
    nlinarith
  have h2 : ∑ b, ∑ b', e b' b * (f b' ^ 2 / 2) = ∑ b, ∑ b', e b b' * (f b ^ 2 / 2) := Finset.sum_comm
  calc ∑ b, ∑ b', e b b' * f b * f b'
      ≤ ∑ b, ∑ b', (e b b' * (f b ^ 2 / 2) + e b b' * (f b' ^ 2 / 2)) :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => h1 b b'
    _ = ∑ b, ∑ b', e b b' * (f b ^ 2 / 2) + ∑ b, ∑ b', e b' b * (f b' ^ 2 / 2) := by
        simp only [Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
        rw [hsym]
    _ = 2 * ∑ b, (∑ b', e b b') * (f b ^ 2 / 2) := by
        rw [h2, ← two_mul]
        congr 1
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
    _ ≤ 2 * ∑ b, E * (f b ^ 2 / 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) (by norm_num)
        exact mul_le_mul_of_nonneg_right (hrow b) (by positivity)
    _ = _ := by
        rw [← Finset.mul_sum, ← Finset.sum_div]
        ring
end Homogeneous
end CostDerivatives
end YangMills.Construction
end
