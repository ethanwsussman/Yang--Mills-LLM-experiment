import YangMills.Construction.ClusterExpansionOfAStep.AdmissionIsAProduct
import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import Mathlib
import YangMills.Construction.ClusterExpansionOfAStep.AttachedClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.FrameReadsItsBox
import YangMills.Construction.ClusterExpansionOfAStep.LeastLogOfTheGroup
import YangMills.Construction.ClusterExpansionOfAStep.PriceOfTheHotLumps
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.ClusterExpansionOfAStep.WeightsOfAStepAreBorel
set_option autoImplicit false

noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours TorusFields TorusLumps StepSettings StepCosts
def AdmissionReadsHull : Prop :=
  ∀ R : StepSetup, R.IsWellPosed → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
    ∀ (V : TorusField n) (q : CoarseState R n), IsHullState R.params R.nextRange V q.1 →
    ∃ adm : (Yt : Finset (TorusSite (n * R.params.side))) → BaseChoice R.params.side n →
        TorusField (n * R.params.side) → (q.unlabelled Yt → R.labels.Ω) → ENNReal,
      (∀ Yt b W ν, adm Yt b W ν ≤ 1) ∧
      (∀ Yt b, Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
        adm Yt b p.1 p.2 *
          ENNReal.ofReal (R.labelWeight (n * R.params.side) (q.fieldWithStoredLinks p.1) Yt
            (q.fillLabels Yt p.2))) ∧
      ∀ V' : TorusField n, hotCoreSites R V' = hotCoreSites R V →
        (∀ c : TorusBond n, (c.1 ∈ q.1 ∨ c.1 + TorusFields.unitStep n c.2 ∈ q.1) → V' c.1 c.2 = V c.1 c.2) →
        coarseStateMass R (hotCoreSites R V') V' q =
          ∑ Yt : Finset (TorusSite (n * R.params.side)), ∑ b : BaseChoice R.params.side n,
            ∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω, adm Yt b W ν *
              ENNReal.ofReal (R.labelWeight (n * R.params.side) (q.fieldWithStoredLinks W) Yt
                  (q.fillLabels Yt ν) *
                baseLaw (q.fieldWithStoredLinks W) b *
                ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
                  bondKernel R.params R.coupling
                    (readAtLevel (stepBlockFrame R.params.side n) 0 (q.fieldWithStoredLinks W))
                    (readAtLevel (stepBlockFrame R.params.side n) 1 V') b c)
            ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))
end YangMills.Construction.ClusterExpansionOfAStep
end

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.TopLevelSites YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.StepSettings YangMills.Construction.StepCosts YangMills.Construction.BlockPlaces YangMills.Construction.TorusBalls
namespace HullLocality
open Classical in
theorem sum_powerset_constrained_prod {B : Type} (M : Finset B) (m : B → ℝ) (must may : B → Prop)
    (hm : ∀ b, must b → may b) :
    ∑ bad ∈ M.powerset, (if (∀ b ∈ M, must b → b ∈ bad) ∧ (∀ b ∈ bad, may b) then
        ∏ b ∈ M, (if b ∈ bad then 1 - m b else m b) else 0) =
      ∏ b ∈ M, (if must b then 1 - m b else if may b then 1 else m b) := by
  have h := Finset.prod_add (fun b => if may b then 1 - m b else 0) (fun b => if must b then 0 else m b) M
  have h1 : ∏ i ∈ M, ((if may i then 1 - m i else 0) + (if must i then 0 else m i)) =
      ∏ b ∈ M, (if must b then 1 - m b else if may b then 1 else m b) := by
    refine Finset.prod_congr rfl fun b _ => ?_
    by_cases hu : must b
    · simp [hu, hm b hu]
    · by_cases hy : may b <;> simp [hu, hy]
  rw [← h1, h]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hsub := Finset.mem_powerset.mp ht
  split_ifs with hok
  · obtain ⟨ha, hb⟩ := hok
    rw [← Finset.prod_sdiff hsub, mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun b hb' => ?_
      simp [hb', hb b hb']
    · refine Finset.prod_congr rfl fun b hb' => ?_
      obtain ⟨hbM, hbt⟩ := Finset.mem_sdiff.mp hb'
      have hnm : ¬ must b := fun hc => hbt (ha b hbM hc)
      simp [hbt, hnm]
  · rw [not_and_or] at hok
    rcases hok with hok | hok
    · push Not at hok
      obtain ⟨b, hbM, hbm, hbt⟩ := hok
      have : ∏ i ∈ M \ t, (if must i then (0 : ℝ) else m i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hbM, hbt⟩) (by simp [hbm])
      rw [this, mul_zero]
    · push Not at hok
      obtain ⟨b, hbt, hbm⟩ := hok
      have : ∏ i ∈ t, (if may i then 1 - m i else 0) = 0 :=
        Finset.prod_eq_zero hbt (by simp [hbm])
      rw [this, zero_mul]
theorem cutoff_nonneg {ρ : ℝ} {p : ℝ → ℝ} (h : IsCutoff ρ p) (hρ : 0 < ρ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < ρ) :
    0 ≤ p u := by
  by_cases hu : u ≤ 5 * ρ / 8
  · rw [h.vanish_small u h0 hu]
  · push Not at hu
    have hupos : 0 < u := by linarith
    have hz : p 0 = 0 := h.vanish_small 0 le_rfl (by linarith)
    have hm : p (5 * ρ / 8) = 0 := h.vanish_small _ (by linarith) le_rfl
    have hb : 0 ≤ 5 * ρ / 8 / u := by positivity
    have hb1 : 5 * ρ / 8 / u ≤ 1 := by
      rw [div_le_one hupos]
      exact hu.le
    have hc := h.convex.2 (show (0 : ℝ) ∈ Set.Ico 0 ρ from ⟨le_rfl, hρ⟩) (show u ∈ Set.Ico 0 ρ from ⟨h0, h1⟩)
      (by linarith : (0 : ℝ) ≤ 1 - 5 * ρ / 8 / u) hb (by ring)
    have he : (1 - 5 * ρ / 8 / u) • (0 : ℝ) + (5 * ρ / 8 / u) • u = 5 * ρ / 8 := by
      simp only [smul_eq_mul, mul_zero, zero_add]
      field_simp
    rw [he, hm, hz] at hc
    simp only [smul_eq_mul, mul_zero, zero_add] at hc
    by_contra hneg
    push Not at hneg
    have hbpos : 0 < 5 * ρ / 8 / u := by positivity
    have := mul_neg_of_pos_of_neg hbpos hneg
    linarith
theorem cutoffFactor_nonneg_le_one {ρ : ℝ} {p : ℝ → ℝ} (h : IsCutoff ρ p) (hρ : 0 < ρ) {u : ℝ} (h0 : 0 ≤ u) :
    0 ≤ cutoffFactor ρ p u ∧ cutoffFactor ρ p u ≤ 1 := by
  unfold cutoffFactor
  split_ifs with hu
  · exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith [cutoff_nonneg h hρ h0 hu])⟩
  · exact ⟨le_rfl, zero_le_one⟩
section Borel
variable {m : ℕ}
theorem measurable_pathHolonomy {F : BlockFrame} {j : ℕ} (x : F.Site j) (l : List PathStep) :
    Measurable fun W : TorusField m => pathHolonomy (readAtLevel F j W) x l := by
  induction l generalizing x with
  | nil => exact measurable_const
  | cons st r ih =>
    simp only [pathHolonomy]
    have hread : ∀ (z : F.Site j) (i : Fin 4), Measurable fun W : TorusField m => readAtLevel F j W z i :=
      fun z i => (measurable_pi_apply i).comp (measurable_pi_apply _)
    refine Measurable.mul ?_ (ih _)
    unfold BlockAverages.linkValue
    by_cases hs : st.2 = true
    · simp only [hs, if_true]
      exact hread _ _
    · simp only [hs, Bool.false_eq_true, if_false]
      exact (hread _ _).inv
theorem measurable_cutoffPiecewise {ρ : ℝ} {p : ℝ → ℝ} (h : IsCutoff ρ p) :
    Measurable ((Set.Ico 0 ρ).piecewise (fun u => Real.exp (-p u)) fun _ => 0) := by
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const measurableSet_Ico
  exact Real.continuous_exp.comp_continuousOn (h.smooth.continuousOn.neg)
theorem measurable_cutoffFactor_minimalLog {ρ : ℝ} {p : ℝ → ℝ} (h : IsCutoff ρ p) (f : ℍ[ℝ]) :
    Measurable fun g : UnitQuaternion => cutoffFactor ρ p ‖((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]) - f‖ := by
  have hN : Measurable fun g : UnitQuaternion => ‖((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]) - f‖ := by
    refine measurable_of_continuousOn_compl_singleton (-1 : UnitQuaternion) ?_
    exact (QuaternionLog.continuousOn_coe_minimalLog.sub continuousOn_const).norm
  have he : (fun g : UnitQuaternion => cutoffFactor ρ p ‖((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]) - f‖) =
      ((Set.Ico 0 ρ).piecewise (fun u => Real.exp (-p u)) fun _ => 0) ∘
        fun g : UnitQuaternion => ‖((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]) - f‖ := by
    funext g
    simp only [Function.comp, cutoffFactor, Set.piecewise, Set.mem_Ico, norm_nonneg, true_and]
  rw [he]
  exact (measurable_cutoffPiecewise h).comp hN
theorem measurableSet_isHullState [NeZero m] {ℓ : StepParameters} (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ m)
    (r : ℕ) (Yt : Finset (TorusSite m)) : MeasurableSet {W : TorusField m | IsHullState ℓ r W Yt} := by
  classical
  let P : Finset (Finset (TorusSite m)) → Prop := fun H =>
    thickening (2 * r) (H.biUnion id) ⊆ Yt ∧ ∀ X ∈ chainComponents r Yt, ∃ l ∈ H, (l ∩ X).Nonempty
  have hset : {W : TorusField m | IsHullState ℓ r W Yt} =
      ⋃ H, {W : TorusField m | torusHotLumps ℓ W = H} ∩ {_W | P H} := by
    ext W
    simp only [mem_iUnion, mem_inter_iff, Set.mem_ofPred_eq, exists_eq_left']
    rfl
  rw [hset]
  refine MeasurableSet.iUnion fun H => (measurableSet_torusHotLumps_eq hfit hLn H).inter ?_
  exact MeasurableSet.const _
end Borel
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem measurable_bondMark (hR : R.IsWellPosed) (V : TorusField n) (b : TorusBond (n * R.params.side)) :
    Measurable fun W : TorusField (n * R.params.side) => bondMark R V W b := by
  classical
  set F := stepBlockFrame R.params.side n
  have hread : ∀ (z : F.Site 0) (i : Fin 4),
      Measurable fun W : TorusField (n * R.params.side) => readAtLevel F 0 W z i :=
    fun z i => (measurable_pi_apply i).comp (measurable_pi_apply _)
  have htree : ∀ x : F.Site 0,
      Measurable fun W : TorusField (n * R.params.side) => axialGauge 1 (readAtLevel F 0 W) x :=
    fun x => measurable_pathHolonomy _ _
  have hgauged : Measurable fun W : TorusField (n * R.params.side) =>
      gaugeTransform (axialGauge 1 (readAtLevel F 0 W)) (readAtLevel F 0 W) (torusSiteInFrame F 0 b.1) b.2 :=
    ((htree _).mul (hread _ _)).mul (htree _).inv
  have hT := measurable_cutoffFactor_minimalLog hR.isCutoff
    ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ])
  by_cases hc : IsCrossingBond (torusSiteInFrame F 0 b.1, b.2)
  · have hG := hgauged.mul_const ((readAtLevel F 1 V (enclosingCell (torusSiteInFrame F 0 b.1)) b.2)⁻¹)
    have key : ∀ W : TorusField (n * R.params.side), bondMark R V W b = cutoffFactor R.ballRadius R.barrierFn
        ‖((minimalLog (gaugeTransform (axialGauge 1 (readAtLevel F 0 W)) (readAtLevel F 0 W)
            (torusSiteInFrame F 0 b.1) b.2 *
          (readAtLevel F 1 V (enclosingCell (torusSiteInFrame F 0 b.1)) b.2)⁻¹) : imaginaryQuaternions) : ℍ[ℝ]) -
          ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ])‖ := by
      intro W
      unfold bondMark chartCoord bondCoordinate
      rw [if_pos hc]
      rfl
    rw [funext key]
    exact Measurable.comp (g := fun g : UnitQuaternion => cutoffFactor R.ballRadius R.barrierFn
      ‖((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]) -
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ])‖) hT hG
  · have key : ∀ W : TorusField (n * R.params.side), bondMark R V W b = cutoffFactor R.ballRadius R.barrierFn
        ‖((minimalLog (gaugeTransform (axialGauge 1 (readAtLevel F 0 W)) (readAtLevel F 0 W)
            (torusSiteInFrame F 0 b.1) b.2) : imaginaryQuaternions) : ℍ[ℝ]) -
          ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ])‖ := by
      intro W
      unfold bondMark chartCoord bondCoordinate
      rw [if_neg hc]
    rw [funext key]
    exact Measurable.comp (g := fun g : UnitQuaternion => cutoffFactor R.ballRadius R.barrierFn
      ‖((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]) -
      ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ])‖) hT hgauged
theorem bondMark_nonneg_le_one (hR : R.IsWellPosed) (V : TorusField n) (W : TorusField (n * R.params.side))
    (b : TorusBond (n * R.params.side)) : 0 ≤ bondMark R V W b ∧ bondMark R V W b ≤ 1 :=
  cutoffFactor_nonneg_le_one hR.isCutoff
    (by have := hR.admissible.σ_pos; unfold StepSetup.ballRadius; positivity) (norm_nonneg _)
theorem markProduct_nonneg (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (bad : Finset (TorusBond (n * R.params.side))) :
    0 ≤ markProduct R C V W bad := by
  classical
  unfold markProduct
  refine Finset.prod_nonneg fun b _ => ?_
  have := bondMark_nonneg_le_one hR V W b
  split_ifs
  · linarith [this.2]
  · exact this.1
theorem sum_markProduct_eq_one (hR : R.IsWellPosed) (C : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) :
    ∑ bad ∈ (markedBonds R C).powerset, ENNReal.ofReal (markProduct R C V W bad) = 1 := by
  classical
  rw [← ENNReal.ofReal_sum_of_nonneg fun bad _ => markProduct_nonneg hR C V W bad]
  have h := sum_powerset_constrained_prod (markedBonds R C) (fun b => bondMark R V W b) (fun _ => False)
    (fun _ => True) (fun _ hf => hf.elim)
  simp only [false_imp_iff, implies_true, and_self, if_true, if_false, Finset.prod_const_one] at h
  unfold markProduct
  convert ENNReal.ofReal_one using 2
  convert h
theorem measurable_fieldWithStoredLinks (q : CoarseState R n) : Measurable q.fieldWithStoredLinks := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun i => ?_
  have hc : Measurable fun W : TorusField (n * R.params.side) => W x i :=
    (measurable_pi_apply i).comp (measurable_pi_apply x)
  rcases h : q.markAt (parentBlock R.params.side x) with _ | s
  · have e : (fun W : TorusField (n * R.params.side) => q.fieldWithStoredLinks W x i) = fun W => W x i := by
      funext W
      simp only [CoarseState.fieldWithStoredLinks, h]
    rw [e]
    exact hc
  · rcases h' : s.linkValue (siteOffset x, i) with u | g
    · have e : (fun W : TorusField (n * R.params.side) => q.fieldWithStoredLinks W x i) = fun W => W x i := by
        funext W
        simp only [CoarseState.fieldWithStoredLinks, h, h']
      rw [e]
      exact hc
    · have e : (fun W : TorusField (n * R.params.side) => q.fieldWithStoredLinks W x i) = fun _ => g := by
        funext W
        simp only [CoarseState.fieldWithStoredLinks, h, h']
      rw [e]
      exact measurable_const
theorem measurable_fillLabels (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable (q.fillLabels Yt) := by
  classical
  refine measurable_pi_iff.mpr fun z => ?_
  by_cases h : (z : TorusSite (n * R.params.side)) ∈ q.labelSet
  · have e : ∀ ν, q.fillLabels Yt ν z = q.labeling ⟨z, h⟩ := fun ν => fillLabels_of_mem q Yt ν z z.2 h
    simp only [e]
    exact measurable_const
  · have hr : (z : TorusSite (n * R.params.side)) ∈ q.unlabelled Yt := by
      rw [unlabelled_eq_sdiff]
      exact Finset.mem_sdiff.mpr ⟨z.2, h⟩
    have e : ∀ ν, q.fillLabels Yt ν z = ν ⟨z, hr⟩ := fun ν => fillLabels_of_mem_unlabelled q Yt ν z z.2 hr
    simp only [e]
    exact measurable_pi_apply _
theorem coarseStateOf_fill (q : CoarseState R n) (C : Finset (TorusSite n))
    (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) (W W' : TorusField (n * R.params.side))
    (ν : q.unlabelled Yt → R.labels.Ω) (ν' : q.unlabelled Yt → R.labels.Ω)
    (h : coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) :
    coarseStateOf R C (q.fieldWithStoredLinks W') Yt (q.fillLabels Yt ν') bad b = q := by
  classical
  refine Eq.trans ?_ h
  refine coarseState_ext _ _ rfl fun y => ?_
  rw [markAt_coarseStateOf, markAt_coarseStateOf]
  by_cases hy : y ∈ storedBlocks R.params.side R.range bad Yt C
  · rw [if_pos hy, if_pos hy]
    congr 1
    unfold blockConfigAt
    congr 1
    · funext o
      by_cases hz : blockSite y o ∈ Yt
      · rw [dif_pos hz, dif_pos hz]
        have hl := (mem_labelSet_coarseStateOf C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b).mpr
          ⟨hz, by rw [parentBlock_blockSite]; exact hy⟩
        rw [h] at hl
        rw [fillLabels_of_mem q Yt ν' _ hz hl, fillLabels_of_mem q Yt ν _ hz hl]
      · rw [dif_neg hz, dif_neg hz]
    · funext c
      by_cases hz : parentBlock R.params.side
          (blockSite (L := R.params.side) y c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈
          storedBlocks R.params.side R.range bad Yt C
      · rw [if_pos hz, if_pos hz]
        have hf := (mem_storedFieldBonds_coarseStateOf C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b
          (c := (blockSite y c.1, c.2))).mpr ⟨by rw [parentBlock_blockSite]; exact hy, hz⟩
        have h2 := fieldWithStoredLinks_coarseStateOf C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b
          W' _ hf
        rw [h] at h2
        exact congrArg Sum.inr h2
      · rw [if_neg hz, if_neg hz]
  · rw [if_neg hy, if_neg hy]
theorem two_mul_supDist_le {m : ℕ} [NeZero m] (x y : TorusSite m) : 2 * _root_.YangMills.Construction.TorusFields.supDist x y ≤ m := by
  have : _root_.YangMills.Construction.TorusFields.supDist x y ≤ m / 2 := (supDist_le_iff x y _).mpr fun i => ZMod.natAbs_valMinAbs_le _
  omega
theorem supDist_add_le_of_inBox {m : ℕ} [NeZero m] (y : TorusSite m) {h : Fin 4 → ℤ} {k : ℕ}
    (hb : OffsetInBox k h) : _root_.YangMills.Construction.TorusFields.supDist y (y + siteOfInt h) ≤ k :=
  supDist_add_siteOfInt_le y h k fun i => by
    have : ((h i).natAbs : ℤ) ≤ k := by rw [Int.natCast_natAbs]; exact hb i
    exact_mod_cast this
theorem bondMark_congr (hFr : FrameLocality.FrameCoordLocal) (hf : R.params.Admissible) (hm : 0 < R.frameReach)
    (hn : 4 * R.frameReach + 5 < n) {V V' : TorusField n} (W : TorusField (n * R.params.side))
    (b : TorusBond (n * R.params.side))
    (hV : ∀ c : TorusBond n, _root_.YangMills.Construction.TorusFields.supDist c.1 (parentBlock R.params.side b.1) ≤ R.frameReach → V' c.1 c.2 = V c.1 c.2) :
    bondMark R V' W b = bondMark R V W b := by
  have hframe : frameCoord R.params R.anchorRadius R.depth R.frameReach V' b =
      frameCoord R.params R.anchorRadius R.depth R.frameReach V b := by
    refine hFr R.params R.anchorRadius R.depth R.frameReach n n V' V b b hf hm hn hn rfl rfl ?_
    intro c hc
    refine hV (bondFrom (parentBlock R.params.side b.1) c) ?_
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm]
    exact supDist_add_le_of_inBox _ hc.1
  have hchart : chartCoord R.params V' W b = chartCoord R.params V W b := by
    unfold chartCoord bondCoordinate
    by_cases hc : IsCrossingBond (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1, b.2)
    · rw [if_pos hc, if_pos hc]
      have e : ∀ U : TorusField n, readAtLevel (stepBlockFrame R.params.side n) 1 U
          (enclosingCell (torusSiteInFrame (stepBlockFrame R.params.side n)
            (stepBlockFrame R.params.side n).depth b.1)) b.2 = U (parentBlock R.params.side b.1) b.2 := by
        intro U
        have : NeZero (n * (stepBlockFrame R.params.side n).blockSide) :=
          inferInstanceAs (NeZero (n * R.params.side))
        have hside : ∀ i, (stepBlockFrame R.params.side n).extent i = n := fun _ => rfl
        have h1 : enclosingCell (torusSiteInFrame (stepBlockFrame R.params.side n)
              (stepBlockFrame R.params.side n).depth b.1) =
            torusSiteInFrame (stepBlockFrame R.params.side n) (stepBlockFrame R.params.side n).top
              (parentBlock R.params.side b.1) :=
          enclosingCell_torusSiteInFrame (F := stepBlockFrame R.params.side n) (n := n) hside b.1
        have h2 : toTorusSite n (torusSiteInFrame (stepBlockFrame R.params.side n)
              (stepBlockFrame R.params.side n).top (parentBlock R.params.side b.1)) =
            parentBlock R.params.side b.1 :=
          toTorusSite_torusSiteInFrame (F := stepBlockFrame R.params.side n) (period_top_of_extent hside) _
        show U (toTorusSite n (enclosingCell (torusSiteInFrame (stepBlockFrame R.params.side n)
          (stepBlockFrame R.params.side n).depth b.1))) b.2 = _
        rw [h1, h2]
      have e' : readAtLevel (stepBlockFrame R.params.side n) 1 V'
          (enclosingCell (torusSiteInFrame (stepBlockFrame R.params.side n)
            (stepBlockFrame R.params.side n).depth b.1)) b.2 =
          readAtLevel (stepBlockFrame R.params.side n) 1 V
            (enclosingCell (torusSiteInFrame (stepBlockFrame R.params.side n)
              (stepBlockFrame R.params.side n).depth b.1)) b.2 := by
        rw [e, e]
        exact hV (parentBlock R.params.side b.1, b.2) (by rw [supDist_self]; omega)
      exact congrArg (fun g : UnitQuaternion => minimalLog (gaugeTransform
        (axialGauge 1 (readAtLevel (stepBlockFrame R.params.side n) 0 W))
        (readAtLevel (stepBlockFrame R.params.side n) 0 W)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1) b.2 * g⁻¹)) e'
    · rw [if_neg hc, if_neg hc]
  unfold bondMark
  rw [hchart, hframe]
theorem storedBlocks_empty (r : ℕ) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) :
    storedBlocks R.params.side r bad Yt (∅ : Finset (TorusSite n)) = ∅ := by
  classical
  have h1 : attachedSites R.params.side r bad Yt (∅ : Finset (TorusSite n)) = ∅ := by
    unfold attachedSites
    refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨X, hX, -⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨z, hz⟩ := (Finset.mem_filter.mp hX).2
    have hz2 := (Finset.mem_inter.mp hz).2
    rw [mem_sitesInBlocks] at hz2
    simp at hz2
  unfold storedBlocks coreBlocks
  rw [h1]
  ext y
  simp only [Finset.empty_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro ⟨z, hz⟩
  have hz2 := (mem_thickening _ _ _).mp (Finset.mem_inter.mp hz).2
  obtain ⟨x, hx, -⟩ := hz2
  simp at hx
variable (R) in
abbrev heldSites (q : CoarseState R n) (C : Finset (TorusSite n)) : Finset (TorusSite (n * R.params.side)) :=
  q.storedBadBonds.image Prod.fst ∪ q.labelSet ∪ sitesInBlocks R.params.side C
theorem frameReach_add_le_half (hR : R.IsWellPosed) :
    R.frameReach + (10 * R.range / R.params.side + 1) ≤ R.nextRange / 2 := by
  have hL := hR.admissible.L_ge
  have h1 := hR.range_le
  have h2 := hR.range_ge_side
  have h3 : 10 * R.range / R.params.side ≤ 10 * R.range / 2 ^ 16 := Nat.div_le_div_left hL (by norm_num)
  have h4 : 2 ^ 56 ≤ R.range := by
    have : 2 ^ 40 * 2 ^ 16 ≤ 2 ^ 40 * R.params.side := Nat.mul_le_mul_left _ hL
    omega
  unfold StepSetup.frameReach
  omega
theorem bondMark_eq_of_near (hFr : FrameLocality.FrameCoordLocal) (hR : R.IsWellPosed) {V V' : TorusField n}
    (q : CoarseState R n) {W₀ W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))}
    {ω₀ : Yt → R.labels.Ω} {bad₀ : Finset (TorusBond (n * R.params.side))} {b : BaseChoice R.params.side n}
    (hst : coarseStateOf R (hotCoreSites R V) W₀ Yt ω₀ bad₀ b = q)
    (hV : ∀ c : TorusBond n, (c.1 ∈ q.1 ∨ c.1 + TorusFields.unitStep n c.2 ∈ q.1) → V' c.1 c.2 = V c.1 c.2)
    {c : TorusBond (n * R.params.side)} (hcM : c ∈ markedBonds R (hotCoreSites R V))
    (hc : parentBlock R.params.side c.1 ∈ q.markedZone ∨
      ∃ u ∈ heldSites R q (hotCoreSites R V), _root_.YangMills.Construction.TorusFields.supDist c.1 u ≤ 10 * R.range) :
    bondMark R V' W c = bondMark R V W c := by
  classical
  have hzone : q.markedZone = storedBlocks R.params.side R.range bad₀ Yt (hotCoreSites R V) := by
    rw [← hst]
    exact markedZone_coarseStateOf _ _ _ _ _ _
  have hq1 : q.1 = thickening (R.nextRange / 2) q.markedZone := by
    rw [hzone, ← hst]
    rfl
  have hCz : hotCoreSites R V ⊆ q.markedZone := by
    rw [hzone]
    exact Finset.subset_union_left
  have hheld : ∀ u ∈ heldSites R q (hotCoreSites R V), parentBlock R.params.side u ∈ q.markedZone := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨s, hs, -⟩ := mem_storedBadBonds.mp hd
        exact mem_controlRegion.mpr (by rw [hs]; rfl)
      · rw [mem_labelSet] at hu
        rw [mem_controlRegion]
        unfold CoarseState.labelAt at hu
        rcases hs : q.markAt (parentBlock R.params.side u) with _ | s
        · rw [hs] at hu
          exact absurd rfl hu
        · rfl
    · exact hCz (mem_sitesInBlocks.mp hu)
  obtain ⟨z, hz, hd⟩ : ∃ z ∈ q.markedZone,
      _root_.YangMills.Construction.TorusFields.supDist (parentBlock R.params.side c.1) z ≤ 10 * R.range / R.params.side + 1 := by
    rcases hc with hc | ⟨u, hu, hd⟩
    · exact ⟨_, hc, by rw [supDist_self]; exact Nat.zero_le _⟩
    · exact ⟨_, hheld u hu, (supDist_parentBlock_le_div_add_one _ _ _).trans
        (Nat.add_le_add_right (Nat.div_le_div_right hd) 1)⟩
  have hcC : parentBlock R.params.side c.1 ∉ hotCoreSites R V := (Finset.mem_filter.mp hcM).2
  have hr := hR.range_ge_side
  have hr1 := hR.range_le
  have hL := hR.admissible.L_ge
  have hrbig : 2 ^ 56 ≤ R.range := by
    have : 2 ^ 40 * 2 ^ 16 ≤ 2 ^ 40 * R.params.side := Nat.mul_le_mul_left _ hL
    omega
  have hm : 0 < R.frameReach := Nat.div_pos (by omega) (by norm_num)
  have hn : 4 * R.frameReach + 5 < n := by
    by_contra hcon
    push Not at hcon
    have hmr : R.frameReach ≤ R.range / 2 ^ 11 := le_rfl
    rcases (torusHotSites R.params V).eq_empty_or_nonempty with he | ⟨h, hh⟩
    · have hCe : hotCoreSites R V = ∅ := by
        unfold hotCoreSites
        rw [he]
        ext y
        simp only [mem_thickening, Finset.notMem_empty, false_and, exists_false]
      rw [hzone, hCe, storedBlocks_empty] at hz
      simp at hz
    · refine hcC ((mem_thickening _ _ _).mpr ⟨h, hh, ?_⟩)
      have := two_mul_supDist_le (parentBlock R.params.side c.1) h
      omega
  refine bondMark_congr hFr hR.admissible hm hn W c fun d hd' => hV d (Or.inl ?_)
  rw [hq1]
  refine (mem_thickening _ _ _).mpr ⟨z, hz, ?_⟩
  have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle d.1 (parentBlock R.params.side c.1) z
  have h2 := frameReach_add_le_half hR
  omega
open Classical in
theorem sum_markProduct_congr (hA : AdmissionIsProduct) (hFr : FrameLocality.FrameCoordLocal)
    (hR : R.IsWellPosed) (hs : IsBlockTorusSide R.params n) {V V' : TorusField n} (q : CoarseState R n)
    (hq : IsHullState R.params R.nextRange V q.1)
    (hV : ∀ c : TorusBond n, (c.1 ∈ q.1 ∨ c.1 + TorusFields.unitStep n c.2 ∈ q.1) → V' c.1 c.2 = V c.1 c.2)
    (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
    (ω : Yt → R.labels.Ω) (b : BaseChoice R.params.side n) :
    ∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset,
        (if IsHullState R.params R.range W Yt ∧ coarseStateOf R (hotCoreSites R V) W Yt ω bad b = q then
          ENNReal.ofReal (markProduct R (hotCoreSites R V) V' W bad) else 0) =
      ∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset,
        (if IsHullState R.params R.range W Yt ∧ coarseStateOf R (hotCoreSites R V) W Yt ω bad b = q then
          ENNReal.ofReal (markProduct R (hotCoreSites R V) V W bad) else 0) := by
  set C := hotCoreSites R V with hCdef
  set M := markedBonds R C with hMdef
  by_cases hex : ∃ bad₀ ∈ M.powerset, IsHullState R.params R.range W Yt ∧ coarseStateOf R C W Yt ω bad₀ b = q
  · obtain ⟨bad₀, hb₀, hhull, hst⟩ := hex
    have hb₀M := Finset.mem_powerset.mp hb₀
    obtain ⟨htest, hcase⟩ := (hA R hR n hs V q hq W Yt ω bad₀ b hb₀M hhull).mp hst
    let must : TorusBond (n * R.params.side) → Prop := fun c => c ∈ q.storedBadBonds
    let may : TorusBond (n * R.params.side) → Prop := fun c =>
      c ∈ q.storedBadBonds ∨ (parentBlock R.params.side c.1 ∉ q.markedZone ∧
        ∀ u ∈ heldSites R q C, 10 * R.range < _root_.YangMills.Construction.TorusFields.supDist c.1 u)
    have hbz : ∀ c, c ∈ q.storedBadBonds → parentBlock R.params.side c.1 ∈ q.markedZone := fun c hc =>
      ((hcase.mem_badBonds_iff c).mp hc).2
    have hP : ∀ bad ∈ M.powerset, (IsHullState R.params R.range W Yt ∧ coarseStateOf R C W Yt ω bad b = q) ↔
        ((∀ c ∈ M, must c → c ∈ bad) ∧ (∀ c ∈ bad, may c)) := by
      intro bad hbad
      have hbM := Finset.mem_powerset.mp hbad
      constructor
      · rintro ⟨-, h⟩
        have hc := ((hA R hR n hs V q hq W Yt ω bad b hbM hhull).mp h).2
        refine ⟨fun c _ hm => ((hc.mem_badBonds_iff c).mp hm).1, fun c hcb => ?_⟩
        by_cases hz : parentBlock R.params.side c.1 ∈ q.markedZone
        · exact Or.inl ((hc.mem_badBonds_iff c).mpr ⟨hcb, hz⟩)
        · exact Or.inr ⟨hz, fun u hu => hc.far_badBonds c hcb hz u hu⟩
      · rintro ⟨h1, h2⟩
        refine ⟨hhull, (hA R hR n hs V q hq W Yt ω bad b hbM hhull).mpr ⟨htest, ?_⟩⟩
        refine
          { field_eq := hcase.field_eq
            mem_support_iff := hcase.mem_support_iff
            labeling_eq := hcase.labeling_eq
            mem_badBonds_iff := fun c =>
              ⟨fun hc => ⟨h1 c (hb₀M ((hcase.mem_badBonds_iff c).mp hc).1) hc, hbz c hc⟩, ?_⟩
            baseOffset_eq := hcase.baseOffset_eq
            far_badBonds := fun c hc hz => ?_
            far_support := hcase.far_support }
        · rintro ⟨hc, hz⟩
          rcases h2 c hc with h | h
          · exact h
          · exact absurd hz h.1
        · rcases h2 c hc with h | h
          · exact absurd (hbz c h) hz
          · exact h.2
    have key : ∀ U : TorusField n, ∑ bad ∈ M.powerset,
        (if IsHullState R.params R.range W Yt ∧ coarseStateOf R C W Yt ω bad b = q then
          ENNReal.ofReal (markProduct R C U W bad) else 0) =
        ENNReal.ofReal (∏ c ∈ M, (if must c then 1 - bondMark R U W c else if may c then 1
          else bondMark R U W c)) := by
      intro U
      have hU := congrArg ENNReal.ofReal
        (sum_powerset_constrained_prod M (fun c => bondMark R U W c) must may (fun c h => Or.inl h))
      refine Eq.trans ?_ (hU.trans (by congr!))
      rw [ENNReal.ofReal_sum_of_nonneg]
      · refine Finset.sum_congr rfl fun bad hbad => ?_
        by_cases hok : (∀ c ∈ M, must c → c ∈ bad) ∧ (∀ c ∈ bad, may c)
        · rw [if_pos ((hP bad hbad).mpr hok), if_pos hok]
          unfold markProduct
          congr!
        · rw [if_neg (fun h => hok ((hP bad hbad).mp h)), if_neg hok, ENNReal.ofReal_zero]
      · intro bad _
        by_cases hok : (∀ c ∈ M, must c → c ∈ bad) ∧ (∀ c ∈ bad, may c)
        · rw [if_pos hok]
          have := markProduct_nonneg hR C U W bad
          unfold markProduct at this
          convert this
        · rw [if_neg hok]
    rw [key V', key V]
    congr 1
    refine Finset.prod_congr rfl fun c hcM => ?_
    by_cases hm : must c
    · rw [if_pos hm, if_pos hm, bondMark_eq_of_near hFr hR q hst hV hcM (Or.inl (hbz c hm))]
    · rw [if_neg hm, if_neg hm]
      by_cases hy : may c
      · rw [if_pos hy, if_pos hy]
      · rw [if_neg hy, if_neg hy]
        refine bondMark_eq_of_near hFr hR q hst hV hcM ?_
        by_contra hcon
        push Not at hcon
        exact hy (Or.inr ⟨hcon.1, hcon.2⟩)
  · push Not at hex
    have hz : ∀ U : TorusField n, ∑ bad ∈ M.powerset,
        (if IsHullState R.params R.range W Yt ∧ coarseStateOf R C W Yt ω bad b = q then
          ENNReal.ofReal (markProduct R C U W bad) else 0) = 0 := by
      intro U
      refine Finset.sum_eq_zero fun bad hbad => if_neg fun h => hex bad hbad h.1 h.2
    rw [hz V', hz V]
def fill (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side)))
    (p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω)) :
    TorusField (n * R.params.side) × (Yt → R.labels.Ω) := (q.fieldWithStoredLinks p.1, q.fillLabels Yt p.2)
theorem measurable_fill (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable (fill q Yt) :=
  ((measurable_fieldWithStoredLinks q).comp measurable_fst).prodMk ((measurable_fillLabels q Yt).comp measurable_snd)
open Classical in
def fillWeight (q : CoarseState R n) (C : Finset (TorusSite n)) (U : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω)) :
    ENNReal :=
  if IsHullState R.params R.range (fill q Yt p).1 Yt ∧
      coarseStateOf R C (fill q Yt p).1 Yt (fill q Yt p).2 bad b = q then
    ENNReal.ofReal (stepWeight R C U (fill q Yt p).1 Yt (fill q Yt p).2 bad b) else 0
open Classical in
def fillMarks (q : CoarseState R n) (C : Finset (TorusSite n)) (U : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω)) :
    ENNReal :=
  if IsHullState R.params R.range (fill q Yt p).1 Yt ∧
      coarseStateOf R C (fill q Yt p).1 Yt (fill q Yt p).2 bad b = q then
    ENNReal.ofReal (markProduct R C U (fill q Yt p).1 bad) else 0
theorem measurable_fillWeight (hw : ConfigurationWeightMeasurable) (hR : R.IsWellPosed) (hn₀ : R.params.n₀ ≤ n)
    (q : CoarseState R n) (C : Finset (TorusSite n)) (U : TorusField n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) : Measurable (fillWeight q C U bad Yt b) := by
  classical
  by_cases ht : ∃ p, coarseStateOf R C (fill q Yt p).1 Yt (fill q Yt p).2 bad b = q
  · obtain ⟨p₀, h₀⟩ := ht
    have he : fillWeight q C U bad Yt b =
        (fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
          configurationWeight R C U bad Yt b p.1 p.2) ∘ fill q Yt := by
      funext p
      have hst : coarseStateOf R C (fill q Yt p).1 Yt (fill q Yt p).2 bad b = q :=
        coarseStateOf_fill q C Yt bad b p₀.1 p.1 p₀.2 p.2 h₀
      simp only [fillWeight, Function.comp, configurationWeight]
      by_cases hh : IsHullState R.params R.range (fill q Yt p).1 Yt
      · rw [if_pos ⟨hh, hst⟩, if_pos hh]
      · rw [if_neg fun h => hh h.1, if_neg hh]
    rw [he]
    exact (hw R hR n hn₀ C U bad Yt b).comp (measurable_fill q Yt)
  · have he : fillWeight q C U bad Yt b = fun _ => 0 := by
      funext p
      exact if_neg fun h => ht ⟨p, h.2⟩
    rw [he]
    exact measurable_const
theorem measurable_fillMarks (hR : R.IsWellPosed) (hLn : R.params.side ∣ n * R.params.side) (q : CoarseState R n)
    (C : Finset (TorusSite n)) (U : TorusField n) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) :
    Measurable (fillMarks q C U bad Yt b) := by
  classical
  have hfst : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      (fill q Yt p).1 :=
    measurable_fst.comp (measurable_fill q Yt)
  have hmk : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
      ENNReal.ofReal (markProduct R C U (fill q Yt p).1 bad) := by
    refine ENNReal.measurable_ofReal.comp ?_
    unfold markProduct
    refine Finset.measurable_prod _ fun c _ => ?_
    have hc : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
        bondMark R U (fill q Yt p).1 c :=
      (measurable_bondMark hR U c).comp hfst
    by_cases hcb : c ∈ bad
    · simp only [if_pos hcb]
      exact measurable_const.sub hc
    · simp only [if_neg hcb]
      exact hc
  by_cases ht : ∃ p, coarseStateOf R C (fill q Yt p).1 Yt (fill q Yt p).2 bad b = q
  · obtain ⟨p₀, h₀⟩ := ht
    have he : fillMarks q C U bad Yt b = fun p => if IsHullState R.params R.range (fill q Yt p).1 Yt then
        ENNReal.ofReal (markProduct R C U (fill q Yt p).1 bad) else 0 := by
      funext p
      have hst : coarseStateOf R C (fill q Yt p).1 Yt (fill q Yt p).2 bad b = q :=
        coarseStateOf_fill q C Yt bad b p₀.1 p.1 p₀.2 p.2 h₀
      unfold fillMarks
      by_cases hh : IsHullState R.params R.range (fill q Yt p).1 Yt
      · rw [if_pos ⟨hh, hst⟩, if_pos hh]
      · rw [if_neg fun h => hh h.1, if_neg hh]
    rw [he]
    exact Measurable.ite (hfst (measurableSet_isHullState hR.admissible hLn R.range Yt)) hmk measurable_const
  · have he : fillMarks q C U bad Yt b = fun _ => 0 := by
      funext p
      exact if_neg fun h => ht ⟨p, h.2⟩
    rw [he]
    exact measurable_const
end HullLocality
open HullLocality in
theorem admissionReadsHull_holds (hA : AdmissionIsProduct) (hw : ConfigurationWeightMeasurable)
    (hFr : FrameLocality.FrameCoordLocal) : AdmissionReadsHull := by
  classical
  intro R hR n _ hs V q hq
  have hn₀ : R.params.n₀ ≤ n := by
    have h1 := hs.2
    have h2 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
    exact (Nat.le_mul_of_pos_left _ h2).trans h1
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [mul_comm R.params.side R.params.n₀]; exact Nat.mul_le_mul_right _ hn₀⟩
  refine ⟨fun Yt b W ν => ∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset,
    fillMarks q (hotCoreSites R V) V bad Yt b (W, ν), ?_, ?_, ?_⟩
  · intro Yt b W ν
    refine le_trans (Finset.sum_le_sum fun bad _ => ?_)
      (sum_markProduct_eq_one hR (hotCoreSites R V) V (q.fieldWithStoredLinks W)).le
    unfold fillMarks
    split_ifs
    · exact le_rfl
    · exact zero_le
  · intro Yt b
    have hD := ((hR.hasExpansions.2.borel (n * R.params.side) hside Yt).1).comp (measurable_fill q Yt)
    have hadm : Measurable fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
        ∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset, fillMarks q (hotCoreSites R V) V bad Yt b p :=
      Finset.measurable_sum _ fun bad _ => measurable_fillMarks hR hside.1 q _ V bad Yt b
    have he : (fun p : TorusField (n * R.params.side) × (q.unlabelled Yt → R.labels.Ω) =>
        (∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset,
            fillMarks q (hotCoreSites R V) V bad Yt b (p.1, p.2)) *
          ENNReal.ofReal (R.labelWeight (n * R.params.side) (q.fieldWithStoredLinks p.1) Yt
            (q.fillLabels Yt p.2))) =
        fun p => (∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset,
            fillMarks q (hotCoreSites R V) V bad Yt b p) *
          ENNReal.ofReal ((fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
            if IsHullState R.params (clusterRange R.coupling) p.1 Yt then
              R.labelWeight (n * R.params.side) p.1 Yt p.2 else 0) (fill q Yt p)) := by
      funext p
      by_cases hh : IsHullState R.params (clusterRange R.coupling) (fill q Yt p).1 Yt
      · beta_reduce
        rw [if_pos hh]
        rfl
      · have hz' : ∀ bad, fillMarks q (hotCoreSites R V) V bad Yt b p = 0 := fun bad => by
          unfold fillMarks
          rw [if_neg]
          exact fun h => hh h.1
        have hz : ∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset,
            fillMarks q (hotCoreSites R V) V bad Yt b p = 0 :=
          Finset.sum_eq_zero fun bad _ => hz' bad
        show (∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset,
            fillMarks q (hotCoreSites R V) V bad Yt b p) * _ =
          (∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset,
            fillMarks q (hotCoreSites R V) V bad Yt b p) * _
        rw [hz, zero_mul, zero_mul]
    exact he ▸ hadm.mul (ENNReal.measurable_ofReal.comp hD)
  · intro V' hC hV
    rw [hC]
    have hG := fun bad Yt b => measurable_fillWeight hw hR hn₀ q (hotCoreSites R V) V' bad Yt b
    unfold coarseStateMass
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Yt _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hstep : ∀ bad, (∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
        (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
            coarseStateOf R (hotCoreSites R V) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
          ENNReal.ofReal (stepWeight R (hotCoreSites R V) V' (q.fieldWithStoredLinks W) Yt
            (q.fillLabels Yt ν) bad b) else 0)
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))) =
        ∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω, fillWeight q (hotCoreSites R V) V' bad Yt b (W, ν)
          ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := fun bad => rfl
    simp only [hstep]
    rw [← lintegral_finsetSum (f := fun bad W => ∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
      fillWeight q (hotCoreSites R V) V' bad Yt b (W, ν) ∂(Measure.pi fun _ => R.labels.μ)) _
      fun bad _ => (hG bad Yt b).lintegral_prod_right']
    refine lintegral_congr fun W => ?_
    rw [← lintegral_finsetSum (f := fun bad ν => fillWeight q (hotCoreSites R V) V' bad Yt b (W, ν)) _
      fun bad _ => (hG bad Yt b).comp measurable_prodMk_left]
    refine lintegral_congr fun ν => ?_
    have hagree := sum_markProduct_congr hA hFr hR hs q hq hV (q.fieldWithStoredLinks W) Yt
      (q.fillLabels Yt ν) b
    have hagree' : ∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset,
        fillMarks q (hotCoreSites R V) V' bad Yt b (W, ν) =
        ∑ bad ∈ (markedBonds R (hotCoreSites R V)).powerset,
          fillMarks q (hotCoreSites R V) V bad Yt b (W, ν) := hagree
    rw [← hagree', Finset.sum_mul]
    refine Finset.sum_congr rfl fun bad _ => ?_
    unfold fillWeight fillMarks
    split_ifs with hp
    · simp only [fill]
      unfold stepWeight
      rw [ENNReal.ofReal_mul' (markProduct_nonneg hR _ V' _ bad), mul_comm]
    · rw [zero_mul]
end YangMills.Construction.ClusterExpansionOfAStep
end
