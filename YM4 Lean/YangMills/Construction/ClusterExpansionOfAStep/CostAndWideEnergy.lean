import YangMills.Construction.ClusterExpansionOfAStep.ChartMovesOfFreeBonds
import YangMills.Construction.ClusterExpansionOfAStep.NearFitsOfASetting
import YangMills.Construction.HoleBesideASecondHole.ActionAtIsACutAction
import YangMills.Construction.HoleBesideASecondHole.CostOnWholeCellsIsTheLeastAction
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.StepCostLocality
open BlockAverages LumpContours HoleSavings FrameTransfer TorusFields TorusLumps StepSettings StepCosts TorusCharts
  QuaternionLogarithm FreeBonds NearFits SettingFits WideCharts FreeBondCharts TorusBlocks TorusContours TorusFrame
  LevelAction RenormalizationStepParameters ColdStepAtMirrorFrames TopLevelSites ColdChain PlainAlignment
theorem actionAtLevel_gaugeTransform (hS : SharesSumToAction) {a δ lam ρ σA cg : ℝ} {L : ℕ} {N : ℕ → ℝ} (ha : 0 < a)
    (hL : Odd L) (hc : ColdChainConstants a δ L lam ρ σA cg N) (t : ℕ) {m : ℕ} [NeZero m] (hm : 64 ≤ m)
    {X : Finset (TorusSite m)} {W : TorusField m} (hreg : IsRegularRegion X 1024) (hcold : IsColdOn σA X W)
    (g : TorusSite m → UnitQuaternion) :
    actionAtLevel a L t X (gaugeTransform g W) = actionAtLevel a L t X W := by
  cases t with
  | zero => exact wilsonAction_gaugeTransform X g W
  | succ t =>
    obtain ⟨hδ, hδ8, hlam, hρ, hρ1, hσ, hcg, hN, hch⟩ := hc
    have hp : ∀ i, (torusFrame L t m).period (torusFrame L t m).top i = m := fun i => period_torusFrame i
    have hreg' : IsOrthantRegular (cellsOfSites (torusFrame L t m) X) 1024 :=
      TorusChain.isOrthantRegular_of_isRegularRegion hp hreg
    have hcold' := TorusChain.isCold_of_isColdOn (F := torusFrame L t m) hp hcold
    obtain ⟨-, -, H3, -⟩ := hch (torusFrame L t m) 1024 _ rfl (Or.inr fun _ => hm) le_rfl hreg' σA _ hσ le_rfl hcold'
    obtain ⟨-, -, -, hG, -⟩ := H3
    rw [← sum_levelShare hS ha.le hL.pos (by omega) (t + 1) X (gaugeTransform g W),
      ← sum_levelShare hS ha.le hL.pos (by omega) (t + 1) X W]
    refine Finset.sum_congr rfl fun y _ => ?_
    show minimalCellShare a (cellsOfSites (torusFrame L t m) X)
        (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top y)
        (readAtLevel (torusFrame L t m) (torusFrame L t m).top (gaugeTransform g W)) =
      minimalCellShare a (cellsOfSites (torusFrame L t m) X)
        (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top y)
        (readAtLevel (torusFrame L t m) (torusFrame L t m).top W)
    rw [readAtLevel_gaugeTransform hp]
    exact hG _ _
theorem continuous_toImaginary : Continuous toImaginary := by
  refine continuous_induced_rng.mpr ?_
  have h : (Subtype.val ∘ toImaginary : ImaginaryCoord → ℍ[ℝ]) = imaginaryCLM := funext coe_toImaginary
  rw [h]
  exact imaginaryCLM.continuous
variable {R : StepSetup} {n : ℕ} [NeZero n] {s : ChartSetting R n} {δ lam σA cg : ℝ} {N : ℕ → ℝ}
omit [NeZero n] in
theorem _root_.YangMills.Construction.StepSettings.ChartSetting.continuous_field (s : ChartSetting R n) :
    Continuous s.field := by
  classical
  refine continuous_pi fun x => continuous_pi fun i => ?_
  unfold ChartSetting.field
  by_cases hf : (x, i) ∈ s.free
  · simp only [dif_pos hf]
    unfold chartLink
    have he : Continuous fun η : FreeCoords s.free => expUnit (s.frame (x, i) + toImaginary (η ⟨(x, i), hf⟩)) :=
      continuous_expUnit.comp (continuous_const.add (continuous_toImaginary.comp (continuous_apply _)))
    refine Continuous.mul (Continuous.mul continuous_const ?_) continuous_const
    split_ifs
    · exact he.mul continuous_const
    · exact he
  · simp only [dif_neg hf]
    exact continuous_const
omit [NeZero n] in
theorem _root_.YangMills.Construction.StepSettings.ChartSetting.field_of_not_mem_free (s : ChartSetting R n)
    (η : FreeCoords s.free) {x : TorusSite (n * R.params.side)} {i : Fin 4}
    (hf : (x, i) ∉ s.free) : s.field η x i = s.fine x i := by
  classical
  unfold ChartSetting.field
  rw [dif_neg hf]
theorem eventually_hot_iff_near (c : s.ChainContext δ lam σA cg N) {η₀ : FreeCoords s.free} (hη₀ : s.InBalls η₀) :
    ∀ᶠ η in 𝓝 η₀, ∀ p : TorusPlaquette (n * R.params.side), p.2.1 < p.2.2 →
      (R.params.threshold ≤ curvature (s.field η) p.1 p.2.1 p.2.2 ↔
        R.params.threshold ≤ curvature (s.field η₀) p.1 p.2.1 p.2.2) := by
  classical
  have hσ := c.params_admissible.σ_pos
  refine Filter.eventually_all.mpr fun p => ?_
  by_cases hlt : p.2.1 < p.2.2
  · by_cases ht : ∃ b ∈ s.free, supDist p.1 b.1 ≤ 3 * R.range
    · obtain ⟨b, hb, hd⟩ := ht
      have h0 : curvature (s.field η₀) p.1 p.2.1 p.2.2 < R.params.threshold :=
        (c.admissible.curvature_lt η₀ hη₀ b hb p.1 p.2.1 p.2.2 hlt hd).trans (by linarith)
      have hc : Continuous fun η => curvature (s.field η) p.1 p.2.1 p.2.2 :=
        (continuous_curvature p.1 p.2.1 p.2.2).comp s.continuous_field
      filter_upwards [hc.continuousAt.eventually (gt_mem_nhds h0)] with η hη _
      exact iff_of_false (not_le.mpr hη) (not_le.mpr h0)
    · have hbig := c.large_range.range_large
      have hoff : ∀ (y : TorusSite (n * R.params.side)) (i : Fin 4), supDist p.1 y ≤ 2 → (y, i) ∉ s.free := by
        intro y i hy hf
        refine ht ⟨(y, i), hf, ?_⟩
        show supDist p.1 y ≤ 3 * R.range
        omega
      have m1 : supDist p.1 p.1 ≤ 2 := by rw [supDist_self]; omega
      have m2 : supDist p.1 (p.1 + TorusFields.unitStep (n * R.params.side) p.2.1) ≤ 2 :=
        (supDist_add_unitStep_le _ _).trans (by omega)
      have m3 : supDist p.1 (p.1 + TorusFields.unitStep (n * R.params.side) p.2.2) ≤ 2 :=
        (supDist_add_unitStep_le _ _).trans (by omega)
      have hsame : ∀ η, curvature (s.field η) p.1 p.2.1 p.2.2 = curvature s.fine p.1 p.2.1 p.2.2 := by
        intro η
        unfold curvature holonomy
        rw [s.field_of_not_mem_free η (hoff _ p.2.1 m1), s.field_of_not_mem_free η (hoff _ p.2.2 m2),
          s.field_of_not_mem_free η (hoff _ p.2.1 m3), s.field_of_not_mem_free η (hoff _ p.2.2 m1)]
      refine Filter.Eventually.of_forall fun η _ => ?_
      rw [hsame, hsame]
  · exact Filter.Eventually.of_forall fun _ h => absurd h hlt
theorem torusHotLumps_eq_of_hot_iff (c : s.ChainContext δ lam σA cg N) {W W' : TorusField (n * R.params.side)}
    (hp : ∀ p : TorusPlaquette (n * R.params.side), p.2.1 < p.2.2 →
      (R.params.threshold ≤ curvature W p.1 p.2.1 p.2.2 ↔ R.params.threshold ≤ curvature W' p.1 p.2.1 p.2.2)) :
    torusHotLumps R.params W = torusHotLumps R.params W' := by
  classical
  refine torusHotLumps_eq_of_hotPlaquettes_eq c.params_admissible (Dvd.intro_left n rfl) ?_
  ext p
  simp only [hotPlaquettes, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (hp p h1).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (hp p h1).mpr h2⟩
theorem stepHotLumps_eq_of_hot_iff {W W' : TorusField (n * R.params.side)}
    (hp : ∀ p : TorusPlaquette (n * R.params.side), p.2.1 < p.2.2 →
      (R.params.threshold ≤ curvature W p.1 p.2.1 p.2.2 ↔ R.params.threshold ≤ curvature W' p.1 p.2.1 p.2.2)) :
    stepHotLumps R.params W = stepHotLumps R.params W' := by
  classical
  have hP := stepBlockFrame_period_zero R n
  unfold stepHotLumps hotLumps
  have hf : (cutPlaquettes (levelSites (stepBlockFrame R.params.side n) 0)).filter
      (fun q => R.params.threshold ≤ plaquetteDefect (readAtLevel (stepBlockFrame R.params.side n) 0 W) q) =
      (cutPlaquettes (levelSites (stepBlockFrame R.params.side n) 0)).filter
      (fun q => R.params.threshold ≤ plaquetteDefect (readAtLevel (stepBlockFrame R.params.side n) 0 W') q) := by
    refine Finset.filter_congr fun q hq => ?_
    obtain ⟨x, μ, ν⟩ := q
    have hlt : μ < ν := (Finset.mem_filter.mp hq).2.1
    rw [TopLevelSites.plaquetteDefect_readAtLevel_eq (F := stepBlockFrame R.params.side n) (j := 0) hP,
      TopLevelSites.plaquetteDefect_readAtLevel_eq (F := stepBlockFrame R.params.side n) (j := 0) hP]
    exact hp (toTorusSite (n * R.params.side) x, μ, ν) hlt
  rw [hf]
theorem costSum_eventuallyEq_near (hS : SharesSumToAction) (c : s.ChainContext δ lam σA cg N)
    {η₀ : FreeCoords s.free} (hη₀ : s.InBalls η₀) :
    ∃ K : ℝ, s.costSum =ᶠ[𝓝 η₀] fun η => K + (actionAtLevel R.params.coupling R.params.side R.depth s.coolRegion
      (torusChart R.params.side (s.coordinates η) s.coarse) +
      s.nearFitSum (torusChart R.params.side (s.coordinates η) s.coarse)) := by
  classical
  have hfit := c.params_admissible
  have hL := hfit.L_odd
  have h2 := c.two_le
  have hchart := c.admissible.subset_chart
  have hbases : IsBaseChoice R.params.baseDepth (stepHotLumps R.params s.fine) s.bases := c.admissible.isBaseChoice
  have ha : 0 < R.params.coupling := by linarith [hfit.a_ge]
  have h64 : 64 ≤ n * R.params.side := by
    have h3 := hfit.n₀_ge
    have h4 := c.n₀_le
    have h5 := hL.pos
    nlinarith
  refine ⟨R.params.coupling * ∑ d ∈ Finset.univ \ s.nearBonds, bondFit R.params (s.field η₀) s.coarse s.bases d, ?_⟩
  filter_upwards [eventually_hot_iff_near c hη₀] with η hp
  have hhot : torusHotLumps R.params (s.field η) = torusHotLumps R.params s.fine :=
    (torusHotLumps_eq_of_hot_iff c hp).trans (c.admissible.hotLumps_eq η₀ hη₀)
  have hsites : torusHotSites R.params (s.field η) = torusHotSites R.params s.fine := by
    unfold torusHotSites
    rw [hhot]
  have hstep := stepHotLumps_eq_of_hot_iff hp
  rw [ChartSetting.costSum_eq hS hfit h2 s η hsites]
  have hcold : IsColdOn σA s.coolRegion (s.field η) :=
    isColdOn_coolRegion hfit (by linarith [hfit.σ_pos, c.threshold_le]) s hsites
  have hreg := isRegularRegion_coolRegion c.complement_regular hfit s
  have e1 : actionAtLevel R.params.coupling R.params.side R.depth s.coolRegion (s.field η) =
      actionAtLevel R.params.coupling R.params.side R.depth s.coolRegion
        (torusChart R.params.side (s.coordinates η) s.coarse) := by
    rw [← ChartSetting.gaugeTransform_field_eq_torusChart hL h2 s hchart η]
    exact (actionAtLevel_gaugeTransform hS ha hL c.chain R.depth h64 hreg hcold _).symm
  have hsplit := Finset.sum_sdiff (s₁ := s.nearBonds) (s₂ := Finset.univ)
    (f := fun d => bondFit R.params (s.field η) s.coarse s.bases d) (Finset.subset_univ _)
  have hfar : ∑ d ∈ Finset.univ \ s.nearBonds, bondFit R.params (s.field η) s.coarse s.bases d =
      ∑ d ∈ Finset.univ \ s.nearBonds, bondFit R.params (s.field η₀) s.coarse s.bases d := by
    refine Finset.sum_congr rfl fun d hd => ?_
    refine bondFit_congr_far c (Finset.mem_sdiff.mp hd).2 hstep fun x i hf => ?_
    rw [s.field_of_not_mem_free η hf, s.field_of_not_mem_free η₀ hf]
  have hnear : ∑ d ∈ s.nearBonds, bondFit R.params (s.field η) s.coarse s.bases d =
      ∑ d ∈ s.nearBonds, plainAlignmentDefect R.params.side d.1 d.2 (s.coarse d.1 d.2)
        (torusChart R.params.side (s.coordinates η) s.coarse) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨b₀, hb₀, hbd⟩ := mem_nearBonds.mp hd
    have hd2 : supDist (parentBlock R.params.side b₀.1) (d.1 + TorusFields.unitStep n d.2) ≤ 17 := by
      have e1 := supDist_add_unitStep_le d.1 d.2
      have e2 := supDist_triangle (parentBlock R.params.side b₀.1) d.1 (d.1 + TorusFields.unitStep n d.2)
      omega
    have hd1 : supDist (parentBlock R.params.side b₀.1) d.1 ≤ 17 := by omega
    have l1 := nearbyLumps_stepHotLumps_eq_empty hfit h2 c.admissible c.large_range hsites hb₀ hd1
    have l3 := nearbyLumps_stepHotLumps_eq_empty hfit h2 c.admissible c.large_range hsites hb₀ hd2
    have k1 := nearbyLumps_stepHotLumps_eq_empty hfit h2 c.admissible c.large_range rfl hb₀ hd1
    have k3 := nearbyLumps_stepHotLumps_eq_empty hfit h2 c.admissible c.large_range rfl hb₀ hd2
    have hb1 := (hbases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 d.1)).1 (Or.inl k1)
    have hb2 := (hbases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (d.1 + TorusFields.unitStep n d.2))).1 (Or.inl k3)
    have e := bondFit_eq_plainAlignmentDefect hfit c.baseDepth_pos h2 s d.1 d.2 l1 l3 hb1 hb2
    rw [ChartSetting.gaugeTransform_field_eq_torusChart hL h2 s hchart η] at e
    exact e
  rw [e1, ← hsplit, hnear, hfar]
  unfold ChartSetting.nearFitSum
  ring
def _root_.YangMills.Construction.StepSettings.ChartSetting.wideField (s : ChartSetting R n)
    (w : (topFrame R n).Site (topFrame R n).depth → Fin 4 → imaginaryQuaternions) (η₀ ζ : FreeCoords s.free) :
    TorusField (n * R.params.side) :=
  torusChart R.params.side (shiftedCoords s.free (s.wideCoords w η₀) ζ) s.coarse
def _root_.YangMills.Construction.StepSettings.ChartSetting.wideFrameCoords (s : ChartSetting R n)
    (w : (topFrame R n).Site (topFrame R n).depth → Fin 4 → imaginaryQuaternions) (η₀ ζ : FreeCoords s.free)
    (x : (topFrame R n).Site (topFrame R n).depth) (i : Fin 4) : imaginaryQuaternions :=
  shiftedCoords s.free (s.wideCoords w η₀) ζ (toTorusSite (n * R.params.side) x, i)
theorem chartedField_wideFrameCoords (c : s.ChainContext δ lam σA cg N)
    (w : (topFrame R n).Site (topFrame R n).depth → Fin 4 → imaginaryQuaternions) (η₀ ζ : FreeCoords s.free) :
    chartedField (s.wideFrameCoords w η₀ ζ) s.topGaugeField =
      readAtLevel (topFrame R n) (topFrame R n).depth (s.wideField w η₀ ζ) := by
  have hn := topFrame_extent R n
  funext x i
  have h : chartedField (s.wideFrameCoords w η₀ ζ) s.topGaugeField
      (topSite R n (toTorusSite (n * R.params.side) x)) i =
      torusChart R.params.side (fun b : TorusBond (n * R.params.side) => s.wideFrameCoords w η₀ ζ (topSite R n b.1) b.2)
        s.coarse (toTorusSite (n * R.params.side) x) i :=
    chartedField_readAtLevel (F := topFrame R n) hn c.params_admissible.L_odd c.two_le (s.wideFrameCoords w η₀ ζ)
      s.coarse (toTorusSite (n * R.params.side) x) i
  rw [topSite_toTorusSite] at h
  rw [h]
  have e : (fun b : TorusBond (n * R.params.side) => s.wideFrameCoords w η₀ ζ (topSite R n b.1) b.2) =
      shiftedCoords s.free (s.wideCoords w η₀) ζ := by
    funext b
    unfold ChartSetting.wideFrameCoords
    rw [toTorusSite_topSite]
  rw [e]
  rfl
theorem sitesOfCells_regionCells (c : s.ChainContext δ lam σA cg N) :
    sitesOfCells s.regionCells (topFrame R n).depth =
      sitesOfTorus (topFrame R n) (topFrame R n).depth s.sitesUnderRegion := by
  classical
  have hn := topFrame_extent R n
  have hP := topFrame_period R n
  have hL : Odd (topFrame R n).blockSide := c.params_admissible.L_odd
  have hs : ∀ i, 2 ≤ (topFrame R n).extent i := fun _ => c.two_le
  ext x
  unfold sitesOfTorus
  rw [Finset.mem_image]
  constructor
  · intro hx
    refine ⟨toTorusSite (n * R.params.side) x, ?_, torusSiteInFrame_toTorusSite hP x⟩
    obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.mp hx
    rw [TopLevelSites.top_sub_depth, pow_one] at hh
    have h1 := enclosingCell_centre_add hL hs y h hh
    have h2 := enclosingCell_torusSiteInFrame hn (toTorusSite (n * (topFrame R n).blockSide)
      (cellCentre (topFrame R n).depth y + siteOfCoords (topFrame R n).depth h))
    rw [torusSiteInFrame_toTorusSite (period_depth_of_extent hn), h1] at h2
    unfold ChartSetting.sitesUnderRegion sitesInBlocks
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h3 : toTorusSite n y ∈ s.region := (TopLevelSites.mem_cellsOfSites_iff hn).mp hy
    rw [h2, toTorusSite_torusSiteInFrame (period_top_of_extent hn)] at h3
    exact h3
  · rintro ⟨u, hu, rfl⟩
    exact torusSiteInFrame_mem_sitesOfCells hn hL c.two_le u (Finset.mem_filter.mp hu).2
theorem blockEnergy_wideField (hC : WholeCellCostEqualsMinimalAction) (hA : ActionAtLevelIsCutAction)
    (c : s.ChainContext δ lam σA cg N)
    (w : (topFrame R n).Site (topFrame R n).depth → Fin 4 → imaginaryQuaternions) (η₀ : FreeCoords s.free) :
    ∃ K : ℝ, ∀ ζ : FreeCoords s.free,
      blockEnergy R.params.coupling s.regionCells (topFrame R n).depth
          (chartedField (s.wideFrameCoords w η₀ ζ) s.topGaugeField) s.topGaugeField =
        K + (actionAtLevel R.params.coupling R.params.side R.depth s.sitesUnderRegion (s.wideField w η₀ ζ) +
          s.nearFitSum (s.wideField w η₀ ζ)) := by
  classical
  have hfit := c.params_admissible
  have hL : Odd (topFrame R n).blockSide := hfit.L_odd
  have ha : 0 ≤ R.params.coupling := by linarith [hfit.a_ge]
  have hn := topFrame_extent R n
  set Cs : Finset (TorusBond n) := Finset.univ.filter fun d => d.1 ∈ s.region ∧ d.1 + TorusFields.unitStep n d.2 ∈ s.region
    with hCs
  have hsub : s.nearBonds ⊆ Cs := by
    intro d hd
    obtain ⟨b₀, hb₀, hbd⟩ := mem_nearBonds.mp hd
    have hbig := c.large_range.range_large
    have k1 : parentBlock R.params.side (blockCentreSite R.params.side d.1) ∈ s.region := by
      refine parentBlock_mem_region_of_near_free c.admissible c.large_range hb₀ ?_
      have := supDist_le_of_near_block c (b₀ := b₀) (Y := d.1) (by omega) (x := blockCentreSite R.params.side d.1)
        (by rw [supDist_self]; omega)
      omega
    have hd2 : supDist (parentBlock R.params.side b₀.1) (d.1 + TorusFields.unitStep n d.2) ≤ 17 := by
      have e1 := supDist_add_unitStep_le d.1 d.2
      have e2 := supDist_triangle (parentBlock R.params.side b₀.1) d.1 (d.1 + TorusFields.unitStep n d.2)
      omega
    have k2 : parentBlock R.params.side (blockCentreSite R.params.side (d.1 + TorusFields.unitStep n d.2)) ∈ s.region := by
      refine parentBlock_mem_region_of_near_free c.admissible c.large_range hb₀ ?_
      have := supDist_le_of_near_block c (b₀ := b₀) (Y := d.1 + TorusFields.unitStep n d.2) (by omega)
        (x := blockCentreSite R.params.side (d.1 + TorusFields.unitStep n d.2)) (by rw [supDist_self]; omega)
      omega
    rw [parentBlock_blockCentreSite hfit.L_odd] at k1 k2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k1, k2⟩
  refine ⟨R.params.coupling * ∑ d ∈ Cs \ s.nearBonds,
    plainAlignmentDefect R.params.side d.1 d.2 (s.coarse d.1 d.2) (s.wideField w η₀ 0), fun ζ => ?_⟩
  obtain ⟨h1, -, h3⟩ := hC (topFrame R n) R.params.coupling s.regionCells hL ha
  rw [← h3]
  unfold plainBlockEnergy
  rw [h1 (topFrame R n).depth (by simp [BlockFrame.top]), sitesOfCells_regionCells c,
    chartedField_wideFrameCoords c w η₀ ζ]
  have hact : cutEffectiveAction R.params.coupling (topFrame R n).depth
      (sitesOfTorus (topFrame R n) (topFrame R n).depth s.sitesUnderRegion)
      (readAtLevel (topFrame R n) (topFrame R n).depth (s.wideField w η₀ ζ)) =
      actionAtLevel R.params.coupling R.params.side R.depth s.sitesUnderRegion (s.wideField w η₀ ζ) :=
    (hA R.params.coupling ha R.params.side hL n (topFrame R n) rfl hn).2 s.sitesUnderRegion (s.wideField w η₀ ζ)
  rw [hact]
  have hbonds : cutBonds s.regionCells =
      Cs.image fun d : TorusBond n => (torusSiteInFrame (topFrame R n) (topFrame R n).top d.1, d.2) := by
    ext ⟨y, i⟩
    simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, Finset.mem_image, hCs,
      true_and, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨toTorusSite n y, i, ⟨(TopLevelSites.mem_cellsOfSites_iff hn).mp h1, ?_⟩,
        torusSiteInFrame_toTorusSite (period_top_of_extent hn) y, rfl⟩
      have := (TopLevelSites.mem_cellsOfSites_iff hn).mp h2
      rwa [TopLevelSites.toTorusSite_add (period_top_of_extent hn),
        TopLevelSites.toTorusSite_unitStep (period_top_of_extent hn)] at this
    · rintro ⟨Y, i', ⟨k1, k2⟩, rfl, rfl⟩
      refine ⟨(torusSiteInFrame_mem_cellsOfSites_iff hn).mpr k1, ?_⟩
      rw [TopLevelSites.mem_cellsOfSites_iff hn, TopLevelSites.toTorusSite_add (period_top_of_extent hn),
        toTorusSite_torusSiteInFrame (period_top_of_extent hn),
        TopLevelSites.toTorusSite_unitStep (period_top_of_extent hn)]
      exact k2
  have hinj : Set.InjOn (fun d : TorusBond n => ((torusSiteInFrame (topFrame R n) (topFrame R n).top d.1, d.2) :
      (topFrame R n).Cell × Fin 4)) Cs := by
    rintro ⟨Y, i⟩ _ ⟨Y', i'⟩ _ h
    have e1 : torusSiteInFrame (topFrame R n) (topFrame R n).top Y =
        torusSiteInFrame (topFrame R n) (topFrame R n).top Y' := congrArg Prod.fst h
    have e2 : i = i' := congrArg Prod.snd h
    have e3 := congrArg (toTorusSite n) e1
    rw [toTorusSite_torusSiteInFrame (period_top_of_extent hn),
      toTorusSite_torusSiteInFrame (period_top_of_extent hn)] at e3
    exact Prod.ext e3 e2
  rw [hbonds, Finset.sum_image hinj]
  have hfit1 : ∀ d : TorusBond n, blockFit (readAtLevel (topFrame R n) (topFrame R n).depth (s.wideField w η₀ ζ))
      s.topGaugeField (torusSiteInFrame (topFrame R n) (topFrame R n).top d.1, d.2) =
      plainAlignmentDefect R.params.side d.1 d.2 (s.coarse d.1 d.2) (s.wideField w η₀ ζ) :=
    fun d => blockFit_readAtLevel hn (s.wideField w η₀ ζ) s.coarse d.1 d.2
  simp only [hfit1]
  have hsplit := Finset.sum_sdiff (s₁ := s.nearBonds) (s₂ := Cs)
    (f := fun d : TorusBond n => plainAlignmentDefect R.params.side d.1 d.2 (s.coarse d.1 d.2) (s.wideField w η₀ ζ))
    hsub
  have hfar : ∑ d ∈ Cs \ s.nearBonds,
      plainAlignmentDefect R.params.side d.1 d.2 (s.coarse d.1 d.2) (s.wideField w η₀ ζ) =
      ∑ d ∈ Cs \ s.nearBonds,
        plainAlignmentDefect R.params.side d.1 d.2 (s.coarse d.1 d.2) (s.wideField w η₀ 0) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    refine plainAlignmentDefect_congr_far c (Finset.mem_sdiff.mp hd).2 _ fun x i hf => ?_
    unfold ChartSetting.wideField
    refine torusChart_congr s.coarse ?_
    unfold shiftedCoords
    rw [dif_neg hf, dif_neg hf]
  rw [← hsplit, hfar]
  unfold ChartSetting.nearFitSum
  ring
end YangMills.Construction.StepCostLocality
end
