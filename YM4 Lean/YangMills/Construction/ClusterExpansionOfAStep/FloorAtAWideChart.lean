import YangMills.Construction.ClusterExpansionOfAStep.CostAsMoves
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.WideChartFloor
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n] {s : StepSettings.ChartSetting R n}
  {δ lam σA cg : ℝ} {N : ℕ → ℝ}
theorem norm_torusChart_sub_le {L : ℕ} (w w' : TorusFields.TorusBond (n * L) → BlockAverages.imaginaryQuaternions)
    (V : TorusFields.TorusField n) (x : TorusFields.TorusSite (n * L)) (i : Fin 4) :
    ‖((TorusCharts.torusChart L w V x i : BlockAverages.UnitQuaternion) : ℍ[ℝ]) -
        ((TorusCharts.torusChart L w' V x i : BlockAverages.UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖((w (x, i) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) -
        ((w' (x, i) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ := by
  classical
  unfold TorusCharts.torusChart
  by_cases hend : TorusCharts.IsBlockEndBond L x i
  · rw [if_pos hend, if_pos hend]
    have hmul := TopLevelSites.norm_mul_sub_mul_le (BlockAverages.expUnit (w (x, i)))
      (BlockAverages.expUnit (w' (x, i))) (V (TorusLumps.parentBlock L x) i) (V (TorusLumps.parentBlock L x) i)
    have hzero : ‖((V (TorusLumps.parentBlock L x) i : BlockAverages.UnitQuaternion) : ℍ[ℝ]) -
        ((V (TorusLumps.parentBlock L x) i : BlockAverages.UnitQuaternion) : ℍ[ℝ])‖ = 0 := by simp
    rw [hzero, add_zero] at hmul
    exact hmul.trans (TopLevelSites.norm_expUnit_sub_le _ _)
  · rw [if_neg hend, if_neg hend]
    by_cases htree : TorusCharts.IsBlockTreeBond L x i
    · rw [if_pos htree, if_pos htree, sub_self, norm_zero]
      exact norm_nonneg _
    · rw [if_neg htree, if_neg htree]
      exact TopLevelSites.norm_expUnit_sub_le _ _
theorem chartedField_minimizer_eq (c : s.ChainContext δ lam σA cg N)
    (w : (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth → Fin 4 →
      BlockAverages.imaginaryQuaternions) :
    BlockAverages.chartedField w s.topGaugeField =
      TorusFields.readAtLevel (WideCharts.topFrame R n) (WideCharts.topFrame R n).depth
        (TorusCharts.torusChart R.params.side (WideCharts.minimizerOnTorus R n w) s.coarse) := by
  have hext := WideCharts.topFrame_extent R n
  funext x i
  have hread : BlockAverages.chartedField w s.topGaugeField
      (WideCharts.topSite R n (TorusLumps.toTorusSite (n * R.params.side) x)) i =
      TorusCharts.torusChart R.params.side (WideCharts.minimizerOnTorus R n w) s.coarse
        (TorusLumps.toTorusSite (n * R.params.side) x) i :=
    TorusCharts.chartedField_readAtLevel (F := WideCharts.topFrame R n) hext c.params_admissible.L_odd c.two_le w
      s.coarse (TorusLumps.toTorusSite (n * R.params.side) x) i
  rw [WideCharts.topSite_toTorusSite] at hread
  exact hread
theorem curvature_wideChartAt_lt (c : s.ChainContext δ lam σA cg N) {σ' : ℝ}
    {w : (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth → Fin 4 →
      BlockAverages.imaginaryQuaternions}
    (d : s.MinimizerData lam σA (N 0) σ' w) {η₀ : StepSettings.FreeCoords s.free} (hη₀ : s.InBalls η₀)
    {x : TorusFields.TorusSite (n * R.params.side)} {μ ν : Fin 4}
    (hp : ((WideCharts.topSite R n x, μ, ν) :
        (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth × Fin 4 × Fin 4) ∈
      BlockAverages.innerPlaquettes s.regionCells (WideCharts.topFrame R n).depth) :
    TorusFields.curvature (s.wideChartAt w η₀) x μ ν < σA := by
  have hper := WideCharts.topFrame_period R n
  have hthr := c.params_admissible.σ_pos
  have hmin : TorusFields.curvature
      (TorusCharts.torusChart R.params.side (WideCharts.minimizerOnTorus R n w) s.coarse) x μ ν < σ' / 8 := by
    have hc := d.cold _ hp
    rw [chartedField_minimizer_eq c w, TopLevelSites.plaquetteDefect_readAtLevel_eq hper,
      WideCharts.toTorusSite_topSite] at hc
    exact hc
  have hclose : ∀ (y : TorusFields.TorusSite (n * R.params.side)) (j : Fin 4),
      ‖((s.wideChartAt w η₀ y j : BlockAverages.UnitQuaternion) : ℍ[ℝ]) -
        ((TorusCharts.torusChart R.params.side (WideCharts.minimizerOnTorus R n w) s.coarse y j :
          BlockAverages.UnitQuaternion) : ℍ[ℝ])‖ ≤ 2 * R.ballRadius := fun y j =>
    (norm_torusChart_sub_le _ _ _ _ _).trans (WideCharts.wideCoords_close c d hη₀ _)
  have hadd := TopLevelSites.curvature_le_add (s.wideChartAt w η₀)
    (TorusCharts.torusChart R.params.side (WideCharts.minimizerOnTorus R n w) s.coarse) x μ ν
  have h1 := hclose x μ
  have h2 := hclose (x + TorusFields.unitStep (n * R.params.side) μ) ν
  have h3 := hclose (x + TorusFields.unitStep (n * R.params.side) ν) μ
  have h4 := hclose x ν
  have hball : R.ballRadius = R.params.threshold / 64 := rfl
  have hle := d.le_two_mul
  have hsig := c.threshold_le
  linarith
theorem mem_innerPlaquettes_of_mem_plaquettesIn (c : s.ChainContext δ lam σA cg N)
    {p : TorusFields.TorusPlaquette (n * R.params.side)} (hp : p ∈ TorusFields.plaquettesIn s.sitesUnderRegion) :
    ((WideCharts.topSite R n p.1, p.2.1, p.2.2) :
        (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth × Fin 4 × Fin 4) ∈
      BlockAverages.innerPlaquettes s.regionCells (WideCharts.topFrame R n).depth := by
  classical
  obtain ⟨hlt, hcorner⟩ := TorusFields.mem_plaquettesIn.mp hp
  have hext := WideCharts.topFrame_extent R n
  have hper := WideCharts.topFrame_period R n
  have hsite : ∀ u ∈ s.sitesUnderRegion,
      WideCharts.topSite R n u ∈ BlockAverages.sitesOfCells s.regionCells (WideCharts.topFrame R n).depth :=
    fun u hu => TopLevelSites.torusSiteInFrame_mem_sitesOfCells hext c.params_admissible.L_odd c.two_le u
      (Finset.mem_filter.mp hu).2
  have hstep : ∀ (u : TorusFields.TorusSite (n * R.params.side)) (i : Fin 4),
      WideCharts.topSite R n (u + TorusFields.unitStep (n * R.params.side) i) =
        WideCharts.topSite R n u + BlockAverages.unitStep (WideCharts.topFrame R n).depth i := by
    intro u i
    apply TopLevelSites.toTorusSite_injective hper
    rw [WideCharts.toTorusSite_topSite, TopLevelSites.toTorusSite_add hper, WideCharts.toTorusSite_topSite,
      TopLevelSites.toTorusSite_unitStep hper]
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨hsite _ (hcorner _ (TorusLumps.base_mem_plaquetteVertices _ _ _)), by simp⟩, hlt, ?_⟩
  intro y hy
  simp only [BlockAverages.plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact hsite _ (hcorner _ (TorusLumps.base_mem_plaquetteVertices _ _ _))
  · rw [← hstep]
    exact hsite _ (hcorner _ (by simp [TorusFields.plaquetteVertices]))
  · rw [← hstep]
    exact hsite _ (hcorner _ (by simp [TorusFields.plaquetteVertices]))
  · rw [← hstep, ← hstep]
    exact hsite _ (hcorner _ (by simp [TorusFields.plaquetteVertices]))
theorem isColdOn_wideChartAt (c : s.ChainContext δ lam σA cg N) {σ' : ℝ}
    {w : (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth → Fin 4 →
      BlockAverages.imaginaryQuaternions}
    (d : s.MinimizerData lam σA (N 0) σ' w) {η₀ : StepSettings.FreeCoords s.free} (hη₀ : s.InBalls η₀) :
    LevelAction.IsColdOn σA s.sitesUnderRegion (s.wideChartAt w η₀) := fun _ hp =>
  curvature_wideChartAt_lt c d hη₀ (mem_innerPlaquettes_of_mem_plaquettesIn c hp)
theorem isColdOn_chartedFieldAt (c : s.ChainContext δ lam σA cg N) {η₀ : StepSettings.FreeCoords s.free}
    (hη₀ : s.InBalls η₀) : LevelAction.IsColdOn σA s.coolRegion (s.chartedFieldAt η₀) := by
  have hhot : TorusLumps.torusHotSites R.params (s.field η₀) = TorusLumps.torusHotSites R.params s.fine := by
    unfold TorusLumps.torusHotSites
    rw [c.admissible.hotLumps_eq η₀ hη₀]
  have hcold : LevelAction.IsColdOn σA s.coolRegion (s.field η₀) :=
    FreeBonds.isColdOn_coolRegion c.params_admissible
      (by linarith [c.params_admissible.σ_pos, c.threshold_le]) s hhot
  have hgauge := StepSettings.ChartSetting.gaugeTransform_field_eq_torusChart c.params_admissible.L_odd c.two_le s
    c.admissible.subset_chart η₀
  show LevelAction.IsColdOn σA s.coolRegion (TorusCharts.torusChart R.params.side (s.coordinates η₀) s.coarse)
  rw [← hgauge]
  exact FreeBonds.isColdOn_gaugeTransform hcold _
theorem shiftedCoords_wideCoords_zero
    (w : (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth → Fin 4 →
      BlockAverages.imaginaryQuaternions) (η₀ : StepSettings.FreeCoords s.free) :
    FreeBondCharts.shiftedCoords s.free (s.wideCoords w η₀) 0 = s.wideCoords w η₀ := by
  classical
  funext b
  unfold FreeBondCharts.shiftedCoords
  split_ifs
  · simp [FreeBondMoves.toImaginary_zero]
  · rfl
theorem hessian_wideChartEnergy_ge (c : s.ChainContext δ lam σA cg N) {σ' : ℝ}
    {w : (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth → Fin 4 →
      BlockAverages.imaginaryQuaternions}
    (d : s.MinimizerData lam σA (N 0) σ' w) {η₀ : StepSettings.FreeCoords s.free} (hη₀ : s.InBalls η₀)
    (v : StepSettings.FreeCoords s.free) :
    lam * ∑ b, ‖v b‖ ^ 2 ≤ deriv (deriv fun τ : ℝ => s.wideChartEnergy w η₀ (η₀ + τ • v)) 0 := by
  classical
  have hper := WideCharts.topFrame_period R n
  have hlam : 0 < lam := c.chain.2.2.1
  set dw : (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth → Fin 4 →
      BlockAverages.imaginaryQuaternions := fun x i =>
    if h : (TorusLumps.toTorusSite (n * R.params.side) x, i) ∈ s.free then
      ColdStepAtMirrorFrames.toImaginary (v ⟨_, h⟩) else 0 with hdw
  have hfree : ∀ (x : (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth) (i : Fin 4),
      (TorusLumps.toTorusSite (n * R.params.side) x, i) ∈ s.free →
      (x, i) ∈ BlockAverages.chordBonds s.regionCells := by
    intro x i hf
    have hchord := (WideCharts.mem_chordBonds_of_isNearFree c (ClusterExpansionOfAStep.isNearFree_of_mem_free hf)
      (ClusterExpansionOfAStep.not_isBlockTreeBond_of_mem_free c _ hf)).2
    simp only at hchord
    rwa [WideCharts.topSite_toTorusSite] at hchord
  have hw0 : ∀ (x : (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth) (i : Fin 4),
      s.wideFrameCoords w η₀ 0 x i = s.wideCoords w η₀ (TorusLumps.toTorusSite (n * R.params.side) x, i) := by
    intro x i
    unfold StepSettings.ChartSetting.wideFrameCoords
    rw [shiftedCoords_wideCoords_zero]
  have hz : ∀ b, b ∉ BlockAverages.chordBonds s.regionCells → s.wideFrameCoords w η₀ 0 b.1 b.2 = 0 := by
    rintro ⟨x, i⟩ hb
    rw [hw0]
    unfold StepSettings.ChartSetting.wideCoords
    rw [if_neg]
    · unfold WideCharts.minimizerOnTorus
      simp only
      rw [WideCharts.topSite_toTorusSite]
      exact d.isMinimizing.1 (x, i) hb
    · rintro ⟨-, h2, -⟩
      simp only at h2
      rw [WideCharts.topSite_toTorusSite] at h2
      exact hb h2
  have hdz : ∀ b, b ∉ BlockAverages.chordBonds s.regionCells → dw b.1 b.2 = 0 := by
    rintro ⟨x, i⟩ hb
    simp only [hdw]
    rw [dif_neg fun hf => hb (hfree x i hf)]
  have hsize : ∀ b ∈ BlockAverages.chordBonds s.regionCells,
      ‖s.wideFrameCoords w η₀ 0 b.1 b.2‖ ≤ R.anchorRadius := by
    rintro ⟨x, i⟩ hb
    rw [hw0]
    have h1 := WideCharts.wideCoords_close c d hη₀ (TorusLumps.toTorusSite (n * R.params.side) x, i)
    have h2 : ‖((WideCharts.minimizerOnTorus R n w (TorusLumps.toTorusSite (n * R.params.side) x, i) :
        BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤ min R.anchorRadius (N 0 * σ') := by
      unfold WideCharts.minimizerOnTorus
      simp only
      rw [WideCharts.topSite_toTorusSite]
      exact d.isMinimizing.2.1 (x, i) hb
    have h3 : ‖((s.wideCoords w η₀ (TorusLumps.toTorusSite (n * R.params.side) x, i) :
          BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        ‖((s.wideCoords w η₀ (TorusLumps.toTorusSite (n * R.params.side) x, i) :
            BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) -
          ((WideCharts.minimizerOnTorus R n w (TorusLumps.toTorusSite (n * R.params.side) x, i) :
            BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ +
        ‖((WideCharts.minimizerOnTorus R n w (TorusLumps.toTorusSite (n * R.params.side) x, i) :
          BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ := by
      have htri := norm_add_le (((s.wideCoords w η₀ (TorusLumps.toTorusSite (n * R.params.side) x, i) :
            BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) -
          ((WideCharts.minimizerOnTorus R n w (TorusLumps.toTorusSite (n * R.params.side) x, i) :
            BlockAverages.imaginaryQuaternions) : ℍ[ℝ]))
        ((WideCharts.minimizerOnTorus R n w (TorusLumps.toTorusSite (n * R.params.side) x, i) :
          BlockAverages.imaginaryQuaternions) : ℍ[ℝ])
      rwa [sub_add_cancel] at htri
    have h4 : N 0 * σ' ≤ 2 * N 0 * R.params.threshold := by
      have hN0 := c.chain.2.2.2.2.2.2.2.1 0
      have hle := d.le_two_mul
      nlinarith
    have h5 := c.anchor_ge
    have h6 := min_le_right R.anchorRadius (N 0 * σ')
    show ‖((s.wideCoords w η₀ (TorusLumps.toTorusSite (n * R.params.side) x, i) :
      BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤ R.anchorRadius
    linarith
  have hcold : BlockAverages.IsCold s.regionCells (WideCharts.topFrame R n).depth σA
      (BlockAverages.chartedField (s.wideFrameCoords w η₀ 0) s.topGaugeField) := by
    rintro ⟨x, μ, ν⟩ hp
    rw [StepCostLocality.chartedField_wideFrameCoords c w η₀ 0, TopLevelSites.plaquetteDefect_readAtLevel_eq hper]
    have e : s.wideField w η₀ 0 = s.wideChartAt w η₀ := by
      unfold StepSettings.ChartSetting.wideField
      rw [shiftedCoords_wideCoords_zero]
    rw [e]
    refine curvature_wideChartAt_lt c d hη₀ ?_
    rw [WideCharts.topSite_toTorusSite]
    exact hp
  have hfl := d.hessian (s.wideFrameCoords w η₀ 0) dw hz hdz hsize hcold
  have hfun : (fun τ : ℝ => BlockAverages.blockEnergy R.params.coupling s.regionCells
      (WideCharts.topFrame R n).depth
      (BlockAverages.chartedField (fun x i => s.wideFrameCoords w η₀ 0 x i + τ • dw x i) s.topGaugeField)
      s.topGaugeField) = fun τ : ℝ => s.wideChartEnergy w η₀ (η₀ + τ • v) := by
    funext τ
    unfold StepSettings.ChartSetting.wideChartEnergy
    congr 2
    funext x i
    rw [hw0]
    unfold StepSettings.ChartSetting.wideFrameCoords FreeBondCharts.shiftedCoords
    simp only [hdw]
    split_ifs with hf
    · simp only [Pi.add_apply, Pi.smul_apply, add_sub_cancel_left, FreeBondMoves.toImaginary_smul]
    · simp
  rw [hfun] at hfl
  refine le_trans ?_ hfl
  refine mul_le_mul_of_nonneg_left ?_ hlam.le
  set img : Finset ((WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth × Fin 4) :=
    (Finset.univ : Finset s.free).image fun b => (WideCharts.topSite R n b.1.1, b.1.2) with himg
  have hinj : Set.InjOn (fun b : s.free => ((WideCharts.topSite R n b.1.1, b.1.2) :
      (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth × Fin 4)) (Finset.univ : Finset s.free) := by
    intro b _ b' _ h
    have h' : ((WideCharts.topSite R n b.1.1, b.1.2) :
        (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth × Fin 4) =
        (WideCharts.topSite R n b'.1.1, b'.1.2) := h
    obtain ⟨e1, e2⟩ := Prod.mk.inj h'
    have e3 := congrArg (TorusLumps.toTorusSite (n * R.params.side)) e1
    rw [WideCharts.toTorusSite_topSite, WideCharts.toTorusSite_topSite] at e3
    exact Subtype.ext (Prod.ext e3 e2)
  have hsum : ∑ b, ‖v b‖ ^ 2 = ∑ q ∈ img, ‖dw q.1 q.2‖ ^ 2 := by
    rw [himg, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hb : (TorusLumps.toTorusSite (n * R.params.side) (WideCharts.topSite R n b.1.1), b.1.2) ∈ s.free := by
      rw [WideCharts.toTorusSite_topSite]
      exact b.2
    have hval : dw (WideCharts.topSite R n b.1.1) b.1.2 = ColdStepAtMirrorFrames.toImaginary (v b) := by
      simp only [hdw]
      rw [dif_pos hb]
      congr 2
      exact Subtype.ext (Prod.ext (WideCharts.toTorusSite_topSite R n _) rfl)
    rw [hval]
    have hnorm : ‖(ColdStepAtMirrorFrames.toImaginary (v b) : BlockAverages.imaginaryQuaternions)‖ = ‖v b‖ :=
      WideCharts.norm_toImaginary (v b)
    rw [hnorm]
  rw [hsum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
  intro q hq
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hq
  have hmem := hfree (WideCharts.topSite R n b.1.1) b.1.2 (by
    rw [WideCharts.toTorusSite_topSite]
    exact b.2)
  exact hmem
end YangMills.Construction.WideChartFloor
end
