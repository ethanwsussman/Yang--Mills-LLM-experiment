import YangMills.Construction.ClusterExpansionOfAStep.CostAndWideEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.ClusterExpansionOfAStep
section Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem fderiv_const_add_add_eq {f g : E → ℝ} {x : E} (K : ℝ) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun a => K + (f a + g a)) x = fderiv ℝ f x + fderiv ℝ g x :=
  ((hf.hasFDerivAt.add hg.hasFDerivAt).const_add K).fderiv
theorem second_fderiv_const_add_add {f g : E → ℝ} {x : E} (K : ℝ) (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ fun a => K + (f a + g a)) x = fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
  have he : (fderiv ℝ fun a => K + (f a + g a)) =ᶠ[𝓝 x] fun a => fderiv ℝ f a + fderiv ℝ g a := by
    filter_upwards [LineCalculus.eventually_differentiableAt_of_contDiffAt_two hf,
      LineCalculus.eventually_differentiableAt_of_contDiffAt_two hg] with a h1 h2
    exact fderiv_const_add_add_eq K h1 h2
  rw [he.fderiv_eq]
  exact ((LineCalculus.hasFDerivAt_fderiv_of_contDiffAt_two hf).add
    (LineCalculus.hasFDerivAt_fderiv_of_contDiffAt_two hg)).fderiv
theorem second_fderiv_apply_of_eventuallyEq_sum {u : E → ℝ} {f g : F → ℝ} {l : E → F} {p : E} {o : F} {K : ℝ}
    (hu : u =ᶠ[𝓝 p] (fun a => K + (f a + g a)) ∘ l) (hl0 : l p = o) (hf : ContDiffAt ℝ 2 f o)
    (hg : ContDiffAt ℝ 2 g o) (hl : ContDiffAt ℝ 2 l p) (v w : E) :
    fderiv ℝ (fderiv ℝ u) p v w =
      fderiv ℝ (fderiv ℝ f) o (fderiv ℝ l p v) (fderiv ℝ l p w) +
      fderiv ℝ (fderiv ℝ g) o (fderiv ℝ l p v) (fderiv ℝ l p w) +
      (fderiv ℝ f o (fderiv ℝ (fderiv ℝ l) p v w) + fderiv ℝ g o (fderiv ℝ (fderiv ℝ l) p v w)) := by
  have hs : ContDiffAt ℝ 2 (fun a => K + (f a + g a)) (l p) := by
    rw [hl0]
    exact contDiffAt_const.add (hf.add hg)
  rw [LineCalculus.second_fderiv_of_eventuallyEq_comp hu hs hl v w, hl0, second_fderiv_const_add_add K hf hg,
    fderiv_const_add_add_eq K (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))]
  simp
theorem fderiv_apply_of_eventuallyEq_sum {u : E → ℝ} {f g : F → ℝ} {l : E → F} {p : E} {o : F} {K : ℝ}
    (hu : u =ᶠ[𝓝 p] (fun a => K + (f a + g a)) ∘ l) (hl0 : l p = o) (hf : DifferentiableAt ℝ f o)
    (hg : DifferentiableAt ℝ g o) (hl : DifferentiableAt ℝ l p) (v : E) :
    fderiv ℝ u p v = fderiv ℝ f o (fderiv ℝ l p v) + fderiv ℝ g o (fderiv ℝ l p v) := by
  have hs : DifferentiableAt ℝ (fun a => K + (f a + g a)) (l p) := by
    rw [hl0]
    exact (differentiableAt_const K).add (hf.add hg)
  rw [LineCalculus.fderiv_of_eventuallyEq_comp hu hs hl, hl0, fderiv_const_add_add_eq K hf hg]
  simp
end Calculus
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n] {s : StepSettings.ChartSetting R n}
  {δ lam σA cg : ℝ} {N : ℕ → ℝ}
theorem not_isBlockTreeBond_of_mem_free (c : s.ChainContext δ lam σA cg N) :
    ∀ b ∈ s.free, ¬ TorusCharts.IsBlockTreeBond R.params.side b.1 b.2 := fun b hb =>
  (WideCharts.mem_chartBonds_iff c b).mp (c.admissible.subset_chart hb)
omit [NeZero n] in
theorem coordinates_eq_shiftedCoords (s : StepSettings.ChartSetting R n) (η₀ η : StepSettings.FreeCoords s.free) :
    s.coordinates η = FreeBondCharts.shiftedCoords s.free (s.coordinates η₀) fun b => η b - η₀ b := by
  classical
  funext b
  unfold StepSettings.ChartSetting.coordinates FreeBondCharts.shiftedCoords
  by_cases hb : b ∈ s.free
  · simp only [dif_pos hb]
    have h : ColdStepAtMirrorFrames.toImaginary (η ⟨b, hb⟩) =
        ColdStepAtMirrorFrames.toImaginary (η₀ ⟨b, hb⟩) +
          ColdStepAtMirrorFrames.toImaginary (η ⟨b, hb⟩ - η₀ ⟨b, hb⟩) := by
      rw [← FreeBondMoves.toImaginary_add, add_sub_cancel]
    rw [h, add_assoc]
  · simp only [dif_neg hb]
theorem isNearFree_of_mem_free {b : TorusFields.TorusBond (n * R.params.side)} (hb : b ∈ s.free) :
    s.IsNearFree b :=
  ⟨b, hb, by rw [TorusFields.supDist_self]; exact Nat.zero_le _⟩
theorem wideCoords_eq_coordinates_of_mem_free (c : s.ChainContext δ lam σA cg N)
    (w : (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth → Fin 4 → BlockAverages.imaginaryQuaternions)
    (η₀ : StepSettings.FreeCoords s.free) {b : TorusFields.TorusBond (n * R.params.side)} (hb : b ∈ s.free) :
    s.wideCoords w η₀ b = s.coordinates η₀ b := by
  classical
  obtain ⟨h1, h2⟩ := WideCharts.mem_chordBonds_of_isNearFree c (isNearFree_of_mem_free hb)
    (not_isBlockTreeBond_of_mem_free c b hb)
  unfold StepSettings.ChartSetting.wideCoords
  rw [if_pos ⟨h1, h2, isNearFree_of_mem_free hb⟩]
theorem leftMoveCoords_wideCoords (c : s.ChainContext δ lam σA cg N)
    (w : (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth → Fin 4 → BlockAverages.imaginaryQuaternions)
    (η₀ : StepSettings.FreeCoords s.free) :
    FreeBondCharts.leftMoveCoords s.free (s.wideCoords w η₀) η₀ =
      FreeBondCharts.leftMoveCoords s.free (s.coordinates η₀) η₀ := by
  funext η b
  unfold FreeBondCharts.leftMoveCoords
  rw [wideCoords_eq_coordinates_of_mem_free c w η₀ b.2]
abbrev _root_.YangMills.Construction.StepSettings.ChartSetting.chartedFieldAt (s : StepSettings.ChartSetting R n)
    (η₀ : StepSettings.FreeCoords s.free) : TorusFields.TorusField (n * R.params.side) :=
  TorusCharts.torusChart R.params.side (s.coordinates η₀) s.coarse
abbrev _root_.YangMills.Construction.StepSettings.ChartSetting.wideChartAt (s : StepSettings.ChartSetting R n)
    (w : (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth → Fin 4 → BlockAverages.imaginaryQuaternions)
    (η₀ : StepSettings.FreeCoords s.free) : TorusFields.TorusField (n * R.params.side) :=
  TorusCharts.torusChart R.params.side (s.wideCoords w η₀) s.coarse
abbrev _root_.YangMills.Construction.StepSettings.ChartSetting.regionActionMoves (s : StepSettings.ChartSetting R n)
    (η₀ : StepSettings.FreeCoords s.free) : StepSettings.FreeCoords s.free → ℝ :=
  FreeBondMoves.alongMoves s.free
    (TorusFields.actionAtLevel R.params.coupling R.params.side R.depth s.coolRegion) (s.chartedFieldAt η₀)
abbrev _root_.YangMills.Construction.StepSettings.ChartSetting.coreActionMoves (s : StepSettings.ChartSetting R n)
    (w : (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth → Fin 4 → BlockAverages.imaginaryQuaternions)
    (η₀ : StepSettings.FreeCoords s.free) : StepSettings.FreeCoords s.free → ℝ :=
  FreeBondMoves.alongMoves s.free
    (TorusFields.actionAtLevel R.params.coupling R.params.side R.depth s.sitesUnderRegion) (s.wideChartAt w η₀)
abbrev _root_.YangMills.Construction.StepSettings.ChartSetting.nearFitMoves (s : StepSettings.ChartSetting R n)
    (η₀ : StepSettings.FreeCoords s.free) : StepSettings.FreeCoords s.free → ℝ :=
  FreeBondMoves.alongMoves s.free s.nearFitSum (s.chartedFieldAt η₀)
def _root_.YangMills.Construction.StepSettings.ChartSetting.wideChartEnergy (s : StepSettings.ChartSetting R n)
    (w : (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth → Fin 4 → BlockAverages.imaginaryQuaternions)
    (η₀ η : StepSettings.FreeCoords s.free) : ℝ :=
  BlockAverages.blockEnergy R.params.coupling s.regionCells (WideCharts.topFrame R n).depth
    (BlockAverages.chartedField (s.wideFrameCoords w η₀ fun b => η b - η₀ b) s.topGaugeField) s.topGaugeField
theorem costSum_eventuallyEq_moves (hS : StepCosts.SharesSumToAction) (c : s.ChainContext δ lam σA cg N)
    {η₀ : StepSettings.FreeCoords s.free} (hη₀ : s.InBalls η₀) :
    ∃ K : ℝ, s.costSum =ᶠ[𝓝 η₀] (fun a => K + (s.regionActionMoves η₀ a + s.nearFitMoves η₀ a)) ∘
      FreeBondCharts.leftMoveCoords s.free (s.coordinates η₀) η₀ := by
  obtain ⟨K, hK⟩ := StepCostLocality.costSum_eventuallyEq_near hS c hη₀
  refine ⟨K, ?_⟩
  filter_upwards [hK, FreeBondCharts.torusChart_shiftedCoords_eventually s.free (not_isBlockTreeBond_of_mem_free c)
    (s.coordinates η₀) s.coarse η₀] with η h1 h2
  rw [h1, coordinates_eq_shiftedCoords s η₀ η, h2]
  simp only [Function.comp, StepSettings.ChartSetting.regionActionMoves, StepSettings.ChartSetting.nearFitMoves,
    FreeBondMoves.alongMoves]
omit [NeZero n] in
theorem leftMovesAt_congr_apply {W W' : TorusFields.TorusField (n * R.params.side)}
    (a : StepSettings.FreeCoords s.free) {x : TorusFields.TorusSite (n * R.params.side)} {i : Fin 4}
    (h : W x i = W' x i) : FreeBondMoves.leftMovesAt s.free a W x i = FreeBondMoves.leftMovesAt s.free a W' x i := by
  rw [FreeBondMoves.leftMovesAt_eq, FreeBondMoves.leftMovesAt_eq, h]
theorem nearFitSum_leftMovesAt_wideChartAt (c : s.ChainContext δ lam σA cg N)
    (w : (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth → Fin 4 → BlockAverages.imaginaryQuaternions)
    (η₀ a : StepSettings.FreeCoords s.free) :
    s.nearFitSum (FreeBondMoves.leftMovesAt s.free a (s.wideChartAt w η₀)) =
      s.nearFitSum (FreeBondMoves.leftMovesAt s.free a (s.chartedFieldAt η₀)) := by
  have h : ∑ d ∈ s.nearBonds, PlainAlignment.plainAlignmentDefect R.params.side d.1 d.2 (s.coarse d.1 d.2)
        (FreeBondMoves.leftMovesAt s.free a (s.wideChartAt w η₀)) =
      ∑ d ∈ s.nearBonds, PlainAlignment.plainAlignmentDefect R.params.side d.1 d.2 (s.coarse d.1 d.2)
        (FreeBondMoves.leftMovesAt s.free a (s.chartedFieldAt η₀)) :=
    Finset.sum_congr rfl fun d hd =>
      NearFits.plainAlignmentDefect_congr_near c hd _ fun x i hn =>
        leftMovesAt_congr_apply a (WideCharts.torusChart_wideCoords c w η₀ hn)
  unfold StepSettings.ChartSetting.nearFitSum
  rw [h]
theorem wideChartEnergy_eventuallyEq_moves (hC : LumpContours.WholeCellCostEqualsMinimalAction)
    (hA : LumpContours.ActionAtLevelIsCutAction) (c : s.ChainContext δ lam σA cg N)
    (w : (WideCharts.topFrame R n).Site (WideCharts.topFrame R n).depth → Fin 4 → BlockAverages.imaginaryQuaternions)
    (η₀ : StepSettings.FreeCoords s.free) :
    ∃ K : ℝ, s.wideChartEnergy w η₀ =ᶠ[𝓝 η₀] (fun a => K + (s.coreActionMoves w η₀ a + s.nearFitMoves η₀ a)) ∘
      FreeBondCharts.leftMoveCoords s.free (s.coordinates η₀) η₀ := by
  obtain ⟨K, hK⟩ := StepCostLocality.blockEnergy_wideField hC hA c w η₀
  refine ⟨K, ?_⟩
  filter_upwards [FreeBondCharts.torusChart_shiftedCoords_eventually s.free (not_isBlockTreeBond_of_mem_free c)
    (s.wideCoords w η₀) s.coarse η₀] with η h2
  unfold StepSettings.ChartSetting.wideChartEnergy
  rw [hK]
  have h3 : s.wideField w η₀ (fun b => η b - η₀ b) =
      FreeBondMoves.leftMovesAt s.free (FreeBondCharts.leftMoveCoords s.free (s.coordinates η₀) η₀ η)
        (s.wideChartAt w η₀) := by
    unfold StepSettings.ChartSetting.wideField
    rw [h2, leftMoveCoords_wideCoords c w η₀]
  rw [h3]
  simp only [Function.comp, StepSettings.ChartSetting.coreActionMoves, StepSettings.ChartSetting.nearFitMoves,
    FreeBondMoves.alongMoves]
  rw [nearFitSum_leftMovesAt_wideChartAt c w η₀]
end YangMills.Construction.ClusterExpansionOfAStep
end
