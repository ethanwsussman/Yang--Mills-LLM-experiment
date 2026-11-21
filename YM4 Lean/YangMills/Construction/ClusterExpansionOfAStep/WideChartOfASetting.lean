import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.ChartOnTheTorus
import YangMills.Construction.ClusterExpansionOfAStep.FrameAgainstTheLeastFieldOfTheCut
import YangMills.Construction.ClusterExpansionOfAStep.GeometryOfFreeBonds
import YangMills.Construction.ClusterExpansionOfAStep.LogarithmOfAMove
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TopLevelSites TorusFields TorusLumps StepSettings StepCosts
  StepMarks TorusCharts FreeBonds RenormalizationStepParameters ColdChain QuaternionLogarithm LumpContours StepFrames
variable {R : StepSetup} {n : ℕ} [NeZero n]
abbrev WideCharts.topFrame (R : StepSetup) (n : ℕ) : BlockFrame := torusFrame R.params.side R.depth n
open WideCharts
instance WideCharts.topFrame_neZero (R : StepSetup) (n : ℕ) [NeZero n] : NeZero (n * (topFrame R n).blockSide) :=
  inferInstanceAs (NeZero (n * R.params.side))
theorem WideCharts.topFrame_extent (R : StepSetup) (n : ℕ) : ∀ i, (topFrame R n).extent i = n := fun _ => rfl
theorem WideCharts.topFrame_period (R : StepSetup) (n : ℕ) [NeZero n] :
    ∀ i, (topFrame R n).period (topFrame R n).depth i = n * R.params.side :=
  period_depth_of_extent (topFrame_extent R n)
abbrev StepSettings.ChartSetting.topGaugeField (s : ChartSetting R n) :
    (topFrame R n).GaugeField (topFrame R n).top :=
  readAtLevel (topFrame R n) (topFrame R n).top s.coarse
abbrev StepSettings.ChartSetting.regionCells (s : ChartSetting R n) : Finset (topFrame R n).Cell :=
  cellsOfSites (topFrame R n) s.region
abbrev WideCharts.topSite (R : StepSetup) (n : ℕ) (x : TorusSite (n * R.params.side)) :
    (topFrame R n).Site (topFrame R n).depth :=
  torusSiteInFrame (topFrame R n) (topFrame R n).depth x
theorem WideCharts.toTorusSite_topSite (R : StepSetup) (n : ℕ) [NeZero n] (y : TorusSite (n * R.params.side)) :
    toTorusSite (n * R.params.side) (topSite R n y) = y :=
  toTorusSite_torusSiteInFrame (topFrame_period R n) y
theorem WideCharts.topSite_toTorusSite (R : StepSetup) (n : ℕ) [NeZero n] (x : (topFrame R n).Site (topFrame R n).depth) :
    topSite R n (toTorusSite (n * R.params.side) x) = x :=
  torusSiteInFrame_toTorusSite (topFrame_period R n) x
structure StepSettings.ChartSetting.ChainContext (s : ChartSetting R n) (δ lam σA cg : ℝ) (N : ℕ → ℝ) : Prop where
  admissible : s.IsAdmissible
  params_admissible : R.params.Admissible
  large_range : R.IsLargeRange
  n₀_le : R.params.n₀ ≤ n
  chain : ColdChainConstants R.params.coupling δ R.params.side lam R.anchorRadius σA cg N
  baseDepth_pos : 0 < R.params.baseDepth
  threshold_le : 2 * R.params.threshold ≤ σA
  anchor_ge : 2 * N 0 * R.params.threshold + 2 * R.ballRadius ≤ R.anchorRadius
  ballRadius_ge : N 0 * (2 * R.params.threshold) * Real.exp (-(δ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤ R.ballRadius
  complement_regular : ComplementOfThickenedLumpsRegular
  frame_near : FrameNearMinimizer
variable {s : ChartSetting R n} {δ lam σA cg : ℝ} {N : ℕ → ℝ}
theorem StepSettings.ChartSetting.ChainContext.rangesAdmissible (c : s.ChainContext δ lam σA cg N) :
    RangesAdmissible R.range R.nextRange := by
  have h1 := c.large_range.range_large
  have h2 := c.large_range.range_le_succ
  have h3 := c.params_admissible.L_ge
  refine ⟨h2, by omega, ?_⟩
  omega
theorem StepSettings.ChartSetting.ChainContext.two_le (c : s.ChainContext δ lam σA cg N) : 2 ≤ n := by
  have := c.params_admissible.n₀_ge
  have := c.n₀_le
  omega
structure StepSettings.ChartSetting.MinimizerData (s : ChartSetting R n) (lam σA : ℝ) (N0 σ' : ℝ)
    (w : (topFrame R n).Site (topFrame R n).depth → Fin 4 → imaginaryQuaternions) : Prop where
  isMinimizing : IsMinimizingChart R.params.coupling s.regionCells s.topGaugeField (min R.anchorRadius (N0 * σ')) w
  cold : IsCold s.regionCells (topFrame R n).depth (σ' / 8) (chartedField w s.topGaugeField)
  hessian : HasCoerciveHessian R.params.coupling lam R.anchorRadius σA s.regionCells s.topGaugeField
  pos : 0 < σ'
  le_two_mul : σ' ≤ 2 * R.params.threshold
  regular : IsOrthantRegular s.regionCells 2047
  frame_near : ∀ b ∈ StepCosts.chartBonds R.params.side n,
    (∃ b₀ ∈ s.free, supDist b₀.1 b.1 ≤ 3 * R.range) →
    ‖((s.frame b : imaginaryQuaternions) : ℍ[ℝ]) - ((w (topSite R n b.1) b.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
      R.ballRadius
theorem StepSettings.ChartSetting.ChainContext.exists_minimizerData (c : s.ChainContext δ lam σA cg N) :
    ∃ σ' w, s.MinimizerData lam σA (N 0) σ' w := by
  obtain ⟨C, σ', hsit, hoff⟩ := ChartSetting.exists_stepSituation c.admissible c.n₀_le
  obtain ⟨hσ0, hσ2, -, hF⟩ := stepSituation_regular_and_cold c.complement_regular c.params_admissible hsit
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
  obtain ⟨w, hw, hwc, hlc⟩ := minimizingCoordinates_eq (F := topFrame R n) hL hs hπ le_rfl H1
  refine ⟨σ', w, hw, hwc, H2, hσ0, hσ2, hreg, fun b hb hnear => ?_⟩
  obtain ⟨b₀, hb₀, hd⟩ := hnear
  have hfr := ((c.frame_near R.params δ lam R.anchorRadius σA cg N c.params_admissible c.chain
    c.threshold_le).2 R.depth R.range R.nextRange n s.coarse s.region C σ' c.rangesAdmissible hsit b hb
    (parentBlock_not_mem_of_near_free c.large_range hoff hb₀ hd)).2
  have hl : minimizerCoord R.params.coupling R.anchorRadius R.params.side R.depth s.region s.coarse b =
      w (topSite R n b.1) b.2 := by
    unfold minimizerCoord minimizingBondCoordinate
    rw [hlc]
  rw [hl] at hfr
  refine hfr.trans ?_
  have hN0 := hN 0
  have he : 0 < Real.exp (-(δ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) := Real.exp_pos _
  have h3 : N 0 * σ' * Real.exp (-(δ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) ≤
      N 0 * (2 * R.params.threshold) * Real.exp (-(δ * ((R.range / 2 ^ 11 : ℕ) : ℝ))) := by gcongr
  exact h3.trans c.ballRadius_ge
def WideCharts.minimizerOnTorus (R : StepSetup) (n : ℕ)
    (w : (topFrame R n).Site (topFrame R n).depth → Fin 4 → imaginaryQuaternions)
    (b : TorusBond (n * R.params.side)) : imaginaryQuaternions :=
  w (topSite R n b.1) b.2
open Classical in
def StepSettings.ChartSetting.wideCoords (s : ChartSetting R n)
    (w : (topFrame R n).Site (topFrame R n).depth → Fin 4 → imaginaryQuaternions)
    (η : FreeCoords s.free) (b : TorusBond (n * R.params.side)) : imaginaryQuaternions :=
  if topSite R n b.1 ∈ sitesOfCells s.regionCells (topFrame R n).depth ∧
      (topSite R n b.1, b.2) ∈ chordBonds s.regionCells ∧ s.IsNearFree b
  then s.coordinates η b else minimizerOnTorus R n w b
theorem WideCharts.isBlockTreeBond_iff_top (c : s.ChainContext δ lam σA cg N) (x : TorusSite (n * R.params.side))
    (i : Fin 4) : IsBlockTreeBond R.params.side x i ↔ IsAxialTreeBond (topSite R n x, i) :=
  (isAxialTreeBond_torusSiteInFrame_iff (F := topFrame R n) (topFrame_extent R n) c.params_admissible.L_odd
    c.two_le x i).symm
theorem WideCharts.isBlockTreeBond_iff_step (c : s.ChainContext δ lam σA cg N) (x : TorusSite (n * R.params.side))
    (i : Fin 4) :
    haveI : NeZero (n * (stepBlockFrame R.params.side n).blockSide) := inferInstanceAs (NeZero (n * R.params.side))
    IsBlockTreeBond R.params.side x i ↔
      IsAxialTreeBond (F := stepBlockFrame R.params.side n) (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i) := by
  have : NeZero (n * (stepBlockFrame R.params.side n).blockSide) := inferInstanceAs (NeZero (n * R.params.side))
  exact (isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame R.params.side n) (fun _ => rfl)
    c.params_admissible.L_odd c.two_le x i).symm
theorem WideCharts.mem_chartBonds_iff (c : s.ChainContext δ lam σA cg N) (b : TorusBond (n * R.params.side)) :
    b ∈ StepCosts.chartBonds R.params.side n ↔ ¬ IsBlockTreeBond R.params.side b.1 b.2 := by
  classical
  unfold StepCosts.chartBonds
  rw [Finset.mem_filter, isBlockTreeBond_iff_step c]
  simp
theorem WideCharts.mem_chordBonds_of_isNearFree (c : s.ChainContext δ lam σA cg N) {b : TorusBond (n * R.params.side)}
    (hb : s.IsNearFree b) (hnt : ¬ IsBlockTreeBond R.params.side b.1 b.2) :
    topSite R n b.1 ∈ sitesOfCells s.regionCells (topFrame R n).depth ∧
      (topSite R n b.1, b.2) ∈ chordBonds s.regionCells := by
  obtain ⟨b₀, hb₀, hd⟩ := hb
  have hbig := c.large_range.range_large
  have h1 : parentBlock R.params.side b.1 ∈ s.region :=
    parentBlock_mem_region_of_near_free c.admissible c.large_range hb₀ (by omega)
  have h3 : parentBlock R.params.side (b.1 + TorusFields.unitStep (n * R.params.side) b.2) ∈ s.region := by
    refine parentBlock_mem_region_of_near_free c.admissible c.large_range hb₀ ?_
    have e1 := supDist_add_unitStep_le b.1 b.2
    have e2 := supDist_triangle b₀.1 b.1 (b.1 + TorusFields.unitStep (n * R.params.side) b.2)
    omega
  have hnt' : ¬ IsAxialTreeBond (topSite R n b.1, b.2) := fun h => hnt ((isBlockTreeBond_iff_top c _ _).mpr h)
  exact ⟨torusSiteInFrame_mem_sitesOfCells (topFrame_extent R n) c.params_admissible.L_odd c.two_le _ h1,
    mem_chordBonds_of_parentBlock (topFrame_extent R n) c.params_admissible.L_odd c.two_le _ _ hnt' h1 h3⟩
theorem WideCharts.norm_toImaginary (v : ImaginaryCoord) :
    ‖((toImaginary v : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖v‖ := by apply _root_.YangMills.Construction.BlockTrees.norm_toImaginary <;> assumption
theorem WideCharts.wideCoords_close (c : s.ChainContext δ lam σA cg N) {σ' : ℝ}
    {w : (topFrame R n).Site (topFrame R n).depth → Fin 4 → imaginaryQuaternions}
    (d : s.MinimizerData lam σA (N 0) σ' w) {η : FreeCoords s.free} (hη : s.InBalls η)
    (b : TorusBond (n * R.params.side)) :
    ‖((s.wideCoords w η b : imaginaryQuaternions) : ℍ[ℝ]) -
      ((minimizerOnTorus R n w b : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 2 * R.ballRadius := by
  classical
  have hρ : 0 ≤ R.ballRadius := by
    have := c.params_admissible.σ_pos
    unfold StepSetup.ballRadius
    positivity
  unfold ChartSetting.wideCoords
  split_ifs with h
  · obtain ⟨-, hc, hnear⟩ := h
    have hnt : ¬ IsBlockTreeBond R.params.side b.1 b.2 := fun ht =>
      (Finset.mem_filter.mp hc).2 ((isBlockTreeBond_iff_top c _ _).mp ht)
    have hcb : b ∈ StepCosts.chartBonds R.params.side n := (mem_chartBonds_iff c b).mpr hnt
    obtain ⟨b₀, hb₀, hd⟩ := hnear
    have hbig := c.large_range.range_large
    have hd3 : supDist b₀.1 b.1 ≤ 3 * R.range := by omega
    have hfr := d.frame_near b hcb ⟨b₀, hb₀, hd3⟩
    by_cases hf : b ∈ s.free
    · have hv : s.coordinates η b = s.frame b + toImaginary (η ⟨b, hf⟩) := by
        unfold ChartSetting.coordinates
        rw [dif_pos hf]
      rw [hv]
      have h1 : ‖((toImaginary (η ⟨b, hf⟩) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ R.ballRadius := hη ⟨b, hf⟩
      have e : (((s.frame b + toImaginary (η ⟨b, hf⟩) : imaginaryQuaternions)) : ℍ[ℝ]) -
            ((minimizerOnTorus R n w b : imaginaryQuaternions) : ℍ[ℝ]) =
          (((s.frame b : imaginaryQuaternions) : ℍ[ℝ]) -
              ((minimizerOnTorus R n w b : imaginaryQuaternions) : ℍ[ℝ])) +
            ((toImaginary (η ⟨b, hf⟩) : imaginaryQuaternions) : ℍ[ℝ]) := by
        push_cast
        abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have : ‖((s.frame b : imaginaryQuaternions) : ℍ[ℝ]) -
          ((minimizerOnTorus R n w b : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ R.ballRadius := hfr
      linarith
    · have hv : s.coordinates η b = chartCoord R.params s.coarse s.fine b := by
        unfold ChartSetting.coordinates
        rw [dif_neg hf]
      rw [hv]
      have hg := c.admissible.near_frame b₀ hb₀ b hcb hf hd3
      have e : ((chartCoord R.params s.coarse s.fine b : imaginaryQuaternions) : ℍ[ℝ]) -
            ((minimizerOnTorus R n w b : imaginaryQuaternions) : ℍ[ℝ]) =
          (((chartCoord R.params s.coarse s.fine b : imaginaryQuaternions) : ℍ[ℝ]) -
              ((s.frame b : imaginaryQuaternions) : ℍ[ℝ])) +
            (((s.frame b : imaginaryQuaternions) : ℍ[ℝ]) -
              ((minimizerOnTorus R n w b : imaginaryQuaternions) : ℍ[ℝ])) := by abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have : ‖((s.frame b : imaginaryQuaternions) : ℍ[ℝ]) -
          ((minimizerOnTorus R n w b : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ R.ballRadius := hfr
      linarith
  · rw [sub_self, norm_zero]
    linarith
theorem WideCharts.torusChart_wideCoords (c : s.ChainContext δ lam σA cg N)
    (w : (topFrame R n).Site (topFrame R n).depth → Fin 4 → imaginaryQuaternions)
    (η : FreeCoords s.free) {x : TorusSite (n * R.params.side)} {i : Fin 4} (hb : s.IsNearFree (x, i)) :
    torusChart R.params.side (s.wideCoords w η) s.coarse x i = torusChart R.params.side (s.coordinates η) s.coarse x i := by
  classical
  by_cases ht : IsBlockTreeBond R.params.side x i
  · have hc : ¬ IsBlockEndBond R.params.side x i := fun h => ht.1 h
    unfold torusChart
    rw [if_neg hc, if_neg hc, if_pos ht, if_pos ht]
  · refine torusChart_congr s.coarse ?_
    obtain ⟨h1, h2⟩ := mem_chordBonds_of_isNearFree c hb ht
    unfold ChartSetting.wideCoords
    rw [if_pos ⟨h1, h2, hb⟩]
end YangMills.Construction
end
