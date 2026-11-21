import YangMills.Construction.ClusterExpansionOfAStep.BondInCoordinates
import YangMills.Construction.RunningCouplingSlope.LeastActionIsWellAtTheTop
import YangMills.Construction.RunningCouplingSlope.LeastChartEnergyIsAnalyticNearTheFlatField
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepReadsNoBoundProof
import YangMills.Construction.RunningCouplingSlope.WellAcrossFrames
import YangMills.Construction.RunningCouplingSlope.WilsonActionIsWellAtOne
import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenBoundsProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames TorusFields ReferenceDensity BondCoordinates SlopeCoefficient
namespace ChartedEnergyNearTrivial
private def siteFintypeOfPos (F : BlockFrame) (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) (j : ℕ) :
    Fintype (F.Site j) :=
  haveI : ∀ i, NeZero (F.period j i) := fun i => ⟨by
    unfold BlockFrame.period
    exact (Nat.mul_pos (hs i) (pow_pos hL _)).ne'⟩
  inferInstance
private theorem nondegenerate_at_depth (hW : WilsonActionNondegenerate) (hX : NondegenerateAcrossFrames)
    (hT : minimalActionNondegeneratePropagatesStatement) {a : ℝ} (ha : 0 < a) {L : ℕ} (hL : Odd L) :
    ∀ (t n : ℕ), 2 ≤ n → ∀ (inst : Fintype ((torusFrame L t n).Site t)),
      IsNondegenerateAtTrivial (F := torusFrame L t n) (k := t)
        (minimalAction a (finiteCells (torusFrame L t n)) t) := by
  intro t
  induction t with
  | zero =>
    intro n hn inst
    exact hW a L n hL hn
  | succ t ih =>
    intro n hn inst
    have hLpos : 0 < L := hL.pos
    have hnL : 2 ≤ n * L := by nlinarith
    have hext : ∀ i : Fin 4, 0 < (torusFrame L t (n * L)).extent i := fun _ => by
      show 0 < n * L
      omega
    letI instDepth := siteFintypeOfPos (torusFrame L t (n * L)) hLpos hext (torusFrame L t (n * L)).depth
    letI instTop := siteFintypeOfPos (torusFrame L t (n * L)) hLpos hext (torusFrame L t (n * L)).top
    letI instSucc : Fintype ((torusFrame L t (n * L)).Site (t + 1)) := instTop
    have hprev := ih (n * L) hnL instDepth
    have htop := (hT (torusFrame L t (n * L)) a ha hL (fun _ => hnL) hprev).1
    refine hX (torusFrame L (t + 1) n) (torusFrame L t (n * L)) (t + 1) a
      ⟨rfl, hL, fun _ => ?_, hext, ?_, ?_, ?_⟩ htop
    · show 0 < n
      omega
    · simp [BlockFrame.top, torusFrame]
    · simp [BlockFrame.top, torusFrame]
    · intro k hk i
      have e : t + 1 + 1 - k = (t + 1 - k) + 1 := by omega
      simp only [BlockFrame.period, BlockFrame.top, torusFrame, e, pow_succ]
      ring
abbrev _root_.YangMills.SharedProofs.p33643 := @nondegenerate_at_depth
variable {F : BlockFrame}
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
private theorem stepCoordinates_add {S : Finset F.Cell} (ξ ζ : StepVariable S) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (ξ + ζ) x i = stepCoordinates ξ x i + stepCoordinates ζ x i := by
  unfold stepCoordinates
  split_ifs with h
  · exact map_add toImaginaryCLM _ _
  · simp
private theorem isMinimizingChart_of_le_one {a ρ : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (h : IsMinimizingChart a S V ρ w) (h1 : ρ ≤ 1) : IsMinimizingChart a S V 1 w :=
  ⟨h.1, fun b hb => (h.2.1 b hb).trans h1, h.2.2⟩
private theorem isMinimizingChart_minimizingCoordinates {a ρ : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top}
    (h : ∃ w, IsMinimizingChart a S V ρ w) : IsMinimizingChart a S V ρ (minimizingCoordinates a S V ρ) := by apply _root_.YangMills.SharedProofs.p13409 <;> assumption
private theorem isCold_three (S : Finset F.Cell) (j : ℕ) (X : F.GaugeField j) : IsCold S j (24 / 8) X := by apply _root_.YangMills.SharedProofs.p32772 <;> assumption
private theorem minimizingCoordinates_eq (hOL : MinimizingChartUnique) (hs : ∀ i, 2 ≤ F.extent i)
    (hL : Odd F.blockSide) {a ρ : ℝ} (hρ : ρ ≤ 1) {η : StepVariable (finiteCells F)} {V : F.GaugeField F.top}
    (hη : ‖η‖ ≤ ρ)
    (hmin : ∀ W', blockEnergy a (finiteCells F) F.depth (chartedField (stepCoordinates η) V) V ≤
      blockEnergy a (finiteCells F) F.depth W' V)
    (horb : ∀ W', (∀ W'', blockEnergy a (finiteCells F) F.depth W' V ≤ blockEnergy a (finiteCells F) F.depth W'' V) →
      ∃ γ : F.Site F.depth → UnitQuaternion, (∀ z, γ (cellCentre F.depth z) = 1) ∧
        W' = gaugeTransform γ (chartedField (stepCoordinates η) V)) :
    minimizingCoordinates a (finiteCells F) V ρ = stepCoordinates η := by
  have hoff : ∀ b, b ∉ chordBonds (finiteCells F) → stepCoordinates η b.1 b.2 = 0 := fun b hb => by
    unfold stepCoordinates
    exact dif_neg hb
  have hsize : ∀ b ∈ chordBonds (finiteCells F), ‖stepCoordinates η b.1 b.2‖ ≤ ρ := fun b hb => by
    unfold stepCoordinates
    rw [dif_pos hb, norm_toImaginary]
    exact (norm_le_pi_norm η ⟨b, hb⟩).trans hη
  have hchart : IsMinimizingChart a (finiteCells F) V ρ (stepCoordinates η) := ⟨hoff, hsize, hmin⟩
  have hunit := isMinimizingChart_of_le_one hchart hρ
  have hcold : HasColdMinimizer a 1 1 24 (finiteCells F) V := by
    refine ⟨stepCoordinates η, ?_, isCold_three _ _ _, ?_⟩
    · have e : min (1 : ℝ) (1 * 24) = 1 := by norm_num
      rw [e]
      exact hunit
    · intro W' hW'
      obtain ⟨γ, hγ, e⟩ := horb W' hW'
      refine ⟨γ, hγ, fun b _ => ?_⟩
      rw [e]
  exact (hOL F a 1 1 24 V _ hL hs le_rfl hcold hunit).1 _
    (isMinimizingChart_of_le_one (isMinimizingChart_minimizingCoordinates ⟨_, hchart⟩) hρ)
private theorem analyticAt_chartedEnergyAtMinimizer {a ρ : ℝ} {W : F.GaugeField F.top}
    {η₀ : StepVariable (finiteCells F)}
    (hc : minimizingCoordinates a (finiteCells F) W ρ = stepCoordinates η₀)
    (hΦ : AnalyticAt ℝ (fun η : StepVariable (finiteCells F) => chartedEnergy a (stepCoordinates η) W) η₀) :
    AnalyticAt ℝ (chartedEnergyAtMinimizer a ρ W) 0 := by
  have hΨ : chartedEnergyAtMinimizer a ρ W =
      (fun η : StepVariable (finiteCells F) => chartedEnergy a (stepCoordinates η) W) ∘ fun η => η₀ + η := by
    funext η
    unfold chartedEnergyAtMinimizer
    simp only [Function.comp]
    congr 1
    funext x i
    rw [stepCoordinates_add, ← hc]
    simp [coordsAboveFrame, ColdStepAtMirrorFrames.stepFrame, minimizingBondCoordinate]
  rw [hΨ]
  refine AnalyticAt.comp_of_eq hΦ ?_ (add_zero η₀)
  exact analyticAt_const.add analyticAt_id
private theorem eventually_analyticAt [Fintype (F.Site F.top)] (hOL : MinimizingChartUnique) {a ρ : ℝ}
    (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide) (h0 : 0 < ρ) (h1 : ρ ≤ 1)
    (hC : MinimizerNearTrivialInChart a F) :
    ∀ᶠ W in 𝓝 (trivialBlockField F F.top), AnalyticAt ℝ (chartedEnergyAtMinimizer a ρ W) 0 := by
  obtain ⟨x, hxa, hx0, hev⟩ := hC
  set q₁ := quaternionsOfField (trivialBlockField F F.top) with hq₁
  have hsmall : ∀ᶠ Y in 𝓝 q₁, ‖x Y‖ < ρ := by
    have ht : Tendsto (fun Y => ‖x Y‖) (𝓝 q₁) (𝓝 0) := by
      have := hxa.continuousAt.tendsto.norm
      simpa [hx0] using this
    exact ht.eventually (gt_mem_nhds h0)
  have hQ : Tendsto (quaternionsOfField (F := F) (k := F.top)) (𝓝 (trivialBlockField F F.top)) (𝓝 q₁) := by
    have hc : Continuous (quaternionsOfField (F := F) (k := F.top)) :=
      continuous_pi fun y => continuous_pi fun i =>
        continuous_subtype_val.comp ((continuous_apply i).comp (continuous_apply y))
    exact hc.tendsto _
  filter_upwards [hQ.eventually (hev.and hsmall)] with W hW
  obtain ⟨hg, hsm⟩ := hW
  rw [fieldOfQuaternions_quaternionsOfField] at hg
  exact analyticAt_chartedEnergyAtMinimizer
    (minimizingCoordinates_eq hOL hs hL h1 hsm.le hg.1 hg.2.1) hg.2.2.1
end ChartedEnergyNearTrivial
open ChartedEnergyNearTrivial in
theorem chartedEnergyAnalyticNearTrivial_of_nondegenerate (hW : WilsonActionNondegenerate)
    (hX : NondegenerateAcrossFrames) (hT : minimalActionNondegeneratePropagatesStatement)
    (hOL : MinimizingChartUnique) :
    ChartedEnergyAnalyticNearTrivial := by
  intro a ha L hLs t n ρ hn h0 h1
  have hL : Odd L := hLs.1
  have hLpos : 0 < L := hL.pos
  have hn2 : 2 ≤ n := by
    have := hLs.2
    omega
  have hext : ∀ i : Fin 4, 0 < (torusFrame L t n).extent i := fun _ => by
    show 0 < n
    omega
  letI instDepth := siteFintypeOfPos (torusFrame L t n) hLpos hext (torusFrame L t n).depth
  letI instTop := siteFintypeOfPos (torusFrame L t n) hLpos hext (torusFrame L t n).top
  obtain ⟨-, hC⟩ := hT (torusFrame L t n) a ha hL (fun _ => hn2)
    (nondegenerate_at_depth hW hX hT ha hL t n hn2 instDepth)
  have hnear := eventually_analyticAt (F := torusFrame L t n) hOL (fun _ => hn2) hL h0 h1 hC
  have hread : Tendsto (fun V : TorusField n => readAtLevel (torusFrame L t n) (torusFrame L t n).top V)
      (𝓝 (trivialField n)) (𝓝 (trivialBlockField (torusFrame L t n) (torusFrame L t n).top)) := by
    have hc : Continuous (fun V : TorusField n => readAtLevel (torusFrame L t n) (torusFrame L t n).top V) :=
      continuous_pi fun y => continuous_pi fun i => (continuous_apply i).comp (continuous_apply _)
    exact hc.tendsto _
  exact hread.eventually hnear
end YangMills.Construction.RunningCouplingSlope
end
