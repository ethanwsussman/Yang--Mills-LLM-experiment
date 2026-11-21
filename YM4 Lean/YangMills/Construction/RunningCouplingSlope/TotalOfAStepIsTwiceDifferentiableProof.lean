import YangMills.Construction.ColdStepAtMirrorFrames.HaarExcessNearZero
import YangMills.Construction.RunningCouplingSlope.LeastFieldNearTheFlatFieldProof
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepIsTwiceDifferentiable
import YangMills.Construction.SummableBoundsOfTheFlow.TwoLevelsOnOneTorus
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames TorusFields SlopeCoefficient ReferenceDensity
namespace StepGaugeTotalSmooth
section Calculus
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem contDiffAt_fderiv_fderiv_apply {Φ : P → E → ℝ} {p₀ : P} {η₀ : E}
    (h : ContDiffAt ℝ 4 (fun q : P × E => Φ q.1 q.2) (p₀, η₀)) (u v : E) :
    ContDiffAt ℝ 2 (fun p => fderiv ℝ (fun ζ => fderiv ℝ (Φ p) ζ u) η₀ v) p₀ := by
  have hf : ContDiffAt ℝ 4 (Function.uncurry fun q : P × E => Φ q.1) ((p₀, η₀), η₀) := by
    have hg : ContDiffAt ℝ 4 (fun r : (P × E) × E => (r.1.1, r.2)) ((p₀, η₀), η₀) :=
      (contDiff_fst.comp contDiff_fst).contDiffAt.prodMk contDiffAt_snd
    exact ContDiffAt.comp (g := fun q : P × E => Φ q.1 q.2) ((p₀, η₀), η₀) h hg
  have h1 : ContDiffAt ℝ 3 (fun q : P × E => fderiv ℝ (Φ q.1) q.2) (p₀, η₀) :=
    ContDiffAt.fderiv (f := fun q : P × E => Φ q.1) (g := Prod.snd) hf contDiffAt_snd (by norm_num)
  have h2 : ContDiffAt ℝ 3 (Function.uncurry fun (p : P) (ζ : E) => fderiv ℝ (Φ p) ζ u) (p₀, η₀) :=
    h1.clm_apply contDiffAt_const
  have h3 : ContDiffAt ℝ 2 (fun p => fderiv ℝ (fun ζ => fderiv ℝ (Φ p) ζ u) η₀) p₀ :=
    ContDiffAt.fderiv (f := fun (p : P) (ζ : E) => fderiv ℝ (Φ p) ζ u) (g := fun _ => η₀) h2
      contDiffAt_const (by norm_num)
  exact h3.clm_apply contDiffAt_const
abbrev _root_.YangMills.SharedProofs.p66887 := @contDiffAt_fderiv_fderiv_apply
private theorem contDiffAt_det_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] {M : P → Matrix ι ι ℝ} {p₀ : P}
    (h : ∀ i j, ContDiffAt ℝ 2 (fun p => M p i j) p₀) : ContDiffAt ℝ 2 (fun p => (M p).det) p₀ := by
  simp only [Matrix.det_apply']
  refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul ?_
  exact contDiffAt_prod fun i _ => h _ _
end Calculus
section Levels
private def siteFintype (F : BlockFrame) (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) (j : ℕ) :
    Fintype (F.Site j) :=
  haveI : ∀ i, NeZero (F.period j i) := fun i => ⟨by
    unfold BlockFrame.period
    exact (Nat.mul_pos (hs i) (pow_pos hL _)).ne'⟩
  inferInstance
private theorem minimalAction_nondegenerate_torusFrame (hW : WilsonActionNondegenerate)
    (hX : NondegenerateAcrossFrames) (hT : minimalActionNondegeneratePropagatesStatement) {a : ℝ} (ha : 0 < a)
    {L : ℕ} (hL : Odd L) :
    ∀ (t n : ℕ), 2 ≤ n → ∀ (inst : Fintype ((torusFrame L t n).Site t)),
      IsNondegenerateAtTrivial (F := torusFrame L t n) (k := t)
        (minimalAction a (finiteCells (torusFrame L t n)) t) := by apply _root_.YangMills.SharedProofs.p33643 <;> assumption
end Levels
section Frames
variable {F : BlockFrame}
private theorem mem_chordBonds_iff (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide) (b : F.Site F.depth × Fin 4) :
    b ∈ chordBonds (finiteCells F) ↔ ¬ IsAxialTreeBond b := by apply _root_.YangMills.SharedProofs.p21924 <;> assumption
private theorem stepCoordinates_zero (S : Finset F.Cell) : stepCoordinates (0 : StepVariable S) =
    fun (_ : F.Site F.depth) (_ : Fin 4) => (0 : imaginaryQuaternions) := by apply _root_.YangMills.SharedProofs.p23017 <;> assumption
private theorem coordsAboveFrame_eq (a ρ : ℝ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F))
    (x : F.Site F.depth) (i : Fin 4) :
    coordsAboveFrame true a ρ 0 V η x i =
      minimizingBondCoordinate a ρ (finiteCells F) (x, i) V + stepCoordinates η x i := by
  simp [coordsAboveFrame, ColdStepAtMirrorFrames.stepFrame]
private theorem rotatedField_bondSpread_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X' : Fin k → imaginaryQuaternions) (W : F.GaugeField F.top) :
    rotatedField (BlockAverages.bondSpread c X' 0) W = W := by apply _root_.YangMills.Construction.BlockAverages.AgreeingPairs.rotatedField_zero <;> assumption
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
private theorem analyticAt_expUnit {w : X → imaginaryQuaternions} {e : X}
    (h : AnalyticAt ℝ (fun y => (w y : ℍ[ℝ])) e) :
    AnalyticAt ℝ (fun y => ((expUnit (w y) : UnitQuaternion) : ℍ[ℝ])) e :=
  AnalyticAt.comp (g := NormedSpace.exp) (f := fun y => (w y : ℍ[ℝ])) (NormedSpace.exp_analytic (𝕂 := ℝ) _) h
private theorem analyticAt_coe_imag {w : X → imaginaryQuaternions} {e : X} (h : AnalyticAt ℝ w e) :
    AnalyticAt ℝ (fun y => (w y : ℍ[ℝ])) e :=
  (imaginaryQuaternions.subtypeL.analyticAt _).comp h
private theorem analyticAt_stepCoordinates {S : Finset F.Cell} {η : X → StepVariable S} {e : X}
    (h : AnalyticAt ℝ η e) (x : F.Site F.depth) (i : Fin 4) :
    AnalyticAt ℝ (fun y => stepCoordinates (η y) x i) e := by apply _root_.YangMills.SharedProofs.p31047 <;> assumption
private theorem isAnalytic_chartedField (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    {w : X → F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : X → F.GaugeField F.top} {e : X}
    (hw : ∀ b ∈ chordBonds (finiteCells F), AnalyticAt ℝ (fun y => (w y b.1 b.2 : ℍ[ℝ])) e)
    (hV : IsAnalyticFieldFamily V e) : IsAnalyticFieldFamily (fun y => chartedField (w y) (V y)) e := by
  intro x i
  by_cases h2 : IsAxialTreeBond (x, i)
  · have h1 : ¬ IsCrossingBond (x, i) := h2.1
    simp only [chartedField, h1, h2, if_true, if_false]
    simpa using analyticAt_const
  · have hb := (mem_chordBonds_iff hs hL (x, i)).2 h2
    by_cases h1 : IsCrossingBond (x, i)
    · simp only [chartedField, h1, if_true]
      exact (analyticAt_expUnit (hw _ hb)).mul (hV _ _)
    · simp only [chartedField, h1, h2, if_false]
      exact analyticAt_expUnit (hw _ hb)
abbrev _root_.YangMills.SharedProofs.p1968 := @isAnalytic_chartedField
private theorem isAnalytic_rotatedField {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X' : Fin k → imaginaryQuaternions) (W : F.GaugeField F.top) :
    IsAnalyticFieldFamily (fun σ : Fin k → ℝ => rotatedField (BlockAverages.bondSpread c X' σ) W) 0 := by apply _root_.YangMills.SharedProofs.p60243 <;> assumption
private theorem analyticAt_blockEnergy [Fintype (F.Site F.depth)] {a : ℝ} (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth))
    {φ : X → F.GaugeField F.depth} {φ' : X → F.GaugeField F.top} {e : X} (h : IsAnalyticFieldFamily φ e)
    (h' : IsAnalyticFieldFamily φ' e) (h0 : φ e = trivialBlockField F F.depth) :
    AnalyticAt ℝ (fun y => blockEnergy a (finiteCells F) F.depth (φ y) (φ' y)) e := by apply _root_.YangMills.SharedProofs.p73682 <;> assumption
private theorem isAnalytic_fieldAboveFrame (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide) {a ρ : ℝ}
    {V : X → F.GaugeField F.top} {e : X}
    (hw : ∀ b ∈ chordBonds (finiteCells F),
      AnalyticAt ℝ (fun y => minimizingBondCoordinate a ρ (finiteCells F) b (V y)) e)
    (hV : IsAnalyticFieldFamily V e) {η : X → StepVariable (finiteCells F)} (hη : AnalyticAt ℝ η e) :
    IsAnalyticFieldFamily (fun y => fieldAboveFrame true a ρ 0 (V y) (η y)) e := by
  refine isAnalytic_chartedField (w := fun y => coordsAboveFrame true a ρ 0 (V y) (η y)) hs hL (fun b hb => ?_) hV
  simp only [coordsAboveFrame_eq]
  exact analyticAt_coe_imag ((hw b hb).add (analyticAt_stepCoordinates hη b.1 b.2))
private theorem analyticAt_chartedEnergy [Fintype (F.Site F.depth)] (hs : ∀ i, 2 ≤ F.extent i)
    (hL : Odd F.blockSide) {a ρ : ℝ}
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth))
    {V : X → F.GaugeField F.top} {e : X}
    (hw : ∀ b ∈ chordBonds (finiteCells F),
      AnalyticAt ℝ (fun y => minimizingBondCoordinate a ρ (finiteCells F) b (V y)) e)
    (hV : IsAnalyticFieldFamily V e) (h1 : fieldAboveFrame true a ρ 0 (V e) 0 = trivialBlockField F F.depth) :
    AnalyticAt ℝ (fun q : X × StepVariable (finiteCells F) => chartedEnergyAtMinimizer a ρ (V q.1) q.2) (e, 0) := by
  have hwq : ∀ b ∈ chordBonds (finiteCells F), AnalyticAt ℝ
      (fun q : X × StepVariable (finiteCells F) => minimizingBondCoordinate a ρ (finiteCells F) b (V q.1)) (e, 0) :=
    fun b hb =>
      AnalyticAt.comp (g := fun y => minimizingBondCoordinate a ρ (finiteCells F) b (V y))
        (f := fun q : X × StepVariable (finiteCells F) => q.1) (hw b hb) analyticAt_fst
  have hVq : IsAnalyticFieldFamily (fun q : X × StepVariable (finiteCells F) => V q.1) (e, 0) := fun x i =>
    AnalyticAt.comp (g := fun y => ((V y x i : UnitQuaternion) : ℍ[ℝ]))
      (f := fun q : X × StepVariable (finiteCells F) => q.1) (hV x i) analyticAt_fst
  have hZ := isAnalytic_fieldAboveFrame hs hL hwq hVq (η := fun q => q.2) analyticAt_snd
  exact analyticAt_blockEnergy hL hA hZ hVq h1
private theorem contDiffAt_stepLogAmplitude [Fintype (F.Site F.depth)] (hs : ∀ i, 2 ≤ F.extent i)
    (hL : Odd F.blockSide) {a ρ : ℝ} (hH : HaarLogRatioNearZero)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth))
    {V : X → F.GaugeField F.top} {e : X}
    (hw : ∀ b ∈ chordBonds (finiteCells F),
      AnalyticAt ℝ (fun y => minimizingBondCoordinate a ρ (finiteCells F) b (V y)) e)
    (hV : IsAnalyticFieldFamily V e) (h1 : fieldAboveFrame true a ρ 0 (V e) 0 = trivialBlockField F F.depth)
    (hdet : (chartedHessian a ρ (V e) 0).det ≠ 0)
    (hsmall : ∀ b ∈ chordBonds (finiteCells F), ‖minimizingBondCoordinate a ρ (finiteCells F) b (V e)‖ ≤ 1) :
    ContDiffAt ℝ 2 (fun y => stepLogAmplitude (F := F) a ρ (V y)) e := by
  obtain ⟨C, -, hC⟩ := hH
  have hE := analyticAt_chartedEnergy hs hL hA hw hV h1
  have hE4 : ContDiffAt ℝ 4
      (fun q : X × StepVariable (finiteCells F) => chartedEnergyAtMinimizer a ρ (V q.1) q.2) (e, 0) :=
    hE.contDiffAt
  have hM : ∀ i j, ContDiffAt ℝ 2 (fun y => chartedHessian a ρ (V y) 0 i j) e := fun i j =>
    contDiffAt_fderiv_fderiv_apply (Φ := fun y => chartedEnergyAtMinimizer a ρ (V y)) hE4 _ _
  have hD := contDiffAt_det_of_entries hM
  have hZ : IsAnalyticFieldFamily (fun y => fieldAboveFrame true a ρ 0 (V y) 0) e :=
    isAnalytic_fieldAboveFrame hs hL hw hV (η := fun _ => 0) analyticAt_const
  unfold stepLogAmplitude
  refine ((contDiffAt_const.mul (hD.log hdet)).add ?_).add ?_
  · refine ContDiffAt.sum fun b _ => ?_
    simp only [coordsAboveFrame_eq, stepCoordinates_zero, add_zero]
    have h3 : ContDiffAt ℝ 2 haarLogRatio (minimizingBondCoordinate a ρ (finiteCells F) b.1 (V e)) :=
      (hC _ (hsmall b.1 b.2)).1.of_le (by norm_num)
    exact ContDiffAt.comp (g := haarLogRatio)
      (f := fun y => minimizingBondCoordinate a ρ (finiteCells F) b.1 (V y)) e h3 (hw b.1 b.2).contDiffAt
  · refine contDiffAt_const.mul (ContDiffAt.sum fun c _ => ?_)
    have hm : _root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true a ρ 0 (V e) 0) c ≠ 0 := by
      rw [h1, contourAverage_trivial hL]
      exact one_ne_zero
    exact (analyticAt_quat_norm (hZ.analyticAt_contourAverage c) hm).contDiffAt.log (norm_ne_zero_iff.2 hm)
end Frames
theorem stepGaugeTotalContDiff_of_minimizers (hN : MinimizerNearTrivialField) (hW : WilsonActionNondegenerate)
    (hX : NondegenerateAcrossFrames) (hT : minimalActionNondegeneratePropagatesStatement)
    (hH : HaarLogRatioNearZero) : StepGaugeTotalContDiff := by
  intro a ha L hLs t ρ h0 h1
  filter_upwards [eventually_ge_atTop (2 * L)] with n hn k c X
  have hL : Odd L := hLs.1
  have hLp : 0 < L := hL.pos
  have hn2 : 2 ≤ n := by
    have := hLs.2
    omega
  have hpos : ∀ i : Fin 4, 0 < (torusFrame L t n).extent i := fun _ => by
    show 0 < n
    omega
  letI iT := siteFintype (torusFrame L t n) hLp hpos (torusFrame L t n).depth
  have hs : ∀ i, 2 ≤ (torusFrame L t n).extent i := fun _ => hn2
  have hA := minimalAction_nondegenerate_torusFrame hW hX hT ha hL t n hn2 iT
  obtain ⟨hlim, hnear⟩ := hN a ha L hLs t n ρ hn h0 h1
  obtain ⟨⟨w, hwl⟩, -, hpd, -, hco⟩ := hnear.self_of_nhds
  set V₀ := readAtLevel (torusFrame L t n) (torusFrame L t n).top (trivialField n) with hV₀
  set c' : Fin k → (torusFrame L t n).Site (torusFrame L t n).top × Fin 4 :=
    fun l => TorusLevels.bondInFrame (torusFrame L t n) (torusFrame L t n).top (c l) with hc'
  have hV : ∀ σ : Fin k → ℝ,
      readAtLevel (torusFrame L t n) (torusFrame L t n).top (TorusFields.perturb c X σ (trivialField n)) =
        rotatedField (BlockAverages.bondSpread c' X σ) V₀ := fun σ =>
    TorusLevels.readAtLevel_perturb (TorusLevels.torusFrame_period_top L t n) c X σ (trivialField n)
  have hz : rotatedField (BlockAverages.bondSpread c' X (0 : Fin k → ℝ)) V₀ = V₀ := rotatedField_bondSpread_zero c' X V₀
  have hone : fieldAboveFrame true a ρ 0 V₀ 0 = trivialBlockField (torusFrame L t n) (torusFrame L t n).depth := by
    have e1 : minimizerOnFinerTorus a ρ L t n (trivialField n) = trivialField (n * L) :=
      tendsto_nhds_unique (tendsto_pure_nhds _ _) (hlim.mono_left (pure_le_nhds _))
    funext y i
    have e2 := congrFun (congrFun e1 (TorusLumps.toTorusSite (n * L) y)) i
    have e3 : fieldAboveFrame true a ρ 0 V₀ 0 (StepCosts.torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth
        (TorusLumps.toTorusSite (n * L) y)) i = 1 := e2
    rwa [TorusLevels.torusSiteInFrame_toTorusSite (TorusLevels.torusFrame_period_depth L t n)] at e3
  have hsmall : ∀ b ∈ chordBonds (finiteCells (torusFrame L t n)),
      ‖minimizingBondCoordinate a ρ (finiteCells (torusFrame L t n)) b V₀‖ ≤ 1 := by
    intro b hb
    have hex : ∃ w, IsMinimizingChart a (finiteCells (torusFrame L t n)) V₀ ρ w := ⟨w, hwl⟩
    unfold minimizingBondCoordinate minimizingCoordinates
    rw [dif_pos hex]
    exact (hex.choose_spec.2.1 b hb).trans h1
  have key := contDiffAt_stepLogAmplitude (F := torusFrame L t n) (a := a) (ρ := ρ) hs hL hH hA
    (V := fun σ : Fin k → ℝ => rotatedField (BlockAverages.bondSpread c' X σ) V₀) (e := 0) (fun b hb => hco b hb k c' X)
    (isAnalytic_rotatedField c' X V₀) (by simpa only [hz] using hone)
    (by simpa only [hz] using hpd.det_pos.ne') (by simpa only [hz] using hsmall)
  have e : (fun σ : Fin k → ℝ => stepGaugeTotal a ρ L t n (TorusFields.perturb c X σ (trivialField n))) = fun σ =>
      stepLogAmplitude (F := torusFrame L t n) a ρ (rotatedField (BlockAverages.bondSpread c' X σ) V₀) -
        stepLogAmplitude (F := torusFrame L t n) a ρ V₀ := by
    funext σ
    show stepLogAmplitude (F := torusFrame L t n) a ρ
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top (TorusFields.perturb c X σ (trivialField n))) -
      stepLogAmplitude (F := torusFrame L t n) a ρ V₀ = _
    rw [hV σ]
  rw [e]
  exact key.sub contDiffAt_const
end StepGaugeTotalSmooth
end YangMills.Construction.RunningCouplingSlope
end
