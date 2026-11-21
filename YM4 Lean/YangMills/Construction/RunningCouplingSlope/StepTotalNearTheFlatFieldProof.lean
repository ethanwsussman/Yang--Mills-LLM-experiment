import YangMills.Construction.ColdStepAtMirrorFrames.GroupGapIsSmooth
import YangMills.Construction.RunningCouplingSlope.GapsAtTheLeastFieldAreSmallProof
import YangMills.Construction.RunningCouplingSlope.HessianOfAStepIsPositive
import YangMills.Construction.RunningCouplingSlope.StepExponentNearTheFlatField
import YangMills.Construction.RunningCouplingSlope.StepTotalNearTheFlatField
import YangMills.Construction.RunningCouplingSlope.TangentsOfTheLeastField
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepIsTwiceDifferentiableProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings RenormalizationStepParameters ReferenceDensity
  LaplaceAsymptotics SlopeCoefficient StepCosts LumpContours TorusLevels BondCoordinates ColdChain
namespace StepTotalNearTrivial
section Calculus
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem contDiffAt_second_fderiv_apply {Φ : P → E → ℝ} {p₀ : P} {η₀ : E}
    (h : ContDiffAt ℝ 4 (fun q : P × E => Φ q.1 q.2) (p₀, η₀)) (u v : E) :
    ContDiffAt ℝ 2 (fun p => fderiv ℝ (fun ζ => fderiv ℝ (Φ p) ζ u) η₀ v) p₀ := by apply _root_.YangMills.SharedProofs.p66887 <;> assumption
private theorem contDiffAt_det {ι : Type} [Fintype ι] [DecidableEq ι] {M : P → Matrix ι ι ℝ} {p₀ : P}
    (h : ∀ i j, ContDiffAt ℝ 2 (fun p => M p i j) p₀) : ContDiffAt ℝ 2 (fun p => (M p).det) p₀ := by
  simp only [Matrix.det_apply']
  refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul ?_
  exact contDiffAt_prod fun i _ => h _ _
end Calculus
section Frames
variable {F : BlockFrame}
private theorem expUnit_zero_eq_one : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem stepCoordinates_zero (S : Finset F.Cell) : stepCoordinates (0 : StepVariable S) =
    fun (_ : F.Site F.depth) (_ : Fin 4) => (0 : imaginaryQuaternions) := by apply _root_.YangMills.SharedProofs.p23017 <;> assumption
private theorem coordsAboveFrame_zero (a ρ : ℝ) (V : F.GaugeField F.top) (x : F.Site F.depth) (i : Fin 4) :
    coordsAboveFrame true a ρ 0 V 0 x i = minimizingBondCoordinate a ρ (finiteCells F) (x, i) V := by
  simp [coordsAboveFrame, ColdStepAtMirrorFrames.stepFrame, stepCoordinates_zero]
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
private theorem analyticAt_coe {w : X → imaginaryQuaternions} {e : X} (h : AnalyticAt ℝ w e) :
    AnalyticAt ℝ (fun y => (w y : ℍ[ℝ])) e :=
  (imaginaryQuaternions.subtypeL.analyticAt _).comp h
private theorem chartedField_analytic (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    {w : X → F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : X → F.GaugeField F.top} {e : X}
    (hw : ∀ b ∈ chordBonds (finiteCells F), AnalyticAt ℝ (fun y => (w y b.1 b.2 : ℍ[ℝ])) e)
    (hV : IsAnalyticFieldFamily V e) : IsAnalyticFieldFamily (fun y => chartedField (w y) (V y)) e := by apply _root_.YangMills.SharedProofs.p1968 <;> assumption
private theorem rotatedField_analytic {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (Y : Fin k → imaginaryQuaternions) (W : F.GaugeField F.top) :
    IsAnalyticFieldFamily (fun σ : Fin k → ℝ => rotatedField (BlockAverages.bondSpread c Y σ) W) 0 := by apply _root_.YangMills.SharedProofs.p60243 <;> assumption
private theorem fieldAboveFrame_analytic (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide) {a ρ : ℝ}
    {V : X → F.GaugeField F.top} {e : X}
    (hw : ∀ b ∈ chordBonds (finiteCells F),
      AnalyticAt ℝ (fun y => minimizingBondCoordinate a ρ (finiteCells F) b (V y)) e)
    (hV : IsAnalyticFieldFamily V e) : IsAnalyticFieldFamily (fun y => fieldAboveFrame true a ρ 0 (V y) 0) e := by
  refine chartedField_analytic (w := fun y => coordsAboveFrame true a ρ 0 (V y) 0) hs hL (fun b hb => ?_) hV
  simp only [coordsAboveFrame_zero]
  exact analyticAt_coe (hw b hb)
private theorem haarLogRatio_sum_contDiffAt (hH : HaarLogRatioNearZero) {a ρ : ℝ} {V : X → F.GaugeField F.top}
    {e : X}
    (hw : ∀ b ∈ chordBonds (finiteCells F),
      AnalyticAt ℝ (fun y => minimizingBondCoordinate a ρ (finiteCells F) b (V y)) e)
    (hsmall : ∀ b ∈ chordBonds (finiteCells F), ‖minimizingBondCoordinate a ρ (finiteCells F) b (V e)‖ ≤ 1) :
    ContDiffAt ℝ 2 (fun y => ∑ b : ↥(chordBonds (finiteCells F)),
      haarLogRatio (coordsAboveFrame true a ρ 0 (V y) 0 b.1.1 b.1.2)) e := by
  obtain ⟨C, -, hC⟩ := hH
  refine ContDiffAt.sum fun b _ => ?_
  simp only [coordsAboveFrame_zero]
  have h3 : ContDiffAt ℝ 2 haarLogRatio (minimizingBondCoordinate a ρ (finiteCells F) b.1 (V e)) :=
    (hC _ (hsmall b.1 b.2)).1.of_le (by norm_num)
  exact ContDiffAt.comp (g := haarLogRatio)
    (f := fun y => minimizingBondCoordinate a ρ (finiteCells F) b.1 (V y)) e h3 (hw b.1 b.2).contDiffAt
end Frames
section Step
variable {k : ℕ}
private theorem perturb_smul_rescale {n : ℕ} (c : Fin k → TorusBond n) (Y : Fin k → imaginaryQuaternions) (s : ℝ)
    (hs : s ≠ 0) (σ : Fin k → ℝ) (W : TorusField n) :
    perturb c Y σ W = perturb c (fun l => s • Y l) (s⁻¹ • σ) W := by
  funext x i
  unfold perturb
  congr 2
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · simp only [Pi.smul_apply, smul_eq_mul, smul_smul]
    rw [mul_comm s⁻¹, mul_assoc, inv_mul_cancel₀ hs, mul_one]
  · rfl
private theorem perturb_zero_eq {n : ℕ} (c : Fin k → TorusBond n) (Y : Fin k → imaginaryQuaternions)
    (W : TorusField n) : perturb c Y 0 W = W := by
  funext x i
  have e : expUnit (∑ l, if c l = (x, i) then (0 : Fin k → ℝ) l • Y l else 0) = 1 := by
    have : (∑ l, if c l = (x, i) then (0 : Fin k → ℝ) l • Y l else (0 : imaginaryQuaternions)) = 0 := by
      refine Finset.sum_eq_zero fun l _ => ?_
      simp
    rw [this]
    exact expUnit_zero_eq_one
  show expUnit _ * W x i = W x i
  rw [e, one_mul]
variable (R : StepSetup) (n : ℕ) (c : Fin k → TorusBond n) (Y : Fin k → imaginaryQuaternions)
private theorem perturbedTop_analytic : IsAnalyticFieldFamily (perturbedTop R n c Y) 0 := by
  have h := rotatedField_analytic (F := torusFrame R.params.side R.depth n)
    (fun l => bondInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top (c l)) Y
    (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top (trivialField n))
  have e : perturbedTop R n c Y = fun σ : Fin k → ℝ => rotatedField (BlockAverages.bondSpread
      (fun l => bondInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top (c l))
        Y σ)
      (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top (trivialField n)) :=
    funext fun σ => readAtLevel_perturb (torusFrame_period_top R.params.side R.depth n) c Y σ (trivialField n)
  rw [e]
  exact h
private theorem familyHessian_eq_chartedHessian (τ : Fin k → ℝ) :
    familyHessian (chartEnergyAlongCurve R n c Y) τ =
      chartedHessian (F := torusFrame R.params.side R.depth n) R.params.coupling R.anchorRadius
        (perturbedTop R n c Y τ) 0 := by
  ext i j
  have h : ∀ ζ, fderiv ℝ (fun η => chartEnergyAlongCurve R n c Y (τ, η)) ζ =
      fderiv ℝ (chartedEnergyAtMinimizer (F := torusFrame R.params.side R.depth n) R.params.coupling
        R.anchorRadius (perturbedTop R n c Y τ)) ζ :=
    fun ζ => by
      show fderiv ℝ (fun η => chartedEnergyAtMinimizer (F := torusFrame R.params.side R.depth n)
          R.params.coupling R.anchorRadius (perturbedTop R n c Y τ) η -
        chartedEnergyAtMinimizer (F := torusFrame R.params.side R.depth n) R.params.coupling R.anchorRadius
          (perturbedTop R n c Y τ) 0) ζ = _
      exact fderiv_sub_const _
  unfold familyHessian chartedHessian ColdStepAtMirrorFrames.secondDerivAlong
  simp only [h]
private theorem remainder_at_zero (τ : Fin k → ℝ) :
    exponentRemainderAlongCurve R n c Y (τ, 0) =
      -(∑ b ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n))
            (torusFrame R.params.side R.depth n).top,
          haarGapExcess R.params.coupling R.coupling
            (fieldAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c Y τ) 0) b) -
        (∑ b : ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n))),
          haarLogRatio (coordsAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c Y τ) 0
            b.1.1 b.1.2)) -
        ∑ y ∈ sitesOfCells (finiteCells (torusFrame R.params.side R.depth n))
            (torusFrame R.params.side R.depth n).depth,
          centredExpansion true R.params.coupling R.anchorRadius 0 (localFamilyOfDensity R.density) y 0
            (perturbedTop R n c Y τ) := by
  unfold exponentRemainderAlongCurve chartEnergyAlongCurve stepExponent
  simp only [sub_self, mul_zero, zero_sub, one_mul, sub_zero]
private theorem localFamily_eq_cast (g : LocalDensity) {F : BlockFrame} {m : ℕ}
    (hp : ∀ i, F.period F.depth i = m) (y : F.Site F.depth) (W : F.GaugeField F.depth) :
    localFamilyOfDensity g F y W = g m (toTorusSite m y) (restrictToTorus m W) := by
  have h := hp 0
  subst h
  rfl
private theorem densityAtMinimizer_eq_sum (hL : Odd R.params.side) (h2 : 2 ≤ n) (V : TorusField n) :
    densityAtMinimizer R n V = ∑ y ∈ sitesOfCells (finiteCells (torusFrame R.params.side R.depth n))
        (torusFrame R.params.side R.depth n).depth,
      centredExpansion true R.params.coupling R.anchorRadius 0 (localFamilyOfDensity R.density) y 0
        (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V) := by
  have hp := torusFrame_period_depth R.params.side R.depth n
  have hm : n * R.params.side ≠ 0 := Nat.mul_ne_zero (by omega) hL.pos.ne'
  have : NeZero (n * R.params.side) := ⟨hm⟩
  have hs : ∀ i, 2 ≤ (torusFrame R.params.side R.depth n).extent i := fun _ => h2
  have hL' : Odd (torusFrame R.params.side R.depth n).blockSide := hL
  unfold densityAtMinimizer atMinimizer centeredDensityTotal
  rw [dif_neg hm]
  refine Finset.sum_bij'
    (fun x _ => torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).depth x)
    (fun y _ => toTorusSite (n * R.params.side) y) ?_ ?_ ?_ ?_ ?_
  · intro x _
    exact (BlockLevels.mem_sitesOfCells_iff (by simp [BlockFrame.top]) hL').2 (BlockOffsets.mem_finiteCells hs _)
  · intro y _
    exact Finset.mem_univ _
  · intro x _
    exact toTorusSite_torusSiteInFrame hp x
  · intro y _
    exact torusSiteInFrame_toTorusSite hp y
  · intro x _
    unfold centredExpansion ColdStepAtMirrorFrames.subtractTrivial TorusLumps.centered
    rw [localFamily_eq_cast R.density hp, localFamily_eq_cast R.density hp, toTorusSite_torusSiteInFrame hp]
    rfl
end Step
section Core
variable {k : ℕ} (R : StepSetup) (n : ℕ) (c : Fin k → TorusBond n) (Y : Fin k → imaginaryQuaternions)
private theorem stepTotal_core (hH : HaarLogRatioNearZero) (hG : HaarGapContDiff)
    (hL : Odd R.params.side) (h2 : 2 ≤ n) (ha : 0 < R.params.coupling) (hx : 0 < R.coupling)
    (hw : ∀ b ∈ chordBonds (finiteCells (torusFrame R.params.side R.depth n)), AnalyticAt ℝ
      (fun τ => minimizingBondCoordinate R.params.coupling R.anchorRadius
        (finiteCells (torusFrame R.params.side R.depth n)) b (perturbedTop R n c Y τ)) 0)
    (h1 : fieldAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c Y 0) 0 =
      trivialBlockField (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).depth)
    (hsmall : ∀ b ∈ chordBonds (finiteCells (torusFrame R.params.side R.depth n)),
      ‖minimizingBondCoordinate R.params.coupling R.anchorRadius
        (finiteCells (torusFrame R.params.side R.depth n)) b (perturbedTop R n c Y 0)‖ ≤ 1)
    (hdet : (familyHessian (chartEnergyAlongCurve R n c Y) 0).det ≠ 0)
    (hQ : ContDiffAt ℝ 4 (chartEnergyAlongCurve R n c Y) (0, 0))
    (hB : ContDiffAt ℝ 3 (exponentRemainderAlongCurve R n c Y) (0, 0)) :
    ContDiffAt ℝ 2 (fun τ : Fin k → ℝ => stepGaugeTotal R.params.coupling R.anchorRadius R.params.side R.depth n
      (perturb c Y τ (trivialField n))) 0 ∧
    ContDiffAt ℝ 2 (fun τ : Fin k → ℝ => densityAtMinimizer R n (perturb c Y τ (trivialField n))) 0 ∧
    ∃ κ : ℝ, ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ),
      stepGaugeTotal R.params.coupling R.anchorRadius R.params.side R.depth n (perturb c Y τ (trivialField n)) +
          densityAtMinimizer R n (perturb c Y τ (trivialField n)) =
        κ + gaussianLogValue (chartEnergyAlongCurve R n c Y) (exponentRemainderAlongCurve R n c Y) τ -
          haarGapSumAlongCurve R n c Y τ := by
  have hs : ∀ i, 2 ≤ (torusFrame R.params.side R.depth n).extent i := fun _ => h2
  have hL' : Odd (torusFrame R.params.side R.depth n).blockSide := hL
  have hZ := fieldAboveFrame_analytic hs hL' hw (perturbedTop_analytic R n c Y)
  have hm0 : ∀ b, _root_.YangMills.Construction.BlockAverages.contourAverage
      (fieldAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c Y 0) 0) b ≠ 0 := by
    intro b
    rw [h1, contourAverage_trivial hL']
    exact one_ne_zero
  have hM : ∀ i j, ContDiffAt ℝ 2 (fun τ => familyHessian (chartEnergyAlongCurve R n c Y) τ i j) 0 :=
    fun i j => contDiffAt_second_fderiv_apply (Φ := fun τ η => chartEnergyAlongCurve R n c Y (τ, η)) hQ _ _
  have hD : ContDiffAt ℝ 2 (fun τ => Real.log (familyHessian (chartEnergyAlongCurve R n c Y) τ).det) 0 :=
    (contDiffAt_det hM).log hdet
  have hHaar := haarLogRatio_sum_contDiffAt hH hw hsmall
  have hLog : ContDiffAt ℝ 2 (fun τ => ∑ b ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n))
        (torusFrame R.params.side R.depth n).top,
      Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage
        (fieldAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c Y τ) 0) b‖) 0 :=
    ContDiffAt.sum fun b _ =>
      (analyticAt_quat_norm (hZ.analyticAt_contourAverage b) (hm0 b)).contDiffAt.log (norm_ne_zero_iff.2 (hm0 b))
  have hGap : ContDiffAt ℝ 2 (fun τ => ∑ b ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n))
        (torusFrame R.params.side R.depth n).top,
      haarGapExcess R.params.coupling R.coupling
        (fieldAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c Y τ) 0) b) 0 := by
    refine ContDiffAt.sum fun b _ => ?_
    unfold haarGapExcess
    have hn : ContDiffAt ℝ 2 (fun τ => R.params.coupling * R.coupling *
        ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c Y τ) 0) b‖) 0 :=
      contDiffAt_const.mul (analyticAt_quat_norm (hZ.analyticAt_contourAverage b) (hm0 b)).contDiffAt
    have hg : ContDiff ℝ 2 haarGap := hG.of_le (by norm_num)
    exact (hg.contDiffAt.comp (0 : Fin k → ℝ) hn).sub contDiffAt_const
  have hB0 : ContDiffAt ℝ 2 (fun τ : Fin k → ℝ => exponentRemainderAlongCurve R n c Y (τ, 0)) 0 := by
    have hB2 : ContDiffAt ℝ 2 (exponentRemainderAlongCurve R n c Y) (0, 0) := hB.of_le (by norm_num)
    have hin : ContDiffAt ℝ 2 (fun τ : Fin k → ℝ =>
        ((τ, 0) : (Fin k → ℝ) × StepVariable (finiteCells (torusFrame R.params.side R.depth n)))) 0 :=
      contDiffAt_id.prodMk contDiffAt_const
    exact ContDiffAt.comp (0 : Fin k → ℝ) hB2 hin
  have hstep : ∀ τ : Fin k → ℝ,
      stepGaugeTotal R.params.coupling R.anchorRadius R.params.side R.depth n (perturb c Y τ (trivialField n)) =
      -(1 / 2) * Real.log (familyHessian (chartEnergyAlongCurve R n c Y) τ).det +
        (∑ b : ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n))),
          haarLogRatio (coordsAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c Y τ) 0
            b.1.1 b.1.2)) +
        3 / 2 * (∑ b ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n))
            (torusFrame R.params.side R.depth n).top,
          Real.log ‖contourAverage
            (fieldAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c Y τ) 0) b‖) -
        stepLogAmplitude (F := torusFrame R.params.side R.depth n) R.params.coupling R.anchorRadius
          (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top
            (trivialField n)) := by
    intro τ
    rw [familyHessian_eq_chartedHessian]
    rfl
  have hdensity : ∀ τ : Fin k → ℝ, densityAtMinimizer R n (perturb c Y τ (trivialField n)) =
      -exponentRemainderAlongCurve R n c Y (τ, 0) -
        (∑ b ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n))
            (torusFrame R.params.side R.depth n).top,
          haarGapExcess R.params.coupling R.coupling
            (fieldAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c Y τ) 0) b) -
        ∑ b : ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n))),
          haarLogRatio (coordsAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c Y τ) 0
            b.1.1 b.1.2) := by
    intro τ
    rw [remainder_at_zero, densityAtMinimizer_eq_sum R n hL h2]
    have e : readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top
        (perturb c Y τ (trivialField n)) = perturbedTop R n c Y τ := rfl
    rw [e]
    ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [hstep]
    exact (((contDiffAt_const.mul hD).add hHaar).add (contDiffAt_const.mul hLog)).sub contDiffAt_const
  · simp only [hdensity]
    exact (hB0.neg.sub hGap).sub hHaar
  · have hax : R.params.coupling * R.coupling ≠ 0 := (mul_pos ha hx).ne'
    set K : ℝ := ∑ b ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n))
        (torusFrame R.params.side R.depth n).top,
      (3 / 2 * Real.log (R.params.coupling * R.coupling) - haarGap (R.params.coupling * R.coupling)) with hK
    refine ⟨-stepLogAmplitude (F := torusFrame R.params.side R.depth n) R.params.coupling R.anchorRadius
      (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top
        (trivialField n)) - K, ?_⟩
    have hne : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), ∀ b ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n))
        (torusFrame R.params.side R.depth n).top,
        _root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c Y τ) 0) b ≠ 0 := by
      rw [Filter.eventually_all_finset]
      intro b _
      exact (hZ.analyticAt_contourAverage b).continuousAt.eventually_ne (hm0 b)
    filter_upwards [hne] with τ hτ
    have hsum : (∑ b ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n))
            (torusFrame R.params.side R.depth n).top,
          haarGapExcess R.params.coupling R.coupling
            (fieldAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c Y τ) 0) b) -
        haarGapSumAlongCurve R n c Y τ =
        K + 3 / 2 * ∑ b ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n))
            (torusFrame R.params.side R.depth n).top,
          Real.log ‖contourAverage
            (fieldAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c Y τ) 0) b‖ := by
      unfold haarGapSumAlongCurve
      rw [hK, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b hb => ?_
      unfold haarGapExcess haarGapSubLog contourAverageNorm
      rw [Real.log_mul hax (norm_ne_zero_iff.2 (hτ b hb))]
      ring
    rw [hstep τ, hdensity τ]
    unfold gaussianLogValue
    linarith
end Core
section Chain
variable {F : BlockFrame}
private theorem flatTopField_isCold {s : ℝ} (hs : 0 < s) (S : Finset F.Cell) :
    IsCold S F.top s (BlockAverages.flatTopField : F.GaugeField F.top) := by apply _root_.YangMills.SharedProofs.p30906 <;> assumption
variable {a ρ δ lam σA cg : ℝ} {N : ℕ → ℝ} {L : ℕ}
private theorem chain_at_trivial (hc : ColdChainConstants a δ L lam ρ σA cg N) {t m : ℕ} [NeZero m]
    (hm : 64 ≤ m) :
    (∃ w, IsMinimizingChart a (finiteCells (torusFrame L t m))
      (readAtLevel (torusFrame L t m) (torusFrame L t m).top (trivialField m)) ρ w) ∧
    HasRegularCoordinates a δ ρ N (finiteCells (torusFrame L t m))
      (readAtLevel (torusFrame L t m) (torusFrame L t m).top (trivialField m)) := by
  obtain ⟨_, _, _, _, _, hσ, _, _, hmain⟩ := hc
  have hs : ∀ i, 2 ≤ (torusFrame L t m).extent i := fun _ => (show 2 ≤ m by omega)
  have hreg : IsOrthantRegular (finiteCells (torusFrame L t m)) 1024 := fun z =>
    ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ _ _ _ _ _ => BlockOffsets.mem_finiteCells hs _⟩
  have h := hmain (torusFrame L t m) 1024 (finiteCells _) rfl (Or.inr fun _ => hm) le_rfl hreg σA
    BlockAverages.flatTopField hσ le_rfl (flatTopField_isCold hσ _)
  obtain ⟨⟨w, hw, -⟩, -, -, hco, -⟩ := h
  exact ⟨⟨w, hw.1, fun b hb => (hw.2.1 b hb).trans (min_le_left _ _), hw.2.2⟩, hco⟩
end Chain
end StepTotalNearTrivial
open StepTotalNearTrivial in
theorem stepTotalNearTrivial (hB : stepExponentNearTrivialStatement)
    (hP : stepHessianPosDefStatement) (hZ : MinimizerDerivativeDecay)
    (hH : HaarLogRatioNearZero) (hG : HaarGapContDiff) :
    stepTotalNearTrivialStatement := by
  intro T hT y R hy hR n _ c Y hn
  have hl := hR.params_eq
  have eA : R.params.coupling = T.coupling := by rw [hl]; rfl
  have eL : R.params.side = T.side := by rw [hl]; rfl
  have eR : R.anchorRadius = T.ρA := hR.anchorRadius_eq
  have h64 : 64 ≤ n := le_trans (by have := hT.n₀_ge; omega) hn
  have h2 : 2 ≤ n := by omega
  have hodd : Odd R.params.side := by rw [eL]; exact hT.L_odd
  have ha : 0 < R.params.coupling := by
    rw [eA]
    linarith [hT.a_ge]
  have hx1 : 1 ≤ R.coupling := by
    have h1 : (1 : ℝ) ≤ T.floorMin := by
      unfold ParameterAssignment.floorMin
      refine le_trans ?_ (le_max_right _ _)
      exact one_le_pow₀ (by norm_num)
    exact h1.trans (hy.trans hR.le_coupling)
  have hx : 0 < R.coupling := by linarith
  have hc : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [eA, eL, eR]
    exact hT.chain
  have hρ1 : R.anchorRadius ≤ 1 := hc.2.2.2.2.1
  obtain ⟨⟨w, hw⟩, hco⟩ := chain_at_trivial (t := R.depth) hc h64
  have hcurve : ∀ τ : Fin _ → ℝ, perturbedTop R n c Y τ = rotatedField (BlockAverages.bondSpread
      (fun l => bondInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top (c l))
        Y τ)
      (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top (trivialField n)) :=
    fun τ => readAtLevel_perturb (torusFrame_period_top R.params.side R.depth n) c Y τ (trivialField n)
  have hcurve0 : perturbedTop R n c Y 0 =
      readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top
        (trivialField n) := by
    unfold perturbedTop
    rw [perturb_zero_eq]
  have hcoord : ∀ b ∈ chordBonds (finiteCells (torusFrame R.params.side R.depth n)), AnalyticAt ℝ
      (fun τ => minimizingBondCoordinate R.params.coupling R.anchorRadius
        (finiteCells (torusFrame R.params.side R.depth n)) b (perturbedTop R n c Y τ)) 0 := by
    intro b hb
    simp only [hcurve]
    exact (hco b hb).1 _ _ Y
  have hflat : ∀ (a ρ : ℝ) (L : ℕ), a = T.coupling → ρ = T.ρA → L = T.side →
      minimizerOnFinerTorus a ρ L R.depth n (trivialField n) = trivialField (n * L) := by
    rintro _ _ _ rfl rfl rfl
    obtain ⟨M, θ, -, -, Z, hZ'⟩ := hZ T hT
    exact ((hZ' R.depth).1 n h64).1.map_trivial
  have hone : fieldAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c Y 0) 0 =
      trivialBlockField (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).depth := by
    rw [hcurve0]
    have e1 := hflat R.params.coupling R.anchorRadius R.params.side eA eR eL
    funext z i
    have e2 := congrFun (congrFun e1 (toTorusSite (n * R.params.side) z)) i
    have e3 : fieldAboveFrame true R.params.coupling R.anchorRadius 0
        (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top
          (trivialField n)) 0
        (torusSiteInFrame (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).depth
          (toTorusSite (n * R.params.side) z)) i = 1 := e2
    rwa [torusSiteInFrame_toTorusSite (torusFrame_period_depth R.params.side R.depth n)] at e3
  have hsmall : ∀ b ∈ chordBonds (finiteCells (torusFrame R.params.side R.depth n)),
      ‖minimizingBondCoordinate R.params.coupling R.anchorRadius
        (finiteCells (torusFrame R.params.side R.depth n)) b (perturbedTop R n c Y 0)‖ ≤ 1 := by
    intro b hb
    rw [hcurve0]
    have hex : ∃ w, IsMinimizingChart R.params.coupling (finiteCells (torusFrame R.params.side R.depth n))
        (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top
          (trivialField n)) R.anchorRadius w := ⟨w, hw⟩
    unfold minimizingBondCoordinate minimizingCoordinates
    rw [dif_pos hex]
    exact (hex.choose_spec.2.1 b hb).trans hρ1
  have hpos : ∀ (a ρ : ℝ) (L : ℕ), a = T.coupling → ρ = T.ρA → L = T.side →
      (chartedHessian (F := torusFrame L R.depth n) a ρ
        (readAtLevel (torusFrame L R.depth n) (torusFrame L R.depth n).top (trivialField n)) 0).PosDef := by
    rintro _ _ _ rfl rfl rfl
    refine hP T hT R.depth n (trivialField n) h64 ?_
    intro x μ ν _
    have hσ := hT.σ_pos
    simpa [TorusFields.curvature, TorusFields.holonomy, trivialField] using
      (by positivity : 0 < 9 / 8 * T.threshold)
  have hdet : (familyHessian (chartEnergyAlongCurve R n c Y) 0).det ≠ 0 := by
    rw [familyHessian_eq_chartedHessian, hcurve0]
    exact (hpos R.params.coupling R.anchorRadius R.params.side eA eR eL).det_pos.ne'
  set s : ℝ := (1 + ∑ l, ‖Y l‖)⁻¹ with hs
  have hs0 : 0 < s := by positivity
  have hYle : ∀ l, ‖s • Y l‖ ≤ 1 := by
    intro l
    have h1 : ‖Y l‖ ≤ ∑ l, ‖Y l‖ :=
      Finset.single_le_sum (f := fun l => ‖Y l‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ l)
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
    rw [hs, inv_mul_le_iff₀ (by positivity)]
    linarith
  obtain ⟨C, q, -, -, hfam⟩ := hB T hT 2
  obtain ⟨-, -, hL⟩ := hfam y R hy hR n c (fun l => s • Y l) hn hYle
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold ParameterAssignment.ballRadius
    positivity
  have h00 : ∀ b, ‖(0 : BondField ↥(chordBonds (finiteCells (torusFrame R.params.side R.depth n)))) b‖ ≤
      T.ballRadius := fun b => by
    simpa using hρ.le
  have hlin : ContDiffAt ℝ 5 (fun q : (Fin 2 → ℝ) × StepVariable (finiteCells (torusFrame R.params.side R.depth n)) =>
      ((s⁻¹ • q.1, q.2) : (Fin 2 → ℝ) × StepVariable (finiteCells (torusFrame R.params.side R.depth n)))) (0, 0) :=
    (contDiff_fst.const_smul s⁻¹).contDiffAt.prodMk contDiffAt_snd
  have hlin0 : ((s⁻¹ • (0, 0).1, (0, 0).2) :
      (Fin 2 → ℝ) × StepVariable (finiteCells (torusFrame R.params.side R.depth n))) = (0, 0) := by
    simp
  have eTop : ∀ τ, perturbedTop R n c Y τ = perturbedTop R n c (fun l => s • Y l) (s⁻¹ • τ) := by
    intro τ
    unfold perturbedTop
    rw [perturb_smul_rescale c Y s hs0.ne' τ]
  have hQ : ContDiffAt ℝ 4 (chartEnergyAlongCurve R n c Y) (0, 0) := by
    have h5 := hL.contDiff_Q 0 h00
    have e : chartEnergyAlongCurve R n c Y = chartEnergyAlongCurve R n c (fun l => s • Y l) ∘
        fun q : (Fin 2 → ℝ) × StepVariable (finiteCells (torusFrame R.params.side R.depth n)) =>
          (s⁻¹ • q.1, q.2) := by
      funext q
      simp only [Function.comp_apply]
      unfold chartEnergyAlongCurve
      simp only []
      rw [eTop]
    rw [e]
    refine (ContDiffAt.comp (0, 0) ?_ hlin).of_le (by norm_num)
    rw [hlin0]
    exact h5
  have hBs : ContDiffAt ℝ 3 (exponentRemainderAlongCurve R n c Y) (0, 0) := by
    have h3 := hL.contDiff_B 0 h00
    have e : exponentRemainderAlongCurve R n c Y = exponentRemainderAlongCurve R n c (fun l => s • Y l) ∘
        fun q : (Fin 2 → ℝ) × StepVariable (finiteCells (torusFrame R.params.side R.depth n)) =>
          (s⁻¹ • q.1, q.2) := by
      funext q
      simp only [Function.comp_apply]
      unfold exponentRemainderAlongCurve chartEnergyAlongCurve
      simp only []
      rw [eTop]
    rw [e]
    refine ContDiffAt.comp (0, 0) ?_ (hlin.of_le (by norm_num))
    rw [hlin0]
    exact h3
  have e1 : stepGaugeTotal T.coupling T.ρA T.side R.depth =
      stepGaugeTotal R.params.coupling R.anchorRadius R.params.side R.depth := by rw [eA, eL, eR]
  rw [e1]
  exact stepTotal_core R n c Y hH hG hodd h2 ha hx hcoord hone hsmall hdet hQ hBs
end YangMills.Construction.RunningCouplingSlope
end
