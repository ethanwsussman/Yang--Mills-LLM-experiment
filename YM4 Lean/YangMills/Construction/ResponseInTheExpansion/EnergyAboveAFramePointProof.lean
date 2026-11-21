import YangMills.Construction.ColdStepAtMirrorFrames.ConvexAboveAChartPointProof
import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenBoundsProof
import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinatesProof
import YangMills.Construction.ResponseInTheExpansion.EnergyAboveAFramePoint
import YangMills.Construction.RunningCouplingSlope.InverseOfTheHessianOfTheChartProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace ResponseInTheExpansion.BasePointEnergy
section Calculus
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
theorem contDiffAt_of_contDiffAt_shift {f : P → ℝ} {η : P} (h : ContDiffAt ℝ 3 (fun ζ => f (η + ζ)) 0) :
    ContDiffAt ℝ 3 f η := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.contDiffAt_of_comp_add_left <;> assumption
theorem deriv_deriv_line_eq_fderiv {f : P → ℝ} (hf : ContDiffAt ℝ 3 f 0) (u : P) :
    deriv (deriv fun τ : ℝ => f (τ • u)) 0 = fderiv ℝ (fun ζ => fderiv ℝ f ζ u) 0 u := by apply _root_.YangMills.SharedProofs.p4878 <;> assumption
end Calculus
variable {F : BlockFrame}
abbrev ChordBond (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F))
theorem norm_toImaginary (v : BondVector) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.norm_toImaginary <;> assumption
theorem stepCoordinates_add (η ζ : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (η + ζ) x i = stepCoordinates η x i + stepCoordinates ζ x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_add <;> assumption
theorem stepCoordinates_smul (r : ℝ) (η : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (r • η) x i = r • stepCoordinates η x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_smul <;> assumption
theorem stepCoordinates_of_not_mem (η : StepVariable (finiteCells F)) {b : F.Site F.depth × Fin 4}
    (hb : b ∉ chordBonds (finiteCells F)) : stepCoordinates η b.1 b.2 = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_of_not_mem <;> assumption
theorem stepCoordinates_chord (η : StepVariable (finiteCells F)) (b : ChordBond F) :
    stepCoordinates η b.1.1 b.1.2 = toImaginary (η b) := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.stepCoordinates_of_chordBond <;> assumption
theorem chartedEnergyAt_add (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (η ζ : StepVariable (finiteCells F)) :
    chartedEnergyAt a w V (η + ζ) = chartedEnergyAt a (shiftCoordinates w η) V ζ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.chartedEnergyAt_add <;> assumption
theorem shiftCoordinates_zero (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) :
    shiftCoordinates w (0 : StepVariable (finiteCells F)) = w := by apply _root_.YangMills.SharedProofs.p71543 <;> assumption
theorem chartedField_congr (hB : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions} (V : F.GaugeField F.top)
    (h : ∀ b ∈ chordBonds (finiteCells F), w b.1 b.2 = w' b.1 b.2) :
    chartedField w V = chartedField w' V := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.chartedField_congr <;> assumption
set_option maxHeartbeats 2000000 in
theorem energyAboveBasePoint (hR : ChartEnergyHessianRowsEventually) (hFr : FrameBoundsEventually)
    (hJ : EventuallyInParametersCombines) (hM : ChartShiftLipschitz)
    (hB : BlocksCoverLowerLevel) : EnergyAboveBasePoint := by
  classical
  refine hJ.2 _ _ ?_ (hJ.1 _ _ hR hFr)
  rintro T hT ⟨hRt, hfr⟩
  obtain ⟨Cf, C, _, _, hCfT, hCT', hL40, hn64, hκ1, hσ1, _, _, hσA, hy1, hay, _⟩ := hfr
  have hρ0 : 0 < T.ballRadius := by
    unfold StepParameters.ballRadius
    have := hT.σ_pos
    positivity
  intro t F V w hF hV hp
  have hOdd : Odd T.L := hT.odd_L
  have hσ0 : 0 < T.σ := hT.σ_pos
  have hFcopy := hF
  obtain ⟨hFL, hFt, n, hside, hn⟩ := hFcopy
  have hn0 : 64 ≤ n := hn64.trans hn
  have hpos : ∀ i, 0 < F.extent i := fun i => by rw [hside]; omega
  have hOddF : Odd F.blockSide := hFL ▸ hOdd
  have hCT : IsBlockTorus T.L F := ⟨hFL, n, hn0, hside⟩
  obtain ⟨KA, hKAs, hKAp, hKArow, hKAM⟩ := hRt F V hCT
  have hclauses := hT.chain_admissible.estimates F (5 / 4 * T.σ) V hCT (by positivity) hσA hV
  have hfloor := hclauses.hessian
  have hcoord : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) → ∀ x i,
      ‖stepCoordinates η x i‖ ≤ T.ballRadius := fun η hη => (hM F V w η T.ballRadius hOddF hη hρ0.le).1
  have hcold : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsSmallCurvature T.σ (chartedField (shiftCoordinates w η) V) := by
    intro η hη p hp'
    have h1 := (hM F V w η T.ballRadius hOddF hη hρ0.le).2.1 p
    have h2 := hp.curvature_small p hp'
    have h3 : T.ballRadius = T.σ / 64 := rfl
    have h4 : plaquetteDefect (chartedField (shiftCoordinates w η) V) p ≤
        plaquetteDefect (chartedField w V) p + 4 * T.ballRadius := h1
    linarith
  have hσσ : T.σ ≤ T.chainParams.σA := by linarith
  have hsmall : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsAdmissibleChartPoint T.L T.chainParams.σA (shiftCoordinates w η) V := by
    intro η hη
    refine ⟨fun b hb => ?_, fun p hp' => (hcold η hη p hp').trans_le hσσ⟩
    have h1 := hcoord η hη b.1 b.2
    have h2 := hp.small b hb
    calc ‖shiftCoordinates w η b.1 b.2‖ ≤ ‖w b.1 b.2‖ + ‖stepCoordinates η b.1 b.2‖ := norm_add_le _ _
      _ ≤ ‖w b.1 b.2‖ + T.ballRadius := by linarith
      _ ≤ _ := h2
  set A : StepVariable (finiteCells F) → ℝ := chartedEnergyAt T.a w V with hA
  have hshift : ∀ η : StepVariable (finiteCells F),
      (fun ζ => A (η + ζ)) = chartedEnergyAt T.a (shiftCoordinates w η) V :=
    fun η => funext fun ζ => chartedEnergyAt_add T.a w V η ζ
  have hAsm : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) → ContDiffAt ℝ 3 A η := by
    intro η hη
    apply contDiffAt_of_contDiffAt_shift
    rw [hshift]
    exact (hKAp _ (hsmall η hη)).1
  have h00 : ∀ b, ‖(0 : StepVariable (finiteCells F)) b‖ ≤ T.ballRadius := fun b => by simpa using hρ0.le
  have hw0 : IsAdmissibleChartPoint T.L T.chainParams.σA w V := by
    have := hsmall 0 h00
    rwa [shiftCoordinates_zero] at this
  refine ⟨hCT, fun η hη => ⟨hsmall η hη, hAsm η hη⟩, ?_, KA, fun b b' e e' => (hKAp w hw0).2 b b' e e', ?_⟩
  · intro u
    set wm : F.Site F.depth → Fin 4 → imaginaryQuaternions :=
      fun x i => if (x, i) ∈ chordBonds (finiteCells F) then w x i else 0 with hwm
    have h1 := hfloor wm (stepCoordinates u)
      (fun b hb => by simp only [hwm]; rw [if_neg hb])
      (fun b hb => stepCoordinates_of_not_mem u hb)
      (fun b hb => by
        simp only [hwm]
        rw [if_pos hb]
        have h3 := hp.room b hb
        have := hρ0.le
        linarith)
      (by
        have e : chartedField wm V = chartedField w V :=
          chartedField_congr hB hOddF hpos V fun b hb => by simp only [hwm]; rw [if_pos hb]
        rw [e]
        intro p hp'
        have hlt : p.2.1 < p.2.2 := (Finset.mem_filter.1 hp').2.1
        have h3 := hp.curvature_small p hlt
        have : 41 / 64 * T.σ ≤ T.chainParams.σA := by linarith
        exact h3.trans_le this)
    have hsum : ∑ b ∈ chordBonds (finiteCells F), ‖stepCoordinates u b.1 b.2‖ ^ 2 =
        ∑ b : ChordBond F, ‖u b‖ ^ 2 := by
      rw [← Finset.sum_coe_sort]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [stepCoordinates_chord, norm_toImaginary]
    have hfun : (fun τ : ℝ => blockEnergy T.a (finiteCells F) F.depth
        (chartedField (fun x i => wm x i + τ • stepCoordinates u x i) V) V) = fun τ : ℝ => A (τ • u) := by
      funext τ
      have e : chartedField (fun x i => wm x i + τ • stepCoordinates u x i) V =
          chartedField (fun x i => w x i + stepCoordinates (τ • u) x i) V := by
        refine chartedField_congr hB hOddF hpos V fun b hb => ?_
        simp only [hwm]
        rw [if_pos hb, stepCoordinates_smul]
      rw [e]
      rfl
    rw [hsum, hfun, deriv_deriv_line_eq_fderiv (hAsm 0 h00) u] at h1
    exact h1
  · intro b
    have := hKArow b
    have hl : 0 < T.chainParams.lam := hT.chain_admissible.positivity.2.2.1
    exact this
end ResponseInTheExpansion.BasePointEnergy
end YangMills.Construction
end
