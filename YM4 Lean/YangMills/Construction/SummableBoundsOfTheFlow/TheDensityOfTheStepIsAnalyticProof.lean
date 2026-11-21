import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsAnalyticAtParametersProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensityOfTheStepIsAnalytic
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames.StepDensity
private theorem analyticAt_integral_diag_resolvent {ι E : Type} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : E → Matrix ι ι ℝ) (z : E) (l : ℝ) (P : ι → Prop) [DecidablePred P]
    (hM : ∀ i j, AnalyticAt ℝ (fun τ => M τ i j) z)
    (hU : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsUnit (s • M z + (1 - s) • l • (1 : Matrix ι ι ℝ))) :
    AnalyticAt ℝ (fun τ => ∫ s in (0 : ℝ)..1, ∑ i, if P i then
      ((M τ - l • (1 : Matrix ι ι ℝ)) * (s • M τ + (1 - s) • l • (1 : Matrix ι ι ℝ))⁻¹) i i else 0) z := by apply _root_.YangMills.SharedProofs.p91236 <;> assumption
section Quaternions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {z : E}
private def conjCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  LinearMap.toContinuousLinearMap
    { toFun := star, map_add' := star_add, map_smul' := fun r q => by ext <;> simp }
private theorem analyticAt_log_norm {G : E → ℍ[ℝ]} (hG : AnalyticAt ℝ G z) (h0 : G z ≠ 0) :
    AnalyticAt ℝ (fun σ => Real.log ‖G σ‖) z := by apply _root_.YangMills.SharedProofs.p33293 <;> assumption
private theorem analyticAt_expUnit {w : E → imaginaryQuaternions} (hw : AnalyticAt ℝ w z) :
    AnalyticAt ℝ (fun p => ((expUnit (w p) : UnitQuaternion) : ℍ[ℝ])) z := by apply _root_.YangMills.SharedProofs.p29648 <;> assumption
variable {F : BlockFrame} {j : ℕ}
private theorem analyticAt_contourAverage {X : E → F.GaugeField j}
    (hX : ∀ x i, AnalyticAt ℝ (fun σ => ((X σ x i : UnitQuaternion) : ℍ[ℝ])) z)
    (c : F.Site (j + 1) × Fin 4) : AnalyticAt ℝ (fun σ => BlockAverages.contourAverage (X σ) c) z := by apply _root_.YangMills.SharedProofs.p5864 <;> assumption
end Quaternions
section Haar
private theorem analyticAt_haarLogRatio {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {z : E}
    {w : E → imaginaryQuaternions} (hw : AnalyticAt ℝ w z) (h : ‖w z‖ < Real.pi) :
    AnalyticAt ℝ (fun σ => haarLogRatio (w σ)) z := by apply _root_.YangMills.SharedProofs.p101296 <;> assumption
end Haar
section Calculus
variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
private def secondDerivAlong (f : H → ℝ) (P : G →L[ℝ] H) (u v : G) (p : H) : ℝ :=
  fderiv ℝ (fun q => fderiv ℝ f q (P u)) p (P v)
private theorem analyticAt_fderiv_apply {f : H → ℝ} {p : H} (hf : AnalyticAt ℝ f p) (e : H) :
    AnalyticAt ℝ (fun q => fderiv ℝ f q e) p :=
  ((ContinuousLinearMap.apply ℝ ℝ e).analyticAt _).comp hf.fderiv
private theorem analyticAt_secondDerivAlong {f : H → ℝ} {p : H} (P : G →L[ℝ] H) (hf : AnalyticAt ℝ f p)
    (u v : G) : AnalyticAt ℝ (secondDerivAlong f P u v) p :=
  analyticAt_fderiv_apply (analyticAt_fderiv_apply hf (P u)) (P v)
private theorem fderiv_comp_add_clm (g : H → ℝ) (P : G →L[ℝ] H) (p : H) (ζ : G)
    (hd : DifferentiableAt ℝ g (p + P ζ)) :
    fderiv ℝ (fun η => g (p + P η)) ζ = (fderiv ℝ g (p + P ζ)).comp P := by
  have h1 : HasFDerivAt (fun η => p + P η) P ζ := P.hasFDerivAt.const_add p
  exact (hd.hasFDerivAt.comp ζ h1).fderiv
private theorem second_fderiv_comp_add_clm {f : H → ℝ} {p : H} (P : G →L[ℝ] H) (hf : AnalyticAt ℝ f p)
    (u v : G) :
    fderiv ℝ (fun ζ => fderiv ℝ (fun η => f (p + P η)) ζ u) 0 v = secondDerivAlong f P u v p := by
  have hcont : Filter.Tendsto (fun ζ : G => p + P ζ) (𝓝 0) (𝓝 p) := by
    have h : Continuous (fun ζ : G => p + P ζ) := by fun_prop
    simpa using h.tendsto 0
  have hev : ∀ᶠ ζ in 𝓝 (0 : G), AnalyticAt ℝ f (p + P ζ) := hcont.eventually hf.eventually_analyticAt
  have heq : (fun ζ => fderiv ℝ (fun η => f (p + P η)) ζ u) =ᶠ[𝓝 0]
      fun ζ => (fun q => fderiv ℝ f q (P u)) (p + P ζ) := by
    filter_upwards [hev] with ζ hζ
    rw [fderiv_comp_add_clm f P p ζ hζ.differentiableAt]
    rfl
  rw [heq.fderiv_eq]
  have hg : DifferentiableAt ℝ (fun q => fderiv ℝ f q (P u)) (p + P 0) := by
    rw [map_zero, add_zero]
    exact (analyticAt_fderiv_apply hf (P u)).differentiableAt
  rw [fderiv_comp_add_clm (fun q => fderiv ℝ f q (P u)) P p 0 hg, map_zero, add_zero]
  rfl
private theorem hasFDerivAt_fderiv_apply {Ψ : G → ℝ} (hΨ : AnalyticAt ℝ Ψ 0) (u : G) :
    HasFDerivAt (fun ζ => fderiv ℝ Ψ ζ u)
      ((ContinuousLinearMap.apply ℝ ℝ u).comp (fderiv ℝ (fderiv ℝ Ψ) 0)) 0 :=
  (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp 0 hΨ.fderiv.differentiableAt.hasFDerivAt
private theorem deriv_deriv_along_line {Ψ : G → ℝ} (hΨ : AnalyticAt ℝ Ψ 0) (u : G) :
    deriv (deriv fun r : ℝ => Ψ (r • u)) 0 = fderiv ℝ (fderiv ℝ Ψ) 0 u u := by apply _root_.YangMills.SharedProofs.p66357 <;> assumption
end Calculus
section Floor
variable {B : Type} [Fintype B] [DecidableEq B]
private def basisField (i : B × Fin 3) : BondField B := bondVariation i.1 (EuclideanSpace.single i.2 1)
private theorem isUnit_of_hessian_floor {Ψ : BondField B → ℝ} (hΨ : AnalyticAt ℝ Ψ 0) {lam : ℝ}
    (hlam : 0 < lam)
    (hfl : ∀ u : BondField B, lam * ∑ b, ‖u b‖ ^ 2 ≤ deriv (deriv fun r : ℝ => Ψ (r • u)) 0)
    (S : Matrix (B × Fin 3) (B × Fin 3) ℝ)
    (hS : ∀ i j, S i j = fderiv ℝ (fun ζ => fderiv ℝ Ψ ζ (basisField i)) 0 (basisField j)) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    IsUnit (s • S + (1 - s) • lam • (1 : Matrix (B × Fin 3) (B × Fin 3) ℝ)) := by apply _root_.YangMills.DeltaSharedProofs.p1583 <;> assumption
end Floor
section Chart
variable {F : BlockFrame}
private theorem toImaginary_zero : toImaginary (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by apply _root_.YangMills.Construction.BondCoordinates.toImaginary_zero <;> assumption
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
private theorem stepCoordinates_add_smul (u v : StepVariable (finiteCells F)) (θ : ℝ) (x : F.Site F.depth)
    (i : Fin 4) :
    stepCoordinates (u + θ • v) x i = stepCoordinates u x i + θ • stepCoordinates v x i := by apply _root_.YangMills.SharedProofs.p44921 <;> assumption
private theorem stepCoordinates_zero (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable (finiteCells F)) x i = 0 := by
  unfold stepCoordinates
  split_ifs with h
  · exact toImaginary_zero
  · rfl
private theorem coordsAboveFrame_zero (dual : Bool) (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (x : F.Site F.depth) (i : Fin 4) :
    coordsAboveFrame dual a ρ m V 0 x i = stepFrame dual a ρ m (x, i) V := by
  unfold coordsAboveFrame
  rw [stepCoordinates_zero, add_zero]
private theorem chartCoordinates_step_add_smul (u v : StepVariable (finiteCells F)) (θ : ℝ) :
    chartCoordinates (stepCoordinates (u + θ • v)) (fun _ _ => 0) =
      chartCoordinates (stepCoordinates u) (fun _ _ => 0) +
        θ • chartCoordinates (stepCoordinates v) (fun _ _ => 0) := by apply _root_.YangMills.SharedProofs.p68589 <;> assumption
private theorem chartCoordinates_step_zero :
    chartCoordinates (stepCoordinates (0 : StepVariable (finiteCells F)))
      (fun _ _ => (0 : imaginaryQuaternions)) = 0 := by apply _root_.YangMills.SharedProofs.p69363 <;> assumption
private def stepChartCLM (F : BlockFrame) :
    StepVariable (finiteCells F) →L[ℝ] (Fin (chartDimension F) → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun η => chartCoordinates (stepCoordinates η) (fun _ _ => 0)
      map_add' := fun u v => by simpa using chartCoordinates_step_add_smul u v 1
      map_smul' := fun r v => by
        have h := chartCoordinates_step_add_smul 0 v r
        rw [chartCoordinates_step_zero, zero_add, zero_add] at h
        exact h }
private theorem stepChartCLM_apply (η : StepVariable (finiteCells F)) :
    stepChartCLM F η = chartCoordinates (stepCoordinates η) (fun _ _ => 0) := rfl
private theorem chartedEnergyAtMinimizer_leftTranslate (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (a ρ : ℝ) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) (η : StepVariable (finiteCells F)) :
    ReferenceDensity.chartedEnergyAtMinimizer a ρ (leftTranslate (bondSpread c X τ) V) η =
      chartRestriction a (fun x i => stepFrame true a ρ 0 (x, i) V) V (chartDirections F)
        (FrameCurves.frameCurve true a ρ 0 V c X τ + stepChartCLM F η) := by
  have h := (hCE F a (fun x i => stepFrame true a ρ 0 (x, i) V)
    (fun x i => (stepFrame true a ρ 0 (x, i) (leftTranslate (bondSpread c X τ) V) - stepFrame true a ρ 0 (x, i) V) +
      (1 : ℝ) • stepCoordinates η x i) V
    (fun y i => bondSpread c X τ y i + (1 : ℝ) • (0 : imaginaryQuaternions)) hL hs).1
  rw [FrameCurves.chartCoordinates_add_smul, one_smul] at h
  have e1 : (fun y i => bondSpread c X τ y i + (1 : ℝ) • (0 : imaginaryQuaternions)) = bondSpread c X τ := by
    funext y i
    simp
  rw [e1] at h
  have e2 : chartCoordinates
      (fun x i => stepFrame true a ρ 0 (x, i) (leftTranslate (bondSpread c X τ) V) - stepFrame true a ρ 0 (x, i) V)
      (bondSpread c X τ) = FrameCurves.frameCurve true a ρ 0 V c X τ := rfl
  rw [stepChartCLM_apply, ← e2]
  refine Eq.trans ?_ h.symm
  show chartedEnergy a (coordsAboveFrame true a ρ 0 (leftTranslate (bondSpread c X τ) V) η)
    (leftTranslate (bondSpread c X τ) V) = _
  congr 1
  funext x i
  simp only [coordsAboveFrame, one_smul, stepFrame]
  abel
end Chart
section Step
variable {F : BlockFrame}
private theorem mem_chordBonds_of_not_tree (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {x : F.Site F.depth} {i : Fin 4}
    (h : ¬ IsAxialTreeBond (x, i)) : (x, i) ∈ chordBonds (finiteCells F) := by apply _root_.YangMills.SharedProofs.p125121 <;> assumption
private theorem isSmallCurvature_of_isCold (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j ≤ F.top) {s : ℝ} {X : F.GaugeField j}
    (h : IsCold (finiteCells F) j s X) : IsSmallCurvature s X := by apply _root_.YangMills.SharedProofs.p16091 <;> assumption
private theorem zero_mem_centredCube {M : ℕ} (hM : 1 ≤ M) : (0 : Fin 4 → ℤ) ∈ centredCube M := by apply _root_.YangMills.Construction.TorusContours.zero_mem_centredCube <;> assumption
private theorem analytic_stepDensity_of_small (hK : ChartEnergyKernelBound) (hCE : ChartedEnergyInCoordinates)
    (hOL : MinimizingChartUnique) {a : ℝ} {L : ℕ} {c : ColdChainParameters} (ha : 1 ≤ a) (hL : Odd L)
    (hL40 : 2 ^ 40 ≤ L) (hc : c.Admissible a L) (hF : IsBlockTorus L F) {s : ℝ} (hs : 0 < s) (hs0 : s ≤ c.s₀)
    {V : F.GaugeField F.top} (hV : IsSmallCurvature s V) (Y : F.Cell) :
    IsBondAnalyticAt (ReferenceDensity.stepDensity a c.ρA c.lam Y) V := by
  obtain ⟨⟨-, hρ1, hs₀, -, -, -, hC1, -⟩, hcl⟩ := hc.classical
  obtain ⟨-, -, hlam, -, -, -, -⟩ := hc.positivity
  obtain ⟨-, -, h16, -, h2C, h64⟩ := hc.inequalities
  have hodd : Odd F.blockSide := by
    rw [hF.1]
    exact hL
  obtain ⟨n, hn, hside⟩ := hF.2
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside]
    omega
  have hs1 : ∀ i, 0 < F.extent i := fun i => by
    rw [hside]
    omega
  have hsσ : s ≤ c.σA := by linarith
  have hcla := hc.estimates F s V hF hs hsσ hV
  obtain ⟨hleast, hsmall, -, -⟩ := hcl F s V hF hs hs0 hV
  have hone := (hOL F a c.ρA (c.N 0) s V _ hodd hs2 hρ1 hcla.minimizer hleast).2
  have hCC : c.C * s ≤ c.C * c.s₀ := mul_le_mul_of_nonneg_left hs0 (by linarith)
  have hCs : c.C * s ≤ 1 / 32 := by linarith
  have hframe : ∀ b : F.Site F.depth × Fin 4, stepFrame true a c.ρA 0 b V = torusCoordinate a c.ρA b V :=
    fun b => by
      simp [stepFrame, torusCoordinate]
  have hfun : (fun x i => stepFrame true a c.ρA 0 (x, i) V) = minimizingCoordinates a (finiteCells F) V c.ρA := by
    funext x i
    simp [stepFrame, minimizingBondCoordinate]
  have hfa : ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (stepFrame true a c.ρA 0 b) V := fun b hb => by
    have e : stepFrame true a c.ρA 0 b = minimizingBondCoordinate a c.ρA (finiteCells F) b := by
      funext V'
      simp [stepFrame]
    rw [e]
    exact (hcla.coordinates b hb).1
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := lt_of_lt_of_le (by positivity) hL40
    exact_mod_cast this
  have hpt : IsAdmissibleChartPoint L c.σA (fun x i => stepFrame true a c.ρA 0 (x, i) V) V := by
    refine ⟨fun b hb => ?_, fun p hp => ?_⟩
    · have h1 := hsmall.1 b hb
      rw [← hframe] at h1
      refine h1.trans ?_
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    · rw [hfun]
      have h1 : IsSmallCurvature (s / 8) (chartedField (minimizingCoordinates a (finiteCells F) V c.ρA) V) :=
        isSmallCurvature_of_isCold hodd hs1 (Nat.le_succ _) hone
      exact (h1 p hp).trans_le (by linarith)
  obtain ⟨Ck, -, hker⟩ := hK a L c ha hL hL40 hc
  have hf : AnalyticAt ℝ (chartRestriction a (fun x i => stepFrame true a c.ρA 0 (x, i) V) V
      (chartDirections F)) 0 :=
    (hker F _ V hF hpt _ (chartDirections F)).1
  intro k e X
  change AnalyticAt ℝ (fun τ : Fin k → ℝ =>
    ReferenceDensity.stepDensity a c.ρA c.lam Y (leftTranslate (bondSpread e X τ) V)) 0
  have hQa := FrameCurves.analyticAt_frameCurve hfa e X
  have hQ0 := FrameCurves.frameCurve_zero true a c.ρA 0 V e X
  have hV0 : leftTranslate (bondSpread e X 0) V = V := FrameCurves.leftTranslate_bondSpread_zero e X V
  have hen : ∀ τ, ReferenceDensity.chartedEnergyAtMinimizer a c.ρA (leftTranslate (bondSpread e X τ) V) =
      fun η => chartRestriction a (fun x i => stepFrame true a c.ρA 0 (x, i) V) V (chartDirections F)
        (FrameCurves.frameCurve true a c.ρA 0 V e X τ + stepChartCLM F η) := fun τ =>
    funext (chartedEnergyAtMinimizer_leftTranslate hCE hodd hs2 a c.ρA V e X τ)
  have hE : AnalyticAt ℝ (ReferenceDensity.chartedEnergyAtMinimizer a c.ρA V) 0 := by
    have h0 := hen 0
    rw [hV0, hQ0] at h0
    rw [h0]
    have h1 : AnalyticAt ℝ (fun η : StepVariable (finiteCells F) =>
        (0 : Fin (chartDimension F) → ℝ) + stepChartCLM F η) 0 :=
      analyticAt_const.add ((stepChartCLM F).analyticAt 0)
    exact AnalyticAt.comp_of_eq hf h1 (by simp)
  have hfl : ∀ u : StepVariable (finiteCells F), c.lam * ∑ b, ‖u b‖ ^ 2 ≤
      deriv (deriv fun r : ℝ => ReferenceDensity.chartedEnergyAtMinimizer a c.ρA V (r • u)) 0 := by
    intro u
    have h := hcla.hessian (minimizingCoordinates a (finiteCells F) V c.ρA) (stepCoordinates u) hleast.1
      (fun b hb => dif_neg hb) hleast.2.1 (fun p hp => (hone p hp).trans_le (by linarith))
    have e1 : ∑ b, ‖u b‖ ^ 2 = ∑ b ∈ chordBonds (finiteCells F), ‖stepCoordinates u b.1 b.2‖ ^ 2 := by
      rw [← Finset.sum_coe_sort (chordBonds (finiteCells F))]
      refine Finset.sum_congr rfl fun b _ => ?_
      have e2 : stepCoordinates u b.1.1 b.1.2 = toImaginary (u b) := dif_pos b.2
      rw [e2, norm_toImaginary]
    have e3 : (fun r : ℝ => ReferenceDensity.chartedEnergyAtMinimizer a c.ρA V (r • u)) =
        fun τ : ℝ => blockEnergy a (finiteCells F) F.depth
          (chartedField (fun x i => minimizingCoordinates a (finiteCells F) V c.ρA x i +
            τ • stepCoordinates u x i) V) V := by
      funext r
      show chartedEnergy a (coordsAboveFrame true a c.ρA 0 V (r • u)) V = _
      unfold chartedEnergy
      congr 2
      funext x i
      have h2 := stepCoordinates_add_smul 0 u r x i
      rw [stepCoordinates_zero, zero_add, zero_add] at h2
      simp only [coordsAboveFrame, h2]
      rw [← congrFun (congrFun hfun x) i]
    rw [e1, e3]
    exact h
  have hU : ∀ s' ∈ Set.Icc (0 : ℝ) 1, IsUnit (s' • ReferenceDensity.chartedHessian a c.ρA V 0 +
      (1 - s') • c.lam • (1 : Matrix (ReferenceDensity.ChartCoord F) (ReferenceDensity.ChartCoord F) ℝ)) :=
    fun s' h' => isUnit_of_hessian_floor hE hlam hfl _ (fun i j => rfl) s' h'
  have hQt : Filter.Tendsto (FrameCurves.frameCurve true a c.ρA 0 V e X) (𝓝 0) (𝓝 0) := by
    have h := hQa.continuousAt.tendsto
    rwa [hQ0] at h
  have hfev := hQt.eventually hf.eventually_analyticAt
  obtain ⟨M, hMd⟩ : ∃ M : (Fin k → ℝ) → Matrix (ReferenceDensity.ChartCoord F) (ReferenceDensity.ChartCoord F) ℝ,
      M = fun τ i j =>
        secondDerivAlong (chartRestriction a (fun x i => stepFrame true a c.ρA 0 (x, i) V) V (chartDirections F))
          (stepChartCLM F) (basisField i) (basisField j) (FrameCurves.frameCurve true a c.ρA 0 V e X τ) :=
    ⟨_, rfl⟩
  have hent : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ),
      ReferenceDensity.chartedHessian a c.ρA (leftTranslate (bondSpread e X τ) V) 0 = M τ := by
    filter_upwards [hfev] with τ hτ
    refine Matrix.ext fun i j => ?_
    rw [hMd]
    show fderiv ℝ (fun ζ => fderiv ℝ (ReferenceDensity.chartedEnergyAtMinimizer a c.ρA
      (leftTranslate (bondSpread e X τ) V)) ζ (basisField i)) 0 (basisField j) = _
    rw [hen τ]
    exact second_fderiv_comp_add_clm (stepChartCLM F) hτ _ _
  have hM0 : M 0 = ReferenceDensity.chartedHessian a c.ρA V 0 := by
    have h := hent.self_of_nhds
    rw [hV0] at h
    exact h.symm
  have hMe : ∀ i j, AnalyticAt ℝ (fun τ => M τ i j) 0 := fun i j => by
    rw [hMd]
    exact AnalyticAt.comp_of_eq (analyticAt_secondDerivAlong (stepChartCLM F) hf _ _) hQa hQ0
  have hA := analyticAt_integral_diag_resolvent M 0 c.lam
    (fun i : ReferenceDensity.ChartCoord F => enclosingCell i.1.1.1 = Y) hMe (by
      rw [hM0]
      exact hU)
  have hA' : AnalyticAt ℝ (fun τ : Fin k → ℝ => ∫ s' in (0 : ℝ)..1,
      ReferenceDensity.hessianCellShare a c.ρA c.lam Y (leftTranslate (bondSpread e X τ) V) s') 0 := by
    refine hA.congr ?_
    filter_upwards [hent] with τ hτ
    unfold ReferenceDensity.hessianCellShare
    rw [hτ]
  have hfr : ∀ b ∈ chordBonds (finiteCells F),
      AnalyticAt ℝ (fun τ : Fin k → ℝ => stepFrame true a c.ρA 0 b (leftTranslate (bondSpread e X τ) V)) 0 :=
    fun b hb => hfa b hb k e X
  have hX : ∀ x i, AnalyticAt ℝ (fun τ : Fin k → ℝ =>
      ((fieldAboveFrame true a c.ρA 0 (leftTranslate (bondSpread e X τ) V) 0 x i : UnitQuaternion) : ℍ[ℝ])) 0 := by
    intro x i
    by_cases hcr : IsCrossingBond (x, i)
    · have ht : ¬ IsAxialTreeBond (x, i) := fun h => h.1 hcr
      have e1 : (fun τ : Fin k → ℝ =>
          ((fieldAboveFrame true a c.ρA 0 (leftTranslate (bondSpread e X τ) V) 0 x i : UnitQuaternion) : ℍ[ℝ])) =
          fun τ => ((expUnit (stepFrame true a c.ρA 0 (x, i) (leftTranslate (bondSpread e X τ) V)) :
              UnitQuaternion) : ℍ[ℝ]) *
            (((expUnit (bondSpread e X τ (enclosingCell x) i) : UnitQuaternion) : ℍ[ℝ]) *
              ((V (enclosingCell x) i : UnitQuaternion) : ℍ[ℝ])) := by
        funext τ
        simp only [fieldAboveFrame, chartedField, if_pos hcr, coordsAboveFrame_zero]
        rfl
      rw [e1]
      exact (analyticAt_expUnit (hfr _ (mem_chordBonds_of_not_tree hodd hs1 ht))).mul
        ((analyticAt_expUnit (FrameCurves.analyticAt_bondSpread e X _ _)).mul analyticAt_const)
    · by_cases ht : IsAxialTreeBond (x, i)
      · have e1 : (fun τ : Fin k → ℝ =>
            ((fieldAboveFrame true a c.ρA 0 (leftTranslate (bondSpread e X τ) V) 0 x i : UnitQuaternion) : ℍ[ℝ])) =
            fun _ => ((1 : UnitQuaternion) : ℍ[ℝ]) := by
          funext τ
          simp only [fieldAboveFrame, chartedField, if_neg hcr, if_pos ht]
        rw [e1]
        exact analyticAt_const
      · have e1 : (fun τ : Fin k → ℝ =>
            ((fieldAboveFrame true a c.ρA 0 (leftTranslate (bondSpread e X τ) V) 0 x i : UnitQuaternion) : ℍ[ℝ])) =
            fun τ => ((expUnit (stepFrame true a c.ρA 0 (x, i) (leftTranslate (bondSpread e X τ) V)) :
              UnitQuaternion) : ℍ[ℝ]) := by
          funext τ
          simp only [fieldAboveFrame, chartedField, if_neg hcr, if_neg ht, coordsAboveFrame_zero]
        rw [e1]
        exact analyticAt_expUnit (hfr _ (mem_chordBonds_of_not_tree hodd hs1 ht))
  have hB : AnalyticAt ℝ (fun τ : Fin k → ℝ =>
      ∑ c' ∈ (innerBonds (finiteCells F) F.top).filter (fun c' => c'.1 = Y),
        Real.log ‖BlockAverages.contourAverage (fieldAboveFrame true a c.ρA 0 (leftTranslate (bondSpread e X τ) V) 0) c'‖) 0 := by
    refine Finset.analyticAt_fun_sum _ fun c' _ =>
      analyticAt_log_norm (analyticAt_contourAverage hX c') ?_
    rw [hV0]
    have e3 : fieldAboveFrame true a c.ρA 0 V 0 = torusMinimizingField a c.ρA V := by
      show chartedField (coordsAboveFrame true a c.ρA 0 V 0) V =
        chartedField (minimizingCoordinates a (finiteCells F) V c.ρA) V
      congr 1
      funext x i
      rw [coordsAboveFrame_zero]
      exact congrFun (congrFun hfun x) i
    rw [e3]
    have h1 := ((hsmall.2 c' 0 1 (zero_mem_centredCube hodd.pos)).2)
    intro h0
    rw [h0, norm_zero] at h1
    linarith
  have hH : AnalyticAt ℝ (fun τ : Fin k → ℝ => ∑ b : ↥(chordBonds (finiteCells F)),
      if enclosingCell b.1.1 = Y then
        haarLogRatio (coordsAboveFrame true a c.ρA 0 (leftTranslate (bondSpread e X τ) V) 0 b.1.1 b.1.2)
      else 0) 0 := by
    refine Finset.analyticAt_fun_sum _ fun b _ => ?_
    by_cases hY : enclosingCell b.1.1 = Y
    · simp only [if_pos hY]
      have hw : AnalyticAt ℝ (fun τ : Fin k → ℝ =>
          coordsAboveFrame true a c.ρA 0 (leftTranslate (bondSpread e X τ) V) 0 b.1.1 b.1.2) 0 :=
        (hfr b.1 b.2).congr (Filter.Eventually.of_forall fun τ => (coordsAboveFrame_zero _ _ _ _ _ _ _).symm)
      refine analyticAt_haarLogRatio hw ?_
      show ‖coordsAboveFrame true a c.ρA 0 (leftTranslate (bondSpread e X 0) V) 0 b.1.1 b.1.2‖ < Real.pi
      rw [hV0, coordsAboveFrame_zero]
      have h1 := hsmall.1 b.1 b.2
      rw [← hframe] at h1
      have := Real.pi_gt_three
      exact lt_of_le_of_lt (h1.trans hCs) (by linarith)
    · simp only [if_neg hY]
      exact analyticAt_const
  unfold ReferenceDensity.stepDensity
  exact ((analyticAt_const.mul hA').add (analyticAt_const.mul hB)).add hH
end Step
end ColdStepAtMirrorFrames.StepDensity
namespace TorusLumps
open ColdStepAtMirrorFrames ColdStepAtMirrorFrames.StepDensity
theorem stepDensityAnalytic_holds (hK : ChartEnergyKernelBound)
    (hCE : ChartedEnergyInCoordinates) (hOL : MinimizingChartUnique) :
    stepDensityAnalyticStatement := by
  intro a ha
  refine ⟨2 ^ 40, fun L hL hL40 c hc => ?_⟩
  have hs₀ : 0 < c.s₀ := hc.classical.1.2.2.1
  refine ⟨0, fun Ct _ => ?_⟩
  refine ⟨1, one_pos, fun κ _ _ => ?_⟩
  refine ⟨1, one_pos, fun η₃ _ _ _ => ?_⟩
  refine ⟨0, fun nss _ => ?_⟩
  refine ⟨c.s₀, hs₀, fun σ hσ hσ₀ p _ => ?_⟩
  refine ⟨0, fun Cs _ E _ => ?_⟩
  refine ⟨64, fun n₀ hn₀ => ?_⟩
  refine ⟨0, fun CE _ => ?_⟩
  refine ⟨0, fun y₁ _ => ?_⟩
  intro _ _ ℓ _ _ t n _ hn y W hW k b X
  have hp : ∀ i, (TorusFields.torusFrame L t n).period (TorusFields.torusFrame L t n).top i = n :=
    fun i => TopLevelSites.period_top i
  have : ∀ i, NeZero ((TorusFields.torusFrame L t n).period (TorusFields.torusFrame L t n).top i) := fun i => ⟨by
    rw [hp i]
    exact NeZero.ne n⟩
  have hF : IsBlockTorus L (TorusFields.torusFrame L t n) := ⟨rfl, n, le_trans hn₀ hn, fun _ => rfl⟩
  have hcold : IsSmallCurvature (F := TorusFields.torusFrame L t n) σ
      (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top W) := by
    rintro ⟨x, μ, ν⟩ hlt
    rw [TopLevelSites.plaquetteDefect_readAtLevel_eq hp]
    exact hW _ μ ν hlt
  have h := analytic_stepDensity_of_small hK hCE hOL ha hL hL40 hc hF hσ hσ₀ hcold
    (siteOfCoords (TorusFields.torusFrame L t n).top fun k => ((y k).cast : ℤ)) k
    (fun l => (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top
      (b l).1, (b l).2)) X
  refine h.congr (Filter.Eventually.of_forall fun τ => ?_)
  show _ = ReferenceDensity.stepDensity a c.ρA c.lam _
    (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top
      (TorusFields.perturb b X τ W))
  rw [TorusChain.readAtLevel_perturb hp]
end TorusLumps
end YangMills.Construction
end
