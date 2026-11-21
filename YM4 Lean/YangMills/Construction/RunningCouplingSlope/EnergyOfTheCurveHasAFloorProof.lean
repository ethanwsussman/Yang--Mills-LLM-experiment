import YangMills.Construction.RunningCouplingSlope.ValueOfTheDensityOfTheStepOnTwoToriAtParametersProof
import YangMills.Construction.HoleBesideASecondHole.EnergyInTheChart
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsAnalyticAtParametersProof
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.RunningCouplingSlope.ExponentOfAStepAlongACurve
import Mathlib
import YangMills.Construction.RunningCouplingSlope.EnergyOverTheCurveHasJets
import YangMills.Construction.RunningCouplingSlope.LeastActionIsWellAtTheTopProof
import YangMills.Construction.RunningCouplingSlope.LeastPointOfTheCurveHasJets
set_option autoImplicit false

noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames StepSettings RenormalizationStepParameters TorusFields TorusLumps
namespace RunningCouplingSlope
def ChartEnergyCriticalWithFloor : Prop :=
  ∀ P : ParameterAssignment, P.Admissible → ∀ k : ℕ,
    ∀ (y : ℝ) (S : StepSetup), P.floorMin ≤ y → S.OnParameters P y →
      ∀ (n : ℕ) [NeZero n] (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
        P.n₀ ≤ n → AreUnitVectors X →
        (∀ᶠ τ in 𝓝 (0 : Fin k → ℝ),
            fderiv ℝ (fun ζ => chartEnergyAlongCurve S n c X (τ, ζ)) 0 = 0) ∧
        ∀ ζ : StepVariable (finiteCells (torusFrame S.params.side S.depth n)),
          (∀ b, ‖ζ b‖ ≤ P.ballRadius) →
          ∀ u : StepVariable (finiteCells (torusFrame S.params.side S.depth n)),
            P.lam * ∑ b, ‖u b‖ ^ 2 ≤
              ColdStepAtMirrorFrames.secondDerivAlong (fun w => chartEnergyAlongCurve S n c X (0, w)) ζ u u
end RunningCouplingSlope
end YangMills.Construction
end

noncomputable section
open Filter
open scoped Topology Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields StepSettings RenormalizationStepParameters TorusLumps ReferenceDensity
namespace RunningCouplingSlope
namespace ChartEnergyFloorAux
section Calculus
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem deriv_deriv_line_eq_fderiv {Ψ : E → ℝ} {η : E} (u : E) (h : ContDiffAt ℝ (2 : ℕ) Ψ η) :
    deriv (deriv fun τ : ℝ => Ψ (η + τ • u)) 0 = fderiv ℝ (fun y => fderiv ℝ Ψ y u) η u := by apply _root_.YangMills.SharedProofs.p27006 <;> assumption
private theorem contDiffAt_slice {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {f : E × P → ℝ} {η : E} {p : P}
    (h : ContDiffAt ℝ (2 : ℕ) f (η, p)) : ContDiffAt ℝ (2 : ℕ) (fun ζ => f (ζ, p)) η :=
  ContDiffAt.comp η (g := f) (f := fun ζ => (ζ, p)) h (contDiffAt_id.prodMk contDiffAt_const)
private theorem secondDerivAlong_sub_const {ι : Type} [Fintype ι] [DecidableEq ι] (Ψ : BondField ι → ℝ) (a : ℝ)
    (η u v : BondField ι) : ColdStepAtMirrorFrames.secondDerivAlong (fun ζ => Ψ ζ - a) η u v =
      ColdStepAtMirrorFrames.secondDerivAlong Ψ η u v := by
  unfold ColdStepAtMirrorFrames.secondDerivAlong
  simp only [fderiv_sub_const]
end Calculus
section Chart
variable {F : BlockFrame}
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
private theorem toImaginary_imaginaryToEuclidean (v : imaginaryQuaternions) :
    toImaginary (imaginaryToEuclidean v) = v := by
  apply Subtype.ext
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
  · exact (show ((v : ℍ[ℝ])).re = 0 from v.2).symm
  · rfl
  · rfl
  · rfl
abbrev _root_.YangMills.SharedProofs.p66610 := @toImaginary_imaginaryToEuclidean
private theorem stepCoordinates_add_smul (η u : StepVariable (finiteCells F)) (s : ℝ) (x : F.Site F.depth)
    (i : Fin 4) :
    stepCoordinates (η + s • u) x i = stepCoordinates η x i + s • stepCoordinates u x i := by apply _root_.YangMills.SharedProofs.p44921 <;> assumption
private theorem stepCoordinates_of_not_mem {S : Finset F.Cell} (η : StepVariable S)
    {b : F.Site F.depth × Fin 4} (h : b ∉ chordBonds S) : stepCoordinates η b.1 b.2 = 0 := by
  simp only [stepCoordinates]
  rw [dif_neg h]
private theorem stepCoordinates_of_mem {S : Finset F.Cell} (η : StepVariable S) (b : ↥(chordBonds S)) :
    stepCoordinates η b.1.1 b.1.2 = toImaginary (η b) := by
  simp only [stepCoordinates]
  rw [dif_pos (show (b.1.1, b.1.2) ∈ chordBonds S from b.2)]
private theorem stepCoordinates_zero {S : Finset F.Cell} (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable S) x i = 0 := by apply _root_.YangMills.SharedProofs.p7539 <;> assumption
private theorem norm_stepCoordinates_le {S : Finset F.Cell} {e : ℝ} (he : 0 ≤ e) {η : StepVariable S}
    (hη : ∀ b, ‖η b‖ ≤ e) (x : F.Site F.depth) (i : Fin 4) : ‖(stepCoordinates η x i : ℍ[ℝ])‖ ≤ e := by
  by_cases h : (x, i) ∈ chordBonds S
  · have h1 := stepCoordinates_of_mem η ⟨(x, i), h⟩
    simp only at h1
    rw [h1]
    have h2 := norm_toImaginary (η ⟨(x, i), h⟩)
    exact (le_of_eq h2).trans (hη _)
  · have h1 := stepCoordinates_of_not_mem η h
    simp only at h1
    rw [h1]
    simpa using he
private theorem coordsAboveFrame_zero (a ρ : ℝ) (V : F.GaugeField F.top) :
    coordsAboveFrame true a ρ 0 V (0 : StepVariable (finiteCells F)) = minimizingCoordinates a (finiteCells F) V ρ := by apply _root_.YangMills.DeltaSharedProofs.p501121 <;> assumption
private theorem chartedEnergyAtMinimizer_zero_le {a ρ : ℝ} {V : F.GaugeField F.top}
    (h : ∃ w, IsMinimizingChart a (finiteCells F) V ρ w)
    (η : StepVariable (finiteCells F)) : chartedEnergyAtMinimizer a ρ V 0 ≤ chartedEnergyAtMinimizer a ρ V η := by
  unfold chartedEnergyAtMinimizer chartedEnergy
  rw [coordsAboveFrame_zero]
  unfold minimizingCoordinates
  rw [dif_pos h]
  exact h.choose_spec.2.2 _
private theorem coercive_secondDerivAlong (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    {a lam ρ σA r e : ℝ} {V : F.GaugeField F.top}
    (hr : 0 ≤ r) (hV : BlockAverages.IsCold (finiteCells F) F.top r V) (he0 : 0 ≤ e) (he : e ≤ 1 / 4)
    (heρ : e ≤ ρ) (hlt : r + 8 * e < σA) (hfl : HasCoerciveHessian a lam ρ σA (finiteCells F) V)
    (η u : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ ≤ e)
    (hΨ : ContDiffAt ℝ (2 : ℕ)
      (fun ζ : StepVariable (finiteCells F) => chartedEnergy a (stepCoordinates ζ) V) η) :
    lam * ∑ b, ‖u b‖ ^ 2 ≤
      ColdStepAtMirrorFrames.secondDerivAlong
        (fun ζ : StepVariable (finiteCells F) => chartedEnergy a (stepCoordinates ζ) V) η u u := by
  have h := hfl (stepCoordinates η) (stepCoordinates u) (fun b hb => stepCoordinates_of_not_mem η hb)
    (fun b hb => stepCoordinates_of_not_mem u hb)
    (fun b _ => (norm_stepCoordinates_le he0 hη b.1 b.2).trans heρ)
    (fun p hp => lt_of_le_of_lt (GaugeFixing.plaquetteDefect_chartedField_le hs hL (finiteCells F) V r e hr hV
      (stepCoordinates η) he (fun b _ => norm_stepCoordinates_le he0 hη b.1 b.2) p hp) hlt)
  have hfun : (fun τ : ℝ => blockEnergy a (finiteCells F) F.depth
      (chartedField (fun x i => stepCoordinates η x i + τ • stepCoordinates u x i) V) V) =
      fun τ : ℝ => (fun ζ : StepVariable (finiteCells F) => chartedEnergy a (stepCoordinates ζ) V) (η + τ • u) := by
    funext τ
    have : (fun x i => stepCoordinates η x i + τ • stepCoordinates u x i) = stepCoordinates (η + τ • u) := by
      funext x i
      rw [stepCoordinates_add_smul]
    rw [this]
    rfl
  rw [hfun, deriv_deriv_line_eq_fderiv u hΨ] at h
  have hsum : ∑ b ∈ chordBonds (finiteCells F), ‖stepCoordinates u b.1 b.2‖ ^ 2 = ∑ b, ‖u b‖ ^ 2 := by
    rw [← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [stepCoordinates_of_mem, norm_toImaginary]
  rw [hsum] at h
  exact h
end Chart
section Perturbations
variable {k n : ℕ}
private theorem continuous_perturb_trivialField (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (x : TorusSite n) (i : Fin 4) :
    Continuous fun τ : Fin k → ℝ => ((perturb c X τ (trivialField n) x i : UnitQuaternion) : ℍ[ℝ]) := by
  let +nondep : NormedAlgebra ℚ ℍ[ℝ] := .restrictScalars ℚ ℝ ℍ[ℝ]
  have hs : Continuous fun τ : Fin k → ℝ =>
      (∑ l, if c l = (x, i) then τ l • X l else 0 : imaginaryQuaternions) := by
    refine continuous_finsetSum _ fun l _ => ?_
    split_ifs
    · exact (continuous_apply l).smul continuous_const
    · exact continuous_const
  have hq : Continuous fun τ : Fin k → ℝ =>
      ((∑ l, if c l = (x, i) then τ l • X l else 0 : imaginaryQuaternions) : ℍ[ℝ]) :=
    continuous_subtype_val.comp hs
  have he : Continuous fun τ : Fin k → ℝ =>
      (NormedSpace.exp ((∑ l, if c l = (x, i) then τ l • X l else 0 : imaginaryQuaternions) : ℍ[ℝ]) : ℍ[ℝ]) :=
    NormedSpace.exp_continuous.comp hq
  simpa [perturb, trivialField, expUnit] using he
private theorem continuous_inv_unit {W : (Fin k → ℝ) → UnitQuaternion}
    (h : Continuous fun τ => ((W τ : UnitQuaternion) : ℍ[ℝ])) :
    Continuous fun τ => (((W τ)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  have e : ∀ τ, (((W τ)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star ((W τ : UnitQuaternion) : ℍ[ℝ]) := by
    intro τ
    rw [← Unitary.star_eq_inv, Unitary.coe_star]
  simp only [e]
  exact continuous_star.comp h
private theorem eventually_isCold_perturb [NeZero n] (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    {s : ℝ} (hs : 0 < s) :
    ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), TorusFields.IsCold s (perturb c X τ (trivialField n)) := by
  have hc : ∀ (x : TorusSite n) (μ ν : Fin 4),
      Continuous fun τ : Fin k → ℝ => curvature (perturb c X τ (trivialField n)) x μ ν := by
    intro x μ ν
    simp only [curvature, holonomy, Submonoid.coe_mul]
    exact ((((continuous_perturb_trivialField c X x μ).mul (continuous_perturb_trivialField c X _ ν)).mul
      (continuous_inv_unit (continuous_perturb_trivialField c X _ μ))).mul
      (continuous_inv_unit (continuous_perturb_trivialField c X x ν))).sub continuous_const |>.norm
  have hall : ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), ∀ p : TorusSite n × Fin 4 × Fin 4,
      curvature (perturb c X τ (trivialField n)) p.1 p.2.1 p.2.2 < s := by
    rw [eventually_all]
    intro p
    have h0 : curvature (perturb c X (0 : Fin k → ℝ) (trivialField n)) p.1 p.2.1 p.2.2 < s := by
      rw [TorusFields.perturb_zero]
      simpa [curvature, holonomy, trivialField] using hs
    exact (hc p.1 p.2.1 p.2.2).continuousAt.eventually (gt_mem_nhds h0)
  filter_upwards [hall] with τ h x μ ν _
  exact h (x, μ, ν)
end Perturbations
section Curve
variable {k : ℕ} (R : StepSetup) (n : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
private theorem coordsAboveFrame_of_minimizer_zero (h : minimizerCoordinatesAlong R n c X 0 = 0)
    (ζ : StepVariable (finiteCells (torusFrame R.params.side R.depth n))) :
    coordsAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c X 0) ζ = stepCoordinates ζ := by
  funext x i
  have hz : minimizingBondCoordinate R.params.coupling R.anchorRadius
      (finiteCells (torusFrame R.params.side R.depth n)) (x, i) (perturbedTop R n c X 0) = 0 := by
    by_cases hb : (x, i) ∈ chordBonds (finiteCells (torusFrame R.params.side R.depth n))
    · have h1 := congrFun h ⟨(x, i), hb⟩
      have h2 : imaginaryToEuclidean (minimizingBondCoordinate R.params.coupling R.anchorRadius
          (finiteCells (torusFrame R.params.side R.depth n)) (x, i) (perturbedTop R n c X 0)) = 0 := h1
      have h3 := toImaginary_imaginaryToEuclidean (minimizingBondCoordinate R.params.coupling R.anchorRadius
          (finiteCells (torusFrame R.params.side R.depth n)) (x, i) (perturbedTop R n c X 0))
      rw [h2] at h3
      rw [← h3]
      apply Subtype.ext
      refine Quaternion.ext _ _ ?_ ?_ ?_ ?_ <;> simp [toImaginary]
    · unfold minimizingBondCoordinate minimizingCoordinates
      split_ifs with he
      · exact he.choose_spec.1 (x, i) hb
      · rfl
  simp only [coordsAboveFrame, ColdStepAtMirrorFrames.stepFrame, if_true, hz, zero_add]
private theorem coercive_at_trivialField (T : ParameterAssignment) (hT : T.Admissible) {y : ℝ} (hR : R.OnParameters T y)
    (h64 : 64 ≤ n) (hΓ : minimizerCoordinatesAlong R n c X 0 = 0) (hN0 : 0 < T.N 0)
    (hflat : ∀ s : ℝ, 0 < s →
      BlockAverages.IsCold (finiteCells (torusFrame R.params.side R.depth n))
        (torusFrame R.params.side R.depth n).top s (perturbedTop R n c X 0))
    (hfl : HasCoerciveHessian R.params.coupling T.lam R.anchorRadius T.σA
      (finiteCells (torusFrame R.params.side R.depth n)) (perturbedTop R n c X 0))
    (η u : StepVariable (finiteCells (torusFrame R.params.side R.depth n))) (hη : ∀ b, ‖η b‖ ≤ T.ballRadius)
    (hC : ContDiffAt ℝ (2 : ℕ) (chartedEnergyAlong R n c X) (η, 0)) :
    T.lam * ∑ b, ‖u b‖ ^ 2 ≤
      ColdStepAtMirrorFrames.secondDerivAlong (fun ζ => chartEnergyAlongCurve R n c X (0, ζ)) η u u := by
  have hodd : Odd (torusFrame R.params.side R.depth n).blockSide := by
    show Odd R.params.side
    rw [hR.params_eq]
    exact hT.L_odd
  have hσ : 0 < T.threshold := hT.σ_pos
  have hρe : T.ballRadius = T.threshold / 64 := rfl
  have hρ0 : 0 ≤ T.ballRadius := by
    rw [hρe]
    positivity
  have hρA : T.ballRadius ≤ R.anchorRadius := by
    rw [hR.anchorRadius_eq]
    have h3 := hT.ρ_le
    have h4 : 0 < T.N 0 * T.threshold := mul_pos hN0 hσ
    linarith
  have hρ4 : T.ballRadius ≤ 1 / 4 := by
    rw [hρe]
    linarith [hT.σ_one]
  have hlt : T.threshold / 8 + 8 * T.ballRadius < T.σA := by
    rw [hρe]
    linarith [hT.σ_le]
  have hside : ∀ i, 2 ≤ (torusFrame R.params.side R.depth n).extent i := fun _ => (show 2 ≤ n by omega)
  have hfloor := coercive_secondDerivAlong hside hodd (by positivity : (0 : ℝ) ≤ T.threshold / 8)
    (hflat _ (by positivity)) hρ0 hρ4 hρA hlt hfl η u hη (contDiffAt_slice hC)
  have hEq : (fun ζ => chartEnergyAlongCurve R n c X (0, ζ)) =
      fun ζ : StepVariable (finiteCells (torusFrame R.params.side R.depth n)) =>
        chartedEnergy R.params.coupling (stepCoordinates ζ) (perturbedTop R n c X 0) -
          chartedEnergyAtMinimizer R.params.coupling R.anchorRadius (perturbedTop R n c X 0) 0 := by
    funext ζ
    unfold chartEnergyAlongCurve
    unfold chartedEnergyAtMinimizer
    simp only [coordsAboveFrame_of_minimizer_zero R n c X hΓ]
  rw [hEq, secondDerivAlong_sub_const
    (fun ζ : StepVariable (finiteCells (torusFrame R.params.side R.depth n)) =>
      chartedEnergy R.params.coupling (stepCoordinates ζ) (perturbedTop R n c X 0))]
  exact hfloor
end Curve
end ChartEnergyFloorAux
open ChartEnergyFloorAux in
theorem chartEnergyCriticalWithFloor_of_jets (h1 : MinimizerCoordinatesJetBound)
    (h2 : ChartedEnergyJetBounds) : ChartEnergyCriticalWithFloor := by
  intro T hT k y R hy hR n _ c X hn hX
  obtain ⟨C₁, q₁, -, -, g₁⟩ := h1 T hT k
  obtain ⟨C₂, q₂, -, -, g₂⟩ := h2 T hT k
  have hl := hR.params_eq
  have eA : R.params.coupling = T.coupling := by rw [hl]; rfl
  have eL : R.params.side = T.side := by rw [hl]; rfl
  have eR : R.anchorRadius = T.ρA := hR.anchorRadius_eq
  have h64 : 64 ≤ n := le_trans (by have := hT.n₀_ge; omega) hn
  have hc : ColdChain.ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [eA, eL, eR]
    exact hT.chain
  obtain ⟨-, -, -, -, -, hσA, -, hN, hmain⟩ := hc
  have hside : ∀ i, (torusFrame R.params.side R.depth n).extent i = n := fun _ => rfl
  have hreg : IsOrthantRegular (finiteCells (torusFrame R.params.side R.depth n)) 1024 :=
    TopLevelSites.isOrthantRegular_finiteCells (fun i => by rw [hside]; omega) 1024
  have hch := fun (V : (torusFrame R.params.side R.depth n).GaugeField (torusFrame R.params.side R.depth n).top)
      (hV : BlockAverages.IsCold (finiteCells (torusFrame R.params.side R.depth n))
        (torusFrame R.params.side R.depth n).top T.σA V) =>
    hmain (torusFrame R.params.side R.depth n) 1024 (finiteCells _) rfl (Or.inr fun _ => h64) le_rfl hreg T.σA V
      hσA le_rfl hV
  constructor
  · filter_upwards [eventually_isCold_perturb c X hσA] with τ hτ
    have hV : BlockAverages.IsCold (finiteCells (torusFrame R.params.side R.depth n))
        (torusFrame R.params.side R.depth n).top T.σA (perturbedTop R n c X τ) :=
      TopLevelSites.isCold_readAtLevel hside hτ
    obtain ⟨⟨w, hw, -⟩, -⟩ := hch _ hV
    have hex : ∃ w, IsMinimizingChart R.params.coupling (finiteCells (torusFrame R.params.side R.depth n))
        (perturbedTop R n c X τ) R.anchorRadius w :=
      ⟨w, hw.1, fun b hb => (hw.2.1 b hb).trans (min_le_left _ _), hw.2.2⟩
    have hmin : IsLocalMin (fun η => chartEnergyAlongCurve R n c X (τ, η)) 0 := Eventually.of_forall fun η => by
      have := chartedEnergyAtMinimizer_zero_le hex η
      simp only [chartEnergyAlongCurve, sub_self]
      linarith
    exact hmin.fderiv_eq_zero
  · intro η hη u
    have e0 : perturbedTop R n c X 0 =
        readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top (trivialField n) := by
      unfold perturbedTop
      rw [TorusFields.perturb_zero]
    have hflat : ∀ s : ℝ, 0 < s →
        BlockAverages.IsCold (finiteCells (torusFrame R.params.side R.depth n))
          (torusFrame R.params.side R.depth n).top s (perturbedTop R n c X 0) := by
      intro s hs
      rw [e0]
      refine TopLevelSites.isCold_readAtLevel hside ?_
      intro x μ ν _
      simpa [curvature, holonomy, trivialField] using hs
    exact coercive_at_trivialField R n c X T hT hR h64 (g₁ y R hy hR n c X hn hX).1 (hN 0) hflat
      (hch _ (hflat T.σA hσA)).2.1 η u hη ((g₂ y R hy hR n c X hn hX η hη).1.of_le (by norm_num))
end RunningCouplingSlope
end YangMills.Construction
end
