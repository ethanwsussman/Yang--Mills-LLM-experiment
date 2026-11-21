import YangMills.Construction.LawByMomentsOfTheFlow.RecursionOfTheClassicalFormsProof
import YangMills.Construction.RunningCouplingSlope.TangentsOfTheLeastFieldProof
import YangMills.Construction.ClusterExpansionOfAStep.ColdAlongAMove
import YangMills.Construction.ColdStepAtMirrorFrames.FlatResponsesAreScalar
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAgainstTheLeastField
import YangMills.Construction.ColdStepAtMirrorFrames.TreeResponseOfTheLeastCoordinatesProof
import YangMills.Construction.LawByMomentsOfTheFlow.ResponseOfTheFrameFieldAtOne
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheParts
import YangMills.Construction.ResponseInTheExpansion.FieldsOfOneColour
import YangMills.Construction.ResponseInTheExpansion.SecondDerivativesAtZero
import YangMills.Construction.RunningCouplingSlope.LeastActionIsWellAtTheTopProof
import YangMills.Construction.SummableBoundsOfTheFlow.FloorsOfTheFrames
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion Topology
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps TorusCharts TopLevelSites TorusFrame StepCosts BlockAverages ColdStepAtMirrorFrames
  WeightedResponses ResponseInTheExpansion ResponseInTheExpansion.SingleColourFields SecondOrder Interpolation TwoLevelMixtures
namespace FrameFieldAtIdentity
instance completeSpace_imaginaryQuaternions : CompleteSpace imaginaryQuaternions :=
  FiniteDimensional.complete ℝ imaginaryQuaternions
section Angles
variable {m : ℕ}
private def angleRead {E : Type} (G : TorusField m → E) (θ : TorusBond m → ℝ) : E := G (expOfColourForm 1 θ)
private theorem perturb_all_eq [NeZero m] (e : TorusBond m ≃ Fin (Fintype.card (TorusBond m)))
    (σ : Fin (Fintype.card (TorusBond m)) → ℝ) :
    perturb e.symm (fun _ => unitGenerator) σ (trivialField m) = expOfColourForm 1 (fun b => σ (e b)) := by
  funext x i
  show expUnit (∑ l, if e.symm l = (x, i) then σ l • unitGenerator else 0) * 1 =
    expUnit ((1 * σ (e (x, i))) • unitGenerator)
  rw [mul_one, one_mul]
  congr 1
  rw [Finset.sum_eq_single (e (x, i))]
  · simp
  · intro l _ hl
    rw [if_neg]
    intro h
    exact hl (by rw [← h]; simp)
  · simp
private theorem contDiffAt_angleRead [NeZero m] {G : TorusField m → ℝ} (h : ContDiffThreeAt G (trivialField m)) :
    ContDiffAt ℝ 2 (angleRead G) 0 := by apply _root_.YangMills.DeltaSharedProofs.p855 <;> assumption
private theorem hessianAtIdentity_eq_hessianAtZero [NeZero m] {G : TorusField m → ℝ}
    (hC : ContDiffAt ℝ 2 (angleRead G) 0) (b b' : TorusBond m) :
    hessianAtIdentity G b b' = hessianAtZero (angleRead G) (Pi.single b 1) (Pi.single b' 1) := by apply _root_.YangMills.DeltaSharedProofs.p501250 <;> assumption
private theorem quadraticForm_eq_hessianAtZero [NeZero m] {G : TorusField m → ℝ}
    (hC : ContDiffAt ℝ 2 (angleRead G) 0) (A A' : TorusBond m → ℝ) :
    ∑ b, ∑ b', A b * hessianAtIdentity G b b' * A' b' = hessianAtZero (angleRead G) A A' := by apply _root_.YangMills.DeltaSharedProofs.p502044 <;> assumption
private theorem mixedDeriv_single_eq_fderiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NeZero m]
    {G : TorusField m → E} (hC : DifferentiableAt ℝ (angleRead G) 0) (b : TorusBond m) :
    mixedDeriv G (trivialField m) ![b] ![unitGenerator] = fderiv ℝ (angleRead G) 0 (Pi.single b 1) := by
  classical
  set ι : (Fin 1 → ℝ) →L[ℝ] (TorusBond m → ℝ) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight (Pi.single b 1) with hι
  have hm : ∀ σ : Fin 1 → ℝ, perturb ![b] ![unitGenerator] σ (trivialField m) = expOfColourForm 1 (ι σ) := by
    intro σ
    funext x i
    show expUnit (∑ l, if ![b] l = (x, i) then σ l • ![unitGenerator] l else 0) * 1 =
      expUnit ((1 * ι σ (x, i)) • unitGenerator)
    rw [mul_one, one_mul, Fin.sum_univ_one]
    congr 1
    by_cases h1 : b = (x, i) <;> simp [hι, h1, eq_comm]
  unfold mixedDeriv
  rw [iteratedFDeriv_one_apply]
  have e : (fun σ : Fin 1 → ℝ => G (perturb ![b] ![unitGenerator] σ (trivialField m))) =
      fun σ => angleRead G (ι σ) :=
    funext fun σ => by rw [hm]; rfl
  rw [e]
  have hι0 : ι 0 = 0 := map_zero ι
  have hD : HasFDerivAt (angleRead G) (fderiv ℝ (angleRead G) 0) (ι 0) := by
    rw [hι0]
    exact hC.hasFDerivAt
  have h2 := hD.comp (0 : Fin 1 → ℝ) ι.hasFDerivAt
  have h3 : fderiv ℝ (fun σ => angleRead G (ι σ)) 0 = (fderiv ℝ (angleRead G) 0).comp ι := h2.fderiv
  rw [h3]
  have e1 : ι (Pi.single 0 1) = Pi.single b 1 := by simp [hι]
  simp [e1]
private theorem fderiv_angleRead_eq_zero [NeZero m] {G : TorusField m → ℝ}
    (hC : DifferentiableAt ℝ (angleRead G) 0)
    (hz : ∀ b, mixedDeriv G (trivialField m) ![b] ![unitGenerator] = 0) : fderiv ℝ (angleRead G) 0 = 0 := by
  classical
  refine ContinuousLinearMap.ext fun A => ?_
  have hs : A = ∑ b, A b • (Pi.single b 1 : TorusBond m → ℝ) := by
    funext b
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hs, map_sum]
  simp only [map_smul]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [← mixedDeriv_single_eq_fderiv hC, hz]
  simp
private theorem hessianAtZero_comp_of_critical {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {f : E → ℝ} {ψ : E' → E} (hf : ContDiffAt ℝ 2 f 0) (hz : fderiv ℝ f 0 = 0) (hψ : ContDiffAt ℝ 2 ψ 0)
    (h0 : ψ 0 = 0) (p q : E') :
    hessianAtZero (fun θ => f (ψ θ)) p q = hessianAtZero f (fderiv ℝ ψ 0 p) (fderiv ℝ ψ 0 q) := by
  have hf' : ContDiffAt ℝ 2 f (ψ 0) := by rwa [h0]
  have hF : ContDiffAt ℝ 2 (fun θ => f (ψ θ)) 0 := hf'.comp (0 : E') hψ
  have hdiag : ∀ r : E', hessianAtZero (fun θ => f (ψ θ)) r r =
      hessianAtZero f (fderiv ℝ ψ 0 r) (fderiv ℝ ψ 0 r) := by
    intro r
    rw [← deriv_deriv_along_line hF r]
    have hl : ContDiffAt ℝ 2 (fun τ : ℝ => τ • r) 0 := contDiffAt_id.smul contDiffAt_const
    have hψ0 : ContDiffAt ℝ 2 ψ ((0 : ℝ) • r) := by simpa using hψ
    have hγ : ContDiffAt ℝ 2 (fun τ : ℝ => ψ (τ • r)) 0 := hψ0.comp (0 : ℝ) hl
    have h1 := deriv_deriv_along_curve hf hz hγ (by simpa using h0)
    rw [h1]
    have hd : deriv (fun τ : ℝ => ψ (τ • r)) 0 = fderiv ℝ ψ 0 r := by
      have hD : HasFDerivAt ψ (fderiv ℝ ψ 0) ((0 : ℝ) • r) := by
        rw [zero_smul]
        exact (hψ.differentiableAt (by norm_num)).hasFDerivAt
      have hs : HasDerivAt (fun τ : ℝ => τ • r) r 0 := by
        have h3 : HasDerivAt (fun τ : ℝ => τ • r) ((1 : ℝ) • r) 0 := (hasDerivAt_id' (0 : ℝ)).smul_const _
        rwa [one_smul] at h3
      exact (HasFDerivAt.comp_hasDerivAt (f := fun τ : ℝ => τ • r) (0 : ℝ) hD hs).deriv
    rw [hd]
  have s₁ := hessianAtZero_comm hF p q
  have s₂ := hessianAtZero_comm hf (fderiv ℝ ψ 0 p) (fderiv ℝ ψ 0 q)
  have d₁ := hdiag (p + q)
  have d₂ := hdiag p
  have d₃ := hdiag q
  rw [map_add, hessianAtZero_add_left, hessianAtZero_add_right, hessianAtZero_add_right, hessianAtZero_add_left,
    hessianAtZero_add_right, hessianAtZero_add_right] at d₁
  linarith
end Angles
section Chain
variable {n N : ℕ} [NeZero n] [NeZero N]
private theorem hessianAtIdentity_comp_of_colour {Fd : TorusField n → TorusField N}
    {ψ : (TorusBond n → ℝ) → TorusBond N → ℝ} (hψ : ContDiffAt ℝ 2 ψ 0) (h0 : ψ 0 = 0)
    (hev : ∀ᶠ θ in 𝓝 (0 : TorusBond n → ℝ), Fd (expOfColourForm 1 θ) = expOfColourForm 1 (ψ θ))
    {g : TorusField N → ℝ} (hg : ContDiffThreeAt g (trivialField N))
    (hf : HasQuadraticFormAtIdentity g) (c c' : TorusBond n) :
    hessianAtIdentity (fun V => g (Fd V)) c c' =
      ∑ b, ∑ b', fderiv ℝ ψ 0 (Pi.single c 1) b * hessianAtIdentity g b b' *
        fderiv ℝ ψ 0 (Pi.single c' 1) b' := by
  have hg2 := contDiffAt_angleRead hg
  have hz : fderiv ℝ (angleRead g) 0 = 0 :=
    fderiv_angleRead_eq_zero (hg2.differentiableAt (by norm_num)) fun b => hf.1 b unitGenerator
  have hg2' : ContDiffAt ℝ 2 (angleRead g) (ψ 0) := by rwa [h0]
  have hcomp : ContDiffAt ℝ 2 (fun θ => angleRead g (ψ θ)) 0 := hg2'.comp (0 : TorusBond n → ℝ) hψ
  have hev' : angleRead (fun V => g (Fd V)) =ᶠ[𝓝 0] fun θ => angleRead g (ψ θ) := hev.mono fun θ h => by
    show g (Fd (expOfColourForm 1 θ)) = g (expOfColourForm 1 (ψ θ))
    rw [h]
  have hC : ContDiffAt ℝ 2 (angleRead fun V => g (Fd V)) 0 := hcomp.congr_of_eventuallyEq hev'
  rw [hessianAtIdentity_eq_hessianAtZero hC]
  have e : hessianAtZero (angleRead fun V => g (Fd V)) (Pi.single c 1) (Pi.single c' 1) =
      hessianAtZero (fun θ => angleRead g (ψ θ)) (Pi.single c 1) (Pi.single c' 1) := by
    unfold hessianAtZero
    rw [hev'.fderiv.fderiv_eq]
  rw [e, hessianAtZero_comp_of_critical hg2 hz hψ h0, quadraticForm_eq_hessianAtZero hg2]
end Chain
section Frames
variable (a ρ : ℝ) (m : ℕ) {L : ℕ} [NeZero L] (u : ℕ) {n : ℕ} [NeZero n]
private def frameComponent (star : Bool) (b : TorusBond (n * L)) (V : TorusField n) : imaginaryQuaternions :=
  stepFrame star a ρ m (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2)
    (readAtLevel (torusFrame L u n) (torusFrame L u n).top V)
private theorem stepCoordinates_zero {F : BlockFrame} {S : Finset F.Cell} (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (0 : StepVariable S) x i = 0 := by apply _root_.YangMills.SharedProofs.p7539 <;> assumption
private theorem interpolatedField_eq_torusChart (hL : Odd L) (h2 : 2 ≤ n) (V : TorusField n) :
    restrictToTorus (n * L) (interpolatedField 1 a ρ m (readAtLevel (torusFrame L u n) (torusFrame L u n).top V) 0) =
      torusChart L (fun b => frameComponent a ρ m u false b V) V := by
  have : NeZero (n * (torusFrame L u n).blockSide) := inferInstanceAs (NeZero (n * L))
  funext x i
  have h := chartedField_readAtLevel (F := torusFrame L u n) (n := n) (fun _ => rfl) hL h2
    (interpolatedCoords 1 a ρ m (readAtLevel (torusFrame L u n) (torusFrame L u n).top V) 0) V x i
  have e : (fun b : TorusBond (n * L) => interpolatedCoords 1 a ρ m
      (readAtLevel (torusFrame L u n) (torusFrame L u n).top V) 0
      (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1) b.2) =
        fun b => frameComponent a ρ m u false b V := by
    funext b
    simp [interpolatedCoords, interpolatedFrame, stepCoordinates_zero, frameComponent]
  exact Eq.trans h (congrFun (congrFun (congrArg
    (fun w : TorusBond (n * L) → imaginaryQuaternions => torusChart L w V) e) x) i)
private theorem gaugeTransform_quarterRotation (θ : TorusBond n → ℝ) :
    gaugeTransform (fun _ => colourRotation (Real.pi / 2))
        (readAtLevel (torusFrame L u n) (torusFrame L u n).top (expOfColourForm 1 θ)) =
      readAtLevel (torusFrame L u n) (torusFrame L u n).top (expOfColourForm 1 θ) := by
  funext x i
  show colourRotation (Real.pi / 2) * expOfColourForm 1 θ _ i * (colourRotation (Real.pi / 2))⁻¹ =
    expOfColourForm 1 θ _ i
  rw [expOfColourForm_apply, colourRotation_inv, ← colourRotation_add, ← colourRotation_add]
  congr 1
  ring
private theorem eq_smul_unitGenerator_of_fixed (w : imaginaryQuaternions)
    (h : (w : ℍ[ℝ]) = ((colourRotation (Real.pi / 2) : UnitQuaternion) : ℍ[ℝ]) * (w : ℍ[ℝ]) *
      (((colourRotation (Real.pi / 2))⁻¹ : UnitQuaternion) : ℍ[ℝ])) :
    w = (w : ℍ[ℝ]).imI • unitGenerator := by
  rw [colourRotation_inv, coe_colourRotation, coe_colourRotation] at h
  have hre : (w : ℍ[ℝ]).re = 0 := w.2
  have c₁ : Real.cos (-(Real.pi / 2)) = 0 := by rw [Real.cos_neg, Real.cos_pi_div_two]
  have c₂ : Real.sin (-(Real.pi / 2)) = -1 := by rw [Real.sin_neg, Real.sin_pi_div_two]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two, c₁, c₂] at h
  have hj := congrArg (fun q : ℍ[ℝ] => q.imJ) h
  have hk := congrArg (fun q : ℍ[ℝ] => q.imK) h
  simp [colourPlane, unitGenerator_re, unitGenerator_imI, unitGenerator_imJ, unitGenerator_imK] at hj hk
  apply Subtype.ext
  apply Quaternion.ext
  · simpa [unitGenerator_re] using hre
  · simp [unitGenerator_imI]
  · simp [unitGenerator_imJ]
    linarith
  · simp [unitGenerator_imK]
    linarith
private def frameAngle (θ : TorusBond n → ℝ) (b : TorusBond (n * L)) : ℝ :=
  ((frameComponent a ρ m u false b (expOfColourForm 1 θ) : imaginaryQuaternions) : ℍ[ℝ]).imI
open Classical in
private def chartAngles (θ : TorusBond n → ℝ) (b : TorusBond (n * L)) : ℝ :=
  if IsBlockEndBond L b.1 b.2 then frameAngle a ρ m u θ b + θ (parentBlock L b.1, b.2)
  else if IsBlockTreeBond L b.1 b.2 then 0 else frameAngle a ρ m u θ b
private theorem torusChart_eq_expOfColourForm (θ : TorusBond n → ℝ)
    (hc : ∀ b : TorusBond (n * L), IsBlockEndBond L b.1 b.2 ∨ ¬ IsBlockTreeBond L b.1 b.2 →
      frameComponent a ρ m u false b (expOfColourForm 1 θ) = frameAngle a ρ m u θ b • unitGenerator) :
    torusChart L (fun b => frameComponent a ρ m u false b (expOfColourForm 1 θ)) (expOfColourForm 1 θ) =
      expOfColourForm 1 (chartAngles a ρ m u θ) := by
  classical
  funext x i
  unfold torusChart chartAngles
  by_cases h1 : IsBlockEndBond L x i
  · simp only [if_pos h1]
    rw [hc (x, i) (Or.inl h1)]
    show colourRotation _ * expOfColourForm 1 θ (parentBlock L x) i = expOfColourForm 1 _ x i
    rw [expOfColourForm_apply, expOfColourForm_apply, ← colourRotation_add]
    simp only [if_pos h1]
    congr 1
    ring
  · by_cases h2 : IsBlockTreeBond L x i
    · simp only [if_neg h1, if_pos h2]
      rw [expOfColourForm_apply]
      simp only [if_neg h1, if_pos h2]
      rw [mul_zero, colourRotation_zero]
    · simp only [if_neg h1, if_neg h2]
      rw [hc (x, i) (Or.inr h2)]
      rw [expOfColourForm_apply]
      simp only [if_neg h1, if_neg h2]
      show colourRotation _ = colourRotation _
      rw [one_mul]
end Frames
section Read
variable {L u n : ℕ} [NeZero L] [NeZero n]
private theorem period_eq (i : Fin 4) : (torusFrame L u n).period (torusFrame L u n).top i = n := period_top i
private def liftBonds {k : ℕ} (L u : ℕ) (c : Fin k → TorusBond n) :
    Fin k → (torusFrame L u n).Site (torusFrame L u n).top × Fin 4 :=
  fun l => (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top (c l).1, (c l).2)
private theorem readAtLevel_perturb {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (V : TorusField n) :
    readAtLevel (torusFrame L u n) (torusFrame L u n).top (perturb c X σ V) =
      leftTranslate (ColdStepAtMirrorFrames.bondSpread (liftBonds L u c) X σ)
        (readAtLevel (torusFrame L u n) (torusFrame L u n).top V) := by apply _root_.YangMills.DeltaSharedProofs.p502130 <;> assumption
private theorem mixedDeriv_readAtLevel {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : (torusFrame L u n).GaugeField (torusFrame L u n).top → E) {k : ℕ}
    (V : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun W => G (readAtLevel (torusFrame L u n) (torusFrame L u n).top W)) V c X =
      bondDeriv G (readAtLevel (torusFrame L u n) (torusFrame L u n).top V) (liftBonds L u c) X := by
  unfold mixedDeriv bondDeriv
  have e : (fun σ : Fin k → ℝ => G (readAtLevel (torusFrame L u n) (torusFrame L u n).top (perturb c X σ V))) =
      fun σ => G (leftTranslate (ColdStepAtMirrorFrames.bondSpread (liftBonds L u c) X σ)
        (readAtLevel (torusFrame L u n) (torusFrame L u n).top V)) := by
    funext σ
    rw [readAtLevel_perturb]
  rw [e]
private theorem contDiffAt_angleRead_of_analytic {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {G : (torusFrame L u n).GaugeField (torusFrame L u n).top → E}
    (h : IsBondAnalyticAt G (uniformField (torusFrame L u n) (torusFrame L u n).top)) :
    ContDiffAt ℝ 2 (angleRead fun V : TorusField n => G (readAtLevel (torusFrame L u n) (torusFrame L u n).top V)) 0 := by
  classical
  set e := Fintype.equivFin (TorusBond n) with he
  have h3 : ContDiffAt ℝ 2 (fun σ : Fin (Fintype.card (TorusBond n)) → ℝ =>
      G (leftTranslate (ColdStepAtMirrorFrames.bondSpread (liftBonds L u e.symm) (fun _ => unitGenerator) σ)
        (uniformField (torusFrame L u n) (torusFrame L u n).top))) 0 :=
    (h _ (liftBonds L u e.symm) (fun _ => unitGenerator)).contDiffAt
  have hm : ∀ θ : TorusBond n → ℝ, readAtLevel (torusFrame L u n) (torusFrame L u n).top (expOfColourForm 1 θ) =
      leftTranslate (ColdStepAtMirrorFrames.bondSpread (liftBonds L u e.symm) (fun _ => unitGenerator) (fun l => θ (e.symm l)))
        (uniformField (torusFrame L u n) (torusFrame L u n).top) := by
    intro θ
    have h1 := perturb_all_eq (m := n) e (fun l => θ (e.symm l))
    simp only [Equiv.symm_apply_apply] at h1
    rw [← h1, readAtLevel_perturb]
    rfl
  have hA : (angleRead fun V : TorusField n => G (readAtLevel (torusFrame L u n) (torusFrame L u n).top V)) =
      (fun σ : Fin (Fintype.card (TorusBond n)) → ℝ =>
        G (leftTranslate (ColdStepAtMirrorFrames.bondSpread (liftBonds L u e.symm) (fun _ => unitGenerator) σ)
          (uniformField (torusFrame L u n) (torusFrame L u n).top))) ∘
        (fun θ : TorusBond n → ℝ => fun l => θ (e.symm l)) := by
    funext θ
    simp only [Function.comp, angleRead, hm]
  rw [hA]
  have hl : ContDiffAt ℝ 2 (fun θ : TorusBond n → ℝ => fun l => θ (e.symm l)) 0 := by
    refine ContDiff.contDiffAt (contDiff_pi.mpr fun l => ?_)
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : TorusBond n => ℝ) (e.symm l)).contDiff
  have h3' : ContDiffAt ℝ 2 (fun σ : Fin (Fintype.card (TorusBond n)) → ℝ =>
      G (leftTranslate (ColdStepAtMirrorFrames.bondSpread (liftBonds L u e.symm) (fun _ => unitGenerator) σ)
        (uniformField (torusFrame L u n) (torusFrame L u n).top)))
      ((fun θ : TorusBond n → ℝ => fun l => θ (e.symm l)) 0) := h3
  exact ContDiffAt.comp (0 : TorusBond n → ℝ) h3' hl
end Read
private def imIComponent : imaginaryQuaternions →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => (w : ℍ[ℝ]).imI
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp }
private theorem imIComponent_apply (w : imaginaryQuaternions) : imIComponent w = (w : ℍ[ℝ]).imI := rfl
private theorem abs_imI_le_norm (q : ℍ[ℝ]) : |q.imI| ≤ ‖q‖ := by
  have h := Quaternion.normSq_eq_norm_mul_self q
  rw [Quaternion.normSq_def'] at h
  refine abs_le_of_sq_le_sq ?_ (norm_nonneg _)
  nlinarith [sq_nonneg q.re, sq_nonneg q.imJ, sq_nonneg q.imK]
section Kernel
variable (a ρ : ℝ) (m : ℕ) {L : ℕ} [NeZero L] (u : ℕ) {n : ℕ} [NeZero n]
private def frameDeriv (star : Bool) (b : TorusBond (n * L)) (c : TorusBond n) : imaginaryQuaternions :=
  mixedDeriv (frameComponent a ρ m u star b) (trivialField n) ![c] ![unitGenerator]
private theorem frameDeriv_eq (star : Bool) (b : TorusBond (n * L)) (c : TorusBond n) :
    frameDeriv a ρ m u star b c =
      bondDeriv (stepFrame star a ρ m (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2))
        (uniformField (torusFrame L u n) (torusFrame L u n).top)
        ![(torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2)] ![unitGenerator] := by
  have h := mixedDeriv_readAtLevel (L := L) (u := u)
    (stepFrame star a ρ m (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2))
    (trivialField n) ![c] ![unitGenerator]
  have e : liftBonds L u ![c] = ![(torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2)] := by
    funext l
    fin_cases l
    rfl
  rw [e] at h
  exact h
private theorem responseKernel_eq_frameDeriv (b : TorusBond (n * L)) (c : TorusBond n) :
    responseKernel a ρ L u b c = imIComponent (frameDeriv a ρ m u true b c) + (open Classical in
      if IsCrossingBond (F := torusFrame L u n)
          (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) ∧
        enclosingCell (F := torusFrame L u n) (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1) =
          torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1 ∧
        b.2 = c.2 then 1 else 0) := by
  classical
  have e : torusCoordinate (F := torusFrame L u n) a ρ
      (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) =
      stepFrame true a ρ m (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) := by
    funext V
    simp [stepFrame, torusCoordinate]
  unfold responseKernel minimizerResponse
  rw [e, ← frameDeriv_eq a ρ m u true b c, imIComponent_apply]
  have hre : ((frameDeriv a ρ m u true b c : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := (frameDeriv a ρ m u true b c).2
  congr 1
  simp [unitGenerator_re, unitGenerator_imI, unitGenerator_imJ, unitGenerator_imK, hre]
end Kernel
section ChartBonds
variable (a ρ : ℝ) (m : ℕ) {L : ℕ} [NeZero L] (u : ℕ) {n : ℕ} [NeZero n]
private def IsChartBond (L : ℕ) {n : ℕ} (b : TorusBond (n * L)) : Prop :=
  IsBlockEndBond L b.1 b.2 ∨ ¬ IsBlockTreeBond L b.1 b.2
private theorem frameAngle_contDiff_fderiv {b : TorusBond (n * L)}
    (hb : IsBondAnalyticAt (stepFrame false a ρ m (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2))
      (uniformField (torusFrame L u n) (torusFrame L u n).top)) :
    ContDiffAt ℝ 2 (fun θ : TorusBond n → ℝ => frameAngle a ρ m u θ b) 0 ∧
      ∀ c : TorusBond n, fderiv ℝ (fun θ : TorusBond n → ℝ => frameAngle a ρ m u θ b) 0 (Pi.single c 1) =
        imIComponent (frameDeriv a ρ m u false b c) := by
  have hA : ContDiffAt ℝ 2 (angleRead (frameComponent a ρ m u false b)) 0 := contDiffAt_angleRead_of_analytic hb
  have e : (fun θ : TorusBond n → ℝ => frameAngle a ρ m u θ b) =
      fun θ => imIComponent (angleRead (frameComponent a ρ m u false b) θ) := rfl
  have hd : DifferentiableAt ℝ (angleRead (frameComponent a ρ m u false b)) 0 := hA.differentiableAt (by norm_num)
  refine ⟨?_, fun c => ?_⟩
  · rw [e]
    exact imIComponent.contDiff.contDiffAt.comp (0 : TorusBond n → ℝ) hA
  · rw [e]
    have h2 := (imIComponent.hasFDerivAt (x := angleRead (frameComponent a ρ m u false b) 0)).comp
      (0 : TorusBond n → ℝ) hd.hasFDerivAt
    have h3 : fderiv ℝ (fun θ => imIComponent (angleRead (frameComponent a ρ m u false b) θ)) 0 =
        imIComponent.comp (fderiv ℝ (angleRead (frameComponent a ρ m u false b)) 0) := h2.fderiv
    rw [h3]
    show imIComponent _ = _
    unfold frameDeriv
    rw [mixedDeriv_single_eq_fderiv hd]
    rfl
private theorem contDiffAt_chartAngles
    (han : ∀ b : TorusBond (n * L), IsChartBond L b →
      IsBondAnalyticAt (stepFrame false a ρ m (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2))
        (uniformField (torusFrame L u n) (torusFrame L u n).top)) :
    ContDiffAt ℝ 2 (chartAngles a ρ m (L := L) u (n := n)) 0 := by
  classical
  refine contDiffAt_pi.mpr fun b => ?_
  by_cases h1 : IsBlockEndBond L b.1 b.2
  · have e : (fun θ : TorusBond n → ℝ => chartAngles a ρ m u θ b) =
        fun θ => frameAngle a ρ m u θ b + θ (parentBlock L b.1, b.2) :=
      funext fun θ => by simp only [chartAngles, if_pos h1]
    rw [e]
    exact (frameAngle_contDiff_fderiv a ρ m u (han b (Or.inl h1))).1.add
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : TorusBond n => ℝ) (parentBlock L b.1, b.2)).contDiff.contDiffAt)
  · by_cases h2 : IsBlockTreeBond L b.1 b.2
    · have e : (fun θ : TorusBond n → ℝ => chartAngles a ρ m u θ b) = fun _ => 0 :=
        funext fun θ => by simp only [chartAngles, if_neg h1, if_pos h2]
      rw [e]
      exact contDiffAt_const
    · have e : (fun θ : TorusBond n → ℝ => chartAngles a ρ m u θ b) = fun θ => frameAngle a ρ m u θ b :=
        funext fun θ => by simp only [chartAngles, if_neg h1, if_neg h2]
      rw [e]
      exact (frameAngle_contDiff_fderiv a ρ m u (han b (Or.inr h2))).1
private theorem fderiv_apply_component {ψ : (TorusBond n → ℝ) → TorusBond (n * L) → ℝ}
    (hψ : ContDiffAt ℝ 2 ψ 0) (b : TorusBond (n * L)) (v : TorusBond n → ℝ) :
    fderiv ℝ ψ 0 v b = fderiv ℝ (fun θ => ψ θ b) 0 v := by
  have h := (hψ.differentiableAt (by norm_num)).hasFDerivAt
  have h2 := (hasFDerivAt_pi'.1 h) b
  rw [h2.fderiv]
  rfl
private theorem isCrossingBond_iff_isBlockEndBond (hL : Odd L) (h2 : 2 ≤ n) (b : TorusBond (n * L)) :
    IsCrossingBond (F := torusFrame L u n) (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) ↔
      IsBlockEndBond L b.1 b.2 := by
  have : NeZero (n * (torusFrame L u n).blockSide) := inferInstanceAs (NeZero (n * L))
  exact isCrossingBond_torusSiteInFrame_iff (F := torusFrame L u n) (n := n) (fun _ => rfl) hL h2 b.1 b.2
private theorem isAxialTreeBond_iff_isBlockTreeBond (hL : Odd L) (h2 : 2 ≤ n) (b : TorusBond (n * L)) :
    IsAxialTreeBond (F := torusFrame L u n) (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) ↔
      IsBlockTreeBond L b.1 b.2 := by
  have : NeZero (n * (torusFrame L u n).blockSide) := inferInstanceAs (NeZero (n * L))
  exact isAxialTreeBond_torusSiteInFrame_iff (F := torusFrame L u n) (n := n) (fun _ => rfl) hL h2 b.1 b.2
private theorem enclosingCell_eq_iff (b : TorusBond (n * L)) (z : TorusSite n) :
    enclosingCell (F := torusFrame L u n) (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1) =
      torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top z ↔ parentBlock L b.1 = z := by
  have : NeZero (n * (torusFrame L u n).blockSide) := inferInstanceAs (NeZero (n * L))
  have e := enclosingCell_torusSiteInFrame (F := torusFrame L u n) (n := n) (fun _ => rfl) b.1
  constructor
  · intro h
    have h3 : torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top (parentBlock L b.1) =
        torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top z :=
      e.symm.trans h
    have h4 := congrArg (toTorusSite n) h3
    rwa [toTorusSite_torusSiteInFrame period_eq, toTorusSite_torusSiteInFrame period_eq] at h4
  · intro h
    rw [← h]
    exact e
open Classical in
private theorem crossingIndicator_eq_single (hL : Odd L) (h2 : 2 ≤ n) (b : TorusBond (n * L)) (c : TorusBond n)
    (hc : IsBlockEndBond L b.1 b.2) :
    (if IsCrossingBond (F := torusFrame L u n)
          (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) ∧
        enclosingCell (F := torusFrame L u n) (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1) =
          torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1 ∧ b.2 = c.2 then (1 : ℝ) else 0) =
      (Pi.single c 1 : TorusBond n → ℝ) (parentBlock L b.1, b.2) := by
  by_cases h : (parentBlock L b.1, b.2) = c
  · have h₁ : parentBlock L b.1 = c.1 := congrArg Prod.fst h
    have h₂ : b.2 = c.2 := congrArg Prod.snd h
    rw [if_pos ⟨(isCrossingBond_iff_isBlockEndBond u hL h2 b).2 hc, (enclosingCell_eq_iff u b c.1).2 h₁, h₂⟩, h,
      Pi.single_eq_same]
  · rw [if_neg, Pi.single_eq_of_ne h]
    rintro ⟨-, h₁, h₂⟩
    exact h (Prod.ext ((enclosingCell_eq_iff u b c.1).1 h₁) h₂)
private theorem crossingIndicator_eq_zero (hL : Odd L) (h2 : 2 ≤ n) (b : TorusBond (n * L)) (c : TorusBond n)
    (hc : ¬ IsBlockEndBond L b.1 b.2) :
    (open Classical in if IsCrossingBond (F := torusFrame L u n)
          (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) ∧
        enclosingCell (F := torusFrame L u n) (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1) =
          torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1 ∧ b.2 = c.2 then (1 : ℝ) else 0) = 0 := by
  classical
  rw [if_neg]
  rintro ⟨h, -⟩
  exact hc ((isCrossingBond_iff_isBlockEndBond u hL h2 b).1 h)
private theorem fderiv_chartAngles_sub_responseKernel (hL : Odd L) (h2 : 2 ≤ n)
    (hψ : ContDiffAt ℝ 2 (chartAngles a ρ m (L := L) u (n := n)) 0) {b : TorusBond (n * L)} (hb : IsChartBond L b)
    (han : IsBondAnalyticAt (stepFrame false a ρ m (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2))
      (uniformField (torusFrame L u n) (torusFrame L u n).top)) (c : TorusBond n) :
    fderiv ℝ (chartAngles a ρ m (L := L) u (n := n)) 0 (Pi.single c 1) b - responseKernel a ρ L u b c =
      imIComponent (frameDeriv a ρ m u false b c) - imIComponent (frameDeriv a ρ m u true b c) := by
  classical
  obtain ⟨hp, hd⟩ := frameAngle_contDiff_fderiv a ρ m u han
  rw [fderiv_apply_component hψ, responseKernel_eq_frameDeriv a ρ m u b c]
  by_cases h1 : IsBlockEndBond L b.1 b.2
  · have e : (fun θ : TorusBond n → ℝ => chartAngles a ρ m u θ b) =
        fun θ => frameAngle a ρ m u θ b + θ (parentBlock L b.1, b.2) :=
      funext fun θ => by simp only [chartAngles, if_pos h1]
    have hq : DifferentiableAt ℝ (fun θ : TorusBond n → ℝ => θ (parentBlock L b.1, b.2)) 0 :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : TorusBond n => ℝ) (parentBlock L b.1, b.2)).differentiableAt
    rw [e, fderiv_fun_add (hp.differentiableAt (by norm_num)) hq, _root_.add_apply, hd c]
    have e₂ : fderiv ℝ (fun θ : TorusBond n → ℝ => θ (parentBlock L b.1, b.2)) 0 =
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : TorusBond n => ℝ) (parentBlock L b.1, b.2) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : TorusBond n => ℝ) (parentBlock L b.1, b.2)).fderiv
    rw [e₂, ContinuousLinearMap.proj_apply, ← crossingIndicator_eq_single u hL h2 b c h1]
    ring
  · have h2' : ¬ IsBlockTreeBond L b.1 b.2 := hb.resolve_left h1
    have e : (fun θ : TorusBond n → ℝ => chartAngles a ρ m u θ b) = fun θ => frameAngle a ρ m u θ b :=
      funext fun θ => by simp only [chartAngles, if_neg h1, if_neg h2']
    rw [e, hd c, crossingIndicator_eq_zero u hL h2 b c h1]
    ring
end ChartBonds
section Matrix
variable (a ρ : ℝ) (m : ℕ) {L : ℕ} [NeZero L] (u : ℕ) {n : ℕ} [NeZero n]
private theorem torusCoordinate_of_not_mem {F : BlockFrame} (a ρ : ℝ) (b : F.Site F.depth × Fin 4)
    (hb : b ∉ chordBonds (finiteCells F)) (V : F.GaugeField F.top) :
    torusCoordinate a ρ b V = 0 := by apply _root_.YangMills.SharedProofs.p33224 <;> assumption
private theorem supDist_self_eq_zero (z : TorusSite n) : TorusFields.supDist z z = 0 := by apply _root_.YangMills.Construction.TorusFields.supDist_self <;> assumption
private theorem abs_imIComponent_le (w : imaginaryQuaternions) : |imIComponent w| ≤ ‖w‖ := abs_imI_le_norm _
private theorem tree_bond_zero (hL : Odd L) (h2 : 2 ≤ n)
    (hψ : ContDiffAt ℝ 2 (chartAngles a ρ m (L := L) u (n := n)) 0) {b : TorusBond (n * L)}
    (hb : ¬ IsChartBond L b) (c : TorusBond n) :
    fderiv ℝ (chartAngles a ρ m (L := L) u (n := n)) 0 (Pi.single c 1) b = 0 ∧ responseKernel a ρ L u b c = 0 := by
  classical
  have h1 : ¬ IsBlockEndBond L b.1 b.2 := fun h => hb (Or.inl h)
  have h3 : IsBlockTreeBond L b.1 b.2 := by
    by_contra h
    exact hb (Or.inr h)
  constructor
  · rw [fderiv_apply_component hψ]
    have e : (fun θ : TorusBond n → ℝ => chartAngles a ρ m u θ b) = fun _ => 0 :=
      funext fun θ => by simp only [chartAngles, if_neg h1, if_pos h3]
    rw [e]
    simp
  · have hnc : (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) ∉
        chordBonds (finiteCells (torusFrame L u n)) :=
      fun h => (Finset.mem_filter.1 h).2 ((isAxialTreeBond_iff_isBlockTreeBond u hL h2 b).2 h3)
    have e : frameComponent a ρ m u true b = fun _ => 0 := by
      funext V
      exact torusCoordinate_of_not_mem a ρ _ hnc _
    have hD : frameDeriv a ρ m u true b c = 0 := by
      unfold frameDeriv mixedDeriv
      rw [e, iteratedFDeriv_const_of_ne (by norm_num)]
      rfl
    rw [responseKernel_eq_frameDeriv a ρ m u b c, hD, crossingIndicator_eq_zero u hL h2 b c h1]
    simp
private theorem exists_responseMatrix (hL : Odd L) (h2 : 2 ≤ n) {g₀ C₁ κ : ℝ} (hg₀ : 0 ≤ g₀) (hC₁ : 0 ≤ C₁)
    (hcol : ∀ᶠ θ in 𝓝 (0 : TorusBond n → ℝ), ∀ b : TorusBond (n * L), IsChartBond L b →
      frameComponent a ρ m u false b (expOfColourForm 1 θ) = frameAngle a ρ m u θ b • unitGenerator)
    (han : ∀ b : TorusBond (n * L), IsChartBond L b →
      IsBondAnalyticAt (stepFrame false a ρ m (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2))
        (uniformField (torusFrame L u n) (torusFrame L u n).top))
    (hzero : ∀ b : TorusBond (n * L), IsChartBond L b → frameComponent a ρ m u false b (trivialField n) = 0)
    (hgap : ∀ b : TorusBond (n * L), IsChartBond L b → ∀ c : TorusBond n,
      ‖((frameDeriv a ρ m u false b c : imaginaryQuaternions) : ℍ[ℝ]) -
          ((frameDeriv a ρ m u true b c : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        g₀ * Real.exp (-(κ * bondSiteDist L b c.1)))
    (hdec : ∀ b : TorusBond (n * L), IsChartBond L b → ∀ c : TorusBond n,
      ‖frameDeriv a ρ m u true b c‖ ≤ C₁ * Real.exp (-(κ * bondSiteDist L b c.1))) :
    ∃ Z : TorusBond (n * L) → TorusBond n → ℝ,
      (∀ g : TorusField (n * L) → ℝ, ContDiffThreeAt g (trivialField (n * L)) → HasQuadraticFormAtIdentity g →
        ∀ c c' : TorusBond n,
          hessianAtIdentity (fun V : TorusField n => g (restrictToTorus (n * L)
            (interpolatedField 1 a ρ m (readAtLevel (torusFrame L u n) (torusFrame L u n).top V) 0))) c c' =
            ∑ b : TorusBond (n * L), ∑ b' : TorusBond (n * L), Z b c * hessianAtIdentity g b b' * Z b' c') ∧
      (∀ (b : TorusBond (n * L)) (c : TorusBond n),
        |Z b c - responseKernel a ρ L u b c| ≤ g₀ * Real.exp (-(κ * bondSiteDist L b c.1))) ∧
      ∀ (b : TorusBond (n * L)) (c : TorusBond n),
        |responseKernel a ρ L u b c| ≤ (C₁ + 1) * Real.exp (-(κ * bondSiteDist L b c.1)) := by
  classical
  have hψ := contDiffAt_chartAngles a ρ m u han
  have hflat : expOfColourForm 1 (0 : TorusBond n → ℝ) = trivialField n := by
    funext x i
    rw [expOfColourForm_apply]
    simp [colourRotation_zero, trivialField]
  have hpa0 : ∀ b : TorusBond (n * L), IsChartBond L b → frameAngle a ρ m u (0 : TorusBond n → ℝ) b = 0 := by
    intro b hb
    unfold frameAngle
    rw [hflat, hzero b hb]
    rfl
  have h0 : chartAngles a ρ m (L := L) u (n := n) 0 = 0 := by
    funext b
    unfold chartAngles
    by_cases h1 : IsBlockEndBond L b.1 b.2
    · rw [if_pos h1, hpa0 b (Or.inl h1)]
      simp
    · by_cases h3 : IsBlockTreeBond L b.1 b.2
      · rw [if_neg h1, if_pos h3]
        rfl
      · rw [if_neg h1, if_neg h3, hpa0 b (Or.inr h3)]
        rfl
  have hev : ∀ᶠ θ in 𝓝 (0 : TorusBond n → ℝ), (fun V : TorusField n => restrictToTorus (n * L)
      (interpolatedField 1 a ρ m (readAtLevel (torusFrame L u n) (torusFrame L u n).top V) 0))
        (expOfColourForm 1 θ) = expOfColourForm 1 (chartAngles a ρ m u θ) :=
    hcol.mono fun θ h =>
      (interpolatedField_eq_torusChart a ρ m u hL h2 _).trans (torusChart_eq_expOfColourForm a ρ m u θ h)
  refine ⟨fun b c => fderiv ℝ (chartAngles a ρ m (L := L) u (n := n)) 0 (Pi.single c 1) b, ?_, ?_, ?_⟩
  · intro g hg hf c c'
    exact hessianAtIdentity_comp_of_colour hψ h0 hev hg hf c c'
  · intro b c
    by_cases hb : IsChartBond L b
    · have e := fderiv_chartAngles_sub_responseKernel a ρ m u hL h2 hψ hb (han b hb) c
      show |fderiv ℝ (chartAngles a ρ m (L := L) u (n := n)) 0 (Pi.single c 1) b - responseKernel a ρ L u b c| ≤ _
      rw [e, ← map_sub]
      exact (abs_imIComponent_le _).trans (hgap b hb c)
    · obtain ⟨z₀, m₀⟩ := tree_bond_zero a ρ m u hL h2 hψ hb c
      show |fderiv ℝ (chartAngles a ρ m (L := L) u (n := n)) 0 (Pi.single c 1) b - responseKernel a ρ L u b c| ≤ _
      rw [z₀, m₀]
      simp only [sub_zero, abs_zero]
      positivity
  · intro b c
    by_cases hb : IsChartBond L b
    · rw [responseKernel_eq_frameDeriv a ρ m u b c]
      refine (abs_add_le _ _).trans ?_
      have t₁ := (abs_imIComponent_le _).trans (hdec b hb c)
      have t₂ : |(if IsCrossingBond (F := torusFrame L u n)
            (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) ∧
          enclosingCell (F := torusFrame L u n) (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1) =
            torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1 ∧ b.2 = c.2 then (1 : ℝ) else 0)| ≤
          Real.exp (-(κ * bondSiteDist L b c.1)) := by
        split_ifs with h
        · have h₁ : parentBlock L b.1 = c.1 := (enclosingCell_eq_iff u b c.1).1 h.2.1
          have h₂ : bondSiteDist L b c.1 = 0 := by
            unfold bondSiteDist
            rw [h₁, supDist_self_eq_zero]
          rw [h₂]
          simp
        · simpa using (Real.exp_pos _).le
      rw [add_mul, one_mul]
      exact add_le_add t₁ t₂
    · obtain ⟨-, m₀⟩ := tree_bond_zero a ρ m u hL h2 hψ hb c
      rw [m₀, abs_zero]
      positivity
end Matrix
section Arith
private theorem frameRadius_inequalities {Cs C σ δ x m : ℝ} (hCs : 0 < Cs) (hC : 0 < C) (hσ : 0 < σ) (hx1 : 1 ≤ x)
    (hδ : 0 < δ) (hm0 : 0 ≤ m)
    (hAm : (Cs * 2 ^ 10 / σ + C * Cs + C) * x ^ 2 * Real.exp (-(3 * δ / 16 * m)) ≤ 1) :
    Cs * Real.exp (-(δ / 4 * m)) ≤ 2⁻¹ ^ 10 * σ ∧
      C * x ^ 2 * (Cs * Real.exp (-(δ / 4 * m))) ≤ Real.exp (-(δ / 16 * m)) ∧
      C * x ^ 2 * Real.exp (-(2 * δ * m)) ≤ 1 := by
  set e₁ := Real.exp (-(3 * δ / 16 * m)) with he₁
  have he₁0 : 0 < e₁ := Real.exp_pos _
  have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx1
  have p₁ : 0 < Cs * 2 ^ 10 / σ := by positivity
  have p₂ : 0 < C * Cs := by positivity
  have s₁ : Real.exp (-(δ / 4 * m)) = Real.exp (-(δ / 16 * m)) * e₁ := by
    rw [he₁, ← Real.exp_add]
    congr 1
    ring
  have s₀ : Real.exp (-(δ / 16 * m)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ δ / 16 * m := by positivity
    linarith)
  have s₂ : Real.exp (-(2 * δ * m)) ≤ e₁ := Real.exp_le_exp.2 (by
    have : 0 ≤ δ * m := by positivity
    nlinarith)
  have hA₁ : Cs * 2 ^ 10 / σ * e₁ ≤ 1 := by
    have : Cs * 2 ^ 10 / σ * e₁ ≤ (Cs * 2 ^ 10 / σ + C * Cs + C) * x ^ 2 * e₁ := by
      have h₁ : Cs * 2 ^ 10 / σ ≤ (Cs * 2 ^ 10 / σ + C * Cs + C) * x ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right h₁ he₁0.le
    linarith
  have hA₂ : C * Cs * x ^ 2 * e₁ ≤ 1 := by
    have : C * Cs * x ^ 2 * e₁ ≤ (Cs * 2 ^ 10 / σ + C * Cs + C) * x ^ 2 * e₁ := by
      have h₁ : C * Cs * x ^ 2 ≤ (Cs * 2 ^ 10 / σ + C * Cs + C) * x ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      exact mul_le_mul_of_nonneg_right h₁ he₁0.le
    linarith
  have hA₃ : C * x ^ 2 * e₁ ≤ 1 := by
    have : C * x ^ 2 * e₁ ≤ (Cs * 2 ^ 10 / σ + C * Cs + C) * x ^ 2 * e₁ := by
      have h₁ : C * x ^ 2 ≤ (Cs * 2 ^ 10 / σ + C * Cs + C) * x ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      exact mul_le_mul_of_nonneg_right h₁ he₁0.le
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [s₁]
    have h₁ : Cs * e₁ ≤ 2⁻¹ ^ 10 * σ := by
      have e : Cs * 2 ^ 10 / σ * e₁ = (Cs * e₁) * 2 ^ 10 / σ := by ring
      rw [e, div_le_one hσ] at hA₁
      norm_num at hA₁ ⊢
      linarith
    have h₂ : Cs * (Real.exp (-(δ / 16 * m)) * e₁) ≤ Cs * e₁ := by
      have : Real.exp (-(δ / 16 * m)) * e₁ ≤ 1 * e₁ := mul_le_mul_of_nonneg_right s₀ he₁0.le
      nlinarith
    linarith
  · rw [s₁]
    have e : C * x ^ 2 * (Cs * (Real.exp (-(δ / 16 * m)) * e₁)) =
        (C * Cs * x ^ 2 * e₁) * Real.exp (-(δ / 16 * m)) := by ring
    rw [e]
    exact mul_le_of_le_one_left (Real.exp_pos _).le hA₂
  · have : C * x ^ 2 * Real.exp (-(2 * δ * m)) ≤ C * x ^ 2 * e₁ := mul_le_mul_of_nonneg_left s₂ (by positivity)
    linarith
end Arith
private theorem mem_chordBonds_of_not_tree (hB : BlocksCoverLowerLevel) {F : BlockFrame} (hL : Odd F.blockSide)
    (hs : ∀ i, 0 < F.extent i) (z : F.Site F.depth) (i : Fin 4) (h : ¬ IsAxialTreeBond (z, i)) :
    (z, i) ∈ chordBonds (finiteCells F) := by
  unfold chordBonds innerBonds
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨⟨hB F hL hs z, hB F hL hs _⟩, h⟩
private theorem isSmallCurvature_readAtLevel {L t n : ℕ} [NeZero L] [NeZero n] {s : ℝ} {V : TorusField n}
    (hV : IsCold s V) :
    IsSmallCurvature (F := torusFrame L t n) s (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by
  rintro ⟨x, μ, ν⟩ hlt
  rw [plaquetteDefect_readAtLevel_eq period_eq]
  exact hV _ μ ν hlt
private theorem eventually_isCold_expOfColourForm {n : ℕ} [NeZero n] (hCold : ColdNearStatement) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ θ in 𝓝 (0 : TorusBond n → ℝ), IsCold s (expOfColourForm 1 θ) := by
  classical
  set e := Fintype.equivFin (TorusBond n) with he
  have h₀ : IsCold s (perturb e.symm (fun _ => unitGenerator) (0 : Fin (Fintype.card (TorusBond n)) → ℝ)
      (trivialField n)) := by
    rw [perturb_zero]
    exact TermCalculus.isCold_trivialField hs n
  have h₁ := hCold n (trivialField n) _ e.symm (fun _ => unitGenerator) 0 s h₀
  have hc : Continuous fun θ : TorusBond n → ℝ => fun l => θ (e.symm l) := continuous_pi fun l => continuous_apply _
  have h₂ : Filter.Tendsto (fun θ : TorusBond n → ℝ => fun l => θ (e.symm l)) (𝓝 0) (𝓝 0) :=
    hc.tendsto (0 : TorusBond n → ℝ)
  filter_upwards [h₂.eventually h₁] with θ hθ
  have h3 := perturb_all_eq (m := n) e (fun l => θ (e.symm l))
  simp only [Equiv.symm_apply_apply] at h3
  rwa [h3] at hθ
private theorem bondListDistance_single {L u n : ℕ} [NeZero n] (b : TorusSite n) (c : TorusBond n) :
    bondListDistance (F := torusFrame L u n) (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top b)
      ![(torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2)] = TorusFields.supDist b c.1 := by
  unfold bondListDistance
  simp only [Finset.univ_unique, Finset.sup_singleton]
  show cellSupDist (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top b)
    (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1) = _
  rw [cellSupDist_torusFrame, siteOfCell_torusSiteInFrame, siteOfCell_torusSiteInFrame]
private theorem bondDeriv_sub {F : BlockFrame} {j : ℕ} {G₁ G₂ : F.GaugeField j → imaginaryQuaternions}
    {W : F.GaugeField j} {c : Fin 1 → F.Site j × Fin 4} {X : Fin 1 → imaginaryQuaternions}
    (h₁ : AnalyticAt ℝ (fun σ : Fin 1 → ℝ => G₁ (leftTranslate (bondSpread c X σ) W)) 0)
    (h₂ : AnalyticAt ℝ (fun σ : Fin 1 → ℝ => G₂ (leftTranslate (bondSpread c X σ) W)) 0) :
    bondDeriv (fun V => (G₁ V : ℍ[ℝ]) - (G₂ V : ℍ[ℝ])) W c X =
      ((bondDeriv G₁ W c X : imaginaryQuaternions) : ℍ[ℝ]) - ((bondDeriv G₂ W c X : imaginaryQuaternions) : ℍ[ℝ]) := by
  unfold bondDeriv
  simp only [iteratedFDeriv_one_apply]
  have d₁ := h₁.differentiableAt
  have d₂ := h₂.differentiableAt
  have c₁ := (imaginaryQuaternions.subtypeL.hasFDerivAt (x := G₁ (leftTranslate (bondSpread c X 0) W))).comp
    (0 : Fin 1 → ℝ) d₁.hasFDerivAt
  have c₂ := (imaginaryQuaternions.subtypeL.hasFDerivAt (x := G₂ (leftTranslate (bondSpread c X 0) W))).comp
    (0 : Fin 1 → ℝ) d₂.hasFDerivAt
  have h3 := c₁.sub c₂
  have e : fderiv ℝ (fun σ : Fin 1 → ℝ => ((G₁ (leftTranslate (bondSpread c X σ) W) : imaginaryQuaternions) : ℍ[ℝ]) -
      ((G₂ (leftTranslate (bondSpread c X σ) W) : imaginaryQuaternions) : ℍ[ℝ])) 0 = _ := h3.fderiv
  rw [e]
  rfl
end FrameFieldAtIdentity
open FrameFieldAtIdentity in
theorem frameFieldResponseAtIdentity (hW : frameBoundsStatement) (hFl : Estimates.frameRadiusGrowthStatement)
    (hS : FlatCoordinatesScalar) (hB : BlocksCoverLowerLevel) (hCold : ColdNearStatement) :
    frameFieldResponseAtIdentityStatement := by
  classical
  unfold frameFieldResponseAtIdentityStatement ForAllPoints ForAllParameters
  intro a ha
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L hodd _ T hTa hTL hD hCS hOn _ _ Kr hFit => ?_⟩
  obtain ⟨c, nss, hties, -⟩ := hOn
  obtain ⟨-, -, eρ, -, -, -, eδ, hc⟩ := hties
  obtain ⟨Cf, C, σ₀, hCf, hC1, hσ₀, hWb⟩ := hW T.coupling T.side c hD.a_ge hD.L_odd hD.L_ge hc
  have hδ : 0 < c.δ₂ := by rw [eδ]; exact hD.δc_pos
  have hC0 : 0 < C := by linarith
  set A : ℝ := Cf * 2 ^ 10 / σ₀ + C * Cf + C with hA
  have hApos : 0 < A := by positivity
  obtain ⟨y₁, hy₁1, hy₁⟩ := hFl (A + 16) (3 * c.δ₂ / 16) (by positivity) (by positivity)
  obtain ⟨y₂, hy₂1, hy₂⟩ := hFl 1 (c.δ₂ / 4) one_pos (by positivity)
  refine ⟨max (max y₁ y₂) T.floorMin, fun y hy hRt hWy gg hg hgy k _ _ _ R d _ => ?_⟩
  have hyy₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hyy₂ : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  refine ⟨fun i => if i = 0 then Cf else C + 1, 1, y, one_pos, le_rfl, fun S t ht n _ hn => ?_⟩
  have ht' : t ≤ S.data.windowLevel := by omega
  have st : StageOnFlow T Kr y S.β t ⟨S.tower.stage t, S.resp t⟩ := by
    have h₁ := S.onFlow t ht'
    rw [← S.stage_eq t ht'] at h₁
    exact h₁
  have hρ : (S.tower.stage t).anchorRadius = c.ρA := st.onFamily.onFamily.anchorRadius_eq.trans eρ.symm
  have hxy : y ≤ (S.tower.stage t).coupling := st.onFamily.onFamily.le_coupling
  have hxc : (S.tower.stage t).coupling = S.coupling t := st.coupling_eq
  set x := (S.tower.stage t).coupling with hx
  set m := frameRadius x with hmdef
  set u := (S.tower.stage t).depth with hu
  have hLo : Odd (T.stepParameters y).side := hD.L_odd
  have hn4 : 4096 ≤ n := hD.n₀_ge.trans hn
  have h2 : 2 ≤ n := by omega
  have hx1 : 1 ≤ x := hy₁1.trans (hyy₁.trans hxy)
  obtain ⟨hAm₁, hAm₂⟩ := hy₁ x (hyy₁.trans hxy)
  obtain ⟨hBm₁, -⟩ := hy₂ x (hyy₂.trans hxy)
  have hm16 : 16 ≤ m := by
    have : (16 : ℝ) ≤ (m : ℝ) := by linarith
    exact_mod_cast this
  have hAm' : A * x ^ 2 * Real.exp (-(3 * c.δ₂ / 16 * (m : ℝ))) ≤ 1 := by
    have h₀ : 0 ≤ x ^ 2 * Real.exp (-(3 * c.δ₂ / 16 * (m : ℝ))) := by positivity
    nlinarith
  obtain ⟨f₁, f₂, f₃⟩ := frameRadius_inequalities hCf hC0 hσ₀ hx1 hδ (Nat.cast_nonneg m) hAm'
  have hκ : 0 < c.δ₂ / 2 ^ 14 := by positivity
  have hκe : Real.exp (-(2 ^ 10 * (c.δ₂ / 2 ^ 14) * (m : ℝ))) = Real.exp (-(c.δ₂ / 16 * (m : ℝ))) := by
    congr 1
    ring
  have hn₀ : 64 ≤ (T.stepParameters y).n₀ := by
    have := hD.n₀_ge
    show 64 ≤ T.n₀
    omega
  have htop : IsCubicTopTorus T.side u (T.stepParameters y).n₀ (torusFrame (T.stepParameters y).side u n) :=
    ⟨rfl, rfl, n, fun _ => rfl, hn⟩
  have hold : ∀ V : TorusField n, IsCold (5 / 4 * σ₀) V →
      FrameBoundsAt T.coupling T.side c Cf C σ₀ (c.δ₂ / 2 ^ 14) x m u (T.stepParameters y).n₀
        (torusFrame (T.stepParameters y).side u n)
        (readAtLevel (torusFrame (T.stepParameters y).side u n) (torusFrame (T.stepParameters y).side u n).top V) :=
    fun V hV =>
      hWb (c.δ₂ / 2 ^ 14) σ₀ x m u _ hκ le_rfl hσ₀ le_rfl hx1 hm16 hn₀ f₁ (by rw [hκe]; exact f₂) f₃ _ _ htop
        (isSmallCurvature_readAtLevel hV)
  have hs0 : 0 < 5 / 4 * σ₀ := by positivity
  have hcoldflat : IsCold (5 / 4 * σ₀) (trivialField n) := TermCalculus.isCold_trivialField hs0 n
  have hsmall : ∀ (star : Bool) (V : TorusField n), IsCold (5 / 4 * σ₀) V →
      FrameSmallness star T.coupling (S.tower.stage t).anchorRadius c.δ₂ c.κ₂ C σ₀ c.Kk m
        (readAtLevel (torusFrame (T.stepParameters y).side u n) (torusFrame (T.stepParameters y).side u n).top V) := by
    intro star V hV
    rw [hρ]
    exact (hold V hV).2.1 star
  have hside : ∀ i, 0 < (torusFrame (T.stepParameters y).side u n).extent i := fun _ => by
    show 0 < n
    omega
  have hchart : ∀ b : TorusBond (n * (T.stepParameters y).side), IsChartBond (T.stepParameters y).side b →
      (torusSiteInFrame (torusFrame (T.stepParameters y).side u n) (torusFrame (T.stepParameters y).side u n).depth b.1,
        b.2) ∈ chordBonds (finiteCells (torusFrame (T.stepParameters y).side u n)) := by
    intro b hb
    refine mem_chordBonds_of_not_tree hB hLo hside _ _ ?_
    intro ht₂
    rcases hb with h₁ | h₁
    · exact ht₂.1 ((isCrossingBond_iff_isBlockEndBond u hLo h2 b).2 h₁)
    · exact h₁ ((isAxialTreeBond_iff_isBlockTreeBond u hLo h2 b).1 ht₂)
  have hcol : ∀ᶠ θ in 𝓝 (0 : TorusBond n → ℝ), ∀ b : TorusBond (n * (T.stepParameters y).side),
      IsChartBond (T.stepParameters y).side b →
        frameComponent T.coupling (S.tower.stage t).anchorRadius m u false b (expOfColourForm 1 θ) =
          frameAngle T.coupling (S.tower.stage t).anchorRadius m u θ b • unitGenerator := by
    filter_upwards [eventually_isCold_expOfColourForm hCold hs0] with θ hθ b hb
    have hg₁ := (hsmall false _ hθ).gauge_covariant _ (hchart b hb) (fun _ => colourRotation (Real.pi / 2))
    rw [gaugeTransform_quarterRotation] at hg₁
    exact eq_smul_unitGenerator_of_fixed _ hg₁
  have han : ∀ b : TorusBond (n * (T.stepParameters y).side), IsChartBond (T.stepParameters y).side b →
      IsBondAnalyticAt (stepFrame false T.coupling (S.tower.stage t).anchorRadius m
        (torusSiteInFrame (torusFrame (T.stepParameters y).side u n)
          (torusFrame (T.stepParameters y).side u n).depth b.1, b.2))
        (uniformField (torusFrame (T.stepParameters y).side u n) (torusFrame (T.stepParameters y).side u n).top) :=
    fun b hb => (hsmall false (trivialField n) hcoldflat).analytic _ (hchart b hb)
  have han' : ∀ b : TorusBond (n * (T.stepParameters y).side), IsChartBond (T.stepParameters y).side b →
      IsBondAnalyticAt (stepFrame true T.coupling (S.tower.stage t).anchorRadius m
        (torusSiteInFrame (torusFrame (T.stepParameters y).side u n)
          (torusFrame (T.stepParameters y).side u n).depth b.1, b.2))
        (uniformField (torusFrame (T.stepParameters y).side u n) (torusFrame (T.stepParameters y).side u n).top) :=
    fun b hb => (hsmall true (trivialField n) hcoldflat).analytic _ (hchart b hb)
  have hF := hS T.coupling T.side c hD.L_odd hc
  have hzero : ∀ b : TorusBond (n * (T.stepParameters y).side), IsChartBond (T.stepParameters y).side b →
      frameComponent T.coupling (S.tower.stage t).anchorRadius m u false b (trivialField n) = 0 := by
    intro b hb
    unfold frameComponent
    rw [hρ]
    show stepFrame false T.coupling c.ρA m _
      (uniformField (torusFrame (T.stepParameters y).side u n) (torusFrame (T.stepParameters y).side u n).top) = 0
    simp only [stepFrame, Bool.false_eq_true, if_false]
    unfold bondFrameCoord
    split_ifs with hbig
    · unfold reflectedBondCoord
      have e : reflectedField m (enclosingCell (torusSiteInFrame (torusFrame (T.stepParameters y).side u n)
            (torusFrame (T.stepParameters y).side u n).depth b.1))
          (uniformField (torusFrame (T.stepParameters y).side u n) (torusFrame (T.stepParameters y).side u n).top) =
          uniformField (reflectedFrame (torusFrame (T.stepParameters y).side u n) m)
            (reflectedFrame (torusFrame (T.stepParameters y).side u n) m).top := by
        funext z i
        simp [reflectedField, uniformField]
      rw [e]
      exact (hF (reflectedFrame (torusFrame (T.stepParameters y).side u n) m) _ (0, 0) unitGenerator
        ⟨rfl, 4 * m, by omega, fun _ => rfl⟩ norm_unitGenerator).1
    · exact (hF (torusFrame (T.stepParameters y).side u n) _ (0, 0) unitGenerator
        ⟨rfl, n, by omega, fun _ => rfl⟩ norm_unitGenerator).1
  have hrate : 2 * (T.stepParameters y).weightRate ≤ c.δ₂ / 4 := by
    have h₁ : T.rt ≤ T.δc / 2 ^ 14 := hD.rt_le
    have h₂ : (T.stepParameters y).weightRate = T.rt / 2 ^ 10 := rfl
    rw [h₂, eδ]
    have := hD.δc_pos
    linarith
  have hexp : ∀ d : ℕ, Real.exp (-(c.δ₂ / 4 * (d : ℝ))) ≤
      Real.exp (-(2 * (T.stepParameters y).weightRate * (d : ℝ))) := fun d =>
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg d)))
  have hx0 : 0 < x := by linarith
  have hE : Real.exp (-(c.δ₂ / 4 * (m : ℝ))) ≤ x ^ (-(1 / 2) : ℝ) := by
    have h₁ : x ^ 2 * Real.exp (-(c.δ₂ / 4 * (m : ℝ))) ≤ 1 := by linarith
    have h₂ : Real.exp (-(c.δ₂ / 4 * (m : ℝ))) ≤ (x ^ 2)⁻¹ := by
      rw [← one_div, le_div_iff₀ (by positivity)]
      linarith
    have h₃ : (x ^ 2)⁻¹ = x ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hx0.le]
      norm_cast
    rw [h₃] at h₂
    exact h₂.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  have hdist : ∀ (b : TorusBond (n * (T.stepParameters y).side)) (z : TorusBond n),
      bondListDistance (F := torusFrame (T.stepParameters y).side u n)
        (enclosingCell (F := torusFrame (T.stepParameters y).side u n)
          (torusSiteInFrame (torusFrame (T.stepParameters y).side u n)
            (torusFrame (T.stepParameters y).side u n).depth b.1))
        ![(torusSiteInFrame (torusFrame (T.stepParameters y).side u n)
          (torusFrame (T.stepParameters y).side u n).top z.1, z.2)] =
        bondSiteDist (T.stepParameters y).side b z.1 := by
    intro b z
    rw [(enclosingCell_eq_iff u b (parentBlock (T.stepParameters y).side b.1)).2 rfl]
    exact bondListDistance_single _ _
  have hunit : AreUnitVectors ![unitGenerator] := by
    intro l
    fin_cases l
    exact norm_unitGenerator
  have hgap : ∀ b : TorusBond (n * (T.stepParameters y).side), IsChartBond (T.stepParameters y).side b →
      ∀ z : TorusBond n,
        ‖((frameDeriv T.coupling (S.tower.stage t).anchorRadius m u false b z : imaginaryQuaternions) : ℍ[ℝ]) -
            ((frameDeriv T.coupling (S.tower.stage t).anchorRadius m u true b z : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
          (Cf * x ^ (-(1 / 2) : ℝ)) *
            Real.exp (-(2 * (T.stepParameters y).weightRate * bondSiteDist (T.stepParameters y).side b z.1)) := by
    intro b hb z
    rw [frameDeriv_eq, frameDeriv_eq]
    by_cases hbig : ∀ i, 4 * m + 5 < (torusFrame (T.stepParameters y).side u n).extent i
    · have hnear := ((hold (trivialField n) hcoldflat).1 hbig _ (hchart b hb)).2 1
        ![(torusSiteInFrame (torusFrame (T.stepParameters y).side u n)
          (torusFrame (T.stepParameters y).side u n).top z.1, z.2)] ![unitGenerator] le_rfl (by norm_num) hunit
      have e₁ := bondDeriv_sub
        (G₁ := stepFrame false T.coupling c.ρA m (torusSiteInFrame (torusFrame (T.stepParameters y).side u n)
          (torusFrame (T.stepParameters y).side u n).depth b.1, b.2))
        (G₂ := stepFrame true T.coupling c.ρA m (torusSiteInFrame (torusFrame (T.stepParameters y).side u n)
          (torusFrame (T.stepParameters y).side u n).depth b.1, b.2))
        (W := uniformField (torusFrame (T.stepParameters y).side u n) (torusFrame (T.stepParameters y).side u n).top)
        (c := ![(torusSiteInFrame (torusFrame (T.stepParameters y).side u n)
          (torusFrame (T.stepParameters y).side u n).top z.1, z.2)]) (X := ![unitGenerator])
        (by have := han b hb 1 ![(torusSiteInFrame (torusFrame (T.stepParameters y).side u n)
              (torusFrame (T.stepParameters y).side u n).top z.1, z.2)] ![unitGenerator]
            rw [hρ] at this
            exact this)
        (by have := han' b hb 1 ![(torusSiteInFrame (torusFrame (T.stepParameters y).side u n)
              (torusFrame (T.stepParameters y).side u n).top z.1, z.2)] ![unitGenerator]
            rw [hρ] at this
            exact this)
      rw [hρ, ← e₁]
      refine (show _ ≤ _ from hnear).trans ?_
      rw [hdist]
      set dd := bondSiteDist (T.stepParameters y).side b z.1 with hdd
      have hl : Real.exp (-(c.δ₂ / 4 * ((m : ℝ) + max (m : ℝ) (dd : ℝ)))) ≤
          Real.exp (-(c.δ₂ / 4 * (m : ℝ))) * Real.exp (-(c.δ₂ / 4 * (dd : ℝ))) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have h₁ : (dd : ℝ) ≤ max (m : ℝ) (dd : ℝ) := le_max_right _ _
        have h₂ : 0 ≤ c.δ₂ / 4 := by positivity
        nlinarith
      have hl₂ : Real.exp (-(c.δ₂ / 4 * (m : ℝ))) * Real.exp (-(c.δ₂ / 4 * (dd : ℝ))) ≤
          x ^ (-(1 / 2) : ℝ) * Real.exp (-(2 * (T.stepParameters y).weightRate * (dd : ℝ))) :=
        mul_le_mul hE (hexp dd) (Real.exp_pos _).le (Real.rpow_nonneg hx0.le _)
      calc _ ≤ Cf * (x ^ (-(1 / 2) : ℝ) * Real.exp (-(2 * (T.stepParameters y).weightRate * (dd : ℝ)))) :=
            mul_le_mul_of_nonneg_left (by
              have := hl.trans hl₂
              simpa using this) hCf.le
        _ = _ := by ring
    · have e : stepFrame false T.coupling (S.tower.stage t).anchorRadius m
            (torusSiteInFrame (torusFrame (T.stepParameters y).side u n)
              (torusFrame (T.stepParameters y).side u n).depth b.1, b.2) =
          stepFrame true T.coupling (S.tower.stage t).anchorRadius m
            (torusSiteInFrame (torusFrame (T.stepParameters y).side u n)
              (torusFrame (T.stepParameters y).side u n).depth b.1, b.2) := by
        funext V
        simp only [stepFrame, Bool.false_eq_true, if_false, if_true]
        unfold bondFrameCoord
        rw [if_neg hbig]
      rw [e, sub_self, norm_zero]
      have : 0 ≤ x ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hx0.le _
      positivity
  have hdec : ∀ b : TorusBond (n * (T.stepParameters y).side), IsChartBond (T.stepParameters y).side b →
      ∀ z : TorusBond n,
        ‖frameDeriv T.coupling (S.tower.stage t).anchorRadius m u true b z‖ ≤
          C * Real.exp (-(2 * (T.stepParameters y).weightRate * bondSiteDist (T.stepParameters y).side b z.1)) := by
    intro b hb z
    rw [frameDeriv_eq]
    have h₁ := (hsmall true (trivialField n) hcoldflat).deriv_decay _ (hchart b hb) 1
      ![(torusSiteInFrame (torusFrame (T.stepParameters y).side u n)
        (torusFrame (T.stepParameters y).side u n).top z.1, z.2)] ![unitGenerator] le_rfl (by norm_num) hunit
    rw [hdist] at h₁
    exact h₁.trans (mul_le_mul_of_nonneg_left (hexp _) hC0.le)
  have hg₀ : 0 ≤ Cf * x ^ (-(1 / 2) : ℝ) := mul_nonneg hCf.le (Real.rpow_nonneg hx0.le _)
  obtain ⟨Z, z₁, z₂, z₃⟩ := exists_responseMatrix T.coupling (S.tower.stage t).anchorRadius m
    (L := (T.stepParameters y).side) u (n := n) hLo h2 hg₀ hC0.le hcol han hzero hgap hdec
  refine ⟨Z, fun g hg hf c₁ c₂ => z₁ g hg hf c₁ c₂, fun b z => ?_, fun b z => z₃ b z⟩
  have h₁ := z₂ b z
  rw [hxc] at h₁
  exact h₁
end YangMills.Construction.MomentLaw
end
