import YangMills.Construction.ResponseInTheExpansion.RestIsGaugeInvariant
import YangMills.Construction.SummableBoundsOfTheFlow.MeansOfTheWeightPartAreInvariantProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheHigherDerivativesOfTheDensityOfTheStepProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace YangMills.Construction
noncomputable section
open scoped Topology Quaternion RealInnerProductSpace
open BlockAverages MeasureTheory Interpolation WeightedResponses
open ColdStepAtMirrorFrames hiding uniformField
namespace ResponseInTheExpansion
namespace GaugeChangeOfVariables
variable {F : BlockFrame}
abbrev BondVariables (F : BlockFrame) : Type := StepVariable (finiteCells F)
theorem forall_norm_lt_of_cutoffWeight_ne_zero {ρ : ℝ} {p : ℝ → ℝ} (η : BondVariables F)
    (h : cutoffWeight ρ p η ≠ 0) : ∀ b, ‖η b‖ < ρ := by apply _root_.YangMills.DeltaSharedProofs.p502036 <;> assumption
theorem cutoffMean_comp {ρ : ℝ} {p : ℝ → ℝ} {R : BondVariables F → BondVariables F}
    (hR : MeasurePreserving R volume volume) (hemb : MeasurableEmbedding R)
    (hcut : ∀ η, cutoffWeight ρ p (R η) = cutoffWeight ρ p η) {Ψ Ψ' H H' : BondVariables F → ℝ}
    (hΨ : ∀ η, (∀ b, ‖η b‖ < ρ) → Ψ' (R η) = Ψ η) (hH : ∀ η, (∀ b, ‖η b‖ < ρ) → H' (R η) = H η) :
    cutoffMean ρ p Ψ' H' = cutoffMean ρ p Ψ H := by apply _root_.YangMills.DeltaSharedProofs.p500520 <;> assumption
theorem chartedField_congr {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions} (V : F.GaugeField F.top)
    (hw : ∀ x i, ¬ IsAxialTreeBond (x, i) → w x i = w' x i) : chartedField w V = chartedField w' V := by apply _root_.YangMills.SharedProofs.p16263 <;> assumption
theorem adjointAction_add (g : UnitQuaternion) (X Y : imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (X + Y) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X + _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g Y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add <;> assumption
theorem norm_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) :
    ‖_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X‖ = ‖X‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction <;> assumption
section Gauge
variable {s a ρA x : ℝ} {m : ℕ} {f : LocalFamily} {V : F.GaugeField F.top} {γ : F.Cell → UnitQuaternion}
theorem chartedEnergy_gaugeTransform (hM : ChartEquivariance F a)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ y i, ¬ IsAxialTreeBond (y, i) → w' y i = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (w y i)) :
    chartedEnergy a w' (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = chartedEnergy a w V := by apply _root_.YangMills.SharedProofs.p19410 <;> assumption
theorem chartedSlope_gaugeTransform (hM : ChartEquivariance F a)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ y i, ¬ IsAxialTreeBond (y, i) → w' y i = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (w y i))
    (b : F.Site F.depth × Fin 4) (hb : ¬ IsAxialTreeBond b) (e : imaginaryQuaternions) :
    chartedSlope a w' (gaugeTransform γ V) b (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) e) =
      chartedSlope a w V b e := by apply _root_.YangMills.SharedProofs.p24183 <;> assumption
def rotateBonds (A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector)
    (η : BondVariables F) : BondVariables F :=
  fun b => A b (η b)
theorem interpolatedCoords_gaugeTransform (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), interpolatedFrame s a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame s a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : BondVariables F) (y : F.Site F.depth) (i : Fin 4) (hnt : ¬ IsAxialTreeBond (y, i)) :
    interpolatedCoords s a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateBonds A η) y i =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (interpolatedCoords s a ρA m V η y i) := by
  have hb : (y, i) ∈ chordBonds (finiteCells F) := hM.mem_chordBonds_of_not_tree _ hnt
  unfold interpolatedCoords stepCoordinates
  rw [dif_pos hb, dif_pos hb, hfr _ hb, _root_.YangMills.Construction.ResponseInTheExpansion.GaugeChangeOfVariables.adjointAction_add]
  congr 1
  exact hA ⟨(y, i), hb⟩ (η ⟨(y, i), hb⟩)
theorem interpolatedField_gaugeTransform (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), interpolatedFrame s a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame s a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : BondVariables F) :
    interpolatedField s a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateBonds A η) =
      _root_.YangMills.Construction.BlockAverages.gaugeTransform (blockConstantGauge γ) (interpolatedField s a ρA m V η) := by
  unfold interpolatedField
  rw [chartedField_congr (gaugeTransform γ V) (_root_.YangMills.Construction.ResponseInTheExpansion.GaugeChangeOfVariables.interpolatedCoords_gaugeTransform hM hfr hA η),
    hM.chartedField_gaugeTransform]
theorem haarGapExcess_gaugeTransform (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), interpolatedFrame s a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame s a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : BondVariables F) (c : F.Site F.top × Fin 4) :
    haarGapExcess a x (interpolatedField s a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateBonds A η)) c =
      haarGapExcess a x (interpolatedField s a ρA m V η) c := by
  unfold haarGapExcess
  rw [_root_.YangMills.Construction.ResponseInTheExpansion.GaugeChangeOfVariables.interpolatedField_gaugeTransform hM hfr hA, hM.norm_contourAverage_gaugeTransform]
theorem haarLogRatio_gaugeTransform (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), interpolatedFrame s a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame s a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : BondVariables F) (b : ↥(chordBonds (finiteCells F))) (hnt : ¬ IsAxialTreeBond b.1) :
    haarLogRatio (interpolatedCoords s a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateBonds A η) b.1.1 b.1.2) =
      haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) := by
  unfold haarLogRatio
  rw [_root_.YangMills.Construction.ResponseInTheExpansion.GaugeChangeOfVariables.interpolatedCoords_gaugeTransform hM hfr hA η _ _ hnt, norm_adjointAction]
theorem smul_rotateBonds {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (v : ℝ) (η : BondVariables F) : v • rotateBonds A η = rotateBonds A (v • η) := by
  funext b
  simp [rotateBonds]
theorem rotateBonds_zero {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector} :
    rotateBonds A (0 : BondVariables F) = 0 := by
  funext b
  simp [rotateBonds]
theorem not_isAxialTreeBond_of_chord (b : ↥(chordBonds (finiteCells F))) : ¬ IsAxialTreeBond b.1 := by apply _root_.YangMills.SharedProofs.p29908 <;> assumption
theorem familyLawExponent_gaugeTransform (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), interpolatedFrame s a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame s a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : BondVariables F)
    (hrow : ∀ y : F.Site F.depth, interpolatedExpansion s a ρA m f y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) =
      interpolatedExpansion s a ρA m f y η V) :
    familyLawExponent s a ρA x m f (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateBonds A η) =
      familyLawExponent s a ρA x m f V η := by
  have hzero : ∀ η : BondVariables F,
      chartedEnergy a (interpolatedCoords s a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateBonds A η))
        (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = chartedEnergy a (interpolatedCoords s a ρA m V η) V := fun η =>
    _root_.YangMills.Construction.ResponseInTheExpansion.GaugeChangeOfVariables.chartedEnergy_gaugeTransform hM (_root_.YangMills.Construction.ResponseInTheExpansion.GaugeChangeOfVariables.interpolatedCoords_gaugeTransform hM hfr hA η)
  unfold familyLawExponent interpolatedExponent
  have h0 := hzero 0
  rw [rotateBonds_zero] at h0
  rw [hzero η, h0]
  have g1 : ∑ b : ↥(chordBonds (finiteCells F)),
      haarLogRatio (interpolatedCoords s a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateBonds A η) b.1.1 b.1.2) =
      ∑ b : ↥(chordBonds (finiteCells F)), haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) :=
    Finset.sum_congr rfl fun b _ =>
      _root_.YangMills.Construction.ResponseInTheExpansion.GaugeChangeOfVariables.haarLogRatio_gaugeTransform hM hfr hA η b (not_isAxialTreeBond_of_chord b)
  have g2 : ∑ c ∈ innerBonds (finiteCells F) F.top,
      haarGapExcess a x (interpolatedField s a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateBonds A η)) c =
      ∑ c ∈ innerBonds (finiteCells F) F.top, haarGapExcess a x (interpolatedField s a ρA m V η) c :=
    Finset.sum_congr rfl fun c _ => _root_.YangMills.Construction.ResponseInTheExpansion.GaugeChangeOfVariables.haarGapExcess_gaugeTransform hM hfr hA η c
  have g3 : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      interpolatedExpansion s a ρA m f y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) =
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, interpolatedExpansion s a ρA m f y η V :=
    Finset.sum_congr rfl fun y _ => hrow y
  rw [g1, g2, g3]
def rotateBondsCLE (A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector) :
    BondVariables F ≃L[ℝ] BondVariables F :=
  ContinuousLinearEquiv.piCongrRight fun b => (A b).toContinuousLinearEquiv
theorem rotateBondsCLE_apply (A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector)
    (η : BondVariables F) : rotateBondsCLE A η = rotateBonds A η := rfl
theorem bondPartialDeriv_rotateBonds {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    {G G' : BondVariables F → ℝ} {η : BondVariables F}
    (hG : ∀ᶠ ζ in 𝓝 η, G' (rotateBonds A ζ) = G ζ) (b : ↥(chordBonds (finiteCells F))) :
    bondPartialDeriv G' b (rotateBonds A η) (rotateBonds A η b) = bondPartialDeriv G b η (η b) := by
  classical
  have e1 : (fun ζ => G' (rotateBondsCLE A ζ)) =ᶠ[𝓝 η] G := hG
  have e2 := (rotateBondsCLE A).comp_right_fderiv (f := G') (x := η)
  have e3 : fderiv ℝ G η =
      (fderiv ℝ G' (rotateBondsCLE A η)).comp (rotateBondsCLE A : BondVariables F →L[ℝ] BondVariables F) := by
    rw [← e1.fderiv_eq]
    exact e2
  have e4 : (bondVariation b (rotateBonds A η b) : BondVariables F) =
      rotateBondsCLE A (bondVariation b (η b)) := by
    funext b'
    by_cases hb : b' = b
    · subst hb
      simp [bondVariation, rotateBondsCLE_apply, rotateBonds]
    · simp [bondVariation, rotateBondsCLE_apply, rotateBonds, Pi.single_eq_of_ne hb]
  unfold bondPartialDeriv
  rw [e4, e3]
  rfl
end Gauge
theorem dilationRemainder_gaugeInvariantAt (hCh : chartEquivarianceStatement)
    (hAd : AdjointActionLinearIsometry) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hT : T.IsOrdered) (hn : 2 ≤ T.n₀)
    {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
    (hfb : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFrameBoundsAt T Cq Cz Cr t x) :
    DilationRemainderGaugeInvariantAt T := by
  classical
  intro t x f F V Y γ hst
  have hx := hst.coupling_le
  have hF := hst.torus
  have hV := hst.small_curvature
  have hφ := hst.family_bounded
  have hFL := hF.1
  have hFt := hF.2.1
  obtain ⟨n, hside, hn'⟩ := hF.2.2
  have hodd : Odd F.blockSide := by
    rw [hFL]
    exact hT.odd_L
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside]
    omega
  have hM : ChartEquivariance F T.a := hCh F T.a hodd hs
  have hLow : IsCubicTorusAbove T.L t T.n₀ F := ⟨hFL, hFt, n, hside,
    le_trans hn' (Nat.le_mul_of_pos_right n hT.odd_L.pos)⟩
  have one := (hfb t x hx).one_torus F V 1 hF hV zero_le_one le_rfl
  have hσ := hT.σ_pos
  have hsmallη : ∀ η : BondVariables F, (∀ b, ‖η b‖ < T.ballRadius) →
      IsSmallCurvature T.σ (interpolatedField 1 T.a T.chainParams.ρA (frameRadius x) V η) := fun η hη => by
    have h2 := one.small.small_curvature_nearby η fun b => (hη b).le
    exact fun q hq => (h2 q hq).trans_le (by linarith)
  choose A hA using fun b : ↥(chordBonds (finiteCells F)) => hAd (γ (enclosingCell b.1.1))
  have hfr : ∀ b ∈ chordBonds (finiteCells F),
      interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) b (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) =
        _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) b V) :=
    fun b hb => Subtype.ext (one.small.gauge_covariant b hb γ)
  have hpres : MeasurePreserving (rotateBonds A) volume volume :=
    measurePreserving_pi _ _ fun b => (A b).measurePreserving
  have hemb : MeasurableEmbedding (rotateBonds A) := by
    have hhom : rotateBonds A = (Homeomorph.piCongrRight fun b => (A b).toHomeomorph) := by
      funext η b
      rfl
    rw [hhom]
    exact Homeomorph.measurableEmbedding _
  have hnorm : ∀ (η : BondVariables F) b, ‖rotateBonds A η b‖ = ‖η b‖ := fun η b => (A b).norm_map _
  have hrow : ∀ (y : F.Site F.depth) (η : BondVariables F), (∀ b, ‖η b‖ < T.ballRadius) →
      interpolatedExpansion 1 T.a T.chainParams.ρA (frameRadius x) f y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) =
        interpolatedExpansion 1 T.a T.chainParams.ρA (frameRadius x) f y η V := fun y η hη => by
    unfold interpolatedExpansion ColdStepAtMirrorFrames.subtractTrivial
    rw [_root_.YangMills.Construction.ResponseInTheExpansion.GaugeChangeOfVariables.interpolatedField_gaugeTransform hM hfr hA,
      hφ.gauge_invariant F hLow y _ (blockConstantGauge γ) (hsmallη η hη)]
  set Q := coldHalfLawAt T x f with hQ
  have hO : IsOpen {η : BondVariables F | ∀ b, ‖η b‖ < T.ballRadius} := by
    have : {η : BondVariables F | ∀ b, ‖η b‖ < T.ballRadius} =
        ⋂ b, {η : BondVariables F | ‖η b‖ < T.ballRadius} := by
      ext η; simp
    rw [this]
    exact isOpen_iInter_of_finite fun b =>
      isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
  have hgh : ∀ ζ : BondVariables F,
      Q.gapHaarExcess (rotateBonds A ζ) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = Q.gapHaarExcess ζ V := fun ζ => by
    unfold ColdHalfLaw.gapHaarExcess
    exact congrArg₂ (· + ·)
      (Finset.sum_congr rfl fun c _ => _root_.YangMills.Construction.ResponseInTheExpansion.GaugeChangeOfVariables.haarGapExcess_gaugeTransform hM hfr hA ζ c)
      (Finset.sum_congr rfl fun b _ =>
        _root_.YangMills.Construction.ResponseInTheExpansion.GaugeChangeOfVariables.haarLogRatio_gaugeTransform hM hfr hA ζ b (not_isAxialTreeBond_of_chord b))
  have hslope : ∀ (η : BondVariables F) (b : ↥(chordBonds (finiteCells F))) (ζ : BondVariables F),
      chartedSlope T.a (interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V)
        (rotateBonds A ζ)) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) b.1 (toImaginary (rotateBonds A η b)) =
      chartedSlope T.a (interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) V ζ) V b.1
        (toImaginary (η b)) := by
    intro η b ζ
    have h1 : toImaginary (rotateBonds A η b) =
        _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary (η b)) := hA b (η b)
    rw [h1]
    exact _root_.YangMills.Construction.ResponseInTheExpansion.GaugeChangeOfVariables.chartedSlope_gaugeTransform hM (_root_.YangMills.Construction.ResponseInTheExpansion.GaugeChangeOfVariables.interpolatedCoords_gaugeTransform hM hfr hA ζ) b.1
      (not_isAxialTreeBond_of_chord b) _
  have hrem : ∀ (η : BondVariables F) (b : ↥(chordBonds (finiteCells F))),
      Q.slopeRemainder b (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = Q.slopeRemainder b η V := by
    intro η b
    unfold ColdHalfLaw.slopeRemainder
    have h1 := hslope η b η
    have h2 : ∫ v in (0 : ℝ)..1, chartedSlope Q.a (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius
        (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (v • rotateBonds A η)) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) b.1
          (toImaginary (rotateBonds A η b)) =
        ∫ v in (0 : ℝ)..1, chartedSlope Q.a (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V
          (v • η)) V b.1 (toImaginary (η b)) := by
      refine intervalIntegral.integral_congr fun v _ => ?_
      show chartedSlope T.a (interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V)
          (v • rotateBonds A η)) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) b.1 (toImaginary (rotateBonds A η b)) =
        chartedSlope T.a (interpolatedCoords 1 T.a T.chainParams.ρA (frameRadius x) V (v • η)) V b.1
          (toImaginary (η b))
      rw [smul_rotateBonds]
      exact hslope η b (v • η)
    rw [h2]
    exact congrArg (fun z => z - _) h1
  have hparts : ∀ η : BondVariables F, (∀ b, ‖η b‖ < T.ballRadius) →
      - Q.cutoffTerm Y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) +
          Q.gapTerm Y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) +
          Q.familyTerm Y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) -
          Q.slopeTerm Y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) =
        - Q.cutoffTerm Y η V + Q.gapTerm Y η V + Q.familyTerm Y η V - Q.slopeTerm Y η V := by
    intro η hη
    have e1 : Q.cutoffTerm Y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = Q.cutoffTerm Y η V := by
      unfold ColdHalfLaw.cutoffTerm ColdHalfLaw.sumOverBlock
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [hnorm]
    have e2 : Q.gapTerm Y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = Q.gapTerm Y η V := by
      unfold ColdHalfLaw.gapTerm ColdHalfLaw.sumOverBlock
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs
      · exact bondPartialDeriv_rotateBonds (Filter.Eventually.of_forall hgh) b
      · rfl
    have e3 : Q.familyTerm Y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = Q.familyTerm Y η V := by
      unfold ColdHalfLaw.familyTerm
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun b _ => ?_
      refine bondPartialDeriv_rotateBonds ?_ b
      filter_upwards [hO.mem_nhds hη] with ζ hζ using hrow y ζ hζ
    have e4 : Q.slopeTerm Y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = Q.slopeTerm Y η V := by
      unfold ColdHalfLaw.slopeTerm ColdHalfLaw.sumOverBlock
      refine congrArg (fun z => Q.coupling * z) (Finset.sum_congr rfl fun b _ => ?_)
      split_ifs
      · exact hrem η b
      · rfl
    rw [e1, e2, e3, e4]
  unfold ColdHalfLaw.dilationRemainder
  refine congrArg (fun z => 1 / (2 * Q.coupling) * z) ?_
  exact cutoffMean_comp (ρ := T.ballRadius) (p := T.p) (Ψ' := Q.exponent (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V))
    (Ψ := Q.exponent V)
    (H' := fun η => - Q.cutoffTerm Y η (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) + Q.gapTerm Y η (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) +
      Q.familyTerm Y η (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) - Q.slopeTerm Y η (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V))
    (H := fun η => - Q.cutoffTerm Y η V + Q.gapTerm Y η V + Q.familyTerm Y η V - Q.slopeTerm Y η V)
    hpres hemb (fun η => by simp only [cutoffWeight, hnorm])
    (fun η hη => _root_.YangMills.Construction.ResponseInTheExpansion.GaugeChangeOfVariables.familyLawExponent_gaugeTransform hM hfr hA η fun y => hrow y η hη) hparts
theorem eventually_two_le_n₀ : EventuallyInParameters fun T => 2 ≤ T.n₀ := by apply _root_.YangMills.SharedProofs.p10519 <;> assumption
end GaugeChangeOfVariables
open GaugeChangeOfVariables in
theorem dilationRemainder_gaugeInvariant (hframes : interpolatedFramesStatement)
    (hJ : EventuallyInParametersCombines) (hCh : chartEquivarianceStatement)
    (hAd : AdjointActionLinearIsometry) : dilationRemainderGaugeInvariantStatement := by
  obtain ⟨Cq, Cz, Cr, hfb⟩ := hframes
  exact hJ.2 _ _ (fun T hT h => dilationRemainder_gaugeInvariantAt hCh hAd T hT h.1 h.2)
    (hJ.1 _ _ eventually_two_le_n₀ hfb)
end ResponseInTheExpansion
end
end YangMills.Construction
