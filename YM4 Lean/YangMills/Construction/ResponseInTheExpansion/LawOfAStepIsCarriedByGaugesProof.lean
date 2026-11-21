import YangMills.Construction.SummableBoundsOfTheFlow.MeansOfTheGapAreInvariantProof
import YangMills.Construction.ResponseInTheExpansion.LawOfAStepIsCarriedByGauges
import YangMills.Construction.SummableBoundsOfTheFlow.MeansOfTheWeightPartAreInvariantProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames MeasureTheory
namespace ResponseInTheExpansion
variable {F : BlockFrame}
namespace GaugeInvariance
private abbrev ChordVariable (F : BlockFrame) : Type := StepVariable (finiteCells F)
private theorem cutoffMean_comp {ρ : ℝ} {p : ℝ → ℝ} {R : ChordVariable F → ChordVariable F}
    (hR : MeasurePreserving R volume volume) (hemb : MeasurableEmbedding R)
    (hw : ∀ η, cutoffWeight ρ p (R η) = cutoffWeight ρ p η) {Φ Φ' G G' : ChordVariable F → ℝ}
    (hΦ : ∀ η, (∀ b, ‖η b‖ < ρ) → Φ' (R η) = Φ η) (hG : ∀ η, G' (R η) = G η) :
    cutoffMean ρ p Φ' G' = cutoffMean ρ p Φ G := by apply _root_.YangMills.Construction.BlockMeans.cutoffMean_comp <;> assumption
private theorem chartedField_congr {u u' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (U : F.GaugeField F.top)
    (hu : ∀ y j, ¬ IsAxialTreeBond (y, j) → u y j = u' y j) :
    chartedField u U = chartedField u' U := by apply _root_.YangMills.SharedProofs.p16263 <;> assumption
private theorem adjointAction_add (g : UnitQuaternion) (X Y : imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (X + Y) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X + _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g Y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add <;> assumption
private theorem norm_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) :
    ‖_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X‖ = ‖X‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction <;> assumption
section Gauge
variable {a ρA κ : ℝ} {m : ℕ} {f : LocalFamily} {U : F.GaugeField F.top}
  {γ : F.Cell → UnitQuaternion}
private theorem chartedEnergy_adjoint (hM : ChartEquivariance F a)
    {u u' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hu : ∀ y j, ¬ IsAxialTreeBond (y, j) → u' y j = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (u y j)) :
    chartedEnergy a u' (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) = chartedEnergy a u U := by apply _root_.YangMills.SharedProofs.p19410 <;> assumption
private def rotateBonds (A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector)
    (η : ChordVariable F) : ChordVariable F :=
  fun b => A b (η b)
private theorem coordsAboveFrame_rotate (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame false a ρA m b (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame false a ρA m b U))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : ChordVariable F) (y : F.Site F.depth) (j : Fin 4) (hnt : ¬ IsAxialTreeBond (y, j)) :
    coordsAboveFrame false a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) (rotateBonds A η) y j =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (coordsAboveFrame false a ρA m U η y j) := by
  have hb : (y, j) ∈ chordBonds (finiteCells F) := hM.mem_chordBonds_of_not_tree _ hnt
  unfold coordsAboveFrame stepCoordinates
  rw [dif_pos hb, dif_pos hb, hfr _ hb, adjointAction_add]
  congr 1
  exact hA ⟨(y, j), hb⟩ (η ⟨(y, j), hb⟩)
private theorem fieldAboveFrame_rotate (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame false a ρA m b (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame false a ρA m b U))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : ChordVariable F) :
    fieldAboveFrame false a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) (rotateBonds A η) =
      _root_.YangMills.Construction.BlockAverages.gaugeTransform (blockConstantGauge γ) (fieldAboveFrame false a ρA m U η) := by
  unfold fieldAboveFrame
  rw [chartedField_congr (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) (coordsAboveFrame_rotate hM hfr hA η),
    hM.chartedField_gaugeTransform]
private theorem haarGapExcess_rotate (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame false a ρA m b (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame false a ρA m b U))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : ChordVariable F) (c : F.Site F.top × Fin 4) :
    haarGapExcess a κ (fieldAboveFrame false a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) (rotateBonds A η)) c =
      haarGapExcess a κ (fieldAboveFrame false a ρA m U η) c := by
  unfold haarGapExcess
  rw [fieldAboveFrame_rotate hM hfr hA, hM.norm_contourAverage_gaugeTransform]
private theorem haarLogRatio_rotate (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame false a ρA m b (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame false a ρA m b U))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : ChordVariable F) (b : ↥(chordBonds (finiteCells F))) (hnt : ¬ IsAxialTreeBond b.1) :
    haarLogRatio (coordsAboveFrame false a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) (rotateBonds A η) b.1.1 b.1.2) =
      haarLogRatio (coordsAboveFrame false a ρA m U η b.1.1 b.1.2) := by
  unfold haarLogRatio
  rw [coordsAboveFrame_rotate hM hfr hA η _ _ hnt, norm_adjointAction]
private theorem rotateBonds_zero
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector} :
    rotateBonds A (0 : ChordVariable F) = 0 := by
  funext b
  simp [rotateBonds]
private theorem not_isAxialTreeBond_of_chord (b : ↥(chordBonds (finiteCells F))) :
    ¬ IsAxialTreeBond b.1 := by apply _root_.YangMills.SharedProofs.p29908 <;> assumption
private theorem stepExponent_rotate (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame false a ρA m b (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame false a ρA m b U))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    {ρ : ℝ} (ν : ℝ)
    (hrow : ∀ (y : F.Site F.depth) (η : ChordVariable F), (∀ b, ‖η b‖ < ρ) →
      centredExpansion false a ρA m f y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) =
        centredExpansion false a ρA m f y η U)
    (η : ChordVariable F) (hη : ∀ b, ‖η b‖ < ρ) :
    stepExponent false a ρA κ m f ν (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) (rotateBonds A η) =
      stepExponent false a ρA κ m f ν U η := by
  have hzero : ∀ η : ChordVariable F,
      chartedEnergy a (coordsAboveFrame false a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) (rotateBonds A η))
        (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) = chartedEnergy a (coordsAboveFrame false a ρA m U η) U := fun η =>
    chartedEnergy_adjoint hM (coordsAboveFrame_rotate hM hfr hA η)
  unfold stepExponent
  have h0 := hzero 0
  rw [rotateBonds_zero] at h0
  rw [hzero η, h0]
  have g1 : ∑ b : ↥(chordBonds (finiteCells F)),
      haarLogRatio (coordsAboveFrame false a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) (rotateBonds A η) b.1.1 b.1.2) =
      ∑ b : ↥(chordBonds (finiteCells F)),
        haarLogRatio (coordsAboveFrame false a ρA m U η b.1.1 b.1.2) :=
    Finset.sum_congr rfl fun b _ => haarLogRatio_rotate hM hfr hA η b (not_isAxialTreeBond_of_chord b)
  have g2 : ∑ c ∈ innerBonds (finiteCells F) F.top,
      haarGapExcess a κ (fieldAboveFrame false a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) (rotateBonds A η)) c =
      ∑ c ∈ innerBonds (finiteCells F) F.top, haarGapExcess a κ (fieldAboveFrame false a ρA m U η) c :=
    Finset.sum_congr rfl fun c _ => haarGapExcess_rotate hM hfr hA η c
  have g3 : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      centredExpansion false a ρA m f y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ U) =
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false a ρA m f y η U :=
    Finset.sum_congr rfl fun y _ => hrow y η hη
  rw [g1, g2, g3]
end Gauge
end GaugeInvariance
open GaugeInvariance in
theorem stepLawGaugeInvariant (hCh : chartEquivarianceStatement)
    (hAd : AdjointActionLinearIsometry) :
    stepLawGaugeInvariantStatement := by
  intro T hTL hn₂ hσ hfr' t x hx f hf F hF V hV γ H
  obtain ⟨hg, -, hab⟩ := hfr' t x hx F V hF hV
  have hFL := hF.1
  have hFt := hF.2.1
  obtain ⟨n, hside, hn⟩ := hF.2.2
  have hodd : Odd F.blockSide := by rw [hFL]; exact hTL
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside]
    omega
  have hM : ChartEquivariance F T.a := hCh F T.a hodd hs
  have hLow : IsCubicTorusAbove T.L t T.n₀ F := ⟨hFL, hFt, n, hside,
    le_trans hn (Nat.le_mul_of_pos_right n hTL.pos)⟩
  have hcold : ∀ η : ChordVariable F, (∀ b, ‖η b‖ < T.ballRadius) →
      IsSmallCurvature T.σ (fieldAboveFrame false T.a T.chainParams.ρA (frameRadius x) V η) :=
    fun η hη p hp => ((hab η fun b => (hη b).le).1 p hp).trans_le (by linarith)
  choose A hA using fun b : ↥(chordBonds (finiteCells F)) => hAd (γ (enclosingCell b.1.1))
  have hfr : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame false T.a T.chainParams.ρA (frameRadius x) b (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) =
        _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame false T.a T.chainParams.ρA (frameRadius x) b V) :=
    fun b hb => hg γ b hb
  have hrow : ∀ (y : F.Site F.depth) (η : ChordVariable F), (∀ b, ‖η b‖ < T.ballRadius) →
      centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) =
        centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y η V := fun y η hη => by
    unfold centredExpansion ColdStepAtMirrorFrames.subtractTrivial
    rw [fieldAboveFrame_rotate hM hfr hA, hf.gauge_invariant F hLow y _ (blockConstantGauge γ) (hcold η hη)]
  have hpres : MeasurePreserving (rotateBonds A) volume volume :=
    measurePreserving_pi _ _ fun b => (A b).measurePreserving
  have hemb : MeasurableEmbedding (rotateBonds A) := by
    have hhom : rotateBonds A = (Homeomorph.piCongrRight fun b => (A b).toHomeomorph) := by
      funext η b
      rfl
    rw [hhom]
    exact Homeomorph.measurableEmbedding _
  have hnorm : ∀ (η : ChordVariable F) b, ‖rotateBonds A η b‖ = ‖η b‖ := fun η b => (A b).norm_map _
  have hturn : ∀ η : ChordVariable F, adjointStepVariable γ η = rotateBonds A η := fun η => by
    funext b
    unfold adjointStepVariable rotateBonds
    rw [← hA b (η b)]
    ext i
    fin_cases i <;> simp [imaginaryCoords, toImaginary]
  refine cutoffMean_comp hpres hemb (fun η => by simp only [cutoffWeight, hnorm])
    (fun η hη => stepExponent_rotate hM hfr hA 1 hrow η hη) fun η => congrArg H (hturn η).symm
end ResponseInTheExpansion
end YangMills.Construction
end
