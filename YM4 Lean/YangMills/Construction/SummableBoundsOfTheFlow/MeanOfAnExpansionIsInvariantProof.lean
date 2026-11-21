import YangMills.Construction.SummableBoundsOfTheFlow.MeansOfTheWeightPartAreInvariantProof
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfTheStepAreInvariantProof
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOfAnExpansionIsInvariant
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open scoped Quaternion
open BlockAverages ColdStepAtMirrorFrames MeasureTheory
namespace Estimates
variable {F : BlockFrame}
namespace ExpansionMean
abbrev StepVars (F : BlockFrame) : Type := StepVariable (finiteCells F)
theorem cutoffMean_comp_measurePreserving {ρ : ℝ} {p : ℝ → ℝ} {R : StepVars F → StepVars F}
    (hR : MeasurePreserving R volume volume) (hemb : MeasurableEmbedding R)
    (hcut : ∀ η, cutoffWeight ρ p (R η) = cutoffWeight ρ p η) {Ψ Ψ' H H' : StepVars F → ℝ}
    (hΨ : ∀ η, (∀ b, ‖η b‖ < ρ) → Ψ' (R η) = Ψ η) (hH : ∀ η, (∀ b, ‖η b‖ < ρ) → H' (R η) = H η) :
    cutoffMean ρ p Ψ' H' = cutoffMean ρ p Ψ H := by apply _root_.YangMills.DeltaSharedProofs.p500520 <;> assumption
theorem chartedField_congr {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions} (V : F.GaugeField F.top)
    (hw : ∀ x i, ¬ IsAxialTreeBond (x, i) → w x i = w' x i) : chartedField w V = chartedField w' V := by apply _root_.YangMills.SharedProofs.p16263 <;> assumption
theorem adjointAction_add (g : UnitQuaternion) (X Y : imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (X + Y) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X + _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g Y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add <;> assumption
theorem norm_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) : ‖_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X‖ = ‖X‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction <;> assumption
section Gauge
variable {star : Bool} {a ρA x : ℝ} {m : ℕ} {V : F.GaugeField F.top} {γ : F.Cell → UnitQuaternion}
theorem chartedEnergy_gaugeTransform (hM : ChartEquivariance F a)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ y i, ¬ IsAxialTreeBond (y, i) → w' y i = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (w y i)) :
    chartedEnergy a w' (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = chartedEnergy a w V := by apply _root_.YangMills.SharedProofs.p19410 <;> assumption
def rotateBonds (A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector) (η : StepVars F) :
    StepVars F :=
  fun b => A b (η b)
theorem coordsAboveFrame_gaugeTransform (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame star a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame star a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : StepVars F) (y : F.Site F.depth) (i : Fin 4) (hnt : ¬ IsAxialTreeBond (y, i)) :
    coordsAboveFrame star a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateBonds A η) y i =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (coordsAboveFrame star a ρA m V η y i) := by
  have hb : (y, i) ∈ chordBonds (finiteCells F) := hM.mem_chordBonds_of_not_tree _ hnt
  unfold coordsAboveFrame stepCoordinates
  rw [dif_pos hb, dif_pos hb, hfr _ hb, _root_.YangMills.Construction.Estimates.ExpansionMean.adjointAction_add]
  congr 1
  exact hA ⟨(y, i), hb⟩ (η ⟨(y, i), hb⟩)
theorem fieldAboveFrame_gaugeTransform (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame star a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame star a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : StepVars F) :
    fieldAboveFrame star a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateBonds A η) =
      _root_.YangMills.Construction.BlockAverages.gaugeTransform (blockConstantGauge γ) (fieldAboveFrame star a ρA m V η) := by
  unfold fieldAboveFrame
  rw [chartedField_congr (gaugeTransform γ V) (_root_.YangMills.Construction.Estimates.ExpansionMean.coordsAboveFrame_gaugeTransform hM hfr hA η),
    hM.chartedField_gaugeTransform]
theorem haarGapExcess_gaugeTransform (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame star a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame star a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : StepVars F) (c : F.Site F.top × Fin 4) :
    haarGapExcess a x (fieldAboveFrame star a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateBonds A η)) c =
      haarGapExcess a x (fieldAboveFrame star a ρA m V η) c := by
  unfold haarGapExcess
  rw [_root_.YangMills.Construction.Estimates.ExpansionMean.fieldAboveFrame_gaugeTransform hM hfr hA, hM.norm_contourAverage_gaugeTransform]
theorem haarLogRatio_gaugeTransform (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame star a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame star a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : StepVars F) (b : ↥(chordBonds (finiteCells F))) (hnt : ¬ IsAxialTreeBond b.1) :
    haarLogRatio (coordsAboveFrame star a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateBonds A η) b.1.1 b.1.2) =
      haarLogRatio (coordsAboveFrame star a ρA m V η b.1.1 b.1.2) := by
  unfold haarLogRatio
  rw [_root_.YangMills.Construction.Estimates.ExpansionMean.coordsAboveFrame_gaugeTransform hM hfr hA η _ _ hnt, norm_adjointAction]
theorem rotateBonds_zero {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector} :
    rotateBonds A (0 : StepVars F) = 0 := by
  funext b
  simp [rotateBonds]
theorem not_isAxialTreeBond_of_chord (b : ↥(chordBonds (finiteCells F))) : ¬ IsAxialTreeBond b.1 := by apply _root_.YangMills.SharedProofs.p29908 <;> assumption
theorem cutoffMean_gaugeTransform {ρ : ℝ} {p : ℝ → ℝ} {φ f : LocalFamily} (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame star a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame star a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (Y : F.Cell)
    (hφ : ∀ (y : F.Site F.depth) (η : StepVars F), (∀ b, ‖η b‖ < ρ) →
      centredExpansion star a ρA m φ y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = centredExpansion star a ρA m φ y η V)
    (hf : ∀ (y : F.Site F.depth) (η : StepVars F), (∀ b, ‖η b‖ < ρ) →
      centredExpansion star a ρA m f y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = centredExpansion star a ρA m f y η V) :
    cutoffMean ρ p (stepExponent star a ρA x m φ 1 (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V))
        (fun η => cellCentredExpansion star a ρA m f Y η (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V)) =
      cutoffMean ρ p (stepExponent star a ρA x m φ 1 V) (fun η => cellCentredExpansion star a ρA m f Y η V) := by
  have hpres : MeasurePreserving (rotateBonds A) volume volume :=
    measurePreserving_pi _ _ fun b => (A b).measurePreserving
  have hemb : MeasurableEmbedding (rotateBonds A) := by
    have hhom : rotateBonds A = (Homeomorph.piCongrRight fun b => (A b).toHomeomorph) := by
      funext η b
      rfl
    rw [hhom]
    exact Homeomorph.measurableEmbedding _
  have hnorm : ∀ (η : StepVars F) b, ‖rotateBonds A η b‖ = ‖η b‖ := fun η b => (A b).norm_map _
  have hzero : ∀ η : StepVars F, chartedEnergy a (coordsAboveFrame star a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateBonds A η))
      (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = chartedEnergy a (coordsAboveFrame star a ρA m V η) V := fun η =>
    _root_.YangMills.Construction.Estimates.ExpansionMean.chartedEnergy_gaugeTransform hM (_root_.YangMills.Construction.Estimates.ExpansionMean.coordsAboveFrame_gaugeTransform hM hfr hA η)
  refine cutoffMean_comp_measurePreserving hpres hemb (fun η => by simp only [cutoffWeight, hnorm])
    (fun η hη => ?_) (fun η hη => ?_)
  · unfold stepExponent
    have h0 := hzero 0
    rw [rotateBonds_zero] at h0
    rw [hzero η, h0]
    have g1 : ∑ b : ↥(chordBonds (finiteCells F)),
        haarLogRatio (coordsAboveFrame star a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateBonds A η) b.1.1 b.1.2) =
        ∑ b : ↥(chordBonds (finiteCells F)), haarLogRatio (coordsAboveFrame star a ρA m V η b.1.1 b.1.2) :=
      Finset.sum_congr rfl fun b _ => _root_.YangMills.Construction.Estimates.ExpansionMean.haarLogRatio_gaugeTransform hM hfr hA η b (not_isAxialTreeBond_of_chord b)
    have g2 : ∑ c ∈ innerBonds (finiteCells F) F.top,
        haarGapExcess a x (fieldAboveFrame star a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateBonds A η)) c =
        ∑ c ∈ innerBonds (finiteCells F) F.top, haarGapExcess a x (fieldAboveFrame star a ρA m V η) c :=
      Finset.sum_congr rfl fun c _ => _root_.YangMills.Construction.Estimates.ExpansionMean.haarGapExcess_gaugeTransform hM hfr hA η c
    have g3 : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
        centredExpansion star a ρA m φ y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) =
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion star a ρA m φ y η V :=
      Finset.sum_congr rfl fun y _ => hφ y η hη
    rw [g1, g2, g3]
  · unfold cellCentredExpansion
    exact Finset.sum_congr rfl fun y _ => hf y η hη
end Gauge
section Shift
variable {star : Bool} {a ρA x : ℝ} {m : ℕ} {V : F.GaugeField F.top} {h : F.Cell}
def chordTranslate (hM : ChartEquivariance F a) (h : F.Cell) :
    ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F)) where
  toFun b := ⟨(b.1.1 + cellCentre F.depth h, b.1.2), (hM.chordBonds_translate h b.1).mpr b.2⟩
  invFun b := ⟨(b.1.1 - cellCentre F.depth h, b.1.2),
    (hM.chordBonds_translate h (b.1.1 - cellCentre F.depth h, b.1.2)).mp (by simpa using b.2)⟩
  left_inv b := Subtype.ext (by simp)
  right_inv b := Subtype.ext (by simp)
def translateVars (e : ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F))) (η : StepVars F) :
    StepVars F :=
  fun b => η (e.symm b)
theorem translateVars_eq_piCongrLeft (e : ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F))) :
    translateVars e =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) e) := by
  funext η b
  obtain ⟨b', rfl⟩ := e.surjective b
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp [translateVars]
theorem chartedEnergy_translate (hM : ChartEquivariance F a)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ y i, ¬ IsAxialTreeBond (y, i) → w' y i = w (y - cellCentre F.depth h) i) :
    chartedEnergy a w' (translateField h V) = chartedEnergy a w V := by apply _root_.YangMills.SharedProofs.p9314 <;> assumption
theorem coordsAboveFrame_translate (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame star a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) = stepFrame star a ρA m b V)
    (η : StepVars F) (y : F.Site F.depth) (i : Fin 4) (hnt : ¬ IsAxialTreeBond (y, i)) :
    coordsAboveFrame star a ρA m (translateField h V) (translateVars (chordTranslate hM h) η) y i =
      coordsAboveFrame star a ρA m V η (y - cellCentre F.depth h) i := by
  have hb : (y, i) ∈ chordBonds (finiteCells F) := hM.mem_chordBonds_of_not_tree _ hnt
  have hb0 : (y - cellCentre F.depth h, i) ∈ chordBonds (finiteCells F) :=
    (hM.chordBonds_translate h (y - cellCentre F.depth h, i)).mp (by simpa using hb)
  have hf := hcar _ hb0
  simp only [sub_add_cancel] at hf
  unfold coordsAboveFrame stepCoordinates
  rw [dif_pos hb, dif_pos hb0, hf]
  rfl
theorem fieldAboveFrame_translate (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame star a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) = stepFrame star a ρA m b V)
    (η : StepVars F) :
    fieldAboveFrame star a ρA m (translateField h V) (translateVars (chordTranslate hM h) η) =
      translateField (cellCentre F.depth h) (fieldAboveFrame star a ρA m V η) := by
  unfold fieldAboveFrame
  rw [chartedField_congr (translateField h V) (coordsAboveFrame_translate hM hcar η), hM.chartedField_translate]
theorem haarGapExcess_translate (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame star a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) = stepFrame star a ρA m b V)
    (η : StepVars F) (c : F.Site F.top × Fin 4) :
    haarGapExcess a x (fieldAboveFrame star a ρA m (translateField h V) (translateVars (chordTranslate hM h) η)) c =
      haarGapExcess a x (fieldAboveFrame star a ρA m V η) (c.1 - h, c.2) := by
  unfold haarGapExcess
  rw [fieldAboveFrame_translate hM hcar, hM.contourAverage_translate]
theorem sum_innerBonds_sub (hM : ChartEquivariance F a) (h : F.Cell) (G : F.Site F.top × Fin 4 → ℝ) :
    ∑ c ∈ innerBonds (finiteCells F) F.top, G (c.1 - h, c.2) = ∑ c ∈ innerBonds (finiteCells F) F.top, G c := by apply _root_.YangMills.SharedProofs.p4672 <;> assumption
theorem sum_sitesOfCells_sub (hM : ChartEquivariance F a) (h : F.Cell) (G : F.Site F.depth → ℝ) :
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, G (y - cellCentre F.depth h) =
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, G y := by apply _root_.YangMills.SharedProofs.p5113 <;> assumption
theorem translateVars_zero (e : ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F))) :
    translateVars e (0 : StepVars F) = 0 := rfl
theorem cutoffMean_translate {ρ : ℝ} {p : ℝ → ℝ} {φ f : LocalFamily} (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame star a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) = stepFrame star a ρA m b V)
    (Y : F.Cell)
    (hφ : ∀ (y : F.Site F.depth) (η : StepVars F), (∀ b, ‖η b‖ < ρ) →
      centredExpansion star a ρA m φ y (translateVars (chordTranslate hM h) η) (translateField h V) =
        centredExpansion star a ρA m φ (y - cellCentre F.depth h) η V)
    (hf : ∀ (y : F.Site F.depth) (η : StepVars F), (∀ b, ‖η b‖ < ρ) →
      centredExpansion star a ρA m f y (translateVars (chordTranslate hM h) η) (translateField h V) =
        centredExpansion star a ρA m f (y - cellCentre F.depth h) η V) :
    cutoffMean ρ p (stepExponent star a ρA x m φ 1 (translateField h V))
        (fun η => cellCentredExpansion star a ρA m f (Y + h) η (translateField h V)) =
      cutoffMean ρ p (stepExponent star a ρA x m φ 1 V) (fun η => cellCentredExpansion star a ρA m f Y η V) := by
  set e := chordTranslate hM h with he
  have happ : ∀ (η : StepVars F) b, translateVars e η (e b) = η b := fun η b => by simp [translateVars]
  have hY : ∀ Z : F.Cell, Z + h = Y + h ↔ Z = Y := fun Z => add_left_inj h
  have hhaarAt : ∀ (η : StepVars F) (b : ↥(chordBonds (finiteCells F))),
      haarLogRatio (coordsAboveFrame star a ρA m (translateField h V) (translateVars e η) (e b).1.1 (e b).1.2) =
        haarLogRatio (coordsAboveFrame star a ρA m V η b.1.1 b.1.2) := fun η b => by
    have hnt : ¬ IsAxialTreeBond (e b).1 := not_isAxialTreeBond_of_chord _
    have h1 := coordsAboveFrame_translate hM hcar η (e b).1.1 (e b).1.2 hnt
    have h2 : (e b).1.1 - cellCentre F.depth h = b.1.1 := by simp [he, chordTranslate]
    have h3 : (e b).1.2 = b.1.2 := rfl
    rw [h2, h3] at h1
    rw [h3, h1]
  have hzero : ∀ η : StepVars F,
      chartedEnergy a (coordsAboveFrame star a ρA m (translateField h V) (translateVars e η)) (translateField h V) =
        chartedEnergy a (coordsAboveFrame star a ρA m V η) V := fun η =>
    chartedEnergy_translate hM (coordsAboveFrame_translate hM hcar η)
  have hpres : MeasurePreserving (translateVars e) volume volume := by
    rw [translateVars_eq_piCongrLeft]
    exact volume_measurePreserving_piCongrLeft _ e
  have hemb : MeasurableEmbedding (translateVars e) := by
    rw [translateVars_eq_piCongrLeft]
    exact MeasurableEquiv.measurableEmbedding _
  have hcut : ∀ η, cutoffWeight ρ p (translateVars e η) = cutoffWeight ρ p η := fun η => by
    unfold cutoffWeight
    rw [← Equiv.prod_comp e]
    exact Finset.prod_congr rfl fun b _ => by rw [happ]
  refine cutoffMean_comp_measurePreserving hpres hemb hcut (fun η hη => ?_) (fun η hη => ?_)
  · unfold stepExponent
    have h0 := hzero 0
    rw [translateVars_zero] at h0
    rw [hzero η, h0]
    have g1 : ∑ c ∈ innerBonds (finiteCells F) F.top,
        haarGapExcess a x (fieldAboveFrame star a ρA m (translateField h V) (translateVars e η)) c =
        ∑ c ∈ innerBonds (finiteCells F) F.top, haarGapExcess a x (fieldAboveFrame star a ρA m V η) c := by
      simp only [he, haarGapExcess_translate hM hcar η]
      exact sum_innerBonds_sub hM h fun c => haarGapExcess a x (fieldAboveFrame star a ρA m V η) c
    have g2 : ∑ b : ↥(chordBonds (finiteCells F)),
        haarLogRatio (coordsAboveFrame star a ρA m (translateField h V) (translateVars e η) b.1.1 b.1.2) =
        ∑ b : ↥(chordBonds (finiteCells F)), haarLogRatio (coordsAboveFrame star a ρA m V η b.1.1 b.1.2) := by
      rw [← Equiv.sum_comp e]
      exact Finset.sum_congr rfl fun b _ => hhaarAt η b
    have g3 : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
        centredExpansion star a ρA m φ y (translateVars e η) (translateField h V) =
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion star a ρA m φ y η V := by
      rw [Finset.sum_congr rfl fun y _ => hφ y η hη]
      exact sum_sitesOfCells_sub hM h fun y => centredExpansion star a ρA m φ y η V
    rw [g1, g2, g3]
  · unfold cellCentredExpansion
    rw [Finset.sum_filter, Finset.sum_filter,
      ← sum_sitesOfCells_sub hM h fun y => if enclosingCell y = Y then centredExpansion star a ρA m f y η V else 0]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hc : enclosingCell y = enclosingCell (y - cellCentre F.depth h) + h := by
      rw [← hM.enclosingCell_translate h (y - cellCentre F.depth h), sub_add_cancel]
    have hc2 : enclosingCell (y - cellCentre F.depth h) = Y ↔ enclosingCell y = Y + h := by
      rw [hc, hY]
    simp only [hc2]
    split_ifs
    · exact hf y η hη
    · rfl
end Shift
end ExpansionMean
open ExpansionMean in
theorem conditionalExpansionMeanInvariant (hAd : AdjointActionLinearIsometry) :
    conditionalExpansionMeanInvariantStatement := by
  intro F star a ρA x ρ m p φ f V σ hM hcold hσ hφ hf
  have hflat : IsSmallCurvature σ (uniformField F F.depth) := fun q _ => by
    have : plaquetteDefect (uniformField F F.depth) q = 0 := by
      simp [plaquetteDefect, plaquetteHolonomy, pathHolonomy, linkValue, uniformField]
    rw [this]
    exact hσ
  refine ⟨fun γ Y hfr => ?_, fun Y h hcar => ?_⟩
  · choose A hA using fun b : ↥(chordBonds (finiteCells F)) => hAd (γ (enclosingCell b.1.1))
    have row : ∀ g : LocalFamily, (∀ (y : F.Site F.depth) (W : F.GaugeField F.depth)
        (γ' : F.Site F.depth → UnitQuaternion),
        IsSmallCurvature σ W → g F y (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ' W) = g F y W) →
        ∀ (y : F.Site F.depth) (η : StepVars F), (∀ b, ‖η b‖ < ρ) →
        centredExpansion star a ρA m g y (rotateBonds A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = centredExpansion star a ρA m g y η V :=
      fun g hg y η hη => by
        unfold centredExpansion subtractTrivial
        rw [_root_.YangMills.Construction.Estimates.ExpansionMean.fieldAboveFrame_gaugeTransform hM hfr hA, hg y _ (blockConstantGauge γ) (hcold η hη)]
    exact _root_.YangMills.Construction.Estimates.ExpansionMean.cutoffMean_gaugeTransform hM hfr hA Y (row φ hφ.1) (row f hf.1)
  · have row : ∀ g : LocalFamily, (∀ (y h' : F.Site F.depth) (W : F.GaugeField F.depth),
        IsSmallCurvature σ W → g F (y + h') (translateField h' W) = g F y W) →
        ∀ (y : F.Site F.depth) (η : StepVars F), (∀ b, ‖η b‖ < ρ) →
        centredExpansion star a ρA m g y (translateVars (chordTranslate hM h) η) (translateField h V) =
          centredExpansion star a ρA m g (y - cellCentre F.depth h) η V := fun g hg y η hη => by
      have h1 := hg (y - cellCentre F.depth h) (cellCentre F.depth h) _ (hcold η hη)
      have h2 := hg (y - cellCentre F.depth h) (cellCentre F.depth h) _ hflat
      rw [sub_add_cancel] at h1 h2
      unfold centredExpansion subtractTrivial
      rw [fieldAboveFrame_translate hM hcar, h1]
      congr 1
    exact cutoffMean_translate hM hcar Y (row φ hφ.2) (row f hf.2)
end Estimates
end YangMills.Construction
end
