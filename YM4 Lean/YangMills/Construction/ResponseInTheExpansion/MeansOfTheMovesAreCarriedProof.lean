import YangMills.Construction.SummableBoundsOfTheFlow.MeansOfTheWeightPartAreInvariantProof
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyUnderGaugesAndShifts
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfTheStepAreInvariantProof
import YangMills.Construction.ResponseInTheExpansion.MeansOfTheMovesAreCarried
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.WeightedResponses MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
variable {F : BlockFrame}
namespace ExpectationsEquivariant
abbrev StepVars (F : BlockFrame) : Type := StepVariable (finiteCells F)
theorem cutoffMean_comp {r : ℝ} {q : ℝ → ℝ} {R : StepVars F → StepVars F}
    (hR : MeasurePreserving R volume volume) (hemb : MeasurableEmbedding R)
    (hw : ∀ η, cutoffWeight r q (R η) = cutoffWeight r q η) {Ψ Ψ' H H' : StepVars F → ℝ}
    (hΨ : ∀ η, (∀ b, ‖η b‖ < r) → Ψ' (R η) = Ψ η) (hH : ∀ η, (∀ b, ‖η b‖ < r) → H' (R η) = H η) :
    cutoffMean r q Ψ' H' = cutoffMean r q Ψ H := by apply _root_.YangMills.DeltaSharedProofs.p500520 <;> assumption
theorem chartedField_congr {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions} (V : F.GaugeField F.top)
    (hw : ∀ x i, ¬ IsAxialTreeBond (x, i) → w x i = w' x i) : chartedField w V = chartedField w' V := by apply _root_.YangMills.SharedProofs.p16263 <;> assumption
theorem adjointAction_add (g : UnitQuaternion) (X Y : imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (X + Y) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X + _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g Y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add <;> assumption
theorem norm_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) : ‖_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X‖ = ‖X‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction <;> assumption
section Gauge
variable {mirrored : Bool} {a ρA x : ℝ} {m : ℕ} {V : F.GaugeField F.top} {γ : F.Cell → UnitQuaternion}
theorem chartedEnergy_gauge (hM : ChartEquivariance F a) {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ y i, ¬ IsAxialTreeBond (y, i) → w' y i = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (w y i)) :
    chartedEnergy a w' (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = chartedEnergy a w V := by apply _root_.YangMills.SharedProofs.p19410 <;> assumption
theorem chartedSlope_gauge (hM : ChartEquivariance F a) {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ y i, ¬ IsAxialTreeBond (y, i) → w' y i = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (w y i))
    (b : F.Site F.depth × Fin 4) (hb : ¬ IsAxialTreeBond b) (e : imaginaryQuaternions) :
    chartedSlope a w' (gaugeTransform γ V) b (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) e) =
      chartedSlope a w V b e := by apply _root_.YangMills.SharedProofs.p24183 <;> assumption
def rotateVars (A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector) (η : StepVars F) :
    StepVars F :=
  fun b => A b (η b)
theorem coordsAboveFrame_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame mirrored a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame mirrored a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : StepVars F) (y : F.Site F.depth) (i : Fin 4) (hnt : ¬ IsAxialTreeBond (y, i)) :
    coordsAboveFrame mirrored a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateVars A η) y i =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (coordsAboveFrame mirrored a ρA m V η y i) := by
  have hb : (y, i) ∈ chordBonds (finiteCells F) := hM.mem_chordBonds_of_not_tree _ hnt
  unfold coordsAboveFrame stepCoordinates
  rw [dif_pos hb, dif_pos hb, hfr _ hb, _root_.YangMills.Construction.ResponseInTheExpansion.ExpectationsEquivariant.adjointAction_add]
  congr 1
  exact hA ⟨(y, i), hb⟩ (η ⟨(y, i), hb⟩)
theorem fieldAboveFrame_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame mirrored a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame mirrored a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : StepVars F) :
    fieldAboveFrame mirrored a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateVars A η) =
      _root_.YangMills.Construction.BlockAverages.gaugeTransform (blockConstantGauge γ) (fieldAboveFrame mirrored a ρA m V η) := by
  unfold fieldAboveFrame
  rw [chartedField_congr (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (coordsAboveFrame_gauge hM hfr hA η),
    hM.chartedField_gaugeTransform]
theorem haarGapExcess_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame mirrored a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame mirrored a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : StepVars F) (c : F.Site F.top × Fin 4) :
    haarGapExcess a x (fieldAboveFrame mirrored a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateVars A η)) c =
      haarGapExcess a x (fieldAboveFrame mirrored a ρA m V η) c := by
  unfold haarGapExcess
  rw [fieldAboveFrame_gauge hM hfr hA, hM.norm_contourAverage_gaugeTransform]
theorem haarLogRatio_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame mirrored a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame mirrored a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : StepVars F) (b : ↥(chordBonds (finiteCells F))) (hnt : ¬ IsAxialTreeBond b.1) :
    haarLogRatio (coordsAboveFrame mirrored a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateVars A η) b.1.1 b.1.2) =
      haarLogRatio (coordsAboveFrame mirrored a ρA m V η b.1.1 b.1.2) := by
  unfold haarLogRatio
  rw [coordsAboveFrame_gauge hM hfr hA η _ _ hnt, norm_adjointAction]
theorem smul_rotateVars {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector} (v : ℝ)
    (η : StepVars F) : v • rotateVars A η = rotateVars A (v • η) := by
  funext b
  simp [rotateVars]
theorem rotateVars_zero {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector} :
    rotateVars A (0 : StepVars F) = 0 := by
  funext b
  simp [rotateVars]
theorem not_isAxialTreeBond_of_chord (b : ↥(chordBonds (finiteCells F))) : ¬ IsAxialTreeBond b.1 := by apply _root_.YangMills.SharedProofs.p29908 <;> assumption
theorem cutoffMean_gauge {r : ℝ} {q : ℝ → ℝ} {φ : LocalFamily} (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame mirrored a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame mirrored a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (hφ : ∀ (y : F.Site F.depth) (η : StepVars F), (∀ b, ‖η b‖ < r) →
      centredExpansion mirrored a ρA m φ y (rotateVars A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = centredExpansion mirrored a ρA m φ y η V)
    {H H' : StepVars F → ℝ} (hH : ∀ η : StepVars F, (∀ b, ‖η b‖ < r) → H' (rotateVars A η) = H η) :
    cutoffMean r q (stepExponent mirrored a ρA x m φ 1 (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V)) H' =
      cutoffMean r q (stepExponent mirrored a ρA x m φ 1 V) H := by
  have hpres : MeasurePreserving (rotateVars A) volume volume :=
    measurePreserving_pi _ _ fun b => (A b).measurePreserving
  have hemb : MeasurableEmbedding (rotateVars A) := by
    have hhom : rotateVars A = (Homeomorph.piCongrRight fun b => (A b).toHomeomorph) := by
      funext η b
      rfl
    rw [hhom]
    exact Homeomorph.measurableEmbedding _
  have hnorm : ∀ (η : StepVars F) b, ‖rotateVars A η b‖ = ‖η b‖ := fun η b => (A b).norm_map _
  have hzero : ∀ η : StepVars F, chartedEnergy a (coordsAboveFrame mirrored a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateVars A η))
      (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = chartedEnergy a (coordsAboveFrame mirrored a ρA m V η) V := fun η =>
    chartedEnergy_gauge hM (coordsAboveFrame_gauge hM hfr hA η)
  refine cutoffMean_comp hpres hemb (fun η => by simp only [cutoffWeight, hnorm]) (fun η hη => ?_) hH
  unfold stepExponent
  have h0 := hzero 0
  rw [rotateVars_zero] at h0
  rw [hzero η, h0]
  have g1 : ∑ b : ↥(chordBonds (finiteCells F)),
      haarLogRatio (coordsAboveFrame mirrored a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateVars A η) b.1.1 b.1.2) =
      ∑ b : ↥(chordBonds (finiteCells F)), haarLogRatio (coordsAboveFrame mirrored a ρA m V η b.1.1 b.1.2) :=
    Finset.sum_congr rfl fun b _ => haarLogRatio_gauge hM hfr hA η b (not_isAxialTreeBond_of_chord b)
  have g2 : ∑ c ∈ innerBonds (finiteCells F) F.top,
      haarGapExcess a x (fieldAboveFrame mirrored a ρA m (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) (rotateVars A η)) c =
      ∑ c ∈ innerBonds (finiteCells F) F.top, haarGapExcess a x (fieldAboveFrame mirrored a ρA m V η) c :=
    Finset.sum_congr rfl fun c _ => haarGapExcess_gauge hM hfr hA η c
  have g3 : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      centredExpansion mirrored a ρA m φ y (rotateVars A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) =
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion mirrored a ρA m φ y η V :=
    Finset.sum_congr rfl fun y _ => hφ y η hη
  rw [g1, g2, g3]
end Gauge
section Shift
variable {mirrored : Bool} {a ρA x : ℝ} {m : ℕ} {V : F.GaugeField F.top} {h : F.Cell}
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
theorem chartedSlope_translate (hM : ChartEquivariance F a)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ y i, ¬ IsAxialTreeBond (y, i) → w' y i = w (y - cellCentre F.depth h) i)
    (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions) :
    chartedSlope a w' (translateField h V) (b.1 + cellCentre F.depth h, b.2) e = chartedSlope a w V b e := by apply _root_.YangMills.SharedProofs.p4342 <;> assumption
theorem coordsAboveFrame_translate (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame mirrored a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
        stepFrame mirrored a ρA m b V)
    (η : StepVars F) (y : F.Site F.depth) (i : Fin 4) (hnt : ¬ IsAxialTreeBond (y, i)) :
    coordsAboveFrame mirrored a ρA m (translateField h V) (translateVars (chordTranslate hM h) η) y i =
      coordsAboveFrame mirrored a ρA m V η (y - cellCentre F.depth h) i := by
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
      stepFrame mirrored a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
        stepFrame mirrored a ρA m b V)
    (η : StepVars F) :
    fieldAboveFrame mirrored a ρA m (translateField h V) (translateVars (chordTranslate hM h) η) =
      translateField (cellCentre F.depth h) (fieldAboveFrame mirrored a ρA m V η) := by
  unfold fieldAboveFrame
  rw [chartedField_congr (translateField h V) (coordsAboveFrame_translate hM hcar η),
    hM.chartedField_translate]
theorem haarGapExcess_translate (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame mirrored a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
        stepFrame mirrored a ρA m b V)
    (η : StepVars F) (c : F.Site F.top × Fin 4) :
    haarGapExcess a x (fieldAboveFrame mirrored a ρA m (translateField h V) (translateVars (chordTranslate hM h) η)) c =
      haarGapExcess a x (fieldAboveFrame mirrored a ρA m V η) (c.1 - h, c.2) := by
  unfold haarGapExcess
  rw [fieldAboveFrame_translate hM hcar, hM.contourAverage_translate]
theorem sum_innerBonds_sub (hM : ChartEquivariance F a) (h : F.Cell) (G : F.Site F.top × Fin 4 → ℝ) :
    ∑ c ∈ innerBonds (finiteCells F) F.top, G (c.1 - h, c.2) =
      ∑ c ∈ innerBonds (finiteCells F) F.top, G c := by apply _root_.YangMills.SharedProofs.p4672 <;> assumption
theorem sum_sitesOfCells_sub (hM : ChartEquivariance F a) (h : F.Cell) (G : F.Site F.depth → ℝ) :
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, G (y - cellCentre F.depth h) =
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, G y := by apply _root_.YangMills.SharedProofs.p5113 <;> assumption
theorem smul_translateVars (e : ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F))) (v : ℝ)
    (η : StepVars F) : v • translateVars e η = translateVars e (v • η) := rfl
theorem translateVars_zero (e : ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F))) :
    translateVars e (0 : StepVars F) = 0 := rfl
theorem cutoffMean_translate {r : ℝ} {q : ℝ → ℝ} {φ : LocalFamily} (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame mirrored a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
        stepFrame mirrored a ρA m b V)
    (hφ : ∀ (y : F.Site F.depth) (η : StepVars F), (∀ b, ‖η b‖ < r) →
      centredExpansion mirrored a ρA m φ y (translateVars (chordTranslate hM h) η) (translateField h V) =
        centredExpansion mirrored a ρA m φ (y - cellCentre F.depth h) η V)
    {H H' : StepVars F → ℝ}
    (hH : ∀ η : StepVars F, (∀ b, ‖η b‖ < r) → H' (translateVars (chordTranslate hM h) η) = H η) :
    cutoffMean r q (stepExponent mirrored a ρA x m φ 1 (translateField h V)) H' =
      cutoffMean r q (stepExponent mirrored a ρA x m φ 1 V) H := by
  set e := chordTranslate hM h with he
  have happ : ∀ (η : StepVars F) b, translateVars e η (e b) = η b := fun η b => by simp [translateVars]
  have hhaarAt : ∀ (η : StepVars F) (b : ↥(chordBonds (finiteCells F))),
      haarLogRatio (coordsAboveFrame mirrored a ρA m (translateField h V) (translateVars e η) (e b).1.1 (e b).1.2) =
        haarLogRatio (coordsAboveFrame mirrored a ρA m V η b.1.1 b.1.2) := fun η b => by
    have hnt : ¬ IsAxialTreeBond (e b).1 := not_isAxialTreeBond_of_chord _
    have h1 := coordsAboveFrame_translate hM hcar η (e b).1.1 (e b).1.2 hnt
    have h2 : (e b).1.1 - cellCentre F.depth h = b.1.1 := by simp [he, chordTranslate]
    have h3 : (e b).1.2 = b.1.2 := rfl
    rw [h2, h3] at h1
    rw [h3, h1]
  have hzero : ∀ η : StepVars F,
      chartedEnergy a (coordsAboveFrame mirrored a ρA m (translateField h V) (translateVars e η))
        (translateField h V) = chartedEnergy a (coordsAboveFrame mirrored a ρA m V η) V := fun η =>
    chartedEnergy_translate hM (coordsAboveFrame_translate hM hcar η)
  have hpres : MeasurePreserving (translateVars e) volume volume := by
    rw [translateVars_eq_piCongrLeft]
    exact volume_measurePreserving_piCongrLeft _ e
  have hemb : MeasurableEmbedding (translateVars e) := by
    rw [translateVars_eq_piCongrLeft]
    exact MeasurableEquiv.measurableEmbedding _
  have hw : ∀ η, cutoffWeight r q (translateVars e η) = cutoffWeight r q η := fun η => by
    unfold cutoffWeight
    rw [← Equiv.prod_comp e]
    exact Finset.prod_congr rfl fun b _ => by rw [happ]
  refine cutoffMean_comp hpres hemb hw (fun η hη => ?_) hH
  · unfold stepExponent
    have h0 := hzero 0
    rw [translateVars_zero] at h0
    rw [hzero η, h0]
    have g1 : ∑ c ∈ innerBonds (finiteCells F) F.top,
        haarGapExcess a x (fieldAboveFrame mirrored a ρA m (translateField h V) (translateVars e η)) c =
        ∑ c ∈ innerBonds (finiteCells F) F.top, haarGapExcess a x (fieldAboveFrame mirrored a ρA m V η) c := by
      simp only [he, haarGapExcess_translate hM hcar η]
      exact sum_innerBonds_sub hM h fun c => haarGapExcess a x (fieldAboveFrame mirrored a ρA m V η) c
    have g2 : ∑ b : ↥(chordBonds (finiteCells F)),
        haarLogRatio (coordsAboveFrame mirrored a ρA m (translateField h V) (translateVars e η) b.1.1 b.1.2) =
        ∑ b : ↥(chordBonds (finiteCells F)), haarLogRatio (coordsAboveFrame mirrored a ρA m V η b.1.1 b.1.2) := by
      rw [← Equiv.sum_comp e]
      exact Finset.sum_congr rfl fun b _ => hhaarAt η b
    have g3 : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
        centredExpansion mirrored a ρA m φ y (translateVars e η) (translateField h V) =
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion mirrored a ρA m φ y η V := by
      rw [Finset.sum_congr rfl fun y _ => hφ y η hη]
      exact sum_sitesOfCells_sub hM h fun y => centredExpansion mirrored a ρA m φ y η V
    rw [g1, g2, g3]
end Shift
section Moves
variable {Q : ColdHalfLaw} {V : F.GaugeField F.top}
theorem segmentEnd_false : segmentEnd false = 1 := by simp [segmentEnd]
theorem interpolatedCoords_one (hE : interpolationAtEndpoints) (Q : ColdHalfLaw) (V : F.GaugeField F.top)
    (η : StepVars F) :
    interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V η =
      coordsAboveFrame false Q.a Q.chartRadius Q.mirrorRadius V η := by
  have := (hE F false Q.a Q.chartRadius 0 Q.coupling 0 Q.mirrorRadius V).2.1 η
  rwa [segmentEnd_false] at this
theorem interpolatedField_one (hE : interpolationAtEndpoints) (Q : ColdHalfLaw) (V : F.GaugeField F.top)
    (η : StepVars F) :
    interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V η =
      fieldAboveFrame false Q.a Q.chartRadius Q.mirrorRadius V η := by
  have := (hE F false Q.a Q.chartRadius 0 Q.coupling 0 Q.mirrorRadius V).2.2.1 η
  rwa [segmentEnd_false] at this
theorem expectation_eq_cutoffMean (hE : interpolationAtEndpoints) (Q : ColdHalfLaw) (V : F.GaugeField F.top)
    (H : StepVars F → ℝ) :
    Q.expectation V H = cutoffMean Q.ballRadius Q.cutoff
      (stepExponent false Q.a Q.chartRadius Q.coupling Q.mirrorRadius Q.family 1 V) H := by
  have e : Q.exponent V = stepExponent false Q.a Q.chartRadius Q.coupling Q.mirrorRadius Q.family 1 V :=
    funext fun η => by
      have := (hE F false Q.a Q.chartRadius 0 Q.coupling 0 Q.mirrorRadius V).2.2.2.2.2.1 Q.family η
      rw [segmentEnd_false] at this
      exact this
  unfold ColdHalfLaw.expectation
  rw [e]
  rfl
variable {γ : F.Cell → UnitQuaternion} {h : F.Cell}
theorem linearBlockPart_gauge (hE : interpolationAtEndpoints) (hM : ChartEquivariance F Q.a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame false Q.a Q.chartRadius Q.mirrorRadius b (gaugeTransform γ V) =
        _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame false Q.a Q.chartRadius Q.mirrorRadius b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (Y : F.Cell) (η : StepVars F) :
    Q.linearBlockPart Y (rotateVars A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = Q.linearBlockPart Y η V := by
  unfold ColdHalfLaw.linearBlockPart
  refine congrArg (fun u => Q.coupling * u) ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · refine intervalIntegral.integral_congr fun v _ => ?_
    beta_reduce
    rw [interpolatedCoords_one hE, interpolatedCoords_one hE, smul_rotateVars]
    have e : toImaginary (rotateVars A η b) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary (η b)) :=
      hA b (η b)
    rw [e]
    exact chartedSlope_gauge hM (coordsAboveFrame_gauge hM hfr hA (v • η)) b.1 (not_isAxialTreeBond_of_chord b) _
  · rfl
theorem linearBlockPart_translate (hE : interpolationAtEndpoints) (hM : ChartEquivariance F Q.a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame false Q.a Q.chartRadius Q.mirrorRadius (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
        stepFrame false Q.a Q.chartRadius Q.mirrorRadius b V)
    (Y : F.Cell) (η : StepVars F) :
    Q.linearBlockPart (Y + h) (translateVars (chordTranslate hM h) η) (translateField h V) =
      Q.linearBlockPart Y η V := by
  unfold ColdHalfLaw.linearBlockPart
  refine congrArg (fun u => Q.coupling * u) ?_
  rw [← Equiv.sum_comp (chordTranslate hM h)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hc : enclosingCell (chordTranslate hM h b).1.1 = enclosingCell b.1.1 + h :=
    hM.enclosingCell_translate h b.1.1
  have hY : (enclosingCell b.1.1 + h = Y + h) ↔ enclosingCell b.1.1 = Y := add_left_inj h
  simp only [hc, hY]
  split_ifs
  · refine intervalIntegral.integral_congr fun v _ => ?_
    beta_reduce
    rw [interpolatedCoords_one hE, interpolatedCoords_one hE, smul_translateVars]
    have e : translateVars (chordTranslate hM h) η (chordTranslate hM h b) = η b := by simp [translateVars]
    rw [e]
    exact chartedSlope_translate hM (fun y i hnt => coordsAboveFrame_translate hM hcar (v • η) y i hnt) b.1 _
  · rfl
theorem scoreRemainderAt_gauge (hE : interpolationAtEndpoints) (hM : ChartEquivariance F Q.a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame false Q.a Q.chartRadius Q.mirrorRadius b (gaugeTransform γ V) =
        _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame false Q.a Q.chartRadius Q.mirrorRadius b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (c : F.Site F.top × Fin 4) (η : StepVars F) :
    Q.scoreRemainderAt c (rotateVars A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = Q.scoreRemainderAt c η V := by
  unfold ColdHalfLaw.scoreRemainderAt ColdHalfLaw.contourAverageSize
  rw [interpolatedField_one hE, interpolatedField_one hE, fieldAboveFrame_gauge hM hfr hA,
    hM.norm_contourAverage_gaugeTransform]
theorem scoreRemainderAt_translate (hE : interpolationAtEndpoints) (hM : ChartEquivariance F Q.a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame false Q.a Q.chartRadius Q.mirrorRadius (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
        stepFrame false Q.a Q.chartRadius Q.mirrorRadius b V)
    (c : F.Site F.top × Fin 4) (η : StepVars F) :
    Q.scoreRemainderAt (c.1 + h, c.2) (translateVars (chordTranslate hM h) η) (translateField h V) =
      Q.scoreRemainderAt c η V := by
  unfold ColdHalfLaw.scoreRemainderAt ColdHalfLaw.contourAverageSize
  rw [interpolatedField_one hE, interpolatedField_one hE, fieldAboveFrame_translate hM hcar,
    hM.contourAverage_translate]
  simp
end Moves
end ExpectationsEquivariant
open ExpectationsEquivariant in
theorem expectationsEquivariantStatement_holds (hCh : chartEquivarianceStatement)
    (hAd : AdjointActionLinearIsometry) (hB : CellEnergyShareInvariant) (hE : interpolationAtEndpoints) :
    expectationsEquivariantStatement := by
  intro T hD hL hn₀ hFr t x f hx hf F V hF hV
  obtain ⟨hFL, hFt, n, hside, hn⟩ := id hF
  have hn2 : 2 ≤ n := by omega
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside]
    exact hn2
  have hodd : Odd F.blockSide := by
    rw [hFL]
    exact hD.odd_L
  obtain ⟨hgauge₀, hshift₀, habove₀⟩ := hFr t x hx F V hF hV
  have hσ := hD.σ_pos
  obtain ⟨Q, hQ⟩ : ∃ Q : ColdHalfLaw, Q = coldHalfLawAt T x f := ⟨_, rfl⟩
  rw [← hQ]
  have hQa : Q.a = T.a := by rw [hQ]; rfl
  have hQρA : Q.chartRadius = T.chainParams.ρA := by rw [hQ]; rfl
  have hQm : Q.mirrorRadius = frameRadius x := by rw [hQ]; rfl
  have hQf : Q.family = f := by rw [hQ]; rfl
  have hQρ : Q.ballRadius = T.ballRadius := by rw [hQ]; rfl
  rw [← hQa, ← hQρA, ← hQm] at hgauge₀ hshift₀ habove₀
  have hgauge := hgauge₀
  have hshift := hshift₀
  have habove := habove₀
  have hM : ChartEquivariance F Q.a := hCh F Q.a hodd hs2
  have hρ0 : 0 ≤ T.ballRadius := by
    unfold StepParameters.ballRadius
    positivity
  have hcold : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) →
      IsSmallCurvature T.σ (fieldAboveFrame false Q.a Q.chartRadius Q.mirrorRadius V η) := fun η hη q hq => by
    have h1 := (habove η fun b => (hQρ ▸ hη b).le).1 q hq
    linarith
  have hLow : IsCubicTorusAbove T.L t T.n₀ F :=
    ⟨hFL, hFt, n, hside, le_trans hn (Nat.le_mul_of_pos_right n hD.odd_L.pos)⟩
  have hflat : IsSmallCurvature T.σ (uniformField F F.depth) := fun q _ => by
    have : plaquetteDefect (uniformField F F.depth) q = 0 := by
      simp [plaquetteDefect, plaquetteHolonomy, pathHolonomy, linkValue, uniformField]
    rw [this]
    exact hσ
  have hChain : IsBlockTorus T.L F := ⟨hFL, n, hn₀.trans hn, hside⟩
  have expansionG : ∀ (γ : F.Cell → UnitQuaternion) {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
      (_ : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
      (y : F.Site F.depth) (η : StepVars F), (∀ b, ‖η b‖ < Q.ballRadius) →
      centredExpansion false Q.a Q.chartRadius Q.mirrorRadius Q.family y (rotateVars A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) =
        centredExpansion false Q.a Q.chartRadius Q.mirrorRadius Q.family y η V := fun γ A hA y η hη => by
    unfold centredExpansion subtractTrivial
    rw [hQf, fieldAboveFrame_gauge hM (hgauge γ) hA,
      hf.gauge_invariant F hLow y _ (blockConstantGauge γ) (hcold η hη)]
  have expansionS : ∀ (h : F.Cell) (y : F.Site F.depth) (η : StepVars F), (∀ b, ‖η b‖ < Q.ballRadius) →
      centredExpansion false Q.a Q.chartRadius Q.mirrorRadius Q.family y (translateVars (chordTranslate hM h) η)
          (translateField h V) =
        centredExpansion false Q.a Q.chartRadius Q.mirrorRadius Q.family (y - cellCentre F.depth h) η V :=
      fun h y η hη => by
    have h1 := hf.translation_invariant F hLow (y - cellCentre F.depth h) (cellCentre F.depth h) _ (hcold η hη)
    have h2 := hf.translation_invariant F hLow (y - cellCentre F.depth h) (cellCentre F.depth h) _ hflat
    rw [sub_add_cancel] at h1 h2
    unfold centredExpansion subtractTrivial
    rw [hQf, fieldAboveFrame_translate hM (hshift h), h1]
    congr 1
  have smallAt : ∀ η : StepVars F, (∀ b, ‖η b‖ ≤ T.ballRadius) →
      IsAdmissibleChartPoint T.L T.chainParams.σA (coordsAboveFrame false Q.a Q.chartRadius Q.mirrorRadius V η) V :=
    fun η hη => (habove η hη).2
  have zero_ball : ∀ b : ↥(chordBonds (finiteCells F)), ‖(0 : StepVars F) b‖ ≤ T.ballRadius := fun b => by
    simpa using hρ0
  have costG : ∀ (γ : F.Cell → UnitQuaternion) {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
      (_ : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v)) (Y : F.Cell)
      (η : StepVars F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      Q.blockCost Y (rotateVars A η) (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V) = Q.blockCost Y η V := fun γ A hA Y η hη => by
    unfold ColdHalfLaw.blockCost
    rw [interpolatedCoords_one hE, interpolatedCoords_one hE]
    refine (hB Q.a T.L T.chainParams (hQa ▸ hD.one_le_a) hD.odd_L hL (hQa ▸ hD.chain_admissible) F _ _ V hChain
      (smallAt η hη) Y).1 γ fun b hb => ?_
    have := coordsAboveFrame_gauge (mirrored := false) hM (hgauge γ) hA η b.1 b.2
      (not_isAxialTreeBond_of_chord ⟨b, hb⟩)
    exact congrArg (fun u : imaginaryQuaternions => (u : Quaternion ℝ)) this
  have costS : ∀ (h Y : F.Cell) (η : StepVars F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      Q.blockCost (Y + h) (translateVars (chordTranslate hM h) η) (translateField h V) = Q.blockCost Y η V :=
      fun h Y η hη => by
    unfold ColdHalfLaw.blockCost
    rw [interpolatedCoords_one hE, interpolatedCoords_one hE]
    refine (hB Q.a T.L T.chainParams (hQa ▸ hD.one_le_a) hD.odd_L hL (hQa ▸ hD.chain_admissible) F _ _ V hChain
      (smallAt η hη) Y).2 h fun b hb => ?_
    have hb' : (b.1 + cellCentre F.depth h, b.2) ∈ chordBonds (finiteCells F) :=
      (hM.chordBonds_translate h b).mpr hb
    have := coordsAboveFrame_translate (mirrored := false) hM (hshift h) η (b.1 + cellCentre F.depth h) b.2
      (not_isAxialTreeBond_of_chord ⟨_, hb'⟩)
    rw [add_sub_cancel_right] at this
    exact this
  refine ⟨fun γ Y => ?_, fun γ c => ?_, fun h Y => ⟨?_, ?_⟩, fun h c => ?_⟩
  · choose A hA using fun b : ↥(chordBonds (finiteCells F)) => hAd (γ (enclosingCell b.1.1))
    refine ⟨?_, ?_⟩
    · show Q.expectation _ _ = Q.expectation _ _
      rw [expectation_eq_cutoffMean hE, expectation_eq_cutoffMean hE]
      exact cutoffMean_gauge hM (hgauge γ) hA (expansionG γ hA) fun η _ =>
        linearBlockPart_gauge hE hM (hgauge γ) hA Y η
    · show Q.expectation _ _ = Q.expectation _ _
      rw [expectation_eq_cutoffMean hE, expectation_eq_cutoffMean hE]
      refine cutoffMean_gauge hM (hgauge γ) hA (expansionG γ hA) fun η hη => ?_
      unfold ColdHalfLaw.blockIncrement
      have e0 := costG γ hA Y 0 zero_ball
      rw [rotateVars_zero] at e0
      rw [costG γ hA Y η fun b => hQρ ▸ (hη b).le, e0]
  · choose A hA using fun b : ↥(chordBonds (finiteCells F)) => hAd (γ (enclosingCell b.1.1))
    have e0 := scoreRemainderAt_gauge (Q := Q) hE hM (hgauge γ) hA c 0
    rw [rotateVars_zero] at e0
    refine ⟨e0, ?_⟩
    show Q.expectation _ _ = Q.expectation _ _
    rw [expectation_eq_cutoffMean hE, expectation_eq_cutoffMean hE]
    refine cutoffMean_gauge hM (hgauge γ) hA (expansionG γ hA) fun η _ => ?_
    unfold ColdHalfLaw.scoreRemainderIncrement
    rw [scoreRemainderAt_gauge hE hM (hgauge γ) hA c η, e0]
  · show Q.expectation _ _ = Q.expectation _ _
    rw [expectation_eq_cutoffMean hE, expectation_eq_cutoffMean hE]
    exact cutoffMean_translate hM (hshift h) (expansionS h) fun η _ =>
      linearBlockPart_translate hE hM (hshift h) Y η
  · show Q.expectation _ _ = Q.expectation _ _
    rw [expectation_eq_cutoffMean hE, expectation_eq_cutoffMean hE]
    refine cutoffMean_translate hM (hshift h) (expansionS h) fun η hη => ?_
    unfold ColdHalfLaw.blockIncrement
    have e0 := costS h Y 0 zero_ball
    rw [translateVars_zero] at e0
    rw [costS h Y η fun b => hQρ ▸ (hη b).le, e0]
  · have e0 := scoreRemainderAt_translate (Q := Q) hE hM (hshift h) c 0
    rw [translateVars_zero] at e0
    refine ⟨e0, ?_⟩
    show Q.expectation _ _ = Q.expectation _ _
    rw [expectation_eq_cutoffMean hE, expectation_eq_cutoffMean hE]
    refine cutoffMean_translate hM (hshift h) (expansionS h) fun η _ => ?_
    unfold ColdHalfLaw.scoreRemainderIncrement
    rw [scoreRemainderAt_translate hE hM (hshift h) c η, e0]
end YangMills.Construction.ResponseInTheExpansion
end
