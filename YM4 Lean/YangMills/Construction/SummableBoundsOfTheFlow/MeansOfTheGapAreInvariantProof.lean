import YangMills.Construction.SummableBoundsOfTheFlow.MeansOfTheWeightPartAreInvariantProof
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfTheStepAreInvariantProof
import YangMills.Construction.SummableBoundsOfTheFlow.FromTheMirrorFramesToTheLeastFieldProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheHigherDerivativesOfTheDensityOfTheStepProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion RealInnerProductSpace
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation MeasureTheory
namespace BlockMeans
variable {F : BlockFrame}
abbrev StepVars (F : BlockFrame) : Type := StepVariable (finiteCells F)
theorem forall_norm_lt_of_cutoffWeight_ne_zero {ρ : ℝ} {p : ℝ → ℝ} (η : StepVars F)
    (h : cutoffWeight ρ p η ≠ 0) : ∀ b, ‖η b‖ < ρ := by apply _root_.YangMills.DeltaSharedProofs.p502036 <;> assumption
theorem cutoffMean_comp {ρ : ℝ} {p : ℝ → ℝ} {R : StepVars F → StepVars F}
    (hR : MeasurePreserving R volume volume) (hemb : MeasurableEmbedding R)
    (hrim : ∀ η, cutoffWeight ρ p (R η) = cutoffWeight ρ p η) {Ψ Ψ' H H' : StepVars F → ℝ}
    (hΨ : ∀ η, (∀ b, ‖η b‖ < ρ) → Ψ' (R η) = Ψ η) (hH : ∀ η, H' (R η) = H η) :
    cutoffMean ρ p Ψ' H' = cutoffMean ρ p Ψ H := by
  have e1 : ∫ η, H' η * (cutoffWeight ρ p η * Real.exp (- Ψ' η)) =
      ∫ η, H η * (cutoffWeight ρ p η * Real.exp (- Ψ η)) := by
    rw [← hR.integral_comp hemb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    by_cases h : cutoffWeight ρ p η = 0
    · simp only [hrim, h, zero_mul, mul_zero]
    · have hb := forall_norm_lt_of_cutoffWeight_ne_zero η h
      simp only [hrim, hΨ η hb, hH η]
  have e2 : ∫ η, cutoffWeight ρ p η * Real.exp (- Ψ' η) =
      ∫ η, cutoffWeight ρ p η * Real.exp (- Ψ η) := by
    rw [← hR.integral_comp hemb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    by_cases h : cutoffWeight ρ p η = 0
    · simp only [hrim, h, zero_mul]
    · have hb := forall_norm_lt_of_cutoffWeight_ne_zero η h
      simp only [hrim, hΨ η hb]
  unfold cutoffMean
  rw [e1, e2]
theorem toImaginary_imaginaryCoords (w : imaginaryQuaternions) :
    toImaginary (_root_.YangMills.Construction.Interpolation.imaginaryCoords w) = w := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_imaginaryCoords <;> assumption
theorem imaginaryCoords_toImaginary (v : BondVector) : _root_.YangMills.Construction.Interpolation.imaginaryCoords (toImaginary v) = v := by apply _root_.YangMills.Construction.FrameInterpolationProof.imaginaryCoords_toImaginary <;> assumption
theorem inner_toImaginary (v : BondVector) (w : imaginaryQuaternions) :
    ⟪((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]), (w : ℍ[ℝ])⟫ = ⟪v, _root_.YangMills.Construction.Interpolation.imaginaryCoords w⟫ := by apply _root_.YangMills.Construction.FrameInterpolationProof.inner_toImaginary <;> assumption
theorem chartedField_congr {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (V : F.GaugeField F.top)
    (hw : ∀ x i, ¬ IsAxialTreeBond (x, i) → w x i = w' x i) :
    chartedField w V = chartedField w' V := by apply _root_.YangMills.SharedProofs.p16263 <;> assumption
theorem adjointAction_add (g : UnitQuaternion) (X Y : imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (X + Y) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X + _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g Y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add <;> assumption
theorem norm_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) :
    ‖_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X‖ = ‖X‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction <;> assumption
section Gauge
variable {s a ρA x : ℝ} {m : ℕ} {f : LocalFamily} {V : F.GaugeField F.top}
  {γ : F.Cell → UnitQuaternion}
theorem chartedEnergy_gauge (hM : ChartEquivariance F a)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ y i, ¬ IsAxialTreeBond (y, i) → w' y i = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (w y i)) :
    chartedEnergy a w' (gaugeTransform γ V) = chartedEnergy a w V := by apply _root_.YangMills.SharedProofs.p19410 <;> assumption
def rotateVars (A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector)
    (η : StepVars F) : StepVars F :=
  fun b => A b (η b)
theorem interpolatedCoords_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), interpolatedFrame s a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame s a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : StepVars F) (y : F.Site F.depth) (i : Fin 4) (hnt : ¬ IsAxialTreeBond (y, i)) :
    interpolatedCoords s a ρA m (gaugeTransform γ V) (rotateVars A η) y i =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (interpolatedCoords s a ρA m V η y i) := by
  have hb : (y, i) ∈ chordBonds (finiteCells F) := hM.mem_chordBonds_of_not_tree _ hnt
  unfold interpolatedCoords stepCoordinates
  rw [dif_pos hb, dif_pos hb, hfr _ hb, _root_.YangMills.Construction.BlockMeans.adjointAction_add]
  congr 1
  exact hA ⟨(y, i), hb⟩ (η ⟨(y, i), hb⟩)
theorem interpolatedField_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), interpolatedFrame s a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame s a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : StepVars F) :
    interpolatedField s a ρA m (gaugeTransform γ V) (rotateVars A η) =
      gaugeTransform (blockConstantGauge γ) (interpolatedField s a ρA m V η) := by
  unfold interpolatedField
  rw [chartedField_congr (gaugeTransform γ V) (interpolatedCoords_gauge hM hfr hA η),
    hM.chartedField_gaugeTransform]
theorem haarGapExcess_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), interpolatedFrame s a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame s a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : StepVars F) (c : F.Site F.top × Fin 4) :
    haarGapExcess a x (interpolatedField s a ρA m (gaugeTransform γ V) (rotateVars A η)) c =
      haarGapExcess a x (interpolatedField s a ρA m V η) c := by
  unfold haarGapExcess
  rw [interpolatedField_gauge hM hfr hA, hM.norm_contourAverage_gaugeTransform]
theorem haarLogRatio_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), interpolatedFrame s a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame s a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : StepVars F) (b : ↥(chordBonds (finiteCells F))) (hnt : ¬ IsAxialTreeBond b.1) :
    haarLogRatio (interpolatedCoords s a ρA m (gaugeTransform γ V) (rotateVars A η) b.1.1 b.1.2) =
      haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) := by
  unfold haarLogRatio
  rw [interpolatedCoords_gauge hM hfr hA η _ _ hnt, norm_adjointAction]
theorem rotateVars_zero {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector} :
    rotateVars A (0 : StepVars F) = 0 := by
  funext b
  simp [rotateVars]
theorem not_isAxialTreeBond_of_chord (b : ↥(chordBonds (finiteCells F))) :
    ¬ IsAxialTreeBond b.1 := by apply _root_.YangMills.SharedProofs.p29908 <;> assumption
theorem familyLawExponent_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), interpolatedFrame s a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame s a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : StepVars F)
    (hrow : ∀ y : F.Site F.depth, interpolatedExpansion s a ρA m f y (rotateVars A η) (gaugeTransform γ V) =
      interpolatedExpansion s a ρA m f y η V) :
    familyLawExponent s a ρA x m f (gaugeTransform γ V) (rotateVars A η) =
      familyLawExponent s a ρA x m f V η := by
  have hzero : ∀ η : StepVars F,
      chartedEnergy a (interpolatedCoords s a ρA m (gaugeTransform γ V) (rotateVars A η))
        (gaugeTransform γ V) = chartedEnergy a (interpolatedCoords s a ρA m V η) V := fun η =>
    chartedEnergy_gauge hM (interpolatedCoords_gauge hM hfr hA η)
  unfold familyLawExponent interpolatedExponent
  have h0 := hzero 0
  rw [rotateVars_zero] at h0
  rw [hzero η, h0]
  have g1 : ∑ b : ↥(chordBonds (finiteCells F)),
      haarLogRatio (interpolatedCoords s a ρA m (gaugeTransform γ V) (rotateVars A η) b.1.1 b.1.2) =
      ∑ b : ↥(chordBonds (finiteCells F)),
        haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) :=
    Finset.sum_congr rfl fun b _ =>
      haarLogRatio_gauge hM hfr hA η b (not_isAxialTreeBond_of_chord b)
  have g2 : ∑ c ∈ innerBonds (finiteCells F) F.top,
      haarGapExcess a x (interpolatedField s a ρA m (gaugeTransform γ V) (rotateVars A η)) c =
      ∑ c ∈ innerBonds (finiteCells F) F.top,
        haarGapExcess a x (interpolatedField s a ρA m V η) c :=
    Finset.sum_congr rfl fun c _ => haarGapExcess_gauge hM hfr hA η c
  have g3 : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      interpolatedExpansion s a ρA m f y (rotateVars A η) (gaugeTransform γ V) =
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, interpolatedExpansion s a ρA m f y η V :=
    Finset.sum_congr rfl fun y _ => hrow y
  rw [g1, g2, g3]
theorem blockGapObservable_gauge {p : ℝ → ℝ}
    (hd : ∀ b ∈ chordBonds (finiteCells F), frameGap a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (frameGap a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (Y : F.Cell) (η : StepVars F) :
    blockGapObservable a ρA m p Y (gaugeTransform γ V) (rotateVars A η) =
      blockGapObservable a ρA m p Y V η := by
  unfold blockGapObservable
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · have hn : ‖rotateVars A η b‖ = ‖η b‖ := (A b).norm_map _
    rw [hn]
    congr 1
    have hb : _root_.YangMills.Construction.Interpolation.imaginaryCoords (frameGap a ρA m b.1 (gaugeTransform γ V)) =
        A b (_root_.YangMills.Construction.Interpolation.imaginaryCoords (frameGap a ρA m b.1 V)) := by
      have h1 := hA b (_root_.YangMills.Construction.Interpolation.imaginaryCoords (frameGap a ρA m b.1 V))
      rw [toImaginary_imaginaryCoords, ← hd b.1 b.2] at h1
      rw [← h1, imaginaryCoords_toImaginary]
    rw [inner_toImaginary, inner_toImaginary, hb]
    exact (A b).inner_map_map _ _
  · rfl
end Gauge
section Shift
variable {s a ρA x : ℝ} {m : ℕ} {f : LocalFamily} {V : F.GaugeField F.top} {h : F.Cell}
def chordTranslate (hM : ChartEquivariance F a) (h : F.Cell) :
    ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F)) where
  toFun b := ⟨(b.1.1 + cellCentre F.depth h, b.1.2), (hM.chordBonds_translate h b.1).mpr b.2⟩
  invFun b := ⟨(b.1.1 - cellCentre F.depth h, b.1.2),
    (hM.chordBonds_translate h (b.1.1 - cellCentre F.depth h, b.1.2)).mp (by simp)⟩
  left_inv b := Subtype.ext (by simp)
  right_inv b := Subtype.ext (by simp)
def translateVars (e : ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F)))
    (η : StepVars F) : StepVars F :=
  fun b => η (e.symm b)
theorem translateVars_eq_piCongrLeft
    (e : ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F))) :
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
theorem interpolatedCoords_translate (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      interpolatedFrame s a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
        interpolatedFrame s a ρA m b V)
    (η : StepVars F) (y : F.Site F.depth) (i : Fin 4) (hnt : ¬ IsAxialTreeBond (y, i)) :
    interpolatedCoords s a ρA m (translateField h V) (translateVars (chordTranslate hM h) η) y i =
      interpolatedCoords s a ρA m V η (y - cellCentre F.depth h) i := by
  have hb : (y, i) ∈ chordBonds (finiteCells F) := hM.mem_chordBonds_of_not_tree _ hnt
  have hb0 : (y - cellCentre F.depth h, i) ∈ chordBonds (finiteCells F) :=
    (hM.chordBonds_translate h (y - cellCentre F.depth h, i)).mp (by simpa using hb)
  have hf := hcar _ hb0
  simp only [sub_add_cancel] at hf
  unfold interpolatedCoords stepCoordinates
  rw [dif_pos hb, dif_pos hb0, hf]
  rfl
theorem interpolatedField_translate (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      interpolatedFrame s a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
        interpolatedFrame s a ρA m b V)
    (η : StepVars F) :
    interpolatedField s a ρA m (translateField h V) (translateVars (chordTranslate hM h) η) =
      translateField (cellCentre F.depth h) (interpolatedField s a ρA m V η) := by
  unfold interpolatedField
  rw [chartedField_congr (translateField h V) (interpolatedCoords_translate hM hcar η),
    hM.chartedField_translate]
theorem haarGapExcess_translate (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      interpolatedFrame s a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
        interpolatedFrame s a ρA m b V)
    (η : StepVars F) (c : F.Site F.top × Fin 4) :
    haarGapExcess a x
        (interpolatedField s a ρA m (translateField h V) (translateVars (chordTranslate hM h) η)) c =
      haarGapExcess a x (interpolatedField s a ρA m V η) (c.1 - h, c.2) := by
  unfold haarGapExcess
  rw [interpolatedField_translate hM hcar, hM.contourAverage_translate]
theorem sum_innerBonds_translate (hM : ChartEquivariance F a) (h : F.Cell)
    (G : F.Site F.top × Fin 4 → ℝ) :
    ∑ c ∈ innerBonds (finiteCells F) F.top, G (c.1 - h, c.2) =
      ∑ c ∈ innerBonds (finiteCells F) F.top, G c := by apply _root_.YangMills.SharedProofs.p4672 <;> assumption
theorem sum_sitesOfCells_translate (hM : ChartEquivariance F a) (h : F.Cell)
    (G : F.Site F.depth → ℝ) :
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, G (y - cellCentre F.depth h) =
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, G y := by apply _root_.YangMills.SharedProofs.p5113 <;> assumption
theorem translateVars_zero (e : ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F))) :
    translateVars e (0 : StepVars F) = 0 := rfl
theorem familyLawExponent_translate (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      interpolatedFrame s a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
        interpolatedFrame s a ρA m b V)
    (η : StepVars F)
    (hrow : ∀ y : F.Site F.depth,
      interpolatedExpansion s a ρA m f y (translateVars (chordTranslate hM h) η) (translateField h V) =
        interpolatedExpansion s a ρA m f (y - cellCentre F.depth h) η V) :
    familyLawExponent s a ρA x m f (translateField h V) (translateVars (chordTranslate hM h) η) =
      familyLawExponent s a ρA x m f V η := by
  set e := chordTranslate hM h with he
  have hhaarAt : ∀ (η : StepVars F) (b : ↥(chordBonds (finiteCells F))),
      haarLogRatio (interpolatedCoords s a ρA m (translateField h V) (translateVars e η)
        (e b).1.1 (e b).1.2) =
        haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) := fun η b => by
    have hnt : ¬ IsAxialTreeBond (e b).1 := not_isAxialTreeBond_of_chord _
    have h1 := interpolatedCoords_translate hM hcar η (e b).1.1 (e b).1.2 hnt
    have h2 : (e b).1.1 - cellCentre F.depth h = b.1.1 := by simp [he, chordTranslate]
    have h3 : (e b).1.2 = b.1.2 := rfl
    rw [h2, h3] at h1
    rw [h3, h1]
  have hzero : ∀ η : StepVars F,
      chartedEnergy a (interpolatedCoords s a ρA m (translateField h V) (translateVars e η))
        (translateField h V) = chartedEnergy a (interpolatedCoords s a ρA m V η) V := fun η =>
    chartedEnergy_translate hM (interpolatedCoords_translate hM hcar η)
  unfold familyLawExponent interpolatedExponent
  have h0 := hzero 0
  rw [translateVars_zero] at h0
  rw [hzero η, h0]
  have g1 : ∑ c ∈ innerBonds (finiteCells F) F.top,
      haarGapExcess a x (interpolatedField s a ρA m (translateField h V) (translateVars e η)) c =
      ∑ c ∈ innerBonds (finiteCells F) F.top,
        haarGapExcess a x (interpolatedField s a ρA m V η) c := by
    simp only [he, haarGapExcess_translate hM hcar η]
    exact sum_innerBonds_translate hM h fun c => haarGapExcess a x (interpolatedField s a ρA m V η) c
  have g2 : ∑ b : ↥(chordBonds (finiteCells F)),
      haarLogRatio (interpolatedCoords s a ρA m (translateField h V) (translateVars e η)
        b.1.1 b.1.2) =
      ∑ b : ↥(chordBonds (finiteCells F)),
        haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) := by
    rw [← Equiv.sum_comp e]
    exact Finset.sum_congr rfl fun b _ => hhaarAt η b
  have g3 : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      interpolatedExpansion s a ρA m f y (translateVars e η) (translateField h V) =
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, interpolatedExpansion s a ρA m f y η V := by
    rw [Finset.sum_congr rfl fun y _ => hrow y]
    exact sum_sitesOfCells_translate hM h fun y => interpolatedExpansion s a ρA m f y η V
  rw [g1, g2, g3]
theorem blockGapObservable_translate {p : ℝ → ℝ} (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      frameGap a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) = frameGap a ρA m b V)
    (Y : F.Cell) (η : StepVars F) :
    blockGapObservable a ρA m p (Y + h) (translateField h V)
        (translateVars (chordTranslate hM h) η) =
      blockGapObservable a ρA m p Y V η := by
  set e := chordTranslate hM h with he
  have happ : ∀ (η : StepVars F) b, translateVars e η (e b) = η b := fun η b => by
    simp [translateVars]
  have hcell : ∀ b : ↥(chordBonds (finiteCells F)),
      enclosingCell (e b).1.1 = enclosingCell b.1.1 + h := fun b =>
    hM.enclosingCell_translate h b.1.1
  have hY : ∀ Z : F.Cell, Z + h = Y + h ↔ Z = Y := fun Z => add_left_inj h
  unfold blockGapObservable
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [hcell, hY, happ]
  split_ifs
  · have hd : frameGap a ρA m (e b).1 (translateField h V) = frameGap a ρA m b.1 V :=
      hcar b.1 b.2
    rw [hd]
  · rfl
theorem cutoffWeight_translateVars {ρ : ℝ} {p : ℝ → ℝ} (hM : ChartEquivariance F a)
    (η : StepVars F) :
    cutoffWeight ρ p (translateVars (chordTranslate hM h) η) = cutoffWeight ρ p η := by
  set e := chordTranslate hM h with he
  have happ : ∀ (η : StepVars F) b, translateVars e η (e b) = η b := fun η b => by
    simp [translateVars]
  unfold cutoffWeight
  rw [← Equiv.prod_comp e]
  exact Finset.prod_congr rfl fun b _ => by rw [happ]
end Shift
theorem frameGap_eq_sub (a ρA : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) (V : F.GaugeField F.top) :
    frameGap a ρA m b V = interpolatedFrame 1 a ρA m b V - interpolatedFrame 0 a ρA m b V := by
  simp [frameGap, interpolatedFrame]
theorem adjointAction_sub (g : UnitQuaternion) (X Y : imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (X - Y) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X - _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g Y := by
  apply Subtype.ext
  change (g : ℍ[ℝ]) * ((X : ℍ[ℝ]) - (Y : ℍ[ℝ])) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
    (g : ℍ[ℝ]) * (X : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
      (g : ℍ[ℝ]) * (Y : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])
  rw [mul_sub, sub_mul]
theorem gapMeansInvariantAt_of (hCh : chartEquivarianceStatement)
    (hAd : AdjointActionLinearIsometry)
    (T : StepParameters) (hT : T.IsOrdered) (hn : 2 ≤ T.n₀) {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
    (hfb : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFrameBoundsAt T Cq Cz Cr t x) :
    GapMeansInvariantAt T := by
  intro t x s φ F V hx h0 h1 hφ hF hV
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
  have one := fun s' (a0 : (0 : ℝ) ≤ s') (a1 : s' ≤ 1) =>
    (hfb t x hx).one_torus F V s' hF hV a0 a1
  have hσ := hT.σ_pos
  have hcoldη : ∀ η : StepVars F, (∀ b, ‖η b‖ < T.ballRadius) →
      IsSmallCurvature T.σ
        (interpolatedField s T.a T.chainParams.ρA (frameRadius x) V η) := fun η hη => by
    have h2 := (one s h0 h1).small.small_curvature_nearby η fun b => (hη b).le
    exact fun q hq => (h2 q hq).trans_le (by linarith)
  have hflat : IsSmallCurvature T.σ (uniformField F F.depth) := fun q _ => by
    have : plaquetteDefect (uniformField F F.depth) q = 0 := by
      simp [plaquetteDefect, plaquetteHolonomy, pathHolonomy, linkValue, uniformField]
    rw [this]
    exact hσ
  refine ⟨fun Y γ => ?_, fun Y h => ?_⟩
  · choose A hA using fun b : ↥(chordBonds (finiteCells F)) => hAd (γ (enclosingCell b.1.1))
    have hcov : ∀ (s' : ℝ), 0 ≤ s' → s' ≤ 1 → ∀ b ∈ chordBonds (finiteCells F),
        interpolatedFrame s' T.a T.chainParams.ρA (frameRadius x) b (gaugeTransform γ V) =
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1))
            (interpolatedFrame s' T.a T.chainParams.ρA (frameRadius x) b V) :=
      fun s' a0 a1 b hb => Subtype.ext ((one s' a0 a1).small.gauge_covariant b hb γ)
    have hd : ∀ b ∈ chordBonds (finiteCells F),
        frameGap T.a T.chainParams.ρA (frameRadius x) b (gaugeTransform γ V) =
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1))
            (frameGap T.a T.chainParams.ρA (frameRadius x) b V) := by
      intro b hb
      rw [frameGap_eq_sub, frameGap_eq_sub, hcov 1 zero_le_one le_rfl b hb,
        hcov 0 le_rfl zero_le_one b hb, _root_.YangMills.Construction.BlockMeans.adjointAction_sub]
    have hpres : MeasurePreserving (rotateVars A) volume volume :=
      measurePreserving_pi _ _ fun b => (A b).measurePreserving
    have hemb : MeasurableEmbedding (rotateVars A) := by
      have hhom : rotateVars A = (Homeomorph.piCongrRight fun b => (A b).toHomeomorph) := by
        funext η b
        rfl
      rw [hhom]
      exact Homeomorph.measurableEmbedding _
    have hnorm : ∀ (η : StepVars F) b, ‖rotateVars A η b‖ = ‖η b‖ := fun η b => (A b).norm_map _
    refine cutoffMean_comp (ρ := T.ballRadius) (p := T.p) hpres hemb
      (fun η => by simp only [cutoffWeight, hnorm])
      (fun η hη => ?_) (fun η => blockGapObservable_gauge hd hA Y η)
    refine familyLawExponent_gauge hM (hcov s h0 h1) hA η fun y => ?_
    unfold interpolatedExpansion subtractTrivial
    rw [interpolatedField_gauge hM (hcov s h0 h1) hA,
      hφ.gauge_invariant F hLow y _ (blockConstantGauge γ) (hcoldη η hη)]
  · have hcar : ∀ (s' : ℝ), 0 ≤ s' → s' ≤ 1 → ∀ b ∈ chordBonds (finiteCells F),
        interpolatedFrame s' T.a T.chainParams.ρA (frameRadius x)
            (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
          interpolatedFrame s' T.a T.chainParams.ρA (frameRadius x) b V :=
      fun s' a0 a1 b hb => (one s' a0 a1).small.translation_invariant b hb h
    have hd : ∀ b ∈ chordBonds (finiteCells F),
        frameGap T.a T.chainParams.ρA (frameRadius x) (b.1 + cellCentre F.depth h, b.2)
            (translateField h V) =
          frameGap T.a T.chainParams.ρA (frameRadius x) b V := by
      intro b hb
      rw [frameGap_eq_sub, frameGap_eq_sub, hcar 1 zero_le_one le_rfl b hb,
        hcar 0 le_rfl zero_le_one b hb]
    refine cutoffMean_comp (ρ := T.ballRadius) (p := T.p) (R := translateVars (chordTranslate hM h))
      ?_ ?_ (fun η => cutoffWeight_translateVars hM η) (fun η hη => ?_)
      (fun η => blockGapObservable_translate hM hd Y η)
    · rw [translateVars_eq_piCongrLeft]
      exact volume_measurePreserving_piCongrLeft _ _
    · rw [translateVars_eq_piCongrLeft]
      exact MeasurableEquiv.measurableEmbedding _
    · refine familyLawExponent_translate hM (hcar s h0 h1) η fun y => ?_
      have e1 := hφ.translation_invariant F hLow (y - cellCentre F.depth h) (cellCentre F.depth h) _
        (hcoldη η hη)
      have e2 := hφ.translation_invariant F hLow (y - cellCentre F.depth h) (cellCentre F.depth h) _
        hflat
      rw [sub_add_cancel] at e1 e2
      unfold interpolatedExpansion subtractTrivial
      rw [interpolatedField_translate hM (hcar s h0 h1), e1]
      congr 1
theorem eventually_two_le_n₀ : EventuallyInParameters fun T => 2 ≤ T.n₀ := by apply _root_.YangMills.SharedProofs.p10519 <;> assumption
theorem gapMeansInvariant_proof (hframes : interpolatedFramesStatement)
    (hJ : EventuallyInParametersCombines) (hCh : chartEquivarianceStatement)
    (hAd : AdjointActionLinearIsometry) : gapMeansInvariant := by
  obtain ⟨Cq, Cz, Cr, hfb⟩ := hframes
  exact hJ.2 _ _ (fun T hT h => gapMeansInvariantAt_of hCh hAd T hT h.1 h.2)
    (hJ.1 _ _ eventually_two_le_n₀ hfb)
end BlockMeans
end YangMills.Construction
end
