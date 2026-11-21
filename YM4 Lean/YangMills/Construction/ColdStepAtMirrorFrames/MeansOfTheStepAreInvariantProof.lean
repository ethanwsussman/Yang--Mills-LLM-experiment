import YangMills.Construction.ColdStepAtMirrorFrames.CouplingFloorOfTheFrames
import YangMills.Construction.ColdStepAtMirrorFrames.FieldAboveTheFrameIsCold
import YangMills.Construction.ColdStepAtMirrorFrames.FramesAgainstTheLeastField
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfTheStepAreInvariant
import YangMills.Construction.SummableBoundsOfTheFlow.MeansOfTheWeightPartAreInvariantProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace StepMeansInvariance
private abbrev Vars (F : BlockFrame) : Type := StepVariable (finiteCells F)
private theorem forall_norm_lt_of_cutoffWeight_ne_zero {ρ : ℝ} {p : ℝ → ℝ} (η : Vars F)
    (h : cutoffWeight ρ p η ≠ 0) :
    ∀ b, ‖η b‖ < ρ := by apply _root_.YangMills.DeltaSharedProofs.p502036 <;> assumption
private theorem cutoffMean_comp {ρ : ℝ} {p : ℝ → ℝ} {R : Vars F → Vars F}
    (hR : MeasurePreserving R volume volume) (hemb : MeasurableEmbedding R)
    (hcut : ∀ η, cutoffWeight ρ p (R η) = cutoffWeight ρ p η) {Ψ Ψ' H H' : Vars F → ℝ}
    (hΨ : ∀ η, (∀ b, ‖η b‖ < ρ) → Ψ' (R η) = Ψ η) (hH : ∀ η, (∀ b, ‖η b‖ < ρ) → H' (R η) = H η) :
    cutoffMean ρ p Ψ' H' = cutoffMean ρ p Ψ H := by apply _root_.YangMills.DeltaSharedProofs.p500520 <;> assumption
structure ChangeOfVariables (a ρA ρ lam x : ℝ) (m : ℕ) (p : ℝ → ℝ) (f : LocalFamily)
    (V V' : F.GaugeField F.top) (Y Y' : F.Cell) (R : Vars F → Vars F) : Prop where
  measurePreserving : MeasurePreserving R volume volume
  measurableEmbedding : MeasurableEmbedding R
  cutoffWeight_eq : ∀ η, cutoffWeight ρ p (R η) = cutoffWeight ρ p η
  totalQuadratic_eq : ∀ η, totalQuadratic lam x (R η) = totalQuadratic lam x η
  cellQuadratic_eq : ∀ η, cellQuadratic lam x Y' (R η) = cellQuadratic lam x Y η
  stepExponent_eq : ∀ (ν : ℝ) (η : Vars F), (∀ b, ‖η b‖ < ρ) →
    stepExponent false a ρA x m f ν V' (R η) = stepExponent false a ρA x m f ν V η
  cellExponent_eq : ∀ η : Vars F, (∀ b, ‖η b‖ < ρ) →
    cellExponent false a ρA x m Y' V' (R η) = cellExponent false a ρA x m Y V η
  cellCentredExpansion_eq : ∀ η : Vars F, (∀ b, ‖η b‖ < ρ) →
    cellCentredExpansion false a ρA m f Y' (R η) V' = cellCentredExpansion false a ρA m f Y η V
private theorem densities_eq_of_changeOfVariables {a ρA ρ lam x : ℝ} {m : ℕ} {p : ℝ → ℝ}
    {f : LocalFamily} {V V' : F.GaugeField F.top}
    {Y Y' : F.Cell} {R : Vars F → Vars F} (M : ChangeOfVariables a ρA ρ lam x m p f V V' Y Y' R) :
    interactionDensity false a ρA ρ lam x m p f Y' V' = interactionDensity false a ρA ρ lam x m p f Y V ∧
      expansionDensity false a ρA ρ x m p f Y' V' = expansionDensity false a ρA ρ x m p f Y V := by
  constructor
  · unfold interactionDensity
    congr 1
    apply intervalIntegral.integral_congr
    intro v _
    exact cutoffMean_comp M.measurePreserving M.measurableEmbedding M.cutoffWeight_eq
      (fun η hη => by simp only [M.stepExponent_eq 0 η hη, M.totalQuadratic_eq η])
      (fun η hη => by simp only [M.cellExponent_eq η hη, M.cellQuadratic_eq η])
  · unfold expansionDensity
    apply intervalIntegral.integral_congr
    intro v _
    exact cutoffMean_comp M.measurePreserving M.measurableEmbedding M.cutoffWeight_eq
      (fun η hη => M.stepExponent_eq v η hη) (fun η hη => M.cellCentredExpansion_eq η hη)
private theorem chartedField_congr {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (V : F.GaugeField F.top)
    (hw : ∀ x i, ¬ IsAxialTreeBond (x, i) → w x i = w' x i) :
    chartedField w V = chartedField w' V := by apply _root_.YangMills.SharedProofs.p16263 <;> assumption
private theorem adjointAction_add (g : UnitQuaternion) (X Y : imaginaryQuaternions) :
    adjointAction g (X + Y) = adjointAction g X + adjointAction g Y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add <;> assumption
private theorem norm_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) :
    ‖adjointAction g X‖ = ‖X‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction <;> assumption
section Gauge
variable {a ρA x : ℝ} {m : ℕ} {f : LocalFamily} {V : F.GaugeField F.top} {γ : F.Cell → UnitQuaternion}
private theorem chartedEnergy_gauge (hM : ChartEquivariance F a)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ y i, ¬ IsAxialTreeBond (y, i) → w' y i = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (w y i)) :
    chartedEnergy a w' (gaugeTransform γ V) = chartedEnergy a w V := by apply _root_.YangMills.SharedProofs.p19410 <;> assumption
private theorem chartedSlope_gauge (hM : ChartEquivariance F a)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ y i, ¬ IsAxialTreeBond (y, i) → w' y i = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (w y i))
    (b : F.Site F.depth × Fin 4) (hb : ¬ IsAxialTreeBond b) (e : imaginaryQuaternions) :
    chartedSlope a w' (gaugeTransform γ V) b (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) e) =
      chartedSlope a w V b e := by apply _root_.YangMills.SharedProofs.p24183 <;> assumption
private def rotateVars (A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector) (η : Vars F) :
    Vars F :=
  fun b => A b (η b)
private theorem coordsAboveFrame_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame false a ρA m b (gaugeTransform γ V) =
      adjointAction (γ (enclosingCell b.1)) (stepFrame false a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : Vars F) (y : F.Site F.depth) (i : Fin 4) (hnt : ¬ IsAxialTreeBond (y, i)) :
    coordsAboveFrame false a ρA m (gaugeTransform γ V) (rotateVars A η) y i =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (coordsAboveFrame false a ρA m V η y i) := by
  have hb : (y, i) ∈ chordBonds (finiteCells F) := hM.mem_chordBonds_of_not_tree _ hnt
  unfold coordsAboveFrame stepCoordinates
  rw [dif_pos hb, dif_pos hb, hfr _ hb, adjointAction_add]
  congr 1
  exact hA ⟨(y, i), hb⟩ (η ⟨(y, i), hb⟩)
private theorem fieldAboveFrame_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame false a ρA m b (gaugeTransform γ V) =
      adjointAction (γ (enclosingCell b.1)) (stepFrame false a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : Vars F) :
    fieldAboveFrame false a ρA m (gaugeTransform γ V) (rotateVars A η) =
      gaugeTransform (blockConstantGauge γ) (fieldAboveFrame false a ρA m V η) := by
  unfold fieldAboveFrame
  rw [chartedField_congr (gaugeTransform γ V) (coordsAboveFrame_gauge hM hfr hA η),
    hM.chartedField_gaugeTransform]
private theorem haarGapExcess_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame false a ρA m b (gaugeTransform γ V) =
      adjointAction (γ (enclosingCell b.1)) (stepFrame false a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : Vars F) (c : F.Site F.top × Fin 4) :
    haarGapExcess a x (fieldAboveFrame false a ρA m (gaugeTransform γ V) (rotateVars A η)) c =
      haarGapExcess a x (fieldAboveFrame false a ρA m V η) c := by
  unfold haarGapExcess
  rw [fieldAboveFrame_gauge hM hfr hA, hM.norm_contourAverage_gaugeTransform]
private theorem haarLogRatio_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame false a ρA m b (gaugeTransform γ V) =
      adjointAction (γ (enclosingCell b.1)) (stepFrame false a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (η : Vars F) (b : ↥(chordBonds (finiteCells F))) (hnt : ¬ IsAxialTreeBond b.1) :
    haarLogRatio (coordsAboveFrame false a ρA m (gaugeTransform γ V) (rotateVars A η) b.1.1 b.1.2) =
      haarLogRatio (coordsAboveFrame false a ρA m V η b.1.1 b.1.2) := by
  unfold haarLogRatio
  rw [coordsAboveFrame_gauge hM hfr hA η _ _ hnt, norm_adjointAction]
private theorem rotateVars_smul {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (v : ℝ) (η : Vars F) :
    v • rotateVars A η = rotateVars A (v • η) := by
  funext b
  simp [rotateVars]
private theorem rotateVars_zero {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector} :
    rotateVars A (0 : Vars F) = 0 := by
  funext b
  simp [rotateVars]
private theorem not_isAxialTreeBond_of_chord (b : ↥(chordBonds (finiteCells F))) :
    ¬ IsAxialTreeBond b.1 := by apply _root_.YangMills.SharedProofs.p29908 <;> assumption
private theorem changeOfVariables_gauge {ρ lam : ℝ} {p : ℝ → ℝ} (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), stepFrame false a ρA m b (gaugeTransform γ V) =
      adjointAction (γ (enclosingCell b.1)) (stepFrame false a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = adjointAction (γ (enclosingCell b.1.1)) (toImaginary v))
    (Y : F.Cell)
    (hrow : ∀ (y : F.Site F.depth) (η : Vars F), (∀ b, ‖η b‖ < ρ) →
      centredExpansion false a ρA m f y (rotateVars A η) (gaugeTransform γ V) =
        centredExpansion false a ρA m f y η V) :
    ChangeOfVariables a ρA ρ lam x m p f V (gaugeTransform γ V) Y Y (rotateVars A) := by
  have hpres : MeasurePreserving (rotateVars A) volume volume :=
    measurePreserving_pi _ _ fun b => (A b).measurePreserving
  have hemb : MeasurableEmbedding (rotateVars A) := by
    have hhom : rotateVars A = (Homeomorph.piCongrRight fun b => (A b).toHomeomorph) := by
      funext η b
      rfl
    rw [hhom]
    exact Homeomorph.measurableEmbedding _
  have hnorm : ∀ (η : Vars F) b, ‖rotateVars A η b‖ = ‖η b‖ := fun η b => (A b).norm_map _
  have hzero : ∀ η : Vars F,
      chartedEnergy a (coordsAboveFrame false a ρA m (gaugeTransform γ V) (rotateVars A η))
        (gaugeTransform γ V) = chartedEnergy a (coordsAboveFrame false a ρA m V η) V := fun η =>
    chartedEnergy_gauge hM (coordsAboveFrame_gauge hM hfr hA η)
  refine ⟨hpres, hemb, fun η => ?_, fun η => ?_, fun η => ?_, fun ν η hη => ?_, fun η hη => ?_,
    fun η hη => ?_⟩
  · simp only [cutoffWeight, hnorm]
  · simp only [totalQuadratic, hnorm]
  · simp only [cellQuadratic, hnorm]
  · unfold stepExponent
    have h0 := hzero 0
    rw [rotateVars_zero] at h0
    rw [hzero η, h0]
    have g1 : ∑ b : ↥(chordBonds (finiteCells F)),
        haarLogRatio (coordsAboveFrame false a ρA m (gaugeTransform γ V) (rotateVars A η) b.1.1 b.1.2) =
        ∑ b : ↥(chordBonds (finiteCells F)), haarLogRatio (coordsAboveFrame false a ρA m V η b.1.1 b.1.2) :=
      Finset.sum_congr rfl fun b _ => haarLogRatio_gauge hM hfr hA η b (not_isAxialTreeBond_of_chord b)
    have g2 : ∑ c ∈ innerBonds (finiteCells F) F.top,
        haarGapExcess a x (fieldAboveFrame false a ρA m (gaugeTransform γ V) (rotateVars A η)) c =
        ∑ c ∈ innerBonds (finiteCells F) F.top, haarGapExcess a x (fieldAboveFrame false a ρA m V η) c :=
      Finset.sum_congr rfl fun c _ => haarGapExcess_gauge hM hfr hA η c
    have g3 : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
        centredExpansion false a ρA m f y (rotateVars A η) (gaugeTransform γ V) =
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false a ρA m f y η V :=
      Finset.sum_congr rfl fun y _ => hrow y η hη
    rw [g1, g2, g3]
  · unfold cellExponent
    have g1 : ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y then
        ∫ v in (0 : ℝ)..1, chartedSlope a
          (coordsAboveFrame false a ρA m (gaugeTransform γ V) (v • rotateVars A η))
          (gaugeTransform γ V) b.1 (toImaginary (rotateVars A η b)) else 0) =
        ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y then
        ∫ v in (0 : ℝ)..1, chartedSlope a (coordsAboveFrame false a ρA m V (v • η)) V b.1
          (toImaginary (η b)) else 0) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs
      · apply intervalIntegral.integral_congr
        intro v _
        simp only
        rw [rotateVars_smul]
        have h1 : toImaginary (rotateVars A η b) =
            _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary (η b)) := hA b (η b)
        rw [h1]
        exact chartedSlope_gauge hM (coordsAboveFrame_gauge hM hfr hA (v • η)) b.1
          (not_isAxialTreeBond_of_chord b) _
      · rfl
    have g2 : ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        haarGapExcess a x (fieldAboveFrame false a ρA m (gaugeTransform γ V) (rotateVars A η)) c =
        ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
          haarGapExcess a x (fieldAboveFrame false a ρA m V η) c :=
      Finset.sum_congr rfl fun c _ => haarGapExcess_gauge hM hfr hA η c
    have g3 : ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y then
        haarLogRatio (coordsAboveFrame false a ρA m (gaugeTransform γ V) (rotateVars A η) b.1.1 b.1.2)
          else 0) =
        ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y then
        haarLogRatio (coordsAboveFrame false a ρA m V η b.1.1 b.1.2) else 0) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs
      · exact haarLogRatio_gauge hM hfr hA η b (not_isAxialTreeBond_of_chord b)
      · rfl
    rw [g1, g2, g3]
  · unfold cellCentredExpansion
    exact Finset.sum_congr rfl fun y _ => hrow y η hη
end Gauge
section Translate
variable {a ρA x : ℝ} {m : ℕ} {f : LocalFamily} {V : F.GaugeField F.top} {h : F.Cell}
private def chordTranslate (hM : ChartEquivariance F a) (h : F.Cell) :
    ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F)) where
  toFun b := ⟨(b.1.1 + cellCentre F.depth h, b.1.2), (hM.chordBonds_translate h b.1).mpr b.2⟩
  invFun b := ⟨(b.1.1 - cellCentre F.depth h, b.1.2),
    (hM.chordBonds_translate h (b.1.1 - cellCentre F.depth h, b.1.2)).mp (by simpa using b.2)⟩
  left_inv b := Subtype.ext (by simp)
  right_inv b := Subtype.ext (by simp)
private def translateVars (e : ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F)))
    (η : Vars F) : Vars F :=
  fun b => η (e.symm b)
private theorem translateVars_eq (e : ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F))) :
    translateVars e =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) e) := by
  funext η b
  obtain ⟨b', rfl⟩ := e.surjective b
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp [translateVars]
private theorem chartedEnergy_translate (hM : ChartEquivariance F a)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ y i, ¬ IsAxialTreeBond (y, i) → w' y i = w (y - cellCentre F.depth h) i) :
    chartedEnergy a w' (translateField h V) = chartedEnergy a w V := by apply _root_.YangMills.SharedProofs.p9314 <;> assumption
private theorem chartedSlope_translate (hM : ChartEquivariance F a)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ y i, ¬ IsAxialTreeBond (y, i) → w' y i = w (y - cellCentre F.depth h) i)
    (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions) :
    chartedSlope a w' (translateField h V) (b.1 + cellCentre F.depth h, b.2) e =
      chartedSlope a w V b e := by apply _root_.YangMills.SharedProofs.p4342 <;> assumption
private theorem coordsAboveFrame_translate (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame false a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
        stepFrame false a ρA m b V)
    (η : Vars F) (y : F.Site F.depth) (i : Fin 4) (hnt : ¬ IsAxialTreeBond (y, i)) :
    coordsAboveFrame false a ρA m (translateField h V) (translateVars (chordTranslate hM h) η) y i =
      coordsAboveFrame false a ρA m V η (y - cellCentre F.depth h) i := by
  have hb : (y, i) ∈ chordBonds (finiteCells F) := hM.mem_chordBonds_of_not_tree _ hnt
  have hb0 : (y - cellCentre F.depth h, i) ∈ chordBonds (finiteCells F) :=
    (hM.chordBonds_translate h (y - cellCentre F.depth h, i)).mp (by simpa using hb)
  have hf := hcar _ hb0
  simp only [sub_add_cancel] at hf
  unfold coordsAboveFrame stepCoordinates
  rw [dif_pos hb, dif_pos hb0, hf]
  rfl
private theorem fieldAboveFrame_translate (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame false a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
        stepFrame false a ρA m b V)
    (η : Vars F) :
    fieldAboveFrame false a ρA m (translateField h V) (translateVars (chordTranslate hM h) η) =
      translateField (cellCentre F.depth h) (fieldAboveFrame false a ρA m V η) := by
  unfold fieldAboveFrame
  rw [chartedField_congr (translateField h V) (coordsAboveFrame_translate hM hcar η),
    hM.chartedField_translate]
private theorem haarGapExcess_translate (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame false a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
        stepFrame false a ρA m b V)
    (η : Vars F) (c : F.Site F.top × Fin 4) :
    haarGapExcess a x
        (fieldAboveFrame false a ρA m (translateField h V) (translateVars (chordTranslate hM h) η)) c =
      haarGapExcess a x (fieldAboveFrame false a ρA m V η) (c.1 - h, c.2) := by
  unfold haarGapExcess
  rw [fieldAboveFrame_translate hM hcar, hM.contourAverage_translate]
private theorem sum_innerBonds_sub (hM : ChartEquivariance F a) (h : F.Cell)
    (G : F.Site F.top × Fin 4 → ℝ) :
    ∑ c ∈ innerBonds (finiteCells F) F.top, G (c.1 - h, c.2) =
      ∑ c ∈ innerBonds (finiteCells F) F.top, G c := by apply _root_.YangMills.SharedProofs.p4672 <;> assumption
private theorem sum_sitesOfCells_sub (hM : ChartEquivariance F a) (h : F.Cell)
    (G : F.Site F.depth → ℝ) :
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, G (y - cellCentre F.depth h) =
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, G y := by
  refine Finset.sum_nbij' (fun y => y - cellCentre F.depth h) (fun y => y + cellCentre F.depth h)
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact (hM.sitesOfCells_translate h _).mp (by simpa using hy)
  · intro y hy
    exact (hM.sitesOfCells_translate h _).mpr hy
  · intro y _
    simp
  · intro y _
    simp
  · intro y _
    rfl
abbrev _root_.YangMills.SharedProofs.p5113 := @sum_sitesOfCells_sub
private theorem translateVars_smul (e : ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F)))
    (v : ℝ) (η : Vars F) : v • translateVars e η = translateVars e (v • η) := rfl
private theorem translateVars_zero (e : ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F))) :
    translateVars e (0 : Vars F) = 0 := rfl
private theorem changeOfVariables_translate {ρ lam : ℝ} {p : ℝ → ℝ} (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      stepFrame false a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
        stepFrame false a ρA m b V)
    (Y : F.Cell)
    (hrow : ∀ (y : F.Site F.depth) (η : Vars F), (∀ b, ‖η b‖ < ρ) →
      centredExpansion false a ρA m f y (translateVars (chordTranslate hM h) η) (translateField h V) =
        centredExpansion false a ρA m f (y - cellCentre F.depth h) η V) :
    ChangeOfVariables a ρA ρ lam x m p f V (translateField h V) Y (Y + h)
      (translateVars (chordTranslate hM h)) := by
  set e := chordTranslate hM h with he
  have happ : ∀ (η : Vars F) b, translateVars e η (e b) = η b := fun η b => by simp [translateVars]
  have hcell : ∀ b : ↥(chordBonds (finiteCells F)), enclosingCell (e b).1.1 = enclosingCell b.1.1 + h :=
    fun b => hM.enclosingCell_translate h b.1.1
  have hY : ∀ Z : F.Cell, Z + h = Y + h ↔ Z = Y := fun Z => add_left_inj h
  have hhaarAt : ∀ (η : Vars F) (b : ↥(chordBonds (finiteCells F))),
      haarLogRatio (coordsAboveFrame false a ρA m (translateField h V) (translateVars e η) (e b).1.1 (e b).1.2) =
        haarLogRatio (coordsAboveFrame false a ρA m V η b.1.1 b.1.2) := fun η b => by
    have hnt : ¬ IsAxialTreeBond (e b).1 := not_isAxialTreeBond_of_chord _
    have h1 := coordsAboveFrame_translate hM hcar η (e b).1.1 (e b).1.2 hnt
    have h2 : (e b).1.1 - cellCentre F.depth h = b.1.1 := by simp [he, chordTranslate]
    have h3 : (e b).1.2 = b.1.2 := rfl
    rw [h2, h3] at h1
    rw [h3, h1]
  have hzero : ∀ η : Vars F,
      chartedEnergy a (coordsAboveFrame false a ρA m (translateField h V) (translateVars e η))
        (translateField h V) = chartedEnergy a (coordsAboveFrame false a ρA m V η) V := fun η =>
    chartedEnergy_translate hM (coordsAboveFrame_translate hM hcar η)
  refine ⟨?_, ?_, fun η => ?_, fun η => ?_, fun η => ?_, fun ν η hη => ?_, fun η hη => ?_,
    fun η hη => ?_⟩
  · rw [translateVars_eq]
    exact volume_measurePreserving_piCongrLeft _ e
  · rw [translateVars_eq]
    exact MeasurableEquiv.measurableEmbedding _
  · unfold cutoffWeight
    rw [← Equiv.prod_comp e]
    exact Finset.prod_congr rfl fun b _ => by rw [happ]
  · unfold totalQuadratic
    rw [← Equiv.sum_comp e]
    exact Finset.sum_congr rfl fun b _ => by rw [happ]
  · unfold cellQuadratic
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hcell, hY, happ]
  · unfold stepExponent
    have h0 := hzero 0
    rw [translateVars_zero] at h0
    rw [hzero η, h0]
    have g1 : ∑ c ∈ innerBonds (finiteCells F) F.top,
        haarGapExcess a x (fieldAboveFrame false a ρA m (translateField h V) (translateVars e η)) c =
        ∑ c ∈ innerBonds (finiteCells F) F.top, haarGapExcess a x (fieldAboveFrame false a ρA m V η) c := by
      simp only [he, haarGapExcess_translate hM hcar η]
      exact sum_innerBonds_sub hM h fun c => haarGapExcess a x (fieldAboveFrame false a ρA m V η) c
    have g2 : ∑ b : ↥(chordBonds (finiteCells F)),
        haarLogRatio (coordsAboveFrame false a ρA m (translateField h V) (translateVars e η) b.1.1 b.1.2) =
        ∑ b : ↥(chordBonds (finiteCells F)), haarLogRatio (coordsAboveFrame false a ρA m V η b.1.1 b.1.2) := by
      rw [← Equiv.sum_comp e]
      exact Finset.sum_congr rfl fun b _ => hhaarAt η b
    have g3 : ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
        centredExpansion false a ρA m f y (translateVars e η) (translateField h V) =
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false a ρA m f y η V := by
      rw [Finset.sum_congr rfl fun y _ => hrow y η hη]
      exact sum_sitesOfCells_sub hM h fun y => centredExpansion false a ρA m f y η V
    rw [g1, g2, g3]
  · unfold cellExponent
    have g1 : ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y + h then
        ∫ v in (0 : ℝ)..1, chartedSlope a
          (coordsAboveFrame false a ρA m (translateField h V) (v • translateVars e η))
          (translateField h V) b.1 (toImaginary (translateVars e η b)) else 0) =
        ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y then
        ∫ v in (0 : ℝ)..1, chartedSlope a (coordsAboveFrame false a ρA m V (v • η)) V b.1
          (toImaginary (η b)) else 0) := by
      rw [← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [hcell, hY, happ]
      split_ifs
      · apply intervalIntegral.integral_congr
        intro v _
        simp only
        rw [translateVars_smul]
        exact chartedSlope_translate hM (coordsAboveFrame_translate hM hcar (v • η)) b.1 _
      · rfl
    have g2 : ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y + h),
        haarGapExcess a x (fieldAboveFrame false a ρA m (translateField h V) (translateVars e η)) c =
        ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
          haarGapExcess a x (fieldAboveFrame false a ρA m V η) c := by
      rw [Finset.sum_filter, Finset.sum_filter,
        ← sum_innerBonds_sub hM h fun c =>
          if c.1 = Y then haarGapExcess a x (fieldAboveFrame false a ρA m V η) c else 0]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hc : c.1 - h = Y ↔ c.1 = Y + h := sub_eq_iff_eq_add
      simp only [hc]
      split_ifs
      · exact haarGapExcess_translate hM hcar η c
      · rfl
    have g3 : ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y + h then
        haarLogRatio (coordsAboveFrame false a ρA m (translateField h V) (translateVars e η) b.1.1 b.1.2)
          else 0) =
        ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y then
        haarLogRatio (coordsAboveFrame false a ρA m V η b.1.1 b.1.2) else 0) := by
      rw [← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [hcell, hY, hhaarAt]
    rw [g1, g2, g3]
  · unfold cellCentredExpansion
    rw [Finset.sum_filter, Finset.sum_filter,
      ← sum_sitesOfCells_sub hM h fun y =>
        if enclosingCell y = Y then centredExpansion false a ρA m f y η V else 0]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hc : enclosingCell y = enclosingCell (y - cellCentre F.depth h) + h := by
      rw [← hM.enclosingCell_translate h (y - cellCentre F.depth h), sub_add_cancel]
    have hc2 : enclosingCell (y - cellCentre F.depth h) = Y ↔ enclosingCell y = Y + h := by
      rw [hc, hY]
    simp only [hc2]
    split_ifs
    · exact hrow y η hη
    · rfl
end Translate
end StepMeansInvariance
open StepMeansInvariance in
theorem stepMeansInvariantStatement_holds (hJ : EventuallyInParametersCombines)
    (hW : frameBoundsStatement) (hC : CouplingThreshold)
    (hCh : chartEquivarianceStatement) (hAd : AdjointActionLinearIsometry)
    (hCold : fieldAboveFrameSmallCurvature) : stepMeansInvariantStatement := by
  obtain ⟨join, weaken⟩ := hJ
  have hF : EventuallyInParameters fun T => 2 ≤ T.n₀ ∧ ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x →
      ∀ F, IsCubicTopTorus T.L t T.n₀ F →
      ∀ V : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V → ∃ C : ℝ,
        FrameSmallness false T.a T.chainParams.ρA T.chainParams.δ₂ T.chainParams.κ₂ C T.σ T.chainParams.Kk (frameRadius x) V := by
    intro a ha
    refine ⟨2 ^ 40, fun L hL hLe c hc => ?_⟩
    obtain ⟨Cf, C, σ₀, hC₁, hC₂, hσ₀, hFr⟩ := hW a L c ha hL hLe hc
    have hδ₂ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
    refine ⟨0, fun Ct _ => ⟨c.δ₂ / 2 ^ 14, by positivity, fun κ hκ hκ' => ⟨1, one_pos,
      fun η₃ _ _ _ => ⟨0, fun k _ => ⟨σ₀, hσ₀, fun σ hσ hσ' p hp => ⟨0, fun Cs _ E hE =>
        ⟨64, fun n₀ hn₀ => ⟨0, fun CE _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩
    obtain ⟨y₀, hy⟩ := hC Cf C c.δ₂ κ σ 0 hδ₂ hκ hκ' hσ
    refine ⟨max y₀ 1, fun y₁ hy₁ => ⟨le_trans (by norm_num) hn₀, fun t x hx F hF V hV => ?_⟩⟩
    have hxy : y₁ ≤ x := hx
    have hx0 : y₀ ≤ x := le_trans (le_trans (le_max_left _ _) hy₁) hxy
    have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) hy₁) hxy
    obtain ⟨-, h16, hg, hxω, hxe, -⟩ := hy x hx0
    exact ⟨C, (hFr κ σ x (frameRadius x) t n₀ hκ hκ' hσ hσ' hx1 h16 hn₀ hg hxω hxe F V hF hV).2.1 false⟩
  refine weaken _ _ (fun T hT h t x hx f hf F hF V hV => ?_) (join _ _ hF hCold)
  obtain ⟨⟨hn₂, hsm⟩, hco⟩ := h
  obtain ⟨C, small⟩ := hsm t x hx F hF V hV
  have hFL := hF.1
  have hFt := hF.2.1
  obtain ⟨n, hside, hn⟩ := hF.2.2
  have hodd : Odd F.blockSide := by rw [hFL]; exact hT.odd_L
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside]
    omega
  have hM : ChartEquivariance F T.a := hCh F T.a hodd hs
  have hLow : IsCubicTorusAbove T.L t T.n₀ F := ⟨hFL, hFt, n, hside,
    le_trans hn (Nat.le_mul_of_pos_right n hT.odd_L.pos)⟩
  have hcoldη : ∀ η : Vars F, (∀ b, ‖η b‖ < T.ballRadius) →
      IsSmallCurvature T.σ (fieldAboveFrame false T.a T.chainParams.ρA (frameRadius x) V η) := fun η hη =>
    hco t x hx F hF V hV η fun b => (hη b).le
  have hflat : IsSmallCurvature T.σ (uniformField F F.depth) := fun q _ => by
    have : plaquetteDefect (uniformField F F.depth) q = 0 := by
      simp [plaquetteDefect, plaquetteHolonomy, pathHolonomy, linkValue, uniformField]
    rw [this]
    exact hT.σ_pos
  refine ⟨fun Y γ => ?_, fun Y h => ?_⟩
  · choose A hA using fun b : ↥(chordBonds (finiteCells F)) => hAd (γ (enclosingCell b.1.1))
    have hfr : ∀ b ∈ chordBonds (finiteCells F),
        stepFrame false T.a T.chainParams.ρA (frameRadius x) b (gaugeTransform γ V) =
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (stepFrame false T.a T.chainParams.ρA (frameRadius x) b V) :=
      fun b hb => Subtype.ext (small.gauge_covariant b hb γ)
    have hrow : ∀ (y : F.Site F.depth) (η : Vars F), (∀ b, ‖η b‖ < T.ballRadius) →
        centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y (rotateVars A η) (gaugeTransform γ V) =
          centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y η V := fun y η hη => by
      unfold centredExpansion subtractTrivial
      rw [fieldAboveFrame_gauge hM hfr hA,
        hf.gauge_invariant F hLow y _ (blockConstantGauge γ) (hcoldη η hη)]
    exact densities_eq_of_changeOfVariables
      (changeOfVariables_gauge (ρ := T.ballRadius) (lam := T.chainParams.lam) (p := T.p) (x := x)
        hM hfr hA Y hrow)
  · have hcar : ∀ b ∈ chordBonds (finiteCells F),
        stepFrame false T.a T.chainParams.ρA (frameRadius x) (b.1 + cellCentre F.depth h, b.2)
            (translateField h V) =
          stepFrame false T.a T.chainParams.ρA (frameRadius x) b V :=
      fun b hb => small.translation_invariant b hb h
    have hrow : ∀ (y : F.Site F.depth) (η : Vars F), (∀ b, ‖η b‖ < T.ballRadius) →
        centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y (translateVars (chordTranslate hM h) η)
            (translateField h V) =
          centredExpansion false T.a T.chainParams.ρA (frameRadius x) f (y - cellCentre F.depth h) η V :=
        fun y η hη => by
      have h1 := hf.translation_invariant F hLow (y - cellCentre F.depth h) (cellCentre F.depth h) _
        (hcoldη η hη)
      have h2 := hf.translation_invariant F hLow (y - cellCentre F.depth h) (cellCentre F.depth h) _ hflat
      rw [sub_add_cancel] at h1 h2
      unfold centredExpansion subtractTrivial
      rw [fieldAboveFrame_translate hM hcar, h1]
      congr 1
    exact densities_eq_of_changeOfVariables
      (changeOfVariables_translate (ρ := T.ballRadius) (lam := T.chainParams.lam) (p := T.p) (x := x)
        hM hcar Y hrow)
end YangMills.Construction.ColdStepAtMirrorFrames
end
