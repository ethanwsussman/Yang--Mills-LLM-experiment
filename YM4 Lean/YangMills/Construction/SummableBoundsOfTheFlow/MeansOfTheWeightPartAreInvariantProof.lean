import YangMills.Construction.ColdStepAtMirrorFrames.AdjointOnABond
import YangMills.Construction.ColdStepAtMirrorFrames.ChartUnderGaugesAndShifts
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionUnderAGaugeOfTheTopProof
import YangMills.Construction.SummableBoundsOfTheFlow.MeansOfTheWeightPartAreInvariant
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeBetweenComparesOnTwoToriProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheFramesBetween
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusComparison MeasureTheory
namespace Interpolation
variable {F : BlockFrame}
namespace RemainderInvariance
private abbrev StepVars (F : BlockFrame) : Type := StepVariable (finiteCells F)
private theorem cutoff_support {ρ : ℝ} {p : ℝ → ℝ} (η : StepVars F) (h : cutoffWeight ρ p η ≠ 0) :
    ∀ b, ‖η b‖ < ρ := fun b => by
  by_contra hb
  exact h (Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, hb]))
abbrev _root_.YangMills.DeltaSharedProofs.p502036 := @cutoff_support
private theorem cutoffMean_comp {ρ : ℝ} {p : ℝ → ℝ} {R : StepVars F → StepVars F}
    (hR : MeasurePreserving R volume volume) (hemb : MeasurableEmbedding R)
    (hcut : ∀ η, cutoffWeight ρ p (R η) = cutoffWeight ρ p η) {Ψ Ψ' H H' : StepVars F → ℝ}
    (hΨ : ∀ η, (∀ b, ‖η b‖ < ρ) → Ψ' (R η) = Ψ η) (hH : ∀ η, (∀ b, ‖η b‖ < ρ) → H' (R η) = H η) :
    cutoffMean ρ p Ψ' H' = cutoffMean ρ p Ψ H := by
  have e1 : ∫ η, H' η * (cutoffWeight ρ p η * Real.exp (- Ψ' η)) =
      ∫ η, H η * (cutoffWeight ρ p η * Real.exp (- Ψ η)) := by
    rw [← hR.integral_comp hemb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    by_cases h : cutoffWeight ρ p η = 0
    · simp only [hcut, h, zero_mul, mul_zero]
    · have hb := cutoff_support η h
      simp only [hcut, hΨ η hb, hH η hb]
  have e2 : ∫ η, cutoffWeight ρ p η * Real.exp (- Ψ' η) = ∫ η, cutoffWeight ρ p η * Real.exp (- Ψ η) := by
    rw [← hR.integral_comp hemb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    by_cases h : cutoffWeight ρ p η = 0
    · simp only [hcut, h, zero_mul]
    · have hb := cutoff_support η h
      simp only [hcut, hΨ η hb]
  unfold cutoffMean
  rw [e1, e2]
abbrev _root_.YangMills.DeltaSharedProofs.p500520 := @cutoffMean_comp
structure TermPreservingChange (s a ρA ρ lam x : ℝ) (m : ℕ) (p : ℝ → ℝ) (V V' : F.GaugeField F.top)
    (Y Y' : F.Cell) (R : StepVariable (finiteCells F) → StepVariable (finiteCells F)) : Prop where
  measurePreserving : MeasurePreserving R volume volume
  measurableEmbedding : MeasurableEmbedding R
  cutoffWeight_eq : ∀ η, cutoffWeight ρ p (R η) = cutoffWeight ρ p η
  totalQuadratic_eq : ∀ η, totalQuadratic lam x (R η) = totalQuadratic lam x η
  cellQuadratic_eq : ∀ η, cellQuadratic lam x Y' (R η) = cellQuadratic lam x Y η
  exponent_eq : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
    interpolatedExponent s a ρA x m V' (R η) = interpolatedExponent s a ρA x m V η
  blockExponent_eq : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
    interpolatedBlockExponent s a ρA x m Y' V' (R η) = interpolatedBlockExponent s a ρA x m Y V η
private theorem cutoffMean_eq {s a ρA ρ lam x : ℝ} {m : ℕ} {p : ℝ → ℝ} {V V' : F.GaugeField F.top}
    {Y Y' : F.Cell} {R : StepVars F → StepVars F} (M : TermPreservingChange s a ρA ρ lam x m p V V' Y Y' R) (τ : ℝ) :
    cutoffMean ρ p (weightLawExponent s a ρA lam x m τ V') (cellExponentRemainder s a ρA lam x m Y' V') =
      cutoffMean ρ p (weightLawExponent s a ρA lam x m τ V) (cellExponentRemainder s a ρA lam x m Y V) :=
  cutoffMean_comp M.measurePreserving M.measurableEmbedding M.cutoffWeight_eq
    (fun η hη => by simp only [weightLawExponent, M.exponent_eq η hη, M.totalQuadratic_eq η])
    (fun η hη => by simp only [cellExponentRemainder, M.blockExponent_eq η hη, M.cellQuadratic_eq η])
private theorem chartedField_congr {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions} (V : F.GaugeField F.top)
    (hw : ∀ x i, ¬ IsAxialTreeBond (x, i) → w x i = w' x i) : chartedField w V = chartedField w' V := by apply _root_.YangMills.SharedProofs.p16263 <;> assumption
private theorem adjointAction_add (g : UnitQuaternion) (X Y : imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (X + Y) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X + _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g Y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add <;> assumption
private theorem adjointAction_smul (g : UnitQuaternion) (c : ℝ) (X : imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (c • X) = c • _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_smul <;> assumption
private theorem norm_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) :
    ‖_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X‖ = ‖X‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction <;> assumption
section Gauge
variable {s a ρA x : ℝ} {m : ℕ} {V : F.GaugeField F.top} {γ : F.Cell → UnitQuaternion}
private theorem chartedEnergy_gauge (hM : ChartEquivariance F a) {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ y i, ¬ IsAxialTreeBond (y, i) → w' y i = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (w y i)) :
    chartedEnergy a w' (gaugeTransform γ V) = chartedEnergy a w V := by
  unfold chartedEnergy
  rw [chartedField_congr (gaugeTransform γ V) hw, hM.chartedField_gaugeTransform, hM.energy_gaugeTransform]
abbrev _root_.YangMills.SharedProofs.p19410 := @chartedEnergy_gauge
private theorem chartedSlope_gauge (hM : ChartEquivariance F a) {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ y i, ¬ IsAxialTreeBond (y, i) → w' y i = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (w y i))
    (b : F.Site F.depth × Fin 4) (hb : ¬ IsAxialTreeBond b) (e : imaginaryQuaternions) :
    chartedSlope a w' (gaugeTransform γ V) b (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) e) = chartedSlope a w V b e := by
  unfold chartedSlope
  congr 1
  funext u
  apply chartedEnergy_gauge hM
  intro y i hnt
  by_cases h1 : y = b.1
  · subst h1
    by_cases h2 : i = b.2
    · subst h2
      simp only [Function.update_self]
      rw [hw _ _ hb, _root_.YangMills.Construction.Interpolation.RemainderInvariance.adjointAction_add, _root_.YangMills.Construction.Interpolation.RemainderInvariance.adjointAction_smul]
    · simp only [Function.update_self, Function.update_of_ne h2]
      exact hw _ _ hnt
  · simp only [Function.update_of_ne h1]
    exact hw _ _ hnt
abbrev _root_.YangMills.SharedProofs.p24183 := @chartedSlope_gauge
private def rotateBonds (A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector) (η : StepVars F) :
    StepVars F :=
  fun b => A b (η b)
private theorem interpolatedCoords_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), interpolatedFrame s a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame s a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v)) (η : StepVars F)
    (y : F.Site F.depth) (i : Fin 4) (hnt : ¬ IsAxialTreeBond (y, i)) :
    interpolatedCoords s a ρA m (gaugeTransform γ V) (rotateBonds A η) y i =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell y)) (interpolatedCoords s a ρA m V η y i) := by
  have hb : (y, i) ∈ chordBonds (finiteCells F) := hM.mem_chordBonds_of_not_tree _ hnt
  unfold interpolatedCoords stepCoordinates
  rw [dif_pos hb, dif_pos hb, hfr _ hb, _root_.YangMills.Construction.Interpolation.RemainderInvariance.adjointAction_add]
  congr 1
  exact hA ⟨(y, i), hb⟩ (η ⟨(y, i), hb⟩)
private theorem interpolatedField_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), interpolatedFrame s a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame s a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v)) (η : StepVars F) :
    interpolatedField s a ρA m (gaugeTransform γ V) (rotateBonds A η) =
      gaugeTransform (blockConstantGauge γ) (interpolatedField s a ρA m V η) := by
  unfold interpolatedField
  rw [chartedField_congr (gaugeTransform γ V) (interpolatedCoords_gauge hM hfr hA η), hM.chartedField_gaugeTransform]
private theorem haarGapExcess_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), interpolatedFrame s a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame s a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v)) (η : StepVars F)
    (c : F.Site F.top × Fin 4) :
    haarGapExcess a x (interpolatedField s a ρA m (gaugeTransform γ V) (rotateBonds A η)) c =
      haarGapExcess a x (interpolatedField s a ρA m V η) c := by
  unfold haarGapExcess
  rw [interpolatedField_gauge hM hfr hA, hM.norm_contourAverage_gaugeTransform]
private theorem haarLogRatio_gauge (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), interpolatedFrame s a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame s a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v)) (η : StepVars F)
    (b : ↥(chordBonds (finiteCells F))) (hnt : ¬ IsAxialTreeBond b.1) :
    haarLogRatio (interpolatedCoords s a ρA m (gaugeTransform γ V) (rotateBonds A η) b.1.1 b.1.2) =
      haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) := by
  unfold haarLogRatio
  rw [interpolatedCoords_gauge hM hfr hA η _ _ hnt, _root_.YangMills.Construction.Interpolation.RemainderInvariance.norm_adjointAction]
private theorem rotateBonds_smul {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector} (v : ℝ)
    (η : StepVars F) : v • rotateBonds A η = rotateBonds A (v • η) := by
  funext b
  simp [rotateBonds]
private theorem rotateBonds_zero {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector} :
    rotateBonds A (0 : StepVars F) = 0 := by
  funext b
  simp [rotateBonds]
private theorem not_axialTree_of_chord (b : ↥(chordBonds (finiteCells F))) : ¬ IsAxialTreeBond b.1 := by
  classical
  have := b.2
  unfold chordBonds at this
  exact (Finset.mem_filter.mp this).2
abbrev _root_.YangMills.SharedProofs.p29908 := @not_axialTree_of_chord
private theorem gauge_termPreserving {ρ lam : ℝ} {p : ℝ → ℝ} (hM : ChartEquivariance F a)
    (hfr : ∀ b ∈ chordBonds (finiteCells F), interpolatedFrame s a ρA m b (gaugeTransform γ V) =
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame s a ρA m b V))
    {A : ↥(chordBonds (finiteCells F)) → BondVector ≃ₗᵢ[ℝ] BondVector}
    (hA : ∀ b v, toImaginary (A b v) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary v)) (Y : F.Cell) :
    TermPreservingChange s a ρA ρ lam x m p V (gaugeTransform γ V) Y Y (rotateBonds A) := by
  have hpres : MeasurePreserving (rotateBonds A) volume volume :=
    measurePreserving_pi _ _ fun b => (A b).measurePreserving
  have hemb : MeasurableEmbedding (rotateBonds A) := by
    have hhom : rotateBonds A = (Homeomorph.piCongrRight fun b => (A b).toHomeomorph) := by
      funext η b
      rfl
    rw [hhom]
    exact Homeomorph.measurableEmbedding _
  have hnorm : ∀ (η : StepVars F) b, ‖rotateBonds A η b‖ = ‖η b‖ := fun η b => (A b).norm_map _
  have hzero : ∀ η : StepVars F, chartedEnergy a (interpolatedCoords s a ρA m (gaugeTransform γ V) (rotateBonds A η))
      (gaugeTransform γ V) = chartedEnergy a (interpolatedCoords s a ρA m V η) V := fun η =>
    chartedEnergy_gauge hM (interpolatedCoords_gauge hM hfr hA η)
  refine ⟨hpres, hemb, fun η => ?_, fun η => ?_, fun η => ?_, fun η hη => ?_, fun η hη => ?_⟩
  · simp only [cutoffWeight, hnorm]
  · simp only [totalQuadratic, hnorm]
  · simp only [cellQuadratic, hnorm]
  · unfold interpolatedExponent
    have h0 := hzero 0
    rw [rotateBonds_zero] at h0
    rw [hzero η, h0]
    have g1 : ∑ b : ↥(chordBonds (finiteCells F)),
        haarLogRatio (interpolatedCoords s a ρA m (gaugeTransform γ V) (rotateBonds A η) b.1.1 b.1.2) =
        ∑ b : ↥(chordBonds (finiteCells F)), haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) :=
      Finset.sum_congr rfl fun b _ => haarLogRatio_gauge hM hfr hA η b (not_axialTree_of_chord b)
    have g2 : ∑ c ∈ innerBonds (finiteCells F) F.top,
        haarGapExcess a x (interpolatedField s a ρA m (gaugeTransform γ V) (rotateBonds A η)) c =
        ∑ c ∈ innerBonds (finiteCells F) F.top, haarGapExcess a x (interpolatedField s a ρA m V η) c :=
      Finset.sum_congr rfl fun c _ => haarGapExcess_gauge hM hfr hA η c
    rw [g1, g2]
  · unfold interpolatedBlockExponent
    have g1 : ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y then
        ∫ v in (0 : ℝ)..1, chartedSlope a (interpolatedCoords s a ρA m (gaugeTransform γ V) (v • rotateBonds A η))
          (gaugeTransform γ V) b.1 (toImaginary (rotateBonds A η b)) else 0) =
        ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y then
        ∫ v in (0 : ℝ)..1, chartedSlope a (interpolatedCoords s a ρA m V (v • η)) V b.1
          (toImaginary (η b)) else 0) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs
      · apply intervalIntegral.integral_congr
        intro v _
        simp only
        rw [rotateBonds_smul]
        have h1 : toImaginary (rotateBonds A η b) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1.1)) (toImaginary (η b)) :=
          hA b (η b)
        rw [h1]
        exact chartedSlope_gauge hM (interpolatedCoords_gauge hM hfr hA (v • η)) b.1 (not_axialTree_of_chord b) _
      · rfl
    have g2 : ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        haarGapExcess a x (interpolatedField s a ρA m (gaugeTransform γ V) (rotateBonds A η)) c =
        ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
          haarGapExcess a x (interpolatedField s a ρA m V η) c :=
      Finset.sum_congr rfl fun c _ => haarGapExcess_gauge hM hfr hA η c
    have g3 : ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y then
        haarLogRatio (interpolatedCoords s a ρA m (gaugeTransform γ V) (rotateBonds A η) b.1.1 b.1.2) else 0) =
        ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y then
        haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) else 0) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs
      · exact haarLogRatio_gauge hM hfr hA η b (not_axialTree_of_chord b)
      · rfl
    rw [g1, g2, g3]
end Gauge
section Shift
variable {s a ρA x : ℝ} {m : ℕ} {V : F.GaugeField F.top} {h : F.Cell}
private def translateBonds (hM : ChartEquivariance F a) (h : F.Cell) :
    ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F)) where
  toFun b := ⟨(b.1.1 + cellCentre F.depth h, b.1.2), (hM.chordBonds_translate h b.1).mpr b.2⟩
  invFun b := ⟨(b.1.1 - cellCentre F.depth h, b.1.2),
    (hM.chordBonds_translate h (b.1.1 - cellCentre F.depth h, b.1.2)).mp (by simpa using b.2)⟩
  left_inv b := Subtype.ext (by simp)
  right_inv b := Subtype.ext (by simp)
private def translateVars (e : ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F))) (η : StepVars F) :
    StepVars F :=
  fun b => η (e.symm b)
private theorem translateVars_eq (e : ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F))) :
    translateVars e =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) e) := by
  funext η b
  obtain ⟨b', rfl⟩ := e.surjective b
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp [translateVars]
private theorem chartedEnergy_shift (hM : ChartEquivariance F a) {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ y i, ¬ IsAxialTreeBond (y, i) → w' y i = w (y - cellCentre F.depth h) i) :
    chartedEnergy a w' (translateField h V) = chartedEnergy a w V := by
  unfold chartedEnergy
  rw [chartedField_congr (translateField h V) hw, hM.chartedField_translate, hM.energy_translate]
abbrev _root_.YangMills.SharedProofs.p9314 := @chartedEnergy_shift
private theorem chartedSlope_shift (hM : ChartEquivariance F a) {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hw : ∀ y i, ¬ IsAxialTreeBond (y, i) → w' y i = w (y - cellCentre F.depth h) i)
    (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions) :
    chartedSlope a w' (translateField h V) (b.1 + cellCentre F.depth h, b.2) e = chartedSlope a w V b e := by
  unfold chartedSlope
  congr 1
  funext u
  apply chartedEnergy_shift hM
  intro y i hnt
  by_cases h1 : y = b.1 + cellCentre F.depth h
  · subst h1
    simp only [add_sub_cancel_right, Function.update_self]
    by_cases h2 : i = b.2
    · subst h2
      simp only [Function.update_self]
      rw [hw _ _ hnt, add_sub_cancel_right]
    · simp only [Function.update_of_ne h2]
      rw [hw _ _ hnt, add_sub_cancel_right]
  · have h3 : y - cellCentre F.depth h ≠ b.1 := fun h4 => h1 (by rw [← h4, sub_add_cancel])
    simp only [Function.update_of_ne h1, Function.update_of_ne h3]
    exact hw _ _ hnt
abbrev _root_.YangMills.SharedProofs.p4342 := @chartedSlope_shift
private theorem interpolatedCoords_shift (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      interpolatedFrame s a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) = interpolatedFrame s a ρA m b V)
    (η : StepVars F) (y : F.Site F.depth) (i : Fin 4) (hnt : ¬ IsAxialTreeBond (y, i)) :
    interpolatedCoords s a ρA m (translateField h V) (translateVars (translateBonds hM h) η) y i =
      interpolatedCoords s a ρA m V η (y - cellCentre F.depth h) i := by
  have hb : (y, i) ∈ chordBonds (finiteCells F) := hM.mem_chordBonds_of_not_tree _ hnt
  have hb0 : (y - cellCentre F.depth h, i) ∈ chordBonds (finiteCells F) :=
    (hM.chordBonds_translate h (y - cellCentre F.depth h, i)).mp (by simpa using hb)
  have hf := hcar _ hb0
  simp only [sub_add_cancel] at hf
  unfold interpolatedCoords stepCoordinates
  rw [dif_pos hb, dif_pos hb0, hf]
  rfl
private theorem interpolatedField_shift (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      interpolatedFrame s a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) = interpolatedFrame s a ρA m b V)
    (η : StepVars F) :
    interpolatedField s a ρA m (translateField h V) (translateVars (translateBonds hM h) η) =
      translateField (cellCentre F.depth h) (interpolatedField s a ρA m V η) := by
  unfold interpolatedField
  rw [chartedField_congr (translateField h V) (interpolatedCoords_shift hM hcar η), hM.chartedField_translate]
private theorem haarGapExcess_shift (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      interpolatedFrame s a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) = interpolatedFrame s a ρA m b V)
    (η : StepVars F) (c : F.Site F.top × Fin 4) :
    haarGapExcess a x (interpolatedField s a ρA m (translateField h V) (translateVars (translateBonds hM h) η)) c =
      haarGapExcess a x (interpolatedField s a ρA m V η) (c.1 - h, c.2) := by
  unfold haarGapExcess
  rw [interpolatedField_shift hM hcar, hM.contourAverage_translate]
private theorem sum_innerBonds_sub (hM : ChartEquivariance F a) (h : F.Cell) (G : F.Site F.top × Fin 4 → ℝ) :
    ∑ c ∈ innerBonds (finiteCells F) F.top, G (c.1 - h, c.2) = ∑ c ∈ innerBonds (finiteCells F) F.top, G c := by
  refine Finset.sum_nbij' (fun c => (c.1 - h, c.2)) (fun c => (c.1 + h, c.2)) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    exact (hM.innerBonds_translate h _).mp (by simpa using hc)
  · intro c hc
    exact (hM.innerBonds_translate h _).mpr hc
  · intro c _
    simp
  · intro c _
    simp
  · intro c _
    rfl
abbrev _root_.YangMills.SharedProofs.p4672 := @sum_innerBonds_sub
private theorem translateVars_smul (e : ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F))) (v : ℝ)
    (η : StepVars F) : v • translateVars e η = translateVars e (v • η) := rfl
private theorem translateVars_zero (e : ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F))) :
    translateVars e (0 : StepVars F) = 0 := rfl
private theorem translate_termPreserving {ρ lam : ℝ} {p : ℝ → ℝ} (hM : ChartEquivariance F a)
    (hcar : ∀ b ∈ chordBonds (finiteCells F),
      interpolatedFrame s a ρA m (b.1 + cellCentre F.depth h, b.2) (translateField h V) = interpolatedFrame s a ρA m b V)
    (Y : F.Cell) :
    TermPreservingChange s a ρA ρ lam x m p V (translateField h V) Y (Y + h) (translateVars (translateBonds hM h)) := by
  set e := translateBonds hM h with he
  have happ : ∀ (η : StepVars F) b, translateVars e η (e b) = η b := fun η b => by simp [translateVars]
  have hcell : ∀ b : ↥(chordBonds (finiteCells F)), enclosingCell (e b).1.1 = enclosingCell b.1.1 + h := fun b =>
    hM.enclosingCell_translate h b.1.1
  have hY : ∀ Z : F.Cell, Z + h = Y + h ↔ Z = Y := fun Z => add_left_inj h
  have hhaarAt : ∀ (η : StepVars F) (b : ↥(chordBonds (finiteCells F))),
      haarLogRatio (interpolatedCoords s a ρA m (translateField h V) (translateVars e η) (e b).1.1 (e b).1.2) =
        haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) := fun η b => by
    have hnt : ¬ IsAxialTreeBond (e b).1 := not_axialTree_of_chord _
    have h1 := interpolatedCoords_shift hM hcar η (e b).1.1 (e b).1.2 hnt
    have h2 : (e b).1.1 - cellCentre F.depth h = b.1.1 := by simp [he, translateBonds]
    have h3 : (e b).1.2 = b.1.2 := rfl
    rw [h2, h3] at h1
    rw [h3, h1]
  have hzero : ∀ η : StepVars F, chartedEnergy a (interpolatedCoords s a ρA m (translateField h V) (translateVars e η))
      (translateField h V) = chartedEnergy a (interpolatedCoords s a ρA m V η) V := fun η =>
    chartedEnergy_shift hM (interpolatedCoords_shift hM hcar η)
  refine ⟨?_, ?_, fun η => ?_, fun η => ?_, fun η => ?_, fun η hη => ?_, fun η hη => ?_⟩
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
  · unfold interpolatedExponent
    have h0 := hzero 0
    rw [translateVars_zero] at h0
    rw [hzero η, h0]
    have g1 : ∑ c ∈ innerBonds (finiteCells F) F.top,
        haarGapExcess a x (interpolatedField s a ρA m (translateField h V) (translateVars e η)) c =
        ∑ c ∈ innerBonds (finiteCells F) F.top, haarGapExcess a x (interpolatedField s a ρA m V η) c := by
      simp only [he, haarGapExcess_shift hM hcar η]
      exact sum_innerBonds_sub hM h fun c => haarGapExcess a x (interpolatedField s a ρA m V η) c
    have g2 : ∑ b : ↥(chordBonds (finiteCells F)),
        haarLogRatio (interpolatedCoords s a ρA m (translateField h V) (translateVars e η) b.1.1 b.1.2) =
        ∑ b : ↥(chordBonds (finiteCells F)), haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) := by
      rw [← Equiv.sum_comp e]
      exact Finset.sum_congr rfl fun b _ => hhaarAt η b
    rw [g1, g2]
  · unfold interpolatedBlockExponent
    have g1 : ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y + h then
        ∫ v in (0 : ℝ)..1, chartedSlope a (interpolatedCoords s a ρA m (translateField h V) (v • translateVars e η))
          (translateField h V) b.1 (toImaginary (translateVars e η b)) else 0) =
        ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y then
        ∫ v in (0 : ℝ)..1, chartedSlope a (interpolatedCoords s a ρA m V (v • η)) V b.1
          (toImaginary (η b)) else 0) := by
      rw [← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [hcell, hY, happ]
      split_ifs
      · apply intervalIntegral.integral_congr
        intro v _
        simp only
        rw [translateVars_smul]
        exact chartedSlope_shift hM (interpolatedCoords_shift hM hcar (v • η)) b.1 _
      · rfl
    have g2 : ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y + h),
        haarGapExcess a x (interpolatedField s a ρA m (translateField h V) (translateVars e η)) c =
        ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
          haarGapExcess a x (interpolatedField s a ρA m V η) c := by
      rw [Finset.sum_filter, Finset.sum_filter,
        ← sum_innerBonds_sub hM h fun c => if c.1 = Y then haarGapExcess a x (interpolatedField s a ρA m V η) c else 0]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hc : c.1 - h = Y ↔ c.1 = Y + h := sub_eq_iff_eq_add
      simp only [hc]
      split_ifs
      · exact haarGapExcess_shift hM hcar η c
      · rfl
    have g3 : ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y + h then
        haarLogRatio (interpolatedCoords s a ρA m (translateField h V) (translateVars e η) b.1.1 b.1.2) else 0) =
        ∑ b : ↥(chordBonds (finiteCells F)), (if enclosingCell b.1.1 = Y then
        haarLogRatio (interpolatedCoords s a ρA m V η b.1.1 b.1.2) else 0) := by
      rw [← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [hcell, hY, hhaarAt]
    rw [g1, g2, g3]
end Shift
end RemainderInvariance
open RemainderInvariance in
theorem remainderMeansInvariant_holds (hJ : EventuallyInParametersCombines) (hW : interpolatedFramesStatement)
    (hCh : chartEquivarianceStatement) (hAd : AdjointActionLinearIsometry) :
    remainderMeansInvariant := by
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cq, Cz, Cr, hW⟩ := hW
  have h2 : EventuallyInParameters fun T => 2 ≤ T.n₀ := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨2, fun _ h => ⟨0, fun _ _ => ⟨0, fun _ _ => h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine weaken _ _ (fun T hT h t x s τ F V hx hs hs1 hF hV => ?_) (join _ _ h2 hW)
  obtain ⟨hn₂, hfr⟩ := h
  have small := ((hfr t x hx).one_torus F V s hF hV hs hs1).small
  obtain ⟨n, hside, hn⟩ := hF.2.2
  have hodd : Odd F.blockSide := by rw [hF.1]; exact hT.odd_L
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside]
    omega
  have hM : ChartEquivariance F T.a := hCh F T.a hodd hs2
  refine ⟨fun Y γ => ?_, fun Y h => ?_⟩
  · choose A hA using fun b : ↥(chordBonds (finiteCells F)) => hAd (γ (enclosingCell b.1.1))
    have hfr' : ∀ b ∈ chordBonds (finiteCells F),
        interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b (gaugeTransform γ V) =
          _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell b.1)) (interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b V) :=
      fun b hb => Subtype.ext (small.gauge_covariant b hb γ)
    exact cutoffMean_eq
      (gauge_termPreserving (ρ := T.ballRadius) (lam := T.chainParams.lam) (p := T.p) (x := x) hM hfr' hA Y) τ
  · have hcar : ∀ b ∈ chordBonds (finiteCells F),
        interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) (b.1 + cellCentre F.depth h, b.2) (translateField h V) =
          interpolatedFrame s T.a T.chainParams.ρA (frameRadius x) b V := fun b hb => small.translation_invariant b hb h
    exact cutoffMean_eq
      (translate_termPreserving (ρ := T.ballRadius) (lam := T.chainParams.lam) (p := T.p) (x := x) hM hcar Y) τ
end Interpolation
end YangMills.Construction
end
