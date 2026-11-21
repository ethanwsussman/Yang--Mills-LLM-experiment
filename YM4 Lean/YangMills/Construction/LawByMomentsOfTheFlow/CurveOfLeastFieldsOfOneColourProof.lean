import YangMills.Construction.ColdStepAtMirrorFrames.TreeResponseOfTheLeastCoordinatesProof
import YangMills.Construction.LawByMomentsOfTheFlow.CurveOfLeastFieldsOfOneColour
import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheMaxwellFormProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
noncomputable section
set_option linter.unusedSectionVars false
open scoped Quaternion Topology
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps TopLevelSites
open WeightedResponses ResponseInTheExpansion ResponseInTheExpansion.SingleColourFields
namespace MomentLaw
namespace MinimizerCurve
section PathSums
variable {N : ℕ}
private theorem contourSum_zero (L : ℕ) {n : ℕ} (c : TorusBond n) (k : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) :
    contourSum L (0 : TorusBond N → ℝ) c k = 0 := by apply _root_.YangMills.SharedProofs.p22967 <;> assumption
end PathSums
section AnglePairs
variable {L n : ℕ} [NeZero L] [NeZero n]
private abbrev AnglePair (L n : ℕ) : Type := (TorusBond (n * L) → ℝ) × (TorusBond n → ℝ)
private def pairFit (L : ℕ) (p : AnglePair L n) (c : TorusBond n) : ℝ :=
  Real.sqrt (contourCosMean L p.1 c 1 ^ 2 + contourSinMean L p.1 c 1 ^ 2) -
    (contourCosMean L p.1 c 1 * Real.cos (1 * p.2 c) + contourSinMean L p.1 c 1 * Real.sin (1 * p.2 c))
private theorem contourCosMean_zero (hL : Odd L) (c : TorusBond n) :
    contourCosMean L (0 : TorusBond (n * L) → ℝ) c 1 = 1 := by apply _root_.YangMills.SharedProofs.p15344 <;> assumption
private theorem contourSinMean_zero (c : TorusBond n) : contourSinMean L (0 : TorusBond (n * L) → ℝ) c 1 = 0 := by
  simp [contourSinMean, contourSum_zero]
private theorem pairFit_zero (hL : Odd L) (c : TorusBond n) : pairFit L (0 : AnglePair L n) c = 0 := by
  unfold pairFit
  have e1 : contourCosMean L (0 : AnglePair L n).1 c 1 = 1 := contourCosMean_zero hL c
  have e2 : contourSinMean L (0 : AnglePair L n).1 c 1 = 0 := contourSinMean_zero c
  rw [e1, e2]
  simp
private def colourAction (a : ℝ) (L t : ℕ) {m : ℕ} [NeZero m] (θ : TorusBond m → ℝ) : ℝ :=
  actionAtLevel a L t Finset.univ (expOfColourForm 1 θ)
private def pairEnergy (a : ℝ) (L u : ℕ) [NeZero L] (p : AnglePair L n) : ℝ :=
  colourAction a L u p.1 + a * ∑ c : TorusBond n, pairFit L p c
end AnglePairs
section OnTheFrame
variable {L n u : ℕ} [NeZero L] [NeZero n]
private theorem period_depth (L u n : ℕ) [NeZero L] [NeZero n] (i : Fin 4) :
    (torusFrame L u n).period u i = n * L :=
  period_depth_of_extent (F := torusFrame L u n) (n := n) (fun _ => rfl) i
private theorem period_top (L u n : ℕ) [NeZero L] [NeZero n] (i : Fin 4) :
    (torusFrame L u n).period (u + 1) i = n :=
  period_top_of_extent (F := torusFrame L u n) (n := n) (fun _ => rfl) i
private theorem extent_pos (L u n : ℕ) [NeZero n] (i : Fin 4) : 0 < (torusFrame L u n).extent i :=
  Nat.pos_of_ne_zero (NeZero.ne n)
private theorem minimalAction_readAtLevel {a : ℝ} (hCut : ActionAtLevelIsCutAction)
    (hWhole : WholeCellCostEqualsMinimalAction) (ha : 0 ≤ a) (hL : Odd L) (W : TorusField (n * L)) :
    minimalAction a (finiteCells (torusFrame L u n)) u (readAtLevel (torusFrame L u n) u W) =
      actionAtLevel a L u Finset.univ W := by apply _root_.YangMills.SharedProofs.p88272 <;> assumption
private theorem sum_innerBonds (hL : Odd L) (f : (torusFrame L u n).Site (u + 1) × Fin 4 → ℝ) :
    ∑ c ∈ innerBonds (finiteCells (torusFrame L u n)) (u + 1), f c =
      ∑ c : TorusBond n, f (StepCosts.torusSiteInFrame (torusFrame L u n) (u + 1) c.1, c.2) := by apply _root_.YangMills.SharedProofs.p37826 <;> assumption
private theorem blockEnergy_readAtLevel {a : ℝ} (hCut : ActionAtLevelIsCutAction)
    (hWhole : WholeCellCostEqualsMinimalAction) (ha : 0 ≤ a) (hL : Odd L) (p : AnglePair L n) :
    blockEnergy a (finiteCells (torusFrame L u n)) u (readAtLevel (torusFrame L u n) u (expOfColourForm 1 p.1))
      (readAtLevel (torusFrame L u n) (u + 1) (expOfColourForm 1 p.2)) = pairEnergy a L u p := by
  unfold blockEnergy pairEnergy colourAction
  rw [minimalAction_readAtLevel hCut hWhole ha hL, sum_innerBonds hL]
  congr 2
  refine Finset.sum_congr rfl fun c _ => ?_
  exact blockFit_readAtLevel (G := torusFrame L u n) (period_depth L u n) (period_top L u n) 1 p.1 p.2 c
private theorem blockEnergy_nonneg' {a : ℝ} (hWhole : WholeCellCostEqualsMinimalAction)
    (hLeast : CutActionEqualsMinimalAction) (ha : 0 ≤ a) (hL : Odd L)
    (W : (torusFrame L u n).GaugeField u) (V : (torusFrame L u n).GaugeField (u + 1)) :
    0 ≤ blockEnergy a (finiteCells (torusFrame L u n)) u W V := by apply _root_.YangMills.SharedProofs.p2190 <;> assumption
private theorem colourAction_zero {a : ℝ} (hCut : ActionAtLevelIsCutAction)
    (hWhole : WholeCellCostEqualsMinimalAction) (hFlat : flatTopVanishingStatement) (ha : 0 ≤ a) (hL : Odd L) :
    colourAction a L u (0 : TorusBond (n * L) → ℝ) = 0 := by apply _root_.YangMills.DeltaSharedProofs.p501681 <;> assumption
private theorem pairEnergy_zero {a : ℝ} (hCut : ActionAtLevelIsCutAction)
    (hWhole : WholeCellCostEqualsMinimalAction) (hFlat : flatTopVanishingStatement) (ha : 0 ≤ a) (hL : Odd L) :
    pairEnergy (n := n) a L u 0 = 0 := by
  unfold pairEnergy
  have e1 : colourAction a L u (0 : AnglePair L n).1 = 0 := colourAction_zero hCut hWhole hFlat ha hL
  rw [e1]
  simp [pairFit_zero hL]
private theorem readAtLevel_top (B : TorusBond n → ℝ) (τ : ℝ) (c : TorusBond n) :
    readAtLevel (torusFrame L u n) (u + 1) (expOfColourForm τ B)
      (StepCosts.torusSiteInFrame (torusFrame L u n) (u + 1) c.1) c.2 = colourRotation (τ * B c) :=
  readAtLevel_torusSiteInFrame (period_top L u n) _ _ _
end OnTheFrame
private def halfRotation : UnitQuaternion := colourRotation (Real.pi / 2)
private theorem coe_halfTurn : ((halfRotation : UnitQuaternion) : ℍ[ℝ]) = colourPlane 0 1 := by
  rw [halfRotation, coe_colourRotation]
  simp
private theorem coe_halfTurn_inv : ((halfRotation⁻¹ : UnitQuaternion) : ℍ[ℝ]) = colourPlane 0 (-1) := by
  rw [halfRotation, colourRotation_inv, coe_colourRotation]
  simp
private theorem colourRotation_comm (s t : ℝ) : colourRotation s * colourRotation t = colourRotation t * colourRotation s := by
  rw [← colourRotation_add, ← colourRotation_add, add_comm]
private theorem halfRotation_conj (s : ℝ) : halfRotation * colourRotation s * halfRotation⁻¹ = colourRotation s := by
  rw [halfRotation, colourRotation_comm, mul_inv_cancel_right]
private theorem adjointAction_piRotation_components (w : imaginaryQuaternions) :
    ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction halfRotation w : imaginaryQuaternions) : ℍ[ℝ]).imJ = -(w : ℍ[ℝ]).imJ ∧
    ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction halfRotation w : imaginaryQuaternions) : ℍ[ℝ]).imK = -(w : ℍ[ℝ]).imK := by
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  have e : ((_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction halfRotation w : imaginaryQuaternions) : ℍ[ℝ]) =
      colourPlane 0 1 * (w : ℍ[ℝ]) * colourPlane 0 (-1) := by
    rw [← coe_halfTurn, ← coe_halfTurn_inv]
    rfl
  rw [e]
  simp only [Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_mul, Quaternion.imI_mul, colourPlane_re,
    colourPlane_imI, colourPlane_imJ, colourPlane_imK, hw]
  constructor <;> ring
private theorem neg_re_mul_unitGenerator (v : imaginaryQuaternions) :
    -((v : ℍ[ℝ]) * (unitGenerator : ℍ[ℝ])).re = (v : ℍ[ℝ]).imI := by apply _root_.YangMills.SharedProofs.p20434 <;> assumption
private theorem eq_imI_smul_of_fixed (w : imaginaryQuaternions) (h : ColdStepAtMirrorFrames.adjointAction halfRotation w = w) :
    w = (w : ℍ[ℝ]).imI • unitGenerator := by
  obtain ⟨h1, h2⟩ := adjointAction_piRotation_components w
  rw [h] at h1 h2
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  apply Subtype.ext
  apply Quaternion.ext
  · simp [hw, unitGenerator_re]
  · simp [unitGenerator_imI]
  · simp [unitGenerator_imJ]
    linarith
  · simp [unitGenerator_imK]
    linarith
private theorem adjointAction_zero' (g : UnitQuaternion) : ColdStepAtMirrorFrames.adjointAction g 0 = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_zero <;> assumption
private theorem norm_adjointAction (g : UnitQuaternion) (w : imaginaryQuaternions) :
    ‖ColdStepAtMirrorFrames.adjointAction g w‖ = ‖w‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction <;> assumption
section Minimizers
variable {L n u : ℕ} [NeZero L] [NeZero n]
private abbrev topField (L u : ℕ) {n : ℕ} (B : TorusBond n → ℝ) (τ : ℝ) :
    (torusFrame L u n).GaugeField (u + 1) :=
  readAtLevel (torusFrame L u n) (u + 1) (expOfColourForm τ B)
private theorem gaugeTransform_topField (B : TorusBond n → ℝ) (τ : ℝ) :
    gaugeTransform (fun _ => halfRotation) (topField L u B τ) = topField L u B τ := by
  funext y i
  show halfRotation * (expOfColourForm τ B (toTorusSite n y) i) * halfRotation⁻¹ = expOfColourForm τ B (toTorusSite n y) i
  rw [expOfColourForm_apply, halfRotation_conj]
private theorem eventually_curvature_lt (B : TorusBond n → ℝ) {σ : ℝ} (hσ : 0 < σ) (q : TorusSite n × Fin 4 × Fin 4) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), curvature (expOfColourForm τ B) q.1 q.2.1 q.2.2 < σ := by apply _root_.YangMills.SharedProofs.p47205 <;> assumption
private theorem eventually_isCold (B : TorusBond n → ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), IsCold (finiteCells (torusFrame L u n)) (u + 1) σ (topField L u B τ) := by apply _root_.YangMills.DeltaSharedProofs.p502287 <;> assumption
private structure StepHypotheses (a ρ δ σA N0 : ℝ) (Nn : ℕ → ℝ) (L u n : ℕ) [NeZero L] [NeZero n] : Prop where
  ha : 0 < a
  hL : Odd L
  h2n : 2 ≤ n
  hρ0 : 0 < ρ
  hρ : ρ < Real.pi
  hσ : 0 < σA
  unique : ∀ V : (torusFrame L u n).GaugeField (u + 1), IsCold (finiteCells (torusFrame L u n)) (u + 1) σA V →
    HasColdMinimizer a ρ N0 σA (finiteCells (torusFrame L u n)) V
  regular : HasRegularCoordinates a δ ρ Nn (finiteCells (torusFrame L u n))
    (ColdStepAtMirrorFrames.uniformField (torusFrame L u n) (torusFrame L u n).top)
  hCut : ActionAtLevelIsCutAction
  hWhole : WholeCellCostEqualsMinimalAction
  hLeast : CutActionEqualsMinimalAction
  hFlat : flatTopVanishingStatement
  hEquiv : chartEquivarianceStatement
variable {a ρ δ σA N0 : ℝ} {Nn : ℕ → ℝ}
private theorem StepHypotheses.extent_ge (P : StepHypotheses a ρ δ σA N0 Nn L u n) (i : Fin 4) :
    2 ≤ (torusFrame L u n).extent i := P.h2n
private theorem minimizing_of_halfRotation_fixed (P : StepHypotheses a ρ δ σA N0 Nn L u n)
    {V : (torusFrame L u n).GaugeField (u + 1)}
    (hV : gaugeTransform (fun _ => halfRotation) V = V) (hc : IsCold (finiteCells (torusFrame L u n)) (u + 1) σA V) :
    IsMinimizingChart a (finiteCells (torusFrame L u n)) V ρ (minimizingCoordinates a (finiteCells (torusFrame L u n)) V ρ) ∧
      ∀ x i, minimizingCoordinates a (finiteCells (torusFrame L u n)) V ρ x i =
        ((minimizingCoordinates a (finiteCells (torusFrame L u n)) V ρ x i : imaginaryQuaternions) : ℍ[ℝ]).imI •
          unitGenerator := by
  obtain ⟨w, hw, -, hu⟩ := P.unique V hc
  have hw2 : IsMinimizingChart a (finiteCells (torusFrame L u n)) V ρ w :=
    ⟨hw.1, fun b hb => (hw.2.1 b hb).trans (min_le_left _ _), hw.2.2⟩
  have hex : ∃ w, IsMinimizingChart a (finiteCells (torusFrame L u n)) V ρ w := ⟨w, hw2⟩
  have hlc : minimizingCoordinates a (finiteCells (torusFrame L u n)) V ρ = w := by
    unfold minimizingCoordinates
    rw [dif_pos hex]
    exact minimizingChart_unique (F := torusFrame L u n) P.hL P.extent_ge P.hρ hex.choose_spec hw2 hu
  have MW := P.hEquiv (torusFrame L u n) a P.hL P.extent_ge
  set γ : (torusFrame L u n).Cell → UnitQuaternion := fun _ => halfRotation with hγ
  have hV' : gaugeTransform γ V = V := hV
  set w' : (torusFrame L u n).Site u → Fin 4 → imaginaryQuaternions :=
    fun x i => _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell x)) (w x i) with hw'd
  have e1 : chartedField w' V = gaugeTransform (ColdStepAtMirrorFrames.blockConstantGauge γ) (chartedField w V) := by
    have := MW.chartedField_gaugeTransform γ w V
    rwa [hV'] at this
  have e2 : ∀ W'', blockEnergy a (finiteCells (torusFrame L u n)) u (chartedField w' V) V ≤
      blockEnergy a (finiteCells (torusFrame L u n)) u W'' V := by
    intro W''
    have h3 := MW.energy_gaugeTransform γ (chartedField w V) V
    rw [hV'] at h3
    have h4 : blockEnergy a (finiteCells (torusFrame L u n)) u (chartedField w' V) V =
        blockEnergy a (finiteCells (torusFrame L u n)) u (chartedField w V) V :=
      (congrArg (fun W => blockEnergy a (finiteCells (torusFrame L u n)) u W V) e1).trans h3
    exact h4.le.trans (hw.2.2 W'')
  have hw' : IsMinimizingChart a (finiteCells (torusFrame L u n)) V ρ w' := by
    refine ⟨fun b hb => ?_, fun b hb => ?_, e2⟩
    · show ColdStepAtMirrorFrames.adjointAction _ (w b.1 b.2) = 0
      rw [hw.1 b hb, adjointAction_zero']
    · show ‖ColdStepAtMirrorFrames.adjointAction _ (w b.1 b.2)‖ ≤ ρ
      rw [norm_adjointAction]
      exact hw2.2.1 b hb
  have hfix : w' = w := minimizingChart_unique (F := torusFrame L u n) P.hL P.extent_ge P.hρ hw' hw2 hu
  rw [hlc]
  refine ⟨hw2, fun x i => eq_imI_smul_of_fixed _ ?_⟩
  exact congrFun (congrFun hfix x) i
private theorem topField_zero (B : TorusBond n → ℝ) :
    topField L u B 0 = readAtLevel (torusFrame L u n) (u + 1) (expOfColourForm 1 (0 : TorusBond n → ℝ)) := by apply _root_.YangMills.DeltaSharedProofs.p501756 <;> assumption
private theorem minimizingCoordinates_flat (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) :
    minimizingCoordinates a (finiteCells (torusFrame L u n)) (topField L u B 0) ρ = fun _ _ => 0 := by
  have hc : IsCold (finiteCells (torusFrame L u n)) (u + 1) σA (topField L u B 0) :=
    (eventually_isCold B P.hσ).self_of_nhds
  obtain ⟨w, hw, -, hu⟩ := P.unique _ hc
  have hw2 : IsMinimizingChart a (finiteCells (torusFrame L u n)) (topField L u B 0) ρ w :=
    ⟨hw.1, fun b hb => (hw.2.1 b hb).trans (min_le_left _ _), hw.2.2⟩
  have hex : ∃ w, IsMinimizingChart a (finiteCells (torusFrame L u n)) (topField L u B 0) ρ w := ⟨w, hw2⟩
  have hlc : minimizingCoordinates a (finiteCells (torusFrame L u n)) (topField L u B 0) ρ = w := by
    unfold minimizingCoordinates
    rw [dif_pos hex]
    exact minimizingChart_unique (F := torusFrame L u n) P.hL P.extent_ge P.hρ hex.choose_spec hw2 hu
  have hz : chartedField (fun _ _ => 0) (topField L u B 0) =
      readAtLevel (torusFrame L u n) u (expOfColourForm 1 (0 : TorusBond (n * L) → ℝ)) := by
    funext y i
    have e0 : expUnit (0 : imaginaryQuaternions) = 1 := by
      have := colourRotation_zero
      rw [colourRotation, zero_smul] at this
      exact this
    have e1 : topField L u B 0 (enclosingCell y) i = 1 := by
      show expOfColourForm 0 B _ i = 1
      rw [expOfColourForm_apply, zero_mul, colourRotation_zero]
    have e2 : readAtLevel (torusFrame L u n) u (expOfColourForm 1 (0 : TorusBond (n * L) → ℝ)) y i = 1 := by
      show expOfColourForm 1 (0 : TorusBond (n * L) → ℝ) _ i = 1
      rw [expOfColourForm_apply]
      simp [colourRotation_zero]
    rw [e2]
    unfold chartedField
    split_ifs <;> simp [e0, e1]
  have hz2 : IsMinimizingChart a (finiteCells (torusFrame L u n)) (topField L u B 0) ρ (fun _ _ => 0) := by
    refine ⟨fun _ _ => rfl, fun b _ => ?_, fun W' => ?_⟩
    · simpa using P.hρ0.le
    · have h0 := blockEnergy_readAtLevel (u := u) P.hCut P.hWhole P.ha.le P.hL (0 : AnglePair L n)
      rw [pairEnergy_zero P.hCut P.hWhole P.hFlat P.ha.le P.hL] at h0
      rw [hz, topField_zero B]
      have h1 : blockEnergy a (finiteCells (torusFrame L u n)) u
          (readAtLevel (torusFrame L u n) u (expOfColourForm 1 (0 : TorusBond (n * L) → ℝ)))
          (readAtLevel (torusFrame L u n) (u + 1) (expOfColourForm 1 (0 : TorusBond n → ℝ))) = 0 := h0
      exact h1.le.trans (blockEnergy_nonneg' P.hWhole P.hLeast P.ha.le P.hL _ _)
  rw [hlc]
  exact (minimizingChart_unique (F := torusFrame L u n) P.hL P.extent_ge P.hρ hz2 hw2 hu).symm
end Minimizers
section MinimizerAngles
variable {L n u : ℕ} [NeZero L] [NeZero n] {a ρ δ σA N0 : ℝ} {Nn : ℕ → ℝ}
private def frameBond (L u : ℕ) {n : ℕ} (b : TorusBond (n * L)) :
    (torusFrame L u n).Site (torusFrame L u n).depth × Fin 4 :=
  (StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2)
private theorem mem_chartBonds_iff (hL : Odd L) (h2 : 2 ≤ n) (b : TorusBond (n * L)) :
    b ∈ StepCosts.chartBonds L n ↔ ¬ IsAxialTreeBond (F := torusFrame L u n) (frameBond L u b) := by apply _root_.YangMills.DeltaSharedProofs.p2283 <;> assumption
open Classical in
private def crossingAngle (L u : ℕ) {n : ℕ} (B : TorusBond n → ℝ) (b : TorusBond (n * L)) : ℝ :=
  if IsCrossingBond (F := torusFrame L u n) (frameBond L u b) then B (parentBlock L b.1, b.2) else 0
open Classical in
private def minimizerAngles (a ρ : ℝ) (L u : ℕ) {n : ℕ} [NeZero L] [NeZero n] (B : TorusBond n → ℝ) (τ : ℝ) :
    TorusBond (n * L) → ℝ := fun b =>
  if b ∈ StepCosts.chartBonds L n then
    ((minimizingCoordinates a (finiteCells (torusFrame L u n)) (topField L u B τ) ρ (frameBond L u b).1
      (frameBond L u b).2 : imaginaryQuaternions) : ℍ[ℝ]).imI + τ * crossingAngle L u B b
  else 0
private theorem minimizerAngles_field (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) {τ : ℝ}
    (hone : ∀ x i, minimizingCoordinates a (finiteCells (torusFrame L u n)) (topField L u B τ) ρ x i =
      ((minimizingCoordinates a (finiteCells (torusFrame L u n)) (topField L u B τ) ρ x i : imaginaryQuaternions) :
        ℍ[ℝ]).imI • unitGenerator) :
    readAtLevel (torusFrame L u n) u (expOfColourForm 1 (minimizerAngles a ρ L u B τ)) =
      chartedField (minimizingCoordinates a (finiteCells (torusFrame L u n)) (topField L u B τ) ρ) (topField L u B τ) := by
  classical
  have : NeZero (n * (torusFrame L u n).blockSide) := inferInstanceAs (NeZero (n * L))
  funext y i
  set w := minimizingCoordinates a (finiteCells (torusFrame L u n)) (topField L u B τ) ρ with hw
  set b : TorusBond (n * L) := (toTorusSite (n * L) y, i) with hb
  have hy : StepCosts.torusSiteInFrame (torusFrame L u n) u b.1 = y :=
    torusSiteInFrame_toTorusSite (period_depth L u n) y
  have hx : frameBond L u b = (y, i) := Prod.ext hy rfl
  have hexp : expUnit (w y i) = colourRotation (((w y i : imaginaryQuaternions) : ℍ[ℝ]).imI) := by
    conv_lhs => rw [hone y i]
    rfl
  have hl : readAtLevel (torusFrame L u n) u (expOfColourForm 1 (minimizerAngles a ρ L u B τ)) y i =
      colourRotation (1 * minimizerAngles a ρ L u B τ b) := rfl
  rw [hl, one_mul]
  unfold chartedField
  by_cases hc : IsCrossingBond (F := torusFrame L u n) (y, i)
  · have hnt : ¬ IsAxialTreeBond (F := torusFrame L u n) (y, i) := fun h => h.1 hc
    have hm : b ∈ StepCosts.chartBonds L n := (mem_chartBonds_iff P.hL P.h2n b).2 (by rw [hx]; exact hnt)
    have hcell : enclosingCell y = StepCosts.torusSiteInFrame (torusFrame L u n) (u + 1) (parentBlock L b.1) := by
      rw [← hy]
      exact enclosingCell_torusSiteInFrame (F := torusFrame L u n) (n := n) (fun _ => rfl) b.1
    have hcr : crossingAngle L u B b = B (parentBlock L b.1, b.2) := by
      unfold crossingAngle
      rw [if_pos (by rw [hx]; exact hc)]
    have hV : topField L u B τ (enclosingCell y) i = colourRotation (τ * B (parentBlock L b.1, b.2)) := by
      rw [hcell]
      exact readAtLevel_top B τ (parentBlock L b.1, b.2)
    have hg : minimizerAngles a ρ L u B τ b =
        ((w y i : imaginaryQuaternions) : ℍ[ℝ]).imI + τ * B (parentBlock L b.1, b.2) := by
      unfold minimizerAngles
      rw [if_pos hm, hcr, hx]
    rw [if_pos hc]
    refine (congrArg colourRotation hg).trans ?_
    rw [colourRotation_add]
    exact congrArg₂ (· * ·) hexp.symm hV.symm
  · rw [if_neg hc]
    have hcr : crossingAngle L u B b = 0 := by
      unfold crossingAngle
      rw [if_neg (by rw [hx]; exact hc)]
    by_cases ht : IsAxialTreeBond (F := torusFrame L u n) (y, i)
    · have hm : b ∉ StepCosts.chartBonds L n :=
        fun h => (mem_chartBonds_iff P.hL P.h2n b).1 h (by rw [hx]; exact ht)
      have hg : minimizerAngles a ρ L u B τ b = 0 := by
        unfold minimizerAngles
        rw [if_neg hm]
      rw [if_pos ht, hg, colourRotation_zero]
    · have hm : b ∈ StepCosts.chartBonds L n := (mem_chartBonds_iff P.hL P.h2n b).2 (by rw [hx]; exact ht)
      have hg : minimizerAngles a ρ L u B τ b = ((w y i : imaginaryQuaternions) : ℍ[ℝ]).imI := by
        unfold minimizerAngles
        rw [if_pos hm, hcr, hx, mul_zero, add_zero]
      rw [if_neg ht]
      exact (congrArg colourRotation hg).trans hexp.symm
private theorem minimizerAngles_zero (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) :
    minimizerAngles a ρ L u B 0 = 0 := by
  classical
  funext b
  unfold minimizerAngles
  split_ifs
  · rw [minimizingCoordinates_flat P B]
    simp
  · rfl
private abbrev bondEnum (n : ℕ) [NeZero n] : TorusBond n ≃ Fin (Fintype.card (TorusBond n)) :=
  Fintype.equivFin (TorusBond n)
private def enumTopBond (L u n : ℕ) [NeZero n] (l : Fin (Fintype.card (TorusBond n))) :
    (torusFrame L u n).Site (torusFrame L u n).top × Fin 4 :=
  (StepCosts.torusSiteInFrame (torusFrame L u n) (u + 1) ((bondEnum n).symm l).1, ((bondEnum n).symm l).2)
private def colourAt (k : ℕ) : Fin k → imaginaryQuaternions := fun _ => unitGenerator
private def enumAngles (B : TorusBond n → ℝ) : Fin (Fintype.card (TorusBond n)) → ℝ := fun l => B ((bondEnum n).symm l)
private theorem enumTopBond_bondEnum (c : TorusBond n) :
    enumTopBond L u n (bondEnum n c) = (StepCosts.torusSiteInFrame (torusFrame L u n) (u + 1) c.1, c.2) := by
  show (StepCosts.torusSiteInFrame (torusFrame L u n) (u + 1) ((bondEnum n).symm (bondEnum n c)).1,
    ((bondEnum n).symm (bondEnum n c)).2) = _
  rw [Equiv.symm_apply_apply]
private theorem bondSpread_single {F : BlockFrame} {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (y : F.Site F.top) (i : Fin 4) (l₀ : Fin k) (h : c l₀ = (y, i)) (hu : ∀ l, l ≠ l₀ → c l ≠ (y, i)) :
    BlockAverages.bondSpread c X σ y i = σ l₀ • X l₀ := by apply _root_.YangMills.SharedProofs.p504 <;> assumption
private theorem topField_eq_rotatedField (B : TorusBond n → ℝ) (τ : ℝ) :
    topField L u B τ = rotatedField (BlockAverages.bondSpread (enumTopBond L u n) (colourAt _) (τ • enumAngles B))
      (ColdStepAtMirrorFrames.uniformField (torusFrame L u n) (torusFrame L u n).top) := by
  classical
  funext y i
  set c : TorusBond n := (toTorusSite n y, i) with hc
  have hq := period_top L u n
  have hy : StepCosts.torusSiteInFrame (torusFrame L u n) (u + 1) c.1 = y := torusSiteInFrame_toTorusSite hq y
  have hs := bondSpread_single (F := torusFrame L u n) (enumTopBond L u n) (colourAt _) (τ • enumAngles B) y i
    (bondEnum n c)
    (by rw [enumTopBond_bondEnum]; exact Prod.ext hy rfl) (by
      intro l hl h
      apply hl
      have h1 : ((bondEnum n).symm l) = c := by
        have h2 := congrArg Prod.fst h
        have h3 := congrArg Prod.snd h
        refine Prod.ext ?_ h3
        have h4 : StepCosts.torusSiteInFrame (torusFrame L u n) (u + 1) ((bondEnum n).symm l).1 = y := h2
        have h5 := toTorusSite_torusSiteInFrame hq ((bondEnum n).symm l).1
        rw [h4] at h5
        exact h5.symm
      rw [← h1]
      simp)
  show expOfColourForm τ B (toTorusSite n y) i =
    expUnit (BlockAverages.bondSpread (enumTopBond L u n) (colourAt _) (τ • enumAngles B) y i) * 1
  rw [mul_one, expOfColourForm_apply, hs]
  show expUnit ((τ * B c) • unitGenerator) = _
  congr 1
  simp [enumAngles, colourAt]
private def coordOfAngles (a ρ : ℝ) (L u : ℕ) {n : ℕ} [NeZero n] (b : TorusBond (n * L))
    (σ : Fin (Fintype.card (TorusBond n)) → ℝ) : imaginaryQuaternions :=
  minimizingBondCoordinate a ρ (finiteCells (torusFrame L u n)) (frameBond L u b)
    (rotatedField (BlockAverages.bondSpread (enumTopBond L u n) (colourAt _) σ)
      (ColdStepAtMirrorFrames.uniformField (torusFrame L u n) (torusFrame L u n).top))
private theorem minimizingCoordinates_eq_coordOfAngles (B : TorusBond n → ℝ) (τ : ℝ) (b : TorusBond (n * L)) :
    minimizingCoordinates a (finiteCells (torusFrame L u n)) (topField L u B τ) ρ (frameBond L u b).1
        (frameBond L u b).2 =
      coordOfAngles a ρ L u b (τ • enumAngles B) :=
  congrArg (fun V => minimizingCoordinates a (finiteCells (torusFrame L u n)) V ρ (frameBond L u b).1
    (frameBond L u b).2) (topField_eq_rotatedField B τ)
private def imIProj : imaginaryQuaternions →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  { toFun := fun v => (v : ℍ[ℝ]).imI
    map_add' := fun _ _ => by simp
    map_smul' := fun _ _ => by simp }
private theorem minimizerAngles_chart (B : TorusBond n → ℝ) {b : TorusBond (n * L)}
    (hb : b ∈ StepCosts.chartBonds L n) (τ : ℝ) :
    minimizerAngles a ρ L u B τ b = imIProj (coordOfAngles a ρ L u b (τ • enumAngles B)) + τ * crossingAngle L u B b := by
  unfold minimizerAngles
  rw [if_pos hb, minimizingCoordinates_eq_coordOfAngles]
  rfl
private theorem frameBond_mem (P : StepHypotheses a ρ δ σA N0 Nn L u n) {b : TorusBond (n * L)}
    (hb : b ∈ StepCosts.chartBonds L n) :
    frameBond L u b ∈ BlockAverages.chordBonds (finiteCells (torusFrame L u n)) :=
  (P.hEquiv (torusFrame L u n) a P.hL P.extent_ge).mem_chordBonds_of_not_tree _
    ((mem_chartBonds_iff P.hL P.h2n b).1 hb)
private theorem coordOfAngles_analytic (P : StepHypotheses a ρ δ σA N0 Nn L u n) {b : TorusBond (n * L)}
    (hb : b ∈ StepCosts.chartBonds L n) : AnalyticAt ℝ (coordOfAngles a ρ L u b) 0 :=
  (P.regular _ (frameBond_mem P hb)).1 _ _ _
private instance imaginaryQuaternionsComplete : CompleteSpace imaginaryQuaternions :=
  FiniteDimensional.complete ℝ imaginaryQuaternions
private theorem minimizerAngles_contDiffAt (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) :
    ContDiffAt ℝ 2 (minimizerAngles a ρ L u B) 0 := by
  classical
  refine contDiffAt_pi.2 fun b => ?_
  by_cases hb : b ∈ StepCosts.chartBonds L n
  · have e : (fun τ => minimizerAngles a ρ L u B τ b) =
        fun τ => imIProj (coordOfAngles a ρ L u b (τ • enumAngles B)) + τ * crossingAngle L u B b :=
      funext fun τ => minimizerAngles_chart B hb τ
    rw [e]
    refine ContDiffAt.add ?_ (contDiffAt_id.mul contDiffAt_const)
    have h1 : ContDiffAt ℝ 2 (coordOfAngles a ρ L u b) ((0 : ℝ) • enumAngles B) := by
      rw [zero_smul]
      exact (coordOfAngles_analytic P hb).contDiffAt
    have h2 : ContDiffAt ℝ 2 (fun τ : ℝ => τ • enumAngles B) 0 := contDiffAt_id.smul contDiffAt_const
    have h3 : ContDiffAt ℝ 2 (fun τ : ℝ => coordOfAngles a ρ L u b (τ • enumAngles B)) 0 :=
      ContDiffAt.comp (g := coordOfAngles a ρ L u b) (f := fun τ : ℝ => τ • enumAngles B) (0 : ℝ) h1 h2
    exact ContDiffAt.comp (g := imIProj) (f := fun τ : ℝ => coordOfAngles a ρ L u b (τ • enumAngles B)) (0 : ℝ)
      imIProj.contDiff.contDiffAt h3
  · have e : (fun τ => minimizerAngles a ρ L u B τ b) = fun _ => 0 := funext fun τ => by
      unfold minimizerAngles
      rw [if_neg hb]
    rw [e]
    exact contDiffAt_const
open Classical in
private def velocityForm (a ρ : ℝ) (L u : ℕ) {n : ℕ} [NeZero L] [NeZero n] (B : TorusBond n → ℝ) :
    TorusBond (n * L) → ℝ := fun b =>
  if b ∈ StepCosts.chartBonds L n then
    imIProj (fderiv ℝ (coordOfAngles a ρ L u b) 0 (enumAngles B)) + crossingAngle L u B b
  else 0
private theorem deriv_minimizerAngles (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) :
    deriv (minimizerAngles a ρ L u B) 0 = velocityForm a ρ L u B := by
  classical
  have hd : ∀ b, DifferentiableAt ℝ (fun τ => minimizerAngles a ρ L u B τ b) 0 := fun b =>
    ((contDiffAt_pi.1 (minimizerAngles_contDiffAt P B) b).differentiableAt (by norm_num))
  rw [deriv_pi hd]
  funext b
  unfold velocityForm
  by_cases hb : b ∈ StepCosts.chartBonds L n
  · rw [if_pos hb]
    have e : (fun τ => minimizerAngles a ρ L u B τ b) =
        fun τ => imIProj (coordOfAngles a ρ L u b (τ • enumAngles B)) + τ * crossingAngle L u B b :=
      funext fun τ => minimizerAngles_chart B hb τ
    rw [e]
    have hD : HasFDerivAt (coordOfAngles a ρ L u b) (fderiv ℝ (coordOfAngles a ρ L u b) 0)
        ((0 : ℝ) • enumAngles B) := by
      rw [zero_smul]
      exact (coordOfAngles_analytic P hb).differentiableAt.hasFDerivAt
    have hl : HasDerivAt (fun τ : ℝ => τ • enumAngles B) (enumAngles B) 0 := by
      have h3 : HasDerivAt (fun τ : ℝ => τ • enumAngles B) ((1 : ℝ) • enumAngles B) 0 :=
        (hasDerivAt_id' (0 : ℝ)).smul_const _
      rwa [one_smul] at h3
    have h3 : HasDerivAt (fun τ : ℝ => coordOfAngles a ρ L u b (τ • enumAngles B))
        (fderiv ℝ (coordOfAngles a ρ L u b) 0 (enumAngles B)) 0 :=
      HasFDerivAt.comp_hasDerivAt (f := fun τ : ℝ => τ • enumAngles B) (0 : ℝ) hD hl
    have h4 : HasDerivAt (fun τ : ℝ => imIProj (coordOfAngles a ρ L u b (τ • enumAngles B)))
        (imIProj (fderiv ℝ (coordOfAngles a ρ L u b) 0 (enumAngles B))) 0 :=
      imIProj.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
    have h5 : HasDerivAt (fun τ : ℝ => τ * crossingAngle L u B b) (crossingAngle L u B b) 0 := by
      simpa using (hasDerivAt_id' (0 : ℝ)).mul_const (crossingAngle L u B b)
    exact (h4.fun_add h5).deriv
  · rw [if_neg hb]
    have e : (fun τ => minimizerAngles a ρ L u B τ b) = fun _ => 0 := funext fun τ => by
      unfold minimizerAngles
      rw [if_neg hb]
    rw [e]
    simp
private theorem bondDeriv_coordOfAngles (P : StepHypotheses a ρ δ σA N0 Nn L u n) {b : TorusBond (n * L)}
    (hb : b ∈ StepCosts.chartBonds L n) (l : Fin (Fintype.card (TorusBond n))) :
    bondDeriv (torusCoordinate a ρ (frameBond L u b))
        (ColdStepAtMirrorFrames.uniformField (torusFrame L u n) (torusFrame L u n).top)
        ![enumTopBond L u n l] ![unitGenerator] =
      fderiv ℝ (coordOfAngles a ρ L u b) 0 (Pi.single l 1) := by
  classical
  unfold bondDeriv
  rw [iteratedFDeriv_one_apply]
  set ι : (Fin 1 → ℝ) →L[ℝ] (Fin (Fintype.card (TorusBond n)) → ℝ) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight (Pi.single l 1) with hι
  have e : (fun τ : Fin 1 → ℝ => torusCoordinate a ρ (frameBond L u b)
      (leftTranslate (ColdStepAtMirrorFrames.bondSpread ![enumTopBond L u n l] ![unitGenerator] τ)
        (ColdStepAtMirrorFrames.uniformField (torusFrame L u n) (torusFrame L u n).top))) =
      fun τ => coordOfAngles a ρ L u b (ι τ) := by
    funext τ
    unfold coordOfAngles torusCoordinate
    congr 1
    funext y i
    show expUnit (ColdStepAtMirrorFrames.bondSpread ![enumTopBond L u n l] ![unitGenerator] τ y i) * 1 =
      expUnit (BlockAverages.bondSpread (enumTopBond L u n) (colourAt _) (ι τ) y i) * 1
    congr 2
    unfold ColdStepAtMirrorFrames.bondSpread BlockAverages.bondSpread
    rw [Fin.sum_univ_one, Finset.sum_eq_single l]
    · by_cases h : enumTopBond L u n l = (y, i)
      · rw [if_pos (by simpa using h), if_pos h]
        simp [hι, colourAt]
      · rw [if_neg (by simpa using h), if_neg h]
    · intro l' _ hl'
      have : (ι τ) l' = 0 := by simp [hι, hl']
      rw [this]
      simp
    · simp
  rw [e]
  have hd : DifferentiableAt ℝ (coordOfAngles a ρ L u b) (ι 0) := by
    rw [map_zero]
    exact (coordOfAngles_analytic P hb).differentiableAt
  have h1 : HasFDerivAt (fun τ => coordOfAngles a ρ L u b (ι τ))
      ((fderiv ℝ (coordOfAngles a ρ L u b) (ι 0)).comp ι) 0 :=
    hd.hasFDerivAt.comp (0 : Fin 1 → ℝ) ι.hasFDerivAt
  rw [h1.fderiv, map_zero]
  simp [hι]
private theorem apply_enumAngles (φ : (Fin (Fintype.card (TorusBond n)) → ℝ) →L[ℝ] ℝ) (B : TorusBond n → ℝ) :
    φ (enumAngles B) = ∑ c : TorusBond n, φ (Pi.single (bondEnum n c) 1) * B c := by apply _root_.YangMills.DeltaSharedProofs.p501545 <;> assumption
private theorem responseMap_chart (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ)
    {b : TorusBond (n * L)} (hb : b ∈ StepCosts.chartBonds L n) :
    responseMap a ρ L u B b = imIProj (fderiv ℝ (coordOfAngles a ρ L u b) 0 (enumAngles B)) + crossingAngle L u B b := by
  classical
  have : NeZero (n * (torusFrame L u n).blockSide) := inferInstanceAs (NeZero (n * L))
  have hq := period_top L u n
  have hentry : ∀ c : TorusBond n, responseKernel a ρ L u b c =
      imIProj (fderiv ℝ (coordOfAngles a ρ L u b) 0 (Pi.single (bondEnum n c) 1)) +
        (if IsCrossingBond (F := torusFrame L u n) (frameBond L u b) ∧
          enclosingCell (frameBond L u b).1 = StepCosts.torusSiteInFrame (torusFrame L u n) (u + 1) c.1 ∧
            b.2 = c.2 then 1 else 0) := by
    intro c
    have h1 := bondDeriv_coordOfAngles P hb (bondEnum n c)
    rw [enumTopBond_bondEnum] at h1
    unfold responseKernel minimizerResponse
    refine congrArg₂ (· + ·) ?_ (if_congr Iff.rfl rfl rfl)
    refine (congrArg (fun v : imaginaryQuaternions => -((v : ℍ[ℝ]) * (unitGenerator : ℍ[ℝ])).re) h1).trans ?_
    exact neg_re_mul_unitGenerator _
  unfold responseMap
  simp only [hentry, add_mul, Finset.sum_add_distrib]
  have e1 : ∑ c : TorusBond n, imIProj (fderiv ℝ (coordOfAngles a ρ L u b) 0 (Pi.single (bondEnum n c) 1)) * B c =
      imIProj (fderiv ℝ (coordOfAngles a ρ L u b) 0 (enumAngles B)) := by
    have := apply_enumAngles (imIProj.comp (fderiv ℝ (coordOfAngles a ρ L u b) 0 : _ →L[ℝ] imaginaryQuaternions)) B
    simpa using this.symm
  rw [e1]
  congr 1
  unfold crossingAngle
  by_cases hc : IsCrossingBond (F := torusFrame L u n) (frameBond L u b)
  · rw [if_pos hc]
    have hcell : enclosingCell (frameBond L u b).1 =
        StepCosts.torusSiteInFrame (torusFrame L u n) (u + 1) (parentBlock L b.1) :=
      enclosingCell_torusSiteInFrame (F := torusFrame L u n) (n := n) (fun _ => rfl) b.1
    rw [Finset.sum_eq_single (parentBlock L b.1, b.2)]
    · rw [if_pos ⟨hc, hcell, rfl⟩, one_mul]
    · intro c _ hne
      rw [if_neg, zero_mul]
      rintro ⟨-, h2, h3⟩
      apply hne
      rw [hcell] at h2
      have h4 := congrArg (toTorusSite n) h2
      rw [toTorusSite_torusSiteInFrame hq, toTorusSite_torusSiteInFrame hq] at h4
      exact Prod.ext h4.symm h3.symm
    · simp
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg (fun h => hc h.1), zero_mul]
end MinimizerAngles
section Conclusion
variable {L n u : ℕ} [NeZero L] [NeZero n] {a ρ δ σA N0 : ℝ} {Nn : ℕ → ℝ}
private theorem eventually_minimizing (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) :
    ∀ᶠ τ in 𝓝 (0 : ℝ),
      IsMinimizingChart a (finiteCells (torusFrame L u n)) (topField L u B τ) ρ
        (minimizingCoordinates a (finiteCells (torusFrame L u n)) (topField L u B τ) ρ) ∧
      ∀ x i, minimizingCoordinates a (finiteCells (torusFrame L u n)) (topField L u B τ) ρ x i =
        ((minimizingCoordinates a (finiteCells (torusFrame L u n)) (topField L u B τ) ρ x i : imaginaryQuaternions) :
          ℍ[ℝ]).imI • unitGenerator :=
  (eventually_isCold B P.hσ).mono fun τ hτ => minimizing_of_halfRotation_fixed P (gaugeTransform_topField B τ) hτ
private theorem torusCoordinate_off_chart {F : BlockFrame} {a ρ : ℝ} (bd : F.Site F.depth × Fin 4)
    (hb : bd ∉ BlockAverages.chordBonds (finiteCells F)) (V : F.GaugeField F.top) :
    torusCoordinate a ρ bd V = 0 := by apply _root_.YangMills.SharedProofs.p33224 <;> assumption
private theorem responseMap_off_chart (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ)
    {b : TorusBond (n * L)} (hb : b ∉ StepCosts.chartBonds L n) : responseMap a ρ L u B b = 0 := by
  classical
  have ht : IsAxialTreeBond (F := torusFrame L u n) (frameBond L u b) := by
    by_contra h
    exact hb ((mem_chartBonds_iff P.hL P.h2n b).2 h)
  have hoff : frameBond L u b ∉ BlockAverages.chordBonds (finiteCells (torusFrame L u n)) :=
    fun h => (Finset.mem_filter.1 h).2 ht
  have hentry : ∀ c : TorusBond n, responseKernel a ρ L u b c = 0 := by
    intro c
    have hz : ∀ X : Fin 1 → imaginaryQuaternions, bondDeriv (torusCoordinate a ρ (frameBond L u b))
        (ColdStepAtMirrorFrames.uniformField (torusFrame L u n) (torusFrame L u n).top)
        ![(StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2)] X = 0 := by
      intro X
      unfold bondDeriv
      have e : (fun τ : Fin 1 → ℝ => torusCoordinate a ρ (frameBond L u b)
          (leftTranslate (ColdStepAtMirrorFrames.bondSpread
            ![(StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2)] X τ)
            (ColdStepAtMirrorFrames.uniformField (torusFrame L u n) (torusFrame L u n).top))) = fun _ => 0 :=
        funext fun τ => torusCoordinate_off_chart _ hoff _
      rw [e, iteratedFDeriv_one_apply]
      simp
    unfold responseKernel minimizerResponse
    have hz1 := hz ![unitGenerator]
    have hnc : ¬ IsCrossingBond (F := torusFrame L u n) (frameBond L u b) := ht.1
    have e1 : bondDeriv (torusCoordinate a ρ
        ((StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2) :
          (torusFrame L u n).Site (torusFrame L u n).depth × Fin 4))
        (ColdStepAtMirrorFrames.uniformField (torusFrame L u n) (torusFrame L u n).top)
        ![(StepCosts.torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2)] ![unitGenerator] = 0 := hz1
    rw [e1, if_neg (fun h => hnc h.1)]
    simp
  unfold responseMap
  simp [hentry]
end Conclusion
end MinimizerCurve
open MinimizerCurve in
theorem minimizerCurve (h2 : ActionAtLevelIsCutAction)
    (h3 : WholeCellCostEqualsMinimalAction) (h4 : CutActionEqualsMinimalAction)
    (h5 : flatTopVanishingStatement) (h6 : chartEquivarianceStatement) :
    minimizerCurveStatement := by
  classical
  intro T hD u n _ hn B
  have hL : Odd T.side := hD.L_odd
  have ha : 0 < T.coupling := lt_of_lt_of_le one_pos hD.a_ge
  obtain ⟨-, -, -, hρ0, hρ1, hσ, -, -, hch⟩ := hD.chain
  have hamb : IsAdmissibleAmbient (torusFrame T.side u n) := Or.inr fun _ => hn
  have hreg' := isOrthantRegular_finiteCells (F := torusFrame T.side u n) (extent_pos T.side u n) 1024
  have hflat : IsCold (finiteCells (torusFrame T.side u n)) (torusFrame T.side u n).top T.σA
      (ColdStepAtMirrorFrames.uniformField (torusFrame T.side u n) (torusFrame T.side u n).top) :=
    (h5 (torusFrame T.side u n) T.coupling _ ha.le hL).1 _ _ hσ
  have P : StepHypotheses T.coupling T.ρA T.δ₁ T.σA (T.N 0) T.N T.side u n :=
    { ha := ha
      hL := hL
      h2n := by omega
      hρ0 := hρ0
      hρ := lt_of_le_of_lt hρ1 (by linarith [Real.pi_gt_three])
      hσ := hσ
      unique := fun V hV => (hch (torusFrame T.side u n) 1024 _ rfl hamb le_rfl hreg' T.σA V hσ le_rfl hV).1
      regular := (hch (torusFrame T.side u n) 1024 _ rfl hamb le_rfl hreg' T.σA _ hσ le_rfl hflat).2.2.2.1
      hCut := h2
      hWhole := h3
      hLeast := h4
      hFlat := h5
      hEquiv := h6 }
  refine ⟨minimizerAngles T.coupling T.ρA T.side u B, minimizerAngles_contDiffAt P B, minimizerAngles_zero P B, ?_, ?_⟩
  · rw [deriv_minimizerAngles P B]
    funext b
    unfold velocityForm
    by_cases hb : b ∈ StepCosts.chartBonds T.side n
    · rw [if_pos hb]
      exact (responseMap_chart P B hb).symm
    · rw [if_neg hb]
      exact (responseMap_off_chart P B hb).symm
  · filter_upwards [eventually_minimizing P B] with τ hτ
    funext x i
    unfold ClusterExpansionOfAStep.minimizingField
    rw [cellsOfSites_univ (F := torusFrame T.side u n) (n := n) (fun _ => rfl)]
    have e := congrFun (congrFun (minimizerAngles_field P B hτ.2)
      (StepCosts.torusSiteInFrame (torusFrame T.side u n) u x)) i
    have e2 : readAtLevel (torusFrame T.side u n) u (expOfColourForm 1 (minimizerAngles T.coupling T.ρA T.side u B τ))
        (StepCosts.torusSiteInFrame (torusFrame T.side u n) u x) i =
        expOfColourForm 1 (minimizerAngles T.coupling T.ρA T.side u B τ) x i :=
      readAtLevel_torusSiteInFrame (period_depth T.side u n) _ _ _
    exact e.symm.trans e2
end MomentLaw
end
end YangMills.Construction
