import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTheGaugeProof
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStepKeepsTheGauge
import YangMills.Construction.ResponseInTheExpansion.ScoreIsGaugeInvariant
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory Set
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings TorusLumps TorusFields StepCosts StepMarks StepGas StepFrames FieldHaar BlockAverages GaugeFixing
  LumpContours ColdStepAtMirrorFrames TorusContours TopLevelSites QuaternionLog BlockPlaces ClusterExpansionOfAStep WeightedResponses
  RenormalizationStepParameters ColdChain
namespace StepResponseGauge
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem fieldWithStoredLinks_gauge (q : CoarseState R n) (g : TorusSite n → UnitQuaternion)
    (W : TorusField (n * R.params.side)) :
    (q.gaugeTransform g).fieldWithStoredLinks (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) =
      TorusFields.gaugeTransform (blockConstantGauge R.params.side g) (q.fieldWithStoredLinks W) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.fieldWithStoredLinks_gaugeTransform <;> assumption
private theorem coarseStateOf_gauge (hL : R.params.side ≤ 6 * R.range) (C : Finset (TorusSite n))
    (g : TorusSite n → UnitQuaternion) (F : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (L : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) :
    coarseStateOf R C (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) F) Yt
        (R.labels.act Yt (blockConstantGauge R.params.side g) L) bad b =
      (coarseStateOf R C F Yt L bad b).gaugeTransform g := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coarseStateOf_gaugeTransform <;> assumption
private theorem parentBlock_add_unitStep {L : ℕ} [NeZero L] (x : TorusSite (n * L)) (i : Fin 4) :
    parentBlock L (x + TorusFields.unitStep (n * L) i) = parentBlock L x ∨
      parentBlock L (x + TorusFields.unitStep (n * L) i) = parentBlock L x + TorusFields.unitStep n i := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.parentBlock_add_unitStep <;> assumption
private theorem axialGauge_gauge (hodd : Odd R.params.side)
    (Wf : (stepBlockFrame R.params.side n).GaugeField (stepBlockFrame R.params.side n).depth)
    (γ : (stepBlockFrame R.params.side n).Site (stepBlockFrame R.params.side n).depth → UnitQuaternion)
    (hγ : ∀ x, γ (cellCentre (stepBlockFrame R.params.side n).depth (enclosingCell x)) = γ x)
    (x : (stepBlockFrame R.params.side n).Site (stepBlockFrame R.params.side n).depth) :
    axialGauge 1 (BlockAverages.gaugeTransform γ Wf) x = γ x * axialGauge 1 Wf x * (γ x)⁻¹ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.axialGauge_gaugeTransform <;> assumption
private theorem readAtLevel_gauge (G : TorusSite (n * R.params.side) → UnitQuaternion) (W : TorusField (n * R.params.side)) :
    readAtLevel (stepBlockFrame R.params.side n) 0 (TorusFields.gaugeTransform G W) =
      BlockAverages.gaugeTransform (fun x => G (toTorusSite (n * R.params.side) x))
        (readAtLevel (stepBlockFrame R.params.side n) 0 W) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.readAtLevel_zero_gaugeTransform <;> assumption
private theorem parentBlock_of_enclosingCell (hodd : Odd R.params.side)
    (x : (stepBlockFrame R.params.side n).Site (stepBlockFrame R.params.side n).depth) :
    parentBlock R.params.side (toTorusSite (n * R.params.side) x) = toTorusSite n (enclosingCell x) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.parentBlock_toTorusSite <;> assumption
private theorem parentBlock_of_cellCentre (hodd : Odd R.params.side) (y : (stepBlockFrame R.params.side n).Cell) :
    parentBlock R.params.side (toTorusSite (n * R.params.side) (cellCentre (stepBlockFrame R.params.side n).depth y)) =
      toTorusSite n y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.parentBlock_toTorusSite_cellCentre <;> assumption
private theorem norm_frameCoord_le {ℓ : StepParameters} {ρA ρ : ℝ} {t m : ℕ} {V : TorusField n}
    {b : TorusBond (n * ℓ.side)} (hρ : 0 ≤ ρ) (h : FrameIsMinimizing ℓ ρA ρ t m V b) :
    ‖(frameCoord ℓ ρA t m V b : ℍ[ℝ])‖ ≤ ρ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.norm_frameCoord_le <;> assumption
private theorem cutoffFactor_conj {ρ : ℝ} {p : ℝ → ℝ} (hρ : ρ ≤ 1) (u Γ : UnitQuaternion) (f f' : imaginaryQuaternions)
    (hf : (f' : ℍ[ℝ]) = (u : ℍ[ℝ]) * (f : ℍ[ℝ]) * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])) (hs : ‖(f : ℍ[ℝ])‖ ≤ 1) :
    cutoffFactor ρ p ‖((minimalLog (u * Γ * u⁻¹) : imaginaryQuaternions) : ℍ[ℝ]) - (f' : ℍ[ℝ])‖ =
      cutoffFactor ρ p ‖((minimalLog Γ : imaginaryQuaternions) : ℍ[ℝ]) - (f : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.cutoffFactor_minimalLog_conj <;> assumption
private theorem bondMark_gauge (hR : R.IsWellPosed) (hF : R.ColdChainFits) (hfr : FrameCovariance)
    (hsz : FrameNearMinimizer) {S C : Finset (TorusSite n)} {s : ℝ} (hs : 0 ≤ s) (V : TorusField n)
    (hsit : IsStepSituation R.params R.nextRange V S C s) (g : TorusSite n → UnitQuaternion)
    (W : TorusField (n * R.params.side)) (c : TorusBond (n * R.params.side)) (hc : c ∈ chartBonds R.params.side n)
    (hC : parentBlock R.params.side c.1 ∉ C) :
    bondMark R (TorusFields.gaugeTransform g V)
        (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) c = bondMark R V W c := by
  classical
  have hfit := hR.admissible
  obtain ⟨δ, lam, σA, cg, N, hch, hσ, hσ1⟩ := hF
  have hrf : RangesAdmissible R.range R.nextRange := ⟨hR.range_le, hR.nextRange_ge, by
    have := hR.range_ge_side
    have := hfit.L_ge
    omega⟩
  have hfr1 := (hfr R.params δ lam R.anchorRadius σA cg N hfit hch hσ R.depth R.range R.nextRange n V _ _ _ hrf hsit
    c hc hC).1 g
  have hsz1 := (hsz R.params δ lam R.anchorRadius σA cg N hfit hch hσ).2 R.depth R.range R.nextRange n V _ _ _ hrf hsit
    c hc hC
  have hρA : 0 < R.anchorRadius ∧ R.anchorRadius ≤ 1 := ⟨hch.2.2.2.1, hch.2.2.2.2.1⟩
  have hN0 : 0 < N 0 := hch.2.2.2.2.2.2.2.1 0
  have hsmall : ‖((frameCoord R.params R.anchorRadius R.depth R.frameReach V c : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 1 :=
    (norm_frameCoord_le (le_min hρA.1.le (mul_nonneg hN0.le hs)) hsz1.1).trans ((min_le_left _ _).trans hρA.2)
  set h : UnitQuaternion := g (parentBlock R.params.side c.1) with hh
  have hodd := hfit.L_odd
  set F₀ := stepBlockFrame R.params.side n with hF₀
  set x : F₀.Site F₀.depth := torusSiteInFrame F₀ 0 c.1 with hx
  have hx1 : toTorusSite (n * R.params.side) x = c.1 :=
    toTorusSite_torusSiteInFrame (fun i => stepBlockFrame_period_zero i) c.1
  have hx2 : toTorusSite (n * R.params.side) (x + BlockAverages.unitStep F₀.depth c.2) =
      c.1 + TorusFields.unitStep (n * R.params.side) c.2 := by
    have h1 := toTorusSite_add (F := stepBlockFrame R.params.side n) (j := 0) (m := n * R.params.side)
      (fun i => stepBlockFrame_period_zero i) x (BlockAverages.unitStep 0 c.2)
    rw [toTorusSite_unitStep (F := stepBlockFrame R.params.side n) (j := 0) (m := n * R.params.side)
      (fun i => stepBlockFrame_period_zero i)] at h1
    exact h1.trans (congrArg (· + TorusFields.unitStep (n * R.params.side) c.2) hx1)
  set T := axialGauge 1 (readAtLevel F₀ 0 W) with hT
  set w : UnitQuaternion := BlockAverages.gaugeTransform T (readAtLevel F₀ 0 W) x c.2 with hw
  set γ : F₀.Site F₀.depth → UnitQuaternion :=
    fun x' => blockConstantGauge R.params.side g (toTorusSite (n * R.params.side) x') with hγ
  have hcentre : ∀ x', γ (cellCentre F₀.depth (enclosingCell x')) = γ x' := by
    intro x'
    show g (parentBlock R.params.side _) = g (parentBlock R.params.side _)
    rw [parentBlock_of_cellCentre hodd, parentBlock_of_enclosingCell hodd]
  have hfine := readAtLevel_gauge (R := R) (blockConstantGauge R.params.side g) W
  have htree : ∀ x', axialGauge 1 (readAtLevel F₀ 0
      (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W)) x' = γ x' * T x' * (γ x')⁻¹ := by
    intro x'
    rw [hfine]
    exact axialGauge_gauge hodd _ γ hcentre x'
  have hγx : γ x = h := by
    show g (parentBlock R.params.side _) = _
    rw [hx1]
  set h₂ : UnitQuaternion := g (parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2))
    with hh₂
  have hγx₂ : γ (x + BlockAverages.unitStep F₀.depth c.2) = h₂ := by
    show g (parentBlock R.params.side _) = _
    rw [hx2]
  have hw' : BlockAverages.gaugeTransform
      (axialGauge 1 (readAtLevel F₀ 0 (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W)))
      (readAtLevel F₀ 0 (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W)) x c.2 =
        h * w * h₂⁻¹ := by
    have e1 : readAtLevel F₀ 0 (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) x c.2 =
        γ x * readAtLevel F₀ 0 W x c.2 * (γ (x + BlockAverages.unitStep F₀.depth c.2))⁻¹ := by
      rw [hfine]
      rfl
    show axialGauge 1 (readAtLevel F₀ 0 (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W)) x *
      readAtLevel F₀ 0 (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) x c.2 *
      (axialGauge 1 (readAtLevel F₀ 0 (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W))
        (x + BlockAverages.unitStep F₀.depth c.2))⁻¹ = _
    rw [htree, htree, e1, hγx, hγx₂]
    show _ = h * (T x * readAtLevel F₀ 0 W x c.2 * (T (x + BlockAverages.unitStep F₀.depth c.2))⁻¹) * h₂⁻¹
    group
  have hρ1 : R.ballRadius ≤ 1 := by
    unfold StepSettings.StepSetup.ballRadius
    linarith
  have hfr2 : ((frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.gaugeTransform g V) c :
      imaginaryQuaternions) : ℍ[ℝ]) = (h : ℍ[ℝ]) *
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach V c : imaginaryQuaternions) : ℍ[ℝ]) *
        ((h⁻¹ : UnitQuaternion) : ℍ[ℝ]) := hfr1
  have hy0 : toTorusSite n (enclosingCell x) = parentBlock R.params.side c.1 := by
    rw [← parentBlock_of_enclosingCell hodd, hx1]
  have hy2 : toTorusSite n (enclosingCell (x + BlockAverages.unitStep F₀.depth c.2)) =
      parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2) := by
    rw [← parentBlock_of_enclosingCell hodd, hx2]
  by_cases hcr : IsCrossingBond (x, c.2)
  · have mk : ∀ (V₁ : TorusField n) (W₁ : TorusField (n * R.params.side)), bondMark R V₁ W₁ c =
        cutoffFactor R.ballRadius R.barrierFn
        ‖((minimalLog (BlockAverages.gaugeTransform (axialGauge 1 (readAtLevel F₀ 0 W₁)) (readAtLevel F₀ 0 W₁) x c.2 *
          (readAtLevel F₀ 1 V₁ (enclosingCell x) c.2)⁻¹) : imaginaryQuaternions) : ℍ[ℝ]) -
          ((frameCoord R.params R.anchorRadius R.depth R.frameReach V₁ c : imaginaryQuaternions) : ℍ[ℝ])‖ := by
      intro V₁ W₁
      unfold bondMark chartCoord bondCoordinate
      rw [if_pos hcr]
    have hstep : parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2) =
        parentBlock R.params.side c.1 + TorusFields.unitStep n c.2 := by
      refine (parentBlock_add_unitStep c.1 c.2).resolve_left fun he => hcr ?_
      refine toTorusSite_injective (N := n) (fun i => stepBlockFrame_period_one i) ?_
      exact hy2.trans (he.trans hy0.symm)
    have hV : readAtLevel F₀ 1 (TorusFields.gaugeTransform g V) (enclosingCell x) c.2 =
        h * readAtLevel F₀ 1 V (enclosingCell x) c.2 * h₂⁻¹ := by
      show TorusFields.gaugeTransform g V (toTorusSite n (enclosingCell x)) c.2 =
        g (parentBlock R.params.side c.1) * V (toTorusSite n (enclosingCell x)) c.2 *
          (g (parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2)))⁻¹
      rw [hy0, hstep]
      rfl
    rw [mk, mk, hw', hV]
    have hg : h * w * h₂⁻¹ * (h * readAtLevel F₀ 1 V (enclosingCell x) c.2 * h₂⁻¹)⁻¹ =
        h * (w * (readAtLevel F₀ 1 V (enclosingCell x) c.2)⁻¹) * h⁻¹ := by
      group
    rw [hg]
    exact cutoffFactor_conj hρ1 h _ _ _ hfr2 hsmall
  · have mk : ∀ (V₁ : TorusField n) (W₁ : TorusField (n * R.params.side)), bondMark R V₁ W₁ c =
        cutoffFactor R.ballRadius R.barrierFn
        ‖((minimalLog (BlockAverages.gaugeTransform (axialGauge 1 (readAtLevel F₀ 0 W₁)) (readAtLevel F₀ 0 W₁) x c.2) :
          imaginaryQuaternions) : ℍ[ℝ]) -
          ((frameCoord R.params R.anchorRadius R.depth R.frameReach V₁ c : imaginaryQuaternions) : ℍ[ℝ])‖ := by
      intro V₁ W₁
      unfold bondMark chartCoord bondCoordinate
      rw [if_neg hcr]
    have hsame : enclosingCell (x + BlockAverages.unitStep F₀.depth c.2) = enclosingCell x := not_not.mp hcr
    have hh₂e : h₂ = h := by
      show g _ = g _
      rw [← hy2, ← hy0, hsame]
    rw [mk, mk, hw', hh₂e]
    exact cutoffFactor_conj hρ1 h _ _ _ hfr2 hsmall
private theorem fillLabels_gauge (q : CoarseState R n) (g : TorusSite n → UnitQuaternion)
    (Yt : Finset (TorusSite (n * R.params.side))) (hAY : q.labelSet ⊆ Yt)
    (hsep : ∀ z ∈ q.labelSet, ∀ u ∈ Yt, supDist u z ≤ 1 → u ∈ q.labelSet)
    (ν : q.unlabelled Yt → R.labels.Ω) (ν' : (q.gaugeTransform g).unlabelled Yt → R.labels.Ω)
    (hν : ∀ z hz hz', ν' ⟨z, hz⟩ = R.labels.act (q.unlabelled Yt) (blockConstantGauge R.params.side g) ν ⟨z, hz'⟩) :
    (q.gaugeTransform g).fillLabels Yt ν' = R.labels.act Yt (blockConstantGauge R.params.side g) (q.fillLabels Yt ν) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.fillLabels_gaugeTransform <;> assumption
private theorem torusHotLumps_gauge (hfit : R.params.Admissible) {m : ℕ} [NeZero m] (hLn : R.params.side ∣ m)
    (G : TorusSite m → UnitQuaternion) (W : TorusField m) :
    torusHotLumps R.params (TorusFields.gaugeTransform G W) = torusHotLumps R.params W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.torusHotLumps_gaugeTransform <;> assumption
private theorem isHullState_gauge (hfit : R.params.Admissible) {m : ℕ} [NeZero m] (hLn : R.params.side ∣ m)
    (G : TorusSite m → UnitQuaternion) (W : TorusField m) (r : ℕ) (Y : Finset (TorusSite m)) :
    IsHullState R.params r (TorusFields.gaugeTransform G W) Y ↔ IsHullState R.params r W Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.isHullState_gaugeTransform_iff <;> assumption
private theorem gaugeTransform_injective (h : CoarseLabelFacts R) {x y : CoarseState R n}
    (g : TorusSite n → UnitQuaternion) (e : x.gaugeTransform g = y.gaugeTransform g) : x = y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.gaugeTransform_injective <;> assumption
private def _root_.YangMills.Construction.StepSettings.CoarseState.LabelsFitIn (q : CoarseState R n)
    (Yt : Finset (TorusSite (n * R.params.side))) : Prop :=
  q.labelSet ⊆ Yt ∧ ∀ z ∈ q.labelSet, ∀ u ∈ Yt, supDist u z ≤ 1 → u ∈ q.labelSet
private theorem labelsFitIn_coarseStateOf (hL : R.params.side ≤ 6 * R.range) (C : Finset (TorusSite n))
    (F : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (L : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    (coarseStateOf R C F Yt L bad b).LabelsFitIn Yt := by
  classical
  have hmem : ∀ {u}, u ∈ (coarseStateOf R C F Yt L bad b).labelSet ↔
      u ∈ Yt ∧ parentBlock R.params.side u ∈ storedBlocks R.params.side R.range bad Yt C :=
    mem_labelSet_coarseStateOf C F Yt L bad b
  refine ⟨fun z hz => (hmem.mp hz).1, fun z hz u hu hd => ?_⟩
  obtain ⟨h1, h2⟩ := hmem.mp hz
  have hθ := mem_attachedSites_of_parentBlock_mem R.range bad Yt C hL
    (Finset.mem_union_left _ (Finset.mem_union_right _ h1)) h2
  have hLp : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  exact hmem.mpr ⟨hu, parentBlock_mem_storedBlocks_of_near R.range bad Yt C hθ (by omega)⟩
private theorem configurationMass_eq_zero (hL : R.params.side ≤ 6 * R.range) (C : Finset (TorusSite n))
    (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (q : CoarseState R n) (hq : ¬ q.LabelsFitIn Yt) :
    configurationMass R C V bad Yt b q = 0 := by
  classical
  have hno : ∀ W ν, ¬ (IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
      coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) := by
    intro W ν h
    apply hq
    have := labelsFitIn_coarseStateOf hL C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b
    rwa [h.2] at this
  have h0 : ∀ W, (∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
      (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
          coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
        ENNReal.ofReal (stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) else 0)
      ∂(Measure.pi fun _ => R.labels.μ)) = 0 := by
    intro W
    rw [lintegral_congr fun ν => if_neg (hno W ν)]
    simp
  unfold configurationMass
  rw [lintegral_congr h0]
  simp
private theorem labelsFitIn_gauge (q : CoarseState R n) (g : TorusSite n → UnitQuaternion)
    (Yt : Finset (TorusSite (n * R.params.side))) :
    (q.gaugeTransform g).LabelsFitIn Yt ↔ q.LabelsFitIn Yt := by
  unfold StepSettings.CoarseState.LabelsFitIn
  rw [labelSet_gaugeTransform]
private theorem lintegral_labels_gauge (Λ : LabelSpace) {m : ℕ} [NeZero m] (G : TorusSite m → UnitQuaternion)
    {S S' : Finset (TorusSite m)} (h : S' = S) (f' : (S' → Λ.Ω) → ENNReal) (f : (S → Λ.Ω) → ENNReal)
    (hf : ∀ ν ν', (∀ z hz hz', ν' ⟨z, hz⟩ = Λ.act S G ν ⟨z, hz'⟩) → f' ν' = f ν) :
    ∫⁻ ν', f' ν' ∂(Measure.pi fun _ : S' => Λ.μ) = ∫⁻ ν, f ν ∂(Measure.pi fun _ : S => Λ.μ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.lintegral_labelAct <;> assumption
private theorem lintegral_field_gauge {m : ℕ} [NeZero m] (hh : HaarInvariantUnderSymmetries)
    (G : TorusSite m → UnitQuaternion) (f' f : TorusField m → ENNReal)
    (hf : ∀ W, f' (TorusFields.gaugeTransform G W) = f W) :
    ∫⁻ W, f' W ∂(fieldHaar m) = ∫⁻ W, f W ∂(fieldHaar m) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.lintegral_fieldHaar_gaugeTransform <;> assumption
private theorem baseLaw_gauge (hk : KernelGaugeInvariance) (hfit : R.params.Admissible) (g : TorusSite n → UnitQuaternion)
    (F : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    baseLaw (R := R) (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) F) b = baseLaw (R := R) F b := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.baseLaw_gaugeTransform <;> assumption
private theorem stepWeight_gauge (hR : R.IsWellPosed) (hF : R.ColdChainFits) (hfr : FrameCovariance)
    (hsz : FrameNearMinimizer) (hk : KernelGaugeInvariance)
    (hn : R.params.n₀ ≤ n) {S C : Finset (TorusSite n)} {s : ℝ} (hs : 0 ≤ s) (V : TorusField n)
    (hsit : IsStepSituation R.params R.nextRange V S C s) (g : TorusSite n → UnitQuaternion)
    (F : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (L : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hh : IsHullState R.params R.range F Yt) :
    stepWeight R C (TorusFields.gaugeTransform g V) (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) F) Yt
        (R.labels.act Yt (blockConstantGauge R.params.side g) L) bad b = stepWeight R C V F Yt L bad b := by
  classical
  have hsideL : IsBlockTorusSide R.params (n * R.params.side) := ⟨Dvd.intro_left n rfl, by
    rw [mul_comm R.params.side R.params.n₀]
    exact Nat.mul_le_mul_right _ hn⟩
  have hD := hR.hasExpansions.2.gauge (n * R.params.side) hsideL F Yt L (blockConstantGauge R.params.side g) hh
  have hB := baseLaw_gauge (R := R) hk hR.admissible g F b
  have hM : markProduct R C (TorusFields.gaugeTransform g V)
      (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) F) bad = markProduct R C V F bad := by
    unfold markProduct
    refine Finset.prod_congr rfl fun c hc => ?_
    have hm := Finset.mem_filter.mp hc
    rw [bondMark_gauge hR hF hfr hsz hs V hsit g F c hm.1 hm.2]
  unfold stepWeight
  rw [hD, hB, hM]
  by_cases hb : b ∈ baseChoices R.params (fineLevelField R.params n F)
  · have hK := ((hk R.params hR.admissible n g F V).2.2 R.coupling).1 b hb
    have : ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4, bondKernel R.params R.coupling
          (readAtLevel (stepBlockFrame R.params.side n) 0
            (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) F))
          (readAtLevel (stepBlockFrame R.params.side n) 1 (TorusFields.gaugeTransform g V)) b c =
        ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4, bondKernel R.params R.coupling
          (readAtLevel (stepBlockFrame R.params.side n) 0 F)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c :=
      Finset.prod_congr rfl fun c _ => hK c
    rw [this]
  · have h0 : baseLaw (R := R) F b = 0 := by
      unfold baseLaw
      exact if_neg hb
    rw [h0]
    simp
private theorem configurationMass_gauge (hl : CoarseLabelFacts R) (hR : R.IsWellPosed) (hF : R.ColdChainFits)
    (hfr : FrameCovariance) (hsz : FrameNearMinimizer) (hk : KernelGaugeInvariance) (hh : HaarInvariantUnderSymmetries)
    (hn : R.params.n₀ ≤ n) {S C : Finset (TorusSite n)} {s : ℝ} (hs : 0 ≤ s) (V : TorusField n)
    (hsit : IsStepSituation R.params R.nextRange V S C s) (g : TorusSite n → UnitQuaternion)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (q : CoarseState R n) :
    configurationMass R C (TorusFields.gaugeTransform g V) bad Yt b (q.gaugeTransform g) =
      configurationMass R C V bad Yt b q := by
  classical
  have hL6 : R.params.side ≤ 6 * R.range := by
    have := hR.range_ge_side
    omega
  have hLn' : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
  by_cases hfit : q.LabelsFitIn Yt
  · unfold configurationMass
    refine lintegral_field_gauge hh (blockConstantGauge R.params.side g) _ _ fun W => ?_
    have hrest : (q.gaugeTransform g).unlabelled Yt = q.unlabelled Yt := by
      rw [unlabelled_eq_sdiff, unlabelled_eq_sdiff, labelSet_gaugeTransform]
    refine lintegral_labels_gauge R.labels (blockConstantGauge R.params.side g) hrest _ _ fun ν ν' hν => ?_
    have hf := fieldWithStoredLinks_gauge q g W
    have hlab := fillLabels_gauge q g Yt hfit.1 hfit.2 ν ν' hν
    rw [hf, hlab, coarseStateOf_gauge hL6]
    by_cases hhull : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt
    · have hh' := (isHullState_gauge (R := R) hR.admissible hLn' (blockConstantGauge R.params.side g)
        (q.fieldWithStoredLinks W) R.range Yt).mpr hhull
      by_cases hst : coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q
      · rw [if_pos ⟨hh', by rw [hst]⟩, if_pos ⟨hhull, hst⟩,
          stepWeight_gauge hR hF hfr hsz hk hn hs V hsit g _ Yt _ bad b hhull]
      · rw [if_neg fun h => hst (gaugeTransform_injective hl g h.2), if_neg fun h => hst h.2]
    · have hh' : ¬ IsHullState R.params R.range
          (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) (q.fieldWithStoredLinks W)) Yt := fun h =>
        hhull ((isHullState_gauge (R := R) hR.admissible hLn' (blockConstantGauge R.params.side g)
          (q.fieldWithStoredLinks W) R.range Yt).mp h)
      rw [if_neg fun h => hh' h.1, if_neg fun h => hhull h.1]
  · rw [configurationMass_eq_zero hL6 _ _ _ _ _ _ hfit,
      configurationMass_eq_zero hL6 _ _ _ _ _ _ (fun h => hfit ((labelsFitIn_gauge q g Yt).mp h))]
private theorem integral_labels_gauge (Λ : LabelSpace) {m : ℕ} [NeZero m] (G : TorusSite m → UnitQuaternion)
    {S S' : Finset (TorusSite m)} (h : S' = S) (f' : (S' → Λ.Ω) → ℝ) (f : (S → Λ.Ω) → ℝ)
    (hf : ∀ ν ν', (∀ z hz hz', ν' ⟨z, hz⟩ = Λ.act S G ν ⟨z, hz'⟩) → f' ν' = f ν) :
    ∫ ν', f' ν' ∂(Measure.pi fun _ : S' => Λ.μ) = ∫ ν, f ν ∂(Measure.pi fun _ : S => Λ.μ) := by
  subst h
  have hmp := Λ.act_keeps S' G
  have hmeas : ∀ G' : TorusSite m → UnitQuaternion, Measurable (Λ.act S' G') := fun G' =>
    (Λ.act_borel S').comp (measurable_const.prodMk measurable_id)
  have hinv : ∀ (G' : TorusSite m → UnitQuaternion) ν, Λ.act S' G'⁻¹ (Λ.act S' G' ν) = ν := by
    intro G' ν
    rw [← Λ.act_mul]
    have : G'⁻¹ * G' = fun _ => 1 := by
      funext z
      simp
    rw [this, Λ.act_one]
  let e : (S' → Λ.Ω) ≃ᵐ (S' → Λ.Ω) :=
    { toFun := Λ.act S' G
      invFun := Λ.act S' G⁻¹
      left_inv := hinv G
      right_inv := fun ν => by
        have := hinv G⁻¹ ν
        rwa [inv_inv] at this
      measurable_toFun := hmeas G
      measurable_invFun := hmeas G⁻¹ }
  rw [← hmp.integral_comp e.measurableEmbedding f']
  exact integral_congr_ae (Filter.Eventually.of_forall fun ν => hf ν _ fun _ _ _ => rfl)
private theorem integral_field_gauge {m : ℕ} [NeZero m] (hh : HaarInvariantUnderSymmetries)
    (G : TorusSite m → UnitQuaternion) (f' f : TorusField m → ℝ) (hf : ∀ W, f' (TorusFields.gaugeTransform G W) = f W) :
    ∫ W, f' W ∂(fieldHaar m) = ∫ W, f W ∂(fieldHaar m) := by
  have hmp := (hh m).1 G
  have hinv : ∀ (G' : TorusSite m → UnitQuaternion) (W : TorusField m),
      TorusFields.gaugeTransform G'⁻¹ (TorusFields.gaugeTransform G' W) = W := by
    intro G' W
    funext x i
    simp [TorusFields.gaugeTransform, mul_assoc]
  let e : TorusField m ≃ᵐ TorusField m :=
    { toFun := TorusFields.gaugeTransform G
      invFun := TorusFields.gaugeTransform G⁻¹
      left_inv := hinv G
      right_inv := fun W => by
        have := hinv G⁻¹ W
        rwa [inv_inv] at this
      measurable_toFun := ((hh m).1 G).measurable
      measurable_invFun := ((hh m).1 G⁻¹).measurable }
  rw [← hmp.integral_comp e.measurableEmbedding f']
  exact integral_congr_ae (Filter.Eventually.of_forall hf)
abbrev _root_.YangMills.SharedProofs.p87219 := @integral_field_gauge
private theorem caseTerm_eq_zero (hL : R.params.side ≤ 6 * R.range) (C : Finset (TorusSite n)) (V : TorusField n)
    (F : CaseFunction R n) (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (q : CoarseState R n) (hq : ¬ q.LabelsFitIn Yt) (W : TorusField (n * R.params.side))
    (ν : q.unlabelled Yt → R.labels.Ω) :
    caseTerm R C V q F bad Yt b W ν = 0 := by
  classical
  unfold caseTerm
  refine if_neg fun h => hq ?_
  have := labelsFitIn_coarseStateOf hL C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b
  rwa [h.2] at this
private theorem caseTerm_integral_gauge (hl : CoarseLabelFacts R) (hR : R.IsWellPosed) (hF : R.ColdChainFits)
    (hfr : FrameCovariance) (hsz : FrameNearMinimizer) (hk : KernelGaugeInvariance) (hh : HaarInvariantUnderSymmetries)
    (hn : R.params.n₀ ≤ n) {S C : Finset (TorusSite n)} {s : ℝ} (hs : 0 ≤ s) (V : TorusField n)
    (hsit : IsStepSituation R.params R.nextRange V S C s) (g : TorusSite n → UnitQuaternion)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (q : CoarseState R n) (Fn Fn' : CaseFunction R n)
    (hFF : ∀ (W : TorusField (n * R.params.side)) (Yt' : Finset (TorusSite (n * R.params.side))) (ωt : Yt' → R.labels.Ω)
      (bad' : Finset (TorusBond (n * R.params.side))) (b' : BaseChoice R.params.side n),
      IsLiveState R.params R.coupling R.labelWeight W Yt' ωt →
      b' ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) →
      Fn' (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) Yt'
        (R.labels.act Yt' (blockConstantGauge R.params.side g) ωt) bad' b' = Fn W Yt' ωt bad' b') :
    ∫ W, ∫ ν : (q.gaugeTransform g).unlabelled Yt → R.labels.Ω,
        caseTerm R C (TorusFields.gaugeTransform g V) (q.gaugeTransform g) Fn' bad Yt b W ν
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) =
      ∫ W, ∫ ν : q.unlabelled Yt → R.labels.Ω, caseTerm R C V q Fn bad Yt b W ν
        ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  classical
  have hL6 : R.params.side ≤ 6 * R.range := by
    have := hR.range_ge_side
    omega
  have hLn' : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
  by_cases hfit : q.LabelsFitIn Yt
  · refine integral_field_gauge hh (blockConstantGauge R.params.side g) _ _ fun W => ?_
    have hrest : (q.gaugeTransform g).unlabelled Yt = q.unlabelled Yt := by
      rw [unlabelled_eq_sdiff, unlabelled_eq_sdiff, labelSet_gaugeTransform]
    refine integral_labels_gauge R.labels (blockConstantGauge R.params.side g) hrest _ _ fun ν ν' hν => ?_
    have hf := fieldWithStoredLinks_gauge q g W
    have hlab := fillLabels_gauge q g Yt hfit.1 hfit.2 ν ν' hν
    unfold caseTerm
    rw [hf, hlab, coarseStateOf_gauge hL6]
    by_cases hhull : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt
    · have hh' := (isHullState_gauge (R := R) hR.admissible hLn' (blockConstantGauge R.params.side g)
        (q.fieldWithStoredLinks W) R.range Yt).mpr hhull
      by_cases hst : coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q
      · rw [if_pos ⟨hh', by rw [hst]⟩, if_pos ⟨hhull, hst⟩,
          stepWeight_gauge hR hF hfr hsz hk hn hs V hsit g _ Yt _ bad b hhull]
        by_cases hw : stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = 0
        · rw [hw, mul_zero, mul_zero]
        · have hlive : IsLiveState R.params R.coupling R.labelWeight (q.fieldWithStoredLinks W) Yt
              (q.fillLabels Yt ν) := by
            have hsideL : IsBlockTorusSide R.params (n * R.params.side) := ⟨Dvd.intro_left n rfl, by
              rw [mul_comm R.params.side R.params.n₀]
              exact Nat.mul_le_mul_right _ hn⟩
            refine ⟨hhull, lt_of_le_of_ne (hR.hasExpansions.2.nonneg _ hsideL _ _ _ hhull) fun h0 => hw ?_⟩
            unfold stepWeight
            rw [← h0]
            ring
          have hb : b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 (q.fieldWithStoredLinks W)) := by
            by_contra hb
            apply hw
            unfold stepWeight baseLaw
            rw [if_neg hb]
            ring
          rw [hFF _ Yt _ bad b hlive hb]
      · rw [if_neg fun h => hst (gaugeTransform_injective hl g h.2), if_neg fun h => hst h.2]
    · have hh' : ¬ IsHullState R.params R.range
          (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) (q.fieldWithStoredLinks W)) Yt := fun h =>
        hhull ((isHullState_gauge (R := R) hR.admissible hLn' (blockConstantGauge R.params.side g)
          (q.fieldWithStoredLinks W) R.range Yt).mp h)
      rw [if_neg fun h => hh' h.1, if_neg fun h => hhull h.1]
  · have h1 : ¬ (q.gaugeTransform g).LabelsFitIn Yt := fun h => hfit ((labelsFitIn_gauge q g Yt).mp h)
    simp only [caseTerm_eq_zero hL6 _ _ _ _ _ _ _ hfit, caseTerm_eq_zero hL6 _ _ _ _ _ _ _ h1]
    simp
private theorem caseIntegral_gauge (hl : CoarseLabelFacts R) (hR : R.IsWellPosed) (hF : R.ColdChainFits)
    (hfr : FrameCovariance) (hsz : FrameNearMinimizer) (hk : KernelGaugeInvariance) (hh : HaarInvariantUnderSymmetries)
    (hn : R.params.n₀ ≤ n) {S C : Finset (TorusSite n)} {s : ℝ} (hs : 0 ≤ s) (V : TorusField n)
    (hsit : IsStepSituation R.params R.nextRange V S C s) (g : TorusSite n → UnitQuaternion) (q : CoarseState R n)
    (Fn Fn' : CaseFunction R n)
    (hFF : ∀ (W : TorusField (n * R.params.side)) (Yt' : Finset (TorusSite (n * R.params.side))) (ωt : Yt' → R.labels.Ω)
      (bad' : Finset (TorusBond (n * R.params.side))) (b' : BaseChoice R.params.side n),
      IsLiveState R.params R.coupling R.labelWeight W Yt' ωt →
      b' ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) →
      Fn' (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) Yt'
        (R.labels.act Yt' (blockConstantGauge R.params.side g) ωt) bad' b' = Fn W Yt' ωt bad' b') :
    caseIntegral R C (TorusFields.gaugeTransform g V) (q.gaugeTransform g) Fn' = caseIntegral R C V q Fn :=
  Finset.sum_congr rfl fun bad _ => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ =>
    caseTerm_integral_gauge hl hR hF hfr hsz hk hh hn hs V hsit g bad Yt b q Fn Fn' hFF
private theorem coarseStateWeight_gauge (hl : CoarseLabelFacts R) (hR : R.IsWellPosed) (hF : R.ColdChainFits)
    (hfr : FrameCovariance) (hsz : FrameNearMinimizer) (hk : KernelGaugeInvariance) (hh : HaarInvariantUnderSymmetries)
    (hn : R.params.n₀ ≤ n) {S C : Finset (TorusSite n)} {s : ℝ} (hs : 0 ≤ s) (V : TorusField n)
    (hsit : IsStepSituation R.params R.nextRange V S C s) (g : TorusSite n → UnitQuaternion) (q : CoarseState R n) :
    coarseStateWeight R C (TorusFields.gaugeTransform g V) (q.gaugeTransform g) = coarseStateWeight R C V q :=
  congrArg ENNReal.toReal (Finset.sum_congr rfl fun bad _ => Finset.sum_congr rfl fun Yt _ =>
    Finset.sum_congr rfl fun b _ => configurationMass_gauge hl hR hF hfr hsz hk hh hn hs V hsit g bad Yt b q)
private theorem caseResponse_gauge (hsg : BondScoreGaugeInvariantStatement) (hfit : R.params.Admissible)
    {A : ResponseSetup R} (hA : A.IsAdmissible) (hside : IsBlockTorusSide R.params (n * R.params.side))
    (V : TorusField n) (g : TorusSite n → UnitQuaternion) (y : TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt)
    (hb : b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)) :
    caseResponse A (TorusFields.gaugeTransform g V) y h
        (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) Yt
        (R.labels.act Yt (blockConstantGauge R.params.side g) ωt) bad b =
      caseResponse A V y h W Yt ωt bad b := by
  have e : ∀ z ∈ sitesInBlocks R.params.side {y}, A.hull (n * R.params.side) z
      (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) Yt
      (R.labels.act Yt (blockConstantGauge R.params.side g) ωt) h = A.hull (n * R.params.side) z W Yt ωt h :=
    fun z _ => hA.bounds.hull_gauge (n * R.params.side) hside z (blockConstantGauge R.params.side g) W Yt ωt hl h
  have e' : ∀ c : TorusBond n, bondScore R.params R.coupling
      (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) (TorusFields.gaugeTransform g V) b c =
      bondScore R.params R.coupling W V b c :=
    fun c => hsg R.params hfit R.coupling n g W V b c hb
  show ∑ z ∈ sitesInBlocks R.params.side {y}, A.hull (n * R.params.side) z
        (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) Yt
        (R.labels.act Yt (blockConstantGauge R.params.side g) ωt) h +
      R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n y h *
        blockBondScores (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W)
          (TorusFields.gaugeTransform g V) b y =
    ∑ z ∈ sitesInBlocks R.params.side {y}, A.hull (n * R.params.side) z W Yt ωt h +
      R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n y h * blockBondScores W V b y
  rw [Finset.sum_congr rfl e]
  unfold blockBondScores
  simp only [e']
end StepResponseGauge
open StepResponseGauge in
theorem stepResponseGaugeInvariant_holds (hfr : FrameCovariance) (hsz : FrameNearMinimizer)
    (hk : KernelGaugeInvariance) (hh : HaarInvariantUnderSymmetries) (hsg : BondScoreGaugeInvariantStatement) :
    StepResponseGaugeInvariant := by
  classical
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ K => ⟨0, fun y _ R A _ hAt hS hL => ?_⟩⟩
  have hOn := hAt.onFamily
  have hresp := hAt.admissible
  have hfit := hS.admissible
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have ha : R.params.coupling = T.coupling := by rw [hOn.params_eq]; rfl
  have hLT : R.params.side = T.side := by rw [hOn.params_eq]; rfl
  have hσ : R.params.threshold = T.threshold := by rw [hOn.params_eq]; rfl
  have hchain : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [ha, hLT, hOn.anchorRadius_eq]
    exact hT.chain
  have hF : R.ColdChainFits :=
    ⟨T.δ₁, T.lam, T.σA, T.cg, T.N, hchain, by rw [hσ]; exact hT.σ_le, by rw [hσ]; exact hT.σ_one⟩
  have hblockOf : ∀ {n : ℕ}, R.params.n₀ ≤ n → IsBlockTorusSide R.params (n * R.params.side) := fun hn =>
    ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  refine ⟨fun n _ hn y' g W hc h => ?_, fun n _ hn y' g W Y ω hl h => ?_⟩
  · have hsit : IsStepSituation R.params R.nextRange W Finset.univ ∅ (9 / 8 * R.params.threshold) :=
      Or.inr ⟨hn, fun x μ ν h => (hc x μ ν h).trans (by linarith [hfit.σ_pos]), rfl, rfl, rfl⟩
    have hs : (0 : ℝ) ≤ 9 / 8 * R.params.threshold := by linarith [hfit.σ_pos]
    have hq : (emptyCoarseState R (n := n)).gaugeTransform g = emptyCoarseState R := by
      unfold emptyCoarseState StepSettings.CoarseState.gaugeTransform
      congr 1
      funext z
      exact absurd z.2 (Finset.notMem_empty _)
    have e₁ := caseIntegral_gauge hL hS hF hfr hsz hk hh hn hs W hsit g (emptyCoarseState R)
      (caseResponse A W y' h) (caseResponse A (TorusFields.gaugeTransform g W) y' h) fun W' Yt ωt bad b hl hb =>
        caseResponse_gauge hsg hfit hresp (hblockOf hn) W g y' h W' Yt ωt bad b hl hb
    have e₂ := coarseStateWeight_gauge hL hS hF hfr hsz hk hh hn hs W hsit g (emptyCoarseState R)
    rw [hq] at e₁ e₂
    show caseMean R ∅ (TorusFields.gaugeTransform g W) (emptyCoarseState R)
        (caseResponse A (TorusFields.gaugeTransform g W) y' h) =
      caseMean R ∅ W (emptyCoarseState R) (caseResponse A W y' h)
    unfold caseMean
    rw [e₁, e₂]
  · have hn₀ : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hL0) hn.2
    have hsit : IsStepSituation R.params R.nextRange W
        (Finset.univ \ thickening lumpRange (torusHotSites R.params W)) (hotCoreSites R W) R.params.threshold :=
      Or.inl ⟨hn, rfl, rfl, rfl⟩
    have hs : (0 : ℝ) ≤ R.params.threshold := hfit.σ_pos.le
    have hC : hotCoreSites R (TorusFields.gaugeTransform g W) = hotCoreSites R W := by
      unfold hotCoreSites torusHotSites
      rw [torusHotLumps_gauge (R := R) hfit hn.1]
    have e₁ := caseIntegral_gauge hL hS hF hfr hsz hk hh hn₀ hs W hsit g ⟨Y, ω⟩
      (caseResponse A W y' h) (caseResponse A (TorusFields.gaugeTransform g W) y' h) fun W' Yt ωt bad b hl hb =>
        caseResponse_gauge hsg hfit hresp (hblockOf hn₀) W g y' h W' Yt ωt bad b hl hb
    have e₂ := coarseStateWeight_gauge hL hS hF hfr hsz hk hh hn₀ hs W hsit g ⟨Y, ω⟩
    show caseMean R (hotCoreSites R (TorusFields.gaugeTransform g W)) (TorusFields.gaugeTransform g W)
        (StepSettings.CoarseState.gaugeTransform ⟨Y, ω⟩ g) (caseResponse A (TorusFields.gaugeTransform g W) y' h) =
      caseMean R (hotCoreSites R W) W ⟨Y, ω⟩ (caseResponse A W y' h)
    rw [hC]
    unfold caseMean
    rw [e₁, e₂]
end YangMills.Construction.ResponseInTheExpansion
end
