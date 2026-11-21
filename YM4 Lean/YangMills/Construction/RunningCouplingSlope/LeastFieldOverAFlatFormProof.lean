import YangMills.Construction.ClusterExpansionOfAStep.ChainOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.ContoursOnTheTorus
import YangMills.Construction.HoleBesideASecondHole.ActionAtIsACutAction
import YangMills.Construction.RunningCouplingSlope.LeastFieldNearTheFlatFieldProof
import YangMills.Construction.RunningCouplingSlope.LeastFieldOverAFlatForm
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.StepCosts YangMills.Construction.FlatLinearization YangMills.Construction.SlopeCoefficient YangMills.Construction.BondCoordinates YangMills.Construction.LumpContours
section Calculus
variable {E G A B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
private theorem fderiv_fderiv_comp_of_critical {f : G → ℝ} {g : E → G} {x : E} (hf : AnalyticAt ℝ f (g x))
    (hg : AnalyticAt ℝ g x) (hc : fderiv ℝ f (g x) = 0) (u v : E) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) x u v =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x u) (fderiv ℝ g x v) := by
  rw [BondCoordinates.secondDeriv_comp hf.contDiffAt hg.contDiffAt, hc]
  simp
private theorem hessian_weak_of_local_min {Φ : A × B → ℝ} {p : A × B} (hΦ : AnalyticAt ℝ Φ p) {ψ : E → A × B} {e : E}
    (hψ : AnalyticAt ℝ ψ e) (h0 : ψ e = p) (hmin : ∀ᶠ σ in 𝓝 e, ∀ Y : A, Φ (ψ σ) ≤ Φ (Y, (ψ σ).2))
    (ζ : A) (v : E) : fderiv ℝ (fderiv ℝ Φ) p (fderiv ℝ ψ e v) (ζ, 0) = 0 := by
  have hd : ∀ᶠ σ in 𝓝 e, fderiv ℝ Φ (ψ σ) (ζ, 0) = 0 := by
    have h1 : ∀ᶠ σ in 𝓝 e, AnalyticAt ℝ Φ (ψ σ) := by
      have h := hΦ.eventually_analyticAt
      rw [← h0] at h
      exact hψ.continuousAt.eventually h
    filter_upwards [h1, hmin] with σ ha hm
    have hl : IsLocalMin (fun u : ℝ => Φ ((ψ σ).1 + u • ζ, (ψ σ).2)) 0 := by
      refine Eventually.of_forall fun u => ?_
      simpa using hm _
    have hc : HasDerivAt (fun u : ℝ => ((ψ σ).1 + u • ζ, (ψ σ).2)) (ζ, (0 : B)) 0 := by
      have h2 : HasDerivAt (fun u : ℝ => (ψ σ).1 + u • ζ) ζ 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ζ).const_add (ψ σ).1
      exact h2.prodMk (hasDerivAt_const _ _)
    have hD : HasDerivAt (fun u : ℝ => Φ ((ψ σ).1 + u • ζ, (ψ σ).2)) (fderiv ℝ Φ (ψ σ) (ζ, 0)) 0 := by
      have h3 : HasFDerivAt Φ (fderiv ℝ Φ (ψ σ)) (((ψ σ).1 + (0 : ℝ) • ζ, (ψ σ).2)) := by
        simpa using ha.differentiableAt.hasFDerivAt
      exact h3.comp_hasDerivAt 0 hc
    exact hl.hasDerivAt_eq_zero hD
  have hH : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) p) (ψ e) := by
    rw [h0]
    exact hΦ.fderiv.differentiableAt.hasFDerivAt
  have hc := hH.comp e hψ.differentiableAt.hasFDerivAt
  have h4 := (ContinuousLinearMap.apply ℝ ℝ ((ζ, 0) : A × B)).hasFDerivAt.comp e hc
  have h5 : HasFDerivAt (fun σ => fderiv ℝ Φ (ψ σ) (ζ, 0)) (0 : E →L[ℝ] ℝ) e :=
    (hasFDerivAt_const (0 : ℝ) e).congr_of_eventuallyEq hd
  have h6 := congrArg (fun T : E →L[ℝ] ℝ => T v) (h4.unique h5)
  simpa using h6
private theorem bilin_eq_polar {H : A →L[ℝ] A →L[ℝ] ℝ} (hs : ∀ u v, H u v = H v u) (u v : A) :
    H u v = (H (u + v) (u + v) - H u u - H v v) / 2 := by
  simp only [map_add, ContinuousLinearMap.add_apply]
  rw [hs v u]
  ring
end Calculus
section Depths
private def fintypeSite (F : BlockFrame) (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) (j : ℕ) :
    Fintype (F.Site j) :=
  haveI : ∀ i, NeZero (F.period j i) := fun i => ⟨by
    unfold BlockFrame.period
    exact (Nat.mul_pos (hs i) (pow_pos hL _)).ne'⟩
  inferInstance
private theorem nondegenerate_at_depth (hW : WilsonActionNondegenerate) (hX : NondegenerateAcrossFrames)
    (hT : minimalActionNondegeneratePropagatesStatement) {a : ℝ} (ha : 0 < a) {L : ℕ} (hL : Odd L) :
    ∀ (t n : ℕ), 2 ≤ n → ∀ (inst : Fintype ((torusFrame L t n).Site t)),
      IsNondegenerateAtTrivial (F := torusFrame L t n) (k := t)
        (minimalAction a (finiteCells (torusFrame L t n)) t) := by apply _root_.YangMills.SharedProofs.p33643 <;> assumption
end Depths
section Charts
variable {F : BlockFrame}
private theorem chartedField_tree (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (b : F.Site F.depth × Fin 4) (hb : IsAxialTreeBond b) :
    chartedField w V b.1 b.2 = 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartDeterminedByField.chartedField_eq_one <;> assumption
private theorem stepCoordinates_zero (S : Finset F.Cell) : stepCoordinates (0 : StepVariable S) =
    fun (_ : F.Site F.depth) (_ : Fin 4) => (0 : imaginaryQuaternions) := by apply _root_.YangMills.SharedProofs.p23017 <;> assumption
private theorem fieldAboveFrame_zero (a ρ : ℝ) (V : F.GaugeField F.top) :
    fieldAboveFrame true a ρ 0 V 0 = chartedField (minimizingCoordinates a (finiteCells F) V ρ) V := by apply _root_.YangMills.SharedProofs.p22006 <;> assumption
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
private theorem analyticAt_expUnit {w : X → imaginaryQuaternions} {e : X}
    (h : AnalyticAt ℝ (fun y => (w y : ℍ[ℝ])) e) :
    AnalyticAt ℝ (fun y => ((expUnit (w y) : UnitQuaternion) : ℍ[ℝ])) e :=
  AnalyticAt.comp (g := NormedSpace.exp) (f := fun y => (w y : ℍ[ℝ])) (NormedSpace.exp_analytic (𝕂 := ℝ) _) h
private theorem analyticAt_stepCoordinates {S : Finset F.Cell} {η : X → StepVariable S} {e : X}
    (h : AnalyticAt ℝ η e) (x : F.Site F.depth) (i : Fin 4) :
    AnalyticAt ℝ (fun y => stepCoordinates (η y) x i) e := by apply _root_.YangMills.SharedProofs.p31047 <;> assumption
private theorem analyticAt_coe_imaginary {w : X → imaginaryQuaternions} {e : X} (h : AnalyticAt ℝ w e) :
    AnalyticAt ℝ (fun y => (w y : ℍ[ℝ])) e :=
  (imaginaryQuaternions.subtypeL.analyticAt _).comp h
private theorem isAnalyticFieldFamily_chartedField {w : X → F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : X → F.GaugeField F.top} {e : X}
    (hw : ∀ x i, AnalyticAt ℝ (fun y => (w y x i : ℍ[ℝ])) e) (hV : IsAnalyticFieldFamily V e) :
    IsAnalyticFieldFamily (fun y => chartedField (w y) (V y)) e := by apply _root_.YangMills.SharedProofs.p38066 <;> assumption
end Charts
section Minimizers
variable {F : BlockFrame}
private theorem chartedField_zero_trivial :
    chartedField (fun _ _ => 0) (trivialBlockField F F.top) = trivialBlockField F F.depth := by apply _root_.YangMills.SharedProofs.p20491 <;> assumption
private theorem stepCoordinates_isMinimizing (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide) {a ρ : ℝ}
    (hρ : ρ ≤ 1) {η : StepVariable (finiteCells F)} {V : F.GaugeField F.top} (hη : ‖η‖ ≤ ρ)
    (hmin : ∀ W', blockEnergy a (finiteCells F) F.depth (chartedField (stepCoordinates η) V) V ≤
      blockEnergy a (finiteCells F) F.depth W' V)
    (horb : ∀ W', (∀ W'', blockEnergy a (finiteCells F) F.depth W' V ≤ blockEnergy a (finiteCells F) F.depth W'' V) →
      ∃ γ : F.Site F.depth → UnitQuaternion, (∀ z, γ (cellCentre F.depth z) = 1) ∧
        W' = _root_.YangMills.Construction.BlockAverages.gaugeTransform γ (chartedField (stepCoordinates η) V)) :
    IsMinimizingChart a (finiteCells F) V ρ (stepCoordinates η) ∧
      minimizingCoordinates a (finiteCells F) V ρ = stepCoordinates η := by apply _root_.YangMills.SharedProofs.p92136 <;> assumption
end Minimizers
section Energy
variable {F : BlockFrame}
private def toQuatForm {k : ℕ} (η : F.Site k → Fin 4 → imaginaryQuaternions) : F.Site k → Fin 4 → ℍ[ℝ] :=
  fun x i => (η x i : ℍ[ℝ])
private theorem toQuatForm_add {k : ℕ} (η η' : F.Site k → Fin 4 → imaginaryQuaternions) :
    toQuatForm (η + η') = toQuatForm η + toQuatForm η' := by
  funext x i
  simp [toQuatForm]
private def averageForm {j : ℕ} (β : F.Site j → Fin 4 → imaginaryQuaternions) (c : F.Site (j + 1) × Fin 4) :
    imaginaryQuaternions :=
  (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
    formAlongPath β (_root_.YangMills.Construction.BlockAverages.refineSite c.1) (bondContour F.blockSide h π c.2)
private theorem linkForm_add {k : ℕ} (β β' : F.Site k → Fin 4 → imaginaryQuaternions) (x : F.Site k)
    (st : PathStep) : linkForm (β + β') x st = linkForm β x st + linkForm β' x st := by
  unfold linkForm
  cases st.2
  · simp only [Bool.false_eq_true, if_false, Pi.add_apply]
    abel
  · simp
private theorem formAlongPath_add {k : ℕ} (β β' : F.Site k → Fin 4 → imaginaryQuaternions) (l : List PathStep) :
    ∀ x, formAlongPath (β + β') x l = formAlongPath β x l + formAlongPath β' x l := by
  induction l with
  | nil => intro x; simp [formAlongPath]
  | cons st r ih =>
    intro x
    simp only [formAlongPath, linkForm_add, ih]
    abel
private theorem averageForm_add {j : ℕ} (β β' : F.Site j → Fin 4 → imaginaryQuaternions)
    (c : F.Site (j + 1) × Fin 4) : averageForm (β + β') c = averageForm β c + averageForm β' c := by
  unfold averageForm
  simp only [formAlongPath_add, Finset.sum_add_distrib, smul_add]
private theorem hasDerivAt_contourAverage {j : ℕ} {c : ℝ → F.GaugeField j}
    {β : F.Site j → Fin 4 → imaginaryQuaternions} (hc : IsCurveThroughTrivial c β) (b : F.Site (j + 1) × Fin 4) :
    HasDerivAt (fun τ => BlockAverages.contourAverage (c τ) b) ((averageForm β b : imaginaryQuaternions) : ℍ[ℝ]) 0 := by
  unfold BlockAverages.contourAverage averageForm
  have hs : HasDerivAt (fun τ => ∑ o ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy (c τ) (_root_.YangMills.Construction.BlockAverages.refineSite b.1) (bondContour F.blockSide o π b.2) : UnitQuaternion) : ℍ[ℝ]))
      (∑ o ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        ((formAlongPath β (_root_.YangMills.Construction.BlockAverages.refineSite b.1) (bondContour F.blockSide o π b.2) : imaginaryQuaternions) : ℍ[ℝ])) 0 :=
    HasDerivAt.fun_sum fun o _ => HasDerivAt.fun_sum fun π _ => hc.hasDerivAt_path _ _
  have h := hs.const_smul (1 / (24 * (F.blockSide : ℝ) ^ 4))
  have e : (((1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      formAlongPath β (_root_.YangMills.Construction.BlockAverages.refineSite b.1) (bondContour F.blockSide h π b.2) : imaginaryQuaternions) : ℍ[ℝ]) =
      (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ o ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        ((formAlongPath β (_root_.YangMills.Construction.BlockAverages.refineSite b.1) (bondContour F.blockSide o π b.2) : imaginaryQuaternions) : ℍ[ℝ]) := by
    simp only [Submodule.coe_smul, AddSubmonoidClass.coe_finset_sum]
  rw [e]
  exact h
private theorem isAnalyticFieldFamily_fieldOfQuaternions {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} [Fintype (F.Site k)] {q : E → F.Site k → Fin 4 → ℍ[ℝ]} {e : E} (h : AnalyticAt ℝ q e)
    (h0 : ∀ x i, q e x i ≠ 0) : IsAnalyticFieldFamily (fun y => fieldOfQuaternions (q y)) e := fun x i =>
  analyticAt_normalize (analyticAt_pi_iff.1 (analyticAt_pi_iff.1 h x) i) (h0 x i)
private theorem isAnalyticFieldFamily_fieldAlongLine {k : ℕ} [Fintype (F.Site k)]
    (η : F.Site k → Fin 4 → imaginaryQuaternions) : IsAnalyticFieldFamily (fieldAlongLine η) (0 : ℝ) := by
  refine isAnalyticFieldFamily_fieldOfQuaternions (q := fun τ x i => 1 + τ • (η x i : ℍ[ℝ])) ?_
    (fun x i => by simp)
  refine AnalyticAt.pi fun x => AnalyticAt.pi fun i => ?_
  exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
private theorem norm_im_sq_imaginary (l : imaginaryQuaternions) : ‖(l : ℍ[ℝ]).im‖ ^ 2 = ‖(l : ℍ[ℝ])‖ ^ 2 := by
  have h := GaugeFixing.re_sq_add_norm_im_sq (l : ℍ[ℝ])
  have h0 : (l : ℍ[ℝ]).re = 0 := l.2
  rw [h0] at h
  simpa using h
private theorem secondDerivZero_blockFit (hL : Odd F.blockSide) {j : ℕ} [Fintype (F.Site j)]
    [Fintype (F.Site (j + 1))] (η : F.Site j → Fin 4 → imaginaryQuaternions)
    (β : F.Site (j + 1) → Fin 4 → imaginaryQuaternions) (c : F.Site (j + 1) × Fin 4) :
    secondDerivZero (fun τ => blockFit (fieldAlongLine η τ) (fieldAlongLine β τ) c) =
      ‖((averageForm η c - β c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2 := by
  have c1 := isCurveThroughTrivial_fieldAlongLine (F := F) η
  have c2 := isCurveThroughTrivial_fieldAlongLine (F := F) β
  have hM := hasDerivAt_contourAverage c1 c
  have hV : HasDerivAt (fun τ => (((fieldAlongLine β τ c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]))
      (-(β c.1 c.2 : ℍ[ℝ])) 0 := by
    have h1 := quatStarCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (c2.hasDerivAt c.1 c.2)
    have e : quatStarCLM ((β c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) = -(β c.1 c.2 : ℍ[ℝ]) := by
      rw [quatStarCLM_apply, star_coe_imaginary]
    rw [e] at h1
    exact h1
  have hM0 : BlockAverages.contourAverage (fieldAlongLine η 0) c = 1 := by
    rw [c1.at_zero]
    exact contourAverage_trivial hL c
  have hV0 : (((fieldAlongLine β 0 c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [c2.at_zero]
    simp [trivialBlockField]
  have hZ := hM.fun_mul hV
  have hZ' : HasDerivAt (fun τ => BlockAverages.contourAverage (fieldAlongLine η τ) c *
      (((fieldAlongLine β τ c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]))
      ((averageForm η c - β c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) 0 := by
    have e : ((averageForm η c - β c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) =
        (averageForm η c : ℍ[ℝ]) * (((fieldAlongLine β 0 c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
        BlockAverages.contourAverage (fieldAlongLine η 0) c * (-(β c.1 c.2 : ℍ[ℝ])) := by
      rw [hM0, hV0]
      simp [sub_eq_add_neg]
    rw [e]
    exact hZ
  have h1 : BlockAverages.contourAverage (fieldAlongLine η 0) c *
      (((fieldAlongLine β 0 c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [hM0, hV0, one_mul]
  have ea : (fun τ => blockFit (fieldAlongLine η τ) (fieldAlongLine β τ) c) = fun τ =>
      reDefect (BlockAverages.contourAverage (fieldAlongLine η τ) c *
        (((fieldAlongLine β τ c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by
    funext τ
    exact blockFit_eq_reDefect _ _ _
  have ha : AnalyticAt ℝ (fun τ => blockFit (fieldAlongLine η τ) (fieldAlongLine β τ) c) 0 :=
    (isAnalyticFieldFamily_fieldAlongLine η).analyticAt_blockFit (isAnalyticFieldFamily_fieldAlongLine β) c
      (by rw [hM0]; exact one_ne_zero)
  rw [ea] at ha ⊢
  rw [secondDerivZero_reDefect hZ' h1 ha, norm_im_sq_imaginary]
private theorem blockFit_nonneg {j : ℕ} (X : F.GaugeField j) (X' : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) : 0 ≤ blockFit X X' c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.blockFit_nonneg <;> assumption
private theorem blockFit_trivial (hL : Odd F.blockSide) {j : ℕ} (c : F.Site (j + 1) × Fin 4) :
    blockFit (trivialBlockField F j) (trivialBlockField F (j + 1)) c = 0 := by
  rw [blockFit_eq_reDefect, contourAverage_trivial hL]
  simp [reDefect, trivialBlockField]
variable [Fintype (F.Site F.depth)] [Fintype (F.Site F.top)]
private abbrev trivialQuat (F : BlockFrame) (k : ℕ) : F.Site k → Fin 4 → ℍ[ℝ] :=
  quaternionsOfField (trivialBlockField F k)
private theorem trivialQuat_ne_zero (k : ℕ) (x : F.Site k) (i : Fin 4) : trivialQuat F k x i ≠ 0 := by
  simp [quaternionsOfField, trivialBlockField]
private theorem fieldOfQuaternions_trivialQuat (k : ℕ) : fieldOfQuaternions (trivialQuat F k) = trivialBlockField F k :=
  fieldOfQuaternions_quaternionsOfField _
private abbrev TopQuatPair (F : BlockFrame) : Type :=
  (F.Site F.depth → Fin 4 → ℍ[ℝ]) × (F.Site F.top → Fin 4 → ℍ[ℝ])
private abbrev trivialPair (F : BlockFrame) : TopQuatPair F := (trivialQuat F F.depth, trivialQuat F F.top)
private def energyQuat (a : ℝ) (F : BlockFrame) (p : TopQuatPair F) : ℝ :=
  blockEnergy a (finiteCells F) F.depth (fieldOfQuaternions p.1) (fieldOfQuaternions p.2)
private def lowerActionQuat (a : ℝ) (F : BlockFrame) (Y : F.Site F.depth → Fin 4 → ℍ[ℝ]) : ℝ :=
  minimalAction a (finiteCells F) F.depth (fieldOfQuaternions Y)
private def topActionQuat (a : ℝ) (F : BlockFrame) (Z : F.Site F.top → Fin 4 → ℍ[ℝ]) : ℝ :=
  minimalAction a (finiteCells F) F.top (fieldOfQuaternions Z)
private theorem analyticAt_energyQuat {a : ℝ} (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth)) :
    AnalyticAt ℝ (energyQuat a F) (trivialPair F) := by
  have f1 : IsAnalyticFieldFamily (fun p : TopQuatPair F => fieldOfQuaternions p.1) (trivialPair F) :=
    isAnalyticFieldFamily_fieldOfQuaternions analyticAt_fst (trivialQuat_ne_zero _)
  have f2 : IsAnalyticFieldFamily (fun p : TopQuatPair F => fieldOfQuaternions p.2) (trivialPair F) :=
    isAnalyticFieldFamily_fieldOfQuaternions analyticAt_snd (trivialQuat_ne_zero _)
  have h1 : AnalyticAt ℝ (fun p : TopQuatPair F => minimalAction a (finiteCells F) F.depth (fieldOfQuaternions p.1))
      (trivialPair F) :=
    AnalyticAt.comp (g := fun Y => minimalAction a (finiteCells F) F.depth (fieldOfQuaternions Y))
      (f := fun p : TopQuatPair F => p.1) hA.analyticAt_trivial analyticAt_fst
  have h2 : AnalyticAt ℝ (fun p : TopQuatPair F => ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1),
      blockFit (fieldOfQuaternions p.1) (fieldOfQuaternions p.2) c) (trivialPair F) :=
    Finset.analyticAt_fun_sum _ fun c _ => f1.analyticAt_blockFit f2 c (by
      rw [show fieldOfQuaternions (trivialPair F).1 = trivialBlockField F F.depth from
        fieldOfQuaternions_trivialQuat _, contourAverage_trivial hL]
      exact one_ne_zero)
  exact h1.add (analyticAt_const.mul h2)
private theorem energyQuat_nonneg {a : ℝ} (ha : 0 < a)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth))
    (p : TopQuatPair F) : 0 ≤ energyQuat a F p :=
  add_nonneg (hA.nonneg _) (mul_nonneg ha.le (Finset.sum_nonneg fun c _ => blockFit_nonneg _ _ _))
private theorem energyQuat_trivial {a : ℝ} (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth)) :
    energyQuat a F (trivialPair F) = 0 := by
  unfold energyQuat blockEnergy
  rw [show fieldOfQuaternions (trivialPair F).1 = trivialBlockField F F.depth from fieldOfQuaternions_trivialQuat _,
    show fieldOfQuaternions (trivialPair F).2 = trivialBlockField F (F.depth + 1) from
      fieldOfQuaternions_trivialQuat _, hA.trivial_eq_zero]
  simp [blockFit_trivial hL]
private theorem fderiv_energyQuat_trivial {a : ℝ} (ha : 0 < a) (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth)) :
    fderiv ℝ (energyQuat a F) (trivialPair F) = 0 :=
  IsLocalMin.fderiv_eq_zero (Eventually.of_forall fun p => by
    rw [energyQuat_trivial hL hA]
    exact energyQuat_nonneg ha hA p)
private theorem fderiv_lowerActionQuat_trivial {a : ℝ}
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth)) :
    fderiv ℝ (lowerActionQuat a F) (trivialQuat F F.depth) = 0 :=
  IsLocalMin.fderiv_eq_zero (Eventually.of_forall fun p => by
    show minimalAction a (finiteCells F) F.depth (fieldOfQuaternions (trivialQuat F F.depth)) ≤
      minimalAction a (finiteCells F) F.depth (fieldOfQuaternions p)
    rw [fieldOfQuaternions_trivialQuat, hA.trivial_eq_zero]
    exact hA.nonneg _)
private theorem fderiv_topActionQuat_trivial {a : ℝ}
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.top) (minimalAction a (finiteCells F) F.top)) :
    fderiv ℝ (topActionQuat a F) (trivialQuat F F.top) = 0 :=
  IsLocalMin.fderiv_eq_zero (Eventually.of_forall fun p => by
    show minimalAction a (finiteCells F) F.top (fieldOfQuaternions (trivialQuat F F.top)) ≤
      minimalAction a (finiteCells F) F.top (fieldOfQuaternions p)
    rw [fieldOfQuaternions_trivialQuat, hA.trivial_eq_zero]
    exact hA.nonneg _)
private theorem fieldOfQuaternions_line {k : ℕ} (η : F.Site k → Fin 4 → imaginaryQuaternions) (τ : ℝ) :
    fieldOfQuaternions (trivialQuat F k + τ • toQuatForm η) = fieldAlongLine η τ := by
  funext x i
  simp [fieldOfQuaternions, fieldAlongLine, quaternionsOfField, trivialBlockField, toQuatForm]
private theorem hessian_energyQuat_diag {a : ℝ} (ha : 0 < a) (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth))
    (η : F.Site F.depth → Fin 4 → imaginaryQuaternions) (β : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    fderiv ℝ (fderiv ℝ (energyQuat a F)) (trivialPair F) (toQuatForm η, toQuatForm β) (toQuatForm η, toQuatForm β) =
      fderiv ℝ (fderiv ℝ (lowerActionQuat a F)) (trivialQuat F F.depth) (toQuatForm η) (toQuatForm η) +
        a * ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1),
          ‖((averageForm η c - β c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ^ 2 := by
  have hΦ := analyticAt_energyQuat hL hA
  have hB : AnalyticAt ℝ (lowerActionQuat a F) (trivialQuat F F.depth) := hA.analyticAt_trivial
  set u : TopQuatPair F := (toQuatForm η, toQuatForm β) with hu
  have g1 : AnalyticAt ℝ (fun τ : ℝ => trivialPair F + τ • u) 0 :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have g2 : AnalyticAt ℝ (fun τ : ℝ => trivialQuat F F.depth + τ • toQuatForm η) 0 :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have d1 : deriv (fun τ : ℝ => trivialPair F + τ • u) 0 = u := by
    have h : HasDerivAt (fun τ : ℝ => trivialPair F + τ • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add (trivialPair F)
    exact h.deriv
  have d2 : deriv (fun τ : ℝ => trivialQuat F F.depth + τ • toQuatForm η) 0 = toQuatForm η := by
    have h : HasDerivAt (fun τ : ℝ => trivialQuat F F.depth + τ • toQuatForm η) (toQuatForm η) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (toQuatForm η)).const_add (trivialQuat F F.depth)
    exact h.deriv
  have s1 := secondDerivZero_comp hΦ (fderiv_energyQuat_trivial ha hL hA) g1 (by simp)
  have s2 := secondDerivZero_comp hB (fderiv_lowerActionQuat_trivial hA) g2 (by simp)
  rw [d1] at s1
  rw [d2] at s2
  rw [← s1, ← s2]
  have e : (fun τ : ℝ => energyQuat a F (trivialPair F + τ • u)) = fun τ =>
      lowerActionQuat a F (trivialQuat F F.depth + τ • toQuatForm η) +
        a * ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1),
          blockFit (fieldAlongLine η τ) (fieldAlongLine β τ) c := by
    funext τ
    have e1 : (trivialPair F + τ • u).1 = trivialQuat F F.depth + τ • toQuatForm η := rfl
    have e2 : (trivialPair F + τ • u).2 = trivialQuat F F.top + τ • toQuatForm β := rfl
    unfold energyQuat blockEnergy lowerActionQuat
    rw [e1, e2, fieldOfQuaternions_line, fieldOfQuaternions_line]
  have a1 : AnalyticAt ℝ (fun τ : ℝ => lowerActionQuat a F (trivialQuat F F.depth + τ • toQuatForm η)) 0 :=
    AnalyticAt.comp (g := lowerActionQuat a F) (f := fun τ : ℝ => trivialQuat F F.depth + τ • toQuatForm η)
      (by simpa using hB) g2
  have a2 : ∀ c ∈ innerBonds (finiteCells F) (F.depth + 1),
      AnalyticAt ℝ (fun τ => blockFit (fieldAlongLine η τ) (fieldAlongLine β τ) c) 0 := fun c _ =>
    (isAnalyticFieldFamily_fieldAlongLine η).analyticAt_blockFit (isAnalyticFieldFamily_fieldAlongLine β) c (by
      rw [(isCurveThroughTrivial_fieldAlongLine (F := F) η).at_zero, contourAverage_trivial hL]
      exact one_ne_zero)
  have a3 := Finset.analyticAt_fun_sum _ a2
  have a4 : AnalyticAt ℝ (fun τ => a * ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1),
      blockFit (fieldAlongLine η τ) (fieldAlongLine β τ) c) 0 :=
    analyticAt_const.mul a3
  rw [e, secondDerivZero_add a1 a4, secondDerivZero_const_mul a a3, secondDerivZero_sum _ _ a2]
  congr 2
  exact Finset.sum_congr rfl fun c _ => secondDerivZero_blockFit hL η β c
private theorem hessian_energyQuat {a : ℝ} (ha : 0 < a) (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth))
    (η η' : F.Site F.depth → Fin 4 → imaginaryQuaternions) (β β' : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    fderiv ℝ (fderiv ℝ (energyQuat a F)) (trivialPair F) (toQuatForm η, toQuatForm β) (toQuatForm η', toQuatForm β') =
      fderiv ℝ (fderiv ℝ (lowerActionQuat a F)) (trivialQuat F F.depth) (toQuatForm η) (toQuatForm η') +
        a * ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1),
          inner ℝ ((averageForm η c - β c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])
            ((averageForm η' c - β' c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) := by
  have hΦ := analyticAt_energyQuat hL hA
  have hB : AnalyticAt ℝ (lowerActionQuat a F) (trivialQuat F F.depth) := hA.analyticAt_trivial
  have sΦ : ∀ u v, fderiv ℝ (fderiv ℝ (energyQuat a F)) (trivialPair F) u v =
      fderiv ℝ (fderiv ℝ (energyQuat a F)) (trivialPair F) v u :=
    fun u v => (hΦ.contDiffAt (n := 2)).isSymmSndFDerivAt (by simp) u v
  have sB : ∀ u v, fderiv ℝ (fderiv ℝ (lowerActionQuat a F)) (trivialQuat F F.depth) u v =
      fderiv ℝ (fderiv ℝ (lowerActionQuat a F)) (trivialQuat F F.depth) v u :=
    fun u v => (hB.contDiffAt (n := 2)).isSymmSndFDerivAt (by simp) u v
  have e1 : ((toQuatForm η, toQuatForm β) + (toQuatForm η', toQuatForm β') : TopQuatPair F) =
      (toQuatForm (η + η'), toQuatForm (β + β')) := by
    rw [toQuatForm_add, toQuatForm_add]
    rfl
  rw [bilin_eq_polar sΦ, bilin_eq_polar sB (toQuatForm η), e1, hessian_energyQuat_diag ha hL hA,
    hessian_energyQuat_diag ha hL hA, hessian_energyQuat_diag ha hL hA, ← toQuatForm_add]
  have e2 : ∀ c : F.Site (F.depth + 1) × Fin 4,
      ((averageForm (η + η') c - (β + β') c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) =
      ((averageForm η c - β c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) +
        ((averageForm η' c - β' c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ]) := by
    intro c
    rw [averageForm_add]
    simp only [Pi.add_apply, Submodule.coe_sub, Submodule.coe_add]
    abel
  simp only [e2, norm_add_sq_real, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
private theorem hasDerivAt_along_line {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {g : E → G} {q : E} (h : DifferentiableAt ℝ g q) (B : E) :
    HasDerivAt (fun τ : ℝ => g (q + τ • B)) (fderiv ℝ g q B) 0 := by
  have hl : HasDerivAt (fun τ : ℝ => q + τ • B) B 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const B).const_add q
  have h3 : HasFDerivAt g (fderiv ℝ g q) (q + (0 : ℝ) • B) := by
    simpa using h.hasFDerivAt
  exact h3.comp_hasDerivAt 0 hl
private def minimizerBranch (x : (F.Site F.top → Fin 4 → ℍ[ℝ]) → StepVariable (finiteCells F))
    (Z : F.Site F.top → Fin 4 → ℍ[ℝ]) : F.Site F.depth → Fin 4 → ℍ[ℝ] :=
  quaternionsOfField (chartedField (stepCoordinates (x Z)) (fieldOfQuaternions Z))
private structure IsMinimizerBranch (a : ℝ) (F : BlockFrame) [Fintype (F.Site F.depth)] [Fintype (F.Site F.top)]
    (x : (F.Site F.top → Fin 4 → ℍ[ℝ]) → StepVariable (finiteCells F)) : Prop where
  pos : 0 < a
  odd : Odd F.blockSide
  extent_ge : ∀ i, 2 ≤ F.extent i
  lower : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth)
  upper : IsNondegenerateAtTrivial (F := F) (k := F.top) (minimalAction a (finiteCells F) F.top)
  analyticAt : AnalyticAt ℝ x (trivialQuat F F.top)
  at_trivial : x (trivialQuat F F.top) = 0
  minimizing : ∀ᶠ Y in 𝓝 (trivialQuat F F.top),
    (∀ W', blockEnergy a (finiteCells F) F.depth (chartedField (stepCoordinates (x Y)) (fieldOfQuaternions Y))
        (fieldOfQuaternions Y) ≤ blockEnergy a (finiteCells F) F.depth W' (fieldOfQuaternions Y)) ∧
    (∀ W', (∀ W'', blockEnergy a (finiteCells F) F.depth W' (fieldOfQuaternions Y) ≤
        blockEnergy a (finiteCells F) F.depth W'' (fieldOfQuaternions Y)) →
      ∃ γ : F.Site F.depth → UnitQuaternion, (∀ z, γ (cellCentre F.depth z) = 1) ∧
        W' = _root_.YangMills.Construction.BlockAverages.gaugeTransform γ (chartedField (stepCoordinates (x Y)) (fieldOfQuaternions Y)))
variable {a : ℝ} {x : (F.Site F.top → Fin 4 → ℍ[ℝ]) → StepVariable (finiteCells F)}
private theorem analyticAt_minimizerBranch (hb : IsMinimizerBranch a F x) :
    AnalyticAt ℝ (minimizerBranch x) (trivialQuat F F.top) := by
  have hΦ : IsAnalyticFieldFamily (fun Y => chartedField (stepCoordinates (x Y)) (fieldOfQuaternions Y))
      (trivialQuat F F.top) :=
    isAnalyticFieldFamily_chartedField
      (fun y i => analyticAt_coe_imaginary (analyticAt_stepCoordinates hb.analyticAt y i))
      (isAnalyticFieldFamily_fieldOfQuaternions analyticAt_id (trivialQuat_ne_zero _))
  exact AnalyticAt.pi fun y => AnalyticAt.pi fun i => hΦ y i
private theorem minimizerBranch_trivial (hb : IsMinimizerBranch a F x) :
    minimizerBranch x (trivialQuat F F.top) = trivialQuat F F.depth := by
  unfold minimizerBranch
  rw [hb.at_trivial, stepCoordinates_zero, fieldOfQuaternions_trivialQuat, chartedField_zero_trivial]
private def branchPair (x : (F.Site F.top → Fin 4 → ℍ[ℝ]) → StepVariable (finiteCells F))
    (Z : F.Site F.top → Fin 4 → ℍ[ℝ]) : TopQuatPair F := (minimizerBranch x Z, Z)
private theorem analyticAt_branchPair (hb : IsMinimizerBranch a F x) :
    AnalyticAt ℝ (branchPair x) (trivialQuat F F.top) :=
  (analyticAt_minimizerBranch hb).prod analyticAt_id
private theorem branchPair_trivial (hb : IsMinimizerBranch a F x) :
    branchPair x (trivialQuat F F.top) = trivialPair F :=
  Prod.ext (minimizerBranch_trivial hb) rfl
private theorem fderiv_branchPair (hb : IsMinimizerBranch a F x) (B : F.Site F.top → Fin 4 → ℍ[ℝ]) :
    fderiv ℝ (branchPair x) (trivialQuat F F.top) B =
      (fderiv ℝ (minimizerBranch x) (trivialQuat F F.top) B, B) := by
  have h := (analyticAt_minimizerBranch hb).differentiableAt.hasFDerivAt.prodMk
    (hasFDerivAt_id (trivialQuat F F.top))
  have e : fderiv ℝ (branchPair x) (trivialQuat F F.top) = _ := h.fderiv
  rw [e]
  rfl
private theorem branchPair_isMin (hb : IsMinimizerBranch a F x) :
    ∀ᶠ Z in 𝓝 (trivialQuat F F.top), ∀ Y,
      energyQuat a F (branchPair x Z) ≤ energyQuat a F (Y, (branchPair x Z).2) := by
  filter_upwards [hb.minimizing] with Z hZ Y
  have h := hZ.1 (fieldOfQuaternions Y)
  simpa only [energyQuat, branchPair, minimizerBranch, fieldOfQuaternions_quaternionsOfField] using h
private theorem hessian_branch_weak (hb : IsMinimizerBranch a F x) (B : F.Site F.top → Fin 4 → ℍ[ℝ])
    (ζ : F.Site F.depth → Fin 4 → ℍ[ℝ]) :
    fderiv ℝ (fderiv ℝ (energyQuat a F)) (trivialPair F)
      (fderiv ℝ (minimizerBranch x) (trivialQuat F F.top) B, B) (ζ, 0) = 0 := by
  have h := hessian_weak_of_local_min (analyticAt_energyQuat hb.odd hb.lower) (analyticAt_branchPair hb)
    (branchPair_trivial hb) (branchPair_isMin hb) ζ B
  rwa [fderiv_branchPair hb] at h
private theorem topActionQuat_eventuallyEq (hb : IsMinimizerBranch a F x) :
    topActionQuat a F =ᶠ[𝓝 (trivialQuat F F.top)] energyQuat a F ∘ branchPair x := by
  filter_upwards [hb.minimizing] with Z hZ
  have hbd : BddBelow (Set.range fun W' : F.GaugeField F.depth =>
      blockEnergy a (finiteCells F) F.depth W' (fieldOfQuaternions Z)) :=
    ⟨0, by
      rintro _ ⟨W', rfl⟩
      exact add_nonneg (hb.lower.nonneg _)
        (mul_nonneg hb.pos.le (Finset.sum_nonneg fun c _ => blockFit_nonneg _ _ _))⟩
  have e : topActionQuat a F Z =
      ⨅ W' : F.GaugeField F.depth, blockEnergy a (finiteCells F) F.depth W' (fieldOfQuaternions Z) := rfl
  rw [e, Function.comp_apply]
  simp only [energyQuat, branchPair, minimizerBranch, fieldOfQuaternions_quaternionsOfField]
  exact le_antisymm (ciInf_le hbd _) (le_ciInf hZ.1)
private theorem hessian_topActionQuat (hb : IsMinimizerBranch a F x) (B B' : F.Site F.top → Fin 4 → ℍ[ℝ]) :
    fderiv ℝ (fderiv ℝ (topActionQuat a F)) (trivialQuat F F.top) B B' =
      fderiv ℝ (fderiv ℝ (energyQuat a F)) (trivialPair F)
        (fderiv ℝ (minimizerBranch x) (trivialQuat F F.top) B, B)
        (fderiv ℝ (minimizerBranch x) (trivialQuat F F.top) B', B') := by
  have e := ((topActionQuat_eventuallyEq hb).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  have hΦ : AnalyticAt ℝ (energyQuat a F) (branchPair x (trivialQuat F F.top)) := by
    rw [branchPair_trivial hb]
    exact analyticAt_energyQuat hb.odd hb.lower
  have hc : fderiv ℝ (energyQuat a F) (branchPair x (trivialQuat F F.top)) = 0 := by
    rw [branchPair_trivial hb]
    exact fderiv_energyQuat_trivial hb.pos hb.odd hb.lower
  rw [e, fderiv_fderiv_comp_of_critical hΦ (analyticAt_branchPair hb) hc, fderiv_branchPair hb,
    fderiv_branchPair hb, branchPair_trivial hb]
private theorem minimizerBranch_re_le_one (Z : F.Site F.top → Fin 4 → ℍ[ℝ]) (y : F.Site F.depth) (i : Fin 4) :
    (minimizerBranch x Z y i).re ≤ 1 := by
  have h := quat_re_le_norm (minimizerBranch x Z y i)
  rwa [show ‖minimizerBranch x Z y i‖ = 1 from norm_coe_unitQuaternion _] at h
private theorem fderiv_minimizerBranch_re (hb : IsMinimizerBranch a F x) (B : F.Site F.top → Fin 4 → ℍ[ℝ])
    (y : F.Site F.depth) (i : Fin 4) : (fderiv ℝ (minimizerBranch x) (trivialQuat F F.top) B y i).re = 0 := by
  have hd := hasDerivAt_along_line (analyticAt_minimizerBranch hb).differentiableAt B
  have h1 := hasDerivAt_pi.1 (hasDerivAt_pi.1 hd y) i
  have h2 := quatReCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  refine IsLocalMax.hasDerivAt_eq_zero (Eventually.of_forall fun τ => ?_) h2
  have e : (quatReCLM ∘ fun τ : ℝ => minimizerBranch x (trivialQuat F F.top + τ • B) y i) 0 = 1 := by
    simp [minimizerBranch_trivial hb, quaternionsOfField, trivialBlockField,
      (show quatReCLM (1 : ℍ[ℝ]) = 1 from rfl)]
  rw [e]
  exact minimizerBranch_re_le_one _ y i
private theorem fderiv_minimizerBranch_tree (hb : IsMinimizerBranch a F x) (B : F.Site F.top → Fin 4 → ℍ[ℝ])
    {y : F.Site F.depth} {i : Fin 4} (ht : IsAxialTreeBond (y, i)) :
    fderiv ℝ (minimizerBranch x) (trivialQuat F F.top) B y i = 0 := by
  have hd := hasDerivAt_along_line (analyticAt_minimizerBranch hb).differentiableAt B
  have h1 := hasDerivAt_pi.1 (hasDerivAt_pi.1 hd y) i
  have e : (fun τ : ℝ => minimizerBranch x (trivialQuat F F.top + τ • B) y i) = fun _ => 1 := by
    funext τ
    unfold minimizerBranch quaternionsOfField
    rw [chartedField_tree _ _ (y, i) ht]
    rfl
  rw [e] at h1
  exact h1.unique (hasDerivAt_const _ _)
private theorem fieldAboveFrame_eventually_eq (hb : IsMinimizerBranch a F x) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    ∀ᶠ Z in 𝓝 (trivialQuat F F.top),
      quaternionsOfField (fieldAboveFrame (F := F) true a ρ 0 (fieldOfQuaternions Z) 0) = minimizerBranch x Z := by
  have hsmall : ∀ᶠ Y in 𝓝 (trivialQuat F F.top), ‖x Y‖ < ρ := by
    have ht : Tendsto (fun Y => ‖x Y‖) (𝓝 (trivialQuat F F.top)) (𝓝 0) := by
      have h := hb.analyticAt.continuousAt.tendsto.norm
      simpa [hb.at_trivial] using h
    exact ht.eventually (gt_mem_nhds h0)
  filter_upwards [hb.minimizing, hsmall] with Z hZ hz
  have h := (stepCoordinates_isMinimizing hb.extent_ge hb.odd h1 hz.le hZ.1 hZ.2).2
  unfold minimizerBranch
  rw [fieldAboveFrame_zero, h]
end Energy
section Torus
variable {F : BlockFrame}
private def formAtLevel {N : ℕ} (j : ℕ) (β : TorusBond N → imaginaryQuaternions) :
    F.Site j → Fin 4 → imaginaryQuaternions := fun x i => β (toTorusSite N x, i)
private def torusQuat (F : BlockFrame) (j : ℕ) {N : ℕ} (W : TorusField N) : F.Site j → Fin 4 → ℍ[ℝ] :=
  quaternionsOfField (readAtLevel F j W)
private theorem fieldOfQuaternions_torusQuat (j : ℕ) {N : ℕ} (W : TorusField N) :
    fieldOfQuaternions (torusQuat F j W) = readAtLevel F j W :=
  fieldOfQuaternions_quaternionsOfField _
private def perturbForm {N k : ℕ} (c : Fin k → TorusBond N) (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (b : TorusBond N) : imaginaryQuaternions :=
  ∑ l, if c l = b then σ l • X l else 0
private def singleBondForm {N : ℕ} (c : TorusBond N) (X : imaginaryQuaternions) (b : TorusBond N) :
    imaginaryQuaternions := if c = b then X else 0
private theorem perturbForm_smul {N k : ℕ} (c : Fin k → TorusBond N) (X : Fin k → imaginaryQuaternions) (τ : ℝ)
    (v : Fin k → ℝ) (b : TorusBond N) : perturbForm c X (τ • v) b = τ • perturbForm c X v b := by
  unfold perturbForm
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · simp [smul_smul]
  · simp
private theorem perturbForm_pair {N : ℕ} (c c' : TorusBond N) (X X' : imaginaryQuaternions) (l : Fin 2) :
    perturbForm ![c, c'] ![X, X'] (Pi.single l 1) = singleBondForm (![c, c'] l) (![X, X'] l) := by
  funext b
  unfold perturbForm singleBondForm
  fin_cases l <;> simp [Fin.sum_univ_two, Pi.single_apply] <;> congr
private theorem perturbForm_one {N : ℕ} (c : TorusBond N) (X : imaginaryQuaternions) :
    perturbForm ![c] ![X] ![1] = singleBondForm c X := by
  funext b
  unfold perturbForm singleBondForm
  simp
private theorem perturb_zero_eq {N k : ℕ} (c : Fin k → TorusBond N) (X : Fin k → imaginaryQuaternions)
    (W : TorusField N) : perturb c X 0 W = W := by apply _root_.YangMills.Construction.TorusFields.perturb_zero <;> assumption
private theorem torusQuat_perturb {N k : ℕ} (j : ℕ) (c : Fin k → TorusBond N) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (y : F.Site j) (i : Fin 4) : torusQuat F j (perturb c X σ (trivialField N)) y i =
      NormedSpace.exp ((perturbForm c X σ (toTorusSite N y, i) : imaginaryQuaternions) : ℍ[ℝ]) := by
  show ((expUnit (perturbForm c X σ (toTorusSite N y, i)) * (1 : UnitQuaternion) : UnitQuaternion) : ℍ[ℝ]) = _
  rw [mul_one]
  rfl
private theorem analyticAt_torusQuat_perturb {N k : ℕ} (j : ℕ) [Fintype (F.Site j)] (c : Fin k → TorusBond N)
    (X : Fin k → imaginaryQuaternions) :
    AnalyticAt ℝ (fun σ : Fin k → ℝ => torusQuat F j (perturb c X σ (trivialField N))) 0 := by
  refine AnalyticAt.pi fun y => AnalyticAt.pi fun i => ?_
  have hs : AnalyticAt ℝ (fun σ : Fin k → ℝ => perturbForm c X σ (toTorusSite N y, i)) 0 := by
    unfold perturbForm
    refine Finset.analyticAt_fun_sum _ fun l _ => ?_
    by_cases h : c l = (toTorusSite N y, i)
    · simp only [h, if_true]
      have hp : AnalyticAt ℝ (fun σ : Fin k → ℝ => σ l) 0 :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l).analyticAt _
      exact hp.smul analyticAt_const
    · simp only [h, if_false]
      exact analyticAt_const
  have h := analyticAt_expUnit (analyticAt_coe_imaginary hs)
  have e : (fun σ : Fin k → ℝ => torusQuat F j (perturb c X σ (trivialField N)) y i) =
      fun σ => ((expUnit (perturbForm c X σ (toTorusSite N y, i)) : UnitQuaternion) : ℍ[ℝ]) := by
    funext σ
    rw [torusQuat_perturb]
    rfl
  rw [e]
  exact h
private theorem torusQuat_perturb_zero {N k : ℕ} (j : ℕ) (c : Fin k → TorusBond N)
    (X : Fin k → imaginaryQuaternions) :
    torusQuat F j (perturb c X (0 : Fin k → ℝ) (trivialField N)) = trivialQuat F j := by
  rw [perturb_zero_eq]
  rfl
private theorem fderiv_torusQuat_perturb {N k : ℕ} (j : ℕ) [Fintype (F.Site j)] (c : Fin k → TorusBond N)
    (X : Fin k → imaginaryQuaternions) (v : Fin k → ℝ) :
    fderiv ℝ (fun σ : Fin k → ℝ => torusQuat F j (perturb c X σ (trivialField N))) 0 v =
      toQuatForm (formAtLevel j (perturbForm c X v)) := by
  have h1 := hasDerivAt_along_line (analyticAt_torusQuat_perturb (F := F) j c X).differentiableAt v
  have h2 : HasDerivAt (fun τ : ℝ => torusQuat F j (perturb c X ((0 : Fin k → ℝ) + τ • v) (trivialField N)))
      (toQuatForm (formAtLevel j (perturbForm c X v))) 0 := by
    refine hasDerivAt_pi.2 fun y => hasDerivAt_pi.2 fun i => ?_
    have e : (fun τ : ℝ => torusQuat F j (perturb c X ((0 : Fin k → ℝ) + τ • v) (trivialField N)) y i) =
        fun τ : ℝ => NormedSpace.exp (τ • ((perturbForm c X v (toTorusSite N y, i) : imaginaryQuaternions) : ℍ[ℝ])) := by
      funext τ
      rw [torusQuat_perturb, zero_add, perturbForm_smul]
      rfl
    rw [e]
    have h3 := hasDerivAt_exp_smul_const (𝕂 := ℝ)
      ((perturbForm c X v (toTorusSite N y, i) : imaginaryQuaternions) : ℍ[ℝ]) (0 : ℝ)
    simpa [toQuatForm, formAtLevel] using h3
  exact h1.unique h2
private theorem pathIntegral_sub_mul {m : ℕ} (ξ η : RealOneForm m) (r : ℝ) (l : List PathStep) :
    ∀ y, pathIntegral (fun b => ξ b - r * η b) y l = pathIntegral ξ y l - r * pathIntegral η y l := by
  induction l with
  | nil => intro y; simp [pathIntegral]
  | cons st s ih =>
    intro y
    obtain ⟨i, u⟩ := st
    cases u <;> simp only [pathIntegral, ih, Bool.false_eq_true, if_false, if_true] <;> ring
private theorem contourAverage_sub_mul {n : ℕ} (L : ℕ) (ξ η : RealOneForm (n * L)) (r : ℝ) (c : TorusBond n) :
    FlatLinearization.contourAverage L (fun b => ξ b - r * η b) c =
      FlatLinearization.contourAverage L ξ c - r * FlatLinearization.contourAverage L η c := by
  unfold FlatLinearization.contourAverage
  simp only [pathIntegral_sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring
variable {n : ℕ} [NeZero n]
private theorem eq_of_weak_equation [NeZero F.blockSide] {a : ℝ}
    {K : TorusBond (n * F.blockSide) → TorusBond (n * F.blockSide) → ℝ}
    {Pn : TorusBond (n * F.blockSide) → TorusBond n → ℝ} (hr : IsMinimizerFamily a F.blockSide K Pn)
    (hpos : IsPositiveOnTreeGauge (n := n) a F.blockSide K) (c : TorusBond n) (r : ℝ)
    (ξ : RealOneForm (n * F.blockSide)) (hξ : VanishesOnBlockTrees F.blockSide ξ)
    (hw : ∀ ζ : RealOneForm (n * F.blockSide), kernelPairing K ξ ζ +
      a * ∑ c', (FlatLinearization.contourAverage F.blockSide ξ c' - r * indicatorForm c c') *
        FlatLinearization.contourAverage F.blockSide ζ c' = 0) :
    ∀ b, ξ b = r * Pn b c := by
  by_contra hne
  have hδ : (fun b => ξ b - r * Pn b c) ≠ 0 := by
    intro h0
    apply hne
    intro b
    have := congrFun h0 b
    simp only [Pi.zero_apply] at this
    linarith
  have hoff : VanishesOnBlockTrees F.blockSide (fun b => ξ b - r * Pn b c) := by
    intro b hb
    simp only [hξ b hb, (hr c).1 b hb, mul_zero, sub_zero]
  have h1 := hpos _ hoff hδ
  have h2 := hw (fun b => ξ b - r * Pn b c)
  have h3 := (hr c).2 _ hoff
  set δ : RealOneForm (n * F.blockSide) := fun b => ξ b - r * Pn b c with hd
  have e1 : kernelPairing K δ δ = kernelPairing K ξ δ - r * kernelPairing K (fun b => Pn b c) δ := by
    unfold kernelPairing
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp only [hd]
    ring
  have e2 : ∑ c', FlatLinearization.contourAverage F.blockSide δ c' ^ 2 =
      ∑ c', (FlatLinearization.contourAverage F.blockSide ξ c' - r * indicatorForm c c') *
          FlatLinearization.contourAverage F.blockSide δ c' -
        r * ∑ c', (FlatLinearization.contourAverage F.blockSide (fun b => Pn b c) c' - indicatorForm c c') *
          FlatLinearization.contourAverage F.blockSide δ c' := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c' _ => ?_
    have e3 : FlatLinearization.contourAverage F.blockSide δ c' =
        FlatLinearization.contourAverage F.blockSide ξ c' -
          r * FlatLinearization.contourAverage F.blockSide (fun b => Pn b c) c' :=
      contourAverage_sub_mul F.blockSide ξ (fun b => Pn b c) r c'
    rw [sq]
    nth_rewrite 1 [e3]
    ring
  rw [e1, e2] at h1
  have e4 : ∀ A B C D : ℝ, A - r * B + a * (C - r * D) = (A + a * C) - r * (B + a * D) := fun _ _ _ _ => by ring
  rw [e4, h2, h3] at h1
  simp at h1
variable [NeZero F.blockSide]
private theorem minimalAction_readAtLevel (hCut : CutActionEqualsMinimalAction) (hAct : ActionAtLevelIsCutAction)
    {a : ℝ} (ha : 0 ≤ a) (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (W : TorusField (n * F.blockSide)) :
    minimalAction a (finiteCells F) F.depth (readAtLevel F F.depth W) =
      actionAtLevel a F.blockSide F.depth Finset.univ W := by
  have hp := TopLevelSites.period_depth_of_extent (F := F) hn
  have hs : ∀ i, 0 < F.extent i := fun i => by rw [hn]; exact Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 := (hAct a ha F.blockSide hL n F rfl hn).2 Finset.univ W
  have h2 := (hCut F a ha).2 hL (finiteCells F) F.depth (Nat.le_succ _) (readAtLevel F F.depth W)
  have e : FrameTransfer.sitesOfTorus F F.depth (Finset.univ : Finset (TorusSite (n * F.blockSide))) =
      sitesOfCells (finiteCells F) F.depth := by
    ext x
    constructor
    · intro _
      exact mem_sitesOfCells_finiteCells hL hs (Nat.le_succ _) x
    · intro _
      exact Finset.mem_image.2 ⟨toTorusSite _ x, Finset.mem_univ _,
        TopLevelSites.torusSiteInFrame_toTorusSite hp x⟩
  rw [e] at h1
  exact h2.symm.trans h1
private theorem minimalAction_top_readAtLevel (hCut : CutActionEqualsMinimalAction)
    (hAct : ActionAtLevelIsCutAction) {a : ℝ} (ha : 0 ≤ a) (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide)
    (V : TorusField n) :
    minimalAction a (finiteCells F) (F.depth + 1) (readAtLevel F F.top V) =
      actionAtLevel a F.blockSide (F.depth + 1) Finset.univ V := by
  have hs : ∀ i, 0 < F.extent i := fun i => by rw [hn]; exact Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 := (hAct a ha F.blockSide hL n F rfl hn).1 Finset.univ V
  have h2 := (hCut F a ha).2 hL (finiteCells F) F.top le_rfl (readAtLevel F F.top V)
  have e : cellsOfSites F (Finset.univ : Finset (TorusSite n)) = sitesOfCells (finiteCells F) F.top := by
    rw [TopLevelSites.cellsOfSites_univ hn]
    ext x
    exact ⟨fun _ => mem_sitesOfCells_finiteCells hL hs le_rfl x, fun _ => TopLevelSites.mem_finiteCells hs x⟩
  rw [e] at h1
  exact h2.symm.trans h1
private theorem minimalActionTotal_eq_lower [Fintype (F.Site F.depth)] (hCut : CutActionEqualsMinimalAction)
    (hAct : ActionAtLevelIsCutAction) {a : ℝ} (ha : 0 ≤ a) (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide)
    (W : TorusField (n * F.blockSide)) :
    minimalActionTotal a F.blockSide F.depth (n * F.blockSide) W = lowerActionQuat a F (torusQuat F F.depth W) := by
  unfold lowerActionQuat minimalActionTotal
  rw [fieldOfQuaternions_torusQuat, dif_neg (NeZero.ne (n * F.blockSide)),
    minimalAction_readAtLevel hCut hAct ha hn hL]
private theorem minimalActionTotal_eq_upper [Fintype (F.Site F.top)] (hCut : CutActionEqualsMinimalAction)
    (hAct : ActionAtLevelIsCutAction) {a : ℝ} (ha : 0 ≤ a) (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide)
    (V : TorusField n) : minimalActionTotal a F.blockSide (F.depth + 1) n V = topActionQuat a F (torusQuat F F.top V) := by
  unfold topActionQuat minimalActionTotal
  rw [fieldOfQuaternions_torusQuat, dif_neg (NeZero.ne n)]
  exact (minimalAction_top_readAtLevel hCut hAct ha hn hL V).symm
section Transport
variable {j N : ℕ} [NeZero N]
private theorem toTorusSite_sub (hp : ∀ i, F.period j i = N) (y y' : F.Site j) :
    toTorusSite N (y - y') = toTorusSite N y - toTorusSite N y' := by
  rw [sub_eq_add_neg, TopLevelSites.toTorusSite_add hp, TopLevelSites.toTorusSite_neg hp, sub_eq_add_neg]
private theorem toTorusSite_step (hp : ∀ i, F.period j i = N) (y : F.Site j) (st : PathStep) :
    toTorusSite N (y + stepDisplacement j st) = stepEndpoint (toTorusSite N y) st := by
  obtain ⟨i, s⟩ := st
  cases s
  · simp only [stepDisplacement, stepEndpoint, Bool.false_eq_true, if_false]
    rw [TopLevelSites.toTorusSite_add hp, TopLevelSites.toTorusSite_neg hp, TopLevelSites.toTorusSite_unitStep hp,
      sub_eq_add_neg]
  · simp only [stepDisplacement, stepEndpoint, if_true]
    rw [TopLevelSites.toTorusSite_add hp, TopLevelSites.toTorusSite_unitStep hp]
private theorem map_formAlongPath (hp : ∀ i, F.period j i = N) (β : TorusBond N → imaginaryQuaternions)
    (ℓ : imaginaryQuaternions →ₗ[ℝ] ℝ) (l : List PathStep) :
    ∀ y : F.Site j, ℓ (formAlongPath (formAtLevel j β) y l) = pathIntegral (fun b => ℓ (β b)) (toTorusSite N y) l := by
  induction l with
  | nil => intro y; simp [formAlongPath, pathIntegral]
  | cons st r ih =>
    intro y
    simp only [formAlongPath, pathIntegral, map_add, ih, toTorusSite_step hp]
    congr 1
    obtain ⟨i, s⟩ := st
    cases s
    · simp [linkForm, formAtLevel, toTorusSite_sub hp, TopLevelSites.toTorusSite_unitStep hp]
    · simp [linkForm, formAtLevel]
private theorem formAlongPath_smul (hp : ∀ i, F.period j i = N) (ξ : TorusBond N → ℝ) (X : imaginaryQuaternions)
    (l : List PathStep) :
    ∀ y : F.Site j, formAlongPath (formAtLevel j fun b => ξ b • X) y l = pathIntegral ξ (toTorusSite N y) l • X := by
  induction l with
  | nil => intro y; simp [formAlongPath, pathIntegral]
  | cons st r ih =>
    intro y
    simp only [formAlongPath, pathIntegral, ih, toTorusSite_step hp, add_smul]
    congr 1
    obtain ⟨i, s⟩ := st
    cases s
    · simp [linkForm, formAtLevel, toTorusSite_sub hp, TopLevelSites.toTorusSite_unitStep hp]
    · simp [linkForm, formAtLevel]
end Transport
private theorem blockCentreSite_eq (Y : TorusSite n) :
    SlopeCoefficient.blockCentreSite F.blockSide Y = TorusBlocks.blockCentreSite F.blockSide Y := by
  funext k
  have h : (((Y k).cast : ℤ)) = ((Y k).val : ℤ) := (ZMod.natCast_val (Y k)).symm
  show (((F.blockSide * (Y k).val : ℕ)) : ZMod (n * F.blockSide)) =
    (((F.blockSide : ℤ) * ((Y k).cast : ℤ) : ℤ) : ZMod (n * F.blockSide))
  rw [h]
  push_cast
  rfl
private theorem map_averageForm (hn : ∀ i, F.extent i = n) (β : TorusBond (n * F.blockSide) → imaginaryQuaternions)
    (ℓ : imaginaryQuaternions →ₗ[ℝ] ℝ) (c : TorusBond n) :
    ℓ (averageForm (formAtLevel F.depth β) (torusSiteInFrame F F.top c.1, c.2)) =
      FlatLinearization.contourAverage F.blockSide (fun b => ℓ (β b)) c := by
  unfold averageForm FlatLinearization.contourAverage
  simp only [map_smul, map_sum, smul_eq_mul, map_formAlongPath (TopLevelSites.period_depth_of_extent hn),
    TorusContours.toTorusSite_refineSite hn, blockCentreSite_eq]
private theorem averageForm_smul (hn : ∀ i, F.extent i = n) (ξ : TorusBond (n * F.blockSide) → ℝ)
    (X : imaginaryQuaternions) (c : TorusBond n) :
    averageForm (formAtLevel F.depth fun b => ξ b • X) (torusSiteInFrame F F.top c.1, c.2) =
      FlatLinearization.contourAverage F.blockSide ξ c • X := by
  unfold averageForm FlatLinearization.contourAverage
  simp only [formAlongPath_smul (TopLevelSites.period_depth_of_extent hn), TorusContours.toTorusSite_refineSite hn,
    blockCentreSite_eq, ← Finset.sum_smul, smul_smul]
private theorem sum_innerBonds_top (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide)
    (g : F.Site (F.depth + 1) × Fin 4 → ℝ) :
    ∑ c ∈ innerBonds (finiteCells F) (F.depth + 1), g c = ∑ c : TorusBond n, g (torusSiteInFrame F F.top c.1, c.2) := by
  have hs : ∀ i, 0 < F.extent i := fun i => by rw [hn]; exact Nat.pos_of_ne_zero (NeZero.ne n)
  have ht := TopLevelSites.period_top_of_extent (F := F) hn
  rw [sum_innerBonds_finiteCells hL hs (k := F.depth + 1) le_rfl, Fintype.sum_prod_type]
  refine Finset.sum_nbij' (toTorusSite n) (torusSiteInFrame F F.top) (fun _ _ => Finset.mem_univ _)
    (fun _ _ => mem_sitesOfCells_finiteCells hL hs le_rfl _)
    (fun y _ => TopLevelSites.torusSiteInFrame_toTorusSite ht y)
    (fun Y _ => TopLevelSites.toTorusSite_torusSiteInFrame ht Y) ?_
  intro y _
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TopLevelSites.torusSiteInFrame_toTorusSite ht y]
private theorem isAxialTreeBond_of_isBlockTreeBond (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide) (h2 : 2 ≤ n)
    {b : TorusBond (n * F.blockSide)} (hb : IsBlockTreeBond F.blockSide b) :
    IsAxialTreeBond (torusSiteInFrame F F.depth b.1, b.2) := by
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; exact h2
  have hp := TopLevelSites.period_depth_of_extent (F := F) hn
  have hnext : torusSiteInFrame F F.depth (b.1 + TorusFields.unitStep (n * F.blockSide) b.2) =
      torusSiteInFrame F F.depth b.1 + BlockAverages.unitStep F.depth b.2 := by
    apply TopLevelSites.toTorusSite_injective hp
    rw [TopLevelSites.toTorusSite_torusSiteInFrame hp, TopLevelSites.toTorusSite_add hp,
      TopLevelSites.toTorusSite_torusSiteInFrame hp, TopLevelSites.toTorusSite_unitStep hp]
  refine ⟨fun hc => ?_, fun l hl => ?_⟩
  · apply hc
    show enclosingCell (torusSiteInFrame F F.depth b.1 + BlockAverages.unitStep F.depth b.2) =
      enclosingCell (torusSiteInFrame F F.depth b.1)
    rw [← hnext, TopLevelSites.enclosingCell_torusSiteInFrame hn, TopLevelSites.enclosingCell_torusSiteInFrame hn]
    have h3 : coarseSite F.blockSide (b.1 + TorusFields.unitStep (n * F.blockSide) b.2) =
        coarseSite F.blockSide b.1 := not_not.1 hb.1
    exact congrArg (torusSiteInFrame F F.top) h3
  · have h0 := hb.2 l hl
    set y := torusSiteInFrame F F.depth b.1 with hy
    set z := cellCentre F.depth (enclosingCell y) with hz
    haveI := TopLevelSites.period_neZero hp l
    have h4 := TorusChain.natAbs_valMinAbs_sub_intCast_cast (hp l) (y l) (z l)
    have e1 : (((y l).cast : ℤ) : ZMod (n * F.blockSide)) = b.1 l :=
      congrFun (TopLevelSites.toTorusSite_torusSiteInFrame hp b.1) l
    have e2 : (((z l).cast : ℤ) : ZMod (n * F.blockSide)) =
        SlopeCoefficient.blockCentreSite F.blockSide (coarseSite F.blockSide b.1) l := by
      have e3 : toTorusSite (n * F.blockSide) z = TorusBlocks.blockCentreSite F.blockSide (parentBlock F.blockSide b.1) := by
        rw [hz, hy, TopLevelSites.enclosingCell_torusSiteInFrame hn, ← TorusContours.toTorusSite_refineSite hn]
        rw [GaugeFixing.refineSite_eq_cellCentre]
      rw [blockCentreSite_eq]
      exact congrFun e3 l
    rw [e1, e2] at h4
    have h5 : ((b.1 - SlopeCoefficient.blockCentreSite F.blockSide (coarseSite F.blockSide b.1)) l).valMinAbs = 0 := h0
    rw [Pi.sub_apply] at h5
    rw [h5] at h4
    have h6 : ((y l - z l).valMinAbs).natAbs = 0 := h4.symm
    exact Int.natAbs_eq_zero.1 h6
variable [Fintype (F.Site F.depth)] [Fintype (F.Site F.top)] {a : ℝ}
private theorem hessian_lower_single (hCut : CutActionEqualsMinimalAction) (hAct : ActionAtLevelIsCutAction)
    (ha : 0 ≤ a) (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth))
    {K : TorusBond (n * F.blockSide) → TorusBond (n * F.blockSide) → ℝ}
    (hK : HasHessianAtTrivial (minimalActionTotal a F.blockSide F.depth) K)
    (c c' : TorusBond (n * F.blockSide)) (X X' : imaginaryQuaternions) :
    fderiv ℝ (fderiv ℝ (lowerActionQuat a F)) (trivialQuat F F.depth)
      (toQuatForm (formAtLevel F.depth (singleBondForm c X)))
      (toQuatForm (formAtLevel F.depth (singleBondForm c' X'))) = inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) * K c c' := by
  rw [← hK.hessian_eq c c' X X']
  unfold SlopeCoefficient.hessianAtTrivial mixedDeriv
  rw [iteratedFDeriv_two_apply]
  set R : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → ℍ[ℝ] :=
    fun σ => torusQuat F F.depth (perturb ![c, c'] ![X, X'] σ (trivialField (n * F.blockSide))) with hR
  have e : (fun σ : Fin 2 → ℝ => minimalActionTotal a F.blockSide F.depth (n * F.blockSide)
      (perturb ![c, c'] ![X, X'] σ (trivialField (n * F.blockSide)))) = lowerActionQuat a F ∘ R := by
    funext σ
    exact minimalActionTotal_eq_lower hCut hAct ha hn hL _
  have h0 : R 0 = trivialQuat F F.depth := torusQuat_perturb_zero _ _ _
  have hf : AnalyticAt ℝ (lowerActionQuat a F) (R 0) := by
    rw [h0]
    exact hA.analyticAt_trivial
  have hc : fderiv ℝ (lowerActionQuat a F) (R 0) = 0 := by
    rw [h0]
    exact fderiv_lowerActionQuat_trivial hA
  rw [e, fderiv_fderiv_comp_of_critical hf (analyticAt_torusQuat_perturb _ _ _) hc, h0]
  have d : ∀ l : Fin 2, fderiv ℝ R 0 (Pi.single l 1) =
      toQuatForm (formAtLevel F.depth (singleBondForm (![c, c'] l) (![X, X'] l))) := by
    intro l
    rw [hR, fderiv_torusQuat_perturb, perturbForm_pair]
  rw [d 0, d 1]
  rfl
private theorem hessian_lower (hCut : CutActionEqualsMinimalAction) (hAct : ActionAtLevelIsCutAction)
    (ha : 0 ≤ a) (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide)
    (hA : IsNondegenerateAtTrivial (F := F) (k := F.depth) (minimalAction a (finiteCells F) F.depth))
    {K : TorusBond (n * F.blockSide) → TorusBond (n * F.blockSide) → ℝ}
    (hK : HasHessianAtTrivial (minimalActionTotal a F.blockSide F.depth) K)
    (β β' : TorusBond (n * F.blockSide) → imaginaryQuaternions) :
    fderiv ℝ (fderiv ℝ (lowerActionQuat a F)) (trivialQuat F F.depth) (toQuatForm (formAtLevel F.depth β))
      (toQuatForm (formAtLevel F.depth β')) =
      ∑ b, ∑ b', K b b' * inner ℝ (β b : ℍ[ℝ]) (β' b' : ℍ[ℝ]) := by
  have e : ∀ γ : TorusBond (n * F.blockSide) → imaginaryQuaternions,
      toQuatForm (formAtLevel (F := F) F.depth γ) = ∑ b, toQuatForm (formAtLevel F.depth (singleBondForm b (γ b))) := by
    intro γ
    funext y i
    simp only [Finset.sum_apply]
    simp only [toQuatForm, formAtLevel, singleBondForm]
    rw [Finset.sum_eq_single (toTorusSite (n * F.blockSide) y, i)]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [e β, e β']
  simp only [map_sum, ContinuousLinearMap.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [hessian_lower_single hCut hAct ha hn hL hA hK, mul_comm]
private def innerWith (e : imaginaryQuaternions) : imaginaryQuaternions →ₗ[ℝ] ℝ where
  toFun y := inner ℝ (y : ℍ[ℝ]) (e : ℍ[ℝ])
  map_add' y y' := by simp [inner_add_left]
  map_smul' r y := by simp [real_inner_smul_left]
private theorem singleBondForm_eq {N : ℕ} (c c' : TorusBond N) (X : imaginaryQuaternions) :
    singleBondForm c X c' = indicatorForm c c' • X := by
  unfold singleBondForm indicatorForm
  by_cases h : c' = c
  · simp [h]
  · have h' : ¬ c = c' := fun e => h e.symm
    simp [h, h']
variable {x : (F.Site F.top → Fin 4 → ℍ[ℝ]) → StepVariable (finiteCells F)}
private theorem weak_equation_real (hCut : CutActionEqualsMinimalAction) (hAct : ActionAtLevelIsCutAction)
    (hn : ∀ i, F.extent i = n) (hb : IsMinimizerBranch a F x)
    {K : TorusBond (n * F.blockSide) → TorusBond (n * F.blockSide) → ℝ}
    (hK : HasHessianAtTrivial (minimalActionTotal a F.blockSide F.depth) K) (c : TorusBond n)
    (X : imaginaryQuaternions) (βt : TorusBond (n * F.blockSide) → imaginaryQuaternions)
    (hβ : fderiv ℝ (minimizerBranch x) (trivialQuat F F.top) (toQuatForm (formAtLevel F.top (singleBondForm c X))) =
      toQuatForm (formAtLevel F.depth βt))
    (e : imaginaryQuaternions) (ζ : RealOneForm (n * F.blockSide)) :
    kernelPairing K (fun b => inner ℝ (βt b : ℍ[ℝ]) (e : ℍ[ℝ])) ζ +
      a * ∑ c', (FlatLinearization.contourAverage F.blockSide (fun b => inner ℝ (βt b : ℍ[ℝ]) (e : ℍ[ℝ])) c' -
        inner ℝ (X : ℍ[ℝ]) (e : ℍ[ℝ]) * indicatorForm c c') * FlatLinearization.contourAverage F.blockSide ζ c' = 0 := by
  have hL := hb.odd
  have z0 : toQuatForm (F := F) (k := F.top) (fun _ _ => (0 : imaginaryQuaternions)) = 0 := by
    funext y i
    simp [toQuatForm]
  have h0 : fderiv ℝ (fderiv ℝ (energyQuat a F)) (trivialPair F)
      (toQuatForm (formAtLevel F.depth βt), toQuatForm (formAtLevel F.top (singleBondForm c X)))
      (toQuatForm (formAtLevel F.depth fun b => ζ b • e), toQuatForm (fun _ _ => (0 : imaginaryQuaternions))) = 0 := by
    have h := hessian_branch_weak hb (toQuatForm (formAtLevel F.top (singleBondForm c X)))
      (toQuatForm (formAtLevel F.depth fun b => ζ b • e))
    rw [hβ] at h
    rw [z0]
    exact h
  rw [hessian_energyQuat hb.pos hL hb.lower, hessian_lower hCut hAct hb.pos.le hn hL hb.lower hK,
    sum_innerBonds_top hn hL] at h0
  refine Eq.trans ?_ h0
  congr 1
  · unfold kernelPairing
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [Submodule.coe_smul, real_inner_smul_right]
    ring
  · congr 1
    refine Finset.sum_congr rfl fun c' _ => ?_
    have m1 := averageForm_smul hn ζ e c'
    have m2 : inner ℝ ((averageForm (formAtLevel F.depth βt) (torusSiteInFrame F F.top c'.1, c'.2) :
        imaginaryQuaternions) : ℍ[ℝ]) (e : ℍ[ℝ]) =
        FlatLinearization.contourAverage F.blockSide (fun b => inner ℝ (βt b : ℍ[ℝ]) (e : ℍ[ℝ])) c' :=
      map_averageForm hn βt (innerWith e) c'
    have m3 : formAtLevel (F := F) F.top (singleBondForm c X) (torusSiteInFrame F F.top c'.1) c'.2 =
        indicatorForm c c' • X := by
      show singleBondForm c X (toTorusSite n (torusSiteInFrame F F.top c'.1), c'.2) = _
      rw [TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn), singleBondForm_eq]
    beta_reduce
    rw [m1, m3, sub_zero, Submodule.coe_smul, real_inner_smul_right, Submodule.coe_sub, inner_sub_left, m2,
      Submodule.coe_smul, real_inner_smul_left]
    ring
private theorem fderiv_minimizerBranch_single (hCut : CutActionEqualsMinimalAction) (hAct : ActionAtLevelIsCutAction)
    (hn : ∀ i, F.extent i = n) (h2 : 2 ≤ n) (hb : IsMinimizerBranch a F x)
    {K : TorusBond (n * F.blockSide) → TorusBond (n * F.blockSide) → ℝ}
    {Pn : TorusBond (n * F.blockSide) → TorusBond n → ℝ}
    (hK : HasHessianAtTrivial (minimalActionTotal a F.blockSide F.depth) K)
    (hr : IsMinimizerFamily a F.blockSide K Pn) (hpos : IsPositiveOnTreeGauge (n := n) a F.blockSide K)
    (c : TorusBond n) (X : imaginaryQuaternions) :
    fderiv ℝ (minimizerBranch x) (trivialQuat F F.top) (toQuatForm (formAtLevel F.top (singleBondForm c X))) =
      toQuatForm (formAtLevel F.depth fun b => Pn b c • X) := by
  have hp := TopLevelSites.period_depth_of_extent (F := F) hn
  let βt : TorusBond (n * F.blockSide) → imaginaryQuaternions := fun b =>
    ⟨fderiv ℝ (minimizerBranch x) (trivialQuat F F.top) (toQuatForm (formAtLevel F.top (singleBondForm c X)))
      (torusSiteInFrame F F.depth b.1) b.2, fderiv_minimizerBranch_re hb _ _ _⟩
  have hβ : fderiv ℝ (minimizerBranch x) (trivialQuat F F.top)
      (toQuatForm (formAtLevel F.top (singleBondForm c X))) = toQuatForm (formAtLevel F.depth βt) := by
    funext y i
    show _ = fderiv ℝ (minimizerBranch x) (trivialQuat F F.top) (toQuatForm (formAtLevel F.top (singleBondForm c X)))
      (torusSiteInFrame F F.depth (toTorusSite (n * F.blockSide) y)) i
    rw [TopLevelSites.torusSiteInFrame_toTorusSite hp y]
  have hoff : ∀ b, IsBlockTreeBond F.blockSide b → βt b = 0 := fun b hb' =>
    Subtype.ext (fderiv_minimizerBranch_tree hb _ (isAxialTreeBond_of_isBlockTreeBond hn hb.odd h2 hb'))
  have key : ∀ (e : imaginaryQuaternions) b,
      inner ℝ (βt b : ℍ[ℝ]) (e : ℍ[ℝ]) = inner ℝ (X : ℍ[ℝ]) (e : ℍ[ℝ]) * Pn b c := by
    intro e
    refine eq_of_weak_equation hr hpos c _ _ ?_ fun ζ => weak_equation_real hCut hAct hn hb hK c X βt hβ e ζ
    intro b hb'
    simp [hoff b hb']
  have hP : βt = fun b : TorusBond (n * F.blockSide) => (Pn b c • X : imaginaryQuaternions) := by
    funext b
    set w : imaginaryQuaternions := βt b - Pn b c • X with hw
    have h3 := key w b
    have e : (w : ℍ[ℝ]) = (βt b : ℍ[ℝ]) - Pn b c • (X : ℍ[ℝ]) := by
      rw [hw]
      rfl
    have h4 : inner ℝ (w : ℍ[ℝ]) (w : ℍ[ℝ]) = 0 := by
      calc inner ℝ (w : ℍ[ℝ]) (w : ℍ[ℝ]) = inner ℝ ((βt b : ℍ[ℝ]) - Pn b c • (X : ℍ[ℝ])) (w : ℍ[ℝ]) := by rw [← e]
        _ = 0 := by
          rw [inner_sub_left, h3, real_inner_smul_left]
          ring
    have h5 : w = 0 := Subtype.ext (inner_self_eq_zero.1 h4)
    exact sub_eq_zero.1 h5
  rw [hβ, hP]
private theorem hessian_upper_single (hCut : CutActionEqualsMinimalAction) (hAct : ActionAtLevelIsCutAction)
    (hn : ∀ i, F.extent i = n) (h2 : 2 ≤ n) (hb : IsMinimizerBranch a F x)
    {K : TorusBond (n * F.blockSide) → TorusBond (n * F.blockSide) → ℝ}
    {Pn : TorusBond (n * F.blockSide) → TorusBond n → ℝ}
    (hK : HasHessianAtTrivial (minimalActionTotal a F.blockSide F.depth) K)
    (hr : IsMinimizerFamily a F.blockSide K Pn) (hpos : IsPositiveOnTreeGauge (n := n) a F.blockSide K)
    (c c' : TorusBond n) (X X' : imaginaryQuaternions) :
    fderiv ℝ (fderiv ℝ (topActionQuat a F)) (trivialQuat F F.top) (toQuatForm (formAtLevel F.top (singleBondForm c X)))
      (toQuatForm (formAtLevel F.top (singleBondForm c' X'))) = inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) *
        (kernelPairing K (fun b => Pn b c) (fun b => Pn b c') +
          a * ∑ c'', (indicatorForm c c'' - FlatLinearization.contourAverage F.blockSide (fun b => Pn b c) c'') *
            (indicatorForm c' c'' - FlatLinearization.contourAverage F.blockSide (fun b => Pn b c') c'')) := by
  have hL := hb.odd
  rw [hessian_topActionQuat hb, fderiv_minimizerBranch_single hCut hAct hn h2 hb hK hr hpos c X,
    fderiv_minimizerBranch_single hCut hAct hn h2 hb hK hr hpos c' X', hessian_energyQuat hb.pos hL hb.lower,
    hessian_lower hCut hAct hb.pos.le hn hL hb.lower hK, sum_innerBonds_top hn hL, mul_add]
  congr 1
  · unfold kernelPairing
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [Submodule.coe_smul, Submodule.coe_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  · rw [mul_left_comm]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c'' _ => ?_
    have m3 : ∀ (d : TorusBond n) (Y : imaginaryQuaternions),
        formAtLevel (F := F) F.top (singleBondForm d Y) (torusSiteInFrame F F.top c''.1) c''.2 =
          indicatorForm d c'' • Y := by
      intro d Y
      show singleBondForm d Y (toTorusSite n (torusSiteInFrame F F.top c''.1), c''.2) = _
      rw [TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn), singleBondForm_eq]
    beta_reduce
    rw [averageForm_smul hn, averageForm_smul hn, m3, m3]
    simp only [Submodule.coe_sub, Submodule.coe_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    ring
private theorem hasHessianAtTrivial_upper (hCut : CutActionEqualsMinimalAction) (hAct : ActionAtLevelIsCutAction)
    (hn : ∀ i, F.extent i = n) (h2 : 2 ≤ n) (hb : IsMinimizerBranch a F x)
    {K : TorusBond (n * F.blockSide) → TorusBond (n * F.blockSide) → ℝ}
    {Pn : TorusBond (n * F.blockSide) → TorusBond n → ℝ}
    (hK : HasHessianAtTrivial (minimalActionTotal a F.blockSide F.depth) K)
    (hr : IsMinimizerFamily a F.blockSide K Pn) (hpos : IsPositiveOnTreeGauge (n := n) a F.blockSide K) :
    HasHessianAtTrivial (minimalActionTotal a F.blockSide (F.depth + 1)) (m := n) (fun c c' =>
      kernelPairing K (fun b => Pn b c) (fun b => Pn b c') +
        a * ∑ c'', (indicatorForm c c'' - FlatLinearization.contourAverage F.blockSide (fun b => Pn b c) c'') *
          (indicatorForm c' c'' - FlatLinearization.contourAverage F.blockSide (fun b => Pn b c') c'')) := by
  have hL := hb.odd
  have hT : AnalyticAt ℝ (topActionQuat a F) (trivialQuat F F.top) := hb.upper.analyticAt_trivial
  have read : ∀ {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      (fun σ : Fin k → ℝ => minimalActionTotal a F.blockSide (F.depth + 1) n (perturb c X σ (trivialField n))) =
        topActionQuat a F ∘ fun σ : Fin k → ℝ => torusQuat F F.top (perturb c X σ (trivialField n)) := by
    intro k c X
    funext σ
    exact minimalActionTotal_eq_upper hCut hAct hb.pos.le hn hL _
  refine ⟨fun r k c X => ?_, fun c c' X X' => ?_⟩
  · rw [read c X]
    have h0 : AnalyticAt ℝ (topActionQuat a F)
        ((fun σ : Fin k → ℝ => torusQuat F F.top (perturb c X σ (trivialField n))) 0) := by
      show AnalyticAt ℝ (topActionQuat a F) (torusQuat F F.top (perturb c X (0 : Fin k → ℝ) (trivialField n)))
      rw [torusQuat_perturb_zero]
      exact hT
    exact (AnalyticAt.comp (g := topActionQuat a F)
      (f := fun σ : Fin k → ℝ => torusQuat F F.top (perturb c X σ (trivialField n))) h0
      (analyticAt_torusQuat_perturb _ c X)).contDiffAt
  · unfold SlopeCoefficient.hessianAtTrivial mixedDeriv
    rw [iteratedFDeriv_two_apply, read ![c, c'] ![X, X']]
    set R : (Fin 2 → ℝ) → F.Site F.top → Fin 4 → ℍ[ℝ] :=
      fun σ => torusQuat F F.top (perturb ![c, c'] ![X, X'] σ (trivialField n)) with hR
    have h0 : R 0 = trivialQuat F F.top := torusQuat_perturb_zero _ _ _
    have hf : AnalyticAt ℝ (topActionQuat a F) (R 0) := by
      rw [h0]
      exact hT
    have hc : fderiv ℝ (topActionQuat a F) (R 0) = 0 := by
      rw [h0]
      exact fderiv_topActionQuat_trivial hb.upper
    rw [fderiv_fderiv_comp_of_critical hf (analyticAt_torusQuat_perturb _ _ _) hc, h0]
    have d : ∀ l : Fin 2, fderiv ℝ R 0 (Pi.single l 1) =
        toQuatForm (formAtLevel F.top (singleBondForm (![c, c'] l) (![X, X'] l))) := by
      intro l
      rw [hR, fderiv_torusQuat_perturb, perturbForm_pair]
    rw [d 0, d 1]
    exact hessian_upper_single hCut hAct hn h2 hb hK hr hpos c c' X X'
private theorem fieldAboveFrame_trivial (hb : IsMinimizerBranch a F x) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1)
    (y : F.Site F.depth) (i : Fin 4) :
    fieldAboveFrame (F := F) true a ρ 0 (readAtLevel F F.top (trivialField n)) 0 y i = 1 := by
  have h := (fieldAboveFrame_eventually_eq hb h0 h1).self_of_nhds
  rw [minimizerBranch_trivial hb, fieldOfQuaternions_trivialQuat] at h
  exact Subtype.ext (congrFun (congrFun h y) i)
private theorem fieldAboveFrame_perturb_eventually (hb : IsMinimizerBranch a F x) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1)
    {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    ∀ᶠ σ in 𝓝 (0 : Fin k → ℝ), ∀ y i,
      ((fieldAboveFrame (F := F) true a ρ 0 (readAtLevel F F.top (perturb c X σ (trivialField n))) 0 y i :
        UnitQuaternion) : ℍ[ℝ]) = minimizerBranch x (torusQuat F F.top (perturb c X σ (trivialField n))) y i := by
  have ht : Tendsto (fun σ : Fin k → ℝ => torusQuat F F.top (perturb c X σ (trivialField n))) (𝓝 0)
      (𝓝 (trivialQuat F F.top)) := by
    have h := (analyticAt_torusQuat_perturb (F := F) F.top c X).continuousAt.tendsto
    rwa [torusQuat_perturb_zero] at h
  filter_upwards [ht.eventually (fieldAboveFrame_eventually_eq hb h0 h1)] with σ hσ y i
  rw [fieldOfQuaternions_torusQuat] at hσ
  exact congrFun (congrFun hσ y) i
private theorem analyticAt_minimizerBranch_perturb (hb : IsMinimizerBranch a F x) {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) :
    AnalyticAt ℝ (fun σ : Fin k → ℝ => minimizerBranch x (torusQuat F F.top (perturb c X σ (trivialField n)))) 0 := by
  have h0 : AnalyticAt ℝ (minimizerBranch x)
      ((fun σ : Fin k → ℝ => torusQuat F F.top (perturb c X σ (trivialField n))) 0) := by
    show AnalyticAt ℝ (minimizerBranch x) (torusQuat F F.top (perturb c X (0 : Fin k → ℝ) (trivialField n)))
    rw [torusQuat_perturb_zero]
    exact analyticAt_minimizerBranch hb
  exact AnalyticAt.comp (g := minimizerBranch x)
    (f := fun σ : Fin k → ℝ => torusQuat F F.top (perturb c X σ (trivialField n))) h0
    (analyticAt_torusQuat_perturb _ c X)
private theorem contDiffAt_fieldAboveFrame (hb : IsMinimizerBranch a F x) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1)
    {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (y : F.Site F.depth) (i : Fin 4) :
    ContDiffAt ℝ 2 (fun σ : Fin k → ℝ =>
      ((fieldAboveFrame (F := F) true a ρ 0 (readAtLevel F F.top (perturb c X σ (trivialField n))) 0 y i :
        UnitQuaternion) : ℍ[ℝ])) 0 := by
  have ha := analyticAt_pi_iff.1 (analyticAt_pi_iff.1 (analyticAt_minimizerBranch_perturb hb c X) y) i
  refine ha.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [fieldAboveFrame_perturb_eventually hb h0 h1 c X] with σ hσ
  exact hσ y i
private theorem hasDerivAt_fieldAboveFrame (hCut : CutActionEqualsMinimalAction) (hAct : ActionAtLevelIsCutAction)
    (hn : ∀ i, F.extent i = n) (h2 : 2 ≤ n) (hb : IsMinimizerBranch a F x)
    {K : TorusBond (n * F.blockSide) → TorusBond (n * F.blockSide) → ℝ}
    {Pn : TorusBond (n * F.blockSide) → TorusBond n → ℝ}
    (hK : HasHessianAtTrivial (minimalActionTotal a F.blockSide F.depth) K)
    (hr : IsMinimizerFamily a F.blockSide K Pn) (hpos : IsPositiveOnTreeGauge (n := n) a F.blockSide K) {ρ : ℝ}
    (h0 : 0 < ρ) (h1 : ρ ≤ 1) (b : TorusBond (n * F.blockSide)) (c : TorusBond n) (X : imaginaryQuaternions) :
    HasDerivAt (fun s : ℝ => ((fieldAboveFrame (F := F) true a ρ 0
      (readAtLevel F F.top (perturb ![c] ![X] ![s] (trivialField n))) 0
      (torusSiteInFrame F F.depth b.1) b.2 : UnitQuaternion) : ℍ[ℝ])) (Pn b c • (X : ℍ[ℝ])) 0 := by
  have hp := TopLevelSites.period_depth_of_extent (F := F) hn
  set R : (Fin 1 → ℝ) → F.Site F.top → Fin 4 → ℍ[ℝ] :=
    fun σ => torusQuat F F.top (perturb ![c] ![X] σ (trivialField n)) with hR
  have hR0 : R 0 = trivialQuat F F.top := torusQuat_perturb_zero _ _ _
  have hB : HasFDerivAt (minimizerBranch x) (fderiv ℝ (minimizerBranch x) (trivialQuat F F.top)) (R 0) := by
    rw [hR0]
    exact (analyticAt_minimizerBranch hb).differentiableAt.hasFDerivAt
  have hg := hB.comp 0 (analyticAt_torusQuat_perturb (F := F) F.top ![c] ![X]).differentiableAt.hasFDerivAt
  have hcv : HasDerivAt (fun s : ℝ => (![s] : Fin 1 → ℝ)) ![1] 0 := by
    refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    exact hasDerivAt_id' (0 : ℝ)
  have hz : (0 : Fin 1 → ℝ) = ![(0 : ℝ)] := by
    funext i
    simp
  have h3 := hg.comp_hasDerivAt_of_eq (0 : ℝ) hcv hz
  have hv : (fderiv ℝ (minimizerBranch x) (trivialQuat F F.top)).comp (fderiv ℝ R 0) ![1] =
      toQuatForm (formAtLevel F.depth fun b => Pn b c • X) := by
    rw [ContinuousLinearMap.comp_apply, hR, fderiv_torusQuat_perturb, perturbForm_one,
      fderiv_minimizerBranch_single hCut hAct hn h2 hb hK hr hpos c X]
  rw [hv] at h3
  have h4 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h3 (torusSiteInFrame F F.depth b.1)) b.2
  have e : (toQuatForm (formAtLevel F.depth fun b => Pn b c • X) (torusSiteInFrame F F.depth b.1) b.2 : ℍ[ℝ]) =
      Pn b c • (X : ℍ[ℝ]) := by
    show ((Pn (toTorusSite (n * F.blockSide) (torusSiteInFrame F F.depth b.1), b.2) c • X :
      imaginaryQuaternions) : ℍ[ℝ]) = _
    rw [TopLevelSites.toTorusSite_torusSiteInFrame hp]
    rfl
  rw [e] at h4
  refine h4.congr_of_eventuallyEq ?_
  have ht : Tendsto (fun s : ℝ => (![s] : Fin 1 → ℝ)) (𝓝 0) (𝓝 0) := by
    have h5 := hcv.continuousAt.tendsto
    rwa [← hz] at h5
  filter_upwards [ht.eventually (fieldAboveFrame_perturb_eventually hb h0 h1 ![c] ![X])] with s hs
  exact hs _ _
end Torus
section Induction
private theorem minimizer_step (hW : WilsonActionNondegenerate) (hX : NondegenerateAcrossFrames)
    (hT : minimalActionNondegeneratePropagatesStatement) (hCut : CutActionEqualsMinimalAction)
    (hAct : ActionAtLevelIsCutAction) {a : ℝ} (ha : 0 < a) {L : ℕ} (hL : Odd L) [NeZero L] {t n : ℕ} [NeZero n]
    (h2 : 2 ≤ n) (K : TorusBond (n * L) → TorusBond (n * L) → ℝ) (Pn : TorusBond (n * L) → TorusBond n → ℝ)
    (hK : HasHessianAtTrivial (minimalActionTotal a L t) K) (hr : IsMinimizerFamily a L K Pn)
    (hpos : IsPositiveOnTreeGauge (n := n) a L K) :
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → minimizerOnFinerTorus a ρ L t n (trivialField n) = trivialField (n * L) ∧
      (∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (b : TorusBond (n * L)),
        ContDiffAt ℝ 2 (fun σ : Fin k → ℝ =>
          ((minimizerOnFinerTorus a ρ L t n (perturb c X σ (trivialField n)) b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) 0) ∧
      ∀ (b : TorusBond (n * L)) (c : TorusBond n) (X : imaginaryQuaternions),
        HasDerivAt (fun s : ℝ =>
          ((minimizerOnFinerTorus a ρ L t n (perturb ![c] ![X] ![s] (trivialField n)) b.1 b.2 :
            UnitQuaternion) : ℍ[ℝ]))
          (Pn b c • (X : ℍ[ℝ])) 0) ∧
    HasHessianAtTrivial (minimalActionTotal a L (t + 1)) (m := n) (fun c c' =>
      kernelPairing K (fun b => Pn b c) (fun b => Pn b c') +
        a * ∑ c'', (indicatorForm c c'' - FlatLinearization.contourAverage L (fun b => Pn b c) c'') *
          (indicatorForm c' c'' - FlatLinearization.contourAverage L (fun b => Pn b c') c'')) := by
  have hLp : 0 < L := hL.pos
  have hpos' : ∀ i : Fin 4, 0 < (torusFrame L t n).extent i := fun _ => by
    show 0 < n
    omega
  letI iT := fintypeSite (torusFrame L t n) hLp hpos' (torusFrame L t n).depth
  letI iN := fintypeSite (torusFrame L t n) hLp hpos' (torusFrame L t n).top
  haveI : NeZero (torusFrame L t n).blockSide := ‹NeZero L›
  obtain ⟨hTop, hC⟩ := hT (torusFrame L t n) a ha hL (fun _ => h2) (nondegenerate_at_depth hW hX hT ha hL t n h2 iT)
  obtain ⟨x, hxa, hx0, hev⟩ := hC
  have hb : IsMinimizerBranch a (torusFrame L t n) x :=
    { pos := ha
      odd := hL
      extent_ge := fun _ => h2
      lower := nondegenerate_at_depth hW hX hT ha hL t n h2 iT
      upper := hTop
      analyticAt := hxa
      at_trivial := hx0
      minimizing := hev.mono fun Y hY => ⟨hY.1, hY.2.1⟩ }
  have hn : ∀ i, (torusFrame L t n).extent i = n := fun _ => rfl
  refine ⟨fun ρ h0 h1 => ⟨?_, fun k c X b => ?_, fun b c X => ?_⟩, ?_⟩
  · funext z i
    exact fieldAboveFrame_trivial hb h0 h1 (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth z) i
  · exact contDiffAt_fieldAboveFrame hb h0 h1 c X (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth b.1) b.2
  · exact hasDerivAt_fieldAboveFrame (F := torusFrame L t n) hCut hAct hn h2 hb hK hr hpos h0 h1 b c X
  · exact hasHessianAtTrivial_upper (F := torusFrame L t n) hCut hAct hn h2 hb hK hr hpos
end Induction
theorem minimizerOverFlatKernel (hW : WilsonActionNondegenerate) (hX : NondegenerateAcrossFrames)
    (hT : minimalActionNondegeneratePropagatesStatement) (hCut : CutActionEqualsMinimalAction)
    (hAct : ActionAtLevelIsCutAction) : MinimizerOverFlatKernel := by
  intro a ha L hLs t h P hf hr
  have hL : Odd L := hLs.1
  have hLp : 0 < L := hL.pos
  haveI : NeZero L := ⟨hLp.ne'⟩
  have hmul : Tendsto (fun n : ℕ => n * L) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hLp) tendsto_id
  have hall := ((hmul.eventually hf).and hr).and (eventually_ge_atTop 2)
  refine ⟨fun ρ h0 h1 => ?_, ?_⟩
  · filter_upwards [hall] with n hn
    obtain ⟨⟨hK, hrn⟩, h2⟩ := hn
    haveI : NeZero n := ⟨by omega⟩
    obtain ⟨r1, r2⟩ := hrn
    exact (minimizer_step hW hX hT hCut hAct ha hL h2 (h (n * L)) (P n) hK r1 r2).1 ρ h0 h1
  · filter_upwards [hall] with n hn
    obtain ⟨⟨hK, hrn⟩, h2⟩ := hn
    have hn0 : n ≠ 0 := by omega
    haveI : NeZero n := ⟨hn0⟩
    obtain ⟨r1, r2⟩ := hrn
    have h3 := (minimizer_step hW hX hT hCut hAct ha hL h2 (h (n * L)) (P n) hK r1 r2).2
    have e : renormalizedKernel a L h P n = fun c c' =>
        kernelPairing (h (n * L)) (fun b => P n b c) (fun b => P n b c') +
          a * ∑ c'', (indicatorForm c c'' - FlatLinearization.contourAverage L (fun b => P n b c) c'') *
            (indicatorForm c' c'' - FlatLinearization.contourAverage L (fun b => P n b c') c'') := by
      funext c c'
      unfold renormalizedKernel
      rw [dif_pos ⟨hn0, hLp.ne'⟩]
    rw [e]
    exact h3
end YangMills.Construction.RunningCouplingSlope
end
