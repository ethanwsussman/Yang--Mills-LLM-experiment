import YangMills.Construction.LawByMomentsOfTheFlow.ExactSquareOfAStep
import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheMaxwellFormProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
noncomputable section
set_option linter.unusedSectionVars false
open scoped Quaternion Topology
open BlockAverages hiding unitStep adjointAction
open ColdStepAtMirrorFrames hiding chartRestriction
open TorusContours hiding contourIndex contourWeight
open LumpContours TorusFields TorusLumps StepSettings StepCosts TopLevelSites TorusBlocks LevelAction RenormalizationStepParameters
  FrameTransfer WeightedResponses ResponseInTheExpansion
open SecondOrder ResponseInTheExpansion.SingleColourFields
namespace MomentLaw
namespace CompletedSquare
section Lines
variable {N : ℕ}
private theorem sumAlongPath_smul (τ : ℝ) (θ : TorusBond N → ℝ) (l : List PathStep) :
    ∀ x, sumAlongPath (τ • θ) x l = τ * sumAlongPath θ x l := by apply _root_.YangMills.SharedProofs.p13483 <;> assumption
private theorem contourSum_smul (L : ℕ) {n : ℕ} (τ : ℝ) (θ : TorusBond N → ℝ) (c : TorusBond n)
    (k : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) :
    contourSum L (τ • θ) c k = τ * contourSum L θ c k := sumAlongPath_smul _ _ _ _
private theorem contourSum_zero (L : ℕ) {n : ℕ} (c : TorusBond n) (k : (Fin 4 → ℤ) × Equiv.Perm (Fin 4)) :
    contourSum L (0 : TorusBond N → ℝ) c k = 0 := by apply _root_.YangMills.SharedProofs.p22967 <;> assumption
private theorem contDiff_sumAlongPath [NeZero N] (l : List PathStep) :
    ∀ x, ContDiff ℝ 2 (fun θ : TorusBond N → ℝ => sumAlongPath θ x l) := by apply _root_.YangMills.SharedProofs.p9311 <;> assumption
end Lines
section Pair
variable {L n : ℕ} [NeZero L] [NeZero n]
private abbrev AnglePair (L n : ℕ) : Type := (TorusBond (n * L) → ℝ) × (TorusBond n → ℝ)
private def pairFit (L : ℕ) (p : AnglePair L n) (c : TorusBond n) : ℝ :=
  Real.sqrt (contourCosMean L p.1 c 1 ^ 2 + contourSinMean L p.1 c 1 ^ 2) -
    (contourCosMean L p.1 c 1 * Real.cos (1 * p.2 c) + contourSinMean L p.1 c 1 * Real.sin (1 * p.2 c))
private theorem secondJet_pairFit (hL : Odd L) (W : TorusBond (n * L) → ℝ) (B : TorusBond n → ℝ) (c : TorusBond n) :
    SecondJet (fun τ : ℝ => pairFit L (τ • ((W, B) : AnglePair L n)) c) 0 0
      ((∑ k ∈ contourIndex L, contourWeight L * contourSum L W c k - B c) ^ 2) := by
  have h := SecondJet.rotationFit (contourIndex L) (fun _ => contourWeight L) (fun k => contourSum L W c k) (B c)
    (sum_contourWeight hL)
  convert h using 1
  funext τ
  simp only [pairFit, contourCosMean, contourSinMean, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
    one_mul, contourSum_smul]
private theorem contDiff_contourCosMean (c : TorusBond n) :
    ContDiff ℝ 2 (fun p : AnglePair L n => contourCosMean L p.1 c 1) := by apply _root_.YangMills.DeltaSharedProofs.p502436 <;> assumption
private theorem contDiff_contourSinMean (c : TorusBond n) :
    ContDiff ℝ 2 (fun p : AnglePair L n => contourSinMean L p.1 c 1) := by apply _root_.YangMills.DeltaSharedProofs.p501378 <;> assumption
private theorem contourCosMean_zero (hL : Odd L) (c : TorusBond n) :
    contourCosMean L (0 : TorusBond (n * L) → ℝ) c 1 = 1 := by apply _root_.YangMills.SharedProofs.p15344 <;> assumption
private theorem contourSinMean_zero (c : TorusBond n) : contourSinMean L (0 : TorusBond (n * L) → ℝ) c 1 = 0 := by
  simp [contourSinMean, contourSum_zero]
private theorem contDiffAt_pairFit (hL : Odd L) (c : TorusBond n) :
    ContDiffAt ℝ 2 (fun p : AnglePair L n => pairFit L p c) 0 := by
  unfold pairFit
  have hC := contDiff_contourCosMean (L := L) c
  have hS := contDiff_contourSinMean (L := L) c
  have h2 : ContDiff ℝ 2 (fun p : AnglePair L n => p.2 c) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : TorusBond n => ℝ) c).contDiff.comp contDiff_snd
  refine ContDiffAt.sub (ContDiffAt.sqrt ?_ ?_) ?_
  · exact ((hC.pow 2).add (hS.pow 2)).contDiffAt
  · have e1 : contourCosMean L (0 : AnglePair L n).1 c 1 = 1 := contourCosMean_zero hL c
    have e2 : contourSinMean L (0 : AnglePair L n).1 c 1 = 0 := contourSinMean_zero c
    rw [e1, e2]
    norm_num
  · exact ((hC.mul (Real.contDiff_cos.comp (contDiff_const.mul h2))).add
      (hS.mul (Real.contDiff_sin.comp (contDiff_const.mul h2)))).contDiffAt
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
variable {a : ℝ} {t : ℕ}
private theorem contDiffAt_pairEnergy (hL : Odd L) {u : ℕ}
    (hA : ContDiffAt ℝ 2 (colourAction a L u (m := n * L)) 0) :
    ContDiffAt ℝ 2 (pairEnergy (n := n) a L u) 0 := by
  unfold pairEnergy
  have h1 : ContDiffAt ℝ 2 (fun p : AnglePair L n => colourAction a L u p.1) 0 :=
    ContDiffAt.comp (0 : AnglePair L n) (g := colourAction a L u (m := n * L)) (f := Prod.fst) hA contDiffAt_fst
  exact h1.add (contDiffAt_const.mul (ContDiffAt.sum fun c _ => contDiffAt_pairFit hL c))
private theorem contDiffAt_colourAction {m : ℕ} [NeZero m]
    (h : ContDiffThreeAt (actionAtLevel a L t Finset.univ) (trivialField m)) :
    ContDiffAt ℝ 2 (colourAction a L t (m := m)) 0 := by apply _root_.YangMills.DeltaSharedProofs.p2351 <;> assumption
private theorem maxwellKernel_eq_hessian {m : ℕ} [NeZero m] (hC : ContDiffAt ℝ 2 (colourAction a L t (m := m)) 0)
    (b b' : TorusBond m) :
    maxwellKernel a L t b b' =
      hessianAtZero (colourAction a L t (m := m)) (Pi.single b 1) (Pi.single b' 1) := by apply _root_.YangMills.DeltaSharedProofs.p502241 <;> assumption
private theorem maxwellForm_eq_hessian {m : ℕ} [NeZero m] (hC : ContDiffAt ℝ 2 (colourAction a L t (m := m)) 0)
    (A A' : TorusBond m → ℝ) :
    maxwellForm a L t A A' = hessianAtZero (colourAction a L t (m := m)) A A' := by apply _root_.YangMills.DeltaSharedProofs.p502089 <;> assumption
end Pair
section Frame
variable {L n u : ℕ} [NeZero L] [NeZero n]
private theorem period_depth (L u n : ℕ) [NeZero L] [NeZero n] (i : Fin 4) :
    (torusFrame L u n).period u i = n * L :=
  period_depth_of_extent (F := torusFrame L u n) (n := n) (fun _ => rfl) i
private theorem period_top (L u n : ℕ) [NeZero L] [NeZero n] (i : Fin 4) :
    (torusFrame L u n).period (u + 1) i = n :=
  period_top_of_extent (F := torusFrame L u n) (n := n) (fun _ => rfl) i
private theorem extent_pos (L u n : ℕ) [NeZero n] (i : Fin 4) : 0 < (torusFrame L u n).extent i :=
  Nat.pos_of_ne_zero (NeZero.ne n)
private theorem minimalAction_readAtLevel {a : ℝ} (h2 : LumpContours.ActionAtLevelIsCutAction)
    (h3 : LumpContours.WholeCellCostEqualsMinimalAction) (ha : 0 ≤ a) (hL : Odd L) (W : TorusField (n * L)) :
    minimalAction a (finiteCells (torusFrame L u n)) u (readAtLevel (torusFrame L u n) u W) =
      actionAtLevel a L u Finset.univ W := by apply _root_.YangMills.SharedProofs.p88272 <;> assumption
private theorem sum_innerBonds (hL : Odd L) (f : (torusFrame L u n).Site (u + 1) × Fin 4 → ℝ) :
    ∑ c ∈ innerBonds (finiteCells (torusFrame L u n)) (u + 1), f c =
      ∑ c : TorusBond n, f (torusSiteInFrame (torusFrame L u n) (u + 1) c.1, c.2) := by apply _root_.YangMills.SharedProofs.p37826 <;> assumption
private theorem blockEnergy_readAtLevel {a : ℝ} (h2 : LumpContours.ActionAtLevelIsCutAction)
    (h3 : LumpContours.WholeCellCostEqualsMinimalAction) (ha : 0 ≤ a) (hL : Odd L) (p : AnglePair L n) :
    blockEnergy a (finiteCells (torusFrame L u n)) u (readAtLevel (torusFrame L u n) u (expOfColourForm 1 p.1))
      (readAtLevel (torusFrame L u n) (u + 1) (expOfColourForm 1 p.2)) = pairEnergy a L u p := by
  unfold blockEnergy pairEnergy colourAction
  rw [minimalAction_readAtLevel h2 h3 ha hL, sum_innerBonds hL]
  congr 2
  refine Finset.sum_congr rfl fun c _ => ?_
  exact SingleColourFields.blockFit_readAtLevel (G := torusFrame L u n) (period_depth L u n) (period_top L u n)
    1 p.1 p.2 c
private theorem blockEnergy_nonneg {a : ℝ} (h3 : LumpContours.WholeCellCostEqualsMinimalAction)
    (h4 : LumpContours.CutActionEqualsMinimalAction) (ha : 0 ≤ a) (hL : Odd L)
    (W : (torusFrame L u n).GaugeField u) (V : (torusFrame L u n).GaugeField (u + 1)) :
    0 ≤ blockEnergy a (finiteCells (torusFrame L u n)) u W V := by apply _root_.YangMills.SharedProofs.p2190 <;> assumption
private theorem pairEnergy_nonneg {a : ℝ} (h2 : LumpContours.ActionAtLevelIsCutAction)
    (h3 : LumpContours.WholeCellCostEqualsMinimalAction) (h4 : LumpContours.CutActionEqualsMinimalAction)
    (ha : 0 ≤ a) (hL : Odd L) (p : AnglePair L n) :
    0 ≤ pairEnergy a L u p := by
  rw [← blockEnergy_readAtLevel h2 h3 ha hL p]
  exact blockEnergy_nonneg h3 h4 ha hL _ _
private theorem expOfColourForm_zero {m : ℕ} (τ : ℝ) : expOfColourForm τ (0 : TorusBond m → ℝ) = trivialField m := by apply _root_.YangMills.SharedProofs.p68982 <;> assumption
private theorem colourAction_zero {a : ℝ} (h2 : LumpContours.ActionAtLevelIsCutAction)
    (h3 : LumpContours.WholeCellCostEqualsMinimalAction) (h5 : flatTopVanishingStatement) (ha : 0 ≤ a) (hL : Odd L) :
    colourAction a L u (0 : TorusBond (n * L) → ℝ) = 0 := by apply _root_.YangMills.DeltaSharedProofs.p501681 <;> assumption
private theorem pairEnergy_zero {a : ℝ} (h2 : LumpContours.ActionAtLevelIsCutAction)
    (h3 : LumpContours.WholeCellCostEqualsMinimalAction) (h5 : flatTopVanishingStatement) (ha : 0 ≤ a) (hL : Odd L) :
    pairEnergy (n := n) a L u 0 = 0 := by
  unfold pairEnergy
  have e1 : colourAction a L u (0 : AnglePair L n).1 = 0 := colourAction_zero h2 h3 h5 ha hL
  rw [e1]
  simp [pairFit_zero hL]
private theorem fderiv_pairEnergy_zero {a : ℝ} (h2 : LumpContours.ActionAtLevelIsCutAction)
    (h3 : LumpContours.WholeCellCostEqualsMinimalAction) (h4 : LumpContours.CutActionEqualsMinimalAction)
    (h5 : flatTopVanishingStatement) (ha : 0 ≤ a) (hL : Odd L) :
    fderiv ℝ (pairEnergy (n := n) a L u) 0 = 0 := by
  have hmin : IsLocalMin (pairEnergy (n := n) a L u) 0 := by
    refine Filter.Eventually.of_forall fun p => ?_
    rw [pairEnergy_zero h2 h3 h5 ha hL]
    exact pairEnergy_nonneg h2 h3 h4 ha hL p
  exact hmin.fderiv_eq_zero
private theorem readAtLevel_top (B : TorusBond n → ℝ) (τ : ℝ) (c : TorusBond n) :
    readAtLevel (torusFrame L u n) (u + 1) (expOfColourForm τ B) (torusSiteInFrame (torusFrame L u n) (u + 1) c.1) c.2 =
      colourRotation (τ * B c) :=
  readAtLevel_torusSiteInFrame (period_top L u n) _ _ _
private theorem expOfColourForm_one_smul {m : ℕ} (τ : ℝ) (B : TorusBond m → ℝ) :
    expOfColourForm 1 (τ • B) = expOfColourForm τ B := by apply _root_.YangMills.SharedProofs.p43028 <;> assumption
private theorem actionAtLevel_succ_eq_blockEnergy {a ρ : ℝ} (h3 : LumpContours.WholeCellCostEqualsMinimalAction)
    (h4 : LumpContours.CutActionEqualsMinimalAction) (ha : 0 ≤ a) (hL : Odd L) {V : TorusField n}
    {w : (torusFrame L u n).Site u → Fin 4 → imaginaryQuaternions}
    (hw : IsMinimizingChart a (finiteCells (torusFrame L u n)) (readAtLevel (torusFrame L u n) (u + 1) V) ρ w) :
    actionAtLevel a L (u + 1) Finset.univ V =
      blockEnergy a (finiteCells (torusFrame L u n)) u (chartedField w (readAtLevel (torusFrame L u n) (u + 1) V))
        (readAtLevel (torusFrame L u n) (u + 1) V) := by apply _root_.YangMills.SharedProofs.p39726 <;> assumption
end Frame
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
private theorem adjointAction_piRotation_imJ_imK (w : imaginaryQuaternions) :
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
private theorem eq_imI_smul_of_fixed (w : imaginaryQuaternions) (h : _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction halfRotation w = w) :
    w = (w : ℍ[ℝ]).imI • unitGenerator := by
  obtain ⟨h1, h2⟩ := adjointAction_piRotation_imJ_imK w
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
private theorem adjointAction_zero (g : UnitQuaternion) : adjointAction g 0 = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_zero <;> assumption
private theorem norm_adjointAction (g : UnitQuaternion) (w : imaginaryQuaternions) : ‖adjointAction g w‖ = ‖w‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction <;> assumption
section Curve
variable {L n u : ℕ} [NeZero L] [NeZero n]
private abbrev topAngleField (L u : ℕ) {n : ℕ} (B : TorusBond n → ℝ) (τ : ℝ) :
    (torusFrame L u n).GaugeField (u + 1) :=
  readAtLevel (torusFrame L u n) (u + 1) (expOfColourForm τ B)
private theorem halfRotation_gaugeTransform_topAngleField (B : TorusBond n → ℝ) (τ : ℝ) :
    gaugeTransform (fun _ => halfRotation) (topAngleField L u B τ) = topAngleField L u B τ := by
  funext y i
  show halfRotation * (expOfColourForm τ B (toTorusSite n y) i) * halfRotation⁻¹ = expOfColourForm τ B (toTorusSite n y) i
  rw [expOfColourForm_apply, halfRotation_conj]
private theorem eventually_curvature_lt (B : TorusBond n → ℝ) {σ : ℝ} (hσ : 0 < σ) (q : TorusSite n × Fin 4 × Fin 4) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), curvature (expOfColourForm τ B) q.1 q.2.1 q.2.2 < σ := by apply _root_.YangMills.SharedProofs.p47205 <;> assumption
private theorem eventually_isCold (B : TorusBond n → ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), IsCold (finiteCells (torusFrame L u n)) (u + 1) σ (topAngleField L u B τ) := by apply _root_.YangMills.DeltaSharedProofs.p502287 <;> assumption
private structure StepHypotheses (a ρ δ σA N0 : ℝ) (Nn : ℕ → ℝ) (L u n : ℕ) [NeZero L] [NeZero n] : Prop where
  coupling_pos : 0 < a
  odd : Odd L
  two_le : 2 ≤ n
  radius_pos : 0 < ρ
  radius_lt_pi : ρ < Real.pi
  threshold_pos : 0 < σA
  unique : ∀ V : (torusFrame L u n).GaugeField (u + 1), IsCold (finiteCells (torusFrame L u n)) (u + 1) σA V →
    HasColdMinimizer a ρ N0 σA (finiteCells (torusFrame L u n)) V
  coordinates : HasRegularCoordinates a δ ρ Nn (finiteCells (torusFrame L u n))
    (uniformField (torusFrame L u n) (torusFrame L u n).top)
  cutAction : LumpContours.ActionAtLevelIsCutAction
  wholeCellCost : LumpContours.WholeCellCostEqualsMinimalAction
  cutMinimal : LumpContours.CutActionEqualsMinimalAction
  flatTop : flatTopVanishingStatement
  equivariance : chartEquivarianceStatement
variable {a ρ δ σA N0 : ℝ} {Nn : ℕ → ℝ}
private theorem StepHypotheses.two_le_extent (P : StepHypotheses a ρ δ σA N0 Nn L u n) (i : Fin 4) :
    2 ≤ (torusFrame L u n).extent i := P.two_le
private theorem minimizingCoordinates_of_fixed (P : StepHypotheses a ρ δ σA N0 Nn L u n)
    {V : (torusFrame L u n).GaugeField (u + 1)}
    (hV : gaugeTransform (fun _ => halfRotation) V = V) (hc : IsCold (finiteCells (torusFrame L u n)) (u + 1) σA V) :
    IsMinimizingChart a (finiteCells (torusFrame L u n)) V ρ
        (minimizingCoordinates a (finiteCells (torusFrame L u n)) V ρ) ∧
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
    exact minimizingChart_unique (F := torusFrame L u n) P.odd P.two_le_extent P.radius_lt_pi hex.choose_spec hw2 hu
  have MW := P.equivariance (torusFrame L u n) a P.odd P.two_le_extent
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
    · show _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction _ (w b.1 b.2) = 0
      rw [hw.1 b hb, adjointAction_zero]
    · show ‖_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction _ (w b.1 b.2)‖ ≤ ρ
      rw [norm_adjointAction]
      exact hw2.2.1 b hb
  have hfix : w' = w := minimizingChart_unique (F := torusFrame L u n) P.odd P.two_le_extent P.radius_lt_pi hw' hw2 hu
  rw [hlc]
  refine ⟨hw2, fun x i => eq_imI_smul_of_fixed _ ?_⟩
  exact congrFun (congrFun hfix x) i
private theorem topAngleField_zero (B : TorusBond n → ℝ) :
    topAngleField L u B 0 = readAtLevel (torusFrame L u n) (u + 1) (expOfColourForm 1 (0 : TorusBond n → ℝ)) := by apply _root_.YangMills.DeltaSharedProofs.p501756 <;> assumption
private theorem minimizingCoordinates_topAngleField_zero (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) :
    minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B 0) ρ = fun _ _ => 0 := by
  have hc : IsCold (finiteCells (torusFrame L u n)) (u + 1) σA (topAngleField L u B 0) :=
    (eventually_isCold B P.threshold_pos).self_of_nhds
  obtain ⟨w, hw, -, hu⟩ := P.unique _ hc
  have hw2 : IsMinimizingChart a (finiteCells (torusFrame L u n)) (topAngleField L u B 0) ρ w :=
    ⟨hw.1, fun b hb => (hw.2.1 b hb).trans (min_le_left _ _), hw.2.2⟩
  have hex : ∃ w, IsMinimizingChart a (finiteCells (torusFrame L u n)) (topAngleField L u B 0) ρ w := ⟨w, hw2⟩
  have hlc : minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B 0) ρ = w := by
    unfold minimizingCoordinates
    rw [dif_pos hex]
    exact minimizingChart_unique (F := torusFrame L u n) P.odd P.two_le_extent P.radius_lt_pi hex.choose_spec hw2 hu
  have hz : chartedField (fun _ _ => 0) (topAngleField L u B 0) =
      readAtLevel (torusFrame L u n) u (expOfColourForm 1 (0 : TorusBond (n * L) → ℝ)) := by
    funext y i
    have e0 : expUnit (0 : imaginaryQuaternions) = 1 := by
      have := colourRotation_zero
      rw [colourRotation, zero_smul] at this
      exact this
    have e1 : topAngleField L u B 0 (enclosingCell y) i = 1 := by
      show expOfColourForm 0 B _ i = 1
      rw [expOfColourForm_apply, zero_mul, colourRotation_zero]
    have e2 : readAtLevel (torusFrame L u n) u (expOfColourForm 1 (0 : TorusBond (n * L) → ℝ)) y i = 1 := by
      show expOfColourForm 1 (0 : TorusBond (n * L) → ℝ) _ i = 1
      rw [expOfColourForm_apply]
      simp [colourRotation_zero]
    rw [e2]
    unfold chartedField
    split_ifs <;> simp [e0, e1]
  have hz2 : IsMinimizingChart a (finiteCells (torusFrame L u n)) (topAngleField L u B 0) ρ (fun _ _ => 0) := by
    refine ⟨fun _ _ => rfl, fun b _ => ?_, fun W' => ?_⟩
    · simpa using P.radius_pos.le
    · have h0 := blockEnergy_readAtLevel (u := u) P.cutAction P.wholeCellCost P.coupling_pos.le P.odd
        (0 : AnglePair L n)
      rw [pairEnergy_zero P.cutAction P.wholeCellCost P.flatTop P.coupling_pos.le P.odd] at h0
      rw [hz, topAngleField_zero B]
      have h1 : blockEnergy a (finiteCells (torusFrame L u n)) u
          (readAtLevel (torusFrame L u n) u (expOfColourForm 1 (0 : TorusBond (n * L) → ℝ)))
          (readAtLevel (torusFrame L u n) (u + 1) (expOfColourForm 1 (0 : TorusBond n → ℝ))) = 0 := h0
      exact h1.le.trans (blockEnergy_nonneg P.wholeCellCost P.cutMinimal P.coupling_pos.le P.odd _ _)
  rw [hlc]
  exact (minimizingChart_unique (F := torusFrame L u n) P.odd P.two_le_extent P.radius_lt_pi hz2 hw2 hu).symm
end Curve
section Angles
variable {L n u : ℕ} [NeZero L] [NeZero n] {a ρ δ σA N0 : ℝ} {Nn : ℕ → ℝ}
private def frameBond (L u : ℕ) {n : ℕ} (b : TorusBond (n * L)) :
    (torusFrame L u n).Site (torusFrame L u n).depth × Fin 4 :=
  (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2)
private theorem mem_chartBonds_iff (hL : Odd L) (h2 : 2 ≤ n) (b : TorusBond (n * L)) :
    b ∈ chartBonds L n ↔ ¬ IsAxialTreeBond (F := torusFrame L u n) (frameBond L u b) := by apply _root_.YangMills.DeltaSharedProofs.p2283 <;> assumption
open Classical in
private def crossingAngle (L u : ℕ) {n : ℕ} (B : TorusBond n → ℝ) (b : TorusBond (n * L)) : ℝ :=
  if IsCrossingBond (F := torusFrame L u n) (frameBond L u b) then B (parentBlock L b.1, b.2) else 0
open Classical in
private def minimizerAngles (a ρ : ℝ) (L u : ℕ) {n : ℕ} [NeZero L] [NeZero n] (B : TorusBond n → ℝ) (τ : ℝ) :
    TorusBond (n * L) → ℝ := fun b =>
  if b ∈ chartBonds L n then
    ((minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ (frameBond L u b).1
      (frameBond L u b).2 : imaginaryQuaternions) : ℍ[ℝ]).imI + τ * crossingAngle L u B b
  else 0
private theorem readAtLevel_minimizerAngles (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) {τ : ℝ}
    (hone : ∀ x i, minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ x i =
      ((minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ x i :
        imaginaryQuaternions) : ℍ[ℝ]).imI • unitGenerator) :
    readAtLevel (torusFrame L u n) u (expOfColourForm 1 (minimizerAngles a ρ L u B τ)) =
      chartedField (minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ)
        (topAngleField L u B τ) := by
  classical
  have : NeZero (n * (torusFrame L u n).blockSide) := inferInstanceAs (NeZero (n * L))
  funext y i
  set w := minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ with hw
  set b : TorusBond (n * L) := (toTorusSite (n * L) y, i) with hb
  have hy : torusSiteInFrame (torusFrame L u n) u b.1 = y := torusSiteInFrame_toTorusSite (period_depth L u n) y
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
    have hm : b ∈ chartBonds L n := (mem_chartBonds_iff P.odd P.two_le b).2 (by rw [hx]; exact hnt)
    have hcell : enclosingCell y = torusSiteInFrame (torusFrame L u n) (u + 1) (parentBlock L b.1) := by
      rw [← hy]
      exact enclosingCell_torusSiteInFrame (F := torusFrame L u n) (n := n) (fun _ => rfl) b.1
    have hcr : crossingAngle L u B b = B (parentBlock L b.1, b.2) := by
      unfold crossingAngle
      rw [if_pos (by rw [hx]; exact hc)]
    have hV : topAngleField L u B τ (enclosingCell y) i = colourRotation (τ * B (parentBlock L b.1, b.2)) := by
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
    · have hm : b ∉ chartBonds L n := fun h => (mem_chartBonds_iff P.odd P.two_le b).1 h (by rw [hx]; exact ht)
      have hg : minimizerAngles a ρ L u B τ b = 0 := by
        unfold minimizerAngles
        rw [if_neg hm]
      rw [if_pos ht, hg, colourRotation_zero]
    · have hm : b ∈ chartBonds L n := (mem_chartBonds_iff P.odd P.two_le b).2 (by rw [hx]; exact ht)
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
  · rw [minimizingCoordinates_topAngleField_zero P B]
    simp
  · rfl
private abbrev topBondEquiv (n : ℕ) [NeZero n] : TorusBond n ≃ Fin (Fintype.card (TorusBond n)) :=
  Fintype.equivFin (TorusBond n)
private def topFrameBond (L u n : ℕ) [NeZero n] (l : Fin (Fintype.card (TorusBond n))) :
    (torusFrame L u n).Site (torusFrame L u n).top × Fin 4 :=
  (torusSiteInFrame (torusFrame L u n) (u + 1) ((topBondEquiv n).symm l).1, ((topBondEquiv n).symm l).2)
private def colourDirections (k : ℕ) : Fin k → imaginaryQuaternions := fun _ => unitGenerator
private def topAngleVector (B : TorusBond n → ℝ) : Fin (Fintype.card (TorusBond n)) → ℝ :=
  fun l => B ((topBondEquiv n).symm l)
private theorem topFrameBond_topBondEquiv (c : TorusBond n) :
    topFrameBond L u n (topBondEquiv n c) = (torusSiteInFrame (torusFrame L u n) (u + 1) c.1, c.2) := by
  show (torusSiteInFrame (torusFrame L u n) (u + 1) ((topBondEquiv n).symm (topBondEquiv n c)).1,
    ((topBondEquiv n).symm (topBondEquiv n c)).2) = _
  rw [Equiv.symm_apply_apply]
private theorem bondSpread_single {F : BlockFrame} {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ)
    (y : F.Site F.top) (i : Fin 4) (l₀ : Fin k) (h : c l₀ = (y, i)) (hu : ∀ l, l ≠ l₀ → c l ≠ (y, i)) :
    BlockAverages.bondSpread c X σ y i = σ l₀ • X l₀ := by apply _root_.YangMills.SharedProofs.p504 <;> assumption
private theorem topAngleField_eq_rotatedField (B : TorusBond n → ℝ) (τ : ℝ) :
    topAngleField L u B τ = rotatedField
      (BlockAverages.bondSpread (topFrameBond L u n) (colourDirections _) (τ • topAngleVector B))
      (uniformField (torusFrame L u n) (torusFrame L u n).top) := by
  classical
  funext y i
  set c : TorusBond n := (toTorusSite n y, i) with hc
  have hq := period_top L u n
  have hy : torusSiteInFrame (torusFrame L u n) (u + 1) c.1 = y := torusSiteInFrame_toTorusSite hq y
  have hs := bondSpread_single (F := torusFrame L u n) (topFrameBond L u n) (colourDirections _)
    (τ • topAngleVector B) y i (topBondEquiv n c)
    (by rw [topFrameBond_topBondEquiv]; exact Prod.ext hy rfl) (by
      intro l hl h
      apply hl
      have h1 : ((topBondEquiv n).symm l) = c := by
        have h2 := congrArg Prod.fst h
        have h3 := congrArg Prod.snd h
        refine Prod.ext ?_ h3
        have h4 : torusSiteInFrame (torusFrame L u n) (u + 1) ((topBondEquiv n).symm l).1 = y := h2
        have h5 := toTorusSite_torusSiteInFrame hq ((topBondEquiv n).symm l).1
        rw [h4] at h5
        exact h5.symm
      rw [← h1]
      simp)
  show expOfColourForm τ B (toTorusSite n y) i =
    expUnit (BlockAverages.bondSpread (topFrameBond L u n) (colourDirections _) (τ • topAngleVector B) y i) * 1
  rw [mul_one, expOfColourForm_apply, hs]
  show expUnit ((τ * B c) • unitGenerator) = _
  congr 1
  simp [topAngleVector, colourDirections]
private def bondCoordinateMap (a ρ : ℝ) (L u : ℕ) {n : ℕ} [NeZero n] (b : TorusBond (n * L))
    (σ : Fin (Fintype.card (TorusBond n)) → ℝ) : imaginaryQuaternions :=
  minimizingBondCoordinate a ρ (finiteCells (torusFrame L u n)) (frameBond L u b)
    (rotatedField (BlockAverages.bondSpread (topFrameBond L u n) (colourDirections _) σ)
      (uniformField (torusFrame L u n) (torusFrame L u n).top))
private theorem minimizingCoordinates_eq_bondCoordinateMap (B : TorusBond n → ℝ) (τ : ℝ) (b : TorusBond (n * L)) :
    minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ (frameBond L u b).1
      (frameBond L u b).2 = bondCoordinateMap a ρ L u b (τ • topAngleVector B) :=
  congrArg (fun V => minimizingCoordinates a (finiteCells (torusFrame L u n)) V ρ (frameBond L u b).1
    (frameBond L u b).2) (topAngleField_eq_rotatedField B τ)
private def imIComponent : imaginaryQuaternions →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  { toFun := fun v => (v : ℍ[ℝ]).imI
    map_add' := fun _ _ => by simp
    map_smul' := fun _ _ => by simp }
private theorem minimizerAngles_of_mem (B : TorusBond n → ℝ) {b : TorusBond (n * L)} (hb : b ∈ chartBonds L n)
    (τ : ℝ) :
    minimizerAngles a ρ L u B τ b =
      imIComponent (bondCoordinateMap a ρ L u b (τ • topAngleVector B)) + τ * crossingAngle L u B b := by
  unfold minimizerAngles
  rw [if_pos hb, minimizingCoordinates_eq_bondCoordinateMap]
  rfl
private theorem frameBond_mem_chordBonds (P : StepHypotheses a ρ δ σA N0 Nn L u n) {b : TorusBond (n * L)}
    (hb : b ∈ chartBonds L n) :
    frameBond L u b ∈ chordBonds (finiteCells (torusFrame L u n)) :=
  (P.equivariance (torusFrame L u n) a P.odd P.two_le_extent).mem_chordBonds_of_not_tree _
    ((mem_chartBonds_iff P.odd P.two_le b).1 hb)
private theorem analyticAt_bondCoordinateMap (P : StepHypotheses a ρ δ σA N0 Nn L u n) {b : TorusBond (n * L)}
    (hb : b ∈ chartBonds L n) :
    AnalyticAt ℝ (bondCoordinateMap a ρ L u b) 0 :=
  (P.coordinates _ (frameBond_mem_chordBonds P hb)).1 _ _ _
private instance completeSpace_imaginaryQuaternions : CompleteSpace imaginaryQuaternions :=
  FiniteDimensional.complete ℝ imaginaryQuaternions
private theorem contDiffAt_minimizerAngles (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) :
    ContDiffAt ℝ 2 (minimizerAngles a ρ L u B) 0 := by
  classical
  refine contDiffAt_pi.2 fun b => ?_
  by_cases hb : b ∈ chartBonds L n
  · have e : (fun τ => minimizerAngles a ρ L u B τ b) =
        fun τ => imIComponent (bondCoordinateMap a ρ L u b (τ • topAngleVector B)) + τ * crossingAngle L u B b :=
      funext fun τ => minimizerAngles_of_mem B hb τ
    rw [e]
    refine ContDiffAt.add ?_ (contDiffAt_id.mul contDiffAt_const)
    have h1 : ContDiffAt ℝ 2 (bondCoordinateMap a ρ L u b) ((0 : ℝ) • topAngleVector B) := by
      rw [zero_smul]
      exact (analyticAt_bondCoordinateMap P hb).contDiffAt
    have h2 : ContDiffAt ℝ 2 (fun τ : ℝ => τ • topAngleVector B) 0 := contDiffAt_id.smul contDiffAt_const
    have h3 : ContDiffAt ℝ 2 (fun τ : ℝ => bondCoordinateMap a ρ L u b (τ • topAngleVector B)) 0 :=
      ContDiffAt.comp (g := bondCoordinateMap a ρ L u b) (f := fun τ : ℝ => τ • topAngleVector B) (0 : ℝ) h1 h2
    exact ContDiffAt.comp (g := imIComponent) (f := fun τ : ℝ => bondCoordinateMap a ρ L u b (τ • topAngleVector B))
      (0 : ℝ) imIComponent.contDiff.contDiffAt h3
  · have e : (fun τ => minimizerAngles a ρ L u B τ b) = fun _ => 0 := funext fun τ => by
      unfold minimizerAngles
      rw [if_neg hb]
    rw [e]
    exact contDiffAt_const
open Classical in
private def responseVelocity (a ρ : ℝ) (L u : ℕ) {n : ℕ} [NeZero L] [NeZero n] (B : TorusBond n → ℝ) :
    TorusBond (n * L) → ℝ := fun b =>
  if b ∈ chartBonds L n then
    imIComponent (fderiv ℝ (bondCoordinateMap a ρ L u b) 0 (topAngleVector B)) + crossingAngle L u B b
  else 0
private theorem deriv_minimizerAngles (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) :
    deriv (minimizerAngles a ρ L u B) 0 = responseVelocity a ρ L u B := by
  classical
  have hd : ∀ b, DifferentiableAt ℝ (fun τ => minimizerAngles a ρ L u B τ b) 0 := fun b =>
    ((contDiffAt_pi.1 (contDiffAt_minimizerAngles P B) b).differentiableAt (by norm_num))
  rw [deriv_pi hd]
  funext b
  unfold responseVelocity
  by_cases hb : b ∈ chartBonds L n
  · rw [if_pos hb]
    have e : (fun τ => minimizerAngles a ρ L u B τ b) =
        fun τ => imIComponent (bondCoordinateMap a ρ L u b (τ • topAngleVector B)) + τ * crossingAngle L u B b :=
      funext fun τ => minimizerAngles_of_mem B hb τ
    rw [e]
    have hD : HasFDerivAt (bondCoordinateMap a ρ L u b) (fderiv ℝ (bondCoordinateMap a ρ L u b) 0)
        ((0 : ℝ) • topAngleVector B) := by
      rw [zero_smul]
      exact (analyticAt_bondCoordinateMap P hb).differentiableAt.hasFDerivAt
    have hl : HasDerivAt (fun τ : ℝ => τ • topAngleVector B) (topAngleVector B) 0 := by
      have h3 : HasDerivAt (fun τ : ℝ => τ • topAngleVector B) ((1 : ℝ) • topAngleVector B) 0 :=
        (hasDerivAt_id' (0 : ℝ)).smul_const _
      rwa [one_smul] at h3
    have h3 : HasDerivAt (fun τ : ℝ => bondCoordinateMap a ρ L u b (τ • topAngleVector B))
        (fderiv ℝ (bondCoordinateMap a ρ L u b) 0 (topAngleVector B)) 0 :=
      HasFDerivAt.comp_hasDerivAt (f := fun τ : ℝ => τ • topAngleVector B) (0 : ℝ) hD hl
    have h4 : HasDerivAt (fun τ : ℝ => imIComponent (bondCoordinateMap a ρ L u b (τ • topAngleVector B)))
        (imIComponent (fderiv ℝ (bondCoordinateMap a ρ L u b) 0 (topAngleVector B))) 0 :=
      imIComponent.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
    have h5 : HasDerivAt (fun τ : ℝ => τ * crossingAngle L u B b) (crossingAngle L u B b) 0 := by
      simpa using (hasDerivAt_id' (0 : ℝ)).mul_const (crossingAngle L u B b)
    exact (h4.fun_add h5).deriv
  · rw [if_neg hb]
    have e : (fun τ => minimizerAngles a ρ L u B τ b) = fun _ => 0 := funext fun τ => by
      unfold minimizerAngles
      rw [if_neg hb]
    rw [e]
    simp
private theorem bondDeriv_eq_fderiv (P : StepHypotheses a ρ δ σA N0 Nn L u n) {b : TorusBond (n * L)}
    (hb : b ∈ chartBonds L n) (l : Fin (Fintype.card (TorusBond n))) :
    bondDeriv (torusCoordinate a ρ (frameBond L u b)) (uniformField (torusFrame L u n) (torusFrame L u n).top)
      ![topFrameBond L u n l] ![unitGenerator] = fderiv ℝ (bondCoordinateMap a ρ L u b) 0 (Pi.single l 1) := by
  classical
  unfold bondDeriv
  rw [iteratedFDeriv_one_apply]
  set ι : (Fin 1 → ℝ) →L[ℝ] (Fin (Fintype.card (TorusBond n)) → ℝ) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight (Pi.single l 1) with hι
  have e : (fun τ : Fin 1 → ℝ => torusCoordinate a ρ (frameBond L u b)
      (leftTranslate (ColdStepAtMirrorFrames.bondSpread ![topFrameBond L u n l] ![unitGenerator] τ)
        (uniformField (torusFrame L u n) (torusFrame L u n).top))) =
      fun τ => bondCoordinateMap a ρ L u b (ι τ) := by
    funext τ
    unfold bondCoordinateMap torusCoordinate
    congr 1
    funext y i
    show expUnit (ColdStepAtMirrorFrames.bondSpread ![topFrameBond L u n l] ![unitGenerator] τ y i) * 1 =
      expUnit (BlockAverages.bondSpread (topFrameBond L u n) (colourDirections _) (ι τ) y i) * 1
    congr 2
    unfold ColdStepAtMirrorFrames.bondSpread BlockAverages.bondSpread
    rw [Fin.sum_univ_one, Finset.sum_eq_single l]
    · by_cases h : topFrameBond L u n l = (y, i)
      · rw [if_pos (by simpa using h), if_pos h]
        simp [hι, colourDirections]
      · rw [if_neg (by simpa using h), if_neg h]
    · intro l' _ hl'
      have : (ι τ) l' = 0 := by simp [hι, hl']
      rw [this]
      simp
    · simp
  rw [e]
  have hd : DifferentiableAt ℝ (bondCoordinateMap a ρ L u b) (ι 0) := by
    rw [map_zero]
    exact (analyticAt_bondCoordinateMap P hb).differentiableAt
  have h1 : HasFDerivAt (fun τ => bondCoordinateMap a ρ L u b (ι τ))
      ((fderiv ℝ (bondCoordinateMap a ρ L u b) (ι 0)).comp ι) 0 :=
    hd.hasFDerivAt.comp (0 : Fin 1 → ℝ) ι.hasFDerivAt
  rw [h1.fderiv, map_zero]
  simp [hι]
private theorem apply_topAngleVector (φ : (Fin (Fintype.card (TorusBond n)) → ℝ) →L[ℝ] ℝ) (B : TorusBond n → ℝ) :
    φ (topAngleVector B) = ∑ c : TorusBond n, φ (Pi.single (topBondEquiv n c) 1) * B c := by apply _root_.YangMills.DeltaSharedProofs.p501545 <;> assumption
private theorem responseMap_eq (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) {b : TorusBond (n * L)}
    (hb : b ∈ chartBonds L n) :
    responseMap a ρ L u B b =
      imIComponent (fderiv ℝ (bondCoordinateMap a ρ L u b) 0 (topAngleVector B)) + crossingAngle L u B b := by
  classical
  have : NeZero (n * (torusFrame L u n).blockSide) := inferInstanceAs (NeZero (n * L))
  have hq := period_top L u n
  have hentry : ∀ c : TorusBond n, responseKernel a ρ L u b c =
      imIComponent (fderiv ℝ (bondCoordinateMap a ρ L u b) 0 (Pi.single (topBondEquiv n c) 1)) +
        (if IsCrossingBond (F := torusFrame L u n) (frameBond L u b) ∧
          enclosingCell (frameBond L u b).1 = torusSiteInFrame (torusFrame L u n) (u + 1) c.1 ∧ b.2 = c.2
          then 1 else 0) := by
    intro c
    have h1 := bondDeriv_eq_fderiv P hb (topBondEquiv n c)
    rw [topFrameBond_topBondEquiv] at h1
    unfold responseKernel minimizerResponse
    refine congrArg₂ (· + ·) ?_ (if_congr Iff.rfl rfl rfl)
    refine (congrArg (fun v : imaginaryQuaternions => -((v : ℍ[ℝ]) * (unitGenerator : ℍ[ℝ])).re) h1).trans ?_
    exact neg_re_mul_unitGenerator _
  unfold responseMap
  simp only [hentry, add_mul, Finset.sum_add_distrib]
  have e1 : ∑ c : TorusBond n,
      imIComponent (fderiv ℝ (bondCoordinateMap a ρ L u b) 0 (Pi.single (topBondEquiv n c) 1)) * B c =
      imIComponent (fderiv ℝ (bondCoordinateMap a ρ L u b) 0 (topAngleVector B)) := by
    have := apply_topAngleVector
      (imIComponent.comp (fderiv ℝ (bondCoordinateMap a ρ L u b) 0 : _ →L[ℝ] imaginaryQuaternions)) B
    simpa using this.symm
  rw [e1]
  congr 1
  unfold crossingAngle
  by_cases hc : IsCrossingBond (F := torusFrame L u n) (frameBond L u b)
  · rw [if_pos hc]
    have hcell : enclosingCell (frameBond L u b).1 =
        torusSiteInFrame (torusFrame L u n) (u + 1) (parentBlock L b.1) :=
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
end Angles
section Final
variable {L n u : ℕ} [NeZero L] [NeZero n] {a ρ δ σA N0 : ℝ} {Nn : ℕ → ℝ}
private theorem contourMeanSlope_eq (W : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    contourMeanSlope L n W c = ∑ k ∈ contourIndex L, contourWeight L * contourSum L W c k := by apply _root_.YangMills.SharedProofs.p78625 <;> assumption
private def minimizerCurve (a ρ : ℝ) (L u : ℕ) {n : ℕ} [NeZero L] [NeZero n] (B : TorusBond n → ℝ) (τ : ℝ) :
    AnglePair L n :=
  (minimizerAngles a ρ L u B τ, τ • B)
private theorem eventually_minimizing_single_colour (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) :
    ∀ᶠ τ in 𝓝 (0 : ℝ),
      IsMinimizingChart a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ
        (minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ) ∧
      ∀ x i, minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ x i =
        ((minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ x i :
          imaginaryQuaternions) : ℍ[ℝ]).imI • unitGenerator :=
  (eventually_isCold B P.threshold_pos).mono fun τ hτ =>
    minimizingCoordinates_of_fixed P (halfRotation_gaugeTransform_topAngleField B τ) hτ
private theorem readAtLevel_smul (B : TorusBond n → ℝ) (τ : ℝ) :
    readAtLevel (torusFrame L u n) (u + 1) (expOfColourForm 1 (τ • B)) = topAngleField L u B τ := by
  rw [expOfColourForm_one_smul]
private theorem blockEnergy_minimizerCurve (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) {τ : ℝ}
    (hone : ∀ x i, minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ x i =
      ((minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ x i :
        imaginaryQuaternions) : ℍ[ℝ]).imI • unitGenerator) :
    blockEnergy a (finiteCells (torusFrame L u n)) u
      (chartedField (minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ)
        (topAngleField L u B τ)) (topAngleField L u B τ) =
      pairEnergy a L u (minimizerCurve a ρ L u B τ) := by
  have h := blockEnergy_readAtLevel (u := u) P.cutAction P.wholeCellCost P.coupling_pos.le P.odd
    (minimizerCurve a ρ L u B τ)
  have e1 : readAtLevel (torusFrame L u n) u (expOfColourForm 1 (minimizerCurve a ρ L u B τ).1) =
      chartedField (minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ)
        (topAngleField L u B τ) := readAtLevel_minimizerAngles P B hone
  have e2 : readAtLevel (torusFrame L u n) (u + 1) (expOfColourForm 1 (minimizerCurve a ρ L u B τ).2) =
      topAngleField L u B τ := readAtLevel_smul B τ
  exact (congrArg₂ (fun W V => blockEnergy a (finiteCells (torusFrame L u n)) u W V) e1 e2).symm.trans h
private theorem colourAction_smul_eq (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) {τ : ℝ}
    (hl : IsMinimizingChart a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ
        (minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ))
    (hone : ∀ x i, minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ x i =
      ((minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ x i :
        imaginaryQuaternions) : ℍ[ℝ]).imI • unitGenerator) :
    colourAction a L (u + 1) (τ • B) = pairEnergy a L u (minimizerCurve a ρ L u B τ) := by
  unfold colourAction
  rw [expOfColourForm_one_smul]
  exact (actionAtLevel_succ_eq_blockEnergy P.wholeCellCost P.cutMinimal P.coupling_pos.le P.odd hl).trans
    (blockEnergy_minimizerCurve P B hone)
private theorem pairEnergy_minimizerCurve_le (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ)
    (D : TorusBond (n * L) → ℝ) {τ : ℝ}
    (hl : IsMinimizingChart a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ
        (minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ))
    (hone : ∀ x i, minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ x i =
      ((minimizingCoordinates a (finiteCells (torusFrame L u n)) (topAngleField L u B τ) ρ x i :
        imaginaryQuaternions) : ℍ[ℝ]).imI • unitGenerator) :
    pairEnergy a L u (minimizerCurve a ρ L u B τ) ≤ pairEnergy a L u (τ • ((D, B) : AnglePair L n)) := by
  have h1 := hl.2.2 (readAtLevel (torusFrame L u n) u (expOfColourForm 1 (τ • D)))
  have h2 := blockEnergy_readAtLevel (u := u) P.cutAction P.wholeCellCost P.coupling_pos.le P.odd
    (τ • ((D, B) : AnglePair L n))
  have e2 : readAtLevel (torusFrame L u n) (u + 1) (expOfColourForm 1 (τ • ((D, B) : AnglePair L n)).2) =
      topAngleField L u B τ := readAtLevel_smul B τ
  have h3 : blockEnergy a (finiteCells (torusFrame L u n)) u
      (readAtLevel (torusFrame L u n) u (expOfColourForm 1 (τ • D))) (topAngleField L u B τ) =
      pairEnergy a L u (τ • ((D, B) : AnglePair L n)) :=
    (congrArg (fun V => blockEnergy a (finiteCells (torusFrame L u n)) u
      (readAtLevel (torusFrame L u n) u (expOfColourForm 1 (τ • D))) V) e2).symm.trans h2
  have h4 := blockEnergy_minimizerCurve P B hone
  calc pairEnergy a L u (minimizerCurve a ρ L u B τ) = _ := h4.symm
    _ ≤ _ := h1
    _ = _ := h3
private theorem contDiffAt_minimizerCurve (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) :
    ContDiffAt ℝ 2 (minimizerCurve a ρ L u B) 0 :=
  (contDiffAt_minimizerAngles P B).prodMk (contDiffAt_id.smul contDiffAt_const)
private theorem minimizerCurve_zero (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) :
    minimizerCurve a ρ L u B 0 = 0 :=
  Prod.ext (minimizerAngles_zero P B) (zero_smul ℝ B)
private theorem deriv_minimizerCurve (P : StepHypotheses a ρ δ σA N0 Nn L u n) (B : TorusBond n → ℝ) :
    deriv (minimizerCurve a ρ L u B) 0 = (responseVelocity a ρ L u B, B) := by
  have h1 : HasDerivAt (minimizerAngles a ρ L u B) (responseVelocity a ρ L u B) 0 := by
    rw [← deriv_minimizerAngles P B]
    exact ((contDiffAt_minimizerAngles P B).differentiableAt (by norm_num)).hasDerivAt
  have h2 : HasDerivAt (fun τ : ℝ => τ • B) B 0 := by
    have h3 : HasDerivAt (fun τ : ℝ => τ • B) ((1 : ℝ) • B) 0 := (hasDerivAt_id' (0 : ℝ)).smul_const _
    rwa [one_smul] at h3
  exact (h1.prodMk h2).deriv
private theorem contDiffAt_pairEnergy_minimizerCurve (P : StepHypotheses a ρ δ σA N0 Nn L u n)
    (hJ : ContDiffAt ℝ 2 (pairEnergy (n := n) a L u) 0) (B : TorusBond n → ℝ) :
    ContDiffAt ℝ 2 (fun τ => pairEnergy a L u (minimizerCurve a ρ L u B τ)) 0 := by
  have h0 : ContDiffAt ℝ 2 (pairEnergy (n := n) a L u) (minimizerCurve a ρ L u B 0) := by
    rw [minimizerCurve_zero P B]
    exact hJ
  exact ContDiffAt.comp (g := pairEnergy (n := n) a L u) (f := minimizerCurve a ρ L u B) (0 : ℝ) h0
    (contDiffAt_minimizerCurve P B)
private theorem deriv_deriv_pairEnergy_minimizerCurve (P : StepHypotheses a ρ δ σA N0 Nn L u n)
    (hJ : ContDiffAt ℝ 2 (pairEnergy (n := n) a L u) 0) (B : TorusBond n → ℝ) :
    deriv (deriv fun τ => pairEnergy a L u (minimizerCurve a ρ L u B τ)) 0 =
      hessianAtZero (pairEnergy (n := n) a L u) (responseVelocity a ρ L u B, B) (responseVelocity a ρ L u B, B) := by
  have e := deriv_deriv_along_curve hJ
    (fderiv_pairEnergy_zero P.cutAction P.wholeCellCost P.cutMinimal P.flatTop P.coupling_pos.le P.odd)
    (contDiffAt_minimizerCurve P B) (minimizerCurve_zero P B)
  rw [deriv_minimizerCurve P B] at e
  exact e
private theorem hessian_minimizerVelocity (P : StepHypotheses a ρ δ σA N0 Nn L u n)
    (hJ : ContDiffAt ℝ 2 (pairEnergy (n := n) a L u) 0)
    (hA' : ContDiffAt ℝ 2 (colourAction a L (u + 1) (m := n)) 0) (B : TorusBond n → ℝ) :
    hessianAtZero (pairEnergy (n := n) a L u) (responseVelocity a ρ L u B, B) (responseVelocity a ρ L u B, B) =
      maxwellForm a L (u + 1) B B := by
  rw [maxwellForm_eq_hessian hA', ← deriv_deriv_pairEnergy_minimizerCurve P hJ B, ← deriv_deriv_along_line hA' B]
  have hev : (fun τ : ℝ => pairEnergy a L u (minimizerCurve a ρ L u B τ)) =ᶠ[𝓝 0]
      fun τ => colourAction a L (u + 1) (τ • B) :=
    (eventually_minimizing_single_colour P B).mono fun τ h => (colourAction_smul_eq P B h.1 h.2).symm
  exact hev.deriv.deriv_eq
private theorem hessian_minimizerVelocity_le (P : StepHypotheses a ρ δ σA N0 Nn L u n)
    (hJ : ContDiffAt ℝ 2 (pairEnergy (n := n) a L u) 0) (B : TorusBond n → ℝ) (D : TorusBond (n * L) → ℝ) :
    hessianAtZero (pairEnergy (n := n) a L u) (responseVelocity a ρ L u B, B) (responseVelocity a ρ L u B, B) ≤
      hessianAtZero (pairEnergy (n := n) a L u) ((D, B) : AnglePair L n) (D, B) := by
  have G1 := SecondJet.of_contDiffAt (contDiffAt_along_line hJ ((D, B) : AnglePair L n))
  have G2 := SecondJet.of_contDiffAt (contDiffAt_pairEnergy_minimizerCurve P hJ B)
  have H := G1.sub G2
  have h0 : (fun τ => pairEnergy a L u (τ • ((D, B) : AnglePair L n)) -
      pairEnergy a L u (minimizerCurve a ρ L u B τ)) 0 = 0 := by
    show pairEnergy a L u ((0 : ℝ) • ((D, B) : AnglePair L n)) - pairEnergy a L u (minimizerCurve a ρ L u B 0) = 0
    rw [minimizerCurve_zero P B, zero_smul, sub_self]
  have hpos : ∀ᶠ τ in 𝓝 (0 : ℝ),
      0 ≤ pairEnergy a L u (τ • ((D, B) : AnglePair L n)) - pairEnergy a L u (minimizerCurve a ρ L u B τ) :=
    (eventually_minimizing_single_colour P B).mono fun τ h =>
      sub_nonneg.2 (pairEnergy_minimizerCurve_le P B D h.1 h.2)
  have h1 := deriv_deriv_nonneg_of_nonneg H.contDiffAt h0 hpos
  rw [H.secondDeriv, deriv_deriv_along_line hJ, deriv_deriv_pairEnergy_minimizerCurve P hJ B] at h1
  linarith
private theorem eq_zero_of_quadratic_nonneg {x y : ℝ} (h : ∀ ε : ℝ, 0 ≤ 2 * ε * x + ε ^ 2 * y) : x = 0 := by apply _root_.YangMills.SharedProofs.p10126 <;> assumption
private theorem hessian_minimizerVelocity_orthogonal (P : StepHypotheses a ρ δ σA N0 Nn L u n)
    (hJ : ContDiffAt ℝ 2 (pairEnergy (n := n) a L u) 0) (B : TorusBond n → ℝ) (E : TorusBond (n * L) → ℝ) :
    hessianAtZero (pairEnergy (n := n) a L u) (responseVelocity a ρ L u B, B) ((E, 0) : AnglePair L n) = 0 := by
  set p : AnglePair L n := (responseVelocity a ρ L u B, B) with hp
  set q : AnglePair L n := (E, 0) with hq
  refine eq_zero_of_quadratic_nonneg (y := hessianAtZero (pairEnergy (n := n) a L u) q q) fun ε => ?_
  have h := hessian_minimizerVelocity_le P hJ B (responseVelocity a ρ L u B + ε • E)
  have e : ((responseVelocity a ρ L u B + ε • E, B) : AnglePair L n) = p + ε • q := by
    rw [hp, hq]
    exact Prod.ext rfl (by simp)
  rw [e] at h
  simp only [hessianAtZero_add_left, hessianAtZero_add_right, hessianAtZero_smul_left,
    hessianAtZero_smul_right] at h
  rw [hessianAtZero_comm hJ q p] at h
  nlinarith
private theorem hessian_pairEnergy (hL : Odd L) (hA : ContDiffAt ℝ 2 (colourAction a L u (m := n * L)) 0)
    (hJ : ContDiffAt ℝ 2 (pairEnergy (n := n) a L u) 0) (W : TorusBond (n * L) → ℝ) (B : TorusBond n → ℝ) :
    hessianAtZero (pairEnergy (n := n) a L u) ((W, B) : AnglePair L n) (W, B) =
      maxwellForm a L u W W + a * ∑ c : TorusBond n, (contourMeanSlope L n W c - B c) ^ 2 := by
  have G := SecondJet.of_contDiffAt (contDiffAt_along_line hA W)
  have S := SecondJet.sum (Finset.univ : Finset (TorusBond n))
    (g := fun c τ => pairFit L (τ • ((W, B) : AnglePair L n)) c)
    (a0 := fun _ => 0) (a1 := fun _ => 0)
    (a2 := fun c => (∑ k ∈ contourIndex L, contourWeight L * contourSum L W c k - B c) ^ 2)
    fun c _ => secondJet_pairFit hL W B c
  have T := G.add (S.const_mul a)
  have h := T.secondDeriv
  rw [deriv_deriv_along_line hA W, ← maxwellForm_eq_hessian hA] at h
  rw [← deriv_deriv_along_line hJ]
  simp only [contourMeanSlope_eq]
  exact h
private def torusBond (L u n : ℕ) [NeZero L] [NeZero n] (b : ↥(chordBonds (finiteCells (torusFrame L u n)))) :
    TorusBond (n * L) :=
  (toTorusSite (n * L) b.1.1, b.1.2)
private def bondIndicator (L u n : ℕ) [NeZero L] [NeZero n] (b : ↥(chordBonds (finiteCells (torusFrame L u n)))) :
    TorusBond (n * L) → ℝ :=
  Pi.single (torusBond L u n b) 1
private theorem frameBond_torusBond (b : ↥(chordBonds (finiteCells (torusFrame L u n)))) :
    frameBond L u (torusBond L u n b) = b.1 :=
  Prod.ext (torusSiteInFrame_toTorusSite (period_depth L u n) _) rfl
private theorem eq_torusBond_iff (y : (torusFrame L u n).Site (torusFrame L u n).depth) (i : Fin 4)
    (b : ↥(chordBonds (finiteCells (torusFrame L u n)))) :
    ((toTorusSite (n * L) y, i) : TorusBond (n * L)) = torusBond L u n b ↔ (y, i) = b.1 := by
  constructor
  · intro h
    have h1 := congrArg (frameBond L u) h
    rw [frameBond_torusBond] at h1
    have h2 : frameBond L u ((toTorusSite (n * L) y, i) : TorusBond (n * L)) = (y, i) :=
      Prod.ext (torusSiteInFrame_toTorusSite (period_depth L u n) y) rfl
    rw [← h2, h1]
  · intro h
    unfold torusBond
    rw [← h]
private theorem not_isAxialTreeBond (b : ↥(chordBonds (finiteCells (torusFrame L u n)))) :
    ¬ IsAxialTreeBond (F := torusFrame L u n) b.1 := by apply _root_.YangMills.SharedProofs.p1367 <;> assumption
private theorem trivialHessian_eq (P : StepHypotheses a ρ δ σA N0 Nn L u n)
    (hJ : ContDiffAt ℝ 2 (pairEnergy (n := n) a L u) 0)
    (b b' : ↥(chordBonds (finiteCells (torusFrame L u n)))) :
    trivialHessian a L u n b b' =
      hessianAtZero (pairEnergy (n := n) a L u) ((bondIndicator L u n b, 0) : AnglePair L n)
        ((bondIndicator L u n b', 0) : AnglePair L n) := by
  classical
  have e : ∀ s s' : ℝ, chartedEnergy a (pairCoordinates L u n b b' s s')
      (uniformField (torusFrame L u n) (torusFrame L u n).top) =
      pairEnergy a L u (s • ((bondIndicator L u n b, 0) : AnglePair L n) +
        s' • ((bondIndicator L u n b', 0) : AnglePair L n)) := by
    intro s s'
    set p : AnglePair L n := s • ((bondIndicator L u n b, 0) : AnglePair L n) +
      s' • ((bondIndicator L u n b', 0) : AnglePair L n) with hp
    have hp2 : p.2 = 0 := by simp [hp]
    have e2 : uniformField (torusFrame L u n) (torusFrame L u n).top =
        readAtLevel (torusFrame L u n) (u + 1) (expOfColourForm 1 p.2) := by
      rw [hp2, expOfColourForm_zero]
      rfl
    have e1 : chartedField (pairCoordinates L u n b b' s s')
        (uniformField (torusFrame L u n) (torusFrame L u n).top) =
        readAtLevel (torusFrame L u n) u (expOfColourForm 1 p.1) := by
      funext y i
      set c : TorusBond (n * L) := (toTorusSite (n * L) y, i) with hc
      have hr : readAtLevel (torusFrame L u n) u (expOfColourForm 1 p.1) y i = colourRotation (1 * p.1 c) := rfl
      have hpc : p.1 c = s * bondIndicator L u n b c + s' * bondIndicator L u n b' c := by simp [hp]
      have hd : ∀ b₁ : ↥(chordBonds (finiteCells (torusFrame L u n))), (y, i) = b₁.1 →
          bondIndicator L u n b₁ c = 1 := by
        intro b₁ h
        have hcb : c = torusBond L u n b₁ := (eq_torusBond_iff y i b₁).2 h
        unfold bondIndicator
        rw [hcb]
        simp
      have hd0 : ∀ b₁ : ↥(chordBonds (finiteCells (torusFrame L u n))), (y, i) ≠ b₁.1 →
          bondIndicator L u n b₁ c = 0 := by
        intro b₁ h
        unfold bondIndicator
        exact Pi.single_eq_of_ne (fun h' => h ((eq_torusBond_iff y i b₁).1 h')) _
      have hw : pairCoordinates L u n b b' s s' y i = (p.1 c) • unitGenerator := by
        rw [hpc]
        unfold pairCoordinates
        by_cases h1 : (y, i) = b.1 <;> by_cases h2 : (y, i) = b'.1
        · rw [if_pos h1, if_pos h2, hd b h1, hd b' h2]
          simp [add_smul]
        · rw [if_pos h1, if_neg h2, hd b h1, hd0 b' h2]
          simp
        · rw [if_neg h1, if_pos h2, hd0 b h1, hd b' h2]
          simp
        · rw [if_neg h1, if_neg h2, hd0 b h1, hd0 b' h2]
          simp
      have hexp : expUnit (pairCoordinates L u n b b' s s' y i) = colourRotation (p.1 c) := by
        rw [hw]
        rfl
      rw [hr, one_mul]
      unfold chartedField
      by_cases hcr : IsCrossingBond (F := torusFrame L u n) (y, i)
      · rw [if_pos hcr]
        exact (congrArg (· * (1 : UnitQuaternion)) hexp).trans (mul_one _)
      · rw [if_neg hcr]
        by_cases ht : IsAxialTreeBond (F := torusFrame L u n) (y, i)
        · rw [if_pos ht]
          have h1 : (y, i) ≠ b.1 := fun h => not_isAxialTreeBond b (h ▸ ht)
          have h2 : (y, i) ≠ b'.1 := fun h => not_isAxialTreeBond b' (h ▸ ht)
          rw [hpc, hd0 b h1, hd0 b' h2]
          simp [colourRotation_zero]
        · rw [if_neg ht]
          exact hexp
    unfold chartedEnergy
    exact (congrArg₂ (fun W V => blockEnergy a (finiteCells (torusFrame L u n)) u W V) e1 e2).trans
      (blockEnergy_readAtLevel (u := u) P.cutAction P.wholeCellCost P.coupling_pos.le P.odd p)
  show deriv (fun s => deriv (fun s' => chartedEnergy a (pairCoordinates L u n b b' s s')
    (uniformField (torusFrame L u n) (torusFrame L u n).top)) 0) 0 = _
  simp only [e]
  exact mixed_deriv_eq_hessianAtZero hJ _ _
private theorem chartRestriction_apply (h : TorusBond (n * L) → ℝ)
    (b : ↥(chordBonds (finiteCells (torusFrame L u n)))) :
    chartRestriction L u n h b = h (torusBond L u n b) := by
  unfold chartRestriction
  rw [Finset.sum_eq_single (torusBond L u n b)]
  · exact if_pos (frameBond_torusBond b)
  · intro c _ hc
    rw [if_neg]
    intro h1
    apply hc
    have h2 := (eq_torusBond_iff (L := L) (u := u) (n := n)
      (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth c.1) c.2 b).2 h1
    rw [← h2]
    exact Prod.ext (toTorusSite_torusSiteInFrame (period_depth L u n) c.1).symm rfl
  · simp
open Classical in
private def restrictToChart (L n : ℕ) [NeZero L] [NeZero n] (h : TorusBond (n * L) → ℝ) : TorusBond (n * L) → ℝ :=
  fun b => if b ∈ chartBonds L n then h b else 0
private theorem torusBond_mem (P : StepHypotheses a ρ δ σA N0 Nn L u n)
    (b : ↥(chordBonds (finiteCells (torusFrame L u n)))) :
    torusBond L u n b ∈ chartBonds L n := by
  rw [mem_chartBonds_iff (u := u) P.odd P.two_le, frameBond_torusBond]
  exact not_isAxialTreeBond b
private theorem restrictToChart_eq_sum (P : StepHypotheses a ρ δ σA N0 Nn L u n) (h : TorusBond (n * L) → ℝ) :
    ((restrictToChart L n h, 0) : AnglePair L n) =
      ∑ b : ↥(chordBonds (finiteCells (torusFrame L u n))),
        h (torusBond L u n b) • ((bondIndicator L u n b, 0) : AnglePair L n) := by
  classical
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    funext c
    rw [Finset.sum_apply]
    simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
    unfold restrictToChart
    by_cases hc : c ∈ chartBonds L n
    · rw [if_pos hc, Finset.sum_eq_single
        (⟨frameBond L u c, frameBond_mem_chordBonds P hc⟩ : ↥(chordBonds (finiteCells (torusFrame L u n))))]
      · have e : torusBond L u n
            (⟨frameBond L u c, frameBond_mem_chordBonds P hc⟩ : ↥(chordBonds (finiteCells (torusFrame L u n)))) = c :=
          Prod.ext (toTorusSite_torusSiteInFrame (period_depth L u n) c.1) rfl
        simp [bondIndicator, e]
      · intro b _ hb
        have : bondIndicator L u n b c = 0 := by
          refine Pi.single_eq_of_ne (fun h' => hb ?_) _
          apply Subtype.ext
          show b.1 = frameBond L u c
          rw [h', frameBond_torusBond]
        rw [this, mul_zero]
      · simp
    · rw [if_neg hc]
      refine (Finset.sum_eq_zero fun b _ => ?_).symm
      have : bondIndicator L u n b c = 0 :=
        Pi.single_eq_of_ne (fun (h' : c = torusBond L u n b) => hc (by rw [h']; exact torusBond_mem P b)) _
      rw [this, mul_zero]
  · rw [Prod.snd_sum]
    simp
private theorem stepHessianForm_eq (P : StepHypotheses a ρ δ σA N0 Nn L u n)
    (hJ : ContDiffAt ℝ 2 (pairEnergy (n := n) a L u) 0) (h : TorusBond (n * L) → ℝ) :
    stepHessianForm a L u n h =
      hessianAtZero (pairEnergy (n := n) a L u) ((restrictToChart L n h, 0) : AnglePair L n)
        (restrictToChart L n h, 0) := by
  rw [restrictToChart_eq_sum P h, hessianAtZero_sum_left]
  simp only [hessianAtZero_sum_right, hessianAtZero_smul_left, hessianAtZero_smul_right]
  unfold stepHessianForm
  simp only [dotProduct, Matrix.mulVec, chartRestriction_apply, trivialHessian_eq P hJ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring
private theorem step_identity (P : StepHypotheses a ρ δ σA N0 Nn L u n)
    (hA : ContDiffAt ℝ 2 (colourAction a L u (m := n * L)) 0)
    (hA' : ContDiffAt ℝ 2 (colourAction a L (u + 1) (m := n)) 0) (W : TorusBond (n * L) → ℝ) (B : TorusBond n → ℝ)
    (hW : ∀ b, b ∉ chartBonds L n → W b = 0) :
    maxwellForm a L u W W + a * ∑ c : TorusBond n, (contourMeanSlope L n W c - B c) ^ 2 =
      maxwellForm a L (u + 1) B B + stepHessianForm a L u n (W - responseMap a ρ L u B) := by
  classical
  have hJ := contDiffAt_pairEnergy (n := n) P.odd hA
  set E : TorusBond (n * L) → ℝ := W - responseVelocity a ρ L u B with hE
  have hm : restrictToChart L n (W - responseMap a ρ L u B) = E := by
    funext b
    unfold restrictToChart
    rw [hE]
    by_cases hb : b ∈ chartBonds L n
    · simp only [Pi.sub_apply]
      rw [if_pos hb, responseMap_eq P B hb]
      unfold responseVelocity
      rw [if_pos hb]
    · simp only [Pi.sub_apply]
      rw [if_neg hb, hW b hb]
      unfold responseVelocity
      rw [if_neg hb]
      ring
  rw [← hessian_pairEnergy P.odd hA hJ, ← hessian_minimizerVelocity P hJ hA', stepHessianForm_eq P hJ, hm]
  have e : ((W, B) : AnglePair L n) = (responseVelocity a ρ L u B, B) + ((E, 0) : AnglePair L n) := by
    rw [hE]
    exact Prod.ext (by simp) (by simp)
  rw [e]
  simp only [hessianAtZero_add_left, hessianAtZero_add_right]
  rw [hessianAtZero_comm hJ ((E, 0) : AnglePair L n) (responseVelocity a ρ L u B, B),
    hessian_minimizerVelocity_orthogonal P hJ]
  ring
private theorem sumAlongWord_pathToWord {N : ℕ} (A : TorusBond N → ℝ) (l : List PathStep) :
    ∀ y : TorusSite N, MomentLaw.sumAlongWord A (pathToWord y l) = sumAlongPath A y l := by
  induction l with
  | nil =>
    intro y
    simp [MomentLaw.sumAlongWord, pathToWord, sumAlongPath]
  | cons st r ih =>
    intro y
    obtain ⟨i, s⟩ := st
    have h := ih
    unfold MomentLaw.sumAlongWord at h ⊢
    cases s
    · simp [pathToWord, sumAlongPath, torusStep, h, sub_eq_add_neg]
    · simp [pathToWord, sumAlongPath, torusStep, h]
abbrev _root_.YangMills.SharedProofs.p6289 := @sumAlongWord_pathToWord
private theorem contourAverage_eq_slope (W : TorusBond (n * L) → ℝ) (c : TorusBond n) :
    MomentLaw.contourAverage L W c = contourMeanSlope L n W c := by
  rw [contourMeanSlope_eq]
  unfold MomentLaw.contourAverage
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show contourWeight L * MomentLaw.sumAlongWord W
    (pathToWord (blockCentreSite L c.1) (bondContour L k.1 k.2 c.2)) = _
  rw [sumAlongWord_pathToWord]
  rfl
private theorem torusCoordinate_of_tree {b : TorusBond (n * L)}
    (ht : IsAxialTreeBond (F := torusFrame L u n) (frameBond L u b))
    (V : (torusFrame L u n).GaugeField (torusFrame L u n).top) : torusCoordinate a ρ (frameBond L u b) V = 0 := by
  classical
  have hb : frameBond L u b ∉ chordBonds (finiteCells (torusFrame L u n)) := by
    intro h
    unfold chordBonds at h
    exact (Finset.mem_filter.1 h).2 ht
  unfold torusCoordinate minimizingBondCoordinate minimizingCoordinates
  split_ifs with h
  · exact h.choose_spec.1 _ hb
  · rfl
private theorem responseKernel_of_not_mem (P : StepHypotheses a ρ δ σA N0 Nn L u n) {b : TorusBond (n * L)}
    (hb : b ∉ chartBonds L n) (c : TorusBond n) : responseKernel a ρ L u b c = 0 := by
  classical
  have ht : IsAxialTreeBond (F := torusFrame L u n) (frameBond L u b) := by
    by_contra h
    exact hb ((mem_chartBonds_iff P.odd P.two_le b).2 h)
  have hz : bondDeriv (torusCoordinate a ρ (frameBond L u b))
      (uniformField (torusFrame L u n) (torusFrame L u n).top)
      ![(torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2)] ![unitGenerator] = 0 := by
    unfold bondDeriv
    rw [iteratedFDeriv_one_apply]
    have e : (fun τ : Fin 1 → ℝ => torusCoordinate a ρ (frameBond L u b)
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread
          ![(torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2)] ![unitGenerator] τ)
          (uniformField (torusFrame L u n) (torusFrame L u n).top))) = fun _ => 0 :=
      funext fun τ => torusCoordinate_of_tree ht _
    rw [e]
    simp
  have hc : ¬ (IsCrossingBond (F := torusFrame L u n) (frameBond L u b) ∧
      enclosingCell (frameBond L u b).1 = torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1 ∧
        b.2 = c.2) :=
    fun h => ht.1 h.1
  have h0 : -(((bondDeriv (torusCoordinate a ρ (frameBond L u b))
      (uniformField (torusFrame L u n) (torusFrame L u n).top)
      ![(torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2)] ![unitGenerator] :
        imaginaryQuaternions) : ℍ[ℝ]) * (unitGenerator : ℍ[ℝ])).re = 0 := by
    rw [hz]
    simp
  unfold responseKernel minimizerResponse
  exact (congrArg₂ (· + ·) h0 (if_neg hc)).trans (add_zero 0)
private theorem extendChart_of_not_mem (P : StepHypotheses a ρ δ σA N0 Nn L u n)
    (η : ↥(chordBonds (finiteCells (torusFrame L u n))) → ℝ) {c : TorusBond (n * L)} (hc : c ∉ chartBonds L n) :
    MomentLaw.extendChart η c = 0 := by
  classical
  have ht : IsAxialTreeBond (F := torusFrame L u n) (frameBond L u c) := by
    by_contra h
    exact hc ((mem_chartBonds_iff P.odd P.two_le c).2 h)
  unfold MomentLaw.extendChart
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [if_neg]
  intro h
  exact not_isAxialTreeBond b (show IsAxialTreeBond (F := torusFrame L u n) b.1 from h ▸ ht)
private theorem chartRestriction_extendChart (η : ↥(chordBonds (finiteCells (torusFrame L u n))) → ℝ) :
    chartRestriction L u n (MomentLaw.extendChart η) = η := by
  classical
  funext b
  rw [chartRestriction_apply]
  unfold MomentLaw.extendChart
  rw [Finset.sum_eq_single b]
  · exact if_pos (frameBond_torusBond b)
  · intro b' _ hb'
    rw [if_neg]
    intro h
    apply hb'
    apply Subtype.ext
    rw [← h]
    exact (frameBond_torusBond b)
  · simp
private theorem completed_square (P : StepHypotheses a ρ δ σA N0 Nn L u n)
    (hA : ContDiffAt ℝ 2 (colourAction a L u (m := n * L)) 0)
    (hA' : ContDiffAt ℝ 2 (colourAction a L (u + 1) (m := n)) 0) (Y : TorusBond n → ℝ)
    (η : ↥(chordBonds (finiteCells (torusFrame L u n))) → ℝ) :
    maxwellForm a L u (fun b => responseMap a ρ L u Y b + MomentLaw.extendChart η b)
        (fun b => responseMap a ρ L u Y b + MomentLaw.extendChart η b) +
      a * ∑ c : TorusBond n, (MomentLaw.contourAverage L
        (fun b => responseMap a ρ L u Y b + MomentLaw.extendChart η b) c - Y c) ^ 2 =
    maxwellForm a L (u + 1) Y Y + η ⬝ᵥ ((trivialHessian a L u n).mulVec η) := by
  have hoff : ∀ b, b ∉ chartBonds L n →
      (fun b => responseMap a ρ L u Y b + MomentLaw.extendChart η b) b = 0 := by
    intro b hb
    show responseMap a ρ L u Y b + MomentLaw.extendChart η b = 0
    rw [extendChart_of_not_mem P η hb, add_zero]
    unfold responseMap
    exact Finset.sum_eq_zero fun c _ => by rw [responseKernel_of_not_mem P hb c, zero_mul]
  have h := step_identity P hA hA' _ Y hoff
  have e : (fun b => responseMap a ρ L u Y b + MomentLaw.extendChart η b) - responseMap a ρ L u Y =
      MomentLaw.extendChart η := by
    funext b
    simp
  rw [e] at h
  unfold stepHessianForm at h
  rw [chartRestriction_extendChart] at h
  simp only [contourAverage_eq_slope]
  exact h
end Final
end CompletedSquare
open CompletedSquare
private theorem completedSquare_of_admissible (h1 : LevelAction.ActionSmoothAlongMoves)
    (h2 : LumpContours.ActionAtLevelIsCutAction) (h3 : LumpContours.WholeCellCostEqualsMinimalAction)
    (h4 : LumpContours.CutActionEqualsMinimalAction) (h5 : flatTopVanishingStatement)
    (h6 : chartEquivarianceStatement)
    (T : ParameterAssignment) (y : ℝ) (hD : T.Admissible) (u n : ℕ) [NeZero n] (hn : 64 ≤ n) (Y : TorusBond n → ℝ)
    (η : MomentLaw.ChartBondIndex (T.stepParameters y).side u n → ℝ) :
    maxwellForm T.coupling (T.stepParameters y).side u
        (fun b => responseMap T.coupling T.ρA (T.stepParameters y).side u Y b + MomentLaw.extendChart η b)
        (fun b => responseMap T.coupling T.ρA (T.stepParameters y).side u Y b + MomentLaw.extendChart η b) +
      T.coupling * ∑ c : TorusBond n, (MomentLaw.contourAverage (T.stepParameters y).side
        (fun b => responseMap T.coupling T.ρA (T.stepParameters y).side u Y b + MomentLaw.extendChart η b) c -
          Y c) ^ 2 =
    maxwellForm T.coupling (T.stepParameters y).side (u + 1) Y Y +
      η ⬝ᵥ ((trivialHessian T.coupling (T.stepParameters y).side u n).mulVec η) := by
  have hL : Odd T.side := hD.L_odd
  have ha : 0 < T.coupling := lt_of_lt_of_le one_pos hD.a_ge
  obtain ⟨-, -, -, hρ0, hρ1, hσ, -, -, hch⟩ := hD.chain
  have hchain := hD.chain
  obtain ⟨C, -, hC⟩ := h1 T.coupling T.δ₁ T.side T.lam T.ρA T.σA T.cg T.N ha hL hchain
  have hreg : ∀ {m : ℕ} [NeZero m], IsRegularRegion (Finset.univ : Finset (TorusSite m)) 1024 := fun z =>
    ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ _ _ _ _ _ => Finset.mem_univ _⟩
  have hcold : ∀ {m : ℕ} [NeZero m], IsColdOn T.σA (Finset.univ : Finset (TorusSite m)) (trivialField m) := by
    intro m _ p _
    have : curvature (trivialField m) p.1 p.2.1 p.2.2 = 0 := by simp [curvature, holonomy, trivialField]
    rw [this]
    exact hσ
  have hL64 : 64 ≤ n * T.side := by
    have : 1 ≤ T.side := Nat.pos_of_ne_zero (NeZero.ne T.side)
    nlinarith
  have hA : ContDiffAt ℝ 2 (colourAction T.coupling T.side u (m := n * T.side)) 0 :=
    contDiffAt_colourAction (hC u (n * T.side) hL64 _ _ hreg hcold).1
  have hA' : ContDiffAt ℝ 2 (colourAction T.coupling T.side (u + 1) (m := n)) 0 :=
    contDiffAt_colourAction (hC (u + 1) n hn _ _ hreg hcold).1
  have hamb : IsAdmissibleAmbient (torusFrame T.side u n) := Or.inr fun _ => hn
  have hreg' := isOrthantRegular_finiteCells (F := torusFrame T.side u n) (extent_pos T.side u n) 1024
  have hflat : IsCold (finiteCells (torusFrame T.side u n)) (torusFrame T.side u n).top T.σA
      (uniformField (torusFrame T.side u n) (torusFrame T.side u n).top) :=
    (h5 (torusFrame T.side u n) T.coupling _ ha.le hL).1 _ _ hσ
  have P : StepHypotheses T.coupling T.ρA T.δ₁ T.σA (T.N 0) T.N T.side u n :=
    { coupling_pos := ha
      odd := hL
      two_le := by omega
      radius_pos := hρ0
      radius_lt_pi := lt_of_le_of_lt hρ1 (by linarith [Real.pi_gt_three])
      threshold_pos := hσ
      unique := fun V hV =>
        (hch (torusFrame T.side u n) 1024 _ rfl hamb le_rfl hreg' T.σA V hσ le_rfl hV).1
      coordinates := (hch (torusFrame T.side u n) 1024 _ rfl hamb le_rfl hreg' T.σA _ hσ le_rfl hflat).2.2.2.1
      cutAction := h2
      wholeCellCost := h3
      cutMinimal := h4
      flatTop := h5
      equivariance := h6 }
  exact completed_square P hA hA' Y η
theorem completedSquareStatement_proof (h1 : LevelAction.ActionSmoothAlongMoves)
    (h2 : LumpContours.ActionAtLevelIsCutAction) (h3 : LumpContours.WholeCellCostEqualsMinimalAction)
    (h4 : LumpContours.CutActionEqualsMinimalAction) (h5 : flatTopVanishingStatement)
    (h6 : chartEquivarianceStatement) :
    completedSquareStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ T _ _ hD _ _ _ _
  refine ⟨0, fun y _ _ _ => ?_⟩
  intro u n _ hn Y η
  exact completedSquare_of_admissible h1 h2 h3 h4 h5 h6 T y hD u n hn Y η
end MomentLaw
end
end YangMills.Construction
