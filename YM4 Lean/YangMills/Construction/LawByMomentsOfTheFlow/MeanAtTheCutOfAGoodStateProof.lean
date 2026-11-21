import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheResponsesInALimitFieldProof
import YangMills.Construction.ColdChainAtEveryLevel.ChainsAtTheSameOffsets
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.LawByMomentsOfTheFlow.CompletedFormAcrossAStepProof
import YangMills.Construction.LawByMomentsOfTheFlow.MeanAtTheCutOfAGoodState
import YangMills.Construction.LawByMomentsOfTheFlow.MeansOfFormsAtAWeight
import YangMills.Construction.LawByMomentsOfTheFlow.TheCutOfAGoodState
import YangMills.Construction.LawByMomentsOfTheFlow.WhatTheMeansOfFormsRead
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
namespace CutoffMean
section TorusSites
variable {L n : ℕ} [NeZero L] [NeZero n]
omit [NeZero L] [NeZero n] in
private theorem period_one (i : Fin 4) : (TorusLumps.stepBlockFrame L n).period 1 i = n := by apply _root_.YangMills.Construction.BlockOffsets.period_one <;> assumption
private theorem toTorusSite_torusSiteInFrame (x : TorusFields.TorusSite n) :
    (TorusLumps.toTorusSite n (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 x :
      (TorusLumps.stepBlockFrame L n).Site 1) : TorusFields.TorusSite n) = x := by
  unfold StepCosts.torusSiteInFrame
  rw [TorusContours.toTorusSite_siteOfCoords period_one]
  funext k
  simp [TorusFields.siteOfInt]
omit [NeZero L] [NeZero n] in
private theorem readAtLevel_eq (W : TorusFields.TorusField n) (y : (TorusLumps.stepBlockFrame L n).Site 1)
    (i : Fin 4) :
    TorusFields.readAtLevel (TorusLumps.stepBlockFrame L n) 1 W y i = W (TorusLumps.toTorusSite n y) i := rfl
omit [NeZero L] [NeZero n] in
private theorem siteOfCoords_offset (Y z : (TorusLumps.stepBlockFrame L n).Cell) :
    (BlockAverages.siteOfCoords 1 (ColdStepAtMirrorFrames.minimalOffset Y z) :
      (TorusLumps.stepBlockFrame L n).Site 1) = z - Y := by
  funext k
  exact ZMod.coe_valMinAbs _
private theorem cellCentre_first (Y : (TorusLumps.stepBlockFrame L n).Cell) :
    (BlockAverages.cellCentre 1 Y : (TorusLumps.stepBlockFrame L n).Site 1) = Y := by
  have : (fun i => ((TorusLumps.stepBlockFrame L n).blockSide : ℤ) ^ ((TorusLumps.stepBlockFrame L n).top - 1) *
      BlockAverages.siteCoords Y i) = BlockAverages.siteCoords Y := by
    funext i
    simp [TorusLumps.stepBlockFrame, BlockAverages.BlockFrame.top]
  unfold BlockAverages.cellCentre
  rw [this]
  exact TorusContours.siteOfCoords_siteCoords Y
private theorem natAbs_offset_le (o z : TorusFields.TorusSite n) (k : Fin 4) :
    (ColdStepAtMirrorFrames.minimalOffset (F := TorusLumps.stepBlockFrame L n)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 o)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 z) k).natAbs ≤ TorusFields.supDist z o := by
  have e : (TorusFields.siteOfInt (ColdStepAtMirrorFrames.minimalOffset (F := TorusLumps.stepBlockFrame L n)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 o)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 z)) : TorusFields.TorusSite n) + o = z := by
    have h0 := siteOfCoords_offset (L := L) (n := n) (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 o)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 z)
    rw [← TorusContours.toTorusSite_siteOfCoords (F := TorusLumps.stepBlockFrame L n) (j := 1) period_one]
    calc _ = TorusLumps.toTorusSite n ((StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 z -
            StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 o : (TorusLumps.stepBlockFrame L n).Site 1)) +
          TorusLumps.toTorusSite n (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 o :
            (TorusLumps.stepBlockFrame L n).Site 1) := by
          rw [toTorusSite_torusSiteInFrame]
          exact congrArg (fun y : (TorusLumps.stepBlockFrame L n).Site 1 =>
            (TorusLumps.toTorusSite n y : TorusFields.TorusSite n) + o) h0
      _ = z := by
          rw [← TorusContours.toTorusSite_add (F := TorusLumps.stepBlockFrame L n) (j := 1) period_one, sub_add_cancel,
            toTorusSite_torusSiteInFrame]
  have e2 : ((ColdStepAtMirrorFrames.minimalOffset (F := TorusLumps.stepBlockFrame L n)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 o)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 1 z) k : ℤ) : ZMod n) =
      (((z k - o k).valMinAbs : ℤ) : ZMod n) := by
    have := congrFun e k
    simp only [Pi.add_apply, TorusFields.siteOfInt] at this
    rw [ZMod.coe_valMinAbs, ← this]
    ring
  have h2 : (TorusLumps.stepBlockFrame L n).period 1 k / 2 = n / 2 := by rw [period_one k]
  have h3 := ZMod.natAbs_min_of_le_div_two n _ _ e2
    ((ZMod.natAbs_valMinAbs_le _).trans h2.le)
  exact h3.trans (Finset.le_sup (f := fun i => ((z i - o i).valMinAbs).natAbs) (Finset.mem_univ k))
private theorem axialGaugeAt_gaugeTransform (ℓ : TorusLumps.StepParameters) {n : ℕ} [NeZero n]
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (W : TorusFields.TorusField n)
    (o z : TorusFields.TorusSite n) :
    ResponseInTheExpansion.axialGaugeAt ℓ (TorusFields.gaugeTransform g W) o z =
      g o * ResponseInTheExpansion.axialGaugeAt ℓ W o z * (g z)⁻¹ := by
  have h1 : TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 (TorusFields.gaugeTransform g W) =
      BlockAverages.gaugeTransform (fun y => g (TorusLumps.toTorusSite n y))
        (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 W) := by
    funext x i
    simp only [BlockAverages.gaugeTransform, readAtLevel_eq, TorusFields.gaugeTransform,
      TorusContours.toTorusSite_add (F := TorusLumps.stepBlockFrame ℓ.side n) (j := 1) period_one,
      TorusContours.toTorusSite_unitStep (F := TorusLumps.stepBlockFrame ℓ.side n) (j := 1) period_one]
  have h0 := siteOfCoords_offset (L := ℓ.side) (n := n)
    (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o)
    (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 z)
  have e := TorusContours.pathHolonomy_gaugeTransform (F := TorusLumps.stepBlockFrame ℓ.side n) (j := 1)
    (fun y => g (TorusLumps.toTorusSite n y))
    (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 W)
    (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o)
    (BlockAverages.axisPath (ColdStepAtMirrorFrames.minimalOffset (F := TorusLumps.stepBlockFrame ℓ.side n)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 z)) 1)
  have e1 := TorusContours.pathEndpoint_axisPath (F := TorusLumps.stepBlockFrame ℓ.side n) (j := 1)
    (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o)
    (ColdStepAtMirrorFrames.minimalOffset (F := TorusLumps.stepBlockFrame ℓ.side n)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 z)) 1
  have e2 : (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o +
      BlockAverages.siteOfCoords 1 (ColdStepAtMirrorFrames.minimalOffset (F := TorusLumps.stepBlockFrame ℓ.side n)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 z)) :
        (TorusLumps.stepBlockFrame ℓ.side n).Site 1) =
      StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 z :=
    (congrArg (fun y : (TorusLumps.stepBlockFrame ℓ.side n).Site 1 =>
      StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o + y) h0).trans (add_sub_cancel _ _)
  rw [e1, e2, toTorusSite_torusSiteInFrame, toTorusSite_torusSiteInFrame, ← h1] at e
  exact e
private theorem gaugeTransform_axial (ℓ : TorusLumps.StepParameters) {n : ℕ} [NeZero n]
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (W : TorusFields.TorusField n)
    (o : TorusFields.TorusSite n) (b : TorusFields.TorusBond n) :
    ResponseInTheExpansion.gaugeTransform (ResponseInTheExpansion.axialGaugeAt ℓ (TorusFields.gaugeTransform g W) o)
        (TorusFields.gaugeTransform g W) b =
      g o * ResponseInTheExpansion.gaugeTransform (ResponseInTheExpansion.axialGaugeAt ℓ W o) W b * (g o)⁻¹ := by
  unfold ResponseInTheExpansion.gaugeTransform
  rw [axialGaugeAt_gaugeTransform, axialGaugeAt_gaugeTransform]
  simp only [TorusFields.gaugeTransform]
  group
private theorem axialGaugeAt_congr (ℓ : TorusLumps.StepParameters) {n : ℕ} [NeZero n]
    (W W' : TorusFields.TorusField n) (o z : TorusFields.TorusSite n) (R : ℕ)
    (hz : TorusFields.supDist z o ≤ R)
    (hW : ∀ c : TorusFields.TorusBond n, TorusFields.supDist c.1 o ≤ R →
      TorusFields.supDist (c.1 + TorusFields.unitStep n c.2) o ≤ R → W c.1 c.2 = W' c.1 c.2) :
    ResponseInTheExpansion.axialGaugeAt ℓ W o z = ResponseInTheExpansion.axialGaugeAt ℓ W' o z := by
  set Y : (TorusLumps.stepBlockFrame ℓ.side n).Cell :=
    StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 o with hY
  set Z : (TorusLumps.stepBlockFrame ℓ.side n).Cell :=
    StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 z with hZ
  set h := ColdStepAtMirrorFrames.minimalOffset Y Z with hh
  have hb : ∀ k, (h k).natAbs ≤ R := fun k => (natAbs_offset_le o z k).trans hz
  have hd : ∀ p : Fin 4 → ℤ, LatticePaths.BetweenOrigin h p →
      TorusFields.supDist (o + TorusFields.siteOfInt p) o ≤ R := by
    intro p hp
    rw [TorusFields.supDist_comm]
    refine TorusFields.supDist_add_siteOfInt_le o p R fun k => ?_
    have h1 := hb k
    have h2 := hp k
    rcases le_total 0 (h k) with h3 | h3
    · rw [min_eq_left h3, max_eq_right h3] at h2
      omega
    · rw [min_eq_right h3, max_eq_left h3] at h2
      omega
  have hat : ∀ p : Fin 4 → ℤ, (TorusLumps.toTorusSite n (BlockAverages.SameOffsets.siteAtOffset Y 1 p) :
      TorusFields.TorusSite n) = o + TorusFields.siteOfInt p := by
    intro p
    unfold BlockAverages.SameOffsets.siteAtOffset
    rw [cellCentre_first, TorusContours.toTorusSite_add (F := TorusLumps.stepBlockFrame ℓ.side n) (j := 1) period_one,
      TorusContours.toTorusSite_siteOfCoords (F := TorusLumps.stepBlockFrame ℓ.side n) (j := 1) period_one,
      toTorusSite_torusSiteInFrame]
  have H : ∀ (p : Fin 4 → ℤ) (i : Fin 4), LatticePaths.BetweenOrigin h p →
      LatticePaths.BetweenOrigin h (p + LatticeFractionalIntegration.basisVector i) →
      TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 W
          (BlockAverages.SameOffsets.siteAtOffset Y 1 p) i =
        TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 W'
          (BlockAverages.SameOffsets.siteAtOffset Y 1 p) i := by
    intro p i h1 h2
    rw [readAtLevel_eq, readAtLevel_eq, hat]
    refine hW (o + TorusFields.siteOfInt p, i) (hd p h1) ?_
    have e : (o + TorusFields.siteOfInt p + TorusFields.unitStep n i : TorusFields.TorusSite n) =
        o + TorusFields.siteOfInt (p + LatticeFractionalIntegration.basisVector i) := by
      rw [TorusFields.siteOfInt_add, add_assoc]
      congr 2
      exact (TorusContours.siteOfInt_single i).symm
    show TorusFields.supDist (o + TorusFields.siteOfInt p + TorusFields.unitStep n i) o ≤ R
    rw [e]
    exact hd _ h2
  have := BlockAverages.SameOffsets.pathHolonomy_eq_of_agree H _ 0 (LatticePaths.axisPath_spec h 1).1
  have e0 : BlockAverages.SameOffsets.siteAtOffset Y 1 0 = Y := by
    unfold BlockAverages.SameOffsets.siteAtOffset
    rw [cellCentre_first]
    have e1 : (BlockAverages.siteOfCoords 1 (0 : Fin 4 → ℤ) : (TorusLumps.stepBlockFrame ℓ.side n).Site 1) = 0 := by
      funext k
      exact Int.cast_zero
    rw [e1, add_zero]
  rw [e0] at this
  exact this
end TorusSites
section ColourRotations
private def quaternionRotation (a b c d : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2, 2 * (b * c - a * d), 2 * (b * d + a * c);
     2 * (b * c + a * d), a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2, 2 * (c * d - a * b);
     2 * (b * d - a * c), 2 * (c * d + a * b), a ^ 2 - b ^ 2 - c ^ 2 + d ^ 2]
private theorem quaternionRotation_mem (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    quaternionRotation a b c d ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionRotation, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
      | linear_combination (0 : ℝ) * h
      | linear_combination (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + 1) * h
private def adjointRotation (u : BlockAverages.UnitQuaternion) : Matrix (Fin 3) (Fin 3) ℝ :=
  quaternionRotation (u : ℍ[ℝ]).re (u : ℍ[ℝ]).imI (u : ℍ[ℝ]).imJ (u : ℍ[ℝ]).imK
private theorem adjointRotation_mem (u : BlockAverages.UnitQuaternion) :
    adjointRotation u ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  refine quaternionRotation_mem _ _ _ _ ?_
  have := TorusFields.normSq_unitQuaternion u
  rw [Quaternion.normSq_def'] at this
  exact this
private theorem imaginaryComponent_adjointAction (u : BlockAverages.UnitQuaternion) (e : Fin 3)
    (X : BlockAverages.imaginaryQuaternions) :
    BlockAverages.imaginaryComponent e (ColdStepAtMirrorFrames.adjointAction u X) =
      ∑ e' : Fin 3, adjointRotation u e e' * BlockAverages.imaginaryComponent e' X := by
  have hX : (X : ℍ[ℝ]).re = 0 := X.2
  have hc : ((ColdStepAtMirrorFrames.adjointAction u X : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) =
      (u : ℍ[ℝ]) * (X : ℍ[ℝ]) * star (u : ℍ[ℝ]) := by
    show (u : ℍ[ℝ]) * (X : ℍ[ℝ]) * ((u⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) = _
    rw [TorusFields.coe_inv_unitQuaternion]
  fin_cases e <;>
    simp [BlockAverages.imaginaryComponent, hc, adjointRotation, quaternionRotation, Fin.sum_univ_three, hX] <;> ring
private theorem imaginaryComponent_smul (e : Fin 3) (c : ℝ) (w : BlockAverages.imaginaryQuaternions) :
    BlockAverages.imaginaryComponent e (c • w) = c * BlockAverages.imaginaryComponent e w := by
  fin_cases e <;> simp [BlockAverages.imaginaryComponent]
private theorem axialCoords_gaugeTransform (ℓ : TorusLumps.StepParameters) {n : ℕ} [NeZero n]
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (W : TorusFields.TorusField n)
    (o : TorusFields.TorusSite n) (b : TorusFields.TorusBond n)
    (h : ResponseInTheExpansion.gaugeTransform (ResponseInTheExpansion.axialGaugeAt ℓ W o) W b ≠ -1) :
    MomentLaw.axialCoords ℓ (TorusFields.gaugeTransform g W) o b =
      ColdStepAtMirrorFrames.adjointAction (g o) (MomentLaw.axialCoords ℓ W o b) := by
  unfold MomentLaw.axialCoords
  rw [gaugeTransform_axial]
  exact Subtype.ext (QuaternionLog.coe_minimalLog_conj _ _ h)
private theorem toColourForm_cutoffCoords_gaugeTransform (ℓ : TorusLumps.StepParameters) {n : ℕ} [NeZero n]
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (W : TorusFields.TorusField n)
    (o : TorusFields.TorusSite n) (m : ℕ)
    (h : ∀ b : TorusFields.TorusBond n, MomentLaw.cutoffProfile o m b.1 ≠ 0 →
      ResponseInTheExpansion.gaugeTransform (ResponseInTheExpansion.axialGaugeAt ℓ W o) W b ≠ -1)
    (e : Fin 3) (b : TorusFields.TorusBond n) :
    MomentLaw.toColourForm (MomentLaw.cutoffCoords ℓ (TorusFields.gaugeTransform g W) o m) e b =
      ∑ e' : Fin 3, adjointRotation (g o) e e' * MomentLaw.toColourForm (MomentLaw.cutoffCoords ℓ W o m) e' b := by
  simp only [MomentLaw.toColourForm, MomentLaw.cutoffCoords, imaginaryComponent_smul]
  by_cases h0 : MomentLaw.cutoffProfile o m b.1 = 0
  · simp [h0]
  · rw [axialCoords_gaugeTransform ℓ g W o b (h b h0), imaginaryComponent_adjointAction, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e' _ => ?_
    ring
private theorem supDist_add_two_le_of_cutoffProfile_ne_zero {n : ℕ} [NeZero n] (o z : TorusFields.TorusSite n)
    (m : ℕ) (hm : 2 ≤ m) (h : MomentLaw.cutoffProfile o m z ≠ 0) :
    TorusFields.supDist z o + 2 ≤ 2 * m := by
  by_contra hc
  apply h
  have h1 : 2 * (m : ℝ) - 1 ≤ (TorusFields.supDist z o : ℝ) := by
    have : 2 * m ≤ TorusFields.supDist z o + 1 := by omega
    have h2 : (2 * m : ℝ) ≤ (TorusFields.supDist z o : ℝ) + 1 := by exact_mod_cast this
    linarith
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  unfold MomentLaw.cutoffProfile
  have h3 : (2 * (m : ℝ) - 1 - (TorusFields.supDist z o : ℝ)) / ((m : ℝ) - 1) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hm1.le
  exact max_eq_left ((min_le_right _ _).trans h3)
private theorem supDist_add_unitStep_le {n : ℕ} [NeZero n] (z o : TorusFields.TorusSite n) (i : Fin 4) :
    TorusFields.supDist (z + TorusFields.unitStep n i) o ≤ TorusFields.supDist z o + 1 := by apply _root_.YangMills.SharedProofs.p13239 <;> assumption
private theorem axialCoords_congr (ℓ : TorusLumps.StepParameters) {n : ℕ} [NeZero n]
    (W W' : TorusFields.TorusField n) (o : TorusFields.TorusSite n) (b : TorusFields.TorusBond n) (R : ℕ)
    (h1 : TorusFields.supDist b.1 o ≤ R) (h2 : TorusFields.supDist (b.1 + TorusFields.unitStep n b.2) o ≤ R)
    (hW : ∀ c : TorusFields.TorusBond n, TorusFields.supDist c.1 o ≤ R →
      TorusFields.supDist (c.1 + TorusFields.unitStep n c.2) o ≤ R → W c.1 c.2 = W' c.1 c.2) :
    MomentLaw.axialCoords ℓ W o b = MomentLaw.axialCoords ℓ W' o b := by
  unfold MomentLaw.axialCoords ResponseInTheExpansion.gaugeTransform
  rw [axialGaugeAt_congr ℓ W W' o b.1 R h1 hW, axialGaugeAt_congr ℓ W W' o _ R h2 hW, hW b h1 h2]
private theorem toColourForm_cutoffCoords_congr (ℓ : TorusLumps.StepParameters) {n : ℕ} [NeZero n]
    (W W' : TorusFields.TorusField n) (o : TorusFields.TorusSite n) (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 2 * m ≤ R)
    (hW : ∀ c : TorusFields.TorusBond n, TorusFields.supDist c.1 o ≤ R →
      TorusFields.supDist (c.1 + TorusFields.unitStep n c.2) o ≤ R → W c.1 c.2 = W' c.1 c.2) :
    MomentLaw.toColourForm (MomentLaw.cutoffCoords ℓ W o m) =
      MomentLaw.toColourForm (MomentLaw.cutoffCoords ℓ W' o m) := by
  funext e b
  simp only [MomentLaw.toColourForm, MomentLaw.cutoffCoords]
  by_cases h0 : MomentLaw.cutoffProfile o m b.1 = 0
  · simp [h0]
  · have h1 := supDist_add_two_le_of_cutoffProfile_ne_zero o b.1 m hm h0
    have h2 := supDist_add_unitStep_le b.1 o b.2
    rw [axialCoords_congr ℓ W W' o b R (by omega) (by omega) hW]
end ColourRotations
section GaugeFields
variable {n : ℕ} [NeZero n]
private theorem boxCurvature_gaugeTransform (o : TorusFields.TorusSite n) (r : ℝ)
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (W : TorusFields.TorusField n) :
    MomentLaw.boxCurvature o r (TorusFields.gaugeTransform g W) = MomentLaw.boxCurvature o r W := by
  simp only [MomentLaw.boxCurvature, TorusFields.curvature_gaugeTransform]
private theorem boxCurvature_congr (o : TorusFields.TorusSite n) (r : ℝ) (W W' : TorusFields.TorusField n)
    (h : ∀ c : TorusFields.TorusBond n, c.1 ∈ ResponseInTheExpansion.supBall o r →
      c.1 + TorusFields.unitStep n c.2 ∈ ResponseInTheExpansion.supBall o r → W c.1 c.2 = W' c.1 c.2) :
    MomentLaw.boxCurvature o r W = MomentLaw.boxCurvature o r W' := by
  unfold MomentLaw.boxCurvature
  congr 1
  funext p
  obtain ⟨⟨x, μ, ν⟩, hlt, hc⟩ := p
  have c1 : x ∈ ResponseInTheExpansion.supBall o r := hc x (by simp [TorusFields.plaquetteVertices])
  have c2 : x + TorusFields.unitStep n μ ∈ ResponseInTheExpansion.supBall o r :=
    hc _ (by simp [TorusFields.plaquetteVertices])
  have c3 : x + TorusFields.unitStep n ν ∈ ResponseInTheExpansion.supBall o r :=
    hc _ (by simp [TorusFields.plaquetteVertices])
  have c4 : x + TorusFields.unitStep n μ + TorusFields.unitStep n ν ∈ ResponseInTheExpansion.supBall o r :=
    hc _ (by simp [TorusFields.plaquetteVertices])
  have c5 : x + TorusFields.unitStep n ν + TorusFields.unitStep n μ ∈ ResponseInTheExpansion.supBall o r := by
    rwa [add_right_comm]
  show TorusFields.curvature W x μ ν = TorusFields.curvature W' x μ ν
  unfold TorusFields.curvature TorusFields.holonomy
  rw [h (x, μ) c1 c2, h (x + TorusFields.unitStep n μ, ν) c2 c4, h (x + TorusFields.unitStep n ν, μ) c3 c5,
    h (x, ν) c1 c3]
private theorem continuous_pathHolonomy (F : BlockAverages.BlockFrame) (j : ℕ) (x : F.Site j)
    (l : List BlockAverages.PathStep) :
    Continuous fun X : F.GaugeField j => BlockAverages.pathHolonomy X x l := by apply _root_.YangMills.Construction.MarkedIntegrals.MarkedIntegralIdentity.continuous_pathHolonomy <;> assumption
omit [NeZero n] in
private theorem continuous_axialGaugeAt (ℓ : TorusLumps.StepParameters) (o z : TorusFields.TorusSite n) :
    Continuous fun W : TorusFields.TorusField n => ResponseInTheExpansion.axialGaugeAt ℓ W o z := by
  have h1 : Continuous fun W : TorusFields.TorusField n =>
      TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 W :=
    continuous_pi fun x => continuous_pi fun i => continuous_apply_apply _ i
  exact (continuous_pathHolonomy (TorusLumps.stepBlockFrame ℓ.side n) 1 _ _).comp h1
omit [NeZero n] in
private theorem continuous_gaugeTransform_axial (ℓ : TorusLumps.StepParameters) (o : TorusFields.TorusSite n)
    (b : TorusFields.TorusBond n) :
    Continuous fun W : TorusFields.TorusField n =>
      ResponseInTheExpansion.gaugeTransform (ResponseInTheExpansion.axialGaugeAt ℓ W o) W b := by
  unfold ResponseInTheExpansion.gaugeTransform
  exact ((continuous_axialGaugeAt ℓ o _).mul (continuous_apply_apply b.1 b.2)).mul
    (continuous_axialGaugeAt ℓ o _).inv
private theorem measurable_toColourForm_cutoffCoords (ℓ : TorusLumps.StepParameters) (o : TorusFields.TorusSite n)
    (m : ℕ)
    (hL : TorusLumps.MeasurableQuaternion
      (fun g : BlockAverages.UnitQuaternion =>
        ((LumpContours.minimalLog g : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]))) :
    Measurable fun W : TorusFields.TorusField n => MomentLaw.toColourForm (MomentLaw.cutoffCoords ℓ W o m) := by
  refine measurable_pi_iff.2 fun e => measurable_pi_iff.2 fun b => ?_
  simp only [MomentLaw.toColourForm, MomentLaw.cutoffCoords, imaginaryComponent_smul]
  refine measurable_const.mul ?_
  have hg : Measurable fun W : TorusFields.TorusField n =>
      ResponseInTheExpansion.gaugeTransform (ResponseInTheExpansion.axialGaugeAt ℓ W o) W b :=
    (continuous_gaugeTransform_axial ℓ o b).measurable
  obtain ⟨-, h1, h2, h3⟩ := hL
  fin_cases e
  · exact h1.comp hg
  · exact h2.comp hg
  · exact h3.comp hg
private theorem measurable_boxCurvature (o : TorusFields.TorusSite n) (r : ℝ) :
    Measurable (MomentLaw.boxCurvature (n := n) o r) := by apply _root_.YangMills.DeltaSharedProofs.p12736 <;> assumption
end GaugeFields
section FormMeans
private theorem forAllParameters_and {Q₁ Q₂ : MomentLaw.MomentParameters → Prop}
    (h₁ : MomentLaw.ForAllParameters Q₁) (h₂ : MomentLaw.ForAllParameters Q₂) :
    MomentLaw.ForAllParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_mono {Q₁ Q₂ : MomentLaw.MomentParameters → Prop}
    (h₁ : MomentLaw.ForAllParameters Q₁) (h : ∀ Λ, Q₁ Λ → Q₂ Λ) : MomentLaw.ForAllParameters Q₂ := by apply _root_.YangMills.SharedProofs.p9549 <;> assumption
private theorem weightRate_pos : MomentLaw.ForAllParameters fun Λ => 0 < Λ.stepParams.weightRate := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hD _ _ _ _ _ _
  refine ⟨0, fun y _ _ _ g _ _ k _ _ _ R d _ => ?_⟩
  have h := hD.rt_pos
  show 0 < (Tb.stepParameters y).rt / 2 ^ 10
  have e : (Tb.stepParameters y).rt = Tb.rt := rfl
  rw [e]
  positivity
abbrev _root_.YangMills.SharedProofs.p57148 := @weightRate_pos
variable {n : ℕ} [NeZero n]
private def totalCurl (X : MomentLaw.ColourForm n) : ℝ :=
  ∑ p : WeightedResponses.OrientedPlaquette n, MomentLaw.curlNorm X p.1
private theorem curlNorm_le_totalCurl (X : MomentLaw.ColourForm n) (p : WeightedResponses.OrientedPlaquette n) :
    MomentLaw.curlNorm X p.1 ≤ totalCurl X :=
  Finset.single_le_sum (f := fun p : WeightedResponses.OrientedPlaquette n => MomentLaw.curlNorm X p.1)
    (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ p)
private theorem totalCurl_nonneg (X : MomentLaw.ColourForm n) : 0 ≤ totalCurl X :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
private theorem continuous_totalCurl : Continuous (totalCurl (n := n)) := by
  unfold totalCurl MomentLaw.curlNorm WeightedResponses.curl
  refine continuous_finsetSum _ fun p _ => Real.continuous_sqrt.comp (continuous_finsetSum _ fun e _ => ?_)
  have h : ∀ c : TorusFields.TorusBond n, Continuous fun X : MomentLaw.ColourForm n => X e c :=
    fun c => continuous_apply_apply e c
  exact ((((h _).add (h _)).sub (h _)).sub (h _)).pow 2
private theorem totalCurl_zero : totalCurl (0 : MomentLaw.ColourForm n) = 0 := by
  unfold totalCurl MomentLaw.curlNorm WeightedResponses.curl
  simp
omit [NeZero n] in
private theorem weightedCurvatureNorm_dirac_le (ω : TorusFields.TorusPlaquette n → ℝ) (hω : ∀ p, ω p ≤ 1)
    (q : ENNReal) (hq : q ≠ 0) (X : MomentLaw.ColourForm n) (K : ℝ)
    (hK : ∀ p : WeightedResponses.OrientedPlaquette n, MomentLaw.curlNorm X p.1 ≤ K) :
    MomentLaw.weightedCurvatureNorm (Measure.dirac ()) ω q (fun _ : Unit => X) ≤ ENNReal.ofReal K := by
  refine iSup_le fun p => ?_
  have h1 : ENNReal.ofReal (ω p.1) ≤ 1 := ENNReal.ofReal_le_one.2 (hω _)
  have h2 : eLpNorm (fun _ : Unit => MomentLaw.curlNorm X p.1) q (Measure.dirac ()) ≤ ENNReal.ofReal K := by
    rw [eLpNorm_const _ hq (NeZero.ne _), measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (show 0 ≤ MomentLaw.curlNorm X p.1 from Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hK p)
  calc _ ≤ 1 * ENNReal.ofReal K := mul_le_mul' h1 h2
    _ = _ := one_mul _
private theorem ofReal_bound_mul (a K h K₁ K₂ : ℝ) (e : ℕ) (ha : 0 ≤ a) (hK : 0 ≤ K) (hh : 0 ≤ h) (h₁ : 0 ≤ K₁)
    (h₂ : 0 ≤ K₂) :
    ENNReal.ofReal a * ENNReal.ofReal K * (1 + ENNReal.ofReal h * (ENNReal.ofReal K₁ + ENNReal.ofReal K₂)) ^ e =
      ENNReal.ofReal (a * K * (1 + h * (K₁ + K₂)) ^ e) := by
  have h3 : 0 ≤ h * (K₁ + K₂) := by positivity
  rw [← ENNReal.ofReal_add h₁ h₂, ← ENNReal.ofReal_mul hh, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one h3, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul ha,
    ← ENNReal.ofReal_mul (by positivity)]
private theorem bounds_of_dirac (p : MomentLaw.ColourForm n → ℝ) (ω : TorusFields.TorusPlaquette n → ℝ)
    (hω : ∀ p, ω p ≤ 1) (q : ENNReal) (hq : q ≠ 0) (c h : ℝ) (hh : 0 ≤ h) (e e' : ℕ)
    (H₁ : ∀ A A' : Unit → MomentLaw.ColourForm n, ∫⁻ w, ENNReal.ofReal |p (A w)| ∂(Measure.dirac ()) ≤
      ENNReal.ofReal c * (1 + ENNReal.ofReal h * (MomentLaw.weightedCurvatureNorm (Measure.dirac ()) ω q A +
        MomentLaw.weightedCurvatureNorm (Measure.dirac ()) ω q A')) ^ e)
    (H₃ : ∀ A A' : Unit → MomentLaw.ColourForm n, ∫⁻ w, ENNReal.ofReal |p (A w) - p (A' w)| ∂(Measure.dirac ()) ≤
      ENNReal.ofReal (c * h) * MomentLaw.weightedCurvatureNorm (Measure.dirac ()) ω q (fun w => A w - A' w) *
        (1 + ENNReal.ofReal h * (MomentLaw.weightedCurvatureNorm (Measure.dirac ()) ω q A +
          MomentLaw.weightedCurvatureNorm (Measure.dirac ()) ω q A')) ^ e') :
    (∀ (X : MomentLaw.ColourForm n) (K : ℝ), 0 ≤ K →
      (∀ p : WeightedResponses.OrientedPlaquette n, MomentLaw.curlNorm X p.1 ≤ K) →
      |p X| ≤ |c| * (1 + h * (K + K)) ^ e) ∧ Continuous p := by
  have hc : 0 ≤ |c| := abs_nonneg c
  constructor
  · intro X K hK0 hK
    have h1 := H₁ (fun _ => X) (fun _ => X)
    rw [lintegral_dirac] at h1
    have hN := weightedCurvatureNorm_dirac_le ω hω q hq X K hK
    have h2 : ENNReal.ofReal |p X| ≤ ENNReal.ofReal (|c| * 1 * (1 + h * (K + K)) ^ e) := by
      rw [← ofReal_bound_mul _ _ _ _ _ _ hc zero_le_one hh hK0 hK0, ENNReal.ofReal_one, mul_one]
      refine h1.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_abs_self c)) ?_)
      gcongr
    have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
    simpa using h3
  · have hlip : ∀ X X' : MomentLaw.ColourForm n, |p X - p X'| ≤
        (|c| * h) * totalCurl (X - X') * (1 + h * (totalCurl X + totalCurl X')) ^ e' := by
      intro X X'
      have h1 := H₃ (fun _ => X) (fun _ => X')
      rw [lintegral_dirac] at h1
      have hN := weightedCurvatureNorm_dirac_le ω hω q hq X _ (curlNorm_le_totalCurl X)
      have hN' := weightedCurvatureNorm_dirac_le ω hω q hq X' _ (curlNorm_le_totalCurl X')
      have hD := weightedCurvatureNorm_dirac_le ω hω q hq (X - X') _ (curlNorm_le_totalCurl (X - X'))
      have h2 : ENNReal.ofReal |p X - p X'| ≤
          ENNReal.ofReal ((|c| * h) * totalCurl (X - X') * (1 + h * (totalCurl X + totalCurl X')) ^ e') := by
        rw [← ofReal_bound_mul _ _ _ _ _ _ (by positivity) (totalCurl_nonneg _) hh (totalCurl_nonneg _)
          (totalCurl_nonneg _)]
        refine h1.trans (mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) hD) ?_)
        · exact mul_le_mul_of_nonneg_right (le_abs_self c) hh
        · gcongr
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (by positivity) (totalCurl_nonneg _))
        (pow_nonneg (add_nonneg zero_le_one (mul_nonneg hh (add_nonneg (totalCurl_nonneg _)
          (totalCurl_nonneg _)))) _))).1 h2
    refine continuous_iff_continuousAt.2 fun X₀ => ?_
    have hG : Continuous fun X : MomentLaw.ColourForm n =>
        (|c| * h) * totalCurl (X - X₀) * (1 + h * (totalCurl X + totalCurl X₀)) ^ e' :=
      ((continuous_const.mul (continuous_totalCurl.comp (continuous_id.sub continuous_const))).mul
        ((continuous_const.add (continuous_const.mul (continuous_totalCurl.add continuous_const))).pow _))
    have h0 := hG.tendsto X₀
    simp only [sub_self, totalCurl_zero, mul_zero, zero_mul] at h0
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun X => ?_) h0)
    exact hlip X X₀
end FormMeans
section LargeCoupling
private theorem hundred_le_rpow (x : ℝ) (hx : (10 : ℝ) ^ 200 ≤ x) : 100 ≤ x ^ ((1 : ℝ) / 100) := by
  have h0 : (0 : ℝ) ≤ 100 := by norm_num
  have h1 : ((100 : ℝ) ^ (100 : ℕ)) ≤ x := by
    refine le_trans (le_of_eq ?_) hx
    norm_num
  have h2 := Real.rpow_le_rpow (by positivity) h1 (show (0 : ℝ) ≤ 1 / 100 by norm_num)
  have h3 : ((100 : ℝ) ^ (100 : ℕ)) ^ ((1 : ℝ) / 100) = 100 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
    norm_num
  rwa [h3] at h2
private theorem clusterRange_bounds (x : ℝ) (hx : (10 : ℝ) ^ 200 ≤ x) :
    2 ≤ TorusLumps.clusterRange x ∧
      8 * ((TorusLumps.clusterRange x : ℝ) ^ 2) * x ^ (-(1 / 4) : ℝ) < 3 ∧
      x ^ ((1 : ℝ) / 2) * x ^ (-(1 / 4) : ℝ) = x ^ ((1 : ℝ) / 4) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  set w := x ^ ((1 : ℝ) / 100) with hw
  have hw1 : 100 ≤ w := hundred_le_rpow x hx
  have hr1 : w ≤ (TorusLumps.clusterRange x : ℝ) := Nat.le_ceil _
  have hr2 : (TorusLumps.clusterRange x : ℝ) < w + 1 := Nat.ceil_lt_add_one (by linarith)
  have hq : x ^ ((1 : ℝ) / 4) = w ^ 25 := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hn : x ^ (-(1 / 4) : ℝ) = (w ^ 25)⁻¹ := by
    rw [Real.rpow_neg hx0.le, ← hq]
  refine ⟨?_, ?_, ?_⟩
  · have : (2 : ℝ) ≤ (TorusLumps.clusterRange x : ℝ) := by linarith
    exact_mod_cast this
  · have hp : 0 < w ^ 25 := by positivity
    rw [hn, ← div_eq_mul_inv, div_lt_iff₀ hp]
    have h3 : w ^ 3 ≤ w ^ 25 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h4 : (TorusLumps.clusterRange x : ℝ) ^ 2 ≤ (w + 1) ^ 2 := pow_le_pow_left₀ (by linarith) hr2.le 2
    nlinarith [sq_nonneg w, mul_nonneg (sq_nonneg w) (show (0 : ℝ) ≤ w - 100 by linarith)]
  · rw [← Real.rpow_add hx0]
    norm_num
end LargeCoupling
end CutoffMean
open CutoffMean in
theorem cutoffMeanBoundsStatement_holds (hCut : MomentLaw.goodConfigCutoffStatement)
    (hMeans : MomentLaw.formMeansAtWeightStatement) (hRead : MomentLaw.formMeansStatement)
    (hBorel : ResponseInTheExpansion.chainMeasurabilityStatement) :
    MomentLaw.cutoffMeanBoundsStatement := by
  obtain ⟨-, hLog, -⟩ := hBorel
  unfold MomentLaw.goodConfigCutoffStatement MomentLaw.ForAllPoints at hCut
  unfold MomentLaw.formMeansAtWeightStatement MomentLaw.ForAllPoints at hMeans
  unfold MomentLaw.formMeansStatement MomentLaw.ForAllPoints at hRead
  unfold MomentLaw.cutoffMeanBoundsStatement MomentLaw.ForAllPoints
  refine forAllParameters_mono (forAllParameters_and weightRate_pos
    (forAllParameters_and hCut (forAllParameters_and hMeans hRead))) ?_
  rintro Λ ⟨hrate, ⟨C₁, c₁, X₁, hc₁, hy₁, H₁⟩, ⟨C₂, c₂, X₂, hc₂, hy₂, H₂⟩, ⟨C₃, c₃, X₃, hc₃, hy₃, H₃⟩⟩
  refine ⟨fun _ => |C₂ 0| * 120 ^ (2 * Λ.k), 1, max (max X₁ X₂) (max Λ.floor ((10 : ℝ) ^ 200)), one_pos,
    le_trans (le_max_left _ _) (le_max_right _ _), fun S hx d n _ hd hn => ?_⟩
  have hx₁ : X₁ ≤ S.scaleCoupling := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx₂ : X₂ ≤ S.scaleCoupling := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx₃ : (10 : ℝ) ^ 200 ≤ S.scaleCoupling := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 < S.scaleCoupling := lt_of_lt_of_le (by positivity) hx₃
  obtain ⟨hr2, hsmall, hhalf⟩ := clusterRange_bounds S.scaleCoupling hx₃
  have hrr : S.range = TorusLumps.clusterRange S.scaleCoupling := rfl
  have hm2 : 2 ≤ S.rangeSq := by
    show 2 ≤ S.range ^ 2
    rw [hrr]
    nlinarith
  set u := S.lastSeparated + d with hu
  have hcut := H₁ S hx₁ u (Nat.le_add_right _ _) (by omega) n hn
  have hω : ∀ p, S.distanceWeight u n p ≤ 1 := fun p => by
    refine Real.exp_le_one_iff.2 ?_
    have : 0 ≤ Λ.stepParams.weightRate / 8 *
        max 0 ((TorusFields.supDist p.1 (S.originSite u n) : ℝ) - (S.radius : ℝ)) := by positivity
    linarith
  have hk : (8 * (Λ.k : ENNReal)) ≠ 0 := by
    have : (Λ.k : ENNReal) ≠ 0 := by exact_mod_cast NeZero.ne Λ.k
    simp [this]
  refine ⟨measurable_toColourForm_cutoffCoords Λ.stepParams (S.originSite u n) S.rangeSq hLog,
    measurable_boxCurvature _ _, fun B => ?_⟩
  have hmean := (H₂ S hx₂).1 d n (by omega) hn B Unit (Measure.dirac ())
  have hrot := (H₃ S).2.2.1 d n B
  obtain ⟨hsize, hcont⟩ := bounds_of_dirac (S.formProductMean d n B) (S.distanceWeight u n) hω _ hk
    (C₂ 0 * (S.range : ℝ) ^ (4 * B.card)) (S.scaleCoupling ^ ((1 : ℝ) / 2)) (Real.rpow_nonneg hx0.le _)
    (2 * B.card) (2 * B.card - 1)
    (fun A A' => (hmean A A' (measurable_of_countable _) (measurable_of_countable _)).1)
    (fun A A' => (hmean A A' (measurable_of_countable _) (measurable_of_countable _)).2.2)
  have hv0 : ∀ W : TorusFields.TorusField n, 0 ≤ S.localCurvature u n W :=
    fun W => Real.iSup_nonneg fun _ => norm_nonneg _
  have hmem : ∀ (z : TorusFields.TorusSite n) (R : ℕ), TorusFields.supDist z (S.originSite u n) ≤ R →
      z ∈ ResponseInTheExpansion.supBall (S.originSite u n) (R : ℝ) := by
    intro z R h
    simp only [ResponseInTheExpansion.supBall, Finset.mem_filter, Finset.mem_univ, true_and]
    exact_mod_cast h
  have hof : ∀ (z : TorusFields.TorusSite n) (R : ℝ), z ∈ ResponseInTheExpansion.supBall (S.originSite u n) R →
      (TorusFields.supDist z (S.originSite u n) : ℝ) ≤ R := by
    intro z R h
    simpa [ResponseInTheExpansion.supBall] using h
  have hne : ∀ (W : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n)), S.IsGoodConfig u n W Y →
      ∀ b : TorusFields.TorusBond n, MomentLaw.cutoffProfile (S.originSite u n) S.rangeSq b.1 ≠ 0 →
      ResponseInTheExpansion.gaugeTransform (ResponseInTheExpansion.axialGaugeAt Λ.stepParams W (S.originSite u n)) W b ≠ -1 := by
    intro W Y hg b hb hγ
    have h1 := supDist_add_two_le_of_cutoffProfile_ne_zero _ b.1 S.rangeSq hm2 hb
    have h2 := supDist_add_unitStep_le b.1 (S.originSite u n) b.2
    have hb1 := hmem b.1 (2 * S.rangeSq) (by omega)
    have hb2 := hmem (b.1 + TorusFields.unitStep n b.2) (2 * S.rangeSq) (by omega)
    push_cast at hb1 hb2
    have h3 := (hcut W Y hg).1 b hb1 hb2
    unfold MomentLaw.axialCoords at h3
    rw [hγ, QuaternionLog.norm_minimalLog_neg_one] at h3
    have h4 : 4 * ((TorusFields.supDist b.1 (S.originSite u n) : ℝ) + 1) ≤ 8 * (S.range : ℝ) ^ 2 := by
      have : TorusFields.supDist b.1 (S.originSite u n) + 1 ≤ 2 * S.range ^ 2 := by
        have e : S.rangeSq = S.range ^ 2 := rfl
        omega
      have h5 : ((TorusFields.supDist b.1 (S.originSite u n) : ℝ) + 1) ≤ 2 * (S.range : ℝ) ^ 2 := by
        exact_mod_cast this
      linarith
    have h6 := mul_le_mul h4 hg.curvature_le (hv0 W) (by positivity)
    have h7 := Real.pi_gt_three
    rw [hrr] at h6
    linarith
  have hB : B.card ≤ Λ.k := by simpa using Finset.card_le_univ B
  have h120 : (120 : ℝ) ^ (2 * B.card) ≤ (120 : ℝ) ^ (2 * Λ.k) := pow_le_pow_right₀ (by norm_num) (by omega)
  refine ⟨?_, hcont, ?_, ?_, ?_, ?_⟩
  · intro X K hK0 hK
    have h1 := hsize X K hK0 hK
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (S.range : ℝ) ^ (4 * B.card) by positivity)] at h1
    refine h1.trans ?_
    have hs0 : 0 ≤ S.scaleCoupling ^ ((1 : ℝ) / 2) * K := mul_nonneg (Real.rpow_nonneg hx0.le _) hK0
    have h2 : (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * (K + K)) ^ (2 * B.card) ≤
        (120 : ℝ) ^ (2 * Λ.k) * (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * K) ^ (2 * B.card) := by
      calc _ ≤ (120 * (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * K)) ^ (2 * B.card) :=
            pow_le_pow_left₀ (by positivity) (by nlinarith) _
        _ = (120 : ℝ) ^ (2 * B.card) * (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * K) ^ (2 * B.card) := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right h120 (by positivity)
    calc _ ≤ |C₂ 0| * (S.range : ℝ) ^ (4 * B.card) *
          ((120 : ℝ) ^ (2 * Λ.k) * (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * K) ^ (2 * B.card)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  · intro W Y
    unfold MomentLaw.MomentPoint.cutoffMean
    dsimp only
    have hs : 0 ≤ S.scaleCoupling ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hx0.le _
    split_ifs with hg
    · have hK : ∀ p : WeightedResponses.OrientedPlaquette n,
          MomentLaw.curlNorm (S.cutoffColourForm u n W) p.1 ≤ 60 * S.scaleCoupling ^ (-(1 / 4) : ℝ) := fun p =>
        ((hcut W Y hg).2.1 p).trans (mul_le_mul_of_nonneg_left hg.curvature_le (by norm_num))
      have h1 := hsize _ _ (by positivity) hK
      have e1 : 1 + S.scaleCoupling ^ ((1 : ℝ) / 2) *
          (60 * S.scaleCoupling ^ (-(1 / 4) : ℝ) + 60 * S.scaleCoupling ^ (-(1 / 4) : ℝ)) =
          1 + 120 * S.scaleCoupling ^ ((1 : ℝ) / 4) := by
        rw [← hhalf]
        ring
      rw [e1, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (S.range : ℝ) ^ (4 * B.card) by positivity)] at h1
      refine h1.trans ?_
      have h2 : (1 + 120 * S.scaleCoupling ^ ((1 : ℝ) / 4)) ^ (2 * B.card) ≤
          (120 : ℝ) ^ (2 * Λ.k) * (1 + S.scaleCoupling ^ ((1 : ℝ) / 4)) ^ (2 * B.card) := by
        calc _ ≤ (120 * (1 + S.scaleCoupling ^ ((1 : ℝ) / 4))) ^ (2 * B.card) :=
              pow_le_pow_left₀ (by positivity) (by linarith) _
          _ = (120 : ℝ) ^ (2 * B.card) * (1 + S.scaleCoupling ^ ((1 : ℝ) / 4)) ^ (2 * B.card) := mul_pow _ _ _
          _ ≤ _ := mul_le_mul_of_nonneg_right h120 (by positivity)
      calc _ ≤ |C₂ 0| * (S.range : ℝ) ^ (4 * B.card) *
            ((120 : ℝ) ^ (2 * Λ.k) * (1 + S.scaleCoupling ^ ((1 : ℝ) / 4)) ^ (2 * B.card)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
    · rw [abs_zero]
      positivity
  · intro Y
    have hset : MeasurableSet {W : TorusFields.TorusField n | S.IsGoodConfig u n W Y} := by
      by_cases hY : Disjoint Y (ResponseInTheExpansion.supBall (S.originSite u n) (8 * S.rangeSq))
      · have e : {W : TorusFields.TorusField n | S.IsGoodConfig u n W Y} =
            (fun W => S.localCurvature u n W) ⁻¹' Set.Iic (S.scaleCoupling ^ (-(1 / 4) : ℝ)) := by
          ext W
          exact ⟨fun h => h.curvature_le, fun h => ⟨hY, h⟩⟩
        rw [e]
        exact measurable_boxCurvature _ _ measurableSet_Iic
      · have e : {W : TorusFields.TorusField n | S.IsGoodConfig u n W Y} = ∅ := by
          ext W
          simpa using fun h : S.IsGoodConfig u n W Y => hY h.disjoint_lumps
        rw [e]
        exact MeasurableSet.empty
    exact Measurable.ite hset
      (hcont.measurable.comp (measurable_toColourForm_cutoffCoords Λ.stepParams (S.originSite u n) S.rangeSq hLog))
      measurable_const
  · intro g W Y
    have hiff : S.IsGoodConfig u n (TorusFields.gaugeTransform g W) Y ↔ S.IsGoodConfig u n W Y := by
      have e : S.localCurvature u n (TorusFields.gaugeTransform g W) = S.localCurvature u n W :=
        boxCurvature_gaugeTransform _ _ g W
      exact ⟨fun h => ⟨h.disjoint_lumps, e ▸ h.curvature_le⟩, fun h => ⟨h.disjoint_lumps, e.symm ▸ h.curvature_le⟩⟩
    unfold MomentLaw.MomentPoint.cutoffMean
    by_cases hg : S.IsGoodConfig u n W Y
    · rw [if_pos hg, if_pos (hiff.2 hg)]
      have he : S.cutoffColourForm u n (TorusFields.gaugeTransform g W) =
          fun e b => ∑ e' : Fin 3, adjointRotation (g (S.originSite u n)) e e' * S.cutoffColourForm u n W e' b :=
        funext₂ fun e b => toColourForm_cutoffCoords_gaugeTransform Λ.stepParams g W (S.originSite u n) S.rangeSq
          (hne W Y hg) e b
      rw [he]
      exact hrot _ _ (adjointRotation_mem _)
    · rw [if_neg hg, if_neg (mt hiff.1 hg)]
  · intro W W' Y Y' hW hY
    have hbox : ∀ c : TorusFields.TorusBond n, TorusFields.supDist c.1 (S.originSite u n) ≤ 8 * S.rangeSq →
        TorusFields.supDist (c.1 + TorusFields.unitStep n c.2) (S.originSite u n) ≤ 8 * S.rangeSq →
        W c.1 c.2 = W' c.1 c.2 := by
      intro c h1 h2
      have e1 := hmem _ _ h1
      have e2 := hmem _ _ h2
      push_cast at e1 e2
      exact hW c e1 e2
    have hv : S.localCurvature u n W = S.localCurvature u n W' := by
      refine boxCurvature_congr _ _ _ _ fun c h1 h2 => hW c ?_ ?_
      · have h3 := hof _ _ h1
        have hm0 : (0 : ℝ) ≤ (S.rangeSq : ℝ) := by positivity
        simp only [ResponseInTheExpansion.supBall, Finset.mem_filter, Finset.mem_univ, true_and]
        linarith
      · have h3 := hof _ _ h2
        have hm0 : (0 : ℝ) ≤ (S.rangeSq : ℝ) := by positivity
        simp only [ResponseInTheExpansion.supBall, Finset.mem_filter, Finset.mem_univ, true_and]
        linarith
    have hc : S.cutoffColourForm u n W = S.cutoffColourForm u n W' :=
      toColourForm_cutoffCoords_congr Λ.stepParams W W' _ S.rangeSq hm2 (8 * S.rangeSq) (by omega) hbox
    have hiff : S.IsGoodConfig u n W Y ↔ S.IsGoodConfig u n W' Y' := by
      have e : Disjoint Y (ResponseInTheExpansion.supBall (S.originSite u n) (8 * S.rangeSq)) ↔
          Disjoint Y' (ResponseInTheExpansion.supBall (S.originSite u n) (8 * S.rangeSq)) := by
        rw [Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_iff_inter_eq_empty, hY]
      exact ⟨fun h => ⟨e.1 h.disjoint_lumps, hv ▸ h.curvature_le⟩,
        fun h => ⟨e.2 h.disjoint_lumps, hv.symm ▸ h.curvature_le⟩⟩
    unfold MomentLaw.MomentPoint.cutoffMean
    by_cases hg : S.IsGoodConfig u n W Y
    · have e2 : S.formProductMean d n B (S.cutoffColourForm (S.lastSeparated + d) n W) =
          S.formProductMean d n B (S.cutoffColourForm (S.lastSeparated + d) n W') :=
        congrArg _ hc
      rw [if_pos hg, if_pos (hiff.1 hg), e2]
    · rw [if_neg hg, if_neg (mt hiff.2 hg)]
end YangMills.Construction.MomentLaw
end
