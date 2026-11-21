import YangMills.Construction.ColdChainAtEveryLevel.ChangesOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfCellsAndSites
import YangMills.Construction.ColdChainAtEveryLevel.LinesOfTheBlocksOfABond
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionAcrossFramesProof
import YangMills.Construction.RunningCouplingSlope.CurvesOfFieldsAtOne
import YangMills.Construction.RunningCouplingSlope.PlainMeanReadsAnyFrameProof
import YangMills.Construction.ClusterExpansionOfAStep.AnglesAlongOneDirection
import YangMills.Construction.ColdStepAtMirrorFrames.CurvedChainIsAbelian
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
private abbrev IntPoint : Type := Fin 4 → ℤ
private theorem expUnit_add_smul (X : imaginaryQuaternions) (s t : ℝ) :
    expUnit ((s + t) • X) = expUnit (s • X) * expUnit (t • X) := by apply _root_.YangMills.SharedProofs.p2328 <;> assumption
private theorem expUnit_zero_smul (X : imaginaryQuaternions) : expUnit ((0 : ℝ) • X) = 1 := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.expUnit_zero_smul <;> assumption
private theorem expUnit_smul_inv (X : imaginaryQuaternions) (s : ℝ) :
    (expUnit (s • X))⁻¹ = expUnit ((-s) • X) := by apply _root_.YangMills.SharedProofs.p4359 <;> assumption
private theorem norm_unitQuaternion (g : UnitQuaternion) : ‖(g : Quaternion ℝ)‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
private theorem curvedChain_coe_expUnit_smul (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (s : ℝ) :
    ((expUnit (s • X) : UnitQuaternion) : Quaternion ℝ) =
      ((Real.cos s : ℝ) : Quaternion ℝ) + Real.sin s • (X : Quaternion ℝ) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.coe_expUnit_smul <;> assumption
private theorem expUnit_two_pi_int_smul (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (k : ℤ) :
    expUnit ((2 * Real.pi * (k : ℝ)) • X) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_two_pi_int_smul <;> assumption
private def stepOffset (st : PathStep) : IntPoint :=
  if st.2 then Pi.single st.1 1 else - Pi.single st.1 1
private theorem curvedChain_siteOfCoords_add (j : ℕ) (a b : IntPoint) :
    (siteOfCoords j (a + b) : F.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_add <;> assumption
private theorem curvedChain_siteOfCoords_neg (j : ℕ) (a : IntPoint) :
    (siteOfCoords j (-a) : F.Site j) = - siteOfCoords j a := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_neg <;> assumption
private theorem siteOfCoords_add_stepDisplacement (j : ℕ) (z : IntPoint) (st : PathStep) :
    (siteOfCoords j z : F.Site j) + stepDisplacement j st = siteOfCoords j (z + stepOffset st) := by apply _root_.YangMills.DeltaSharedProofs.p4150 <;> assumption
private def linkPhase (a : IntPoint → Fin 4 → ℝ) (z : IntPoint) (st : PathStep) : ℝ :=
  if st.2 then a z st.1 else - a (z - Pi.single st.1 1) st.1
private def pathPhase (a : IntPoint → Fin 4 → ℝ) : IntPoint → List PathStep → ℝ
  | _, [] => 0
  | z, st :: r => linkPhase a z st + pathPhase a (z + stepOffset st) r
private def pathOffset : List PathStep → IntPoint
  | [] => 0
  | st :: r => stepOffset st + pathOffset r
private theorem pathHolonomy_eq_expUnit {j : ℕ} {U : F.GaugeField j} {X : imaginaryQuaternions}
    {a : IntPoint → Fin 4 → ℝ}
    (h : ∀ z i, U (siteOfCoords j z) i = expUnit (a z i • X)) :
    ∀ (p : List PathStep) (z : IntPoint),
      pathHolonomy U (siteOfCoords j z) p = expUnit (pathPhase a z p • X)
  | [], z => by
    simp only [pathHolonomy, pathPhase]
    exact (expUnit_zero_smul X).symm
  | st :: r, z => by
    rw [pathHolonomy, pathPhase, siteOfCoords_add_stepDisplacement,
      pathHolonomy_eq_expUnit h r, expUnit_add_smul]
    congr 1
    unfold linkValue linkPhase
    by_cases hb : st.2 = true
    · simp only [hb, if_true]
      exact h z st.1
    · simp only [hb, Bool.false_eq_true, if_false]
      have : (siteOfCoords j z : F.Site j) - unitStep j st.1 =
          siteOfCoords j (z - Pi.single st.1 1) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, curvedChain_siteOfCoords_add, curvedChain_siteOfCoords_neg]; rfl
      rw [this, h, expUnit_smul_inv]
private theorem pathPhase_append (a : IntPoint → Fin 4 → ℝ) (p q : List PathStep) (z : IntPoint) :
    pathPhase a z (p ++ q) = pathPhase a z p + pathPhase a (z + pathOffset p) q := by
  induction p generalizing z with
  | nil => simp [pathPhase, pathOffset]
  | cons st r ih =>
    simp only [List.cons_append, pathPhase, pathOffset, ih]
    ring
abbrev _root_.YangMills.DeltaSharedProofs.p500791 := @pathPhase_append
private theorem pathOffset_append (p q : List PathStep) :
    pathOffset (p ++ q) = pathOffset p + pathOffset q := by
  induction p with
  | nil => simp [pathOffset]
  | cons st r ih => simp only [List.cons_append, pathOffset, ih, add_assoc]
private theorem reversePath_cons (st : PathStep) (r : List PathStep) :
    reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
  simp [reversePath]
private theorem stepOffset_flip (st : PathStep) : stepOffset (st.1, !st.2) = - stepOffset st := by apply _root_.YangMills.Construction.LatticePaths.stepDisplacement_flip <;> assumption
private theorem pathOffset_reversePath (p : List PathStep) :
    pathOffset (reversePath p) = - pathOffset p := by
  induction p with
  | nil => simp [reversePath, pathOffset]
  | cons st r ih =>
    rw [reversePath_cons, pathOffset_append, ih]
    simp only [pathOffset, stepOffset_flip, add_zero, neg_add_rev]
private theorem linkPhase_flip (a : IntPoint → Fin 4 → ℝ) (w : IntPoint) (st : PathStep) :
    linkPhase a w (st.1, !st.2) = - linkPhase a (w - stepOffset st) st := by
  unfold linkPhase stepOffset
  by_cases h : st.2 = true
  · simp [h]
  · simp [h]
private theorem pathPhase_reversePath (a : IntPoint → Fin 4 → ℝ) (p : List PathStep) (z : IntPoint) :
    pathPhase a z (reversePath p) = - pathPhase a (z - pathOffset p) p := by
  induction p generalizing z with
  | nil => simp [reversePath, pathPhase]
  | cons st r ih =>
    rw [reversePath_cons, pathPhase_append, ih, pathOffset_reversePath]
    simp only [pathPhase, pathOffset, linkPhase_flip, add_zero]
    have h1 : z + - pathOffset r - stepOffset st = z - (stepOffset st + pathOffset r) := by abel
    have h2 : z - (stepOffset st + pathOffset r) + stepOffset st = z - pathOffset r := by abel
    rw [h1, h2, sub_eq_add_neg z (pathOffset r)]
    ring
private theorem linkPhase_linear (g : ℝ) (μ ν : Fin 4) (φ : IntPoint → ℝ) (z : IntPoint)
    (st : PathStep) :
    linkPhase (linearFluxAngle g μ ν φ) z st =
      φ (z + stepOffset st) - φ z + linkPhase (linearFluxAngle g μ ν fun _ => 0) z st := by
  unfold linkPhase stepOffset linearFluxAngle
  by_cases h : st.2 = true
  · simp [h]
  · simp only [h, Bool.false_eq_true, if_false, sub_add_cancel, sub_self, zero_add, sub_zero]
    rw [← sub_eq_add_neg z]
    ring
abbrev _root_.YangMills.DeltaSharedProofs.p500583 := @linkPhase_linear
private theorem pathPhase_linear (g : ℝ) (μ ν : Fin 4) (φ : IntPoint → ℝ) (p : List PathStep)
    (z : IntPoint) :
    pathPhase (linearFluxAngle g μ ν φ) z p =
      φ (z + pathOffset p) - φ z + pathPhase (linearFluxAngle g μ ν fun _ => 0) z p := by
  induction p generalizing z with
  | nil => simp [pathPhase, pathOffset]
  | cons st r ih =>
    simp only [pathPhase, pathOffset, ih, linkPhase_linear g μ ν φ z st]
    rw [add_assoc z]
    ring
abbrev _root_.YangMills.DeltaSharedProofs.p502250 := @pathPhase_linear
private theorem linkPhase_translate (g : ℝ) (μ ν : Fin 4) (z w : IntPoint) (st : PathStep) :
    linkPhase (linearFluxAngle g μ ν fun _ => 0) (z + w) st =
      linkPhase (linearFluxAngle g μ ν fun _ => 0) z st + g * (w μ : ℝ) * (stepOffset st ν : ℝ) := by
  unfold linkPhase stepOffset linearFluxAngle
  by_cases h : st.2 = true
  · by_cases hi : st.1 = ν
    · simp [h, hi]; ring
    · have : (Pi.single st.1 (1 : ℤ) : IntPoint) ν = 0 := by simp [Pi.single_apply, Ne.symm hi]
      simp [h, hi, this]
  · by_cases hi : st.1 = ν
    · simp [h, hi]; ring
    · have : (Pi.single st.1 (1 : ℤ) : IntPoint) ν = 0 := by simp [Pi.single_apply, Ne.symm hi]
      simp [h, hi, this]
private theorem pathPhase_translate (g : ℝ) (μ ν : Fin 4) (p : List PathStep) (z w : IntPoint) :
    pathPhase (linearFluxAngle g μ ν fun _ => 0) (z + w) p =
      pathPhase (linearFluxAngle g μ ν fun _ => 0) z p + g * (w μ : ℝ) * (pathOffset p ν : ℝ) := by
  induction p generalizing z with
  | nil => simp [pathPhase, pathOffset]
  | cons st r ih =>
    simp only [pathPhase, pathOffset]
    have h1 : z + w + stepOffset st = (z + stepOffset st) + w := by abel
    rw [h1, ih, linkPhase_translate]
    simp only [Pi.add_apply, Int.cast_add]
    ring
private theorem pathOffset_replicate (m : ℕ) (st : PathStep) :
    pathOffset (List.replicate m st) = (m : ℤ) • stepOffset st := by
  induction m with
  | zero => simp [pathOffset]
  | succ m ih =>
    rw [List.replicate_succ, pathOffset, ih]
    push_cast
    rw [add_smul, one_smul, add_comm]
abbrev _root_.YangMills.DeltaSharedProofs.p501650 := @pathOffset_replicate
private theorem pathOffset_axisPath (h : IntPoint) (π : Equiv.Perm (Fin 4)) :
    pathOffset (axisPath h π) = h := by
  have hk : ∀ k : Fin 4, pathOffset (List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))) =
      Pi.single (π k) (h (π k)) := by
    intro k
    rw [pathOffset_replicate]
    unfold stepOffset
    funext i
    by_cases hi : i = π k
    · subst hi
      by_cases h0 : 0 ≤ h (π k)
      · simp [h0, abs_of_nonneg h0]
      · have h0' : h (π k) < 0 := not_le.mp h0
        simp [h0, abs_of_neg h0']
    · by_cases h0 : 0 ≤ h (π k) <;> simp [h0, Pi.single_apply, hi]
  have hl : axisPath h π = List.replicate (h (π 0)).natAbs (π 0, decide (0 ≤ h (π 0))) ++
      (List.replicate (h (π 1)).natAbs (π 1, decide (0 ≤ h (π 1))) ++
      (List.replicate (h (π 2)).natAbs (π 2, decide (0 ≤ h (π 2))) ++
      (List.replicate (h (π 3)).natAbs (π 3, decide (0 ≤ h (π 3)))))) := by
    simp [axisPath, List.finRange_succ]
  rw [hl, pathOffset_append, pathOffset_append, pathOffset_append, hk, hk, hk, hk]
  have hs : ∑ k : Fin 4, (Pi.single (π k) (h (π k)) : IntPoint) = h := by
    rw [Equiv.sum_comp π (fun k => (Pi.single k (h k) : IntPoint))]
    exact Finset.univ_sum_single h
  calc _ = ∑ k : Fin 4, (Pi.single (π k) (h (π k)) : IntPoint) := by rw [Fin.sum_univ_four]; abel
    _ = h := hs
private theorem pathPhase_replicate_forward (g : ℝ) (μ ν : Fin 4) (hμν : μ ≠ ν) (i : Fin 4) (m : ℕ)
    (z : IntPoint) :
    pathPhase (linearFluxAngle g μ ν fun _ => 0) z (List.replicate m (i, true)) =
      if i = ν then (m : ℝ) * (g * (z μ : ℝ)) else 0 := by
  induction m generalizing z with
  | zero => simp [pathPhase]
  | succ m ih =>
    rw [List.replicate_succ, pathPhase, ih]
    unfold linkPhase stepOffset linearFluxAngle
    by_cases hi : i = ν
    · subst hi
      simp [Pi.single_apply, hμν]
      ring
    · simp [hi]
abbrev _root_.YangMills.DeltaSharedProofs.p500547 := @pathPhase_replicate_forward
private def contourPhase (g : ℝ) (μ ν : Fin 4) (L : ℕ) (h : IntPoint) (i : Fin 4) : ℝ :=
  (L : ℝ) * g * ((if i = ν then (h μ : ℝ) else 0) - (if i = μ then (h ν : ℝ) else 0))
private theorem pathOffset_bondContour (L : ℕ) (h : IntPoint) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    pathOffset (bondContour L h π i) = (L : ℤ) • Pi.single i 1 := by
  unfold bondContour
  rw [pathOffset_append, pathOffset_append, pathOffset_reversePath, pathOffset_axisPath,
    pathOffset_replicate]
  simp [stepOffset]
private theorem pathPhase_bondContour (g : ℝ) (μ ν : Fin 4) (hμν : μ ≠ ν) (φ : IntPoint → ℝ) (L : ℕ)
    (h : IntPoint) (π : Equiv.Perm (Fin 4)) (i : Fin 4) (z : IntPoint) :
    pathPhase (linearFluxAngle g μ ν φ) z (bondContour L h π i) =
      φ (z + (L : ℤ) • Pi.single i 1) - φ z + (if i = ν then (L : ℝ) * (g * (z μ : ℝ)) else 0) +
        contourPhase g μ ν L h i := by
  rw [pathPhase_linear, pathOffset_bondContour]
  unfold bondContour
  rw [pathPhase_append, pathPhase_append, pathOffset_append, pathOffset_axisPath, pathOffset_replicate,
    pathPhase_reversePath, pathOffset_axisPath, pathPhase_replicate_forward g μ ν hμν]
  have hst : stepOffset (i, true) = Pi.single i 1 := by simp [stepOffset]
  have hw : z + (h + (L : ℤ) • stepOffset (i, true)) - h = z + (L : ℤ) • Pi.single i 1 := by
    rw [hst]; abel
  have hwμ : ((((L : ℤ) • Pi.single i 1 : IntPoint) μ : ℤ) : ℝ) = if i = μ then (L : ℝ) else 0 := by
    by_cases hm : i = μ
    · subst hm; simp
    · simp [hm, Ne.symm hm]
  rw [hw, pathPhase_translate, pathOffset_axisPath, hwμ]
  unfold contourPhase
  by_cases hi : i = ν
  · have hm : i ≠ μ := by rw [hi]; exact Ne.symm hμν
    simp only [if_pos hi, if_neg hm, Pi.add_apply, Int.cast_add]
    ring
  · by_cases hm : i = μ
    · simp only [if_neg hi, if_pos hm]
      ring
    · simp only [if_neg hi, if_neg hm]
      ring
private theorem period_succ {j : ℕ} (hj : j < F.top) (i : Fin 4) :
    F.period j i = F.period (j + 1) i * F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.period_eq_mul_blockSide <;> assumption
private theorem curvedChain_siteOfCoords_siteCoords {j : ℕ} (y : F.Site j) : siteOfCoords j (siteCoords y) = y := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
private theorem curvedChain_refineSite_siteOfCoords {j : ℕ} (hj : j < F.top) (z : IntPoint) :
    (_root_.YangMills.Construction.BlockAverages.refineSite (siteOfCoords (j + 1) z : F.Site (j + 1)) : F.Site j) =
      siteOfCoords j (fun i => (F.blockSide : ℤ) * z i) := by apply _root_.YangMills.Construction.BlockLines.refineSite_siteOfCoords <;> assumption
private theorem neg_mem_centredCube {M : ℕ} {h : IntPoint} (hh : h ∈ centredCube M) :
    -h ∈ centredCube M := by
  unfold centredCube at *
  rw [Fintype.mem_piFinset] at *
  intro k
  have := hh k
  rw [Finset.mem_Icc] at *
  simp only [Pi.neg_apply]
  omega
abbrev _root_.YangMills.DeltaSharedProofs.p501275 := @neg_mem_centredCube
private theorem curvedChain_zero_mem_centredCube (M : ℕ) (hM : 0 < M) : (0 : IntPoint) ∈ centredCube M := by apply _root_.YangMills.Construction.BlockAverages.GaugeChange.zero_mem_centredCube <;> assumption
private theorem two_mul_abs_le_of_mem_centredCube {M : ℕ} {h : IntPoint} (hh : h ∈ centredCube M)
    (k : Fin 4) (hM : 0 < M) :
    2 * |(h k : ℝ)| ≤ M := by
  unfold centredCube at hh
  rw [Fintype.mem_piFinset] at hh
  have := hh k
  rw [Finset.mem_Icc] at this
  have h1 : 2 * |h k| ≤ (M : ℤ) := by
    rcases abs_cases (h k) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> omega
  have h2 : ((2 * |h k| : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  exact h2
private theorem contourPhase_neg (g : ℝ) (μ ν : Fin 4) (L : ℕ) (h : IntPoint) (i : Fin 4) :
    contourPhase g μ ν L (-h) i = - contourPhase g μ ν L h i := by
  unfold contourPhase
  simp only [Pi.neg_apply, Int.cast_neg]
  split_ifs <;> ring
private theorem sum_sin_contourPhase (g : ℝ) (μ ν : Fin 4) (L : ℕ) (i : Fin 4) :
    ∑ h ∈ centredCube L, Real.sin (contourPhase g μ ν L h i) = 0 := by
  have h1 : ∑ h ∈ centredCube L, Real.sin (contourPhase g μ ν L h i) =
      ∑ h ∈ centredCube L, Real.sin (contourPhase g μ ν L (-h) i) := by
    apply Finset.sum_nbij' (fun h => -h) (fun h => -h)
    · intro h hh; exact neg_mem_centredCube hh
    · intro h hh; exact neg_mem_centredCube hh
    · intro h _; simp
    · intro h _; simp
    · intro h _; simp
  simp only [contourPhase_neg, Real.sin_neg, Finset.sum_neg_distrib] at h1
  linarith
private theorem cos_contourPhase_pos (g : ℝ) (μ ν : Fin 4) (hμν : μ ≠ ν) (L : ℕ) (hL : 0 < L)
    (hg : (L : ℝ) ^ 2 * |g| ≤ 1) {h : IntPoint} (hh : h ∈ centredCube L) (i : Fin 4) :
    0 < Real.cos (contourPhase g μ ν L h i) := by
  have hA : 2 * |(if i = ν then (h μ : ℝ) else 0) - (if i = μ then (h ν : ℝ) else 0)| ≤ L := by
    by_cases hi : i = ν
    · have hm : i ≠ μ := by rw [hi]; exact Ne.symm hμν
      simp only [if_pos hi, if_neg hm, sub_zero]
      exact two_mul_abs_le_of_mem_centredCube hh μ hL
    · by_cases hm : i = μ
      · simp only [if_neg hi, if_pos hm, zero_sub, abs_neg]
        exact two_mul_abs_le_of_mem_centredCube hh ν hL
      · simp only [if_neg hi, if_neg hm, sub_zero, abs_zero, mul_zero]
        exact_mod_cast hL.le
  have hb : |contourPhase g μ ν L h i| ≤ 1 / 2 := by
    unfold contourPhase
    rw [abs_mul, abs_mul, Nat.abs_cast]
    have hL' : (0 : ℝ) ≤ L := by positivity
    have hg' : (0 : ℝ) ≤ |g| := abs_nonneg g
    nlinarith [mul_le_mul_of_nonneg_left hA (mul_nonneg hL' hg')]
  apply Real.cos_pos_of_mem_Ioo
  have hp := Real.pi_gt_three
  rw [abs_le] at hb
  constructor <;> linarith [hb.1, hb.2]
private theorem contourAverage_of_linear {j : ℕ} (hj : j < F.top) (hL : 0 < F.blockSide)
    {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {g : ℝ}
    {μ ν : Fin 4} (hμν : μ ≠ ν) {φ : IntPoint → ℝ} {U : F.GaugeField j}
    (hU : ∀ z i, U (siteOfCoords j z) i = expUnit (linearFluxAngle g μ ν φ z i • X))
    (z : IntPoint) (i : Fin 4) :
    _root_.YangMills.Construction.BlockAverages.contourAverage U (siteOfCoords (j + 1) z, i) =
      ((1 / (F.blockSide : ℝ) ^ 4) *
          ∑ h ∈ centredCube F.blockSide, Real.cos (contourPhase g μ ν F.blockSide h i)) •
        ((expUnit ((φ ((fun k => (F.blockSide : ℤ) * z k) + (F.blockSide : ℤ) • Pi.single i 1) -
            φ (fun k => (F.blockSide : ℤ) * z k) +
            (if i = ν then (F.blockSide : ℝ) * (g * (((F.blockSide : ℤ) * z μ : ℤ) : ℝ)) else 0)) • X) :
            UnitQuaternion) :
          Quaternion ℝ) := by
  set S : ℝ := φ ((fun k => (F.blockSide : ℤ) * z k) + (F.blockSide : ℤ) • Pi.single i 1) -
    φ (fun k => (F.blockSide : ℤ) * z k) +
    (if i = ν then (F.blockSide : ℝ) * (g * (((F.blockSide : ℤ) * z μ : ℤ) : ℝ)) else 0) with hS
  have hol : ∀ (h : IntPoint) (π : Equiv.Perm (Fin 4)),
      ((pathHolonomy U (_root_.YangMills.Construction.BlockAverages.refineSite (siteOfCoords (j + 1) z : F.Site (j + 1)))
          (bondContour F.blockSide h π i) : UnitQuaternion) : Quaternion ℝ) =
      ((expUnit (S • X) : UnitQuaternion) : Quaternion ℝ) *
        (((Real.cos (contourPhase g μ ν F.blockSide h i) : ℝ) : Quaternion ℝ) +
          Real.sin (contourPhase g μ ν F.blockSide h i) • (X : Quaternion ℝ)) := by
    intro h π
    rw [curvedChain_refineSite_siteOfCoords hj, pathHolonomy_eq_expUnit hU, pathPhase_bondContour g μ ν hμν,
      ← hS, expUnit_add_smul]
    show ((expUnit (S • X) : UnitQuaternion) : Quaternion ℝ) *
      ((expUnit (contourPhase g μ ν F.blockSide h i • X) : UnitQuaternion) : Quaternion ℝ) = _
    rw [curvedChain_coe_expUnit_smul X hX (contourPhase g μ ν F.blockSide h i)]
  have hπ : ∀ h : IntPoint, ∑ π : Equiv.Perm (Fin 4),
      ((pathHolonomy U (_root_.YangMills.Construction.BlockAverages.refineSite (siteOfCoords (j + 1) z : F.Site (j + 1)))
          (bondContour F.blockSide h π i) : UnitQuaternion) : Quaternion ℝ) =
      (24 * Real.cos (contourPhase g μ ν F.blockSide h i)) •
          ((expUnit (S • X) : UnitQuaternion) : Quaternion ℝ) +
        (24 * Real.sin (contourPhase g μ ν F.blockSide h i)) •
          (((expUnit (S • X) : UnitQuaternion) : Quaternion ℝ) * (X : Quaternion ℝ)) := by
    intro h
    rw [Finset.sum_congr rfl (fun π _ => hol h π), Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, show Nat.factorial 4 = 24 from rfl,
      ← Nat.cast_smul_eq_nsmul ℝ, mul_add, Quaternion.mul_coe_eq_smul, mul_smul_comm, smul_add,
      smul_smul, smul_smul]
    norm_num
  unfold _root_.YangMills.Construction.BlockAverages.contourAverage
  dsimp only
  rw [Finset.sum_congr rfl (fun h _ => hπ h), Finset.sum_add_distrib, ← Finset.sum_smul,
    ← Finset.sum_smul, ← Finset.mul_sum, ← Finset.mul_sum, sum_sin_contourPhase, mul_zero, zero_smul,
    add_zero, smul_smul]
  congr 1
  have : (F.blockSide : ℝ) ≠ 0 := by positivity
  field_simp
private theorem quaternionUnitPart_smul (g : UnitQuaternion) {ρ : ℝ} (hρ : 0 < ρ) :
    quaternionUnitPart (ρ • (g : Quaternion ℝ)) = g := by
  have hn : ‖ρ • (g : Quaternion ℝ)‖ = ρ := by
    rw [norm_smul, norm_unitQuaternion, mul_one, Real.norm_eq_abs, abs_of_pos hρ]
  have hq : ρ • (g : Quaternion ℝ) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact hρ.ne hn
  have hex : ∃ g' : UnitQuaternion, ρ • (g : Quaternion ℝ) ≠ 0 ∧
      ρ • (g : Quaternion ℝ) = ‖ρ • (g : Quaternion ℝ)‖ • (g' : Quaternion ℝ) := ⟨g, hq, by rw [hn]⟩
  unfold quaternionUnitPart
  rw [dif_pos hex]
  have hs : ρ • (g : Quaternion ℝ) = ρ • (hex.choose : Quaternion ℝ) :=
    hex.choose_spec.2.trans (congrArg (· • (hex.choose : Quaternion ℝ)) hn)
  apply Subtype.ext
  exact (smul_right_injective _ hρ.ne' hs).symm
private theorem contourWeight_pos {g : ℝ} {μ ν : Fin 4} (hμν : μ ≠ ν) {L : ℕ} (hL : 0 < L)
    (hg : (L : ℝ) ^ 2 * |g| ≤ 1) (i : Fin 4) :
    0 < (1 / (L : ℝ) ^ 4) * ∑ h ∈ centredCube L, Real.cos (contourPhase g μ ν L h i) := by
  apply mul_pos (by positivity)
  exact Finset.sum_pos (fun h hh => cos_contourPhase_pos g μ ν hμν L hL hg hh i)
    ⟨0, curvedChain_zero_mem_centredCube L hL⟩
private theorem curvedChain_period_pos (hL : 0 < F.blockSide) {n : ℕ} (hn : ∀ i, F.extent i = n) (h0 : 0 < n)
    (j : ℕ) (i : Fin 4) :
    0 < F.period j i := by
  unfold BlockFrame.period
  rw [hn]
  positivity
private theorem levelFlux_succ {j : ℕ} (hj : j < F.top) (hL : 0 < F.blockSide) {n : ℕ}
    (hn : ∀ i, F.extent i = n) (h0 : 0 < n) (μ : Fin 4) (l : ℕ) :
    levelFlux F μ l (j + 1) = (F.blockSide : ℝ) ^ 2 * levelFlux F μ l j := by
  unfold levelFlux
  rw [period_succ hj μ]
  have h1 : ((F.period (j + 1) μ : ℕ) : ℝ) ≠ 0 := by
    have := curvedChain_period_pos hL hn h0 (j + 1) μ
    positivity
  have h2 : (F.blockSide : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
private theorem abs_levelFlux_le_one {j : ℕ} (hL : 0 < F.blockSide) {n : ℕ} (hn : ∀ i, F.extent i = n)
    (h0 : 0 < n) (μ : Fin 4) (l : ℕ) (hl : 2 * Real.pi * l / (n : ℝ) ^ 2 ≤ 1) :
    |levelFlux F μ l j| ≤ 1 := by
  unfold levelFlux
  have hp : (0 : ℝ) ≤ 2 * Real.pi * l := by positivity
  rw [abs_of_nonneg (by positivity)]
  refine le_trans ?_ hl
  apply div_le_div_of_nonneg_left hp (by positivity)
  have h1 : n ≤ F.period j μ := by
    unfold BlockFrame.period
    rw [hn]
    exact Nat.le_mul_of_pos_right n (by positivity)
  have h2 : (n : ℝ) ≤ F.period j μ := by exact_mod_cast h1
  nlinarith
private theorem scale_add_single (L : ℕ) (z : IntPoint) (i : Fin 4) :
    (fun k => (L : ℤ) * ((z + Pi.single i 1 : IntPoint) k)) =
      (fun k => (L : ℤ) * z k) + (L : ℤ) • (Pi.single i 1 : IntPoint) := by apply _root_.YangMills.Construction.RunningCouplingSlope.blockCoords_add_single <;> assumption
private theorem linear_blockStep {j : ℕ} (hj : j < F.top) (hL : 0 < F.blockSide) {n : ℕ}
    (hn : ∀ i, F.extent i = n)
    (h0 : 0 < n) {X : imaginaryQuaternions} (hX : ‖X‖ = 1) {μ ν : Fin 4} (hμν : μ ≠ ν) {l : ℕ}
    (hl : 2 * Real.pi * l / (n : ℝ) ^ 2 ≤ 1) {U : F.GaugeField j} {U' : F.GaugeField (j + 1)}
    (hU' : ∀ y i, U' y i = quaternionUnitPart (_root_.YangMills.Construction.BlockAverages.contourAverage U (y, i)))
    (hU : IsAbelianLinearAlong X (levelFlux F μ l j) μ ν U) :
    IsAbelianLinearAlong X (levelFlux F μ l (j + 1)) μ ν U' ∧ (∀ c, blockFit U U' c = 0) ∧
      IsAbelianLinearPair X (levelFlux F μ l j) μ ν U U' ∧
      ∀ c : F.Site (j + 1) × Fin 4, ∃ ρ : ℝ, 0 < ρ ∧
        _root_.YangMills.Construction.BlockAverages.contourAverage U c = ρ • ((U' c.1 c.2 : UnitQuaternion) : Quaternion ℝ) := by
  obtain ⟨φ, hφ⟩ := hU
  have hg : (F.blockSide : ℝ) ^ 2 * |levelFlux F μ l j| ≤ 1 := by
    have h1 := abs_levelFlux_le_one (j := j + 1) hL hn h0 μ l hl
    rw [levelFlux_succ hj hL hn h0, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (F.blockSide : ℝ) ^ 2)] at h1
    exact h1
  have hlin : ∀ z i, U' (siteOfCoords (j + 1) z) i =
      expUnit (linearFluxAngle (levelFlux F μ l (j + 1)) μ ν
        (fun z => φ (fun k => (F.blockSide : ℤ) * z k)) z i • X) := by
    intro z i
    rw [hU', contourAverage_of_linear hj hL hX hμν hφ z i,
      quaternionUnitPart_smul _ (contourWeight_pos hμν hL hg i)]
    congr 2
    unfold linearFluxAngle
    dsimp only
    rw [scale_add_single, levelFlux_succ hj hL hn h0]
    by_cases hi : i = ν
    · simp only [if_pos hi]
      push_cast
      ring
    · simp only [if_neg hi]
  refine ⟨⟨_, hlin⟩, ?_, ⟨φ, hφ, ?_⟩, ?_⟩
  rotate_left
  · intro z i
    rw [hlin, levelFlux_succ hj hL hn h0]
  · rintro ⟨y, i⟩
    have hy := curvedChain_siteOfCoords_siteCoords y
    rw [← hy]
    have hm := contourAverage_of_linear hj hL hX hμν hφ (siteCoords y) i
    have hu := hU' (siteOfCoords (j + 1) (siteCoords y)) i
    rw [hm, quaternionUnitPart_smul _ (contourWeight_pos hμν hL hg i)] at hu
    exact ⟨_, contourWeight_pos hμν hL hg i, by dsimp only; rw [hm, hu]⟩
  rintro ⟨y, i⟩
  have hy := curvedChain_siteOfCoords_siteCoords y
  rw [← hy]
  have hm := contourAverage_of_linear hj hL hX hμν hφ (siteCoords y) i
  have hu := hU' (siteOfCoords (j + 1) (siteCoords y)) i
  rw [hm, quaternionUnitPart_smul _ (contourWeight_pos hμν hL hg i)] at hu
  unfold blockFit
  dsimp only
  rw [hm, hu, norm_smul, norm_unitQuaternion, mul_one, Real.norm_eq_abs,
    abs_of_pos (contourWeight_pos hμν hL hg i), smul_mul_assoc]
  have hE : ∀ E : UnitQuaternion, (E : Quaternion ℝ) * ((E⁻¹ : UnitQuaternion) : Quaternion ℝ) = 1 := by
    intro E
    show ((E * E⁻¹ : UnitQuaternion) : Quaternion ℝ) = 1
    rw [mul_inv_cancel]
    rfl
  rw [hE]
  have h1 : (1 : Quaternion ℝ).re = 1 := rfl
  simp [h1]
private theorem linear_constantCurvatureField (hL : 0 < F.blockSide) {n : ℕ} (hn : ∀ i, F.extent i = n)
    (h0 : 0 < n) {X : imaginaryQuaternions}
    (hX : ‖X‖ = 1) {μ ν : Fin 4} (hμν : μ ≠ ν) (l : ℕ) :
    IsAbelianLinearAlong X (levelFlux F μ l 0) μ ν (constantCurvatureField F X μ ν l) := by
  set M : ℕ := F.period 0 μ with hM
  have hMpos : 0 < M := curvedChain_period_pos hL hn h0 0 μ
  have hper : F.period 0 ν = M := by
    rw [hM]; unfold BlockFrame.period; rw [hn, hn]
  have hMr : (M : ℝ) ≠ 0 := by positivity
  have hMz : (0 : ℤ) < M := by exact_mod_cast hMpos
  set γ : ℝ := 2 * Real.pi * l / (M : ℝ) ^ 2 with hγ
  have hγM : γ * (M : ℝ) ^ 2 = 2 * Real.pi * l := by rw [hγ]; field_simp
  refine ⟨fun z => - γ * (M : ℝ) * (((z μ / (M : ℤ) : ℤ)) : ℝ) * (z ν : ℝ), ?_⟩
  intro z i
  have hcμ : siteCoords (siteOfCoords 0 z : F.Site 0) μ = z μ % (M : ℤ) := by
    unfold siteCoords siteOfCoords
    exact ZMod.coe_intCast _
  have hcν : siteCoords (siteOfCoords 0 z : F.Site 0) ν = z ν % (M : ℤ) := by
    unfold siteCoords siteOfCoords
    rw [ZMod.coe_intCast, hper]
  have hzμ : (z μ : ℝ) = (M : ℝ) * ((z μ / (M : ℤ) : ℤ) : ℝ) + ((z μ % (M : ℤ) : ℤ) : ℝ) := by
    have := Int.mul_ediv_add_emod (z μ) (M : ℤ)
    exact_mod_cast this.symm
  have hzν : (z ν : ℝ) = (M : ℝ) * ((z ν / (M : ℤ) : ℤ) : ℝ) + ((z ν % (M : ℤ) : ℤ) : ℝ) := by
    have := Int.mul_ediv_add_emod (z ν) (M : ℤ)
    exact_mod_cast this.symm
  have hflux : levelFlux F μ l 0 = γ := rfl
  rw [hflux]
  unfold constantCurvatureField finestSide linearFluxAngle
  dsimp only
  rw [← hM, ← hγ, hcμ, hcν]
  by_cases hi : i = ν
  · subst hi
    rw [if_pos rfl, if_pos rfl]
    congr 2
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hμν]
    simp only [add_zero]
    push_cast
    rw [hzμ]
    ring
  · rw [if_neg hi, if_neg hi]
    by_cases hm : i = μ
    · subst hm
      have hq : (z i + 1) / (M : ℤ) =
          if z i % (M : ℤ) + 1 = (M : ℤ) then z i / (M : ℤ) + 1 else z i / (M : ℤ) := by
        have h1 := Int.mul_ediv_add_emod (z i) (M : ℤ)
        have h2 := Int.emod_nonneg (z i) hMz.ne'
        have h3 := Int.emod_lt_of_pos (z i) hMz
        split_ifs with hc
        · have : z i + 1 = (M : ℤ) * (z i / (M : ℤ) + 1) := by rw [mul_add]; linarith
          rw [this]
          exact Int.mul_ediv_cancel_left _ hMz.ne'
        · have hlt : z i % (M : ℤ) + 1 < (M : ℤ) := by omega
          have : z i + 1 = (z i % (M : ℤ) + 1) + (M : ℤ) * (z i / (M : ℤ)) := by linarith
          rw [this, Int.add_mul_ediv_left _ _ hMz.ne', Int.ediv_eq_zero_of_lt (by omega) hlt, zero_add]
      by_cases hc : z i % (M : ℤ) + 1 = (M : ℤ)
      · rw [if_pos ⟨rfl, hc⟩]
        rw [if_pos hc] at hq
        have hB : (- γ * (M : ℝ) * ((((z + Pi.single i 1 : IntPoint) i / (M : ℤ) : ℤ)) : ℝ) *
              (((z + Pi.single i 1 : IntPoint) ν : ℤ) : ℝ) -
            - γ * (M : ℝ) * (((z i / (M : ℤ) : ℤ)) : ℝ) * (z ν : ℝ) + 0) =
            (- γ * (M : ℝ) * ((z ν % (M : ℤ) : ℤ) : ℝ)) +
              2 * Real.pi * (((- (l : ℤ) * (z ν / (M : ℤ)) : ℤ)) : ℝ) := by
          simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hμν), add_zero]
          rw [hq]
          push_cast
          rw [hzν]
          have : γ * (M : ℝ) ^ 2 * ((z ν / (M : ℤ) : ℤ) : ℝ) =
              2 * Real.pi * (l : ℝ) * ((z ν / (M : ℤ) : ℤ) : ℝ) := by rw [hγM]
          ring_nf
          ring_nf at this
          linarith
        rw [hB, expUnit_add_smul, expUnit_two_pi_int_smul X hX, mul_one]
      · rw [if_neg (fun hh => hc hh.2)]
        rw [if_neg hc] at hq
        have hB : (- γ * (M : ℝ) * ((((z + Pi.single i 1 : IntPoint) i / (M : ℤ) : ℤ)) : ℝ) *
              (((z + Pi.single i 1 : IntPoint) ν : ℤ) : ℝ) -
            - γ * (M : ℝ) * (((z i / (M : ℤ) : ℤ)) : ℝ) * (z ν : ℝ) + 0) = 0 := by
          simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hμν), add_zero]
          rw [hq]
          ring
        rw [hB, expUnit_zero_smul]
    · rw [if_neg (fun hh => hm hh.1)]
      have hB : (- γ * (M : ℝ) * ((((z + Pi.single i 1 : IntPoint) μ / (M : ℤ) : ℤ)) : ℝ) *
            (((z + Pi.single i 1 : IntPoint) ν : ℤ) : ℝ) -
          - γ * (M : ℝ) * (((z μ / (M : ℤ) : ℤ)) : ℝ) * (z ν : ℝ) + 0) = 0 := by
        simp only [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hi), Pi.single_eq_of_ne (Ne.symm hm),
          add_zero]
        ring
      rw [hB, expUnit_zero_smul]
theorem constantCurvatureChain_abelian : ConstantCurvatureChainAbelian := by
  intro F X μ ν n l hodd hn h0 hX hμν hl
  have hL : 0 < F.blockSide := hodd.pos
  have hne : μ ≠ ν := hμν.ne
  have key : ∀ j, j ≤ F.top →
      IsAbelianLinearAlong X (levelFlux F μ l j) μ ν (constantCurvatureChain F X μ ν l j) := by
    intro j
    induction j with
    | zero => intro _; exact linear_constantCurvatureField hL hn h0 hX hne l
    | succ j ih =>
      intro hj
      exact (linear_blockStep (by omega) hL hn h0 hX hne hl (fun _ _ => rfl) (ih (by omega))).1
  intro j hj
  exact ⟨key j hj, fun hlt => (linear_blockStep hlt hL hn h0 hX hne hl (fun _ _ => rfl) (key j hj)).2⟩
end YangMills.Construction.ColdStepAtMirrorFrames
end
