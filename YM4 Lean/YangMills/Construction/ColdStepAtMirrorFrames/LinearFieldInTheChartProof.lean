import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfCellsAndSites
import YangMills.Construction.ColdStepAtMirrorFrames.CurvedChainIsAbelianProof
import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormAtTheLeastFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionAcrossFramesProof
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOverContoursOfAFormForm
import YangMills.Construction.HoleBesideASecondHole.WhatAHoleSavesAtParametersProof
import YangMills.Construction.RunningCouplingSlope.PlainMeanReadsAnyFrameProof
import YangMills.Construction.ColdStepAtMirrorFrames.BareActionIsCriticalAtAnAbelianFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyAtTheLeastChartProof
import YangMills.Construction.ColdStepAtMirrorFrames.LinearFieldInTheChart
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
private abbrev IntVec : Type := Fin 4 → ℤ
private theorem expUnit_add_smul (X : imaginaryQuaternions) (s t : ℝ) :
    expUnit ((s + t) • X) = expUnit (s • X) * expUnit (t • X) := by apply _root_.YangMills.SharedProofs.p2328 <;> assumption
private theorem expUnit_zero_smul (X : imaginaryQuaternions) : expUnit ((0 : ℝ) • X) = 1 := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.expUnit_zero_smul <;> assumption
private theorem expUnit_smul_inv (X : imaginaryQuaternions) (s : ℝ) :
    (expUnit (s • X))⁻¹ = expUnit ((-s) • X) := by apply _root_.YangMills.SharedProofs.p4359 <;> assumption
private def stepShift (st : PathStep) : IntVec :=
  if st.2 then Pi.single st.1 1 else - Pi.single st.1 1
private theorem siteOfCoords_add_local (j : ℕ) (a b : IntVec) :
    (siteOfCoords j (a + b) : F.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_add <;> assumption
private theorem siteOfCoords_neg_local (j : ℕ) (a : IntVec) :
    (siteOfCoords j (-a) : F.Site j) = - siteOfCoords j a := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_neg <;> assumption
private theorem siteOfCoords_add_step (j : ℕ) (z : IntVec) (st : PathStep) :
    (siteOfCoords j z : F.Site j) + stepDisplacement j st = siteOfCoords j (z + stepShift st) := by apply _root_.YangMills.DeltaSharedProofs.p4150 <;> assumption
private def stepAngle (a : IntVec → Fin 4 → ℝ) (z : IntVec) (st : PathStep) : ℝ :=
  if st.2 then a z st.1 else - a (z - Pi.single st.1 1) st.1
private def pathAngle (a : IntVec → Fin 4 → ℝ) : IntVec → List PathStep → ℝ
  | _, [] => 0
  | z, st :: r => stepAngle a z st + pathAngle a (z + stepShift st) r
private def pathShift : List PathStep → IntVec
  | [] => 0
  | st :: r => stepShift st + pathShift r
private theorem pathHolonomy_eq_expUnit {j : ℕ} {U : F.GaugeField j} {X : imaginaryQuaternions}
    {a : IntVec → Fin 4 → ℝ}
    (h : ∀ z i, U (siteOfCoords j z) i = expUnit (a z i • X)) :
    ∀ (p : List PathStep) (z : IntVec),
      pathHolonomy U (siteOfCoords j z) p = expUnit (pathAngle a z p • X)
  | [], z => by
    simp only [pathHolonomy, pathAngle]
    exact (expUnit_zero_smul X).symm
  | st :: r, z => by
    rw [pathHolonomy, pathAngle, siteOfCoords_add_step, pathHolonomy_eq_expUnit h r, expUnit_add_smul]
    congr 1
    unfold linkValue stepAngle
    by_cases hb : st.2 = true
    · simp only [hb, if_true]
      exact h z st.1
    · simp only [hb, Bool.false_eq_true, if_false]
      have : (siteOfCoords j z : F.Site j) - unitStep j st.1 =
          siteOfCoords j (z - Pi.single st.1 1) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, siteOfCoords_add_local, siteOfCoords_neg_local]; rfl
      rw [this, h, expUnit_smul_inv]
private theorem pathAngle_append (a : IntVec → Fin 4 → ℝ) (p q : List PathStep) (z : IntVec) :
    pathAngle a z (p ++ q) = pathAngle a z p + pathAngle a (z + pathShift p) q := by
  induction p generalizing z with
  | nil => simp [pathAngle, pathShift]
  | cons st r ih =>
    simp only [List.cons_append, pathAngle, pathShift, ih]
    ring
private theorem pathShift_append (p q : List PathStep) :
    pathShift (p ++ q) = pathShift p + pathShift q := by
  induction p with
  | nil => simp [pathShift]
  | cons st r ih => simp only [List.cons_append, pathShift, ih, add_assoc]
private theorem stepAngle_linearFluxAngle (g : ℝ) (μ ν : Fin 4) (φ : IntVec → ℝ) (z : IntVec)
    (st : PathStep) :
    stepAngle (linearFluxAngle g μ ν φ) z st =
      φ (z + stepShift st) - φ z + stepAngle (linearFluxAngle g μ ν fun _ => 0) z st := by
  unfold stepAngle stepShift linearFluxAngle
  by_cases h : st.2 = true
  · simp [h]
  · simp only [h, Bool.false_eq_true, if_false, sub_add_cancel, sub_self, zero_add, sub_zero]
    rw [← sub_eq_add_neg z]
    ring
private theorem pathAngle_linearFluxAngle (g : ℝ) (μ ν : Fin 4) (φ : IntVec → ℝ)
    (p : List PathStep) (z : IntVec) :
    pathAngle (linearFluxAngle g μ ν φ) z p =
      φ (z + pathShift p) - φ z + pathAngle (linearFluxAngle g μ ν fun _ => 0) z p := by
  induction p generalizing z with
  | nil => simp [pathAngle, pathShift]
  | cons st r ih =>
    simp only [pathAngle, pathShift, ih, stepAngle_linearFluxAngle g μ ν φ z st]
    rw [add_assoc z]
    ring
private theorem pathShift_replicate (m : ℕ) (st : PathStep) :
    pathShift (List.replicate m st) = (m : ℤ) • stepShift st := by
  induction m with
  | zero => simp [pathShift]
  | succ m ih =>
    rw [List.replicate_succ, pathShift, ih]
    push_cast
    rw [add_smul, one_smul, add_comm]
private theorem pathShift_axisPath (h : IntVec) (π : Equiv.Perm (Fin 4)) :
    pathShift (axisPath h π) = h := by
  have hk : ∀ k : Fin 4, pathShift (List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))) =
      Pi.single (π k) (h (π k)) := by
    intro k
    rw [pathShift_replicate]
    unfold stepShift
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
  rw [hl, pathShift_append, pathShift_append, pathShift_append, hk, hk, hk, hk]
  have hs : ∑ k : Fin 4, (Pi.single (π k) (h (π k)) : IntVec) = h := by
    rw [Equiv.sum_comp π (fun k => (Pi.single k (h k) : IntVec))]
    exact Finset.univ_sum_single h
  calc _ = ∑ k : Fin 4, (Pi.single (π k) (h (π k)) : IntVec) := by rw [Fin.sum_univ_four]; abel
    _ = h := hs
private theorem pathAngle_forward_flow (g : ℝ) (μ ν : Fin 4) (hμν : μ ≠ ν) (i : Fin 4) (m : ℕ)
    (z : IntVec) :
    pathAngle (linearFluxAngle g μ ν fun _ => 0) z (List.replicate m (i, true)) =
      if i = ν then (m : ℝ) * (g * (z μ : ℝ)) else 0 := by
  induction m generalizing z with
  | zero => simp [pathAngle]
  | succ m ih =>
    rw [List.replicate_succ, pathAngle, ih]
    unfold stepAngle stepShift linearFluxAngle
    by_cases hi : i = ν
    · subst hi
      simp [Pi.single_apply, hμν]
      ring
    · simp [hi]
private theorem pathAngle_backward_flow (g : ℝ) (μ ν : Fin 4) (hμν : μ ≠ ν) (i : Fin 4) (m : ℕ)
    (z : IntVec) :
    pathAngle (linearFluxAngle g μ ν fun _ => 0) z (List.replicate m (i, false)) =
      if i = ν then -((m : ℝ) * (g * (z μ : ℝ))) else 0 := by
  induction m generalizing z with
  | zero => simp [pathAngle]
  | succ m ih =>
    rw [List.replicate_succ, pathAngle, ih]
    unfold stepAngle stepShift linearFluxAngle
    by_cases hi : i = ν
    · subst hi
      simp [Pi.single_apply, hμν]
      ring
    · simp [hi]
private theorem pathAngle_axis_segment (g : ℝ) (μ ν : Fin 4) (hμν : μ ≠ ν) (k : Fin 4) (c : ℤ)
    (z : IntVec) :
    pathAngle (linearFluxAngle g μ ν fun _ => 0) z (List.replicate c.natAbs (k, decide (0 ≤ c))) =
      if k = ν then (c : ℝ) * (g * (z μ : ℝ)) else 0 := by
  by_cases h0 : 0 ≤ c
  · have : decide (0 ≤ c) = true := by simp [h0]
    rw [this, pathAngle_forward_flow g μ ν hμν]
    have hc : ((c.natAbs : ℕ) : ℝ) = (c : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_nonneg h0]
    rw [hc]
  · have : decide (0 ≤ c) = false := by simp [h0]
    rw [this, pathAngle_backward_flow g μ ν hμν]
    have hc : ((c.natAbs : ℕ) : ℝ) = - (c : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_neg (not_le.mp h0)]
      push_cast
      rfl
    rw [hc]
    split_ifs <;> ring
private theorem pathAngle_axisPath (g : ℝ) (μ ν : Fin 4) (hμν : μ < ν) (z h : IntVec) :
    pathAngle (linearFluxAngle g μ ν fun _ => 0) z (axisPath h 1) =
      g * ((z μ : ℝ) + (h μ : ℝ)) * (h ν : ℝ) := by
  have hl : axisPath h (1 : Equiv.Perm (Fin 4)) =
      List.replicate (h 0).natAbs (0, decide (0 ≤ h 0)) ++
      (List.replicate (h 1).natAbs (1, decide (0 ≤ h 1)) ++
      (List.replicate (h 2).natAbs (2, decide (0 ≤ h 2)) ++
      (List.replicate (h 3).natAbs (3, decide (0 ≤ h 3))))) := by
    simp [axisPath, List.finRange_succ]
    rfl
  have hs : ∀ k : Fin 4, pathShift (List.replicate (h k).natAbs (k, decide (0 ≤ h k))) =
      Pi.single k (h k) := by
    intro k
    rw [pathShift_replicate]
    unfold stepShift
    funext i
    by_cases hi : i = k
    · subst hi
      by_cases h0 : 0 ≤ h i
      · simp [h0, abs_of_nonneg h0]
      · have h0' : h i < 0 := not_le.mp h0
        simp [h0, abs_of_neg h0']
    · by_cases h0 : 0 ≤ h k <;> simp [h0, hi]
  have hne : μ ≠ ν := hμν.ne
  rw [hl, pathAngle_append, pathAngle_append, pathAngle_append, hs, hs, hs]
  simp only [pathAngle_axis_segment g μ ν hne]
  revert hμν hne
  fin_cases μ <;> fin_cases ν <;> intro hμν hne <;>
    simp_all [Pi.single_apply] <;> ring
private theorem siteOfCoords_eq_of_dvd_local {H : BlockFrame} {k : ℕ} {z z' : IntVec}
    (h : ∀ i, (H.period k i : ℤ) ∣ z' i - z i) :
    (siteOfCoords k z : H.Site k) = siteOfCoords k z' := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_eq_of_dvd <;> assumption
private theorem siteOfCoords_siteCoords_local {H : BlockFrame} {k : ℕ} (y : H.Site k) :
    siteOfCoords k (siteCoords y) = y := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
private theorem period_dvd_sub_siteCoords_local {H : BlockFrame} {k : ℕ} (z : IntVec) (i : Fin 4) :
    (H.period k i : ℤ) ∣ z i - siteCoords (siteOfCoords k z : H.Site k) i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.period_dvd_sub_siteCoords <;> assumption
private theorem period_top (H : BlockFrame) (i : Fin 4) : H.period H.top i = H.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
private theorem period_depth (H : BlockFrame) (i : Fin 4) :
    H.period H.depth i = H.extent i * H.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimizingChart.period_depth <;> assumption
private def blockPoint (L : ℕ) (q h : IntVec) : IntVec := fun i => (L : ℤ) * q i + h i
private theorem cellCentre_siteOfCoords (H : BlockFrame) (q : IntVec) :
    (cellCentre H.depth (siteOfCoords H.top q : H.Cell) : H.Site H.depth) =
      siteOfCoords H.depth fun i => (H.blockSide : ℤ) * q i := by apply _root_.YangMills.Construction.HoleBounds.FromThresholds.cellCentre_siteOfCoords <;> assumption
private theorem enclosingCell_blockPoint (H : BlockFrame) (m : ℕ) (hm : H.blockSide = 2 * m + 1)
    {n : ℕ} (hn : ∀ i, H.extent i = n) (h0 : 0 < n)
    (q h : IntVec) (hh : ∀ i, |h i| ≤ (m : ℤ)) :
    enclosingCell (siteOfCoords H.depth (blockPoint H.blockSide q h) : H.Site H.depth) =
      siteOfCoords H.top q := by apply _root_.YangMills.DeltaSharedProofs.p502341 <;> assumption
private theorem cellOffset_blockPoint (H : BlockFrame) (m : ℕ) (hm : H.blockSide = 2 * m + 1)
    {n : ℕ} (hn : ∀ i, H.extent i = n) (h0 : 0 < n)
    (q h : IntVec) (hh : ∀ i, |h i| ≤ (m : ℤ)) :
    cellOffset (siteOfCoords H.depth (blockPoint H.blockSide q h) : H.Site H.depth) = h := by
  unfold cellOffset
  rw [enclosingCell_blockPoint H m hm hn h0 q h hh, cellCentre_siteOfCoords]
  funext i
  have hP : 0 < H.period H.depth i := by
    rw [period_depth, hn, hm]
    positivity
  have : NeZero (H.period H.depth i) := ⟨hP.ne'⟩
  have hx : (((siteOfCoords H.depth (blockPoint H.blockSide q h) : H.Site H.depth) -
      (siteOfCoords H.depth fun i => (H.blockSide : ℤ) * q i : H.Site H.depth)) :
        H.Site H.depth) i =
      ((h i : ℤ) : ZMod (H.period H.depth i)) := by
    simp [siteOfCoords, blockPoint]
  rw [hx]
  apply (ZMod.valMinAbs_spec _ _).2
  refine ⟨rfl, ?_⟩
  have hbi := abs_le.1 (hh i)
  have hPL : (2 * (m : ℤ) + 1) ≤ (H.period H.depth i : ℤ) := by
    rw [period_depth, hn, hm]
    push_cast
    have : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast h0
    nlinarith
  constructor <;> linarith [hbi.1, hbi.2]
private theorem exists_blockPoint (H : BlockFrame) (m : ℕ) (hm : H.blockSide = 2 * m + 1)
    (x : H.Site H.depth) :
    ∃ q h : IntVec, (∀ i, |h i| ≤ (m : ℤ)) ∧
      x = siteOfCoords H.depth (blockPoint H.blockSide q h) := by apply _root_.YangMills.DeltaSharedProofs.p502172 <;> assumption
theorem linearFieldChartGauge_holds : LinearFieldChartGauge := by
  classical
  intro F X g μ ν n hodd hn hn3 hX hμν U V hpair
  obtain ⟨φ, hU, hV⟩ := hpair
  obtain ⟨m, hm⟩ := hodd
  have hm' : F.blockSide = 2 * m + 1 := hm
  have hLpos : 0 < F.blockSide := by omega
  have h0 : 0 < n := by omega
  have hne : μ ≠ ν := hμν.ne
  set L : ℕ := F.blockSide with hLdef
  have hLr : (L : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hm'
  have hLz : (L : ℤ) = 2 * (m : ℤ) + 1 := by exact_mod_cast hm'
  let γ : F.Site F.depth → UnitQuaternion := fun x =>
    pathHolonomy U (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) 1)
  let α : IntVec → IntVec → ℝ := fun q h => φ (blockPoint L q h) - φ (fun k => (L : ℤ) * q k) +
    g * ((((L : ℤ) * q μ : ℤ) : ℝ) + (h μ : ℝ)) * (h ν : ℝ)
  have hγ : ∀ q h : IntVec, (∀ i, |h i| ≤ (m : ℤ)) →
      γ (siteOfCoords F.depth (blockPoint L q h)) = expUnit (α q h • X) := by
    intro q h hh
    show pathHolonomy U (cellCentre F.depth (enclosingCell (siteOfCoords F.depth (blockPoint L q h))))
      (axisPath (cellOffset (siteOfCoords F.depth (blockPoint L q h))) 1) = _
    rw [enclosingCell_blockPoint F m hm' hn h0 q h hh, cellOffset_blockPoint F m hm' hn h0 q h hh,
      cellCentre_siteOfCoords, pathHolonomy_eq_expUnit hU,
      pathAngle_linearFluxAngle, pathAngle_axisPath g μ ν hμν]
    have hp : (fun k => (F.blockSide : ℤ) * q k) + pathShift (axisPath h 1) = blockPoint L q h := by
      rw [pathShift_axisPath]
      rfl
    rw [hp]
  have hoffb : ∀ (x : F.Site F.depth) (k : Fin 4), |(cellOffset x k : ℝ)| ≤ (m : ℝ) := by
    intro x k
    obtain ⟨q, h, hh, rfl⟩ := exists_blockPoint F m hm' x
    rw [cellOffset_blockPoint F m hm' hn h0 q h hh]
    have := hh k
    have h2 : ((|h k| : ℤ) : ℝ) ≤ ((m : ℤ) : ℝ) := by exact_mod_cast this
    simpa using h2
  let w : F.Site F.depth → Fin 4 → imaginaryQuaternions := fun x i =>
    (if i = μ then -(g * (cellOffset x ν : ℝ))
      else if i = ν ∧ IsCrossingBond (x, i) then g * (L : ℝ) * (cellOffset x μ : ℝ) else 0) • X
  have htree : ∀ b, IsAxialTreeBond b → w b.1 b.2 = 0 := by
    rintro ⟨x, i⟩ ⟨hnc, hl⟩
    show (if i = μ then -(g * (cellOffset x ν : ℝ))
      else if i = ν ∧ IsCrossingBond (x, i) then g * (L : ℝ) * (cellOffset x μ : ℝ) else 0) • X = 0
    by_cases hi : i = μ
    · have := hl ν (by show i < ν; rw [hi]; exact hμν)
      rw [if_pos hi, this]
      simp
    · rw [if_neg hi, if_neg (fun hh => hnc hh.2), zero_smul]
  have hgauge : ∀ x i, _root_.YangMills.Construction.BlockAverages.gaugeTransform γ U x i = chartedField w V x i := by
    intro x i
    obtain ⟨q, h, hh, rfl⟩ := exists_blockPoint F m hm' x
    set z : IntVec := blockPoint L q h with hz
    have hoff := cellOffset_blockPoint F m hm' hn h0 q h hh
    have hcell := enclosingCell_blockPoint F m hm' hn h0 q h hh
    unfold _root_.YangMills.Construction.BlockAverages.gaugeTransform
    rw [hγ q h hh, hU z i]
    by_cases hc : h i = m
    · set q' : IntVec := q + Pi.single i 1 with hq'
      set h' : IntVec := h + Pi.single i 1 - (L : ℤ) • Pi.single i 1 with hh'def
      have hh' : ∀ k, |h' k| ≤ (m : ℤ) := by
        intro k
        by_cases hk : k = i
        · subst hk
          have : h' k = - (m : ℤ) := by
            simp only [hh'def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
              smul_eq_mul, hc]
            rw [hLz]; ring
          rw [this, abs_neg]
          simp
        · have : h' k = h k := by
            simp [hh'def, Pi.single_apply, hk]
          rw [this]
          exact hh k
      have hpt : blockPoint L q' h' = z + Pi.single i 1 := by
        funext k
        simp only [hz, hq', hh'def, blockPoint, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have hx' : (siteOfCoords F.depth z : F.Site F.depth) + unitStep F.depth i =
          siteOfCoords F.depth (blockPoint L q' h') := by
        rw [hpt, siteOfCoords_add_local]; rfl
      have hcell' : enclosingCell ((siteOfCoords F.depth z : F.Site F.depth) + unitStep F.depth i) =
          siteOfCoords F.top q' := by
        rw [hx']; exact enclosingCell_blockPoint F m hm' hn h0 q' h' hh'
      have hcross : IsCrossingBond (siteOfCoords F.depth z, i) := by
        show enclosingCell ((siteOfCoords F.depth z : F.Site F.depth) + unitStep F.depth i) ≠
          enclosingCell (siteOfCoords F.depth z : F.Site F.depth)
        rw [hcell', hcell]
        intro heq
        have h1 := congrFun heq i
        have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
        rw [period_top, hn] at h2
        have h3 : q i - q' i = -1 := by simp [hq']
        rw [h3] at h2
        have h4 : (n : ℤ) ∣ 1 := by simpa using h2
        have h5 : (n : ℤ) ≤ 1 := Int.le_of_dvd one_pos h4
        omega
      have hw : w (siteOfCoords F.depth z) i = (if i = μ then -(g * (h ν : ℝ))
          else if i = ν then g * (L : ℝ) * (h μ : ℝ) else 0) • X := by
        show (if i = μ then -(g * (cellOffset (siteOfCoords F.depth z : F.Site F.depth) ν : ℝ))
          else if i = ν ∧ IsCrossingBond (siteOfCoords F.depth z, i) then
            g * (L : ℝ) * (cellOffset (siteOfCoords F.depth z : F.Site F.depth) μ : ℝ) else 0) • X = _
        rw [hoff]
        simp only [hcross, and_true]
      rw [hx', hγ q' h' hh']
      unfold chartedField
      rw [if_pos hcross, hcell, hV q i, hw, expUnit_smul_inv, ← expUnit_add_smul,
        ← expUnit_add_smul, ← expUnit_add_smul]
      congr 2
      have hzμ : (z μ : ℝ) = (L : ℝ) * (q μ : ℝ) + (h μ : ℝ) := by
        simp [hz, blockPoint]
      have hqμ : ((q' μ : ℤ) : ℝ) = (q μ : ℝ) + (if i = μ then 1 else 0) := by
        by_cases hi : i = μ
        · subst hi; simp [hq']
        · simp [hq', hi, Ne.symm hi]
      have hhμ : ((h' μ : ℤ) : ℝ) = (h μ : ℝ) + (if i = μ then 1 - (L : ℝ) else 0) := by
        by_cases hi : i = μ
        · subst hi; simp [hh'def]; ring
        · simp [hh'def, hi, Ne.symm hi]
      have hhν : ((h' ν : ℤ) : ℝ) = (h ν : ℝ) + (if i = ν then 1 - (L : ℝ) else 0) := by
        by_cases hi : i = ν
        · subst hi; simp [hh'def]; ring
        · simp [hh'def, hi, Ne.symm hi]
      simp only [α, hpt, linearFluxAngle]
      push_cast
      rw [hzμ, hqμ, hhμ, hhν]
      by_cases hiμ : i = μ
      · have hiν : i ≠ ν := by rw [hiμ]; exact hne
        simp only [if_pos hiμ, if_neg hiν]
        ring
      · by_cases hiν : i = ν
        · simp only [if_neg hiμ, if_pos hiν]
          ring
        · simp only [if_neg hiμ, if_neg hiν]
          ring
    · set h' : IntVec := h + Pi.single i 1 with hh'def
      have hh' : ∀ k, |h' k| ≤ (m : ℤ) := by
        intro k
        by_cases hk : k = i
        · subst hk
          have h1 := abs_le.1 (hh k)
          have : h' k = h k + 1 := by simp [hh'def]
          rw [this, abs_le]
          omega
        · have : h' k = h k := by simp [hh'def, Pi.single_apply, hk]
          rw [this]
          exact hh k
      have hpt : blockPoint L q h' = z + Pi.single i 1 := by
        funext k
        simp only [hz, hh'def, blockPoint, Pi.add_apply]
        ring
      have hx' : (siteOfCoords F.depth z : F.Site F.depth) + unitStep F.depth i =
          siteOfCoords F.depth (blockPoint L q h') := by
        rw [hpt, siteOfCoords_add_local]; rfl
      have hcross : ¬ IsCrossingBond (siteOfCoords F.depth z, i) := by
        intro hcr
        apply hcr
        show enclosingCell ((siteOfCoords F.depth z : F.Site F.depth) + unitStep F.depth i) =
          enclosingCell (siteOfCoords F.depth z : F.Site F.depth)
        rw [hx', enclosingCell_blockPoint F m hm' hn h0 q h' hh', hcell]
      have hw : w (siteOfCoords F.depth z) i = (if i = μ then -(g * (h ν : ℝ)) else 0) • X := by
        show (if i = μ then -(g * (cellOffset (siteOfCoords F.depth z : F.Site F.depth) ν : ℝ))
          else if i = ν ∧ IsCrossingBond (siteOfCoords F.depth z, i) then
            g * (L : ℝ) * (cellOffset (siteOfCoords F.depth z : F.Site F.depth) μ : ℝ) else 0) • X = _
        rw [hoff]
        simp only [hcross, and_false, if_false]
      have key : expUnit (α q h • X) * expUnit (linearFluxAngle g μ ν φ z i • X) *
          (expUnit (α q h' • X))⁻¹ = expUnit (w (siteOfCoords F.depth z) i) := by
        rw [hw, expUnit_smul_inv, ← expUnit_add_smul, ← expUnit_add_smul]
        congr 2
        have hzμ : (z μ : ℝ) = (L : ℝ) * (q μ : ℝ) + (h μ : ℝ) := by
          simp [hz, blockPoint]
        have hhμ : ((h' μ : ℤ) : ℝ) = (h μ : ℝ) + (if i = μ then 1 else 0) := by
          by_cases hi : i = μ
          · subst hi; simp [hh'def]
          · simp [hh'def, hi, Ne.symm hi]
        have hhν : ((h' ν : ℤ) : ℝ) = (h ν : ℝ) + (if i = ν then 1 else 0) := by
          by_cases hi : i = ν
          · subst hi; simp [hh'def]
          · simp [hh'def, hi, Ne.symm hi]
        simp only [α, hpt, linearFluxAngle]
        push_cast
        rw [hzμ, hhμ, hhν]
        by_cases hiμ : i = μ
        · have hiν : i ≠ ν := by rw [hiμ]; exact hne
          simp only [if_pos hiμ, if_neg hiν]
          ring
        · by_cases hiν : i = ν
          · simp only [if_neg hiμ, if_pos hiν]
            ring
          · simp only [if_neg hiμ, if_neg hiν]
            ring
      rw [hx', hγ q h' hh', key]
      unfold chartedField
      rw [if_neg hcross]
      by_cases ht : IsAxialTreeBond (siteOfCoords F.depth z, i)
      · rw [if_pos ht]
        have h1 := htree _ ht
        have h2 : w (siteOfCoords F.depth z) i = 0 := h1
        rw [h2]
        have h3 : (0 : imaginaryQuaternions) = (0 : ℝ) • X := by simp
        rw [h3, expUnit_zero_smul]
      · rw [if_neg ht]
  refine ⟨γ, w, ?_, ?_, hgauge, htree, ?_⟩
  · intro y
    have hy : cellCentre F.depth y =
        (siteOfCoords F.depth (blockPoint L (siteCoords y) 0) : F.Site F.depth) := by
      conv_lhs => rw [← siteOfCoords_siteCoords_local y]
      rw [cellCentre_siteOfCoords]
      congr 1
      funext k
      simp [blockPoint, hLdef]
    have ho0 : cellOffset (cellCentre F.depth y) = 0 := by
      rw [hy, cellOffset_blockPoint F m hm' hn h0 _ _ (by simp)]
    show pathHolonomy U (cellCentre F.depth (enclosingCell (cellCentre F.depth y)))
      (axisPath (cellOffset (cellCentre F.depth y)) 1) = 1
    rw [ho0]
    have : axisPath (0 : IntVec) (1 : Equiv.Perm (Fin 4)) = [] := by
      simp [axisPath]
    rw [this]
    rfl
  · intro x
    obtain ⟨q, h, hh, rfl⟩ := exists_blockPoint F m hm' x
    exact ⟨_, hγ q h hh⟩
  · intro x i
    have hLr1 : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
    have hmL : (m : ℝ) ≤ L := by
      rw [hLr]
      have : (0 : ℝ) ≤ m := by positivity
      linarith
    have hg0 : 0 ≤ |g| := abs_nonneg g
    show ‖(if i = μ then -(g * (cellOffset x ν : ℝ))
      else if i = ν ∧ IsCrossingBond (x, i) then g * (L : ℝ) * (cellOffset x μ : ℝ) else 0) • X‖ ≤ _
    rw [norm_smul, hX, mul_one, Real.norm_eq_abs]
    split_ifs with h1 h2
    · rw [abs_neg, abs_mul]
      have := hoffb x ν
      have h4 : |g| * |(cellOffset x ν : ℝ)| ≤ |g| * L :=
        mul_le_mul_of_nonneg_left (this.trans hmL) hg0
      have h5 : |g| * (L : ℝ) * 1 ≤ |g| * L * L :=
        mul_le_mul_of_nonneg_left hLr1 (mul_nonneg hg0 (by positivity))
      nlinarith
    · rw [abs_mul, abs_mul, Nat.abs_cast]
      have := hoffb x μ
      have h3 : |g| * (L : ℝ) * |(cellOffset x μ : ℝ)| ≤ |g| * L * L :=
        mul_le_mul_of_nonneg_left (this.trans hmL) (by positivity)
      nlinarith
    · simp
      positivity
end YangMills.Construction.ColdStepAtMirrorFrames
end
