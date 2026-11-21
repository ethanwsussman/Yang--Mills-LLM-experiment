import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheColdStepProof
import YangMills.Construction.ColdStepAtMirrorFrames.SizeOfAFlatResponseProof
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheMarkedIntegralOfAllBlocksProof
import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingIsCold
import YangMills.Construction.ClusterExpansionOfAStep.MeanOfAContourAtAColdTop
import YangMills.Construction.ColdChainAtEveryLevel.FloorOfTheChartFormProof
import YangMills.Construction.RunningCouplingSlope.LeastPointReadsTheChainProof
import YangMills.Construction.SummableBoundsOfTheFlow.LinesOfTwoTopsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames
namespace ClusterExpansionOfAStep
namespace ContourApprox
open TopLevelSites
variable {F : BlockFrame}
open Classical in
def crossingField (V : F.GaugeField F.top) : F.GaugeField F.depth := fun x i =>
  if IsCrossingBond (x, i) then V (enclosingCell x) i else 1
abbrev blockSite (z : F.Cell) (o : Fin 4 → ℤ) : F.Site F.depth := cellCentre F.depth z + siteOfCoords F.depth o
theorem siteOfCoords_add (a b : Fin 4 → ℤ) :
    (siteOfCoords F.depth (a + b) : F.Site F.depth) = siteOfCoords F.depth a + siteOfCoords F.depth b := by
  funext l
  simp [siteOfCoords]
theorem blockSite_add_siteOfCoords (z : F.Cell) (o a : Fin 4 → ℤ) :
    blockSite z o + siteOfCoords F.depth a = blockSite z (o + a) := by
  simp only [blockSite, _root_.YangMills.Construction.ClusterExpansionOfAStep.ContourApprox.siteOfCoords_add, add_assoc]
theorem axisPath_eq_append (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) : axisPath h π =
    axisSegment (h (π 0)) (π 0) ++ axisSegment (h (π 1)) (π 1) ++ axisSegment (h (π 2)) (π 2) ++
      axisSegment (h (π 3)) (π 3) := by
  have e : List.finRange 4 = [0, 1, 2, 3] := by decide
  simp [axisPath, e, axisSegment, List.flatMap_cons, List.append_assoc]
theorem eq_perm_apply_cases (π : Equiv.Perm (Fin 4)) (l : Fin 4) :
    l = π 0 ∨ l = π 1 ∨ l = π 2 ∨ l = π 3 := by
  obtain ⟨k, rfl⟩ := π.surjective l
  fin_cases k <;> simp
theorem sum_single_perm_apply (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    Pi.single (π 0) (h (π 0)) + Pi.single (π 1) (h (π 1)) + Pi.single (π 2) (h (π 2)) +
      Pi.single (π 3) (h (π 3)) = h := by
  funext l
  have h01 : π 0 ≠ π 1 := fun q => by simpa using π.injective q
  have h02 : π 0 ≠ π 2 := fun q => by simpa using π.injective q
  have h03 : π 0 ≠ π 3 := fun q => by simpa using π.injective q
  have h12 : π 1 ≠ π 2 := fun q => by simpa using π.injective q
  have h13 : π 1 ≠ π 3 := fun q => by simpa using π.injective q
  have h23 : π 2 ≠ π 3 := fun q => by simpa using π.injective q
  rcases eq_perm_apply_cases π l with rfl | rfl | rfl | rfl <;>
    simp [Pi.single_apply, h01, h02, h03, h12, h13, h23, h01.symm, h02.symm, h03.symm, h12.symm,
      h13.symm, h23.symm]
theorem axisPath_displacement (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    ((axisPath h π).map (stepDisplacement (F := F) F.depth)).sum = siteOfCoords F.depth h := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AxialResponseDecay.pathDisplacement_axisPath <;> assumption
theorem mem_centredCube_of_partial {L : ℕ} {h : Fin 4 → ℤ} (hh : h ∈ centredCube L) {o : Fin 4 → ℤ}
    (ho : ∀ l, o l = 0 ∨ o l = h l) (hq : 0 ≤ halfWidth L) : o ∈ centredCube L := by
  rw [_root_.YangMills.Construction.TopLevelSites.mem_centredCube_iff] at hh ⊢
  intro l
  rcases ho l with e | e
  · rw [e]
    omega
  · rw [e]
    exact hh l
theorem blockSite_zero_add_add (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) (i : Fin 4) (h : Fin 4 → ℤ) :
    blockSite (F := F) z 0 + (siteOfCoords F.depth h + siteOfCoords F.depth (Pi.single i (F.blockSide : ℤ))) =
      blockSite (z + unitStep F.top i) 0 + siteOfCoords F.depth h := by
  have h0 : (siteOfCoords F.depth (0 : Fin 4 → ℤ) : F.Site F.depth) = 0 := by
    funext l
    simp [siteOfCoords]
  simp only [blockSite, h0, add_zero]
  rw [cellCentre_add_unitStep hs z i]
  abel
variable (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (V : F.GaugeField F.top) (z : F.Cell)
include hL hs
theorem crossingField_eq_one {o : Fin 4 → ℤ} (hh : o ∈ centredCube F.blockSide) {i : Fin 4}
    (hne : o i ≠ halfWidth F.blockSide) : crossingField V (blockSite z o) i = 1 := by
  unfold crossingField
  rw [if_neg]
  rw [isCrossingBond_iff hL hs z o hh i]
  exact hne
theorem pathHolonomy_replicate_forward (i : Fin 4) : ∀ (m : ℕ) (o : Fin 4 → ℤ),
    o ∈ centredCube F.blockSide → o i + m ≤ halfWidth F.blockSide →
    pathHolonomy (crossingField V) (blockSite z o) (List.replicate m (i, true)) = 1 := by
  intro m
  induction m with
  | zero => intro o _ _; rfl
  | succ m ih =>
    intro o hh hb
    have hin : o + Pi.single i 1 ∈ centredCube F.blockSide := by
      rw [_root_.YangMills.Construction.TopLevelSites.mem_centredCube_iff] at hh ⊢
      intro l
      by_cases hl : l = i
      · subst hl
        have := hh l
        simp only [Pi.add_apply, Pi.single_eq_same]
        push_cast at hb
        omega
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
        exact hh l
    have hne : o i ≠ halfWidth F.blockSide := by
      push_cast at hb
      omega
    rw [List.replicate_succ]
    simp only [pathHolonomy, linkValue, if_true, stepDisplacement]
    rw [crossingField_eq_one hL hs V z hh hne, one_mul, centre_add_add_unitStep]
    refine ih _ hin ?_
    simp only [Pi.add_apply, Pi.single_eq_same]
    push_cast at hb
    omega
theorem pathHolonomy_replicate_backward (i : Fin 4) : ∀ (m : ℕ) (o : Fin 4 → ℤ),
    o ∈ centredCube F.blockSide → - halfWidth F.blockSide ≤ o i - m →
    pathHolonomy (crossingField V) (blockSite z o) (List.replicate m (i, false)) = 1 := by
  intro m
  induction m with
  | zero => intro o _ _; rfl
  | succ m ih =>
    intro o hh hb
    have hin : o + Pi.single i (-1) ∈ centredCube F.blockSide := by
      rw [_root_.YangMills.Construction.TopLevelSites.mem_centredCube_iff] at hh ⊢
      intro l
      by_cases hl : l = i
      · subst hl
        have := hh l
        simp only [Pi.add_apply, Pi.single_eq_same]
        push_cast at hb
        omega
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
        exact hh l
    have hback : blockSite z o - unitStep F.depth i = blockSite z (o + Pi.single i (-1)) := by
      have h1 := centre_add_add_unitStep z (o + Pi.single i (-1)) i
      have h2 : o + Pi.single i (-1) + Pi.single i 1 = o := by
        funext l
        by_cases hl : l = i
        · subst hl; simp
        · simp [Pi.single_eq_of_ne hl]
      rw [h2] at h1
      exact (eq_sub_of_add_eq h1).symm
    have hne : (o + Pi.single i (-1) : Fin 4 → ℤ) i ≠ halfWidth F.blockSide := by
      have := ((_root_.YangMills.Construction.TopLevelSites.mem_centredCube_iff o).1 hh) i
      simp only [Pi.add_apply, Pi.single_eq_same]
      omega
    rw [List.replicate_succ]
    simp only [pathHolonomy, linkValue, stepDisplacement, Bool.false_eq_true, if_false]
    rw [hback, crossingField_eq_one hL hs V z hin hne, inv_one, one_mul, ← sub_eq_add_neg, hback]
    refine ih _ hin ?_
    simp only [Pi.add_apply, Pi.single_eq_same]
    push_cast at hb
    omega
theorem pathHolonomy_axisSegment {o : Fin 4 → ℤ} (hh : o ∈ centredCube F.blockSide) (k : Fin 4) (c : ℤ)
    (h2 : o + Pi.single k c ∈ centredCube F.blockSide) :
    pathHolonomy (crossingField V) (blockSite z o) (axisSegment c k) = 1 := by
  have hb := ((_root_.YangMills.Construction.TopLevelSites.mem_centredCube_iff _).1 h2) k
  simp only [Pi.add_apply, Pi.single_eq_same] at hb
  unfold axisSegment
  by_cases hc : 0 ≤ c
  · rw [decide_eq_true hc]
    exact pathHolonomy_replicate_forward hL hs V z k _ o hh (by omega)
  · rw [decide_eq_false hc]
    exact pathHolonomy_replicate_backward hL hs V z k _ o hh (by omega)
theorem pathHolonomy_axisPath {h : Fin 4 → ℤ} (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    pathHolonomy (crossingField V) (blockSite z 0) (axisPath h π) = 1 := by
  have hq : 0 ≤ halfWidth F.blockSide := by
    have := ((_root_.YangMills.Construction.TopLevelSites.mem_centredCube_iff h).1 hh) 0
    omega
  have h01 : π 0 ≠ π 1 := fun q => by simpa using π.injective q
  have h02 : π 0 ≠ π 2 := fun q => by simpa using π.injective q
  have h03 : π 0 ≠ π 3 := fun q => by simpa using π.injective q
  have h12 : π 1 ≠ π 2 := fun q => by simpa using π.injective q
  have h13 : π 1 ≠ π 3 := fun q => by simpa using π.injective q
  have h23 : π 2 ≠ π 3 := fun q => by simpa using π.injective q
  set o1 : Fin 4 → ℤ := 0 + Pi.single (π 0) (h (π 0)) with ho1
  set o2 : Fin 4 → ℤ := o1 + Pi.single (π 1) (h (π 1)) with ho2
  set o3 : Fin 4 → ℤ := o2 + Pi.single (π 2) (h (π 2)) with ho3
  set o4 : Fin 4 → ℤ := o3 + Pi.single (π 3) (h (π 3)) with ho4
  have c0 : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide :=
    mem_centredCube_of_partial hh (fun _ => Or.inl rfl) hq
  have c1 : o1 ∈ centredCube F.blockSide := mem_centredCube_of_partial hh (fun l => by
    by_cases e : l = π 0
    · subst e; right; simp [ho1]
    · left; simp [ho1, Pi.single_eq_of_ne e]) hq
  have c2 : o2 ∈ centredCube F.blockSide := mem_centredCube_of_partial hh (fun l => by
    rcases eq_perm_apply_cases π l with rfl | rfl | rfl | rfl <;>
      simp [ho1, ho2, Pi.single_apply, h01, h02, h03, h12, h13, h23, h01.symm, h02.symm, h03.symm,
        h12.symm, h13.symm, h23.symm]) hq
  have c3 : o3 ∈ centredCube F.blockSide := mem_centredCube_of_partial hh (fun l => by
    rcases eq_perm_apply_cases π l with rfl | rfl | rfl | rfl <;>
      simp [ho1, ho2, ho3, Pi.single_apply, h01, h02, h03, h12, h13, h23, h01.symm, h02.symm, h03.symm,
        h12.symm, h13.symm, h23.symm]) hq
  have c4 : o4 ∈ centredCube F.blockSide := by
    have : o4 = h := by
      simp only [ho4, ho3, ho2, ho1, zero_add]
      exact sum_single_perm_apply h π
    rw [this]
    exact hh
  rw [axisPath_eq_append, pathHolonomy_append, pathHolonomy_append, pathHolonomy_append,
    pathHolonomy_axisSegment hL hs V z c0 _ _ c1]
  simp only [List.map_append, List.sum_append, axisSegment_displacement, one_mul]
  rw [blockSite_add_siteOfCoords, pathHolonomy_axisSegment hL hs V z c1 _ _ c2, one_mul, ← add_assoc,
    blockSite_add_siteOfCoords, blockSite_add_siteOfCoords,
    pathHolonomy_axisSegment hL hs V z c2 _ _ c3, one_mul, ← add_assoc, ← add_assoc,
    blockSite_add_siteOfCoords, blockSite_add_siteOfCoords, blockSite_add_siteOfCoords]
  exact pathHolonomy_axisSegment hL hs V z c3 _ _ c4
theorem pathHolonomy_replicate_side {ξ : Fin 4 → ℤ} (hh : ξ ∈ centredCube F.blockSide) (i : Fin 4) :
    pathHolonomy (crossingField V) (blockSite z ξ) (List.replicate F.blockSide (i, true)) = V z i := by
  obtain ⟨k, hk⟩ := hL
  have hLz : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have hq : halfWidth F.blockSide = k := by
    unfold halfWidth
    rw [hLz]
    omega
  have hb := ((_root_.YangMills.Construction.TopLevelSites.mem_centredCube_iff ξ).1 hh) i
  rw [hq] at hb
  obtain ⟨m₁, hm₁⟩ : ∃ m : ℕ, (m : ℤ) = k - ξ i := ⟨(k - ξ i).toNat, by omega⟩
  obtain ⟨m₃, hm₃⟩ : ∃ m : ℕ, (m : ℤ) = k + ξ i := ⟨(k + ξ i).toNat, by omega⟩
  have hsplit : F.blockSide = m₁ + (1 + m₃) := by omega
  have hodd : Odd F.blockSide := ⟨k, hk⟩
  set o : Fin 4 → ℤ := ξ + Pi.single i (m₁ : ℤ) with ho
  have hoi : o i = halfWidth F.blockSide := by
    simp only [ho, Pi.add_apply, Pi.single_eq_same, hq]
    omega
  have hoc : o ∈ centredCube F.blockSide := by
    rw [_root_.YangMills.Construction.TopLevelSites.mem_centredCube_iff] at hh ⊢
    intro l
    by_cases hl : l = i
    · subst hl
      rw [hoi, hq]
      omega
    · simp only [ho, Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
      exact hh l
  have hvec : ((List.replicate m₁ ((i, true) : PathStep)).map (stepDisplacement (F := F) F.depth)).sum =
      siteOfCoords F.depth (Pi.single i (m₁ : ℤ)) := by
    have h1 := axisSegment_displacement (F := F) (j := F.depth) (m₁ : ℤ) i
    have h2 : axisSegment (m₁ : ℤ) i = List.replicate m₁ ((i, true) : PathStep) := by
      unfold axisSegment
      simp
    rwa [h2] at h1
  obtain ⟨hoc', hacross⟩ := centre_add_add_unitStep_of_edge hodd hs z o hoc i hoi
  have hcross : IsCrossingBond ((blockSite z o, i) : F.Site F.depth × Fin 4) :=
    (isCrossingBond_iff hodd hs z o hoc i).2 hoi
  have hval : crossingField V (blockSite z o) i = V z i := by
    unfold crossingField
    rw [if_pos hcross, enclosingCell_centre_add hodd hs z o hoc]
  rw [hsplit, List.replicate_add, pathHolonomy_append,
    pathHolonomy_replicate_forward hodd hs V z i m₁ ξ hh (by rw [hq]; omega),
    one_mul, hvec, blockSite_add_siteOfCoords, List.replicate_add, pathHolonomy_append]
  have hone : pathHolonomy (crossingField V) (blockSite z (ξ + Pi.single i (m₁ : ℤ)))
      (List.replicate 1 ((i, true) : PathStep)) = V z i := by
    simp only [List.replicate_one, pathHolonomy, linkValue, if_true, mul_one]
    exact hval
  rw [hone]
  have hend : blockSite z (ξ + Pi.single i (m₁ : ℤ)) +
      ((List.replicate 1 ((i, true) : PathStep)).map (stepDisplacement (F := F) F.depth)).sum =
      blockSite (z + unitStep F.top i) (o + Pi.single i (1 - (F.blockSide : ℤ))) := by
    simp only [List.replicate_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      stepDisplacement, if_true]
    exact hacross
  rw [hend, pathHolonomy_replicate_forward hodd hs V (z + unitStep F.top i) i m₃ _ hoc' ?_, mul_one]
  simp only [Pi.add_apply, Pi.single_eq_same]
  rw [hoi, hq, hLz]
  omega
omit hL hs in
theorem reversePath_displacement {j : ℕ} (r : List PathStep) :
    ((reversePath r).map (stepDisplacement (F := F) j)).sum = - (r.map (stepDisplacement (F := F) j)).sum := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_reversePath <;> assumption
omit hL hs in
theorem pathHolonomy_reversePath {j : ℕ} (X : F.GaugeField j) (l : List PathStep) (x : F.Site j) :
    pathHolonomy X (x + (l.map (stepDisplacement (F := F) j)).sum) (reversePath l) =
      (pathHolonomy X x l)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_reversePath <;> assumption
theorem pathHolonomy_bondContour {h : Fin 4 → ℤ} (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4))
    (i : Fin 4) :
    pathHolonomy (crossingField V) (_root_.YangMills.Construction.BlockAverages.refineSite (j := F.depth) z) (bondContour F.blockSide h π i) = V z i := by
  have hd : _root_.YangMills.Construction.BlockAverages.refineSite (j := F.depth) z = blockSite z 0 := by
    funext k
    have he : F.top - F.depth = 1 := by simp [BlockFrame.top]
    show (((F.blockSide : ℤ) * siteCoords z k : ℤ) : ZMod (F.period F.depth k)) =
      (((F.blockSide : ℤ) ^ (F.top - F.depth) * siteCoords z k : ℤ) : ZMod (F.period F.depth k)) +
        (((0 : Fin 4 → ℤ) k : ℤ) : ZMod _)
    rw [he, pow_one]
    simp
  have hvec : ((List.replicate F.blockSide ((i, true) : PathStep)).map
      (stepDisplacement (F := F) F.depth)).sum = siteOfCoords F.depth (Pi.single i (F.blockSide : ℤ)) := by
    have h1 := axisSegment_displacement (F := F) (j := F.depth) (F.blockSide : ℤ) i
    have h2 : axisSegment (F.blockSide : ℤ) i = List.replicate F.blockSide ((i, true) : PathStep) := by
      unfold axisSegment
      simp
    rwa [h2] at h1
  have hz : (blockSite z 0 : F.Site F.depth) + siteOfCoords F.depth h = blockSite z h := by
    rw [blockSite_add_siteOfCoords, zero_add]
  unfold bondContour
  rw [hd, pathHolonomy_append, pathHolonomy_append, pathHolonomy_axisPath hL hs V z hh π, one_mul,
    axisPath_displacement, hz, pathHolonomy_replicate_side hL hs V z hh i]
  simp only [List.map_append, List.sum_append, axisPath_displacement, hvec]
  have hend : blockSite z 0 + (siteOfCoords F.depth h + siteOfCoords F.depth (Pi.single i (F.blockSide : ℤ))) =
      blockSite (z + unitStep F.top i) 0 + ((axisPath h π).map (stepDisplacement (F := F) F.depth)).sum := by
    rw [axisPath_displacement, blockSite_zero_add_add hs z i h]
  rw [hend, pathHolonomy_reversePath, pathHolonomy_axisPath hL hs V (z + unitStep F.top i) hh π]
  simp
omit hL hs V z in
theorem norm_expUnit_sub_one_le (w : imaginaryQuaternions) :
    ‖((expUnit w : UnitQuaternion) : ℍ[ℝ]) - ((1 : UnitQuaternion) : ℍ[ℝ])‖ ≤ ‖(w : ℍ[ℝ])‖ := by
  have h := norm_expUnit_sub_le w 0
  have e : ((expUnit (0 : imaginaryQuaternions) : UnitQuaternion) : ℍ[ℝ]) = ((1 : UnitQuaternion) : ℍ[ℝ]) := by
    rw [coe_expUnit]
    simp
  rw [e] at h
  simpa using h
omit hL hs in
theorem norm_chartedField_sub_crossingField_le (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (B : ℝ)
    (hB : ∀ x i, ‖(w x i : ℍ[ℝ])‖ ≤ B) (x : F.Site F.depth) (i : Fin 4) :
    ‖((chartedField w V x i : UnitQuaternion) : ℍ[ℝ]) - ((crossingField V x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x i)
  unfold chartedField crossingField
  by_cases hc : IsCrossingBond (x, i)
  · rw [if_pos hc, if_pos hc]
    have h1 := norm_mul_sub_mul_le (expUnit (w x i)) 1 (V (enclosingCell x) i) (V (enclosingCell x) i)
    simp only [one_mul, sub_self, norm_zero, add_zero] at h1
    exact h1.trans ((norm_expUnit_sub_one_le (w x i)).trans (hB x i))
  · rw [if_neg hc, if_neg hc]
    by_cases ht : IsAxialTreeBond (x, i)
    · rw [if_pos ht]
      simpa using hB0
    · rw [if_neg ht]
      exact (norm_expUnit_sub_one_le (w x i)).trans (hB x i)
omit hL hs V z in
theorem norm_pathHolonomy_sub_le {j : ℕ} (X Y : F.GaugeField j) (B : ℝ)
    (h : ∀ x i, ‖((X x i : UnitQuaternion) : ℍ[ℝ]) - ((Y x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ B)
    (l : List PathStep) (x : F.Site j) :
    ‖((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ]) - ((pathHolonomy Y x l : UnitQuaternion) : ℍ[ℝ])‖ ≤
      l.length * B := by apply _root_.YangMills.Construction.DerivativeInterpolation.HolonomyPerturbation.norm_sub_pathHolonomy_le <;> assumption
omit hL hs V z in
theorem length_reversePath (l : List PathStep) : (reversePath l).length = l.length := by apply _root_.YangMills.Construction.BlockAverages.ChartFloor.length_reversePath <;> assumption
theorem length_bondContour_le {h : Fin 4 → ℤ} (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4))
    (i : Fin 4) : ((bondContour F.blockSide h π i).length : ℝ) ≤ 5 * F.blockSide := by
  obtain ⟨k, hk⟩ := hL
  have hLz : (F.blockSide : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have hq : halfWidth F.blockSide = k := by
    unfold halfWidth
    rw [hLz]
    omega
  have hb : ∀ l, (h l).natAbs ≤ k := fun l => by
    have := ((_root_.YangMills.Construction.TopLevelSites.mem_centredCube_iff h).1 hh) l
    rw [hq] at this
    omega
  have hleg : (axisPath h π).length ≤ 4 * k := by
    rw [axisPath_eq_append]
    simp only [List.length_append, axisSegment, List.length_replicate]
    have := hb (π 0)
    have := hb (π 1)
    have := hb (π 2)
    have := hb (π 3)
    omega
  unfold bondContour
  simp only [List.length_append, List.length_replicate, length_reversePath]
  have : (axisPath h π).length + F.blockSide + (axisPath h π).length ≤ 5 * F.blockSide := by omega
  exact_mod_cast this
theorem norm_contourAverage_sub_le (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (B : ℝ)
    (hB : ∀ x i, ‖(w x i : ℍ[ℝ])‖ ≤ B) (c : F.Cell × Fin 4) :
    ‖_root_.YangMills.Construction.BlockAverages.contourAverage (j := F.depth) (chartedField w V) c - ((V c.1 c.2 : UnitQuaternion) : ℍ[ℝ])‖ ≤
      5 * F.blockSide * B := by
  have hodd := hL
  obtain ⟨q, hq⟩ := id hL
  have hLpos : (0 : ℝ) < F.blockSide := by
    have : 0 < F.blockSide := by omega
    exact_mod_cast this
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (blockSite c.1 0) 0)
  have hcard : ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by
    have h1 : (centredCube F.blockSide).card = F.blockSide ^ 4 := by
      obtain ⟨k, hk⟩ := hodd
      unfold centredCube
      rw [Fintype.card_piFinset, hk]
      simp [Int.card_Icc]
      omega
    rw [h1]
    push_cast
    rfl
  have hperm : (Fintype.card (Equiv.Perm (Fin 4)) : ℝ) = 24 := by
    rw [Fintype.card_perm]
    norm_num [Nat.factorial]
  have hone : ((V c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) =
      (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ _h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4),
        ((V c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) := by
    simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
    rw [smul_smul, smul_smul, hcard, hperm]
    have : 1 / (24 * (F.blockSide : ℝ) ^ 4) * (F.blockSide : ℝ) ^ 4 * 24 = 1 := by
      field_simp
    rw [this, one_smul]
  unfold _root_.YangMills.Construction.BlockAverages.contourAverage
  rw [hone, ← smul_sub, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  rw [norm_smul]
  have hterm : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy (chartedField w V) (_root_.YangMills.Construction.BlockAverages.refineSite (j := F.depth) c.1)
          (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) -
        ((V c.1 c.2 : UnitQuaternion) : ℍ[ℝ])‖ ≤ 5 * F.blockSide * B := by
    intro h hh π
    have h1 := norm_pathHolonomy_sub_le (chartedField w V) (crossingField V) B
      (fun x i => norm_chartedField_sub_crossingField_le V w B hB x i)
      (bondContour F.blockSide h π c.2) (_root_.YangMills.Construction.BlockAverages.refineSite (j := F.depth) c.1)
    rw [pathHolonomy_bondContour hL hs V c.1 hh π c.2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (length_bondContour_le hL hs hh π c.2) hB0)
  have hsum : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      (((pathHolonomy (chartedField w V) (_root_.YangMills.Construction.BlockAverages.refineSite (j := F.depth) c.1)
          (bondContour F.blockSide h π c.2) : UnitQuaternion) : ℍ[ℝ]) -
        ((V c.1 c.2 : UnitQuaternion) : ℍ[ℝ]))‖ ≤
        (F.blockSide : ℝ) ^ 4 * (24 * (5 * F.blockSide * B)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (24 * (5 * F.blockSide * B)) fun h hh => ?_).trans ?_
    · refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ (5 * F.blockSide * B) fun π _ => hterm h hh π).trans ?_
      rw [nsmul_eq_mul, Finset.card_univ, hperm]
    · rw [nsmul_eq_mul, hcard]
  have hc0 : ‖(1 / (24 * (F.blockSide : ℝ) ^ 4) : ℝ)‖ = 1 / (24 * (F.blockSide : ℝ) ^ 4) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hc0]
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _ ≤
        1 / (24 * (F.blockSide : ℝ) ^ 4) * ((F.blockSide : ℝ) ^ 4 * (24 * (5 * F.blockSide * B))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 5 * F.blockSide * B := by field_simp
end ContourApprox
namespace TorusTransfer
theorem cast_intCast_of_eq (P m : ℕ) (h : P = m) (z : ℤ) :
    ((((z : ZMod m)).cast : ℤ) : ZMod P) = (z : ZMod P) := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.cast_intCast_of_eq <;> assumption
variable {H : BlockFrame} {m : ℕ}
theorem toTorusSite_torusSiteInFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusFields.TorusSite m) :
    TorusLumps.toTorusSite m (StepCosts.torusSiteInFrame H j x) = x := by apply _root_.YangMills.Construction.TorusLevels.toTorusSite_torusSiteInFrame <;> assumption
theorem torusSiteInFrame_toTorusSite (j : ℕ) (hm : ∀ i, H.period j i = m) (y : H.Site j) :
    StepCosts.torusSiteInFrame H j (TorusLumps.toTorusSite m y) = y := by apply _root_.YangMills.Construction.TorusLevels.torusSiteInFrame_toTorusSite <;> assumption
theorem torusSiteInFrame_add (j : ℕ) (hm : ∀ i, H.period j i = m) (x y : TorusFields.TorusSite m) :
    StepCosts.torusSiteInFrame H j (x + y) =
      StepCosts.torusSiteInFrame H j x + StepCosts.torusSiteInFrame H j y := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_add <;> assumption
theorem torusSiteInFrame_unitStep (j : ℕ) (hm : ∀ i, H.period j i = m) (i : Fin 4) :
    StepCosts.torusSiteInFrame H j (TorusFields.unitStep m i) = unitStep j i := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_unitStep <;> assumption
theorem torusSiteInFrame_neg (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusFields.TorusSite m) :
    StepCosts.torusSiteInFrame H j (-x) = - StepCosts.torusSiteInFrame H j x := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusSiteInFrame_neg <;> assumption
theorem torusSiteInFrame_sub (j : ℕ) (hm : ∀ i, H.period j i = m) (x y : TorusFields.TorusSite m) :
    StepCosts.torusSiteInFrame H j (x - y) =
      StepCosts.torusSiteInFrame H j x - StepCosts.torusSiteInFrame H j y := by
  rw [sub_eq_add_neg, torusSiteInFrame_add j hm, torusSiteInFrame_neg j hm, sub_eq_add_neg]
theorem readAtLevel_torusSiteInFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (W : TorusFields.TorusField m)
    (x : TorusFields.TorusSite m) (i : Fin 4) :
    TorusFields.readAtLevel H j W (StepCosts.torusSiteInFrame H j x) i = W x i := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.readAtLevel_torusSiteInFrame <;> assumption
section Blocks
variable {H : BlockFrame} {n : ℕ}
theorem period_depth (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.depth i = n * H.blockSide := by
  simp [BlockFrame.period, hs]
theorem period_top_eq (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.top i = n := by
  simp [BlockFrame.period, hs]
theorem cast_cast_int_of_eq (P m : ℕ) (h : P = m) (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod P)).cast : ℤ) = (a.cast : ℤ) := by
  subst h; simp
theorem siteCoords_torusSiteInFrame {m : ℕ} (j : ℕ) (hm : ∀ i, H.period j i = m)
    (x : TorusFields.TorusSite m) (k : Fin 4) :
    siteCoords (StepCosts.torusSiteInFrame H j x) k = ((x k).cast : ℤ) :=
  cast_cast_int_of_eq _ _ (hm k) (x k)
def torusCellCentre (L : ℕ) (Y : TorusFields.TorusSite n) : TorusFields.TorusSite (n * L) :=
  fun i => (((L : ℤ) * ((Y i).cast : ℤ) : ℤ) : ZMod (n * L))
theorem enclosingCell_torusSiteInFrame (hs : ∀ i, H.extent i = n) (x : TorusFields.TorusSite (n * H.blockSide)) :
    enclosingCell (StepCosts.torusSiteInFrame H H.depth x) =
      StepCosts.torusSiteInFrame H H.top (TorusLumps.parentBlock H.blockSide x) := by
  funext k
  have he : H.top - H.depth = 1 := by simp [BlockFrame.top]
  have h1 := siteCoords_torusSiteInFrame (H := H) H.depth (period_depth hs) x k
  show ((((siteCoords (StepCosts.torusSiteInFrame H H.depth x) k +
      ((H.blockSide : ℤ) ^ (H.top - H.depth) - 1) / 2) /
    (H.blockSide : ℤ) ^ (H.top - H.depth) : ℤ)) : ZMod (H.period H.top k)) = _
  rw [h1, he, pow_one]
  exact (cast_intCast_of_eq _ _ (period_top_eq hs k) _).symm
theorem torusSiteInFrame_injective {m : ℕ} (j : ℕ) (hm : ∀ i, H.period j i = m) :
    Function.Injective (StepCosts.torusSiteInFrame (n := m) H j) := by
  intro x y h
  rw [← toTorusSite_torusSiteInFrame j hm x, h, toTorusSite_torusSiteInFrame j hm y]
theorem isCrossingBond_torusSiteInFrame_iff (hs : ∀ i, H.extent i = n)
    (x : TorusFields.TorusSite (n * H.blockSide)) (i : Fin 4) :
    IsCrossingBond (F := H) (StepCosts.torusSiteInFrame H H.depth x, i) ↔
      TorusLumps.parentBlock H.blockSide (x + TorusFields.unitStep _ i) ≠ TorusLumps.parentBlock H.blockSide x := by
  unfold IsCrossingBond
  show enclosingCell (StepCosts.torusSiteInFrame H H.depth x + unitStep H.depth i) ≠
    enclosingCell (StepCosts.torusSiteInFrame H H.depth x) ↔ _
  rw [← torusSiteInFrame_unitStep H.depth (period_depth hs), ← torusSiteInFrame_add H.depth (period_depth hs),
    enclosingCell_torusSiteInFrame hs, enclosingCell_torusSiteInFrame hs]
  exact not_congr (torusSiteInFrame_injective H.top (period_top_eq hs)).eq_iff
theorem cellCentre_torusSiteInFrame (hs : ∀ i, H.extent i = n) (Y : TorusFields.TorusSite n) :
    cellCentre H.depth (StepCosts.torusSiteInFrame H H.top Y) =
      StepCosts.torusSiteInFrame H H.depth (torusCellCentre H.blockSide Y) := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.cellCentre_torusSiteInFrame <;> assumption
theorem valMinAbs_cast_of_eq (P m : ℕ) (h : P = m) (a : ZMod m) :
    ((((a.cast : ℤ) : ZMod P))).valMinAbs = a.valMinAbs := by
  subst h; simp
def torusCellOffset (L : ℕ) (x : TorusFields.TorusSite (n * L)) (k : Fin 4) : ℤ :=
  ((x - torusCellCentre L (TorusLumps.parentBlock L x)) k).valMinAbs
theorem cellOffset_torusSiteInFrame (hs : ∀ i, H.extent i = n) (x : TorusFields.TorusSite (n * H.blockSide)) :
    cellOffset (StepCosts.torusSiteInFrame H H.depth x) = torusCellOffset H.blockSide x := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.cellOffset_torusSiteInFrame <;> assumption
def IsTorusTreeBond (L : ℕ) (x : TorusFields.TorusSite (n * L)) (i : Fin 4) : Prop :=
  TorusLumps.parentBlock L (x + TorusFields.unitStep _ i) = TorusLumps.parentBlock L x ∧
    ∀ l, i < l → torusCellOffset L x l = 0
theorem isAxialTreeBond_torusSiteInFrame_iff (hs : ∀ i, H.extent i = n)
    (x : TorusFields.TorusSite (n * H.blockSide)) (i : Fin 4) :
    IsAxialTreeBond (F := H) (StepCosts.torusSiteInFrame H H.depth x, i) ↔ IsTorusTreeBond H.blockSide x i := by apply _root_.YangMills.Construction.ColdImage.EvaluationMaps.isAxialTreeBond_iff <;> assumption
end Blocks
section Plain
variable {H : BlockFrame} {n : ℕ}
theorem contourMean_of_empty (hs : ∀ i, H.extent i = n) (hn : 0 < n) (hL : Odd H.blockSide) (J₀ : ℕ)
    (W : H.GaugeField H.depth) (c : H.Cell × Fin 4) :
    contourMean J₀ (∅ : Finset (Finset (H.Site H.depth))) (fun y => cellCentre H.depth y) W c =
      _root_.YangMills.Construction.BlockAverages.contourAverage (j := H.depth) W c := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.contourMean_empty <;> assumption
end Plain
section Hot
variable {n : ℕ}
theorem stepHotLumps_eq_empty (ℓ : TorusLumps.StepParameters) (W : TorusFields.TorusField (n * ℓ.side))
    (hW : TorusFields.IsCold ℓ.threshold W) : StepCosts.stepHotLumps ℓ W = ∅ := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.stepHotLumps_eq_empty <;> assumption
end Hot
section Chart
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
theorem pathHolonomy_const_one {H : BlockFrame} {j : ℕ} (x : H.Site j) (l : List PathStep) :
    pathHolonomy (fun _ _ => (1 : UnitQuaternion) : H.GaugeField j) x l = 1 := by apply _root_.YangMills.SharedProofs.p3325 <;> assumption
omit [NeZero n] in
theorem gaugeAt_trivialField (x : TorusFields.TorusSite (n * R.params.side)) :
    StepSettings.gaugeAt (R := R) (TorusFields.trivialField (n * R.params.side)) x = 1 :=
  pathHolonomy_const_one _ _
abbrev twoLevelFrame (R : StepSettings.StepSetup) (n : ℕ) : BlockFrame :=
  TorusLumps.stepBlockFrame R.params.side n
def torusChartCoords (V : TorusFields.TorusField n)
    (η : StepSettings.FreeCoords (StepSettings.coldChartSetting R V).free)
    (x : TorusFields.TorusSite (n * R.params.side)) (i : Fin 4) : imaginaryQuaternions :=
  open Classical in
  if h : (x, i) ∈ (StepSettings.coldChartSetting R V).free then
    (StepSettings.coldChartSetting R V).frame (x, i) + toImaginary (η ⟨(x, i), h⟩)
  else 0
def frameChartCoords (V : TorusFields.TorusField n)
    (η : StepSettings.FreeCoords (StepSettings.coldChartSetting R V).free) :
    (twoLevelFrame R n).Site (twoLevelFrame R n).depth → Fin 4 → imaginaryQuaternions :=
  fun z i => torusChartCoords V η (TorusLumps.toTorusSite (n * R.params.side) z) i
theorem mem_free_iff (V : TorusFields.TorusField n) (x : TorusFields.TorusSite (n * R.params.side)) (i : Fin 4) :
    (x, i) ∈ (StepSettings.coldChartSetting R V).free ↔ ¬ IsTorusTreeBond R.params.side x i := by
  show (x, i) ∈ StepCosts.chartBonds R.params.side n ↔ _
  unfold StepCosts.chartBonds
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact not_congr (isAxialTreeBond_torusSiteInFrame_iff (H := twoLevelFrame R n) (fun _ => rfl) x i)
theorem readAtLevel_field_eq_chartedField (V : TorusFields.TorusField n)
    (η : StepSettings.FreeCoords (StepSettings.coldChartSetting R V).free) :
    TorusFields.readAtLevel (twoLevelFrame R n) (twoLevelFrame R n).depth
        ((StepSettings.coldChartSetting R V).field η) =
      chartedField (frameChartCoords V η)
        (TorusFields.readAtLevel (twoLevelFrame R n) (twoLevelFrame R n).top V) := by
  have hlow : ∀ i, (twoLevelFrame R n).period (twoLevelFrame R n).depth i = n * R.params.side :=
    period_depth (H := twoLevelFrame R n) (n := n) fun _ => rfl
  funext y i
  obtain ⟨x, rfl⟩ : ∃ x : TorusFields.TorusSite (n * R.params.side),
      StepCosts.torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth x = y :=
    ⟨_, torusSiteInFrame_toTorusSite _ hlow y⟩
  refine (readAtLevel_torusSiteInFrame (H := twoLevelFrame R n) _ hlow
    ((StepSettings.coldChartSetting R V).field η) x i).trans ?_
  have hw : frameChartCoords V η (StepCosts.torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth x) i =
      torusChartCoords V η x i := by
    show torusChartCoords V η (TorusLumps.toTorusSite (n * R.params.side)
      (StepCosts.torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth x)) i = _
    rw [toTorusSite_torusSiteInFrame _ hlow]
  have hcell : TorusFields.readAtLevel (twoLevelFrame R n) (twoLevelFrame R n).top V
      (enclosingCell (StepCosts.torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth x)) i =
      V (TorusLumps.parentBlock R.params.side x) i := by
    have h0 : enclosingCell (StepCosts.torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth x) =
        StepCosts.torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).top
          (TorusLumps.parentBlock R.params.side x) :=
      enclosingCell_torusSiteInFrame (H := twoLevelFrame R n) (n := n) (fun _ => rfl) x
    rw [h0]
    exact readAtLevel_torusSiteInFrame _ (period_top_eq (H := twoLevelFrame R n) (n := n) fun _ => rfl) V _ i
  unfold chartedField
  by_cases hb : (x, i) ∈ (StepSettings.coldChartSetting R V).free
  · have htree : ¬ IsAxialTreeBond (F := twoLevelFrame R n)
        (StepCosts.torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth x, i) := fun h2 =>
      ((mem_free_iff V x i).1 hb)
        ((isAxialTreeBond_torusSiteInFrame_iff (H := twoLevelFrame R n) (fun _ => rfl) x i).1 h2)
    have hval : torusChartCoords V η x i =
        (StepSettings.coldChartSetting R V).frame (x, i) + toImaginary (η ⟨(x, i), hb⟩) := dif_pos hb
    have hfield : (StepSettings.coldChartSetting R V).field η x i =
        StepSettings.chartLink (StepSettings.coldChartSetting R V) x i
          ((StepSettings.coldChartSetting R V).frame (x, i) + toImaginary (η ⟨(x, i), hb⟩)) := dif_pos hb
    rw [hfield, hw, hval]
    unfold StepSettings.chartLink
    have h1 : StepSettings.gaugeAt (R := R) (StepSettings.coldChartSetting R V).fine = fun _ => 1 :=
      funext fun z => gaugeAt_trivialField z
    rw [h1]
    simp only [inv_one, one_mul, mul_one]
    by_cases hc : IsCrossingBond (F := twoLevelFrame R n)
        (StepCosts.torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth x, i)
    · have hc0 : IsCrossingBond (F := twoLevelFrame R n)
          (StepCosts.torusSiteInFrame (twoLevelFrame R n) 0 x, i) := hc
      rw [if_pos hc0, if_pos hc, hcell]
      rfl
    · have hc0 : ¬ IsCrossingBond (F := twoLevelFrame R n)
          (StepCosts.torusSiteInFrame (twoLevelFrame R n) 0 x, i) := hc
      rw [if_neg hc0, if_neg hc, if_neg htree]
  · have hfield : (StepSettings.coldChartSetting R V).field η x i =
        (StepSettings.coldChartSetting R V).fine x i := dif_neg hb
    have htr : IsTorusTreeBond R.params.side x i := by
      by_contra h
      exact hb ((mem_free_iff V x i).2 h)
    have htree := (isAxialTreeBond_torusSiteInFrame_iff (H := twoLevelFrame R n) (fun _ => rfl) x i).2 htr
    have hnc : ¬ IsCrossingBond (F := twoLevelFrame R n)
        (StepCosts.torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).depth x, i) := htree.1
    rw [hfield, if_neg hnc]
    exact Eq.trans rfl (if_pos htree).symm
end Chart
end TorusTransfer
namespace TorusTransfer
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
theorem meanNorm_eq_norm_contourAverage (ℓ : TorusLumps.StepParameters) (hodd : Odd ℓ.side)
    (W : TorusFields.TorusField (n * ℓ.side)) (hW : TorusFields.IsCold ℓ.threshold W)
    (c : TorusFields.TorusBond n) :
    StepCosts.meanNorm ℓ W (fun y => cellCentre 0 y) c =
      ‖_root_.YangMills.Construction.BlockAverages.contourAverage (j := (TorusLumps.stepBlockFrame ℓ.side n).depth)
        (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0 W)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 c.1, c.2)‖ := by
  unfold StepCosts.meanNorm
  rw [stepHotLumps_eq_empty ℓ W hW]
  have h := contourMean_of_empty (H := TorusLumps.stepBlockFrame ℓ.side n) (n := n) (fun _ => rfl)
    (Nat.pos_of_ne_zero (NeZero.ne n)) hodd ℓ.baseDepth
    (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0 W)
    (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 c.1, c.2)
  exact congrArg norm h
theorem norm_le_of_isMinimizingChart {F : BlockFrame} {a ρ : ℝ} {S : Finset F.Cell}
    {V : F.GaugeField F.top} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (h : IsMinimizingChart a S V ρ w) (hρ : 0 ≤ ρ) (x : F.Site F.depth) (i : Fin 4) : ‖w x i‖ ≤ ρ := by
  by_cases hb : (x, i) ∈ chordBonds S
  · exact h.2.1 _ hb
  · have := h.1 (x, i) hb
    simp only at this
    rw [this]
    simpa using hρ
theorem rangesAdmissible_clusterRange (T : RenormalizationStepParameters.ParameterAssignment) (hT : T.Admissible) (y x : ℝ)
    (hy : T.floorMin ≤ y) (hx : y ≤ x) :
    StepMarks.RangesAdmissible (TorusLumps.clusterRange x) (TorusLumps.clusterRange x) := by
  have hf := hT.fits y hy
  have h1 : (1 : ℝ) ≤ y := hf.y₁_ge
  have h2 : TorusLumps.clusterRange y ≤ TorusLumps.clusterRange x :=
    Nat.ceil_mono (Real.rpow_le_rpow (by linarith) hx (by norm_num))
  have h3 : 2 ^ 16 ≤ TorusLumps.clusterRange y := hf.range_ge
  have h4 : 2 ^ 16 ≤ TorusLumps.clusterRange x := h3.trans h2
  refine ⟨Nat.le_succ _, h4, ?_⟩
  omega
end TorusTransfer
open BlockAverages TorusTransfer in
theorem contourMeanAtColdField_holds (hcold : StepSettings.ColdChartSettingIsCold)
    (hframe : StepFrames.FrameNearMinimizer)
    (hcov : ColdStepAtMirrorFrames.BlocksCoverLowerLevel) : ContourMeanAtColdField := by
  intro T hT
  obtain ⟨y₁, hy₁⟩ := hcold T hT
  refine ⟨max y₁ T.floorMin, fun y hy R hR n _ hn V hV η hη c => ?_⟩
  have hy1 : y₁ ≤ y := le_trans (le_max_left _ _) hy
  have hy0 : T.floorMin ≤ y := le_trans (le_max_right _ _) hy
  have hcoldR := hy₁ y hy1 R hR n hn V hV η hη
  have hσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hLe : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hx : y ≤ R.coupling := hR.le_coupling
  have hσ0 : 0 < R.params.threshold := by rw [hσ]; exact hT.σ_pos
  have hodd : Odd R.params.side := by rw [hLe]; exact hT.L_odd
  have hn₀ : R.params.n₀ ≤ n := by
    have : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
    omega
  have h4096 : 4096 ≤ T.n₀ := hT.n₀_ge
  have hn2 : 2 ≤ n := by omega
  have hcoldW : TorusFields.IsCold R.params.threshold ((StepSettings.coldChartSetting R V).field η) := by
    intro x' μ ν hμ
    have h1 := hcoldR x' μ ν hμ
    rw [hσ]
    linarith
  have hfit : StepMarks.RangesAdmissible R.range R.range :=
    rangesAdmissible_clusterRange T hT y R.coupling hy0 hx
  have hN : 0 < T.N 0 := hT.chain.2.2.2.2.2.2.2.1 0
  have hsit : StepMarks.IsStepSituation R.params R.range V Finset.univ ∅ (9 / 8 * R.params.threshold) :=
    Or.inr ⟨hn₀, by rw [hσ]; exact hV, rfl, rfl, rfl⟩
  have hfits : R.params.Admissible := by rw [hR.params_eq]; exact hT.fits y hy0
  have hchain : ColdChain.ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius
      T.σA T.cg T.N := by
    rw [hR.params_eq, hR.anchorRadius_eq]
    exact hT.chain
  have h2σ : 2 * R.params.threshold ≤ T.σA := by rw [hσ]; exact hT.σ_le
  have hfr := (hframe R.params T.δ₁ T.lam R.anchorRadius T.σA T.cg T.N hfits hchain h2σ).2 R.depth R.range
    R.range n V Finset.univ ∅ (9 / 8 * R.params.threshold) hfit hsit
  have hρ : 0 < R.anchorRadius := by rw [hR.anchorRadius_eq]; exact hT.chain.2.2.2.1
  have hnum : 0 ≤ min R.anchorRadius (T.N 0 * (9 / 8 * R.params.threshold)) := le_min hρ.le (by positivity)
  have hframe_norm : ∀ b ∈ StepCosts.chartBonds R.params.side n,
      ‖(StepSettings.coldChartSetting R V).frame b‖ ≤ T.N 0 * (9 / 8 * R.params.threshold) := by
    intro b hb
    have hform := (hfr b hb (Finset.notMem_empty _)).1
    by_cases hsm : 4 * (R.range / 2 ^ 11) + 5 < n
    · obtain ⟨w, hw, he⟩ := hform.1 hsm
      have h3 := norm_le_of_isMinimizingChart hw hnum
        (reflectedBond (F := TorusFields.torusFrame R.params.side R.depth n) (R.range / 2 ^ 11)
          (StepCosts.torusSiteInFrame (TorusFields.torusFrame R.params.side R.depth n)
            (TorusFields.torusFrame R.params.side R.depth n).depth b.1, b.2)).1 b.2
      exact (le_of_eq (congrArg norm he)).trans (h3.trans (min_le_right _ _))
    · obtain ⟨w, hw, he⟩ := hform.2 hsm
      have h3 := norm_le_of_isMinimizingChart hw hnum
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame R.params.side R.depth n)
          (TorusFields.torusFrame R.params.side R.depth n).depth b.1) b.2
      exact (le_of_eq (congrArg norm he)).trans (h3.trans (min_le_right _ _))
  have hB0 : 0 ≤ T.N 0 * (9 / 8 * R.params.threshold) + R.params.threshold / 64 := by positivity
  have hwB : ∀ (z : (twoLevelFrame R n).Site (twoLevelFrame R n).depth) (i : Fin 4),
      ‖(frameChartCoords V η z i : ℍ[ℝ])‖ ≤ T.N 0 * (9 / 8 * R.params.threshold) + R.params.threshold / 64 := by
    intro z i
    show ‖(torusChartCoords V η (TorusLumps.toTorusSite (n * R.params.side) z) i : ℍ[ℝ])‖ ≤ _
    unfold torusChartCoords
    split_ifs with hb
    · have h3 : ‖(((StepSettings.coldChartSetting R V).frame (TorusLumps.toTorusSite (n * R.params.side) z, i) +
          toImaginary (η ⟨(TorusLumps.toTorusSite (n * R.params.side) z, i), hb⟩) : imaginaryQuaternions) :
            ℍ[ℝ])‖ ≤
          ‖(StepSettings.coldChartSetting R V).frame (TorusLumps.toTorusSite (n * R.params.side) z, i)‖ +
            ‖toImaginary (η ⟨(TorusLumps.toTorusSite (n * R.params.side) z, i), hb⟩)‖ := norm_add_le _ _
      have h4 := hframe_norm _ hb
      have h5 : ‖toImaginary (η ⟨(TorusLumps.toTorusSite (n * R.params.side) z, i), hb⟩)‖ ≤
          R.params.threshold / 64 := hη _
      linarith
    · simpa using hB0
  have hmean := ContourApprox.norm_contourAverage_sub_le (F := twoLevelFrame R n) hodd (fun _ => hn2)
    (TorusFields.readAtLevel (twoLevelFrame R n) (twoLevelFrame R n).top V) (frameChartCoords V η) _ hwB
    (StepCosts.torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).top c.1, c.2)
  rw [← readAtLevel_field_eq_chartedField] at hmean
  have hsize := meanNorm_eq_norm_contourAverage R.params hodd _ hcoldW c
  have hsmall : 5 * ((twoLevelFrame R n).blockSide : ℝ) *
      (T.N 0 * (9 / 8 * R.params.threshold) + R.params.threshold / 64) ≤ 1 / 2 := by
    have hσL := hT.σ_L
    have e0 : ((twoLevelFrame R n).blockSide : ℝ) = T.side := by
      show ((R.params.side : ℕ) : ℝ) = _
      rw [hLe]
    rw [e0, hσ]
    have hLpos : (0 : ℝ) ≤ T.side := by positivity
    have hσ1 : 0 < T.threshold := hT.σ_pos
    have e : 5 * (T.side : ℝ) * (T.N 0 * (9 / 8 * T.threshold) + T.threshold / 64) ≤
        (2 ^ 10 * (T.side : ℝ) * (T.N 0 + 1) * T.threshold) * (1 / 2) := by
      nlinarith [mul_nonneg (mul_nonneg hLpos hN.le) hσ1.le, mul_nonneg hLpos hσ1.le]
    nlinarith
  have hunit : ‖((TorusFields.readAtLevel (twoLevelFrame R n) (twoLevelFrame R n).top V
      (StepCosts.torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).top c.1) c.2 : UnitQuaternion) :
        ℍ[ℝ])‖ = 1 :=
    TorusFields.norm_unitQuaternion _
  have htri := norm_sub_norm_le
    ((TorusFields.readAtLevel (twoLevelFrame R n) (twoLevelFrame R n).top V
      (StepCosts.torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).top c.1) c.2 : UnitQuaternion) : ℍ[ℝ])
    (_root_.YangMills.Construction.BlockAverages.contourAverage (j := (twoLevelFrame R n).depth)
      (TorusFields.readAtLevel (twoLevelFrame R n) (twoLevelFrame R n).depth
        ((StepSettings.coldChartSetting R V).field η))
      (StepCosts.torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).top c.1, c.2))
  rw [norm_sub_rev, hunit] at htri
  have hfinal : 1 / 2 ≤ ‖_root_.YangMills.Construction.BlockAverages.contourAverage (j := (twoLevelFrame R n).depth)
      (TorusFields.readAtLevel (twoLevelFrame R n) (twoLevelFrame R n).depth
        ((StepSettings.coldChartSetting R V).field η))
      (StepCosts.torusSiteInFrame (twoLevelFrame R n) (twoLevelFrame R n).top c.1, c.2)‖ := by linarith
  exact hfinal.trans_eq hsize.symm
end ClusterExpansionOfAStep
end YangMills.Construction
end
