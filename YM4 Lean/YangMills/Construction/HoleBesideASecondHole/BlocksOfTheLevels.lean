import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.SitesOfAPatch
import YangMills.Construction.HoleBesideASecondHole.CutActionIsTheLeastActionProof
import YangMills.Construction.PeriodicLattice.WilsonMeasureIsometryInvarianceProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace LumpContours
open YangMills.Construction.BlockAverages
namespace BlockLevels
variable {F : BlockFrame}
theorem unitQuaternion_coe_mul (g g' : UnitQuaternion) :
    ((g * g' : UnitQuaternion) : ℍ[ℝ]) = (g : ℍ[ℝ]) * (g' : ℍ[ℝ]) := rfl
theorem unitQuaternion_norm (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem unitQuaternion_inv_mul (g : UnitQuaternion) :
    ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := (Unitary.mem_iff.1 g.2).1
theorem unitQuaternion_mul_inv (g : UnitQuaternion) :
    (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := (Unitary.mem_iff.1 g.2).2
theorem norm_unitQuaternion_mul (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖(g : ℍ[ℝ]) * q‖ = ‖q‖ := by
  rw [norm_mul, unitQuaternion_norm, one_mul]
theorem norm_mul_unitQuaternion (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖q * (g : ℍ[ℝ])‖ = ‖q‖ := by
  rw [norm_mul, unitQuaternion_norm, mul_one]
theorem norm_sub_inv_inv (g g' : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(g : ℍ[ℝ]) - g'‖ := by
  rw [← norm_unitQuaternion_mul g, ← norm_mul_unitQuaternion g', mul_sub, sub_mul,
    unitQuaternion_mul_inv, one_mul, mul_assoc, unitQuaternion_inv_mul, mul_one, norm_sub_rev]
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem pathDisplacement_append (j : ℕ) (l l' : List PathStep) :
    pathDisplacement (F := F) j (l ++ l') = pathDisplacement j l + pathDisplacement j l' := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_append <;> assumption
theorem pathDisplacement_reversePath (j : ℕ) (l : List PathStep) :
    pathDisplacement (F := F) j (reversePath l) = - pathDisplacement j l := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_reversePath <;> assumption
theorem period_succ (j : ℕ) (hj : j < F.top) (i : Fin 4) :
    F.period j i = F.blockSide * F.period (j + 1) i := by
  simp only [BlockFrame.period]
  have : F.top - j = (F.top - (j + 1)) + 1 := by omega
  rw [this, pow_succ]
  ring
theorem siteCoords_cast {j : ℕ} (x : F.Site j) (i : Fin 4) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by
  simp [siteCoords]
theorem refineSite_add (j : ℕ) (hj : j < F.top) (y y' : F.Site (j + 1)) :
    refineSite (y + y') = refineSite y + refineSite y' := by
  funext k
  simp only [refineSite, siteOfCoords, Pi.add_apply]
  have h1 : ((siteCoords (y + y') k : ℤ) : ZMod (F.period (j + 1) k)) =
      ((siteCoords y k + siteCoords y' k : ℤ) : ZMod (F.period (j + 1) k)) := by
    rw [siteCoords_cast, Int.cast_add, siteCoords_cast, siteCoords_cast]
    rfl
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  have h2 : ((F.blockSide * siteCoords (y + y') k : ℤ) : ZMod (F.period j k)) =
      ((F.blockSide * (siteCoords y k + siteCoords y' k) : ℤ) : ZMod (F.period j k)) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub, period_succ j hj k]
    push_cast
    rw [← mul_sub]
    exact mul_dvd_mul_left _ h1
  rw [h2]
  push_cast
  rw [mul_add]
theorem refineSite_unitStep (j : ℕ) (hj : j < F.top) (i : Fin 4) :
    refineSite (unitStep (j + 1) i : F.Site (j + 1)) = F.blockSide • unitStep j i := by
  funext k
  simp only [refineSite, siteOfCoords, Pi.smul_apply, unitStep]
  set e : ℤ := (Pi.single i 1 : Fin 4 → ℤ) k with he
  have h1 : ((siteCoords (siteOfCoords (F := F) (j + 1) (Pi.single i 1)) k : ℤ) :
      ZMod (F.period (j + 1) k)) = ((e : ℤ) : ZMod (F.period (j + 1) k)) := by
    rw [siteCoords_cast]
    simp [siteOfCoords, he]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  have h2 : ((F.blockSide * siteCoords (siteOfCoords (F := F) (j + 1) (Pi.single i 1)) k : ℤ) :
      ZMod (F.period j k)) = ((F.blockSide * e : ℤ) : ZMod (F.period j k)) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub, period_succ j hj k]
    push_cast
    rw [← mul_sub]
    exact mul_dvd_mul_left _ h1
  rw [h2]
  push_cast
  simp [siteOfCoords, nsmul_eq_mul]
theorem refineSite_add_step (j : ℕ) (hj : j < F.top) (y : F.Site (j + 1)) (st : PathStep) :
    refineSite (y + stepDisplacement (j + 1) st) = refineSite y + F.blockSide • stepDisplacement j st := by
  obtain ⟨i, b⟩ := st
  cases b
  · have e : y = (y + - unitStep (j + 1) i) + unitStep (j + 1) i := by abel
    have h1 := refineSite_add j hj (y + - unitStep (j + 1) i) (unitStep (j + 1) i)
    rw [← e, refineSite_unitStep j hj] at h1
    simp only [stepDisplacement, Bool.false_eq_true, if_false]
    rw [smul_neg, h1]
    abel
  · simp only [stepDisplacement, if_true]
    rw [refineSite_add j hj, refineSite_unitStep j hj]
theorem pathDisplacement_replicate (j n : ℕ) (st : PathStep) :
    pathDisplacement (F := F) j (List.replicate n st) = n • stepDisplacement j st := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_replicate <;> assumption
theorem siteOfCoords_eq_sum (j : ℕ) (h : Fin 4 → ℤ) :
    siteOfCoords (F := F) j h = ∑ i, h i • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_eq_sum <;> assumption
theorem pathDisplacement_straightFlow (j : ℕ) (c : ℤ) (i : Fin 4) :
    pathDisplacement (F := F) j (List.replicate c.natAbs (i, decide (0 ≤ c))) = c • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_replicate_axis <;> assumption
theorem pathDisplacement_axisPath (j : ℕ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    pathDisplacement (F := F) j (axisPath h π) = siteOfCoords j h := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_axisPath <;> assumption
def WithinBlock (L : ℕ) (o : Fin 4 → ℤ) : Prop := ∀ m, |o m| ≤ ((L : ℤ) - 1) / 2
theorem siteOfCoords_add (j : ℕ) (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j (a + b) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem siteOfCoords_single (j : ℕ) (c : ℤ) (i : Fin 4) :
    siteOfCoords (F := F) j (c • Pi.single i 1) = c • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_single <;> assumption
theorem siteOfCoords_zero (j : ℕ) : siteOfCoords (F := F) j 0 = 0 := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_zero <;> assumption
theorem mem_centredCube_of_withinBlock {L : ℕ} {o : Fin 4 → ℤ} (ho : WithinBlock L o) :
    o ∈ centredCube L := by
  simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc]
  intro m
  exact abs_le.1 (ho m)
theorem withinBlock_of_mem_centredCube {L : ℕ} {o : Fin 4 → ℤ} (ho : o ∈ centredCube L) :
    WithinBlock L o := by
  simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc] at ho
  intro m
  exact abs_le.2 (ho m)
theorem refineSite_add_mem_sitesBelow (j : ℕ) (y : F.Site (j + 1)) {o : Fin 4 → ℤ}
    (ho : WithinBlock F.blockSide o) :
    refineSite y + siteOfCoords j o ∈ sitesBelow j y := by
  have e : j + 1 - j = 1 := by omega
  simp only [sitesBelow, e, pow_one]
  refine Finset.mem_image.2 ⟨o, mem_centredCube_of_withinBlock ho, ?_⟩
  funext k
  simp [refineSite, siteOfCoords]
theorem add_smul_single_apply (o : Fin 4 → ℤ) (c : ℤ) (i m : Fin 4) :
    (o + c • (Pi.single i 1 : Fin 4 → ℤ)) m = o m + if m = i then c else 0 := by apply _root_.YangMills.Construction.GaugeFixing.add_smul_single_apply <;> assumption
theorem mem_adjacent_blocks (j : ℕ) (hj : j < F.top) (hL : Odd F.blockSide) (y : F.Site (j + 1))
    (i : Fin 4) {o : Fin 4 → ℤ} (ho : WithinBlock F.blockSide o) (r : ℕ) (hr : r ≤ F.blockSide) :
    refineSite y + siteOfCoords j o + r • unitStep j i ∈
      sitesBelow j y ∪ sitesBelow j (y + unitStep (j + 1) i) := by
  obtain ⟨k, hk⟩ := hL
  have hhalf : ((F.blockSide : ℤ) - 1) / 2 = k := by
    rw [hk]
    push_cast
    omega
  have hoi := abs_le.1 (ho i)
  rw [hhalf] at hoi
  by_cases hc : o i + r ≤ k
  · refine Finset.mem_union_left _ ?_
    have e : refineSite y + siteOfCoords j o + r • unitStep j i =
        refineSite y + siteOfCoords j (o + (r : ℤ) • Pi.single i 1) := by
      rw [siteOfCoords_add, siteOfCoords_single, natCast_zsmul, add_assoc]
    rw [e]
    refine refineSite_add_mem_sitesBelow j y ?_
    intro m
    rw [add_smul_single_apply, hhalf]
    have hm := abs_le.1 (ho m)
    rw [hhalf] at hm
    by_cases h : m = i
    · subst h
      simp only [if_true]
      rw [abs_le]
      omega
    · simp only [h, if_false, add_zero]
      rw [abs_le]
      omega
  · refine Finset.mem_union_right _ ?_
    have e : refineSite y + siteOfCoords j o + r • unitStep j i =
        refineSite (y + unitStep (j + 1) i) +
          siteOfCoords j (o + ((r : ℤ) - F.blockSide) • Pi.single i 1) := by
      have h1 := refineSite_add_step j hj y (i, true)
      simp only [stepDisplacement, if_true] at h1
      rw [h1, siteOfCoords_add, siteOfCoords_single, sub_smul, natCast_zsmul, natCast_zsmul]
      abel
    rw [e]
    refine refineSite_add_mem_sitesBelow _ _ ?_
    intro m
    rw [add_smul_single_apply, hhalf]
    have hm := abs_le.1 (ho m)
    rw [hhalf] at hm
    have hLk : (F.blockSide : ℤ) = 2 * k + 1 := by
      rw [hk]
      push_cast
      ring
    by_cases h : m = i
    · subst h
      simp only [if_true]
      rw [abs_le]
      omega
    · simp only [h, if_false, add_zero]
      rw [abs_le]
      omega
def axisPathOffset (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : ℕ) : Fin 4 → ℤ :=
  fun m => if ((π.symm m : Fin 4) : ℕ) < k then h m else 0
theorem axisPathOffset_zero (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) : axisPathOffset h π 0 = 0 := by apply _root_.YangMills.Construction.GaugeFixing.partialOffset_zero <;> assumption
theorem axisPathOffset_succ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : Fin 4) :
    axisPathOffset h π ((k : ℕ) + 1) = axisPathOffset h π k + h (π k) • Pi.single (π k) 1 := by apply _root_.YangMills.Construction.GaugeFixing.partialOffset_succ <;> assumption
theorem axisPathOffset_flow_withinBlock (L : ℕ) (h : Fin 4 → ℤ) (hh : WithinBlock L h)
    (π : Equiv.Perm (Fin 4)) (k : Fin 4) (r : ℕ) (hr : r ≤ (h (π k)).natAbs) :
    WithinBlock L (axisPathOffset h π k +
      (if decide (0 ≤ h (π k)) then (r : ℤ) else -(r : ℤ)) • Pi.single (π k) 1) := by
  intro m
  rw [add_smul_single_apply]
  by_cases e : m = π k
  · subst e
    have e0 : axisPathOffset h π k (π k) = 0 := by simp [axisPathOffset]
    rw [e0, zero_add]
    simp only [if_true]
    have := hh (π k)
    have h3 : |(if decide (0 ≤ h (π k)) then (r : ℤ) else -(r : ℤ))| = r := by
      split_ifs <;> simp
    rw [h3]
    refine le_trans ?_ this
    have : (r : ℤ) ≤ ((h (π k)).natAbs : ℤ) := by exact_mod_cast hr
    rwa [Int.natCast_natAbs] at this
  · simp only [e, if_false, add_zero, axisPathOffset]
    split_ifs
    · exact hh m
    · have := hh (π 0)
      exact le_trans (by simp) this
theorem axisPath_eq_flows (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    axisPath h π =
      List.replicate (h (π 0)).natAbs (π 0, decide (0 ≤ h (π 0))) ++
      (List.replicate (h (π 1)).natAbs (π 1, decide (0 ≤ h (π 1))) ++
      (List.replicate (h (π 2)).natAbs (π 2, decide (0 ≤ h (π 2))) ++
      (List.replicate (h (π 3)).natAbs (π 3, decide (0 ≤ h (π 3))) ++ []))) := by apply _root_.YangMills.Construction.GaugeFixing.axisPath_eq_append <;> assumption
def axisPathFlow (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : Fin 4) : List PathStep :=
  List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))
theorem add_axisPathFlow (j : ℕ) (x : F.Site j) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : Fin 4) :
    x + siteOfCoords j (axisPathOffset h π k) + pathDisplacement j (axisPathFlow h π k) =
      x + siteOfCoords j (axisPathOffset h π ((k : ℕ) + 1)) := by
  rw [axisPathOffset_succ, siteOfCoords_add, siteOfCoords_single, axisPathFlow,
    pathDisplacement_straightFlow, add_assoc]
def PathWithin {j : ℕ} (Z : Finset (F.Site j)) : F.Site j → List PathStep → Prop
  | _, [] => True
  | x, st :: r => x ∈ Z ∧ x + stepDisplacement j st ∈ Z ∧ PathWithin Z (x + stepDisplacement j st) r
theorem PathWithin.append {j : ℕ} (Z : Finset (F.Site j)) (l l' : List PathStep) :
    ∀ x, PathWithin Z x l → PathWithin Z (x + pathDisplacement j l) l' → PathWithin Z x (l ++ l') := by
  induction l with
  | nil =>
    intro x _ h
    simpa [pathDisplacement] using h
  | cons st r ih =>
    intro x h h'
    refine ⟨h.1, h.2.1, ih _ h.2.2 ?_⟩
    have e : x + stepDisplacement j st + pathDisplacement j r = x + pathDisplacement j (st :: r) := by
      simp [pathDisplacement, add_assoc]
    rw [e]
    exact h'
theorem PathWithin.replicate {j : ℕ} (Z : Finset (F.Site j)) (st : PathStep) (n : ℕ) :
    ∀ x, (∀ r ≤ n, x + r • stepDisplacement j st ∈ Z) → PathWithin Z x (List.replicate n st) := by
  induction n with
  | zero => intro x _; trivial
  | succ n ih =>
    intro x h
    refine ⟨by simpa using h 0 (Nat.zero_le _), by simpa using h 1 (by omega), ih _ fun r hr => ?_⟩
    have := h (r + 1) (by omega)
    rw [add_smul, one_smul, add_comm (r • _), ← add_assoc] at this
    exact this
theorem PathWithin.reversePath {j : ℕ} (Z : Finset (F.Site j)) (l : List PathStep) :
    ∀ x, PathWithin Z x l → PathWithin Z (x + pathDisplacement j l) (BlockAverages.reversePath l) := by
  induction l with
  | nil => intro x _; trivial
  | cons st r ih =>
    intro x h
    have e : BlockAverages.reversePath (st :: r) = BlockAverages.reversePath r ++ [(st.1, !st.2)] := by
      simp [BlockAverages.reversePath]
    have e2 : x + pathDisplacement j (st :: r) = x + stepDisplacement j st + pathDisplacement j r := by
      simp [pathDisplacement, add_assoc]
    rw [e, e2]
    refine PathWithin.append Z _ _ _ (ih _ h.2.2) ?_
    rw [pathDisplacement_reversePath, add_neg_cancel_right]
    refine ⟨h.2.1, ?_, trivial⟩
    have e3 : x + stepDisplacement j st + stepDisplacement j (st.1, !st.2) = x := by
      obtain ⟨d, b⟩ := st
      cases b <;> simp [stepDisplacement]
    rw [e3]
    exact h.1
theorem axisPath_within_block (j : ℕ) (hL : Odd F.blockSide) (y : F.Site (j + 1)) (h : Fin 4 → ℤ)
    (hh : WithinBlock F.blockSide h) (π : Equiv.Perm (Fin 4)) :
    PathWithin (sitesBelow j y) (refineSite y) (axisPath h π) := by
  have piece : ∀ k : Fin 4, PathWithin (sitesBelow j y)
      (refineSite y + siteOfCoords j (axisPathOffset h π k)) (axisPathFlow h π k) := by
    intro k
    refine PathWithin.replicate _ _ _ _ fun r hr => ?_
    have h1 := axisPathOffset_flow_withinBlock F.blockSide h hh π k r hr
    have e : refineSite y + siteOfCoords j (axisPathOffset h π k) +
        r • stepDisplacement j (π k, decide (0 ≤ h (π k))) =
        refineSite y + siteOfCoords j (axisPathOffset h π k +
          (if decide (0 ≤ h (π k)) then (r : ℤ) else -(r : ℤ)) • Pi.single (π k) 1) := by
      rw [siteOfCoords_add, siteOfCoords_single, add_assoc]
      by_cases hc : 0 ≤ h (π k)
      · simp [stepDisplacement, hc]
      · simp [stepDisplacement, hc]
    rw [e]
    exact refineSite_add_mem_sitesBelow j y h1
  rw [axisPath_eq_flows]
  have s0 := add_axisPathFlow j (refineSite y) h π 0
  have s1 := add_axisPathFlow j (refineSite y) h π 1
  have s2 := add_axisPathFlow j (refineSite y) h π 2
  have z0 : refineSite y + siteOfCoords j (axisPathOffset h π ((0 : Fin 4) : ℕ)) = refineSite y := by
    simp [axisPathOffset_zero, siteOfCoords_zero]
  have p0 := piece 0
  have p1 := piece 1
  have p2 := piece 2
  have p3 := piece 3
  rw [z0] at p0 s0
  refine PathWithin.append _ _ _ _ p0 ?_
  have e01 : refineSite y + pathDisplacement j (axisPathFlow h π 0) =
      refineSite y + siteOfCoords j (axisPathOffset h π ((1 : Fin 4) : ℕ)) := s0
  simp only [axisPathFlow] at e01
  rw [e01]
  refine PathWithin.append _ _ _ _ p1 ?_
  have e12 : refineSite y + siteOfCoords j (axisPathOffset h π ((1 : Fin 4) : ℕ)) +
      pathDisplacement j (axisPathFlow h π 1) =
      refineSite y + siteOfCoords j (axisPathOffset h π ((2 : Fin 4) : ℕ)) := s1
  simp only [axisPathFlow] at e12
  rw [e12]
  refine PathWithin.append _ _ _ _ p2 ?_
  have e23 : refineSite y + siteOfCoords j (axisPathOffset h π ((2 : Fin 4) : ℕ)) +
      pathDisplacement j (axisPathFlow h π 2) =
      refineSite y + siteOfCoords j (axisPathOffset h π ((3 : Fin 4) : ℕ)) := s2
  simp only [axisPathFlow] at e23
  rw [e23]
  refine PathWithin.append _ _ _ _ p3 ?_
  trivial
theorem PathWithin.mono {j : ℕ} {Z Z' : Finset (F.Site j)} (hz : Z ⊆ Z') (l : List PathStep) :
    ∀ x, PathWithin Z x l → PathWithin Z' x l := by
  induction l with
  | nil => intro x _; trivial
  | cons st r ih => intro x h; exact ⟨hz h.1, hz h.2.1, ih _ h.2.2⟩
theorem bondContour_within_blocks (j : ℕ) (hj : j < F.top) (hL : Odd F.blockSide)
    (c : F.Site (j + 1) × Fin 4) (h : Fin 4 → ℤ) (hh : WithinBlock F.blockSide h) (π : Equiv.Perm (Fin 4)) :
    PathWithin (sitesBelow j c.1 ∪ sitesBelow j (c.1 + unitStep (j + 1) c.2)) (refineSite c.1)
      (bondContour F.blockSide h π c.2) := by
  unfold bondContour
  set Z := sitesBelow j c.1 ∪ sitesBelow j (c.1 + unitStep (j + 1) c.2) with hZ
  have l1 := axisPath_within_block j hL c.1 h hh π
  have l2 := axisPath_within_block j hL (c.1 + unitStep (j + 1) c.2) h hh π
  refine PathWithin.append _ _ _ _
    (PathWithin.append _ _ _ _ (PathWithin.mono Finset.subset_union_left _ _ l1) ?_) ?_
  · rw [pathDisplacement_axisPath]
    refine PathWithin.replicate _ _ _ _ fun r hr => ?_
    have := mem_adjacent_blocks j hj hL c.1 c.2 hh r hr
    have e : stepDisplacement j (c.2, true) = (unitStep j c.2 : F.Site j) := by simp [stepDisplacement]
    rw [e]
    exact this
  · have r2 := PathWithin.reversePath _ _ _ (PathWithin.mono (Z' := Z) Finset.subset_union_right _ _ l2)
    rw [pathDisplacement_append, pathDisplacement_axisPath, pathDisplacement_replicate]
    have e : refineSite c.1 + (siteOfCoords j h + F.blockSide • stepDisplacement j (c.2, true)) =
        refineSite (c.1 + unitStep (j + 1) c.2) + pathDisplacement j (axisPath h π) := by
      have := refineSite_add_step j hj c.1 (c.2, true)
      simp only [stepDisplacement, if_true] at this ⊢
      rw [this, pathDisplacement_axisPath]
      abel
    rw [e]
    exact r2
theorem period_eq_pow_mul {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (k : Fin 4) :
    F.period i k = F.blockSide ^ (j - i) * F.period j k := by
  simp only [BlockFrame.period]
  have : F.top - i = (F.top - j) + (j - i) := by omega
  rw [this, pow_add]
  ring
theorem pow_mul_cast_eq {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (k : Fin 4) {a b : ℤ}
    (h : (a : ZMod (F.period j k)) = b) :
    (((F.blockSide : ℤ) ^ (j - i) * a : ℤ) : ZMod (F.period i k)) =
      (((F.blockSide : ℤ) ^ (j - i) * b : ℤ) : ZMod (F.period i k)) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h ⊢
  rw [period_eq_pow_mul hij hj k]
  push_cast
  rw [← mul_sub]
  exact mul_dvd_mul_left _ h
theorem siteOfCoords_siteCoords {j : ℕ} (x : F.Site j) : siteOfCoords j (siteCoords x) = x := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
theorem mem_centredCube_iff {M : ℕ} {o : Fin 4 → ℤ} :
    o ∈ centredCube M ↔ ∀ m, |o m| ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.GaugeFixing.mem_centredCube_iff_abs_le <;> assumption
theorem odd_blockSide_pow (hL : Odd F.blockSide) (e : ℕ) : Odd (F.blockSide ^ e) := hL.pow
theorem abs_mul_add_le_half {A B : ℕ} (hA : Odd A) (hB : Odd B) {h h' : ℤ} (h1 : |h| ≤ ((B : ℤ) - 1) / 2)
    (h2 : |h'| ≤ ((A : ℤ) - 1) / 2) : |(A : ℤ) * h + h'| ≤ (((A * B : ℕ) : ℤ) - 1) / 2 := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  have e1 : (((2 * b + 1 : ℕ) : ℤ) - 1) / 2 = b := by
    push_cast
    omega
  have e2 : (((2 * a + 1 : ℕ) : ℤ) - 1) / 2 = a := by
    push_cast
    omega
  have e3 : ((((2 * a + 1) * (2 * b + 1) : ℕ) : ℤ) - 1) / 2 = 2 * a * b + a + b := by
    push_cast
    have : (2 * (a : ℤ) + 1) * (2 * b + 1) - 1 = 2 * (2 * a * b + a + b) := by ring
    rw [this]
    omega
  rw [e1] at h1
  rw [e2] at h2
  rw [e3]
  have h1' := abs_le.1 h1
  have h2' := abs_le.1 h2
  rw [abs_le]
  push_cast
  constructor <;> nlinarith
theorem sitesBelow_trans {i j m : ℕ} (hij : i ≤ j) (hjm : j ≤ m) (hm : m ≤ F.top) (hL : Odd F.blockSide)
    (x : F.Site m) {w : F.Site j} (hw : w ∈ sitesBelow j x) {z : F.Site i} (hz : z ∈ sitesBelow i w) :
    z ∈ sitesBelow i x := by
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hw
  obtain ⟨h', hh', rfl⟩ := Finset.mem_image.1 hz
  have hh1 := mem_centredCube_iff.1 hh
  have hh2 := mem_centredCube_iff.1 hh'
  refine Finset.mem_image.2 ⟨fun k => (F.blockSide : ℤ) ^ (j - i) * h k + h' k, ?_, ?_⟩
  · refine mem_centredCube_iff.2 fun k => ?_
    have e : m - i = (j - i) + (m - j) := by omega
    rw [e, pow_add]
    have := abs_mul_add_le_half (odd_blockSide_pow hL (j - i)) (odd_blockSide_pow hL (m - j))
      (hh1 k) (hh2 k)
    simpa using this
  · funext k
    simp only [siteOfCoords]
    have h1 : ((siteCoords (siteOfCoords (F := F) j fun k =>
        (F.blockSide : ℤ) ^ (m - j) * siteCoords x k + h k) k : ℤ) : ZMod (F.period j k)) =
        (((F.blockSide : ℤ) ^ (m - j) * siteCoords x k + h k : ℤ) : ZMod (F.period j k)) := by
      rw [siteCoords_cast]
      rfl
    have h2 := pow_mul_cast_eq hij (hjm.trans hm) k h1
    have e : (F.blockSide : ℤ) ^ (m - i) = (F.blockSide : ℤ) ^ (j - i) * (F.blockSide : ℤ) ^ (m - j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [Int.cast_add (R := ZMod (F.period i k)) _ (h' k), h2, e]
    push_cast
    ring
theorem siteCoords_siteOfCoords {j : ℕ} (A : Fin 4 → ℤ) (i : Fin 4) :
    ∃ q : ℤ, siteCoords (siteOfCoords (F := F) j A) i = A i + (F.period j i : ℤ) * q := by
  have h : ((siteCoords (siteOfCoords (F := F) j A) i : ℤ) : ZMod (F.period j i)) =
      ((A i : ℤ) : ZMod (F.period j i)) := by
    simp [siteCoords, siteOfCoords]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨q, hq⟩ := h
  exact ⟨-q, by linarith⟩
theorem enclosingCell_siteOfCoords {j : ℕ} (hj : j ≤ F.top) (hL : 0 < F.blockSide) (A : Fin 4 → ℤ) :
    enclosingCell (siteOfCoords (F := F) j A) =
      siteOfCoords F.top fun i => (A i + ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2) /
        (F.blockSide : ℤ) ^ (F.top - j) := by
  funext i
  obtain ⟨q, hq⟩ := siteCoords_siteOfCoords (F := F) (j := j) A i
  have hM : (0 : ℤ) < (F.blockSide : ℤ) ^ (F.top - j) := by positivity
  show (((siteCoords (siteOfCoords (F := F) j A) i + ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2) /
      (F.blockSide : ℤ) ^ (F.top - j) : ℤ) : ZMod (F.period F.top i)) =
      (((A i + ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2) / (F.blockSide : ℤ) ^ (F.top - j) : ℤ) :
      ZMod (F.period F.top i))
  have hper : (F.period j i : ℤ) = (F.extent i : ℤ) * (F.blockSide : ℤ) ^ (F.top - j) := by
    simp [BlockFrame.period]
  have e : (siteCoords (siteOfCoords (F := F) j A) i + ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2) /
      (F.blockSide : ℤ) ^ (F.top - j) =
      (A i + ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2) / (F.blockSide : ℤ) ^ (F.top - j) +
        (F.extent i : ℤ) * q := by
    rw [hq, hper]
    have : A i + (F.extent i : ℤ) * (F.blockSide : ℤ) ^ (F.top - j) * q +
        ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2 =
        A i + ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2 +
          ((F.extent i : ℤ) * q) * (F.blockSide : ℤ) ^ (F.top - j) := by ring
    rw [this, Int.add_mul_ediv_right _ _ hM.ne']
  rw [e]
  have h0 : (((F.extent i : ℤ) * q : ℤ) : ZMod (F.period F.top i)) = 0 := by
    have : ((F.extent i : ℕ) : ZMod (F.period F.top i)) = 0 := by
      have h1 : F.period F.top i = F.extent i := by simp [BlockFrame.period]
      rw [h1]
      exact ZMod.natCast_self _
    push_cast
    rw [this, zero_mul]
  rw [Int.cast_add, h0, add_zero]
theorem half_mul_odd {M K : ℕ} (hM : Odd M) (hK : Odd K) :
    (((M * K : ℕ) : ℤ) - 1) / 2 = (M : ℤ) * (((K : ℤ) - 1) / 2) + ((M : ℤ) - 1) / 2 := by
  obtain ⟨a, rfl⟩ := hM
  obtain ⟨b, rfl⟩ := hK
  have e1 : (((2 * b + 1 : ℕ) : ℤ) - 1) / 2 = b := by
    push_cast
    omega
  have e2 : (((2 * a + 1 : ℕ) : ℤ) - 1) / 2 = a := by
    push_cast
    omega
  have e3 : ((((2 * a + 1) * (2 * b + 1) : ℕ) : ℤ) - 1) / 2 = 2 * a * b + a + b := by
    push_cast
    have : (2 * (a : ℤ) + 1) * (2 * b + 1) - 1 = 2 * (2 * a * b + a + b) := by ring
    rw [this]
    omega
  rw [e1, e2, e3]
  push_cast
  ring
theorem enclosingCell_of_mem_sitesBelow {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (hL : Odd F.blockSide)
    {y : F.Site j} {x : F.Site i} (hx : x ∈ sitesBelow i y) : enclosingCell x = enclosingCell y := by
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx
  have hh1 := mem_centredCube_iff.1 hh
  rw [enclosingCell_siteOfCoords (hij.trans hj) hL.pos]
  funext k
  simp only [enclosingCell, siteOfCoords]
  congr 1
  have hn : F.top - i = (j - i) + (F.top - j) := by omega
  set M := F.blockSide ^ (j - i) with hMd
  set K := F.blockSide ^ (F.top - j) with hKd
  have hMo : Odd M := hL.pow
  have hKo : Odd K := hL.pow
  have e1 : (F.blockSide : ℤ) ^ (j - i) = (M : ℤ) := by rw [hMd]; push_cast; rfl
  have e2 : (F.blockSide : ℤ) ^ (F.top - j) = (K : ℤ) := by rw [hKd]; push_cast; rfl
  have e3 : (F.blockSide : ℤ) ^ (F.top - i) = ((M * K : ℕ) : ℤ) := by
    rw [hn, pow_add, e1, e2]
    push_cast
    ring
  rw [e1, e2, e3, half_mul_odd hMo hKo]
  have hM0 : (0 : ℤ) < M := by exact_mod_cast hMo.pos
  have hb := abs_le.1 (hh1 k)
  have e4 : (M : ℤ) * siteCoords y k + h k + ((M : ℤ) * (((K : ℤ) - 1) / 2) + ((M : ℤ) - 1) / 2) =
      (h k + ((M : ℤ) - 1) / 2) + (M : ℤ) * (siteCoords y k + ((K : ℤ) - 1) / 2) := by ring
  have e5 : (((M * K : ℕ) : ℤ)) = (M : ℤ) * K := by push_cast; ring
  rw [e4, e5, ← Int.ediv_ediv_of_nonneg hM0.le, Int.add_mul_ediv_left _ _ hM0.ne']
  have e6 : (h k + ((M : ℤ) - 1) / 2) / (M : ℤ) = 0 := by
    apply Int.ediv_eq_zero_of_lt
    · omega
    · obtain ⟨a, ha⟩ := hMo
      rw [ha] at hb ⊢
      push_cast at hb ⊢
      omega
  rw [e6, zero_add]
theorem sitesBelow_cell_eq (i : ℕ) (z : F.Cell) :
    sitesBelow i z = (centredCube (F.blockSide ^ (F.top - i))).image fun h => cellCentre i z + siteOfCoords i h := by
  refine Finset.image_congr fun h _ => ?_
  funext k
  simp [cellCentre, siteOfCoords]
theorem cutBelow_eq_sitesOfCells (i : ℕ) (S : Finset F.Cell) : cutBelow i S = sitesOfCells S i := by
  simp only [cutBelow, sitesOfCells]
  exact Finset.biUnion_congr rfl fun z _ => sitesBelow_cell_eq i z
theorem enclosingCell_cell (hL : 0 < F.blockSide) (z : F.Cell) : enclosingCell z = z := by
  funext k
  have h1 : F.top - F.top = 0 := Nat.sub_self _
  simp [enclosingCell, siteOfCoords, siteCoords, h1]
theorem enclosingCell_mem_of_mem_sitesOfCells {j : ℕ} (hj : j ≤ F.top) (hL : Odd F.blockSide)
    {S : Finset F.Cell} {x : F.Site j} (hx : x ∈ sitesOfCells S j) : enclosingCell x ∈ S := by
  rw [← cutBelow_eq_sitesOfCells] at hx
  obtain ⟨y, hy, hu⟩ := Finset.mem_biUnion.1 hx
  rw [enclosingCell_of_mem_sitesBelow hj le_rfl hL hu, enclosingCell_cell hL.pos]
  exact hy
theorem mem_sitesBelow_enclosingCell {j : ℕ} (hj : j ≤ F.top) (hL : Odd F.blockSide) (x : F.Site j) :
    x ∈ sitesBelow j (enclosingCell x) := by
  obtain ⟨a, ha⟩ := (hL.pow : Odd (F.blockSide ^ (F.top - j)))
  set M := F.blockSide ^ (F.top - j) with hMd
  have e1 : (F.blockSide : ℤ) ^ (F.top - j) = (M : ℤ) := by rw [hMd]; push_cast; rfl
  have hM : (M : ℤ) = 2 * a + 1 := by rw [ha]; push_cast; ring
  have hM0 : (0 : ℤ) < M := by rw [hM]; omega
  have hhalf : ((M : ℤ) - 1) / 2 = a := by rw [hM]; omega
  refine Finset.mem_image.2 ⟨fun k => (siteCoords x k + a) % (M : ℤ) - a, ?_, ?_⟩
  · refine mem_centredCube_iff.2 fun k => ?_
    rw [hhalf]
    have h1 := Int.emod_nonneg (siteCoords x k + a) hM0.ne'
    have h2 := Int.emod_lt_of_pos (siteCoords x k + a) hM0
    rw [abs_le]
    constructor <;> omega
  · funext k
    have hq : ((siteCoords (enclosingCell x) k : ℤ) : ZMod (F.period F.top k)) =
        (((siteCoords x k + a) / (M : ℤ) : ℤ) : ZMod (F.period F.top k)) := by
      rw [siteCoords_cast]
      show (((siteCoords x k + ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2) / (F.blockSide : ℤ) ^ (F.top - j) : ℤ) :
        ZMod (F.period F.top k)) = _
      rw [e1, hhalf]
    have h2 := pow_mul_cast_eq (i := j) (j := F.top) hj le_rfl k hq
    simp only [siteOfCoords]
    rw [Int.cast_add, h2, ← Int.cast_add, e1]
    have e : (M : ℤ) * ((siteCoords x k + a) / (M : ℤ)) + ((siteCoords x k + a) % (M : ℤ) - a) =
        siteCoords x k := by
      have := Int.mul_ediv_add_emod (siteCoords x k + a) (M : ℤ)
      linarith
    rw [e]
    exact siteCoords_cast x k
theorem mem_sitesOfCells_iff {j : ℕ} (hj : j ≤ F.top) (hL : Odd F.blockSide) {S : Finset F.Cell}
    {x : F.Site j} : x ∈ sitesOfCells S j ↔ enclosingCell x ∈ S := by
  refine ⟨enclosingCell_mem_of_mem_sitesOfCells hj hL, fun h => ?_⟩
  rw [← cutBelow_eq_sitesOfCells]
  exact Finset.mem_biUnion.2 ⟨enclosingCell x, h, mem_sitesBelow_enclosingCell hj hL x⟩
theorem eq_of_mem_sitesBelow_of_mem_sitesBelow {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top)
    (hL : Odd F.blockSide) {x : F.Site i} {y y' : F.Site j}
    (h1 : x ∈ sitesBelow i y) (h2 : x ∈ sitesBelow i y') : y = y' := by
  obtain ⟨h, hh, e1⟩ := Finset.mem_image.1 h1
  obtain ⟨h', hh', e2⟩ := Finset.mem_image.1 h2
  have a1 := mem_centredCube_iff.1 hh
  have a2 := mem_centredCube_iff.1 hh'
  obtain ⟨q, hq⟩ := (hL.pow : Odd (F.blockSide ^ (j - i)))
  set B := F.blockSide ^ (j - i) with hB
  have hBc : (F.blockSide : ℤ) ^ (j - i) = (B : ℤ) := by rw [hB]; push_cast; rfl
  have hhalf : ((B : ℤ) - 1) / 2 = q := by
    rw [hq]
    push_cast
    omega
  rw [hhalf] at a1 a2
  funext k
  have ek := congrFun (e1.trans e2.symm) k
  simp only [siteOfCoords, hBc] at ek
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, period_eq_pow_mul hij hj k] at ek
  push_cast at ek
  rw [hBc] at ek
  have hd : (B : ℤ) ∣ h' k - h k := by
    have h3 : (B : ℤ) ∣ (B : ℤ) * siteCoords y' k + h' k - ((B : ℤ) * siteCoords y k + h k) :=
      dvd_trans (Dvd.intro _ rfl) ek
    have h4 : (B : ℤ) * siteCoords y' k + h' k - ((B : ℤ) * siteCoords y k + h k) =
        (B : ℤ) * (siteCoords y' k - siteCoords y k) + (h' k - h k) := by ring
    rw [h4] at h3
    exact (dvd_add_right (Dvd.intro _ rfl)).1 h3
  have hz : h' k - h k = 0 := by
    have b1 := abs_le.1 (a1 k)
    have b2 := abs_le.1 (a2 k)
    refine Int.eq_zero_of_abs_lt_dvd hd ?_
    rw [abs_lt]
    constructor <;> omega
  have h4 : (B : ℤ) * siteCoords y' k + h' k - ((B : ℤ) * siteCoords y k + h k) =
      (B : ℤ) * (siteCoords y' k - siteCoords y k) := by
    have : h' k = h k := by omega
    rw [this]
    ring
  rw [h4] at ek
  have hB0 : (B : ℤ) ≠ 0 := by omega
  have h5 := (mul_dvd_mul_iff_left hB0).1 ek
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, siteCoords_cast, siteCoords_cast] at h5
  exact h5
theorem sum_sum_le_mul_sum_of_card_le {A B : Type} [DecidableEq B] (P : Finset A) (E : A → Finset B)
    (Q : Finset B) (f : B → ℝ) (hf : ∀ x, 0 ≤ f x) (K : ℕ) (hsub : ∀ p ∈ P, E p ⊆ Q)
    (hcount : ∀ x ∈ Q, (P.filter fun p => x ∈ E p).card ≤ K) :
    ∑ p ∈ P, ∑ x ∈ E p, f x ≤ K * ∑ x ∈ Q, f x := by
  classical
  calc ∑ p ∈ P, ∑ x ∈ E p, f x = ∑ p ∈ P, ∑ x ∈ Q, if x ∈ E p then f x else 0 := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext x
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨hsub p hp h, h⟩, fun h => h.2⟩
    _ = ∑ x ∈ Q, ∑ p ∈ P, if x ∈ E p then f x else 0 := Finset.sum_comm
    _ = ∑ x ∈ Q, ((P.filter fun p => x ∈ E p).card : ℝ) * f x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ Q, (K : ℝ) * f x := by
        refine Finset.sum_le_sum fun x hx => ?_
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount x hx) (hf x)
    _ = _ := (Finset.mul_sum _ _ _).symm
theorem re_mul_unitQuaternion_le_norm (q : ℍ[ℝ]) (g : UnitQuaternion) : (q * (g : ℍ[ℝ])).re ≤ ‖q‖ := by
  have h : (q * (g : ℍ[ℝ])).re ^ 2 ≤ ‖q * (g : ℍ[ℝ])‖ ^ 2 := by
    rw [sq ‖_‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    nlinarith [sq_nonneg (q * (g : ℍ[ℝ])).imI, sq_nonneg (q * (g : ℍ[ℝ])).imJ,
      sq_nonneg (q * (g : ℍ[ℝ])).imK]
  have h1 := (abs_le_of_sq_le_sq' h (norm_nonneg _)).2
  rwa [norm_mul, unitQuaternion_norm, mul_one] at h1
theorem plaquetteEnergy_nonneg (U : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) :
    0 ≤ plaquetteEnergy U p := by apply _root_.YangMills.Construction.LumpContours.CutAction.plaquetteEnergy_nonneg <;> assumption
theorem blockFit_nonneg {l : ℕ} (W : F.GaugeField l) (V : F.GaugeField (l + 1)) (c : F.Site (l + 1) × Fin 4) :
    0 ≤ blockFit W V c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.blockFit_nonneg <;> assumption
theorem gaugedBlockFit_nonneg {l : ℕ} (W : F.GaugeField l) (k : F.Site (l + 1) → UnitQuaternion)
    (V : F.GaugeField (l + 1)) (c : F.Site (l + 1) × Fin 4) : 0 ≤ gaugedBlockFit W k V c := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.gaugedBlockFit_nonneg <;> assumption
theorem cutBelow_mono {m : ℕ} (i : ℕ) {Z Z' : Finset (F.Site m)} (h : Z ⊆ Z') :
    cutBelow i Z ⊆ cutBelow i Z' := Finset.biUnion_subset_biUnion_of_subset_left _ h
theorem cutPlaquettes_mono {l : ℕ} {Z Z' : Finset (F.Site l)} (h : Z ⊆ Z') :
    cutPlaquettes Z ⊆ cutPlaquettes Z' := by
  intro p hp
  simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp ⊢
  exact ⟨h hp.1, hp.2.1, hp.2.2.trans h⟩
theorem cutBonds_mono {l : ℕ} {Z Z' : Finset (F.Site l)} (h : Z ⊆ Z') : cutBonds Z ⊆ cutBonds Z' := by
  intro b hb
  simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hb ⊢
  exact ⟨h hb.1, h hb.2⟩
theorem succ_ediv_eq_or (a M : ℤ) (hM : 0 < M) : (a + 1) / M = a / M ∨ (a + 1) / M = a / M + 1 := by
  have h1 : a / M ≤ (a + 1) / M := Int.ediv_le_ediv hM (by omega)
  have h2 : (a + 1) / M ≤ (a + M) / M := Int.ediv_le_ediv hM (by omega)
  have h3 : (a + M) / M = a / M + 1 := by
    have := Int.add_mul_ediv_right a 1 hM.ne'
    simpa using this
  omega
theorem enclosingCell_add_unitStep {j : ℕ} (hj : j ≤ F.top) (hL : 0 < F.blockSide) (x : F.Site j) (i : Fin 4) :
    enclosingCell (x + unitStep j i) = enclosingCell x ∨
      enclosingCell (x + unitStep j i) = enclosingCell x + unitStep F.top i := by
  have hM : (0 : ℤ) < (F.blockSide : ℤ) ^ (F.top - j) := by positivity
  have e1 : x + unitStep j i = siteOfCoords j (siteCoords x + Pi.single i 1) := by
    rw [siteOfCoords_add, siteOfCoords_siteCoords]
    rfl
  have e2 : enclosingCell x = siteOfCoords F.top fun k =>
      (siteCoords x k + ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2) / (F.blockSide : ℤ) ^ (F.top - j) := rfl
  rw [e1, enclosingCell_siteOfCoords hj hL, e2]
  set b := ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2
  set M := (F.blockSide : ℤ) ^ (F.top - j)
  have hstep : ((siteCoords x i + b) + 1) / M = (siteCoords x i + b) / M ∨
      ((siteCoords x i + b) + 1) / M = (siteCoords x i + b) / M + 1 :=
    succ_ediv_eq_or _ _ hM
  rcases hstep with h | h
  · left
    funext k
    by_cases hk : k = i
    · subst hk
      simp only [siteOfCoords, Pi.add_apply, Pi.single_eq_same]
      have e3 : siteCoords x k + 1 + b = siteCoords x k + b + 1 := by ring
      rw [e3, h]
    · simp only [siteOfCoords, Pi.add_apply, Pi.single_eq_of_ne hk, add_zero]
  · right
    funext k
    by_cases hk : k = i
    · subst hk
      simp only [siteOfCoords, unitStep, Pi.add_apply, Pi.single_eq_same]
      have e3 : siteCoords x k + 1 + b = siteCoords x k + b + 1 := by ring
      rw [e3, h]
      push_cast
      rfl
    · simp only [siteOfCoords, unitStep, Pi.add_apply, Pi.single_eq_of_ne hk, add_zero]
      simp
theorem add_mem_cellBall_one (z : F.Cell) (h : Fin 4 → ℤ) (hh : ∀ m, |h m| ≤ 1) :
    z + siteOfCoords F.top h ∈ cellBall z 1 := by
  refine Finset.mem_image.2 ⟨h, mem_centredCube_iff.2 fun m => ?_, rfl⟩
  simpa using hh m
theorem abs_single_le_one (i m : Fin 4) : |(Pi.single i (1 : ℤ) : Fin 4 → ℤ) m| ≤ 1 := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.abs_single_one_le <;> assumption
theorem enclosingCell_add_unitStep_mem_cellBall {j : ℕ} (hj : j ≤ F.top) (hL : 0 < F.blockSide)
    (x : F.Site j) (i : Fin 4) : enclosingCell (x + unitStep j i) ∈ cellBall (enclosingCell x) 1 := by
  rcases enclosingCell_add_unitStep hj hL x i with h | h
  · rw [h]
    have := add_mem_cellBall_one (enclosingCell x) 0 (by simp)
    simpa [siteOfCoords_zero] using this
  · rw [h]
    exact add_mem_cellBall_one (enclosingCell x) _ (abs_single_le_one i)
theorem enclosingCell_corner_mem_cellBall {j : ℕ} (hj : j ≤ F.top) (hL : 0 < F.blockSide)
    (p : F.Site j × Fin 4 × Fin 4) (hlt : p.2.1 < p.2.2) {x : F.Site j} (hx : x ∈ plaquetteCorners p) :
    enclosingCell x ∈ cellBall (enclosingCell p.1) 1 := by
  have hne : p.2.1 ≠ p.2.2 := hlt.ne
  have two : enclosingCell (p.1 + unitStep j p.2.1 + unitStep j p.2.2) ∈ cellBall (enclosingCell p.1) 1 := by
    have hh : ∀ (d d' : ℤ), (d = 0 ∨ d = 1) → (d' = 0 ∨ d' = 1) → ∀ m,
        |(d • (Pi.single p.2.1 (1 : ℤ) : Fin 4 → ℤ) + d' • (Pi.single p.2.2 (1 : ℤ) : Fin 4 → ℤ)) m| ≤ 1 := by
      intro d d' hd hd' m
      by_cases h1 : m = p.2.1
      · subst h1
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, smul_eq_mul]
        rcases hd with rfl | rfl <;> simp
      · by_cases h2 : m = p.2.2
        · subst h2
          simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne h1, smul_eq_mul]
          rcases hd' with rfl | rfl <;> simp
        · simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
    have e : ∀ (d d' : ℤ), enclosingCell p.1 + siteOfCoords F.top (d • (Pi.single p.2.1 (1 : ℤ) : Fin 4 → ℤ) +
        d' • (Pi.single p.2.2 (1 : ℤ) : Fin 4 → ℤ)) =
        enclosingCell p.1 + d • unitStep F.top p.2.1 + d' • unitStep F.top p.2.2 := by
      intro d d'
      rw [siteOfCoords_add, siteOfCoords_single, siteOfCoords_single, add_assoc]
    rcases enclosingCell_add_unitStep hj hL p.1 p.2.1 with h | h <;>
      rcases enclosingCell_add_unitStep hj hL (p.1 + unitStep j p.2.1) p.2.2 with h' | h'
    · rw [h', h]
      have hm := add_mem_cellBall_one (enclosingCell p.1) _ (hh 0 0 (Or.inl rfl) (Or.inl rfl))
      rw [e 0 0] at hm
      simpa using hm
    · rw [h', h]
      have hm := add_mem_cellBall_one (enclosingCell p.1) _ (hh 0 1 (Or.inl rfl) (Or.inr rfl))
      rw [e 0 1] at hm
      simpa using hm
    · rw [h', h]
      have hm := add_mem_cellBall_one (enclosingCell p.1) _ (hh 1 0 (Or.inr rfl) (Or.inl rfl))
      rw [e 1 0] at hm
      simpa using hm
    · rw [h', h]
      have hm := add_mem_cellBall_one (enclosingCell p.1) _ (hh 1 1 (Or.inr rfl) (Or.inr rfl))
      rw [e 1 1] at hm
      simpa using hm
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · have := add_mem_cellBall_one (enclosingCell p.1) 0 (by simp)
    simpa [siteOfCoords_zero] using this
  · exact enclosingCell_add_unitStep_mem_cellBall hj hL _ _
  · exact enclosingCell_add_unitStep_mem_cellBall hj hL _ _
  · exact two
end BlockLevels
end LumpContours
end YangMills.Construction
end
