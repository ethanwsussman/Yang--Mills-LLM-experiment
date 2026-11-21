import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.HoleBesideASecondHole.ChainChangedAtTheBottom
import YangMills.Construction.HoleBesideASecondHole.CoercivityOfTheChainProof
import YangMills.Construction.HoleBesideASecondHole.MeanOfAProductOfGroupVariablesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LumpContours
open BlockAverages GroupMeans
namespace BottomModified
variable {F : BlockFrame}
theorem unitQuaternion_mul_inv (g : UnitQuaternion) :
    (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := (Unitary.mem_iff.1 g.2).2
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem pathDisplacement_append (j : ℕ) (l l' : List PathStep) :
    pathDisplacement (F := F) j (l ++ l') = pathDisplacement j l + pathDisplacement j l' := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_append <;> assumption
theorem pathDisplacement_reversePath (j : ℕ) (l : List PathStep) :
    pathDisplacement (F := F) j (reversePath l) = - pathDisplacement j l := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_reversePath <;> assumption
theorem refineSite_add_step (j : ℕ) (hj : j < F.top) (y : F.Site (j + 1)) (st : PathStep) :
    refineSite (y + stepDisplacement (j + 1) st) = refineSite y + F.blockSide • stepDisplacement j st := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.refineSite_add_step <;> assumption
theorem pathDisplacement_replicate (j n : ℕ) (st : PathStep) :
    pathDisplacement (F := F) j (List.replicate n st) = n • stepDisplacement j st := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_replicate <;> assumption
theorem siteOfCoords_eq_sum (j : ℕ) (h : Fin 4 → ℤ) :
    siteOfCoords (F := F) j h = ∑ i, h i • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_eq_sum <;> assumption
theorem pathDisplacement_axisPath (j : ℕ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    pathDisplacement (F := F) j (axisPath h π) = siteOfCoords j h := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_axisPath <;> assumption
def WithinBlock (L : ℕ) (o : Fin 4 → ℤ) : Prop := ∀ m, |o m| ≤ ((L : ℤ) - 1) / 2
theorem siteOfCoords_add (j : ℕ) (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j (a + b) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem siteOfCoords_single (j : ℕ) (c : ℤ) (i : Fin 4) :
    siteOfCoords (F := F) j (c • Pi.single i 1) = c • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_single <;> assumption
theorem siteOfCoords_zero (j : ℕ) : siteOfCoords (F := F) j 0 = 0 := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_zero <;> assumption
theorem mem_centredCube_of_withinBlock {L : ℕ} {o : Fin 4 → ℤ} (ho : WithinBlock L o) : o ∈ centredCube L := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.mem_centredCube_of_withinBlock <;> assumption
theorem withinBlock_of_mem_centredCube {L : ℕ} {o : Fin 4 → ℤ} (ho : o ∈ centredCube L) : WithinBlock L o := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.withinBlock_of_mem_centredCube <;> assumption
theorem refineSite_add_mem_sitesBelow (j : ℕ) (y : F.Site (j + 1)) {o : Fin 4 → ℤ}
    (ho : WithinBlock F.blockSide o) :
    refineSite y + siteOfCoords j o ∈ sitesBelow j y := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.refineSite_add_mem_sitesBelow <;> assumption
theorem add_smul_single_apply (o : Fin 4 → ℤ) (c : ℤ) (i m : Fin 4) :
    (o + c • (Pi.single i 1 : Fin 4 → ℤ)) m = o m + if m = i then c else 0 := by apply _root_.YangMills.Construction.GaugeFixing.add_smul_single_apply <;> assumption
theorem mem_adjacent_blocks (j : ℕ) (hj : j < F.top) (hL : Odd F.blockSide) (y : F.Site (j + 1)) (i : Fin 4)
    {o : Fin 4 → ℤ} (ho : WithinBlock F.blockSide o) (r : ℕ) (hr : r ≤ F.blockSide) :
    refineSite y + siteOfCoords j o + r • unitStep j i ∈
      sitesBelow j y ∪ sitesBelow j (y + unitStep (j + 1) i) := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.mem_adjacent_blocks <;> assumption
def axisPrefixOffset (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : ℕ) : Fin 4 → ℤ :=
  fun m => if ((π.symm m : Fin 4) : ℕ) < k then h m else 0
theorem axisPrefixOffset_zero (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) : axisPrefixOffset h π 0 = 0 := by apply _root_.YangMills.Construction.GaugeFixing.partialOffset_zero <;> assumption
theorem axisSegment_withinBlock (L : ℕ) (h : Fin 4 → ℤ) (hh : WithinBlock L h) (π : Equiv.Perm (Fin 4))
    (k : Fin 4) (r : ℕ) (hr : r ≤ (h (π k)).natAbs) :
    WithinBlock L (axisPrefixOffset h π k +
      (if decide (0 ≤ h (π k)) then (r : ℤ) else -(r : ℤ)) • Pi.single (π k) 1) := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.axisPathOffset_flow_withinBlock <;> assumption
theorem axisPath_eq_segments (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    axisPath h π =
      List.replicate (h (π 0)).natAbs (π 0, decide (0 ≤ h (π 0))) ++
      (List.replicate (h (π 1)).natAbs (π 1, decide (0 ≤ h (π 1))) ++
      (List.replicate (h (π 2)).natAbs (π 2, decide (0 ≤ h (π 2))) ++
      (List.replicate (h (π 3)).natAbs (π 3, decide (0 ≤ h (π 3))) ++ []))) := by apply _root_.YangMills.Construction.GaugeFixing.axisPath_eq_append <;> assumption
def axisSegment (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : Fin 4) : List PathStep :=
  List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))
theorem add_axisPrefixOffset_step (j : ℕ) (x : F.Site j) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : Fin 4) :
    x + siteOfCoords j (axisPrefixOffset h π k) + pathDisplacement j (axisSegment h π k) =
      x + siteOfCoords j (axisPrefixOffset h π ((k : ℕ) + 1)) := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.add_axisPathFlow <;> assumption
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
theorem PathWithin.reverse {j : ℕ} (Z : Finset (F.Site j)) (l : List PathStep) :
    ∀ x, PathWithin Z x l → PathWithin Z (x + pathDisplacement j l) (reversePath l) := by
  induction l with
  | nil => intro x _; trivial
  | cons st r ih =>
    intro x h
    have e : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
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
theorem pathHolonomy_congr {j : ℕ} (Z : Finset (F.Site j)) (X X' : F.GaugeField j)
    (hX : ∀ x i, x ∈ Z → x + unitStep j i ∈ Z → X x i = X' x i) (l : List PathStep) :
    ∀ x, PathWithin Z x l → pathHolonomy X x l = pathHolonomy X' x l := by
  induction l with
  | nil => intro x _; rfl
  | cons st r ih =>
    intro x h
    simp only [pathHolonomy]
    rw [ih _ h.2.2]
    congr 1
    obtain ⟨d, b⟩ := st
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      have h1 := h.1
      have h2 := h.2.1
      simp only [stepDisplacement, Bool.false_eq_true, if_false] at h2
      rw [hX (x - unitStep j d) d (by simpa [sub_eq_add_neg] using h2) (by simpa using h1)]
    · simp only [linkValue, if_true]
      have h2 := h.2.1
      simp only [stepDisplacement, if_true] at h2
      rw [hX x d h.1 h2]
theorem axisPath_within_block (j : ℕ) (hL : Odd F.blockSide) (y : F.Site (j + 1)) (h : Fin 4 → ℤ)
    (hh : WithinBlock F.blockSide h) (π : Equiv.Perm (Fin 4)) :
    PathWithin (sitesBelow j y) (refineSite y) (axisPath h π) := by
  have piece : ∀ k : Fin 4, PathWithin (sitesBelow j y)
      (refineSite y + siteOfCoords j (axisPrefixOffset h π k)) (axisSegment h π k) := by
    intro k
    refine PathWithin.replicate _ _ _ _ fun r hr => ?_
    have h1 := axisSegment_withinBlock F.blockSide h hh π k r hr
    have e : refineSite y + siteOfCoords j (axisPrefixOffset h π k) +
          r • stepDisplacement j (π k, decide (0 ≤ h (π k))) =
        refineSite y + siteOfCoords j (axisPrefixOffset h π k +
          (if decide (0 ≤ h (π k)) then (r : ℤ) else -(r : ℤ)) • Pi.single (π k) 1) := by
      rw [siteOfCoords_add, siteOfCoords_single, add_assoc]
      by_cases hc : 0 ≤ h (π k)
      · simp [stepDisplacement, hc]
      · simp [stepDisplacement, hc]
    rw [e]
    exact refineSite_add_mem_sitesBelow j y h1
  rw [axisPath_eq_segments]
  have s0 := add_axisPrefixOffset_step j (refineSite y) h π 0
  have s1 := add_axisPrefixOffset_step j (refineSite y) h π 1
  have s2 := add_axisPrefixOffset_step j (refineSite y) h π 2
  have z0 : refineSite y + siteOfCoords j (axisPrefixOffset h π ((0 : Fin 4) : ℕ)) = refineSite y := by
    simp [axisPrefixOffset_zero, siteOfCoords_zero]
  have p0 := piece 0
  have p1 := piece 1
  have p2 := piece 2
  have p3 := piece 3
  rw [z0] at p0 s0
  refine PathWithin.append _ _ _ _ p0 ?_
  have e01 : refineSite y + pathDisplacement j (axisSegment h π 0) =
      refineSite y + siteOfCoords j (axisPrefixOffset h π ((1 : Fin 4) : ℕ)) := s0
  simp only [axisSegment] at e01
  rw [e01]
  refine PathWithin.append _ _ _ _ p1 ?_
  have e12 : refineSite y + siteOfCoords j (axisPrefixOffset h π ((1 : Fin 4) : ℕ)) +
      pathDisplacement j (axisSegment h π 1) =
      refineSite y + siteOfCoords j (axisPrefixOffset h π ((2 : Fin 4) : ℕ)) := s1
  simp only [axisSegment] at e12
  rw [e12]
  refine PathWithin.append _ _ _ _ p2 ?_
  have e23 : refineSite y + siteOfCoords j (axisPrefixOffset h π ((2 : Fin 4) : ℕ)) +
      pathDisplacement j (axisSegment h π 2) =
      refineSite y + siteOfCoords j (axisPrefixOffset h π ((3 : Fin 4) : ℕ)) := s2
  simp only [axisSegment] at e23
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
  · have r2 := PathWithin.reverse _ _ _ (PathWithin.mono (Z' := Z) Finset.subset_union_right _ _ l2)
    rw [pathDisplacement_append, pathDisplacement_axisPath, pathDisplacement_replicate]
    have e : refineSite c.1 + (siteOfCoords j h + F.blockSide • stepDisplacement j (c.2, true)) =
        refineSite (c.1 + unitStep (j + 1) c.2) + pathDisplacement j (axisPath h π) := by
      have := refineSite_add_step j hj c.1 (c.2, true)
      simp only [stepDisplacement, if_true] at this ⊢
      rw [this, pathDisplacement_axisPath]
      abel
    rw [e]
    exact r2
theorem sitesBelow_subset_cutBelow {t l : ℕ} (hl : l < t) (hm : t ≤ F.top) (hL : Odd F.blockSide)
    {X : Finset (F.Site t)} {w : F.Site (l + 1)} (hw : w ∈ cutBelow (l + 1) X) :
    sitesBelow l w ⊆ cutBelow l X := by apply _root_.YangMills.Construction.CoercivityProof.sitesBelow_subset_cutBelow <;> assumption
theorem norm_smul_polarPart (q : ℍ[ℝ]) : (‖q‖ : ℝ) • ((polarPart q : UnitQuaternion) : ℍ[ℝ]) = q := by apply _root_.YangMills.Construction.GroupMeans.norm_smul_polarPart <;> assumption
theorem norm_sub_re_mul_polarPart_inv (q : ℍ[ℝ]) :
    ‖q‖ - (q * (((polarPart q)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = 0 := by
  have e : q * (((polarPart q)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = ((‖q‖ : ℝ) : ℍ[ℝ]) := by
    calc q * (((polarPart q)⁻¹ : UnitQuaternion) : ℍ[ℝ])
        = ((‖q‖ : ℝ) • ((polarPart q : UnitQuaternion) : ℍ[ℝ])) *
            (((polarPart q)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
          rw [norm_smul_polarPart]
      _ = (‖q‖ : ℝ) • (((polarPart q : UnitQuaternion) : ℍ[ℝ]) *
            (((polarPart q)⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by
          rw [smul_mul_assoc]
      _ = _ := by
          rw [unitQuaternion_mul_inv]
          ext <;> simp
  rw [e]
  simp
section bottomModified
variable {t : ℕ} (G : Finset (F.Site t)) (U : F.FieldChain) (U₀ : F.GaugeField 0)
theorem bottomModifiedField_cut (hb : ∀ b ∈ cutBonds (cutBelow 0 G), U₀ b.1 b.2 = U 0 b.1 b.2) :
    ∀ i, ∀ b ∈ cutBonds (cutBelow i G), bottomModifiedField G U U₀ i b.1 b.2 = U i b.1 b.2 := by
  intro i b hbm
  cases i with
  | zero => exact hb b hbm
  | succ i =>
    have h := (Finset.mem_filter.1 hbm)
    rw [bottomModifiedField]
    have h1 := (Finset.mem_product.1 h.1).1
    simp only [if_pos (And.intro h1 h.2)]
theorem contourAverage_bottomModifiedField (ht : t ≤ F.top) (hL : Odd F.blockSide)
    (hb : ∀ b ∈ cutBonds (cutBelow 0 G), U₀ b.1 b.2 = U 0 b.1 b.2)
    {i : ℕ} (hi : i < t) (c : F.Site (i + 1) × Fin 4) (hc : c ∈ cutBonds (cutBelow (i + 1) G)) :
    contourAverage (bottomModifiedField G U U₀ i) c = contourAverage (U i) c := by
  have hi' : i < F.top := by omega
  have h := Finset.mem_filter.1 hc
  have h1 := (Finset.mem_product.1 h.1).1
  have hZ : sitesBelow i c.1 ∪ sitesBelow i (c.1 + unitStep (i + 1) c.2) ⊆ cutBelow i G :=
    Finset.union_subset (sitesBelow_subset_cutBelow hi ht hL h1) (sitesBelow_subset_cutBelow hi ht hL h.2)
  unfold contourAverage
  congr 1
  refine Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun π _ => ?_
  rw [pathHolonomy_congr (sitesBelow i c.1 ∪ sitesBelow i (c.1 + unitStep (i + 1) c.2))
    (bottomModifiedField G U U₀ i) (U i)
    (fun x d h2 h3 => ?_) _ _ (bondContour_within_blocks i hi' hL c e (withinBlock_of_mem_centredCube he) π)]
  refine bottomModifiedField_cut G U U₀ hb i (x, d) ?_
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hZ h2, Finset.mem_univ _⟩, hZ h3⟩
theorem blockFit_bottomModifiedField (ht : t ≤ F.top) (hL : Odd F.blockSide)
    (hb : ∀ b ∈ cutBonds (cutBelow 0 G), U₀ b.1 b.2 = U 0 b.1 b.2)
    {i : ℕ} (hi : i < t) (c : F.Site (i + 1) × Fin 4) :
    blockFit (bottomModifiedField G U U₀ i) (bottomModifiedField G U U₀ (i + 1)) c =
      if c ∈ cutBonds (cutBelow (i + 1) G) then blockFit (U i) (U (i + 1)) c else 0 := by
  classical
  by_cases hc : c ∈ cutBonds (cutBelow (i + 1) G)
  · rw [if_pos hc]
    unfold blockFit
    rw [contourAverage_bottomModifiedField G U U₀ ht hL hb hi c hc, bottomModifiedField_cut G U U₀ hb (i + 1) c hc]
  · rw [if_neg hc]
    have hn : ¬ (c.1 ∈ cutBelow (i + 1) G ∧ c.1 + unitStep (i + 1) c.2 ∈ cutBelow (i + 1) G) := by
      intro h
      exact hc (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h.1, Finset.mem_univ _⟩, h.2⟩)
    have e : bottomModifiedField G U U₀ (i + 1) c.1 c.2 =
        polarPart (contourAverage (bottomModifiedField G U U₀ i) c) := by
      rw [bottomModifiedField]
      simp only [if_neg hn]
    unfold blockFit
    rw [e]
    exact norm_sub_re_mul_polarPart_inv _
theorem cutChainEnergy_bottomModifiedField (ht : t ≤ F.top) (hL : Odd F.blockSide)
    (hb : ∀ b ∈ cutBonds (cutBelow 0 G), U₀ b.1 b.2 = U 0 b.1 b.2) (a : ℝ) (Q : Finset (F.Site t))
    (hQ : G ⊆ Q) :
    cutChainEnergy a t Q (bottomModifiedField G U U₀) =
      ∑ p ∈ cutPlaquettes (cutBelow 0 Q), plaquetteEnergy U₀ p +
        a * ∑ i ∈ Finset.range t, ∑ c ∈ cutBonds (cutBelow (i + 1) G), blockFit (U i) (U (i + 1)) c := by
  classical
  unfold cutChainEnergy
  have e0 : bottomModifiedField G U U₀ 0 = U₀ := by rw [bottomModifiedField]
  have hs : ∑ i ∈ Finset.range t, ∑ c ∈ cutBonds (cutBelow (i + 1) Q),
      blockFit (bottomModifiedField G U U₀ i) (bottomModifiedField G U U₀ (i + 1)) c =
      ∑ i ∈ Finset.range t, ∑ c ∈ cutBonds (cutBelow (i + 1) G), blockFit (U i) (U (i + 1)) c := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    have hsub : cutBonds (cutBelow (i + 1) G) ⊆ cutBonds (cutBelow (i + 1) Q) := by
      intro c hc
      have hm : cutBelow (i + 1) G ⊆ cutBelow (i + 1) Q := Finset.biUnion_subset_biUnion_of_subset_left _ hQ
      have h := Finset.mem_filter.1 hc
      exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hm (Finset.mem_product.1 h.1).1, Finset.mem_univ _⟩, hm h.2⟩
    rw [Finset.sum_congr rfl fun c _ => blockFit_bottomModifiedField G U U₀ ht hL hb hi' c, Finset.sum_ite_mem,
      Finset.inter_eq_right.2 hsub]
  rw [e0, hs]
end bottomModified
end BottomModified
theorem bottomModifiedChainIdentity_proof : BottomModifiedChainIdentity := by
  intro F t ht hL G U U₀ hb
  exact ⟨fun i _ b hbm => BottomModified.bottomModifiedField_cut G U U₀ hb i b hbm,
    fun i hi c => BottomModified.blockFit_bottomModifiedField G U U₀ ht hL hb hi c,
    fun a Q hQ => BottomModified.cutChainEnergy_bottomModifiedField G U U₀ ht hL hb a Q hQ⟩
end YangMills.Construction.LumpContours
end
