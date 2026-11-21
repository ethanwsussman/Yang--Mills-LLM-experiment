import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours
namespace PathHolonomy
variable {F : BlockFrame}
theorem unitQuaternion_coe_mul (g g' : UnitQuaternion) :
    ((g * g' : UnitQuaternion) : ℍ[ℝ]) = (g : ℍ[ℝ]) * (g' : ℍ[ℝ]) := rfl
theorem unitQuaternion_norm (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem unitQuaternion_coe_mul_inv (g : UnitQuaternion) :
    (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := (Unitary.mem_iff.1 g.2).2
theorem norm_unitQuaternion_mul (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖(g : ℍ[ℝ]) * q‖ = ‖q‖ := by
  rw [norm_mul, unitQuaternion_norm, one_mul]
theorem norm_mul_unitQuaternion (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖q * (g : ℍ[ℝ])‖ = ‖q‖ := by
  rw [norm_mul, unitQuaternion_norm, mul_one]
theorem norm_sub_inv_eq (g g' : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(g : ℍ[ℝ]) - g'‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem pathHolonomy_append {j : ℕ} (X : F.GaugeField j) (l l' : List PathStep) :
    ∀ x, pathHolonomy X x (l ++ l') =
      pathHolonomy X x l * pathHolonomy X (x + pathDisplacement j l) l' := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_append <;> assumption
theorem pathDisplacement_append (j : ℕ) (l l' : List PathStep) :
    pathDisplacement (F := F) j (l ++ l') = pathDisplacement j l + pathDisplacement j l' := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_append <;> assumption
theorem pathDisplacement_reversePath (j : ℕ) (l : List PathStep) :
    pathDisplacement (F := F) j (reversePath l) = - pathDisplacement j l := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_reversePath <;> assumption
theorem pathHolonomy_reversePath {j : ℕ} (X : F.GaugeField j) (l : List PathStep) :
    ∀ x, pathHolonomy X (x + pathDisplacement j l) (reversePath l) = (pathHolonomy X x l)⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_reversePath <;> assumption
theorem refineSite_add_stepDisplacement (j : ℕ) (hj : j < F.top) (y : F.Site (j + 1)) (st : PathStep) :
    refineSite (y + stepDisplacement (j + 1) st) = refineSite y + F.blockSide • stepDisplacement j st := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.refineSite_add_step <;> assumption
theorem pathDisplacement_replicate (j n : ℕ) (st : PathStep) :
    pathDisplacement (F := F) j (List.replicate n st) = n • stepDisplacement j st := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_replicate <;> assumption
theorem siteOfCoords_eq_sum (j : ℕ) (h : Fin 4 → ℤ) :
    siteOfCoords (F := F) j h = ∑ i, h i • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_eq_sum <;> assumption
theorem pathDisplacement_straight (j : ℕ) (c : ℤ) (i : Fin 4) :
    pathDisplacement (F := F) j (List.replicate c.natAbs (i, decide (0 ≤ c))) = c • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_replicate_axis <;> assumption
theorem pathDisplacement_axisPath (j : ℕ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    pathDisplacement (F := F) j (axisPath h π) = siteOfCoords j h := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_axisPath <;> assumption
def OffsetInBlock (L : ℕ) (o : Fin 4 → ℤ) : Prop := ∀ m, |o m| ≤ ((L : ℤ) - 1) / 2
theorem siteOfCoords_add (j : ℕ) (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j (a + b) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem siteOfCoords_zero (j : ℕ) : siteOfCoords (F := F) j 0 = 0 := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_zero <;> assumption
theorem mem_centredCube_of_offsetInBlock {L : ℕ} {o : Fin 4 → ℤ} (ho : OffsetInBlock L o) :
    o ∈ centredCube L := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.mem_centredCube_of_withinBlock <;> assumption
theorem offsetInBlock_of_mem_centredCube {L : ℕ} {o : Fin 4 → ℤ} (ho : o ∈ centredCube L) :
    OffsetInBlock L o := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.withinBlock_of_mem_centredCube <;> assumption
open Classical in
def touchCount {j : ℕ} (D : Finset (F.Site j)) : F.Site j → List PathStep → ℕ
  | _, [] => 0
  | x, st :: r => (if x ∈ D ∨ x + stepDisplacement j st ∈ D then 1 else 0) +
      touchCount D (x + stepDisplacement j st) r
theorem touchCount_append {j : ℕ} (D : Finset (F.Site j)) (P Q : List PathStep) :
    ∀ x, touchCount D x (P ++ Q) = touchCount D x P + touchCount D (x + pathDisplacement j P) Q := by
  induction P with
  | nil =>
    intro x
    simp [touchCount, pathDisplacement]
  | cons st r ih =>
    intro x
    simp only [List.cons_append, touchCount]
    have : x + stepDisplacement j st + pathDisplacement j r = x + pathDisplacement j (st :: r) := by
      simp [pathDisplacement, add_assoc]
    rw [ih, this]
    omega
def LinksClose {j : ℕ} (X Y : F.GaugeField j) (D Q : Finset (F.Site j)) (K : ℝ) : Prop :=
  ∀ x ∈ Q, ∀ st : PathStep, x + stepDisplacement j st ∈ Q →
    ‖((linkValue X x st : UnitQuaternion) : ℍ[ℝ]) - (linkValue Y x st : UnitQuaternion)‖ ≤ K ∧
      (x ∉ D → x + stepDisplacement j st ∉ D → linkValue X x st = linkValue Y x st)
theorem linksClose_of_cutBonds {j : ℕ} (X Y : F.GaugeField j) (D Q : Finset (F.Site j)) (K : ℝ)
    (h1 : ∀ b ∈ cutBonds Q, ‖((X b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - (Y b.1 b.2 : UnitQuaternion)‖ ≤ K)
    (h2 : ∀ b ∈ cutBonds Q, b.1 ∉ D → b.1 + unitStep j b.2 ∉ D → X b.1 b.2 = Y b.1 b.2) :
    LinksClose X Y D Q K := by
  intro x hx st hst
  obtain ⟨d, b⟩ := st
  cases b
  · have hs : x + stepDisplacement j (d, false) = x - unitStep j d := by
      simp only [stepDisplacement, Bool.false_eq_true, if_false]
      rw [sub_eq_add_neg]
    rw [hs] at hst ⊢
    have e : x - unitStep j d + unitStep j d = x := sub_add_cancel _ _
    have hb : ((x - unitStep j d, d) : F.Site j × Fin 4) ∈ cutBonds Q := by
      refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hst, Finset.mem_univ _⟩, ?_⟩
      show x - unitStep j d + unitStep j d ∈ Q
      rw [e]
      exact hx
    constructor
    · have h3 := h1 (x - unitStep j d, d) hb
      simp only at h3
      simp only [linkValue, Bool.false_eq_true, if_false]
      rw [norm_sub_inv_eq]
      exact h3
    · intro a1 a2
      simp only [linkValue, Bool.false_eq_true, if_false]
      have a3 : (x - unitStep j d, d).1 + unitStep j (x - unitStep j d, d).2 ∉ D := by
        show x - unitStep j d + unitStep j d ∉ D
        rw [e]
        exact a1
      rw [h2 _ hb a2 a3]
  · have hs : x + stepDisplacement j (d, true) = x + unitStep j d := by
      simp only [stepDisplacement, if_true]
    rw [hs] at hst ⊢
    have hb : ((x, d) : F.Site j × Fin 4) ∈ cutBonds Q :=
      Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩, hst⟩
    constructor
    · simp only [linkValue, if_true]
      exact h1 _ hb
    · intro a1 a2
      simp only [linkValue, if_true]
      rw [h2 _ hb a1 a2]
theorem norm_pathHolonomy_sub_le {j : ℕ} (X Y : F.GaugeField j) (D Q : Finset (F.Site j)) (K : ℝ)
    (hK : 0 ≤ K) (h : LinksClose X Y D Q K) (P : List PathStep) :
    ∀ x, (∀ z ∈ pathSites x P, z ∈ Q) →
      ‖((pathHolonomy X x P : UnitQuaternion) : ℍ[ℝ]) - (pathHolonomy Y x P : UnitQuaternion)‖ ≤
        K * touchCount D x P := by
  classical
  induction P with
  | nil =>
    intro x _
    simp [pathHolonomy, touchCount]
  | cons st r ih =>
    intro x hx
    have hx0 : x ∈ Q := hx x (by simp [pathSites])
    have hx1 : ∀ z ∈ pathSites (x + stepDisplacement j st) r, z ∈ Q := fun z hz => hx z (by
      simp only [pathSites, List.mem_cons]
      exact Or.inr hz)
    have hx2 : x + stepDisplacement j st ∈ Q := by
      refine hx1 _ ?_
      cases r with
      | nil => simp [pathSites]
      | cons st' r' => simp [pathSites]
    have i1 := ih _ hx1
    obtain ⟨s1, s2⟩ := h x hx0 st hx2
    simp only [pathHolonomy, touchCount]
    set a := linkValue X x st
    set b := linkValue Y x st
    set u := pathHolonomy X (x + stepDisplacement j st) r
    set v := pathHolonomy Y (x + stepDisplacement j st) r
    have e : ((a * u : UnitQuaternion) : ℍ[ℝ]) - ((b * v : UnitQuaternion) : ℍ[ℝ]) =
        ((a : ℍ[ℝ]) - b) * (u : ℍ[ℝ]) + (b : ℍ[ℝ]) * ((u : ℍ[ℝ]) - v) := by
      rw [unitQuaternion_coe_mul, unitQuaternion_coe_mul]
      noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul_unitQuaternion, norm_unitQuaternion_mul]
    by_cases hc : x ∈ D ∨ x + stepDisplacement j st ∈ D
    · simp only [hc, if_true]
      push_cast
      nlinarith
    · push_neg at hc
      have hab : a = b := s2 hc.1 hc.2
      simp only [hab, sub_self, norm_zero]
      have : ¬ (x ∈ D ∨ x + stepDisplacement j st ∈ D) := by
        rintro (h' | h')
        · exact hc.1 h'
        · exact hc.2 h'
      simp only [this, if_false]
      push_cast
      linarith
theorem unitStep_apply_self (j : ℕ) (i : Fin 4) : (unitStep j i : F.Site j) i = 1 := by
  simp [unitStep, siteOfCoords]
theorem natCast_inj_of_lt {p r r' : ℕ} (h : (r : ZMod p) = r') (hr : r < p) (hr' : r' < p) :
    r = r' := by
  have := (ZMod.natCast_eq_natCast_iff' r r' p).1 h
  rwa [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at this
open Classical in
theorem touchCount_straight_le {j : ℕ} (D : Finset (F.Site j)) (x : F.Site j) (st : PathStep) (m N : ℕ)
    (hm : m < F.period j st.1) (hN : (D.image fun z => z st.1).card ≤ N) :
    touchCount D x (List.replicate m st) ≤ 2 * N := by
  let f : F.Site j → ℕ → ℕ := fun x r => if x + r • stepDisplacement j st ∈ D then 1 else 0
  have h1 : ∀ m x, touchCount D x (List.replicate m st) ≤
      ∑ r ∈ Finset.range m, (f x r + f x (r + 1)) := by
    intro m
    induction m with
    | zero =>
      intro x
      simp [touchCount]
    | succ m ih =>
      intro x
      rw [List.replicate_succ]
      simp only [touchCount]
      have a1 := ih (x + stepDisplacement j st)
      have e : ∀ r, f (x + stepDisplacement j st) r = f x (r + 1) := by
        intro r
        simp only [f]
        have : x + stepDisplacement j st + r • stepDisplacement j st =
            x + (r + 1) • stepDisplacement j st := by
          rw [add_smul, one_smul]
          abel
        rw [this]
      simp only [e] at a1
      rw [Finset.sum_range_succ']
      have a2 : (if x ∈ D ∨ x + stepDisplacement j st ∈ D then 1 else 0) ≤ f x 0 + f x (0 + 1) := by
        simp only [f, zero_smul, add_zero, zero_add, one_smul]
        split_ifs <;> simp_all
      omega
  have h2 : ∑ r ∈ Finset.range m, (f x r + f x (r + 1)) ≤ 2 * ∑ r ∈ Finset.range (m + 1), f x r := by
    rw [Finset.sum_add_distrib, two_mul]
    refine add_le_add ?_ ?_
    · rw [Finset.sum_range_succ]
      omega
    · rw [Finset.sum_range_succ']
      omega
  have h3 : ∑ r ∈ Finset.range (m + 1), f x r ≤ N := by
    have e : ∑ r ∈ Finset.range (m + 1), f x r =
        ((Finset.range (m + 1)).filter fun r => x + r • stepDisplacement j st ∈ D).card := by
      simp only [f, Finset.card_filter]
    rw [e]
    refine le_trans ?_ hN
    refine Finset.card_le_card_of_injOn (fun r => (x + r • stepDisplacement j st : F.Site j) st.1) ?_ ?_
    · intro r hr
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hr
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, hr.2, rfl⟩)
    · intro r hr r' hr' he
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hr hr'
      obtain ⟨d, b⟩ := st
      simp only at hm he
      have he2 : ((r • stepDisplacement j (d, b) : F.Site j) d) =
          ((r' • stepDisplacement j (d, b) : F.Site j) d) := by
        have : (x d + (r • stepDisplacement j (d, b) : F.Site j) d) =
            (x d + (r' • stepDisplacement j (d, b) : F.Site j) d) := he
        exact add_left_cancel this
      simp only [Pi.smul_apply, nsmul_eq_mul] at he2
      have hu : (stepDisplacement j (d, b) : F.Site j) d = 1 ∨
          (stepDisplacement j (d, b) : F.Site j) d = -1 := by
        cases b
        · right
          simp [stepDisplacement, unitStep_apply_self]
        · left
          simp [stepDisplacement, unitStep_apply_self]
      have hc : (r : ZMod (F.period j d)) = r' := by
        rcases hu with hu | hu
        · rw [hu, mul_one, mul_one] at he2
          exact he2
        · rw [hu, mul_neg, mul_neg, mul_one, mul_one] at he2
          exact neg_injective he2
      exact natCast_inj_of_lt hc (by omega) (by omega)
  have := h1 m x
  omega
theorem touchCount_axisPath_le {j : ℕ} (D : Finset (F.Site j)) (x : F.Site j) (h : Fin 4 → ℤ)
    (π : Equiv.Perm (Fin 4)) (N : ℕ)
    (hm : ∀ k, (h k).natAbs < F.period j k) (hN : ∀ k, (D.image fun z => z k).card ≤ N) :
    touchCount D x (axisPath h π) ≤ 8 * N := by
  have e : axisPath h π =
      List.replicate (h (π 0)).natAbs (π 0, decide (0 ≤ h (π 0))) ++
      (List.replicate (h (π 1)).natAbs (π 1, decide (0 ≤ h (π 1))) ++
      (List.replicate (h (π 2)).natAbs (π 2, decide (0 ≤ h (π 2))) ++
      (List.replicate (h (π 3)).natAbs (π 3, decide (0 ≤ h (π 3))) ++ []))) := by
    simp [axisPath, List.finRange_succ]
  rw [e]
  simp only [touchCount_append]
  have t : ∀ (k : Fin 4) (z : F.Site j),
      touchCount D z (List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))) ≤ 2 * N :=
    fun k z => touchCount_straight_le D z _ _ N (hm _) (hN _)
  have t0 := t 0 x
  have t1 := t 1 (x + pathDisplacement j (List.replicate (h (π 0)).natAbs (π 0, decide (0 ≤ h (π 0)))))
  have t2 := t 2 (x + pathDisplacement j (List.replicate (h (π 0)).natAbs (π 0, decide (0 ≤ h (π 0)))) +
    pathDisplacement j (List.replicate (h (π 1)).natAbs (π 1, decide (0 ≤ h (π 1)))))
  have t3 := t 3 (x + pathDisplacement j (List.replicate (h (π 0)).natAbs (π 0, decide (0 ≤ h (π 0)))) +
    pathDisplacement j (List.replicate (h (π 1)).natAbs (π 1, decide (0 ≤ h (π 1)))) +
    pathDisplacement j (List.replicate (h (π 2)).natAbs (π 2, decide (0 ≤ h (π 2)))))
  simp only [touchCount, add_zero]
  omega
theorem card_centredCube {L : ℕ} (hL : Odd L) : (centredCube L).card = L ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
open Classical in
theorem card_offsets_le {L : ℕ} (hL : Odd L) (j : ℕ) (hper : ∀ k, L ≤ F.period j k) (base : F.Site j)
    (i : Fin 4) (A : (k : Fin 4) → Finset (ZMod (F.period j k))) (N : ℕ) (hA : ∀ k, (A k).card ≤ N) :
    ((centredCube L).filter fun ξ => ∀ k, k ≠ i → (base + siteOfCoords j ξ : F.Site j) k ∈ A k).card ≤
      L * N ^ 3 := by
  obtain ⟨q, hq⟩ := hL
  have hq2 : ((L : ℤ) - 1) / 2 = q := by
    rw [hq]
    push_cast
    omega
  let P : (k : Fin 4) → Finset (ZMod (F.period j k)) := fun k =>
    (Finset.Icc (-(q : ℤ)) q).image fun c => base k + ((c : ℤ) : ZMod (F.period j k))
  have hP : ∀ k, (P k).card ≤ L := by
    intro k
    refine Finset.card_image_le.trans ?_
    simp only [Int.card_Icc]
    omega
  let B : (k : Fin 4) → Finset (ZMod (F.period j k)) := fun k => if k = i then P k else A k
  have hcard : (Fintype.piFinset B).card ≤ L * N ^ 3 := by
    rw [Fintype.card_piFinset]
    have hb : ∀ k, (B k).card ≤ if k = i then L else N := by
      intro k
      simp only [B]
      split_ifs
      · exact hP k
      · exact hA k
    calc ∏ k, (B k).card ≤ ∏ k, (if k = i then L else N) := Finset.prod_le_prod' fun k _ => hb k
      _ = L * N ^ 3 := by
        fin_cases i <;> simp [Fin.prod_univ_four] <;> ring
  refine le_trans ?_ hcard
  refine Finset.card_le_card_of_injOn (fun ξ => (base + siteOfCoords j ξ : F.Site j)) ?_ ?_
  · intro ξ hξ
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hξ
    refine Finset.mem_coe.2 (Fintype.mem_piFinset.2 fun k => ?_)
    simp only [B]
    split_ifs with hk
    · refine Finset.mem_image.2 ⟨ξ k, ?_, rfl⟩
      have := Fintype.mem_piFinset.1 hξ.1 k
      rw [hq2] at this
      exact this
    · exact hξ.2 k hk
  · intro ξ hξ ξ' hξ' he
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hξ hξ'
    funext k
    have h1 := congrFun he k
    simp only [Pi.add_apply, add_right_inj, siteOfCoords] at h1
    have a1 := Fintype.mem_piFinset.1 hξ.1 k
    have a2 := Fintype.mem_piFinset.1 hξ'.1 k
    rw [hq2] at a1 a2
    simp only [Finset.mem_Icc] at a1 a2
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
    have h3 : (F.period j k : ℤ) ≥ L := by exact_mod_cast hper k
    have h4 : |ξ' k - ξ k| < (F.period j k : ℤ) := by
      rw [abs_lt]
      rw [hq] at h3
      push_cast at h3
      constructor <;> omega
    have h5 := Int.eq_zero_of_abs_lt_dvd h2 h4
    omega
theorem siteOfCoords_smul_single (j : ℕ) (c : ℤ) (i : Fin 4) :
    siteOfCoords (F := F) j (c • Pi.single i 1) = c • unitStep j i := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_single <;> assumption
theorem refineSite_add_mem_sitesBelow (j : ℕ) (y : F.Site (j + 1)) {o : Fin 4 → ℤ}
    (ho : OffsetInBlock F.blockSide o) :
    refineSite y + siteOfCoords j o ∈ sitesBelow j y := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.refineSite_add_mem_sitesBelow <;> assumption
theorem exists_offset_of_mem_sitesBelow (j : ℕ) (y : F.Site (j + 1)) {x : F.Site j}
    (hx : x ∈ sitesBelow j y) :
    ∃ o ∈ centredCube F.blockSide, x = refineSite y + siteOfCoords j o := by
  have e : j + 1 - j = 1 := by omega
  simp only [sitesBelow, e, pow_one] at hx
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.1 hx
  refine ⟨o, ho, ?_⟩
  funext k
  simp [refineSite, siteOfCoords]
theorem add_smul_single_apply (o : Fin 4 → ℤ) (c : ℤ) (i m : Fin 4) :
    (o + c • (Pi.single i 1 : Fin 4 → ℤ)) m = o m + if m = i then c else 0 := by apply _root_.YangMills.Construction.GaugeFixing.add_smul_single_apply <;> assumption
theorem mem_adjacent_blocks (j : ℕ) (hj : j < F.top) (hL : Odd F.blockSide) (y : F.Site (j + 1))
    (i : Fin 4) {o : Fin 4 → ℤ} (ho : OffsetInBlock F.blockSide o) (r : ℕ) (hr : r ≤ F.blockSide) :
    refineSite y + siteOfCoords j o + r • unitStep j i ∈
      sitesBelow j y ∪ sitesBelow j (y + unitStep (j + 1) i) := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.mem_adjacent_blocks <;> assumption
theorem self_mem_pathSites {j : ℕ} (x : F.Site j) (P : List PathStep) : x ∈ pathSites x P := by
  cases P with
  | nil => simp [pathSites]
  | cons st r => simp [pathSites]
theorem mem_pathSites_append {j : ℕ} (P Q : List PathStep) :
    ∀ (x z : F.Site j), z ∈ pathSites x (P ++ Q) →
      z ∈ pathSites x P ∨ z ∈ pathSites (x + pathDisplacement j P) Q := by
  induction P with
  | nil =>
    intro x z hz
    right
    simpa [pathDisplacement] using hz
  | cons st r ih =>
    intro x z hz
    simp only [List.cons_append, pathSites, List.mem_cons] at hz
    rcases hz with rfl | hz
    · left
      simp [pathSites]
    · rcases ih _ _ hz with h | h
      · left
        simp only [pathSites, List.mem_cons]
        exact Or.inr h
      · right
        have : x + stepDisplacement j st + pathDisplacement j r = x + pathDisplacement j (st :: r) := by
          simp [pathDisplacement, add_assoc]
        rwa [this] at h
theorem mem_pathSites_replicate {j : ℕ} (st : PathStep) (m : ℕ) :
    ∀ (x z : F.Site j), z ∈ pathSites x (List.replicate m st) →
      ∃ r ≤ m, z = x + r • stepDisplacement j st := by
  induction m with
  | zero =>
    intro x z hz
    refine ⟨0, le_rfl, ?_⟩
    simpa [pathSites] using hz
  | succ m ih =>
    intro x z hz
    rw [List.replicate_succ] at hz
    simp only [pathSites, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ⟨0, Nat.zero_le _, by simp⟩
    · obtain ⟨r, hr, rfl⟩ := ih _ _ hz
      refine ⟨r + 1, by omega, ?_⟩
      rw [add_smul, one_smul]
      abel
open Classical in
theorem touchCount_eq_zero {j : ℕ} (D : Finset (F.Site j)) (P : List PathStep) :
    ∀ x, (∀ z ∈ pathSites x P, z ∉ D) → touchCount D x P = 0 := by
  induction P with
  | nil =>
    intro x _
    simp [touchCount]
  | cons st r ih =>
    intro x h
    simp only [touchCount]
    have h0 : x ∉ D := h x (by simp [pathSites])
    have h1 : ∀ z ∈ pathSites (x + stepDisplacement j st) r, z ∉ D := fun z hz => h z (by
      simp only [pathSites, List.mem_cons]
      exact Or.inr hz)
    have h2 : x + stepDisplacement j st ∉ D := h1 _ (self_mem_pathSites _ _)
    rw [ih _ h1]
    simp [h0, h2]
def partialOffset (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : ℕ) : Fin 4 → ℤ :=
  fun m => if ((π.symm m : Fin 4) : ℕ) < k then h m else 0
theorem partialOffset_zero (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) : partialOffset h π 0 = 0 := by apply _root_.YangMills.Construction.GaugeFixing.partialOffset_zero <;> assumption
theorem partialOffset_succ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : Fin 4) :
    partialOffset h π ((k : ℕ) + 1) = partialOffset h π k + h (π k) • Pi.single (π k) 1 := by apply _root_.YangMills.Construction.GaugeFixing.partialOffset_succ <;> assumption
def axisPathSegment (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : Fin 4) : List PathStep :=
  List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))
theorem axisPath_eq_segments (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    axisPath h π = axisPathSegment h π 0 ++ (axisPathSegment h π 1 ++
      (axisPathSegment h π 2 ++ (axisPathSegment h π 3 ++ []))) := by apply _root_.YangMills.Construction.GaugeFixing.axisPath_eq_append <;> assumption
theorem segment_endpoint (j : ℕ) (x : F.Site j) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (k : Fin 4) :
    x + siteOfCoords j (partialOffset h π k) + pathDisplacement j (axisPathSegment h π k) =
      x + siteOfCoords j (partialOffset h π ((k : ℕ) + 1)) := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.add_axisPathFlow <;> assumption
theorem axisPath_sites_mem_sitesBelow (j : ℕ) (y : F.Site (j + 1)) {o o' : Fin 4 → ℤ}
    (ho : OffsetInBlock F.blockSide o) (ho' : OffsetInBlock F.blockSide o') (π : Equiv.Perm (Fin 4)) :
    ∀ z ∈ pathSites (refineSite y + siteOfCoords j o) (axisPath (o' - o) π), z ∈ sitesBelow j y := by
  set h := o' - o with hh
  let q : ℕ → Fin 4 → ℤ := fun k => o + partialOffset h π k
  let start : ℕ → F.Site j := fun k => refineSite y + siteOfCoords j (q k)
  have hqb : ∀ k m, q k m = o m ∨ q k m = o' m := by
    intro k m
    simp only [q, partialOffset, Pi.add_apply, hh, Pi.sub_apply]
    by_cases h2 : (((π.symm m : Fin 4) : ℕ)) < k
    · right
      simp [h2]
    · left
      simp [h2]
  have hqi : ∀ k, OffsetInBlock F.blockSide (q k) := by
    intro k m
    rcases hqb k m with h' | h'
    · rw [h']
      exact ho m
    · rw [h']
      exact ho' m
  have piece : ∀ (k : Fin 4), ∀ z ∈ pathSites (start k) (axisPathSegment h π k), z ∈ sitesBelow j y := by
    intro k z hz
    obtain ⟨r, hr, rfl⟩ := mem_pathSites_replicate _ _ _ _ hz
    set d := π k with hd
    have hq0 : q k d = o d := by
      have : ¬ (((π.symm d : Fin 4) : ℕ)) < k := by
        simp [hd]
      simp [q, partialOffset, this]
    have hsg : r • stepDisplacement j (d, decide (0 ≤ h d)) =
        siteOfCoords (F := F) j ((if 0 ≤ h d then (r : ℤ) else -(r : ℤ)) • Pi.single d 1) := by
      rw [siteOfCoords_smul_single]
      by_cases hc : 0 ≤ h d
      · simp [stepDisplacement, hc, natCast_zsmul]
      · simp [stepDisplacement, hc, natCast_zsmul]
    have hz2 : start k + r • stepDisplacement j (d, decide (0 ≤ h d)) =
        refineSite y + siteOfCoords j (q k + (if 0 ≤ h d then (r : ℤ) else -(r : ℤ)) • Pi.single d 1) := by
      rw [hsg, siteOfCoords_add, add_assoc]
    rw [hz2]
    refine refineSite_add_mem_sitesBelow j y ?_
    intro m
    rw [add_smul_single_apply]
    by_cases hm : m = d
    · rw [hm]
      have hv : h d = o' d - o d := rfl
      have a1 := abs_le.1 (ho d)
      have a2 := abs_le.1 (ho' d)
      simp only [if_true]
      rw [hq0, abs_le]
      by_cases hc : 0 ≤ h d
      · simp only [hc, if_true]
        omega
      · simp only [hc, if_false]
        omega
    · simp only [hm, if_false, add_zero]
      exact hqi k m
  have next : ∀ k : Fin 4, start k + pathDisplacement j (axisPathSegment h π k) = start ((k : ℕ) + 1) := by
    intro k
    have := segment_endpoint j (refineSite y + siteOfCoords j o) h π k
    simp only [start, q, siteOfCoords_add, add_assoc] at this ⊢
    exact this
  have s0 : refineSite y + siteOfCoords j o = start 0 := by
    simp [start, q, partialOffset_zero, siteOfCoords_zero]
  intro z hz
  rw [axisPath_eq_segments, s0] at hz
  rcases mem_pathSites_append _ _ _ _ hz with h0 | hz
  · exact piece 0 z h0
  have n0 : start 0 + pathDisplacement j (axisPathSegment h π 0) = start 1 := next 0
  rw [n0] at hz
  rcases mem_pathSites_append _ _ _ _ hz with h1 | hz
  · exact piece 1 z h1
  have n1 : start 1 + pathDisplacement j (axisPathSegment h π 1) = start 2 := next 1
  rw [n1] at hz
  rcases mem_pathSites_append _ _ _ _ hz with h2 | hz
  · exact piece 2 z h2
  have n2 : start 2 + pathDisplacement j (axisPathSegment h π 2) = start 3 := next 2
  rw [n2] at hz
  rcases mem_pathSites_append _ _ _ _ hz with h3 | hz
  · exact piece 3 z h3
  have n3 : start 3 + pathDisplacement j (axisPathSegment h π 3) = start 4 := next 3
  rw [n3] at hz
  have hz4 : z = start 4 := by simpa [pathSites] using hz
  rw [hz4]
  exact refineSite_add_mem_sitesBelow j y (hqi 4)
end PathHolonomy
end YangMills.Construction
end
