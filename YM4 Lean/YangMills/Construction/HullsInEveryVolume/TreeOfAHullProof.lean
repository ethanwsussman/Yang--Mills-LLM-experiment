import YangMills.Construction.FourPointCondition.LawsAtALevelOfTheWindowProof
import YangMills.Construction.HullsInEveryVolume.OneStepDownFromAHull
import YangMills.Construction.HullsInEveryVolume.HullDefs
import Mathlib
import YangMills.Construction.SixteenPointsOnASmallTorus.LevelsOfARadiusProof
set_option autoImplicit false

noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
open TorusFields TorusLumps WeightedResponses
def HullSiteTreeExists : Prop :=
  EventuallyInParameters fun Tb _ y => ∀ (g β : ℝ) (K m : ℕ) (T : StageTower (Tb.stepParameters y)) (u n : ℕ) [NeZero n],
    HullChainAtLevel Tb y g β K m T u n →
    ∀ (w : MarkedSample (Tb.stepParameters y) u n) (z : TorusSite n), z ∈ hullSet T u n w →
      ∃ tr : SiteTree (Tb.stepParameters y).side u n, tr.root = z ∧
        tr.Embeds T (treeBranching (Tb.stepParameters y).side) w ∧
        tr.leafWeight (treeBranching (Tb.stepParameters y).side) = 1 ∧
        (∃ j ≤ u, levelWeight j * (treeBranching (Tb.stepParameters y).side : ℝ) ^ j ≤ (tr.leavesAtDepth j : ℝ)) ∧
        ∀ j ≤ u, (tr.leafSites j).card = tr.leavesAtDepth j ∧
          Separated (30 * stageRange T (u - j)) (tr.leafSites j)
end YangMills.Construction.HullTrees
end

noncomputable section
namespace YangMills.Construction.HullTrees
open TorusLumps TorusFields TorusBalls WeightedResponses RenormalizationStepParameters StepReturn
variable {ℓ : StepParameters}
private def ancestorSite (L : ℕ) : (j n : ℕ) → TorusSite (fineSide L j n) → TorusSite n
  | 0, _, a => a
  | j + 1, n, a => parentBlock L (ancestorSite L j (n * L) a)
private theorem mem_leafSites_leaf {L u n : ℕ} {y : TorusSite n} {a : TorusSite (fineSide L 0 n)}
    (h : a ∈ (SiteTree.leaf y : SiteTree L u n).leafSites 0) : a = y :=
  Finset.mem_singleton.1 h
private theorem exists_mem_leafSites_of_mem_node {L u n k' j : ℕ} {y : TorusSite n}
    {kids : Fin k' → SiteTree L u (n * L)}
    {a : TorusSite (fineSide L (j + 1) n)} (h : a ∈ (SiteTree.node y k' kids).leafSites (j + 1)) :
    ∃ i, a ∈ (kids i).leafSites j := by
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 h
  exact ⟨i, hi⟩
private theorem supDist_ancestorSite_le (L : ℕ) [NeZero L] (hL : 2 ≤ L) (j : ℕ) :
    ∀ (n : ℕ) [NeZero n] (a b : TorusSite (fineSide L j n)),
      _root_.YangMills.Construction.TorusFields.supDist (ancestorSite L j n a) (ancestorSite L j n b) ≤ _root_.YangMills.Construction.TorusFields.supDist a b / L ^ j + 2 := by
  induction j with
  | zero =>
    intro n _ a b
    show _root_.YangMills.Construction.TorusFields.supDist a b ≤ _root_.YangMills.Construction.TorusFields.supDist a b / L ^ 0 + 2
    simp
  | succ j ih =>
    intro n _ a b
    have h0 := ih (n * L) a b
    have h1 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one L (ancestorSite L j (n * L) a)
      (ancestorSite L j (n * L) b)
    change _root_.YangMills.Construction.TorusFields.supDist (parentBlock L (ancestorSite L j (n * L) a))
        (parentBlock L (ancestorSite L j (n * L) b)) ≤
      @_root_.YangMills.Construction.TorusFields.supDist (fineSide L j (n * L)) a b / L ^ (j + 1) + 2
    have h2 : @_root_.YangMills.Construction.TorusFields.supDist (fineSide L j (n * L)) a b / L ^ (j + 1) =
        @_root_.YangMills.Construction.TorusFields.supDist (fineSide L j (n * L)) a b / L ^ j / L := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    rw [h2]
    set A := @_root_.YangMills.Construction.TorusFields.supDist (fineSide L j (n * L)) a b / L ^ j
    have h3 : _root_.YangMills.Construction.TorusFields.supDist (ancestorSite L j (n * L) a) (ancestorSite L j (n * L) b) / L ≤ (A + L) / L :=
      Nat.div_le_div_right (by omega)
    have h4 : (A + L) / L = A / L + 1 := Nat.add_div_right _ (by omega)
    omega
private theorem stageRange_sub_le {T : StageTower ℓ} {K : ℕ}
    (h2 : ∀ v < K, stageRange T v ≤ 2 * stageRange T (v + 1)) (u : ℕ) (hu : u ≤ K)
    (j : ℕ) (hj : j ≤ u) : stageRange T (u - j) ≤ 2 ^ j * stageRange T u := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h3 := ih (by omega)
    have h4 := h2 (u - (j + 1)) (by omega)
    have e : u - (j + 1) + 1 = u - j := by omega
    rw [e] at h4
    rw [pow_succ]
    nlinarith
private theorem leafSites_near_root {T : StageTower ℓ} {K : ℕ} (hL : 20 ≤ ℓ.side)
    (h4 : ∀ v ≤ K, 4 ≤ stageRange T v)
    (h2 : ∀ v < K, stageRange T v ≤ 2 * stageRange T (v + 1)) (k : ℕ) {u n : ℕ}
    (tr : SiteTree ℓ.side u n) :
    ∀ [NeZero n] (w : MarkedSample ℓ u n), tr.Embeds T k w → u ≤ K → ∀ (j : ℕ), ∀ a ∈ tr.leafSites j,
      2 * _root_.YangMills.Construction.TorusFields.supDist (ancestorSite ℓ.side j n a) tr.root ≤ 5 * stageRange T u := by
  induction tr with
  | @leaf u n y =>
    intro _ w _ _ j a ha
    cases j with
    | zero =>
      have e : a = y := mem_leafSites_leaf ha
      subst e
      show 2 * _root_.YangMills.Construction.TorusFields.supDist a a ≤ _
      rw [_root_.YangMills.Construction.TorusFields.supDist_self]
      simp
    | succ j => simp [SiteTree.leafSites] at ha
  | @node u n y k' kids ih =>
    intro _ w hh hu j a ha
    cases j with
    | zero => simp [SiteTree.leafSites] at ha
    | succ j =>
      obtain ⟨-, -, hbox, -, hkids⟩ := hh
      obtain ⟨i, hi⟩ := exists_mem_leafSites_of_mem_node ha
      have h5 := ih i w.1 (hkids i) (by omega) j a hi
      obtain ⟨y', hy', hd⟩ := (mem_thickening _ _ _).1 (hbox i)
      obtain rfl : y' = y := by simpa using hy'
      have h6 := _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one ℓ.side
        (ancestorSite ℓ.side j (n * ℓ.side) a) (kids i).root
      have h7 := _root_.YangMills.Construction.TorusFields.supDist_triangle (parentBlock ℓ.side (ancestorSite ℓ.side j (n * ℓ.side) a))
        (parentBlock ℓ.side (kids i).root) y'
      have h8 := h2 u (by omega)
      have h9 := h4 (u + 1) hu
      set d := _root_.YangMills.Construction.TorusFields.supDist (ancestorSite ℓ.side j (n * ℓ.side) a) (kids i).root
      have h10 : (d / ℓ.side) * 20 ≤ d :=
        (Nat.mul_le_mul_left _ hL).trans (Nat.div_mul_le_self d ℓ.side)
      show 2 * _root_.YangMills.Construction.TorusFields.supDist (parentBlock ℓ.side (ancestorSite ℓ.side j (n * ℓ.side) a)) y' ≤
        5 * stageRange T (u + 1)
      omega
private theorem leafSites_separated_of_roots {T : StageTower ℓ} {K : ℕ} (hL : 20 ≤ ℓ.side)
    (h4 : ∀ v ≤ K, 4 ≤ stageRange T v)
    (h2 : ∀ v < K, stageRange T v ≤ 2 * stageRange T (v + 1)) (k : ℕ) {u n : ℕ} [NeZero n]
    (c c' : SiteTree ℓ.side u n)
    (w : MarkedSample ℓ u n) (hc : c.Embeds T k w) (hc' : c'.Embeds T k w) (hu : u ≤ K)
    (hd : 40 * stageRange T u ≤ _root_.YangMills.Construction.TorusFields.supDist c.root c'.root) (j : ℕ) (hj : j ≤ u)
    (a : TorusSite (fineSide ℓ.side j n))
    (ha : a ∈ c.leafSites j) (b : TorusSite (fineSide ℓ.side j n)) (hb : b ∈ c'.leafSites j) :
    30 * stageRange T (u - j) ≤ _root_.YangMills.Construction.TorusFields.supDist a b := by
  have h5 := leafSites_near_root hL h4 h2 k c w hc hu j a ha
  have h6 := leafSites_near_root hL h4 h2 k c' w hc' hu j b hb
  have h7 := supDist_ancestorSite_le ℓ.side (by omega) j n a b
  have h8 := _root_.YangMills.Construction.TorusFields.supDist_triangle c.root (ancestorSite ℓ.side j n a) c'.root
  have h9 := _root_.YangMills.Construction.TorusFields.supDist_triangle (ancestorSite ℓ.side j n a) (ancestorSite ℓ.side j n b) c'.root
  have h10 := _root_.YangMills.Construction.TorusFields.supDist_comm c.root (ancestorSite ℓ.side j n a)
  have h11 := _root_.YangMills.Construction.TorusFields.supDist_comm c'.root (ancestorSite ℓ.side j n b)
  have h12 := h4 u hu
  have h13 : 30 * stageRange T u ≤ _root_.YangMills.Construction.TorusFields.supDist a b / ℓ.side ^ j := by omega
  have hpos : 0 < ℓ.side ^ j := Nat.pow_pos (by omega)
  have h14 : 30 * stageRange T u * ℓ.side ^ j ≤ _root_.YangMills.Construction.TorusFields.supDist a b := (Nat.le_div_iff_mul_le hpos).1 h13
  have h15 : (2 : ℕ) ^ j ≤ ℓ.side ^ j := Nat.pow_le_pow_left (by omega) j
  have h16 := stageRange_sub_le h2 u hu j hj
  calc 30 * stageRange T (u - j) ≤ 30 * (2 ^ j * stageRange T u) := by omega
    _ ≤ 30 * (ℓ.side ^ j * stageRange T u) := by gcongr
    _ = 30 * stageRange T u * ℓ.side ^ j := by ring
    _ ≤ _root_.YangMills.Construction.TorusFields.supDist a b := h14
private theorem leafSites_card_and_separated {T : StageTower ℓ} {K : ℕ} (hL : 20 ≤ ℓ.side)
    (h4 : ∀ v ≤ K, 4 ≤ stageRange T v)
    (h2 : ∀ v < K, stageRange T v ≤ 2 * stageRange T (v + 1)) (k : ℕ) {u n : ℕ}
    (tr : SiteTree ℓ.side u n) :
    ∀ [NeZero n] (w : MarkedSample ℓ u n), tr.Embeds T k w → u ≤ K → ∀ j ≤ u,
      (tr.leafSites j).card = tr.leavesAtDepth j ∧
        Separated (30 * stageRange T (u - j)) (tr.leafSites j) := by
  induction tr with
  | @leaf u n y =>
    intro _ w _ _ j _
    cases j with
    | zero =>
      refine ⟨Finset.card_singleton y, ?_⟩
      intro a ha b hb hab
      exact absurd ((mem_leafSites_leaf ha).trans (mem_leafSites_leaf hb).symm) hab
    | succ j =>
      refine ⟨by simp [SiteTree.leafSites, SiteTree.leavesAtDepth], ?_⟩
      intro a ha
      simp [SiteTree.leafSites] at ha
  | @node u n y k' kids ih =>
    intro _ w hh hu j hj
    cases j with
    | zero =>
      refine ⟨by simp [SiteTree.leafSites, SiteTree.leavesAtDepth], ?_⟩
      intro a ha
      simp [SiteTree.leafSites] at ha
    | succ j =>
      obtain ⟨-, -, -, hap, hkids⟩ := hh
      have hj' : j ≤ u := by omega
      have hu' : u ≤ K := by omega
      have hcross : ∀ i i', i ≠ i' → ∀ a ∈ (kids i).leafSites j, ∀ b ∈ (kids i').leafSites j,
          30 * stageRange T (u - j) ≤ _root_.YangMills.Construction.TorusFields.supDist a b := fun i i' hi a ha b hb =>
        leafSites_separated_of_roots hL h4 h2 k (kids i) (kids i') w.1 (hkids i) (hkids i') hu'
          (hap i i' hi) j hj' a ha b hb
      have hr : 0 < stageRange T (u - j) := by
        have := h4 (u - j) (by omega)
        omega
      constructor
      · classical
        have hdis : ∀ i ∈ (Finset.univ : Finset (Fin k')), ∀ i' ∈ (Finset.univ : Finset (Fin k')),
            i ≠ i' → Disjoint ((kids i).leafSites j) ((kids i').leafSites j) := by
          intro i _ i' _ hi
          rw [Finset.disjoint_left]
          intro a ha ha'
          have h5 := hcross i i' hi a ha a ha'
          rw [_root_.YangMills.Construction.TorusFields.supDist_self] at h5
          omega
        have e : (SiteTree.node y k' kids).leafSites (j + 1) =
            Finset.univ.biUnion fun i => (kids i).leafSites j := by
          simp only [SiteTree.leafSites]
          congr
        have e2 : ((SiteTree.node y k' kids).leafSites (j + 1)).card =
            ∑ i, ((kids i).leafSites j).card := by
          rw [e]
          exact Finset.card_biUnion hdis
        rw [e2]
        simp only [SiteTree.leavesAtDepth]
        exact Finset.sum_congr rfl fun i _ => (ih i w.1 (hkids i) hu' j hj').1
      · intro a ha b hb hab
        obtain ⟨i, hi⟩ := exists_mem_leafSites_of_mem_node ha
        obtain ⟨i', hi'⟩ := exists_mem_leafSites_of_mem_node hb
        have e : u + 1 - (j + 1) = u - j := by omega
        rw [e]
        by_cases hii : i = i'
        · subst hii
          exact (ih i w.1 (hkids i) hu' j hj').2 a hi b hi' hab
        · exact hcross i i' hii a hi b hi'
private theorem leafWeight_eq_sum {L : ℕ} (k : ℕ) {u n : ℕ} (tr : SiteTree L u n) :
    tr.leafWeight k = ∑ j ∈ Finset.range (u + 1), (tr.leavesAtDepth j : ℝ) / (k : ℝ) ^ j := by
  induction tr with
  | @leaf u n y =>
    rw [Finset.sum_range_succ']
    simp [SiteTree.leafWeight, SiteTree.leavesAtDepth]
  | @node u n y k' kids ih =>
    rw [Finset.sum_range_succ']
    simp only [SiteTree.leafWeight, SiteTree.leavesAtDepth, ih]
    rw [Finset.sum_comm, Finset.sum_div]
    simp only [Nat.cast_zero, zero_div, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.cast_sum, Finset.sum_div, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ, div_div]
private theorem sum_inv_sq_le (u : ℕ) :
    ∑ j ∈ Finset.range (u + 1), 1 / ((j : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((u : ℝ) + 1) := by
  induction u with
  | zero => norm_num
  | succ u ih =>
    rw [Finset.sum_range_succ]
    have hp : (0 : ℝ) < (u : ℝ) + 1 := by positivity
    have h : 1 / (((u + 1 : ℕ) : ℝ) + 1) ^ 2 ≤ 1 / ((u : ℝ) + 1) - 1 / (((u + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      rw [div_sub_div _ _ hp.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
private theorem sum_levelWeight_le_one (u : ℕ) : ∑ j ∈ Finset.range (u + 1), levelWeight j ≤ 1 := by
  have h1 := sum_inv_sq_le u
  have h2 : (0 : ℝ) ≤ 1 / ((u : ℝ) + 1) := by positivity
  have h3 : ∑ j ∈ Finset.range (u + 1), levelWeight j =
      3 / Real.pi ^ 2 * ∑ j ∈ Finset.range (u + 1), 1 / ((j : ℝ) + 1) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [levelWeight]
    ring
  have h4 : (9 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have h5 : 3 / Real.pi ^ 2 ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have h6 : (0 : ℝ) ≤ ∑ j ∈ Finset.range (u + 1), 1 / ((j : ℝ) + 1) ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  rw [h3]
  nlinarith
abbrev _root_.YangMills.SharedProofs.p12137 := @sum_levelWeight_le_one
private theorem exists_depth_many_leaves {L : ℕ} {k : ℕ} (hk : 0 < k) {u n : ℕ} (tr : SiteTree L u n)
    (hm : tr.leafWeight k = 1) :
    ∃ j ≤ u, levelWeight j * (k : ℝ) ^ j ≤ (tr.leavesAtDepth j : ℝ) := by
  by_contra hno
  push Not at hno
  have h1 : ∑ j ∈ Finset.range (u + 1), (tr.leavesAtDepth j : ℝ) / (k : ℝ) ^ j <
      ∑ j ∈ Finset.range (u + 1), levelWeight j := by
    refine Finset.sum_lt_sum_of_nonempty (by simp) fun j hj => ?_
    rw [div_lt_iff₀ (by positivity)]
    exact hno j (by simpa [Nat.lt_succ_iff] using hj)
  rw [← leafWeight_eq_sum, hm] at h1
  linarith [sum_levelWeight_le_one u]
private theorem exists_siteTree (T : StageTower ℓ) {k : ℕ} (hk : 0 < k) (P : ℕ → ℕ → Prop)
    (hP : ∀ u n, P (u + 1) n → P u (n * ℓ.side))
    (hOne : ∀ (u n : ℕ) [NeZero n], P u n → ∀ (w : MarkedSample ℓ u n) (z : TorusSite n),
      z ∈ hullSet T u n w → IsUnit T u n w z ∨ HasSeparatedChildren T k u n w z) (u : ℕ) :
    ∀ (n : ℕ) [NeZero n], P u n → ∀ (w : MarkedSample ℓ u n) (z : TorusSite n), z ∈ hullSet T u n w →
      ∃ tr : SiteTree ℓ.side u n, tr.root = z ∧ tr.Embeds T k w ∧ tr.leafWeight k = 1 := by
  have hleaf : ∀ (u n : ℕ) [NeZero n] (w : MarkedSample ℓ u n) (z : TorusSite n), z ∈ hullSet T u n w →
      IsUnit T u n w z →
      ∃ tr : SiteTree ℓ.side u n, tr.root = z ∧ tr.Embeds T k w ∧ tr.leafWeight k = 1 := by
    intro u n _ w z hz hU
    refine ⟨.leaf z, rfl, ?_, rfl⟩
    cases u with
    | zero => exact ⟨hz, hU⟩
    | succ u => exact ⟨hz, hU⟩
  induction u with
  | zero =>
    intro n _ hp w z hz
    rcases hOne 0 n hp w z hz with hU | hC
    · exact hleaf 0 n w z hz hU
    · exact False.elim hC
  | succ u ih =>
    intro n _ hp w z hz
    rcases hOne (u + 1) n hp w z hz with hU | hC
    · exact hleaf (u + 1) n w z hz hU
    · obtain ⟨S, hS, hsub, hblk, hap⟩ := hC
      let e : Fin k ≃ S := (S.equivFinOfCardEq hS).symm
      have hkid : ∀ i : Fin k, ∃ t : SiteTree ℓ.side u (n * ℓ.side),
          t.root = (e i : TorusSite (n * ℓ.side)) ∧ t.Embeds T k w.1 ∧ t.leafWeight k = 1 := fun i =>
        ih (n * ℓ.side) (hP u n hp) w.1 (e i) (hsub (e i).2)
      choose t ht1 ht2 ht3 using hkid
      have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      refine ⟨.node z k t, rfl, ?_, ?_⟩
      · show z ∈ hullSet T (u + 1) n w ∧ k = k ∧
          (∀ i, parentBlock ℓ.side (t i).root ∈ box z (2 * stageRange T (u + 1))) ∧
          (∀ i i', i ≠ i' → 40 * stageRange T u ≤ _root_.YangMills.Construction.TorusFields.supDist (t i).root (t i').root) ∧
          ∀ i, SiteTree.Embeds T k (t i) w.1
        refine ⟨hz, rfl, fun i => ?_, fun i i' hi => ?_, ht2⟩
        · rw [ht1]
          exact hblk _ (e i).2
        · rw [ht1, ht1]
          refine hap _ (e i).2 _ (e i').2 fun h => hi ?_
          exact e.injective (Subtype.ext h)
      · show (∑ i : Fin k, SiteTree.leafWeight k (t i)) / (k : ℝ) = 1
        simp only [ht3]
        simp [hk']
private theorem hullChainAtLevel_down {Tb : ParameterAssignment} {y g β : ℝ} {K m : ℕ}
    {T : StageTower (Tb.stepParameters y)} (u n : ℕ)
    (h : HullChainAtLevel Tb y g β K m T (u + 1) n) :
    HullChainAtLevel Tb y g β K m T u (n * (Tb.stepParameters y).side) := by
  refine ⟨h.chain, by have := h.le; omega, ?_⟩
  have e : K - u = K - (u + 1) + 1 := by
    have := h.le
    omega
  have h1 := h.side_eq
  show n * Tb.side = torusSideAtLevel Tb.side K m u
  rw [h1]
  simp only [torusSideAtLevel]
  rw [e, fineSide, fineSide_eq, fineSide_eq]
  ring
private theorem abs_couplingFlow_succ_sub_le {ℓ : StepParameters} (hR : ExpansionReturnsAt ℓ) {β : ℝ}
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) (t : ℕ)
    (h : ∀ j ≤ t, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) :
    |(couplingFlow ℓ β (t + 1)).1 - (couplingFlow ℓ β t).1| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p4489 <;> assumption
private theorem four_le_clusterRange {x : ℝ} (hx : (2 : ℝ) ^ 200 ≤ x) : 4 ≤ clusterRange x := by
  have h1 : ((4 : ℝ) ^ 100) ^ ((1 : ℝ) / 100) = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h2 : (4 : ℝ) ≤ x ^ ((1 : ℝ) / 100) := by
    calc (4 : ℝ) = ((4 : ℝ) ^ 100) ^ ((1 : ℝ) / 100) := h1.symm
      _ ≤ x ^ ((1 : ℝ) / 100) :=
        Real.rpow_le_rpow (by norm_num) (le_trans (by norm_num) hx) (by norm_num)
  have h3 : (4 : ℝ) ≤ (clusterRange x : ℝ) := h2.trans (Nat.le_ceil _)
  exact_mod_cast h3
private theorem clusterRange_le_two_mul {x x' : ℝ} (h0 : 0 ≤ x) (h1 : 0 ≤ x') (h : x ≤ 2 * x') :
    clusterRange x ≤ 2 * clusterRange x' := by apply _root_.YangMills.SharedProofs.p21096 <;> assumption
private theorem stageRange_bounds {Tb : ParameterAssignment} {y g β : ℝ} {K m : ℕ}
    {T : StageTower (Tb.stepParameters y)}
    (hD : Tb.Admissible) (hy : (2 : ℝ) ^ 200 ≤ y) (hB : 2 * Tb.B ≤ y)
    (hR : ExpansionReturnsAt (Tb.stepParameters y))
    (hW : ∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β))
    (h : HullChain Tb y g β K m T) :
    (∀ v ≤ K, 4 ≤ stageRange T v) ∧ ∀ v < K, stageRange T v ≤ 2 * stageRange T (v + 1) := by
  have hB1 : (1 : ℝ) ≤ Tb.B := hD.B_ge
  have hfl : y ≤ (g ^ 2)⁻¹ := h.le_inv_sq
  have htop : windowUpper (Tb.stepParameters y) g = (g ^ 2)⁻¹ + 2 * Tb.B := rfl
  have hab : windowUpper (Tb.stepParameters y) g ≤ β := h.upper_le
  have hpass : ∀ k < K, windowUpper (Tb.stepParameters y) g < (couplingFlow (Tb.stepParameters y) β k).1 :=
    h.isFirst.2
  have hyβ : y ≤ β := by linarith
  have h0 := hW β hyβ
  have hlow : ∀ j < K, y ≤ (couplingFlow (Tb.stepParameters y) β j).1 := fun j hj => by
    have := hpass j hj
    linarith
  have hstep : ∀ t < K, |(couplingFlow (Tb.stepParameters y) β (t + 1)).1 -
      (couplingFlow (Tb.stepParameters y) β t).1| ≤ 2 * Tb.B :=
    fun t ht => abs_couplingFlow_succ_sub_le hR h0 t fun j hj => hlow j (by omega)
  have hall : ∀ j ≤ K, y ≤ (couplingFlow (Tb.stepParameters y) β j).1 := by
    intro j hj
    rcases Nat.lt_or_ge j K with hlt | hge
    · exact hlow j hlt
    · obtain rfl : j = K := le_antisymm hj hge
      cases j with
      | zero =>
        show y ≤ β
        exact hyβ
      | succ j =>
        have h1 := (abs_le.1 (hstep j (by omega))).1
        have h2 := hpass j (by omega)
        linarith
  have hx : ∀ j ≤ K, (T.stage j).coupling = (couplingFlow (Tb.stepParameters y) β j).1 :=
    fun j hj => h.follows j (by omega)
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · show 4 ≤ clusterRange (T.stage v).coupling
    rw [hx v hv]
    exact four_le_clusterRange (hy.trans (hall v hv))
  · show clusterRange (T.stage v).coupling ≤ 2 * clusterRange (T.stage (v + 1)).coupling
    rw [hx v hv.le, hx (v + 1) hv]
    have h1 := (abs_le.1 (hstep v hv)).1
    have h2 := hall (v + 1) hv
    have h3 := hall v hv.le
    exact clusterRange_le_two_mul (by linarith) (by linarith) (by linarith)
theorem hullSiteTreeExists_of_unitOrSeparatedChildren (h : UnitOrSeparatedChildren) :
    HullSiteTreeExists := by
  unfold UnitOrSeparatedChildren EventuallyInParameters at h
  unfold HullSiteTreeExists EventuallyInParameters
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, H⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hLo hL Tb hTa hTL hD hC hH hTrt hCd => ?_⟩
  obtain ⟨M, HM⟩ := H L hLo hL Tb hTa hTL hD hC hH hTrt hCd
  refine ⟨M, fun Kr hM h1 h2 hF hS => ?_⟩
  obtain ⟨y₀, Hy⟩ := HM Kr hM h1 h2 hF hS
  refine ⟨max y₀ (max ((2 : ℝ) ^ 200) (2 * Tb.B)), fun y hy hR hW => ?_⟩
  have hy₀ : y₀ ≤ y := (le_max_left _ _).trans hy
  have hy200 : (2 : ℝ) ^ 200 ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hyB : 2 * Tb.B ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hchild := Hy y hy₀ hR hW
  intro g β K m T u n _ hA w z hz
  have hLge : 20 ≤ (Tb.stepParameters y).side := le_trans (by norm_num) hD.L_ge
  have hbr : 0 < treeBranching (Tb.stepParameters y).side := by
    have : 100 ≤ (Tb.stepParameters y).side := le_trans (by norm_num) hD.L_ge
    exact Nat.div_pos this (by norm_num)
  obtain ⟨h4, h2'⟩ := stageRange_bounds hD hy200 hyB hR hW hA.chain
  obtain ⟨tr, hroot, hh, hm⟩ := exists_siteTree T hbr
    (fun u n => HullChainAtLevel Tb y g β K m T u n)
    (fun u n hp => hullChainAtLevel_down u n hp)
    (fun u n _ hp w z hz => hchild g β K m T u n hp w z hz) u n hA w z hz
  refine ⟨tr, hroot, hh, hm, exists_depth_many_leaves hbr tr hm, fun j hj => ?_⟩
  exact leafSites_card_and_separated hLge h4 h2' _ tr w hh hA.le j hj
end YangMills.Construction.HullTrees
end
