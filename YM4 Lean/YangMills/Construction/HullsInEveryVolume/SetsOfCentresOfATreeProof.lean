import YangMills.Construction.CellOfTheFlow.LongClassesAreRareProof
import YangMills.Construction.HullsInEveryVolume.SetsOfCentresOfATree
import YangMills.Construction.ResponseInTheExpansion.RunningCouplingSlope
import YangMills.Construction.ResponseInTheExpansion.TheLocalEventIsLikelyProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
open TorusLumps TorusFields WeightedResponses
section Counting
private theorem card_powerset_filter_card_le_le {α : Type*} (B : Finset α) (a : ℕ) (c : ℝ) (hc : 1 ≤ c)
    (hB : (B.card : ℝ) ≤ a * c) :
    ((B.powerset.filter fun A => A.card ≤ a).card : ℝ) ≤ (Real.exp 1 * c) ^ a := by
  have hc0 : 0 < c := by linarith
  set q : ℝ := c⁻¹ with hq
  have hq0 : 0 < q := inv_pos.mpr hc0
  have hq1 : q ≤ 1 := inv_le_one_of_one_le₀ hc
  have hsum : ∑ s ∈ B.powerset, q ^ s.card * 1 ^ (B.card - s.card) = (q + 1) ^ B.card :=
    Finset.sum_pow_mul_eq_add_pow q 1 B
  have hlow : ((B.powerset.filter fun A => A.card ≤ a).card : ℝ) * q ^ a ≤
      ∑ s ∈ B.powerset, q ^ s.card * 1 ^ (B.card - s.card) := by
    calc ((B.powerset.filter fun A => A.card ≤ a).card : ℝ) * q ^ a
        = ∑ _s ∈ B.powerset.filter (fun A => A.card ≤ a), q ^ a := by simp
      _ ≤ ∑ s ∈ B.powerset.filter (fun A => A.card ≤ a), q ^ s.card * 1 ^ (B.card - s.card) := by
          refine Finset.sum_le_sum fun s hs => ?_
          simp only [one_pow, mul_one]
          exact pow_le_pow_of_le_one hq0.le hq1 (Finset.mem_filter.mp hs).2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
  have hup : (q + 1) ^ B.card ≤ Real.exp 1 ^ a := by
    have h1 : q + 1 ≤ Real.exp q := Real.add_one_le_exp q
    have h2 : (B.card : ℝ) * q ≤ a := by
      calc (B.card : ℝ) * q ≤ (a * c) * q := by gcongr
        _ = a := by rw [hq, mul_assoc, mul_inv_cancel₀ hc0.ne', mul_one]
    calc (q + 1) ^ B.card ≤ Real.exp q ^ B.card := pow_le_pow_left₀ (by positivity) h1 _
      _ = Real.exp ((B.card : ℝ) * q) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (a : ℝ) := Real.exp_le_exp.mpr h2
      _ = Real.exp 1 ^ a := by rw [← Real.exp_nat_mul]; simp
  have hmain : ((B.powerset.filter fun A => A.card ≤ a).card : ℝ) * q ^ a ≤ Real.exp 1 ^ a :=
    hlow.trans (hsum.le.trans hup)
  have hqc : q ^ a * c ^ a = 1 := by rw [← mul_pow, hq, inv_mul_cancel₀ hc0.ne', one_pow]
  rw [mul_pow]
  calc ((B.powerset.filter fun A => A.card ≤ a).card : ℝ)
      = ((B.powerset.filter fun A => A.card ≤ a).card : ℝ) * q ^ a * c ^ a := by
        rw [mul_assoc, hqc, mul_one]
    _ ≤ Real.exp 1 ^ a * c ^ a := by gcongr
private theorem sum_range_pow_succ_le (k : ℕ) (hk : 2 ≤ k) (j : ℕ) :
    ∑ d ∈ Finset.range j, k ^ (d + 1) ≤ 2 * k ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have h1 : 2 * k ^ j ≤ k ^ (j + 1) := by
      rw [pow_succ, mul_comm]
      exact Nat.mul_le_mul_left _ hk
    linarith
private theorem sum_min_pow_le (k N j : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N)
    (hθ : levelWeight j * (k : ℝ) ^ j ≤ N) :
    ((∑ l ∈ Finset.range j, min (k ^ (j - l)) N : ℕ) : ℝ) ≤
      5 * (N : ℝ) * (1 + Real.log ((j : ℝ) + 1)) := by
  have hlog0 : 0 ≤ Real.log ((j : ℝ) + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hrefl : ∑ l ∈ Finset.range j, min (k ^ (j - l)) N =
      ∑ d ∈ Finset.range j, min (k ^ (d + 1)) N := by
    rw [← Finset.sum_range_reflect (fun d => min (k ^ (d + 1)) N) j]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l < j := Finset.mem_range.mp hl
    have : j - 1 - l + 1 = j - l := by omega
    simp only [this]
  rw [hrefl]
  set D := Nat.log k N with hD
  have hD1 : k ^ D ≤ N := Nat.pow_log_le_self k (by omega)
  have hD2 : N < k ^ (D + 1) := Nat.lt_pow_succ_log_self (by omega) N
  rcases le_or_gt j D with hjD | hjD
  · have h1 : ∑ d ∈ Finset.range j, min (k ^ (d + 1)) N ≤ 2 * N := by
      calc ∑ d ∈ Finset.range j, min (k ^ (d + 1)) N
          ≤ ∑ d ∈ Finset.range j, k ^ (d + 1) :=
            Finset.sum_le_sum fun d _ => min_le_left _ _
        _ ≤ 2 * k ^ j := sum_range_pow_succ_le k hk j
        _ ≤ 2 * k ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hjD)
        _ ≤ 2 * N := Nat.mul_le_mul_left _ hD1
    have h2 : ((∑ d ∈ Finset.range j, min (k ^ (d + 1)) N : ℕ) : ℝ) ≤ 2 * N := by exact_mod_cast h1
    nlinarith [mul_nonneg hN0 hlog0]
  · obtain ⟨e, he⟩ : ∃ e, j = D + (e + 1) := ⟨j - D - 1, by omega⟩
    have hsplit : ∑ d ∈ Finset.range j, min (k ^ (d + 1)) N ≤ 2 * N + (e + 1) * N := by
      rw [he, Finset.sum_range_add]
      have h1 : ∑ d ∈ Finset.range D, min (k ^ (d + 1)) N ≤ 2 * N := by
        calc ∑ d ∈ Finset.range D, min (k ^ (d + 1)) N
            ≤ ∑ d ∈ Finset.range D, k ^ (d + 1) :=
              Finset.sum_le_sum fun d _ => min_le_left _ _
          _ ≤ 2 * k ^ D := sum_range_pow_succ_le k hk D
          _ ≤ 2 * N := Nat.mul_le_mul_left _ hD1
      have h2 : ∑ x ∈ Finset.range (e + 1), min (k ^ (D + x + 1)) N ≤ (e + 1) * N := by
        calc ∑ x ∈ Finset.range (e + 1), min (k ^ (D + x + 1)) N
            ≤ ∑ _x ∈ Finset.range (e + 1), N := Finset.sum_le_sum fun d _ => min_le_right _ _
          _ = (e + 1) * N := by simp
      exact Nat.add_le_add h1 h2
    have hsplit' : ((∑ d ∈ Finset.range j, min (k ^ (d + 1)) N : ℕ) : ℝ) ≤ 2 * N + ((e : ℝ) + 1) * N := by
      exact_mod_cast hsplit
    have hpi : Real.pi ^ 2 ≤ 12 := by
      have h1 := Real.pi_lt_d2
      have h2 := Real.pi_pos
      nlinarith
    have hweight : levelWeight j * (k : ℝ) ^ e < 1 := by
      have h1 : levelWeight j * (k : ℝ) ^ j < (k : ℝ) ^ (D + 1) :=
        lt_of_le_of_lt hθ (by exact_mod_cast hD2)
      have h2 : (k : ℝ) ^ j = (k : ℝ) ^ (D + 1) * (k : ℝ) ^ e := by
        rw [he, ← pow_add]
        congr 1
        omega
      rw [h2] at h1
      have h3 : 0 < (k : ℝ) ^ (D + 1) := by positivity
      have h4 : (k : ℝ) ^ (D + 1) * (levelWeight j * (k : ℝ) ^ e) < (k : ℝ) ^ (D + 1) * 1 := by
        calc (k : ℝ) ^ (D + 1) * (levelWeight j * (k : ℝ) ^ e)
            = levelWeight j * ((k : ℝ) ^ (D + 1) * (k : ℝ) ^ e) := by ring
          _ < (k : ℝ) ^ (D + 1) := h1
          _ = (k : ℝ) ^ (D + 1) * 1 := by ring
      exact lt_of_mul_lt_mul_left h4 h3.le
    have hpow : (2 : ℝ) ^ e < 4 * ((j : ℝ) + 1) ^ 2 := by
      have h1 : (2 : ℝ) ^ e ≤ (k : ℝ) ^ e :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hk) _
      have h2 : 0 < levelWeight j := by unfold levelWeight; positivity
      have h3 : levelWeight j * (2 : ℝ) ^ e < 1 :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 h2.le) hweight
      have h4 : levelWeight j = 3 / (Real.pi ^ 2 * ((j : ℝ) + 1) ^ 2) := by
        unfold levelWeight
        rw [div_div]
      rw [h4, div_mul_eq_mul_div, div_lt_one (by positivity)] at h3
      nlinarith
    have hloge : (e : ℝ) * Real.log 2 < 2 * Real.log 2 + 2 * Real.log ((j : ℝ) + 1) := by
      have h1 := Real.log_lt_log (by positivity) hpow
      rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [h4] at h1
      push_cast at h1
      linarith
    have hl2 : (2 : ℝ) / 3 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have he3 : (e : ℝ) ≤ 2 + 3 * Real.log ((j : ℝ) + 1) := by
      by_contra hcon
      have hcon := not_le.mp hcon
      have h1 : 0 ≤ (e : ℝ) - 2 := by linarith
      have h2 : ((e : ℝ) - 2) * (2 / 3) ≤ ((e : ℝ) - 2) * Real.log 2 :=
        mul_le_mul_of_nonneg_left hl2 h1
      nlinarith
    have : 2 * (N : ℝ) + ((e : ℝ) + 1) * N ≤ 5 * (N : ℝ) * (1 + Real.log ((j : ℝ) + 1)) := by
      have h1 : ((e : ℝ) + 1) * N ≤ (3 + 3 * Real.log ((j : ℝ) + 1)) * N :=
        mul_le_mul_of_nonneg_right (by linarith) hN0
      nlinarith [mul_nonneg hN0 hlog0]
    linarith
end Counting
section Trees
variable {ℓ : TorusLumps.StepParameters}
private def coarsenSite (L : ℕ) : (i n : ℕ) → TorusSite (fineSide L i n) → TorusSite n
  | 0, _, c => c
  | i + 1, n, c => parentBlock L (coarsenSite L i (n * L) c)
private theorem mem_leafSites_node_succ {L u n k' i : ℕ} (y : TorusSite n)
    (kids : Fin k' → SiteTree L u (n * L)) (s : TorusSite (fineSide L (i + 1) n)) :
    s ∈ (SiteTree.node y k' kids).leafSites (i + 1) ↔ ∃ a, s ∈ (kids a).leafSites i := by
  constructor
  · intro h
    obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.mp h
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, ha⟩
private theorem not_mem_leafSites_leaf_succ {L u n i : ℕ} (y : TorusSite n)
    (s : TorusSite (fineSide L (i + 1) n)) :
    ¬ s ∈ (SiteTree.leaf y : SiteTree L u n).leafSites (i + 1) := by
  intro h
  exact Finset.notMem_empty _ h
private theorem not_mem_leafSites_node_zero {L u n k' : ℕ} (y : TorusSite n)
    (kids : Fin k' → SiteTree L u (n * L)) (s : TorusSite (fineSide L 0 n)) :
    ¬ s ∈ (SiteTree.node y k' kids).leafSites 0 := by
  intro h
  exact Finset.notMem_empty _ h
private theorem supDist_coarsenSite_root_le (T : StageTower ℓ) (k : ℕ) (hL : 12 ≤ ℓ.side) {v n : ℕ}
    (tr : SiteTree ℓ.side v n) :
    ∀ [NeZero n] (w : MarkedSample ℓ v n) (i : ℕ) (c : TorusSite (fineSide ℓ.side i n)),
      (∀ t ≤ v, 1 ≤ stageRange T t) → (∀ t < v, stageRange T t ≤ 2 * stageRange T (t + 1)) →
      tr.Embeds T k w → c ∈ tr.leafSites i →
      supDist (coarsenSite ℓ.side i n c) tr.root ≤ 4 * stageRange T v := by
  induction tr with
  | @leaf u n y =>
    intro _ w i c _ _ _ hc
    cases i with
    | zero =>
      have hc' : (c : TorusSite n) = y := Finset.mem_singleton.mp hc
      have h0 : supDist (c : TorusSite n) y = 0 :=
        (congrArg (fun q : TorusSite n => supDist q y) hc').trans (supDist_self y)
      show supDist (c : TorusSite n) y ≤ _
      omega
    | succ i => exact (not_mem_leafSites_leaf_succ y c hc).elim
  | @node u n y k' kids ih =>
    intro _ w i c h1 h2 hh hc
    cases i with
    | zero => exact (not_mem_leafSites_node_zero y kids c hc).elim
    | succ i =>
      obtain ⟨-, -, hbox, -, hkids⟩ := hh
      obtain ⟨a, ha⟩ := (mem_leafSites_node_succ y kids c).mp hc
      have hih := ih a w.1 i c (fun t ht => h1 t (by omega)) (fun t ht => h2 t (by omega)) (hkids a) ha
      have hb := hbox a
      rw [HullTrees.box, mem_thickening] at hb
      obtain ⟨x, hx, hb⟩ := hb
      rw [Finset.mem_singleton] at hx
      subst hx
      have hblock := TorusBalls.supDist_parentBlock_le_div_add_one (n := n) ℓ.side
        (coarsenSite ℓ.side i (n * ℓ.side) c) (kids a).root
      have hu : stageRange T u ≤ 2 * stageRange T (u + 1) := h2 u (by omega)
      have hone : 1 ≤ stageRange T (u + 1) := h1 (u + 1) le_rfl
      have hdiv : supDist (coarsenSite ℓ.side i (n * ℓ.side) c) (kids a).root / ℓ.side ≤
          stageRange T (u + 1) := by
        refine Nat.div_le_of_le_mul ?_
        have : 12 * stageRange T (u + 1) ≤ ℓ.side * stageRange T (u + 1) := Nat.mul_le_mul_right _ hL
        omega
      have htri := supDist_triangle (parentBlock ℓ.side (coarsenSite ℓ.side i (n * ℓ.side) c))
        (parentBlock ℓ.side (kids a).root) x
      show supDist (parentBlock ℓ.side (coarsenSite ℓ.side i (n * ℓ.side) c)) x ≤ _
      omega
private theorem card_leafSites_eq (T : StageTower ℓ) (k : ℕ) (hL : 12 ≤ ℓ.side) {v n : ℕ}
    (tr : SiteTree ℓ.side v n) :
    ∀ [NeZero n] (w : MarkedSample ℓ v n),
      (∀ t ≤ v, 1 ≤ stageRange T t) → (∀ t < v, stageRange T t ≤ 2 * stageRange T (t + 1)) →
      tr.Embeds T k w → ∀ i, (tr.leafSites i).card = tr.leavesAtDepth i := by
  induction tr with
  | @leaf u n y =>
    intro _ w _ _ _ i
    cases i with
    | zero => exact Finset.card_singleton y
    | succ i => exact Finset.card_empty
  | @node u n y k' kids ih =>
    intro _ w h1 h2 hh i
    cases i with
    | zero => exact Finset.card_empty
    | succ i =>
      have hh' := hh
      obtain ⟨-, -, -, hapart, hkids⟩ := hh'
      have h1' : ∀ t ≤ u, 1 ≤ stageRange T t := fun t ht => h1 t (by omega)
      have h2' : ∀ t < u, stageRange T t ≤ 2 * stageRange T (t + 1) := fun t ht => h2 t (by omega)
      refine (Finset.card_biUnion ?_).trans ?_
      · intro a _ b _ hab
        refine Finset.disjoint_left.mpr fun c hca hcb => ?_
        have ra := supDist_coarsenSite_root_le T k hL (kids a) w.1 i c h1' h2' (hkids a) hca
        have rb := supDist_coarsenSite_root_le T k hL (kids b) w.1 i c h1' h2' (hkids b) hcb
        have hd := hapart a b hab
        have htri := supDist_triangle (kids a).root (coarsenSite ℓ.side i (n * ℓ.side) c) (kids b).root
        have hcomm := supDist_comm (kids a).root (coarsenSite ℓ.side i (n * ℓ.side) c)
        have hone := h1 u (by omega)
        omega
      · exact Finset.sum_congr rfl fun a _ => ih a w.1 h1' h2' (hkids a) i
open Classical in
private def children {L v n : ℕ} : SiteTree L (v + 1) n → Finset (SiteTree L v (n * L))
  | .leaf _ => ∅
  | .node _ _ kids => Finset.univ.image kids
private theorem exists_child_of_mem_leafSites {L v n i : ℕ} (t : SiteTree L (v + 1) n)
    (s : TorusSite (fineSide L (i + 1) n))
    (h : s ∈ t.leafSites (i + 1)) : ∃ t' ∈ children t, s ∈ t'.leafSites i := by
  cases t with
  | leaf y => exact (not_mem_leafSites_leaf_succ y s h).elim
  | node y k' kids =>
    obtain ⟨a, ha⟩ := (mem_leafSites_node_succ y kids s).mp h
    exact ⟨kids a, by simp [children], ha⟩
private theorem children_embed (T : StageTower ℓ) (k : ℕ) {v n : ℕ} [NeZero n]
    (t : SiteTree ℓ.side (v + 1) n)
    (w : MarkedSample ℓ (v + 1) n) (h : t.Embeds T k w) :
    (children t).card ≤ k ∧ ∀ t' ∈ children t, t'.Embeds T k w.1 ∧
      parentBlock ℓ.side t'.root ∈ HullTrees.box t.root (2 * stageRange T (v + 1)) := by
  classical
  cases t with
  | leaf y => simp [children]
  | node y k' kids =>
    obtain ⟨-, hk, hbox, -, hkids⟩ := h
    subst hk
    refine ⟨?_, ?_⟩
    · simp only [children]
      exact Finset.card_image_le.trans (by simp)
    · intro t' ht'
      simp only [children, Finset.mem_image, Finset.mem_univ, true_and] at ht'
      obtain ⟨a, rfl⟩ := ht'
      exact ⟨hkids a, hbox a⟩
private theorem eq_root_of_mem_leafSites_zero {L v n : ℕ} (t : SiteTree L v n)
    (s : TorusSite (fineSide L 0 n))
    (h : s ∈ t.leafSites 0) : s = t.root := by
  cases t with
  | leaf y => exact Finset.mem_singleton.mp h
  | node y k' kids => exact (not_mem_leafSites_node_zero y kids s h).elim
private theorem not_mem_leafSites_of_height_zero {L n i : ℕ} (t : SiteTree L 0 n)
    (s : TorusSite (fineSide L (i + 1) n))
    (h : s ∈ t.leafSites (i + 1)) : False := by
  cases t with
  | leaf y => exact not_mem_leafSites_leaf_succ y s h
private theorem card_sitesInBlocks_le {n : ℕ} [NeZero n] (L : ℕ) [NeZero L] (S : Finset (TorusSite n)) :
    (sitesInBlocks L S).card ≤ S.card * (2 * L + 1) ^ 4 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.LocalEventLikely.card_sitesInBlocks_le <;> assumption
open Classical in
private def descendingFamilies (ℓ : TorusLumps.StepParameters) (ρ cap : ℕ → ℕ) : (i v n : ℕ) → [NeZero n] →
    Finset (TorusSite n) → Finset (Finset (TorusSite (fineSide ℓ.side i n)))
  | 0, _, _, _, A => {A}
  | _ + 1, 0, _, _, _ => ∅
  | i + 1, v + 1, n, _, A =>
      ((sitesInBlocks ℓ.side (thickening (2 * ρ (v + 1)) A)).powerset.filter fun A' => A'.card ≤ cap i).biUnion
        fun A' => descendingFamilies ℓ ρ cap i v (n * ℓ.side) A'
private theorem card_descendingFamilies_le (ℓ : TorusLumps.StepParameters) (ρ cap : ℕ → ℕ) (c : ℝ) (hc : 1 ≤ c)
    (hcap : ∀ l, cap (l + 1) ≤ cap l) (i : ℕ) :
    ∀ (v n : ℕ) [NeZero n] (A : Finset (TorusSite n)), A.card ≤ cap i →
      (∀ t, t ≤ v → v < t + i → (((2 * (2 * ρ t) + 1) ^ 4 * (2 * ℓ.side + 1) ^ 4 : ℕ) : ℝ) ≤ c) →
      ((descendingFamilies ℓ ρ cap i v n A).card : ℝ) ≤
        (Real.exp 1 * c) ^ (∑ l ∈ Finset.range i, cap l) := by
  induction i with
  | zero =>
    intro v n _ A _ _
    have h1 : (descendingFamilies ℓ ρ cap 0 v n A).card = 1 := Finset.card_singleton A
    rw [h1]
    simp
  | succ i ih =>
    intro v n _ A hA hrange
    cases v with
    | zero =>
      simp only [descendingFamilies, Finset.card_empty, Nat.cast_zero]
      positivity
    | succ v =>
      classical
      simp only [descendingFamilies]
      set B := sitesInBlocks ℓ.side (thickening (2 * ρ (v + 1)) A) with hB
      have hBcard : (B.card : ℝ) ≤ (cap i : ℝ) * c := by
        have h1 : B.card ≤ A.card * (2 * (2 * ρ (v + 1)) + 1) ^ 4 * (2 * ℓ.side + 1) ^ 4 :=
          (card_sitesInBlocks_le ℓ.side _).trans
            (Nat.mul_le_mul_right _ (TorusCounting.card_thickening_le _ _))
        have h2 : A.card ≤ cap i := hA.trans (hcap i)
        have h3 : (B.card : ℝ) ≤
            (A.card : ℝ) * (((2 * (2 * ρ (v + 1)) + 1) ^ 4 * (2 * ℓ.side + 1) ^ 4 : ℕ) : ℝ) := by
          rw [mul_assoc] at h1
          exact_mod_cast h1
        have h4 := hrange (v + 1) le_rfl (by omega)
        calc (B.card : ℝ) ≤
              (A.card : ℝ) * (((2 * (2 * ρ (v + 1)) + 1) ^ 4 * (2 * ℓ.side + 1) ^ 4 : ℕ) : ℝ) := h3
          _ ≤ (cap i : ℝ) * c := by
            have : (A.card : ℝ) ≤ cap i := by exact_mod_cast h2
            gcongr
      have hsub := card_powerset_filter_card_le_le B (cap i) c hc hBcard
      have hbound : ∀ A' ∈ B.powerset.filter (fun A' => A'.card ≤ cap i),
          (((descendingFamilies ℓ ρ cap i v (n * ℓ.side) A').card : ℕ) : ℝ) ≤
            (Real.exp 1 * c) ^ (∑ l ∈ Finset.range i, cap l) := by
        intro A' hA'
        refine ih v (n * ℓ.side) A' (Finset.mem_filter.mp hA').2 fun t ht1 ht2 => ?_
        exact hrange t (by omega) (by omega)
      calc (((B.powerset.filter fun A' => A'.card ≤ cap i).biUnion
              fun A' => descendingFamilies ℓ ρ cap i v (n * ℓ.side) A').card : ℝ)
          ≤ ∑ A' ∈ B.powerset.filter (fun A' => A'.card ≤ cap i),
              ((descendingFamilies ℓ ρ cap i v (n * ℓ.side) A').card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _A' ∈ B.powerset.filter (fun A' => A'.card ≤ cap i),
              (Real.exp 1 * c) ^ (∑ l ∈ Finset.range i, cap l) := Finset.sum_le_sum hbound
        _ = ((B.powerset.filter fun A' => A'.card ≤ cap i).card : ℝ) *
              (Real.exp 1 * c) ^ (∑ l ∈ Finset.range i, cap l) := by simp
        _ ≤ (Real.exp 1 * c) ^ cap i * (Real.exp 1 * c) ^ (∑ l ∈ Finset.range i, cap l) := by
            gcongr
        _ = (Real.exp 1 * c) ^ (∑ l ∈ Finset.range (i + 1), cap l) := by
            rw [Finset.sum_range_succ, pow_add, mul_comm]
open Classical in
private theorem mem_descendingFamilies (T : StageTower ℓ) (k N : ℕ) (cap : ℕ → ℕ) (i : ℕ) :
    ∀ (v n : ℕ) [NeZero n] (w : MarkedSample ℓ v n) (Φ : Finset (SiteTree ℓ.side v n)) (p : ℕ)
      (S : Finset (TorusSite (fineSide ℓ.side i n))),
      S.Nonempty → S.card ≤ N → Φ.card ≤ p → (∀ l < i, min (k ^ (i - l) * p) N ≤ cap l) →
      (∀ t ∈ Φ, t.Embeds T k w) → (∀ t ∈ Φ, ∃ s ∈ S, s ∈ t.leafSites i) →
      (∀ s ∈ S, ∃ t ∈ Φ, s ∈ t.leafSites i) →
      S ∈ descendingFamilies ℓ (stageRange T) cap i v n (Φ.image SiteTree.root) := by
  induction i with
  | zero =>
    intro v n _ w Φ p S _ _ _ _ _ hused hcover
    refine Finset.mem_singleton.mpr (Finset.ext fun s => ⟨fun hs => ?_, fun hs => ?_⟩)
    · obtain ⟨t, ht, hst⟩ := hcover s hs
      exact Finset.mem_image.mpr ⟨t, ht, (eq_root_of_mem_leafSites_zero t s hst).symm⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨s', hs', hst⟩ := hused t ht
      have := eq_root_of_mem_leafSites_zero t s' hst
      rw [← this]
      exact hs'
  | succ i ih =>
    intro v n _ w Φ p S hne hS hΦ hcap hemb hused hcover
    cases v with
    | zero =>
      obtain ⟨s, hs⟩ := hne
      obtain ⟨t, -, hst⟩ := hcover s hs
      exact (not_mem_leafSites_of_height_zero t s hst).elim
    | succ v =>
      have hkid : ∀ s ∈ S, ∃ t' ∈ Φ.biUnion children, s ∈ t'.leafSites i := by
        intro s hs
        obtain ⟨t, ht, hst⟩ := hcover s hs
        obtain ⟨t', ht', hst'⟩ := exists_child_of_mem_leafSites t s hst
        exact ⟨t', Finset.mem_biUnion.mpr ⟨t, ht, ht'⟩, hst'⟩
      choose f hf hfs using hkid
      set Φ' : Finset (SiteTree ℓ.side v (n * ℓ.side)) := S.attach.image fun s => f s.1 s.2 with hΦ'
      have hsub : Φ' ⊆ Φ.biUnion children := by
        intro t' ht'
        obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp ht'
        exact hf s.1 s.2
      have hcard1 : Φ'.card ≤ N := by
        refine Finset.card_image_le.trans ?_
        simpa using hS
      have hcard2 : Φ'.card ≤ k * p := by
        refine (Finset.card_le_card hsub).trans ?_
        refine (Finset.card_biUnion_le_card_mul Φ children k fun t ht =>
          (children_embed T k t w (hemb t ht)).1).trans ?_
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ hΦ
      simp only [descendingFamilies]
      refine Finset.mem_biUnion.mpr ⟨Φ'.image SiteTree.root, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
        · intro x hx
          obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨t, ht, htk⟩ := Finset.mem_biUnion.mp (hsub ht')
          have hb := ((children_embed T k t w (hemb t ht)).2 t' htk).2
          rw [HullTrees.box, mem_thickening] at hb
          obtain ⟨x, hx, hb⟩ := hb
          rw [Finset.mem_singleton] at hx
          subst hx
          simp only [sitesInBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (mem_thickening _ _ _).mpr ⟨t.root, Finset.mem_image.mpr ⟨t, ht, rfl⟩, hb⟩
        · refine Finset.card_image_le.trans ?_
          have h1 := hcap i (by omega)
          have h2 : i + 1 - i = 1 := by omega
          rw [h2, pow_one] at h1
          exact (le_min hcard2 hcard1).trans h1
      · refine ih v (n * ℓ.side) w.1 Φ' (k * p) S hne hS hcard2 ?_ ?_ ?_ ?_
        · intro l hl
          have h1 := hcap l (by omega)
          have h2 : k ^ (i + 1 - l) * p = k ^ (i - l) * (k * p) := by
            have : i + 1 - l = (i - l) + 1 := by omega
            rw [this, pow_succ]
            ring
          rwa [h2] at h1
        · intro t' ht'
          obtain ⟨t, ht, htk⟩ := Finset.mem_biUnion.mp (hsub ht')
          exact ((children_embed T k t w (hemb t ht)).2 t' htk).1
        · intro t' ht'
          obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp ht'
          exact ⟨s.1, s.2, hfs s.1 s.2⟩
        · intro s hs
          exact ⟨f s hs, Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_attach _ _, rfl⟩, hfs s hs⟩
end Trees
section Levels
private theorem one_le_clusterRange {x : ℝ} (hx : 1 ≤ x) : 1 ≤ clusterRange x := by
  unfold clusterRange
  exact Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (by linarith) _)
private theorem clusterRange_le_two_mul {x x' : ℝ} (hx : 1 ≤ x) (hx' : 1 ≤ x') (h : x ≤ 2 * x') :
    clusterRange x ≤ 2 * clusterRange x' := by
  unfold clusterRange
  refine Nat.ceil_le.mpr ?_
  have h1 : x ^ ((1 : ℝ) / 100) ≤ (2 * x') ^ ((1 : ℝ) / 100) :=
    Real.rpow_le_rpow (by linarith) h (by norm_num)
  have h2 : (2 * x') ^ ((1 : ℝ) / 100) = 2 ^ ((1 : ℝ) / 100) * x' ^ ((1 : ℝ) / 100) :=
    Real.mul_rpow (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h4 : x' ^ ((1 : ℝ) / 100) ≤ (⌈x' ^ ((1 : ℝ) / 100)⌉₊ : ℝ) := Nat.le_ceil _
  have h5 : 0 ≤ x' ^ ((1 : ℝ) / 100) := Real.rpow_nonneg (by linarith) _
  push_cast
  calc x ^ ((1 : ℝ) / 100) ≤ 2 ^ ((1 : ℝ) / 100) * x' ^ ((1 : ℝ) / 100) := h2 ▸ h1
    _ ≤ 2 * x' ^ ((1 : ℝ) / 100) := mul_le_mul_of_nonneg_right h3 h5
    _ ≤ 2 * (⌈x' ^ ((1 : ℝ) / 100)⌉₊ : ℝ) := by linarith
private theorem clusterRange_le {x : ℝ} (hx : 1 ≤ x) : (clusterRange x : ℝ) ≤ x + 1 := by apply _root_.YangMills.SharedProofs.p37996 <;> assumption
variable {ℓ : TorusLumps.StepParameters}
private theorem exists_leafSiteFamilies (T : StageTower ℓ) (u n : ℕ) [NeZero n] (hL : 2 ^ 40 ≤ ℓ.side)
    (hx1 : ∀ t ≤ u, 1 ≤ stageCoupling T t)
    (hstep : ∀ t < u, stageCoupling T t ≤ 2 * stageCoupling T (t + 1))
    (hdesc : ∀ i t, i ≤ t → t ≤ u → stageCoupling T t ≤ 2 * stageCoupling T i) :
    ∃ F : TorusSite n → (j : ℕ) → Finset (Finset (TorusSite (fineSide ℓ.side j n))),
      ∀ (z : TorusSite n) (j : ℕ), j ≤ u →
        ((F z j).card : ℝ) ≤ Real.exp (65 * (minLeafCount ℓ.side j : ℝ) *
          (1 + Real.log ((j : ℝ) + 1)) * (Real.log (ℓ.side : ℝ) + Real.log (stageCoupling T (u - j)))) ∧
        (∀ S ∈ F z j, S.card = minLeafCount ℓ.side j) ∧
        ∀ (w : MarkedSample ℓ u n) (tr : SiteTree ℓ.side u n), tr.root = z →
          tr.Embeds T (treeBranching ℓ.side) w →
          levelWeight j * (treeBranching ℓ.side : ℝ) ^ j ≤ (tr.leavesAtDepth j : ℝ) →
          ∃ S ∈ F z j, S ⊆ tr.leafSites j := by
  classical
  have hLn : 1099511627776 ≤ ℓ.side := by simpa using hL
  have hk2 : 2 ≤ treeBranching ℓ.side := by
    unfold treeBranching
    omega
  have hL12 : 12 ≤ ℓ.side := by omega
  have h1 : ∀ t ≤ u, 1 ≤ stageRange T t := fun t ht => one_le_clusterRange (hx1 t ht)
  have h2 : ∀ t < u, stageRange T t ≤ 2 * stageRange T (t + 1) := fun t ht =>
    clusterRange_le_two_mul (hx1 t ht.le) (hx1 (t + 1) ht) (hstep t ht)
  refine ⟨fun z j => (descendingFamilies ℓ (stageRange T)
    (fun l => min (treeBranching ℓ.side ^ (j - l)) (minLeafCount ℓ.side j))
    j u n {z}).filter fun S => S.card = minLeafCount ℓ.side j, ?_⟩
  intro z j hj
  have hweight : 0 < levelWeight j * (treeBranching ℓ.side : ℝ) ^ j := by
    have : 0 < levelWeight j := by
      unfold levelWeight
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      positivity
    positivity
  have hfloor : max 1 (levelWeight j * (treeBranching ℓ.side : ℝ) ^ j) ≤ (minLeafCount ℓ.side j : ℝ) :=
    Nat.le_ceil _
  have hN1 : 1 ≤ minLeafCount ℓ.side j := by
    have : (1 : ℝ) ≤ (minLeafCount ℓ.side j : ℝ) := (le_max_left _ _).trans hfloor
    exact_mod_cast this
  have hθ : levelWeight j * (treeBranching ℓ.side : ℝ) ^ j ≤ (minLeafCount ℓ.side j : ℝ) :=
    (le_max_right _ _).trans hfloor
  have hx : 1 ≤ stageCoupling T (u - j) := hx1 _ (by omega)
  have hLr : (1099511627776 : ℝ) ≤ (ℓ.side : ℝ) := by exact_mod_cast hLn
  refine ⟨?_, fun S hS => (Finset.mem_filter.mp hS).2, ?_⟩
  · set x := stageCoupling T (u - j) with hxdef
    set c : ℝ := (13 * x) ^ 4 * (2 * (ℓ.side : ℝ) + 1) ^ 4 with hc
    have hc1 : 1 ≤ c := by
      have e1 : 1 ≤ (13 * x) ^ 4 := one_le_pow₀ (by linarith)
      have e2 : 1 ≤ (2 * (ℓ.side : ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith)
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ c := mul_le_mul e1 e2 zero_le_one (by positivity)
    have hanti : ∀ l, min (treeBranching ℓ.side ^ (j - (l + 1))) (minLeafCount ℓ.side j) ≤
        min (treeBranching ℓ.side ^ (j - l)) (minLeafCount ℓ.side j) := fun l =>
      min_le_min_right _ (Nat.pow_le_pow_right (by omega) (by omega))
    have hA : ({z} : Finset (TorusSite n)).card ≤
        min (treeBranching ℓ.side ^ (j - j)) (minLeafCount ℓ.side j) := by
      rw [Finset.card_singleton]
      exact le_min (by simp) hN1
    have hrange : ∀ t, t ≤ u → u < t + j →
        (((2 * (2 * stageRange T t) + 1) ^ 4 * (2 * ℓ.side + 1) ^ 4 : ℕ) : ℝ) ≤ c := by
      intro t ht1 ht2
      have e1 : (stageRange T t : ℝ) ≤ stageCoupling T t + 1 := clusterRange_le (hx1 t ht1)
      have e2 : stageCoupling T t ≤ 2 * x := hdesc (u - j) t (by omega) ht1
      have e3 : 2 * (2 * (stageRange T t : ℝ)) + 1 ≤ 13 * x := by linarith
      push_cast
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) e3 _) (by positivity)
    have hfam := card_descendingFamilies_le ℓ (stageRange T)
      (fun l => min (treeBranching ℓ.side ^ (j - l)) (minLeafCount ℓ.side j))
      c hc1 hanti j u n {z} hA hrange
    have hM := sum_min_pow_le (treeBranching ℓ.side) (minLeafCount ℓ.side j) j hk2 hN1 hθ
    have hec : 0 < Real.exp 1 * c := by positivity
    have hΛ0 : 0 ≤ Real.log (Real.exp 1 * c) := Real.log_nonneg (by
      have := Real.add_one_le_exp (1 : ℝ)
      nlinarith)
    have hlogL : 1 ≤ Real.log (ℓ.side : ℝ) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
    have hΛ : Real.log (Real.exp 1 * c) ≤ 13 * (Real.log (ℓ.side : ℝ) + Real.log x) := by
      have e1 : Real.log (Real.exp 1 * c) =
          1 + (4 * Real.log (13 * x) + 4 * Real.log (2 * (ℓ.side : ℝ) + 1)) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, hc,
          Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
        norm_num
      have e2 : Real.log (13 * x) ≤ Real.log (ℓ.side : ℝ) + Real.log x := by
        rw [Real.log_mul (by norm_num) (by linarith)]
        have := Real.log_le_log (by norm_num : (0 : ℝ) < 13) (by linarith : (13 : ℝ) ≤ (ℓ.side : ℝ))
        linarith
      have e3 : Real.log (2 * (ℓ.side : ℝ) + 1) ≤ 2 * Real.log (ℓ.side : ℝ) := by
        have := Real.log_le_log (by positivity : (0 : ℝ) < 2 * (ℓ.side : ℝ) + 1)
          (by nlinarith : 2 * (ℓ.side : ℝ) + 1 ≤ (ℓ.side : ℝ) ^ 2)
        rwa [Real.log_pow] at this
      rw [e1]
      linarith
    have hMnn : (0 : ℝ) ≤ 5 * (minLeafCount ℓ.side j : ℝ) * (1 + Real.log ((j : ℝ) + 1)) :=
      le_trans (Nat.cast_nonneg _) hM
    calc ((Finset.filter (fun S => S.card = minLeafCount ℓ.side j) (descendingFamilies ℓ (stageRange T)
            (fun l => min (treeBranching ℓ.side ^ (j - l)) (minLeafCount ℓ.side j)) j u n {z})).card : ℝ)
        ≤ ((descendingFamilies ℓ (stageRange T)
            (fun l => min (treeBranching ℓ.side ^ (j - l)) (minLeafCount ℓ.side j)) j u n {z}).card : ℝ) := by
          exact_mod_cast Finset.card_filter_le _ _
      _ ≤ (Real.exp 1 * c) ^
            (∑ l ∈ Finset.range j, min (treeBranching ℓ.side ^ (j - l)) (minLeafCount ℓ.side j)) := hfam
      _ = Real.exp (((∑ l ∈ Finset.range j,
            min (treeBranching ℓ.side ^ (j - l)) (minLeafCount ℓ.side j) : ℕ) : ℝ) *
            Real.log (Real.exp 1 * c)) := by
          rw [Real.exp_nat_mul, Real.exp_log hec]
      _ ≤ _ := by
          refine Real.exp_le_exp.mpr ?_
          calc _ ≤ (5 * (minLeafCount ℓ.side j : ℝ) * (1 + Real.log ((j : ℝ) + 1))) *
                  (13 * (Real.log (ℓ.side : ℝ) + Real.log x)) :=
                mul_le_mul hM hΛ hΛ0 hMnn
            _ = _ := by ring
  · intro w tr hroot hemb hcount
    have hcard := card_leafSites_eq T (treeBranching ℓ.side) hL12 tr w h1 h2 hemb j
    have hNle : minLeafCount ℓ.side j ≤ (tr.leafSites j).card := by
      rw [hcard]
      refine Nat.ceil_le.mpr (max_le ?_ hcount)
      have : (0 : ℝ) < (tr.leavesAtDepth j : ℝ) := lt_of_lt_of_le hweight hcount
      have h' : 0 < tr.leavesAtDepth j := by exact_mod_cast this
      exact_mod_cast h'
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hNle
    have hne : S.Nonempty := by
      rw [← Finset.card_pos, hScard]
      omega
    refine ⟨S, Finset.mem_filter.mpr ⟨?_, hScard⟩, hSsub⟩
    have hmem := mem_descendingFamilies T (treeBranching ℓ.side) (minLeafCount ℓ.side j)
      (fun l => min (treeBranching ℓ.side ^ (j - l)) (minLeafCount ℓ.side j)) j u n w {tr} 1 S hne
      hScard.le (by simp)
      (fun l _ => by simp)
      (fun t ht => by rw [Finset.mem_singleton] at ht; rw [ht]; exact hemb)
      (fun t ht => by
        rw [Finset.mem_singleton] at ht
        obtain ⟨s, hs⟩ := hne
        exact ⟨s, hs, ht ▸ hSsub hs⟩)
      (fun s hs => ⟨tr, Finset.mem_singleton_self _, hSsub hs⟩)
    have himg : ({tr} : Finset (SiteTree ℓ.side u n)).image SiteTree.root = {z} := by
      rw [Finset.image_singleton, hroot]
    rw [himg] at hmem
    exact hmem
private theorem expansion_step (hret : StepReturn.ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ}
    {D : TorusFunctional} (hy : ℓ.y₁ ≤ x) (hexp : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
end Levels
theorem fewLeafSiteFamilies_of_flowDescendsLinearly (hs : FlowDescendsLinearly) :
    FewLeafSiteFamilies := by
  refine ⟨fun _ => 65, ?_⟩
  intro a ha
  obtain ⟨L₀, rt₀, hrt, hL⟩ := hs a ha
  refine ⟨L₀, rt₀, 0, hrt, fun L hodd hLge Tb hTa hTL hAdm _ _ hTrt _ => ?_⟩
  obtain ⟨lam, c₅, hlam, hT⟩ := hL L hodd hLge
  refine ⟨0, fun Kr _ _ _ _ _ => ?_⟩
  obtain ⟨y₀, hy₀⟩ := hT Tb hTa hTL hAdm hTrt
  refine ⟨max (max y₀ 1) (max (2 * Tb.B) c₅), fun y hy hret hexp => ?_⟩
  have hyy₀ : y₀ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy1 : 1 ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hyB : 2 * Tb.B ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hyc : c₅ ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hsl : HasLinearDescent (Tb.stepParameters y) lam c₅ := hy₀ y hyy₀ hret hexp
  intro g β K m T u n _ hat
  have hchain := hat.chain
  have huK : u ≤ K := hat.le
  have hB : 1 ≤ Tb.B := hAdm.B_ge
  have hfloor : y ≤ (g ^ 2)⁻¹ := hchain.le_inv_sq
  have hupper : (g ^ 2)⁻¹ + 2 * Tb.B ≤ β := hchain.upper_le
  have hfirst := hchain.isFirst
  have hβ : y ≤ β := by linarith
  have hfar : ∀ k < K, (g ^ 2)⁻¹ + 2 * Tb.B < (couplingFlow (Tb.stepParameters y) β k).1 := hfirst.2
  have hnear : ∀ k < K, y ≤ (couplingFlow (Tb.stepParameters y) β k).1 := fun k hk => by
    have := hfar k hk
    linarith
  have hexps : ∀ t, t ≤ K → HasExpansion (Tb.stepParameters y) t
      (couplingFlow (Tb.stepParameters y) β t).1 (couplingFlow (Tb.stepParameters y) β t).2 := by
    intro t
    induction t with
    | zero => exact fun _ => hexp β hβ
    | succ t ih =>
      intro ht
      exact (expansion_step hret (hnear t (by omega)) (ih (by omega))).1
  have hmove : ∀ t, t < K → |(couplingFlow (Tb.stepParameters y) β (t + 1)).1 -
      (couplingFlow (Tb.stepParameters y) β t).1| ≤ 2 * Tb.B :=
    fun t ht => (expansion_step hret (hnear t ht) (hexps t ht.le)).2
  have hall : ∀ t, t ≤ K → y ≤ (couplingFlow (Tb.stepParameters y) β t).1 := by
    intro t ht
    rcases Nat.lt_or_ge t K with h | h
    · exact hnear t h
    · have htK : t = K := le_antisymm ht h
      subst htK
      cases t with
      | zero => exact hβ
      | succ t =>
        have h1 := hfar t (by omega)
        have h2 := abs_le.mp (hmove t (by omega))
        linarith [h2.1]
  have hlev : ∀ t, t ≤ K → stageCoupling T t = (couplingFlow (Tb.stepParameters y) β t).1 := fun t ht =>
    hchain.follows t (by omega)
  have hLbig : 2 ^ 40 ≤ (Tb.stepParameters y).side := hAdm.L_ge
  refine exists_leafSiteFamilies T u n hLbig ?_ ?_ ?_
  · intro t ht
    rw [hlev t (by omega)]
    exact hy1.trans (hall t (by omega))
  · intro t ht
    rw [hlev t (by omega), hlev (t + 1) (by omega)]
    have h1 := abs_le.mp (hmove t (by omega))
    have h2 := hall (t + 1) (by omega)
    linarith [h1.1]
  · intro i t hit ht
    rw [hlev t (by omega), hlev i (by omega)]
    have h1 := hsl β hβ t (fun k hk => hall k (by omega)) i hit
    have h2 : (0 : ℝ) ≤ lam * ((t : ℝ) - i) := by
      have : (i : ℝ) ≤ t := by exact_mod_cast hit
      exact mul_nonneg hlam.le (by linarith)
    have h3 := hall i (by omega)
    linarith
end YangMills.Construction.HullTrees
end
