import YangMills.Construction.Lattice.EdgesOfAPartitionAndTheirEndPoints
import YangMills.Construction.Lattice.EdgesOfAPartitionAreCompactAndConnected
import YangMills.Construction.Lattice.NumberingOfVerticesAlongEdges
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.PeriodicLattice.VertexNumbering
open EdgeGraphCubeProperties
variable (S : LevelUnitPartition)
theorem chain_exists_step_across {α : Type*} {R : α → α → Prop} (P : α → Prop) :
    ∀ (c : List α) (x y : α), c.IsChain R → c.head? = some x → c.getLast? = some y → P x → ¬P y →
      ∃ a b, b ∈ c ∧ R a b ∧ P a ∧ ¬P b := by
  intro c
  induction c with
  | nil => intro x y _ hx; simp at hx
  | cons u t ih =>
    intro x y hc hx hy hPx hPy
    have hux : u = x := by simpa using hx
    subst hux
    cases t with
    | nil =>
      have huy : u = y := by simpa using hy
      exact absurd (huy ▸ hPx) hPy
    | cons z t =>
      rw [List.isChain_cons_cons] at hc
      by_cases hz : P z
      · obtain ⟨a, b, hb, hR, hPa, hPb⟩ :=
          ih z y hc.2 rfl (by simpa using hy) hz hPy
        exact ⟨a, b, List.mem_cons_of_mem _ hb, hR, hPa, hPb⟩
      · exact ⟨u, z, by simp, hc.1, hPx, hz⟩
theorem ncard_Icc_one_eq (n : ℕ) : (Icc 1 n : Set ℕ).ncard = n := by
  rw [← Finset.coe_Icc, Set.ncard_coe_finset]
  simp
theorem exists_initial_numbering {W : Set S.Points} {q : ℕ} {A : Set (Set S.Points)}
    (hq : W.ncard = q) (hjoin : ∀ v ∈ W, ∀ v' ∈ W, LinkedByChain S W A v v')
    {F : S.Points} (hF : F ∈ W) (n : ℕ) (hn : 1 ≤ n) (hnq : n ≤ q) :
    ∃ (v : ℕ → S.Points) (a : ℕ → Set S.Points), v 1 = F ∧ MapsTo v (Icc 1 n) W ∧
      InjOn v (Icc 1 n) ∧
      ∀ k, 2 ≤ k → k ≤ n → a k ∈ A ∧ ∃ l, 1 ≤ l ∧ l < k ∧ HasEndpoints S (a k) (v k) (v l) := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨fun _ => F, fun _ => ∅, rfl, ?_, ?_, ?_⟩
    · intro _ _
      exact hF
    · intro i hi j hj _
      have hi' := hi.2
      have hj' := hj.2
      have hi'' := hi.1
      have hj'' := hj.1
      omega
    · intro k h2 h1
      omega
  | succ n hn ih =>
    obtain ⟨v, a, hv1, hmaps, hinj, hstep⟩ := ih (by omega)
    have hcard : (v '' Icc 1 n).ncard = n := by
      rw [hinj.ncard_image, ncard_Icc_one_eq]
    obtain ⟨x, hxW, hx⟩ : ∃ x ∈ W, x ∉ v '' Icc 1 n := by
      by_contra hall
      push Not at hall
      have hle := Set.ncard_le_ncard (show W ⊆ v '' Icc 1 n from hall)
        ((Set.finite_Icc 1 n).image v)
      omega
    obtain ⟨c, hcW, hchain, hhead, hlast⟩ := hjoin F hF x hxW
    have hF' : F ∈ v '' Icc 1 n := ⟨1, ⟨le_refl 1, hn⟩, hv1⟩
    obtain ⟨u, b, hbc, ⟨e, heA, hends⟩, ⟨l, hl, rfl⟩, hb⟩ :=
      chain_exists_step_across (fun y => y ∈ v '' Icc 1 n) c F x hchain hhead hlast hF' hx
    have hne : ∀ i, i ≤ n → i ≠ n + 1 := fun i hi => by omega
    refine ⟨Function.update v (n + 1) b, Function.update a (n + 1) e, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by omega)]
      exact hv1
    · intro i hi
      by_cases hin : i = n + 1
      · subst hin
        rw [Function.update_self]
        exact hcW b hbc
      · rw [Function.update_of_ne hin]
        exact hmaps ⟨hi.1, by have := hi.2; omega⟩
    · intro i hi j hj hij
      by_cases hin : i = n + 1
      · by_cases hjn : j = n + 1
        · omega
        · subst hin
          rw [Function.update_self, Function.update_of_ne hjn] at hij
          exact absurd ⟨j, ⟨hj.1, by have := hj.2; omega⟩, hij.symm⟩ hb
      · by_cases hjn : j = n + 1
        · subst hjn
          rw [Function.update_self, Function.update_of_ne hin] at hij
          exact absurd ⟨i, ⟨hi.1, by have := hi.2; omega⟩, hij⟩ hb
        · rw [Function.update_of_ne hin, Function.update_of_ne hjn] at hij
          exact hinj ⟨hi.1, by have := hi.2; omega⟩ ⟨hj.1, by have := hj.2; omega⟩ hij
    · intro k h2 hk
      by_cases hkn : k = n + 1
      · subst hkn
        rw [Function.update_self, Function.update_self]
        refine ⟨heA, l, hl.1, by have := hl.2; omega, ?_⟩
        rw [Function.update_of_ne (hne l hl.2)]
        exact ⟨hends.1.symm, hends.2.2, hends.2.1⟩
      · rw [Function.update_of_ne hkn, Function.update_of_ne hkn]
        obtain ⟨hA, l', hl1, hlk, hl'⟩ := hstep k h2 (by omega)
        refine ⟨hA, l', hl1, hlk, ?_⟩
        rw [Function.update_of_ne (by omega)]
        exact hl'
theorem edgeEndpoint_eq_or_eq
    (hends : PartitionEdgeEndpoints) {e : Set S.Points}
    (he : S.IsEdge e) {x y z : S.Points} (hxy : HasEndpoints S e x y)
    (hz : S.IsEdgeEndpoint e z) : z = x ∨ z = y := by
  have hregion : IsPartitionRegion S.index S.fullRegion := ⟨S.cubes, subset_rfl, rfl⟩
  have htwo : {w | S.IsEdgeEndpoint e w}.ncard = 2 := (hends S S.fullRegion hregion).2.1 e he
  have hfin : {w | S.IsEdgeEndpoint e w}.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hsub : ({x, y} : Set S.Points) ⊆ {w | S.IsEdgeEndpoint e w} := by
    rintro w (rfl | rfl)
    · exact hxy.2.1
    · exact hxy.2.2
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (by rw [htwo, Set.ncard_pair hxy.1]) hfin
  have hmem : z ∈ ({x, y} : Set S.Points) := by
    rw [heq]
    exact hz
  simpa using hmem
theorem verticesNumberedAlongEdges_holds (hends : PartitionEdgeEndpoints)
    (hedges : LevelUnitPartitionEdgesCompactConnected) :
    VerticesNumberedAlongEdges := by
  intro S W q A hW hq hq1 _ hA hjoin F hF
  obtain ⟨v, a, hv1, hmaps, hinj, hstep⟩ :=
    exists_initial_numbering S hq hjoin hF q hq1 le_rfl
  have hbij : BijOn v (Icc 1 q) W := by
    refine ⟨hmaps, hinj, ?_⟩
    have hsub : v '' Icc 1 q ⊆ W := hmaps.image_subset
    have hcard : W.ncard ≤ (v '' Icc 1 q).ncard := by
      rw [hinj.ncard_image, ncard_Icc_one_eq, hq]
    exact (Set.eq_of_subset_of_ncard_le hsub hcard hW).ge
  have hedge : ∀ k, 2 ≤ k → k ≤ q → S.IsEdge (a k) :=
    fun k h2 hk => (hA _ (hstep k h2 hk).1).1
  have hlt : ∀ j k, 2 ≤ j → j < k → k ≤ q → a j ≠ a k := by
    intro j k hj hjk hk heq
    obtain ⟨_, l, hl1, hlj, hl⟩ := hstep j hj (by omega)
    obtain ⟨_, _, _, _, hkl⟩ := hstep k (by omega) hk
    have hz : S.IsEdgeEndpoint (a j) (v k) := heq ▸ hkl.2.1
    rcases edgeEndpoint_eq_or_eq S hends (hedge j hj (by omega)) hl hz with h | h
    · have := hinj ⟨by omega, hk⟩ ⟨by omega, by omega⟩ h
      omega
    · have := hinj ⟨by omega, hk⟩ ⟨hl1, by omega⟩ h
      omega
  refine ⟨v, hv1, hbij, a, hstep, ?_, ?_⟩
  · intro j hj k hk heq
    rcases lt_trichotomy j k with h | h | h
    · exact absurd heq (hlt j k hj.1 h hk.2)
    · exact h
    · exact absurd heq.symm (hlt k j hk.1 h hj.2)
  · intro h2
    have hmem : ∀ k, 2 ≤ k → k ≤ q → ∀ x, S.IsEdgeEndpoint (a k) x → x ∈ a k :=
      fun k h2 hk x hx => (hedges S (a k) (hedge k h2 hk)).2.2 x hx
    have hind : ∀ n, 2 ≤ n → n ≤ q → IsConnected (⋃ k ∈ Icc 2 n, a k) ∧
        ∀ i ∈ Icc 1 n, v i ∈ ⋃ k ∈ Icc 2 n, a k := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base =>
        intro hq2
        obtain ⟨_, l, hl1, hl2, hl⟩ := hstep 2 le_rfl hq2
        have hl' : l = 1 := by omega
        subst hl'
        have hU : (⋃ k ∈ Icc 2 2, a k) = a 2 := by simp
        rw [hU]
        refine ⟨(hedges S (a 2) (hedge 2 le_rfl hq2)).2.1, ?_⟩
        intro i hi
        have hi' : i = 1 ∨ i = 2 := by
          have := hi.1
          have := hi.2
          omega
        rcases hi' with rfl | rfl
        · exact hmem 2 le_rfl hq2 _ hl.2.2
        · exact hmem 2 le_rfl hq2 _ hl.2.1
      | succ n hn ih =>
        intro hnq
        obtain ⟨hconn, hcontains⟩ := ih (by omega)
        obtain ⟨_, l, hl1, hln, hl⟩ := hstep (n + 1) (by omega) hnq
        have hU : (⋃ k ∈ Icc 2 (n + 1), a k) = (⋃ k ∈ Icc 2 n, a k) ∪ a (n + 1) := by
          ext x
          simp only [mem_iUnion, mem_union, mem_Icc, exists_prop]
          constructor
          · rintro ⟨k, ⟨hk2, hk⟩, hx⟩
            by_cases hkn : k = n + 1
            · exact Or.inr (hkn ▸ hx)
            · exact Or.inl ⟨k, ⟨hk2, by omega⟩, hx⟩
          · rintro (⟨k, ⟨hk2, hk⟩, hx⟩ | hx)
            · exact ⟨k, ⟨hk2, by omega⟩, hx⟩
            · exact ⟨n + 1, ⟨by omega, le_rfl⟩, hx⟩
        rw [hU]
        have hvl : v l ∈ a (n + 1) := hmem (n + 1) (by omega) hnq _ hl.2.2
        refine ⟨⟨⟨v l, Or.inr hvl⟩, IsPreconnected.union (v l) (hcontains l ⟨hl1, by omega⟩) hvl hconn.2
          (hedges S (a (n + 1)) (hedge (n + 1) (by omega) hnq)).2.1.2⟩, ?_⟩
        intro i hi
        by_cases hin : i = n + 1
        · subst hin
          exact Or.inr (hmem (n + 1) (by omega) hnq _ hl.2.1)
        · exact Or.inl (hcontains i ⟨hi.1, by have := hi.2; omega⟩)
    obtain ⟨hconn, hcontains⟩ := hind q h2 le_rfl
    refine ⟨hconn, ?_⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := hbij.surjOn hx
    exact hcontains i hi
end YangMills.Construction.PeriodicLattice.VertexNumbering
