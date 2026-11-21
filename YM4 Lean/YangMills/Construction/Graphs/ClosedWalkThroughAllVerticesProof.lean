import YangMills.Construction.Graphs.ClosedWalkThroughAllVertices
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Graphs
namespace ClosedWalkGrowth
variable {α β : Type}
def seqRange (u : ℕ → α) (n : ℕ) : Set α := {v | ∃ t ≤ n, u t = v}
def insertDetour (u : ℕ → α) (i : ℕ) (y : α) (t : ℕ) : α :=
  if t ≤ i then u t else if t = i + 1 then y else if t = i + 2 then u i else u (t - 2)
lemma insertDetour_of_le (u : ℕ → α) {i t : ℕ} (y : α) (h : t ≤ i) :
    insertDetour u i y t = u t := by
  simp [insertDetour, h]
lemma insertDetour_succ (u : ℕ → α) (i : ℕ) (y : α) : insertDetour u i y (i + 1) = y := by
  simp [insertDetour]
lemma insertDetour_add_two (u : ℕ → α) (i : ℕ) (y : α) : insertDetour u i y (i + 2) = u i := by
  simp [insertDetour]
lemma insertDetour_of_ge (u : ℕ → α) {i t : ℕ} (y : α) (h : i + 3 ≤ t) :
    insertDetour u i y t = u (t - 2) := by
  rw [insertDetour, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
lemma seqRange_insertDetour (u : ℕ → α) {i n : ℕ} (y : α) (hi : i ≤ n) :
    seqRange (insertDetour u i y) (n + 2) = insert y (seqRange u n) := by
  ext v
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases h1 : t ≤ i
    · rw [insertDetour_of_le u y h1]
      exact Or.inr ⟨t, by omega, rfl⟩
    by_cases h2 : t = i + 1
    · subst h2
      rw [insertDetour_succ]
      exact Or.inl rfl
    by_cases h3 : t = i + 2
    · subst h3
      rw [insertDetour_add_two]
      exact Or.inr ⟨i, hi, rfl⟩
    rw [insertDetour_of_ge u y (by omega)]
    exact Or.inr ⟨t - 2, by omega, rfl⟩
  · rintro (rfl | ⟨t, ht, rfl⟩)
    · exact ⟨i + 1, by omega, insertDetour_succ u i _⟩
    by_cases h1 : t ≤ i
    · exact ⟨t, by omega, insertDetour_of_le u y h1⟩
    · refine ⟨t + 2, by omega, ?_⟩
      rw [insertDetour_of_ge u y (by omega)]
      rfl
structure WalkStage (G : Graph α β) (r : α) (k : ℕ) (F : Set β) (u : ℕ → α) : Prop where
  subset_edgeSet : F ⊆ G.edgeSet
  ncard_eq : F.ncard = k
  head_eq : u 0 = r
  tail_eq : u (2 * k) = r
  mem_vertexSet : ∀ t ≤ 2 * k, u t ∈ G.vertexSet
  adj_step : ∀ t : ℕ, 1 ≤ t → t ≤ 2 * k → G.Adj (u (t - 1)) (u t)
  ends_mem : ∀ e ∈ F, ∀ x y, G.IsLink e x y → x ∈ seqRange u (2 * k)
  ncard_range_le : (seqRange u (2 * k)).ncard ≤ k + 1
lemma exists_adj_mem_not_mem {G : Graph α β} (hG : MultigraphPathConnected G) {S : Set α}
    {x y : α} (hx : x ∈ G.vertexSet) (hy : y ∈ G.vertexSet) (hxS : x ∈ S) (hyS : y ∉ S) :
    ∃ a b, a ∈ S ∧ b ∉ S ∧ G.Adj a b := by
  obtain ⟨n, p, h0, hn, hstep⟩ := hG x hx y hy
  by_contra hno
  have hall : ∀ i ≤ n, p i ∈ S := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact hxS
    | succ i ih =>
      intro hi
      by_contra hout
      exact hno ⟨p i, p (i + 1), ih (by omega), hout, hstep i (by omega)⟩
  exact hyS (hn ▸ hall n le_rfl)
lemma WalkStage.extend {G : Graph α β} {r : α} {k : ℕ} {F : Set β} {u : ℕ → α}
    (h : WalkStage G r k F u) (hE : G.edgeSet.Finite) {e : β} {x y : α} (he : e ∉ F)
    (hl : G.IsLink e x y) (hx : x ∈ seqRange u (2 * k)) :
    ∃ F' u', WalkStage G r (k + 1) F' u' := by
  obtain ⟨i, hi, rfl⟩ := hx
  have h2 : 2 * (k + 1) = 2 * k + 2 := by ring
  have hrange := seqRange_insertDetour u y hi
  have hV : ∀ v ∈ seqRange (insertDetour u i y) (2 * k + 2), v ∈ G.vertexSet := by
    intro v hv
    rw [hrange] at hv
    rcases hv with rfl | ⟨t, ht, rfl⟩
    · exact hl.right_mem
    · exact h.mem_vertexSet t ht
  refine ⟨insert e F, insertDetour u i y, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact Set.insert_subset hl.edge_mem h.subset_edgeSet
  · rw [Set.ncard_insert_of_notMem he (hE.subset h.subset_edgeSet), h.ncard_eq]
  · rw [insertDetour_of_le u y (Nat.zero_le i)]
    exact h.head_eq
  · rw [h2]
    by_cases hlast : i = 2 * k
    · subst hlast
      rw [insertDetour_add_two]
      exact h.tail_eq
    · rw [insertDetour_of_ge u y (by omega), Nat.add_sub_cancel]
      exact h.tail_eq
  · intro t ht
    rw [h2] at ht
    exact hV _ ⟨t, ht, rfl⟩
  · intro t h1 ht
    rw [h2] at ht
    by_cases c1 : t ≤ i
    · rw [insertDetour_of_le u y c1, insertDetour_of_le u y (by omega)]
      exact h.adj_step t h1 (by omega)
    by_cases c2 : t = i + 1
    · subst c2
      rw [Nat.add_sub_cancel, insertDetour_of_le u y le_rfl, insertDetour_succ]
      exact hl.adj
    by_cases c3 : t = i + 2
    · subst c3
      rw [show i + 2 - 1 = i + 1 by omega, insertDetour_succ, insertDetour_add_two]
      exact hl.symm.adj
    by_cases c4 : t = i + 3
    · subst c4
      rw [show i + 3 - 1 = i + 2 by omega, insertDetour_add_two, insertDetour_of_ge u y le_rfl,
        show i + 3 - 2 = i + 1 by omega]
      simpa using h.adj_step (i + 1) (by omega) (by omega)
    rw [insertDetour_of_ge u y (t := t - 1) (by omega), insertDetour_of_ge u y (by omega),
      show t - 1 - 2 = t - 2 - 1 by omega]
    exact h.adj_step (t - 2) (by omega) (by omega)
  · intro e' he' a b hab
    rw [h2, hrange]
    rcases he' with rfl | he'
    · rcases hl.eq_and_eq_or_eq_and_eq hab with ⟨h1, _⟩ | ⟨_, h1⟩
      · exact Or.inr ⟨i, hi, h1⟩
      · exact Or.inl h1.symm
    · exact Or.inr (h.ends_mem e' he' a b hab)
  · rw [h2, hrange]
    exact (Set.ncard_insert_le y _).trans (by have := h.ncard_range_le; omega)
lemma exists_walkStage {G : Graph α β} (hE : G.edgeSet.Finite) (hG : MultigraphPathConnected G)
    {r : α} (hr : r ∈ G.vertexSet) : ∀ k ≤ G.edgeSet.ncard, ∃ F u, WalkStage G r k F u := by
  intro k
  induction k with
  | zero =>
    intro _
    have hrange : seqRange (fun _ : ℕ => r) (2 * 0) = {r} := by
      ext v
      simp [seqRange, eq_comm]
    refine ⟨∅, fun _ => r, ⟨by simp, by simp, rfl, rfl, fun _ _ => hr, ?_, by simp, ?_⟩⟩
    · intro t h1 ht
      omega
    · rw [hrange]
      simp
  | succ k ih =>
    intro hk
    obtain ⟨F, u, h⟩ := ih (by omega)
    have hout : ∃ e ∈ G.edgeSet, e ∉ F := by
      by_contra hno
      have hsub : G.edgeSet ⊆ F := fun e he => by
        by_contra heF
        exact hno ⟨e, he, heF⟩
      have := Set.ncard_le_ncard hsub (hE.subset h.subset_edgeSet)
      have := h.ncard_eq
      omega
    obtain ⟨e, heE, heF⟩ := hout
    obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet heE
    by_cases ha : a ∈ seqRange u (2 * k)
    · exact h.extend hE heF hab ha
    obtain ⟨a', b', ha', hb', f, hf⟩ :=
      exists_adj_mem_not_mem hG hr hab.left_mem
        (⟨0, Nat.zero_le _, h.head_eq⟩ : r ∈ seqRange u (2 * k)) ha
    exact h.extend hE (fun hfF => hb' (h.ends_mem f hfF b' a' hf.symm)) hf ha'
end ClosedWalkGrowth
open ClosedWalkGrowth in
theorem exists_closedWalkThroughAllVertices : ExistsClosedWalkThroughAllVertices := by
  intro α β G hV hE _ hG E hcard r hr
  obtain ⟨F, u, h⟩ := exists_walkStage hE hG hr E hcard.ge
  have hF : F = G.edgeSet :=
    Set.eq_of_subset_of_ncard_le h.subset_edgeSet (by rw [h.ncard_eq, hcard]) hE
  have hall : G.vertexSet ⊆ seqRange u (2 * E) := by
    intro v hv
    by_contra hout
    obtain ⟨a, b, _, hb, e, hl⟩ :=
      exists_adj_mem_not_mem hG hr hv
        (⟨0, Nat.zero_le _, h.head_eq⟩ : r ∈ seqRange u (2 * E)) hout
    exact hb (h.ends_mem e (hF ▸ hl.edge_mem) b a hl.symm)
  have hfin : (seqRange u (2 * E)).Finite :=
    hV.subset fun v ⟨t, ht, hv⟩ => hv ▸ h.mem_vertexSet t ht
  refine ⟨(Set.ncard_le_ncard hall hfin).trans h.ncard_range_le, u, h.head_eq, h.tail_eq,
    h.mem_vertexSet, ?_, h.adj_step⟩
  intro v hv
  obtain ⟨t, ht, rfl⟩ := hall hv
  exact ⟨t, ht, rfl⟩
end YangMills.Construction.Graphs
