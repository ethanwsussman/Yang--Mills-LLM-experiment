import YangMills.Construction.Continuum.MultilinearityAndInversionOfTheConnectedFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TestSpaces.CumulantInversion
open SetPartition
section Partitions
variable {α : Type*} [DecidableEq α]
def signedFactorial (t : ℕ) : ℝ := (-1 : ℝ) ^ (t - 1) * ((t - 1).factorial : ℝ)
theorem signedFactorial_one : signedFactorial 1 = 1 := by simp [signedFactorial]
theorem signedFactorial_add_two (q : ℕ) :
    signedFactorial (q + 2) + ((q + 1 : ℕ) : ℝ) * signedFactorial (q + 1) = 0 := by
  simp only [signedFactorial, Nat.add_sub_cancel, show q + 2 - 1 = q + 1 by omega,
    Nat.factorial_succ]
  push_cast
  ring
theorem sup_parts_erase_eq_sdiff {A D : Finset α} (π : Partitions A) (hD : D ∈ π.parts) :
    (π.parts.erase D).sup id = A \ D := by
  ext x
  simp only [Finset.sup_eq_biUnion, Finset.mem_biUnion, Finset.mem_erase, id_eq, Finset.mem_sdiff]
  constructor
  · rintro ⟨C, ⟨hCD, hC⟩, hx⟩
    exact ⟨π.le hC hx, fun hxD => Finset.disjoint_left.1 (π.disjoint hC hD hCD) hx hxD⟩
  · rintro ⟨hxA, hxD⟩
    obtain ⟨t, ht, hxt⟩ := π.exists_mem hxA
    exact ⟨t, ⟨fun h => hxD (h ▸ hxt), ht⟩, hxt⟩
def eraseBlock {A D : Finset α} (π : Partitions A) (hD : D ∈ π.parts) : Partitions (A \ D) :=
  π.ofSubset (Finset.erase_subset D π.parts) (sup_parts_erase_eq_sdiff π hD)
def insertBlock {A D : Finset α} (π : Partitions (A \ D)) (hDA : D ⊆ A) (hD : D.Nonempty) :
    Partitions A :=
  π.extend hD.ne_empty Finset.sdiff_disjoint (Finset.sdiff_union_of_subset hDA)
theorem sum_sum_parts_eq_sum_powerset (A : Finset α) (Φ : Finset α → Finset (Finset α) → ℝ) :
    ∑ π : Partitions A, ∑ D ∈ π.parts, Φ D (π.parts.erase D) =
      ∑ D ∈ A.powerset.filter (fun D => D.Nonempty),
        ∑ π' : Partitions (A \ D), Φ D π'.parts := by
  rw [Finset.sum_comm' (t' := A.powerset.filter (fun D => D.Nonempty))
    (s' := fun D => Finset.univ.filter fun π : Partitions A => D ∈ π.parts)]
  · refine Finset.sum_congr rfl fun D hD => ?_
    obtain ⟨hDA, hDne⟩ := Finset.mem_filter.1 hD
    have hDA' : D ⊆ A := Finset.mem_powerset.1 hDA
    refine Finset.sum_bij'
      (fun π hπ => eraseBlock π (Finset.mem_filter.1 hπ).2)
      (fun π' _ => insertBlock π' hDA' hDne)
      (fun _ _ => Finset.mem_univ _)
      (fun π' _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_insert_self _ _⟩)
      (fun π hπ => Finpartition.ext (Finset.insert_erase (Finset.mem_filter.1 hπ).2))
      (fun π' _ => Finpartition.ext (Finset.erase_insert fun h => ?_))
      (fun _ _ => rfl)
    obtain ⟨x, hx⟩ := hDne
    exact (Finset.mem_sdiff.1 (π'.le h hx)).2 hx
  · intro π D
    simp only [Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => ⟨h, π.le h, π.nonempty_of_mem_parts h⟩, fun h => h.1⟩
theorem sum_parts_ite_mem_eq {A : Finset α} (π : Partitions A) {e : α} (he : e ∈ A)
    (h : Finset α → ℝ) (H : ℝ) (hh : ∀ D ∈ π.parts, e ∈ D → h D = H) :
    ∑ D ∈ π.parts, (if e ∈ D then h D else 0) = H := by
  obtain ⟨t, ⟨ht, het⟩, hu⟩ := π.existsUnique_mem he
  rw [Finset.sum_eq_single_of_mem t ht
    fun D hD hDt => if_neg fun heD => hDt (hu D ⟨hD, heD⟩), if_pos het]
  exact hh t ht het
def blockProductSum (c : Finset α → ℝ) (A : Finset α) : ℝ :=
  ∑ π : Partitions A, ∏ J ∈ π.parts, c J
theorem blockProductSum_empty (c : Finset α → ℝ) : blockProductSum c ∅ = 1 := by
  unfold blockProductSum
  refine (Fintype.sum_eq_single (⊥ : Partitions (∅ : Finset α)) fun π hπ =>
    absurd (Finpartition.ext (by rw [parts_eq_empty_of_empty π, parts_eq_empty_of_empty ⊥])) hπ).trans ?_
  rw [parts_eq_empty_of_empty ⊥, Finset.prod_empty]
theorem sum_powerset_filter_mem {A : Finset α} {e : α} (he : e ∈ A) (g : Finset α → ℝ) :
    ∑ D ∈ A.powerset.filter (fun D => e ∈ D), g D = ∑ D ∈ (A.erase e).powerset, g (A \ D) := by
  refine Finset.sum_nbij' (fun D => A \ D) (fun D => A \ D) ?_ ?_ ?_ ?_ ?_
  · intro D hD
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hD
    refine Finset.mem_powerset.2 fun x hx => ?_
    obtain ⟨hxA, hxD⟩ := Finset.mem_sdiff.1 hx
    exact Finset.mem_erase.2 ⟨fun h => hxD (h ▸ h2), hxA⟩
  · intro D hD
    have hDs := Finset.mem_powerset.1 hD
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 Finset.sdiff_subset,
      Finset.mem_sdiff.2 ⟨he, fun h => ?_⟩⟩
    exact (Finset.mem_erase.1 (hDs h)).1 rfl
  · intro D hD
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 (Finset.mem_filter.1 hD).1)
  · intro D hD
    exact Finset.sdiff_sdiff_eq_self ((Finset.mem_powerset.1 hD).trans (Finset.erase_subset _ _))
  · intro D hD
    rw [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 (Finset.mem_filter.1 hD).1)]
theorem blockProductSum_eq_sum_powerset_erase {A : Finset α} {e : α} (he : e ∈ A)
    (c : Finset α → ℝ) :
    blockProductSum c A = ∑ D ∈ (A.erase e).powerset, c (A \ D) * blockProductSum c D := by
  have key := sum_sum_parts_eq_sum_powerset A fun D R => if e ∈ D then c D * ∏ J ∈ R, c J else 0
  have hl : ∀ π : Partitions A,
      ∑ D ∈ π.parts, (if e ∈ D then c D * ∏ J ∈ π.parts.erase D, c J else 0) =
        ∏ J ∈ π.parts, c J :=
    fun π => sum_parts_ite_mem_eq π he _ _ fun D hD _ => Finset.mul_prod_erase _ _ hD
  simp only [hl] at key
  have hset : A.powerset.filter (fun D => e ∈ D) =
      (A.powerset.filter fun D => D.Nonempty).filter fun D => e ∈ D := by
    ext D
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨⟨h.1, e, h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  have hs := sum_powerset_filter_mem he fun D => c D * blockProductSum c (A \ D)
  have hr : ∑ D ∈ (A.erase e).powerset, c (A \ D) * blockProductSum c (A \ (A \ D)) =
      ∑ D ∈ (A.erase e).powerset, c (A \ D) * blockProductSum c D :=
    Finset.sum_congr rfl fun D hD => by
      rw [Finset.sdiff_sdiff_eq_self
        ((Finset.mem_powerset.1 hD).trans (Finset.erase_subset _ _))]
  rw [← hr, ← hs, hset, Finset.sum_filter]
  unfold blockProductSum at *
  rw [key]
  refine Finset.sum_congr rfl fun D _ => ?_
  by_cases h : e ∈ D
  · simp only [if_pos h, Finset.mul_sum]
  · simp only [if_neg h, Finset.sum_const_zero]
theorem blockProductSum_signedFactorial (m : ℕ) : ∀ E : Finset α, E.card = m →
    blockProductSum (fun W => signedFactorial W.card) E = if m ≤ 1 then 1 else 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro E hE
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · obtain rfl := Finset.card_eq_zero.1 hE
      simpa using blockProductSum_empty _
    obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
    obtain ⟨e, he⟩ : E.Nonempty := Finset.card_pos.1 (by omega)
    have hcard : (E.erase e).card = r := by rw [Finset.card_erase_of_mem he, hE]; rfl
    have h1 : blockProductSum (fun W => signedFactorial W.card) E = ∑ D ∈ (E.erase e).powerset,
        (fun k => signedFactorial (r + 1 - k) * if k ≤ 1 then (1 : ℝ) else 0) D.card := by
      rw [blockProductSum_eq_sum_powerset_erase he]
      refine Finset.sum_congr rfl fun D hD => ?_
      have hsub : D ⊆ E := (Finset.mem_powerset.1 hD).trans (Finset.erase_subset _ _)
      have hDc : D.card ≤ r := hcard ▸ Finset.card_le_card (Finset.mem_powerset.1 hD)
      have hc : (E \ D).card = r + 1 - D.card := by
        have := Finset.card_sdiff_add_card_eq_card hsub
        omega
      simp only [hc]
      rw [ih D.card (by omega) D rfl]
    rw [h1, Finset.sum_powerset_apply_card
      (fun k => signedFactorial (r + 1 - k) * if k ≤ 1 then (1 : ℝ) else 0) (x := E.erase e),
      hcard]
    rcases r with _ | q
    · simp [signedFactorial]
    · rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have hz : ∑ k ∈ Finset.range q, (q + 1).choose (k + 1 + 1) •
          (fun k => signedFactorial (q + 1 + 1 - k) * if k ≤ 1 then (1 : ℝ) else 0) (k + 1 + 1)
            = 0 :=
        Finset.sum_eq_zero fun k _ => by simp
      have hw := signedFactorial_add_two q
      rw [hz]
      simp only [Nat.choose_zero_right, Nat.choose_one_right, zero_add, nsmul_eq_mul]
      simp only [show q + 1 + 1 - 1 = q + 1 by omega, show q + 1 + 1 - 0 = q + 2 by omega]
      norm_num
      push_cast at hw
      linarith
def momentCumulantSum (m : Finset α → ℝ) (B : Finset α) : ℝ :=
  ∑ ρ : Partitions B, signedFactorial ρ.parts.card * ∏ C ∈ ρ.parts, m C
theorem sum_parts_not_mem {A : Finset α} {e : α} (he : e ∈ A) (m : Finset α → ℝ)
    (π : Partitions A) :
    ∑ D ∈ π.parts, (if e ∉ D then
        m D * (signedFactorial (π.parts.erase D).card * ∏ C ∈ π.parts.erase D, m C) else 0) =
      ((π.parts.card : ℝ) - 1) * signedFactorial (π.parts.card - 1) * ∏ C ∈ π.parts, m C := by
  set x := signedFactorial (π.parts.card - 1) * ∏ C ∈ π.parts, m C with hx
  have h1 : ∀ D ∈ π.parts, (if e ∉ D then
      m D * (signedFactorial (π.parts.erase D).card * ∏ C ∈ π.parts.erase D, m C) else 0) =
      x - if e ∈ D then x else 0 := by
    intro D hD
    have hm : m D * (signedFactorial (π.parts.erase D).card * ∏ C ∈ π.parts.erase D, m C) = x := by
      rw [hx, Finset.card_erase_of_mem hD, ← Finset.mul_prod_erase _ _ hD]
      ring
    by_cases h : e ∈ D
    · simp [h]
    · simp [h, hm]
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib,
    sum_parts_ite_mem_eq π he (fun _ => x) x fun _ _ _ => rfl, Finset.sum_const, nsmul_eq_mul, hx]
  ring
theorem sum_partitions_coeff {A : Finset α} (hA : A.Nonempty) (m : Finset α → ℝ) :
    ∑ π : Partitions A, (signedFactorial π.parts.card +
      ((π.parts.card : ℝ) - 1) * signedFactorial (π.parts.card - 1)) * ∏ C ∈ π.parts, m C
        = m A := by
  have hA' : A ≠ ⊥ := hA.ne_empty
  refine (Fintype.sum_eq_single (Finpartition.indiscrete hA') fun π hπ => ?_).trans ?_
  · have hne : π.parts.card ≠ 1 := fun h => hπ <| by
      obtain ⟨B, hB⟩ := Finset.card_eq_one.1 h
      have hBA : B = A := by simpa [hB] using π.sup_parts
      exact Finpartition.ext (by rw [hB, hBA]; rfl)
    have hpos : 0 < π.parts.card := Finset.card_pos.2 (π.parts_nonempty hA')
    obtain ⟨q, hq⟩ : ∃ q, π.parts.card = q + 2 := ⟨π.parts.card - 2, by omega⟩
    have hw := signedFactorial_add_two q
    rw [hq, show q + 2 - 1 = q + 1 by omega]
    push_cast at hw ⊢
    have : signedFactorial (q + 2) + ((q : ℝ) + 2 - 1) * signedFactorial (q + 1) = 0 := by
      linarith
    rw [this, zero_mul]
  · simp [Finpartition.indiscrete, signedFactorial_one]
theorem sum_momentCumulantSum_mul {A : Finset α} {e : α} (he : e ∈ A) (m : Finset α → ℝ) :
    ∑ D ∈ (A.erase e).powerset, momentCumulantSum m (A \ D) * (if D = ∅ then 1 else m D)
      = m A := by
  have hemp : (∅ : Finset α) ∈ (A.erase e).powerset := Finset.empty_mem_powerset _
  rw [← Finset.add_sum_erase _ _ hemp]
  have hset : (A.erase e).powerset.erase ∅ =
      (A.powerset.filter fun D => D.Nonempty).filter fun D => e ∉ D := by
    ext D
    simp only [Finset.mem_erase, Finset.mem_powerset, Finset.mem_filter, Finset.subset_erase]
    constructor
    · rintro ⟨h0, h1, h2⟩
      exact ⟨⟨h1, Finset.nonempty_iff_ne_empty.2 h0⟩, h2⟩
    · rintro ⟨⟨h1, h0⟩, h2⟩
      exact ⟨h0.ne_empty, h1, h2⟩
  have hstep : ∑ D ∈ (A.erase e).powerset.erase ∅,
      momentCumulantSum m (A \ D) * (if D = ∅ then 1 else m D) =
      ∑ π : Partitions A, ((π.parts.card : ℝ) - 1) * signedFactorial (π.parts.card - 1) *
        ∏ C ∈ π.parts, m C := by
    have key := sum_sum_parts_eq_sum_powerset A fun D R =>
      if e ∉ D then m D * (signedFactorial R.card * ∏ C ∈ R, m C) else 0
    simp only [sum_parts_not_mem he m] at key
    rw [key, hset, Finset.sum_filter]
    refine Finset.sum_congr rfl fun D hD => ?_
    have hDne : D ≠ ∅ := (Finset.mem_filter.1 hD).2.ne_empty
    by_cases h : e ∉ D
    · simp only [if_pos h, if_neg hDne, momentCumulantSum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun π _ => by ring
    · simp only [if_neg h, Finset.sum_const_zero]
  rw [hstep, if_pos rfl, mul_one, Finset.sdiff_empty, momentCumulantSum, ← Finset.sum_add_distrib]
  refine Eq.trans (Finset.sum_congr rfl fun π _ => ?_) (sum_partitions_coeff ⟨e, he⟩ m)
  ring
theorem blockProductSum_momentCumulantSum (m : Finset α → ℝ) (k : ℕ) : ∀ A : Finset α,
    A.card = k → A.Nonempty → blockProductSum (momentCumulantSum m) A = m A := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro A hk ⟨e, he⟩
    rw [blockProductSum_eq_sum_powerset_erase he, ← sum_momentCumulantSum_mul he m]
    refine Finset.sum_congr rfl fun D hD => ?_
    by_cases h0 : D = ∅
    · rw [if_pos h0, h0, blockProductSum_empty]
    · rw [if_neg h0]
      have hlt : D.card < k := by
        have h1 := Finset.card_le_card (Finset.mem_powerset.1 hD)
        have h2 := Finset.card_erase_lt_of_mem he
        omega
      rw [ih D.card hlt D rfl (Finset.nonempty_iff_ne_empty.2 h0)]
end Partitions
section Relabelling
variable {E : Type*} [Fintype E] [DecidableEq E] {α : Type*} [DecidableEq α]
omit [DecidableEq E] in
theorem mem_symGraph_partitions {η : Finset (Finset E)} :
    η ∈ ClusterExpansion.SymGraph.partitions E ↔ ClusterExpansion.SymGraph.IsPartition η := by
  simp only [ClusterExpansion.SymGraph.partitions, Finset.mem_filter, Finset.mem_univ, true_and]
omit [DecidableEq E] in
theorem exists_mem_of_isPartition {η : Finset (Finset E)}
    (h : ClusterExpansion.SymGraph.IsPartition η) (y : E) : ∃ K ∈ η, y ∈ K := by
  have hy := Finset.mem_univ y
  rw [← h.2.2] at hy
  simpa using hy
def partitionMap (f : E ↪ α) {η : Finset (Finset E)}
    (h : ClusterExpansion.SymGraph.IsPartition η) : Partitions (Finset.univ.map f) where
  parts := η.image (Finset.map f)
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.2 (by
    intro b hb b' hb' hne
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
    obtain ⟨K', hK', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb')
    exact (Finset.disjoint_map f).2 (h.2.1 hK hK' fun e => hne (by rw [e])))
  sup_parts := by
    ext x
    simp only [Finset.sup_eq_biUnion, Finset.mem_biUnion, Finset.mem_image, id_eq, Finset.mem_map,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨K, _, rfl⟩, hx⟩
      obtain ⟨y, _, rfl⟩ := Finset.mem_map.1 hx
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨K, hK, hyK⟩ := exists_mem_of_isPartition h y
      exact ⟨_, ⟨K, hK, rfl⟩, Finset.mem_map_of_mem f hyK⟩
  bot_notMem := by
    intro hb
    obtain ⟨K, hK, hKe⟩ := Finset.mem_image.1 hb
    exact (h.1 K hK).ne_empty (Finset.map_eq_empty.1 hKe)
theorem sum_partitions_map (f : E ↪ α) (F : Finset (Finset α) → ℝ) :
    ∑ η ∈ ClusterExpansion.SymGraph.partitions E, F (η.image (Finset.map f)) =
      ∑ ρ : Partitions (Finset.univ.map f), F ρ.parts := by
  refine Finset.sum_bij (fun η hη => partitionMap f (mem_symGraph_partitions.1 hη))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro η _ η' _ h
    exact Finset.image_injective (Finset.map_injective f) (congrArg Finpartition.parts h)
  · intro ρ _
    let pre : Finset α → Finset E := fun C => Finset.univ.filter fun y => f y ∈ C
    have hmem : ∀ {C x}, C ∈ ρ.parts → x ∈ C → ∃ y, f y = x ∧ y ∈ pre C := by
      intro C x hC hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 (ρ.le hC hx)
      exact ⟨y, rfl, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩⟩
    have hmap : ∀ C ∈ ρ.parts, (pre C).map f = C := by
      intro C hC
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
        exact (Finset.mem_filter.1 hy).2
      · intro hx
        obtain ⟨y, rfl, hy⟩ := hmem hC hx
        exact Finset.mem_map_of_mem f hy
    have hset : ClusterExpansion.SymGraph.IsPartition (ρ.parts.image pre) := by
      refine ⟨?_, ?_, ?_⟩
      · intro b hb
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hb
        obtain ⟨x, hx⟩ := ρ.nonempty_of_mem_parts hC
        obtain ⟨y, -, hy⟩ := hmem hC hx
        exact ⟨y, hy⟩
      · intro b hb b' hb' hne
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
        obtain ⟨C', hC', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb')
        have hCC : C ≠ C' := fun e => hne (by rw [e])
        refine Finset.disjoint_left.2 fun y hy hy' => ?_
        exact Finset.disjoint_left.1 (ρ.disjoint hC hC' hCC) (Finset.mem_filter.1 hy).2
          (Finset.mem_filter.1 hy').2
      · ext y
        simp only [Finset.mem_biUnion, Finset.mem_image, id_eq, Finset.mem_univ, iff_true]
        obtain ⟨C, hC, hyC⟩ := ρ.exists_mem (Finset.mem_map_of_mem f (Finset.mem_univ y))
        exact ⟨_, ⟨C, hC, rfl⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hyC⟩⟩
    refine ⟨ρ.parts.image pre, mem_symGraph_partitions.2 hset, ?_⟩
    apply Finpartition.ext
    change (ρ.parts.image pre).image (Finset.map f) = ρ.parts
    rw [Finset.image_image]
    ext C
    simp only [Finset.mem_image, Function.comp]
    constructor
    · rintro ⟨C', hC', rfl⟩
      rwa [hmap C' hC']
    · exact fun hC => ⟨C, hC, hmap C hC⟩
theorem sum_partitions_map_of_eq (f : E ↪ α) {J : Finset α} (hJ : Finset.univ.map f = J)
    (F : Finset (Finset α) → ℝ) :
    ∑ η ∈ ClusterExpansion.SymGraph.partitions E, F (η.image (Finset.map f)) =
      ∑ ρ : Partitions J, F ρ.parts := by
  subst hJ
  exact sum_partitions_map f F
end Relabelling
section Tuples
variable {n : ℕ}
def increasingEmb (J : Finset (Fin n)) : Fin J.card ↪ Fin n := (J.orderEmbOfFin rfl).toEmbedding
theorem map_increasingEmb_univ (J : Finset (Fin n)) : Finset.univ.map (increasingEmb J) = J := by
  ext x
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  have h := Finset.range_orderEmbOfFin J rfl
  constructor
  · rintro ⟨t, rfl⟩
    exact Finset.orderEmbOfFin_mem J rfl t
  · intro hx
    have : x ∈ Set.range (J.orderEmbOfFin rfl) := h ▸ hx
    exact this
theorem sepRestrict_sepRestrict (X : SepTupleOfCard n) (J : Finset (Fin n))
    (K : Finset (Fin J.card)) :
    (⟨K.card, sepRestrict (sepRestrict X J) K⟩ : SepTuple) =
      ⟨(K.map (increasingEmb J)).card, sepRestrict X (K.map (increasingEmb J))⟩ := by
  have hc : (K.map (increasingEmb J)).card = K.card := Finset.card_map _
  refine sepTuple_ext _ _ hc.symm fun t => ?_
  have hu := Finset.orderEmbOfFin_unique (s := K.map (increasingEmb J)) rfl
    (f := fun u => J.orderEmbOfFin rfl (K.orderEmbOfFin rfl (Fin.cast hc u)))
    (fun u => Finset.mem_map.2 ⟨_, Finset.orderEmbOfFin_mem K rfl _, rfl⟩)
    (fun a b hab => (J.orderEmbOfFin rfl).strictMono ((K.orderEmbOfFin rfl).strictMono hab))
  have h : (K.map (increasingEmb J)).orderEmbOfFin rfl (Fin.cast hc.symm t) =
      J.orderEmbOfFin rfl (K.orderEmbOfFin rfl t) := (congrFun hu (Fin.cast hc.symm t)).symm
  simp only [sepRestrict, SchwingerFunctions.restrictTuple, h]
theorem cumulant_sepRestrict (σ : SepTuple → ℝ) (X : SepTupleOfCard n) (J : Finset (Fin n)) :
    cumulant σ (sepRestrict X J) =
      momentCumulantSum (fun C => σ ⟨C.card, sepRestrict X C⟩) J := by
  have key := sum_partitions_map_of_eq (increasingEmb J) (map_increasingEmb_univ J)
    fun R => signedFactorial R.card * ∏ C ∈ R, σ ⟨C.card, sepRestrict X C⟩
  refine Eq.trans (Finset.sum_congr rfl fun η _ => ?_) key
  have hinj := Finset.map_injective (increasingEmb J)
  rw [Finset.card_image_of_injective _ hinj, Finset.prod_image fun _ _ _ _ h => hinj h]
  refine congrArg _ (Finset.prod_congr rfl fun K _ => ?_)
  rw [sepRestrict_sepRestrict]
def extendFamily (S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ) (Y : SepTuple) : ℝ :=
  if h : 2 ≤ Y.1 then S Y.1 h Y.2 else 0
theorem extendFamily_mk (S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ) {m : ℕ} (h : 2 ≤ m)
    (Y : SepTupleOfCard m) : extendFamily S ⟨m, Y⟩ = S m h Y :=
  dif_pos h
theorem centredOfCumulants_eq (S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ) {k : ℕ}
    (Y : SepTupleOfCard k) :
    centredOfCumulants S ⟨k, Y⟩ = ∑ η ∈ ClusterExpansion.SymGraph.partitions (Fin k),
      if ∀ K ∈ η, 2 ≤ K.card then ∏ K ∈ η, extendFamily S ⟨K.card, sepRestrict Y K⟩ else 0 := by
  have hf : (ClusterExpansion.SymGraph.partitions (Fin k)).filter
      (fun η => ∀ K ∈ η, 2 ≤ K.card) = partitionsNoSingletons (Fin k) := by
    ext η
    simp only [partitionsNoSingletons, Finset.mem_filter]
  rw [← Finset.sum_filter, hf]
  rw [← Finset.sum_attach (partitionsNoSingletons (Fin k))]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [← Finset.prod_attach η.1]
  exact Finset.prod_congr rfl fun J _ =>
    (extendFamily_mk S (two_le_card_of_mem_partitionsNoSingletons η.2 J.2) _).symm
theorem sum_atLeastTwoPartitions_eq (S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ)
    (X : SepTupleOfCard n) (J : Finset (Fin n)) :
    ∑ ρ ∈ (atLeastTwoPartitions J).attach, ∏ C ∈ ρ.1.parts.attach,
        S C.1.card (two_le_card_of_mem_atLeastTwoPartitions ρ.2 C.2) (sepRestrict X C.1) =
      ∑ ρ : Partitions J, if ∀ C ∈ ρ.parts, 2 ≤ C.card then
        ∏ C ∈ ρ.parts, extendFamily S ⟨C.card, sepRestrict X C⟩ else 0 := by
  have hf : (Finset.univ.filter fun ρ : Partitions J => ∀ C ∈ ρ.parts, 2 ≤ C.card) =
      atLeastTwoPartitions J := by
    ext ρ
    simp only [mem_atLeastTwoPartitions, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← Finset.sum_filter, hf]
  rw [← Finset.sum_attach (atLeastTwoPartitions J)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [← Finset.prod_attach ρ.1.parts]
  exact Finset.prod_congr rfl fun C _ =>
    (extendFamily_mk S (two_le_card_of_mem_atLeastTwoPartitions ρ.2 C.2) _).symm
theorem centredOfCumulants_sepRestrict (S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ)
    (X : SepTupleOfCard n) (J : Finset (Fin n)) :
    CentredRestrictFormula S X J := by
  unfold CentredRestrictFormula
  rw [sum_atLeastTwoPartitions_eq, centredOfCumulants_eq]
  have key := sum_partitions_map_of_eq (increasingEmb J) (map_increasingEmb_univ J)
    fun R => if ∀ C ∈ R, 2 ≤ C.card then
      ∏ C ∈ R, extendFamily S ⟨C.card, sepRestrict X C⟩ else 0
  refine Eq.trans (Finset.sum_congr rfl fun η _ => ?_) key
  have hinj := Finset.map_injective (increasingEmb J)
  have hiff : (∀ C ∈ η.image (Finset.map (increasingEmb J)), 2 ≤ C.card) ↔
      ∀ K ∈ η, 2 ≤ K.card := by
    simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      Finset.card_map]
  by_cases h : ∀ K ∈ η, 2 ≤ K.card
  · rw [if_pos h, if_pos (hiff.2 h), Finset.prod_image fun _ _ _ _ h => hinj h]
    refine Finset.prod_congr rfl fun K _ => ?_
    rw [sepRestrict_sepRestrict]
  · rw [if_neg h, if_neg (mt hiff.1 h)]
theorem sepRestrict_eq_of_notMem {X X' : SepTupleOfCard n} {i : Fin n}
    (h : ∀ j, j ≠ i → X.1 j = X'.1 j) {J : Finset (Fin n)} (hJ : i ∉ J) :
    sepRestrict X J = sepRestrict X' J :=
  Subtype.ext (funext fun k => h _ fun e => hJ (e ▸ Finset.orderEmbOfFin_mem J rfl k))
theorem prod_blocks_linear_combination (Ψ : SepTuple → ℝ) {η : Finset (Finset (Fin n))}
    {J₀ : Finset (Fin n)} {i : Fin n} (hJ₀ : J₀ ∈ η) (hi : i ∈ J₀)
    (huniq : ∀ J ∈ η, J ≠ J₀ → i ∉ J)
    (hΨ : IsMultilinearOnSep fun Y : SepTupleOfCard J₀.card => Ψ ⟨_, Y⟩) {b b' : ℝ}
    {X X' X'' : SepTupleOfCard n} (h₁ : ∀ j, j ≠ i → X.1 j = X'.1 j)
    (h₂ : X''.1 i = b • X.1 i + b' • X'.1 i) (h₃ : ∀ j, j ≠ i → X''.1 j = X.1 j) :
    ∏ J ∈ η, Ψ ⟨J.card, sepRestrict X'' J⟩ =
      b * ∏ J ∈ η, Ψ ⟨J.card, sepRestrict X J⟩ + b' * ∏ J ∈ η, Ψ ⟨J.card, sepRestrict X' J⟩ := by
  have hX' : ∏ J ∈ η.erase J₀, Ψ ⟨J.card, sepRestrict X' J⟩ =
      ∏ J ∈ η.erase J₀, Ψ ⟨J.card, sepRestrict X J⟩ :=
    Finset.prod_congr rfl fun J hJ => by
      rw [sepRestrict_eq_of_notMem h₁
        (huniq J (Finset.mem_of_mem_erase hJ) (Finset.ne_of_mem_erase hJ))]
  have hX'' : ∏ J ∈ η.erase J₀, Ψ ⟨J.card, sepRestrict X'' J⟩ =
      ∏ J ∈ η.erase J₀, Ψ ⟨J.card, sepRestrict X J⟩ :=
    Finset.prod_congr rfl fun J hJ => by
      rw [sepRestrict_eq_of_notMem h₃
        (huniq J (Finset.mem_of_mem_erase hJ) (Finset.ne_of_mem_erase hJ))]
  obtain ⟨t, ht⟩ : ∃ t, J₀.orderEmbOfFin rfl t = i := by
    have hm : i ∈ Finset.univ.map (increasingEmb J₀) := by rw [map_increasingEmb_univ]; exact hi
    obtain ⟨t, -, ht⟩ := Finset.mem_map.1 hm
    exact ⟨t, ht⟩
  have hne : ∀ u, u ≠ t → J₀.orderEmbOfFin rfl u ≠ i := fun u hu e =>
    hu ((J₀.orderEmbOfFin rfl).injective (e.trans ht.symm))
  have hm : Ψ ⟨_, sepRestrict X'' J₀⟩ =
      b * Ψ ⟨_, sepRestrict X J₀⟩ + b' * Ψ ⟨_, sepRestrict X' J₀⟩ := by
    refine hΨ t b b' (sepRestrict X J₀) (sepRestrict X' J₀) (sepRestrict X'' J₀)
      (fun u hu => h₁ _ (hne u hu)) ?_ (fun u hu => h₃ _ (hne u hu))
    change X''.1 (J₀.orderEmbOfFin rfl t) =
      b • X.1 (J₀.orderEmbOfFin rfl t) + b' • X'.1 (J₀.orderEmbOfFin rfl t)
    rw [ht]
    exact h₂
  rw [← Finset.mul_prod_erase η _ hJ₀, ← Finset.mul_prod_erase η _ hJ₀,
    ← Finset.mul_prod_erase η (fun J => Ψ ⟨J.card, sepRestrict X' J⟩) hJ₀, hm, hX', hX'']
  ring
theorem exists_block_mem {η : Finset (Finset (Fin n))}
    (h : ClusterExpansion.SymGraph.IsPartition η) (i : Fin n) :
    ∃ J₀ ∈ η, i ∈ J₀ ∧ ∀ J ∈ η, J ≠ J₀ → i ∉ J := by
  obtain ⟨J₀, hJ₀, hiJ₀⟩ := exists_mem_of_isPartition h i
  exact ⟨J₀, hJ₀, hiJ₀, fun J hJ hne hiJ =>
    Finset.disjoint_left.1 (h.2.1 hJ hJ₀ hne) hiJ hiJ₀⟩
theorem isMultilinearOnSep_cumulant {σ : SepTuple → ℝ} (hσ : IsSepFunctional σ) (n : ℕ) :
    IsMultilinearOnSep fun X : SepTupleOfCard n => cumulant σ X := by
  intro i b b' X X' X'' h₁ h₂ h₃
  simp only [cumulant]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun η hη => ?_
  obtain ⟨J₀, hJ₀, hi, hu⟩ := exists_block_mem (mem_symGraph_partitions.1 hη) i
  rw [prod_blocks_linear_combination σ hJ₀ hi hu (hσ.2 _ (Finset.card_pos.2 ⟨i, hi⟩)) h₁ h₂ h₃]
  ring
theorem isMultilinearOnSep_centredOfCumulants {S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ}
    (hS : ∀ p (hp : 2 ≤ p), IsMultilinearOnSep (S p hp)) (n : ℕ) :
    IsMultilinearOnSep fun X : SepTupleOfCard n => centredOfCumulants S ⟨n, X⟩ := by
  intro i b b' X X' X'' h₁ h₂ h₃
  simp only [centredOfCumulants_eq]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun η hη => ?_
  by_cases h : ∀ K ∈ η, 2 ≤ K.card
  · obtain ⟨J₀, hJ₀, hi, hu⟩ := exists_block_mem (mem_symGraph_partitions.1 hη) i
    have hc := h J₀ hJ₀
    have hΨ : IsMultilinearOnSep fun Y : SepTupleOfCard J₀.card => extendFamily S ⟨_, Y⟩ := by
      have he : (fun Y : SepTupleOfCard J₀.card => extendFamily S ⟨_, Y⟩) = S _ hc :=
        funext fun Y => extendFamily_mk S hc Y
      rw [he]
      exact hS _ hc
    simp only [if_pos h]
    exact prod_blocks_linear_combination _ hJ₀ hi hu hΨ h₁ h₂ h₃
  · simp only [if_neg h, mul_zero, add_zero]
theorem isSepFunctional_centredOfCumulants {S : (n : ℕ) → 2 ≤ n → SepTupleOfCard n → ℝ}
    (hS : ∀ p (hp : 2 ≤ p), IsMultilinearOnSep (S p hp)) :
    IsSepFunctional (centredOfCumulants S) :=
  ⟨centredOfCumulants_nil S, fun n _ => isMultilinearOnSep_centredOfCumulants hS n⟩
theorem momentCumulantInversion_holds (σ : SepTuple → ℝ) (hn : 1 ≤ n) (X : SepTupleOfCard n) :
    MomentCumulantInversion σ X := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have h := blockProductSum_momentCumulantSum (fun C => σ ⟨C.card, sepRestrict X C⟩) _
    Finset.univ rfl hne
  unfold MomentCumulantInversion
  simp only [cumulant_sepRestrict]
  rw [sepRestrict_univ] at h
  exact h.symm
end Tuples
theorem cumulantMultilinearInversion : CumulantMultilinearInversion := by
  refine ⟨fun σ hσ S => ⟨fun n _ X J => ⟨fun _ => ?_, centredOfCumulants_sepRestrict S X J⟩,
    fun n _ => isMultilinearOnSep_cumulant hσ n, isSepFunctional_centredOfCumulants,
    isSepFunctional_centredOfCumulants fun p _ => isMultilinearOnSep_cumulant hσ p,
    fun n hn X => momentCumulantInversion_holds σ hn X⟩, fun α _ E => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact cumulant_sepRestrict σ X J
  · exact (blockProductSum_signedFactorial 1 E h).trans (if_pos le_rfl)
  · have := blockProductSum_signedFactorial E.card E rfl
    rw [if_neg (by omega)] at this
    exact this
end YangMills.Construction.TestSpaces.CumulantInversion
