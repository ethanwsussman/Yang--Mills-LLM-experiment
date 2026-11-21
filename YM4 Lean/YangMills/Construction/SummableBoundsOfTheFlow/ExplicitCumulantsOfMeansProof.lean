import YangMills.Construction.SummableBoundsOfTheFlow.ExplicitCumulantsOfMeans
import Mathlib
set_option autoImplicit false
noncomputable section
open Finset YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.Cumulants
def partitionWeight {p : ℕ} (m : Finset (Fin p) → ℝ) (P : Finset (Finset (Fin p))) : ℝ :=
  (-1 : ℝ) ^ (P.card - 1) * ((P.card - 1).factorial : ℝ) * ∏ J ∈ P, m J
theorem exists_finpartition_parts_eq {p : ℕ} (P : Finset (Finset (Fin p))) (hne : ∀ B ∈ P, B.Nonempty)
    (hdisj : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) (hcov : ∀ i, ∃ B ∈ P, i ∈ B) :
    ∃ π : Finpartition (univ : Finset (Fin p)), π.parts = P := by
  refine ⟨⟨P, Finset.supIndep_iff_pairwiseDisjoint.mpr fun B hB C hC hBC => hdisj B hB C hC hBC, ?_, ?_⟩, rfl⟩
  · ext i
    simp only [Finset.mem_sup, id, mem_univ, iff_true]
    exact hcov i
  · intro h
    exact not_nonempty_empty (hne _ h)
theorem sum_finpartition_eq_sum_partitionWeight {p : ℕ} (S : Finset (Finset (Finset (Fin p))))
    (hS : ∀ P ∈ S, ∃ π : Finpartition (univ : Finset (Fin p)), π.parts = P)
    (hmem : ∀ π : Finpartition (univ : Finset (Fin p)), π.parts ∈ S) (m : Finset (Fin p) → ℝ) :
    ∑ π : Finpartition (univ : Finset (Fin p)),
      (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) * ∏ J ∈ π.parts, m J =
    ∑ P ∈ S, partitionWeight m P := by
  refine sum_nbij (fun π => π.parts) (fun π _ => hmem π) ?_ ?_ ?_
  · intro π _ σ _ h
    exact Finpartition.ext h
  · intro P hP
    obtain ⟨π, hπ⟩ := hS P hP
    exact ⟨π, mem_coe.mpr (mem_univ π), hπ⟩
  · intro π _
    rfl
theorem part_eq_or_disjoint {p : ℕ} (π : Finpartition (univ : Finset (Fin p))) (i j : Fin p) :
    π.part i = π.part j ∨ Disjoint (π.part i) (π.part j) := by
  by_cases h : π.part i = π.part j
  · exact Or.inl h
  · exact Or.inr (π.disjoint (π.part_mem.mpr (mem_univ i)) (π.part_mem.mpr (mem_univ j)) h)
theorem parts_eq_image_part {p : ℕ} (π : Finpartition (univ : Finset (Fin p))) :
    π.parts = univ.image π.part := by
  ext J
  constructor
  · intro hJ
    obtain ⟨a, ha⟩ := π.nonempty_of_mem_parts hJ
    exact mem_image.mpr ⟨a, mem_univ a, π.part_eq_of_mem hJ ha⟩
  · intro hJ
    obtain ⟨a, -, rfl⟩ := mem_image.mp hJ
    exact π.part_mem.mpr (mem_univ a)
def partitionsFinTwo : Finset (Finset (Finset (Fin 2))) := {{{0, 1}}, {{0}, {1}}}
def partitionsFinThree : Finset (Finset (Finset (Fin 3))) :=
  {{{0, 1, 2}}, {{0, 1}, {2}}, {{0, 2}, {1}}, {{1, 2}, {0}}, {{0}, {1}, {2}}}
def partitionsFinFour : Finset (Finset (Finset (Fin 4))) :=
  {{{0, 1, 2, 3}},
   {{0, 1, 2}, {3}}, {{0, 1, 3}, {2}}, {{0, 2, 3}, {1}}, {{1, 2, 3}, {0}},
   {{0, 1}, {2, 3}}, {{0, 2}, {1, 3}}, {{0, 3}, {1, 2}},
   {{0, 1}, {2}, {3}}, {{0, 2}, {1}, {3}}, {{0, 3}, {1}, {2}},
   {{1, 2}, {0}, {3}}, {{1, 3}, {0}, {2}}, {{2, 3}, {0}, {1}},
   {{0}, {1}, {2}, {3}}}
def EqOrDisjoint {p : ℕ} (s t : Finset (Fin p)) : Prop := s = t ∨ Disjoint s t
instance decidableRelEqOrDisjoint {p : ℕ} : DecidableRel (EqOrDisjoint (p := p)) := fun s t => by
  unfold EqOrDisjoint
  infer_instance
set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 0 in
theorem blocks_mem_partitionsFinTwo : ∀ s₀ : Finset (Fin 2), 0 ∈ s₀ → ∀ s₁ : Finset (Fin 2), 1 ∈ s₁ →
    EqOrDisjoint s₀ s₁ →
    ({s₀, s₁} : Finset (Finset (Fin 2))) ∈ partitionsFinTwo := by
  decide +kernel
set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 0 in
theorem blocks_mem_partitionsFinThree : ∀ s₀ : Finset (Fin 3), 0 ∈ s₀ → ∀ s₁ : Finset (Fin 3), 1 ∈ s₁ →
    EqOrDisjoint s₀ s₁ →
    ∀ s₂ : Finset (Fin 3), 2 ∈ s₂ → EqOrDisjoint s₀ s₂ → EqOrDisjoint s₁ s₂ →
    ({s₀, s₁, s₂} : Finset (Finset (Fin 3))) ∈ partitionsFinThree := by
  decide +kernel
set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 0 in
theorem blocks_mem_partitionsFinFour : ∀ s₀ : Finset (Fin 4), 0 ∈ s₀ → ∀ s₁ : Finset (Fin 4), 1 ∈ s₁ →
    EqOrDisjoint s₀ s₁ →
    ∀ s₂ : Finset (Fin 4), 2 ∈ s₂ → EqOrDisjoint s₀ s₂ → EqOrDisjoint s₁ s₂ →
    ∀ s₃ : Finset (Fin 4), 3 ∈ s₃ → EqOrDisjoint s₀ s₃ → EqOrDisjoint s₁ s₃ → EqOrDisjoint s₂ s₃ →
    ({s₀, s₁, s₂, s₃} : Finset (Finset (Fin 4))) ∈ partitionsFinFour := by
  decide +kernel
theorem partitionsFinTwo_isPartition : ∀ P ∈ partitionsFinTwo, (∀ B ∈ P, B.Nonempty) ∧
    (∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) ∧ ∀ i : Fin 2, ∃ B ∈ P, i ∈ B := by
  intro P hP
  simp only [partitionsFinTwo, mem_insert, mem_singleton] at hP
  rcases hP with rfl | rfl <;> decide +kernel
theorem partitionsFinThree_isPartition : ∀ P ∈ partitionsFinThree, (∀ B ∈ P, B.Nonempty) ∧
    (∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) ∧ ∀ i : Fin 3, ∃ B ∈ P, i ∈ B := by
  intro P hP
  simp only [partitionsFinThree, mem_insert, mem_singleton] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem partitionsFinFour_isPartition : ∀ P ∈ partitionsFinFour, (∀ B ∈ P, B.Nonempty) ∧
    (∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) ∧ ∀ i : Fin 4, ∃ B ∈ P, i ∈ B := by
  intro P hP
  simp only [partitionsFinFour, mem_insert, mem_singleton] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide +kernel
theorem mem_part_self_univ {p : ℕ} (π : Finpartition (univ : Finset (Fin p))) (i : Fin p) : i ∈ π.part i :=
  π.mem_part_self.mpr (mem_univ i)
theorem parts_mem_partitionsFinTwo (π : Finpartition (univ : Finset (Fin 2))) :
    π.parts ∈ partitionsFinTwo := by
  have h := blocks_mem_partitionsFinTwo _ (mem_part_self_univ π 0) _ (mem_part_self_univ π 1)
    (part_eq_or_disjoint π 0 1)
  have e : π.parts = {π.part 0, π.part 1} := by
    rw [parts_eq_image_part]
    ext J
    simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton, Fin.exists_fin_two]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  rw [e]
  exact h
theorem parts_mem_partitionsFinThree (π : Finpartition (univ : Finset (Fin 3))) :
    π.parts ∈ partitionsFinThree := by
  have h := blocks_mem_partitionsFinThree _ (mem_part_self_univ π 0) _ (mem_part_self_univ π 1)
    (part_eq_or_disjoint π 0 1) _ (mem_part_self_univ π 2)
    (part_eq_or_disjoint π 0 2) (part_eq_or_disjoint π 1 2)
  have e : π.parts = {π.part 0, π.part 1, π.part 2} := by
    rw [parts_eq_image_part]
    ext J
    simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      fin_cases a <;> simp
    · rintro (h | h | h)
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
  rw [e]
  exact h
theorem parts_mem_partitionsFinFour (π : Finpartition (univ : Finset (Fin 4))) :
    π.parts ∈ partitionsFinFour := by
  have h := blocks_mem_partitionsFinFour _ (mem_part_self_univ π 0) _ (mem_part_self_univ π 1)
    (part_eq_or_disjoint π 0 1) _ (mem_part_self_univ π 2)
    (part_eq_or_disjoint π 0 2) (part_eq_or_disjoint π 1 2) _ (mem_part_self_univ π 3)
    (part_eq_or_disjoint π 0 3) (part_eq_or_disjoint π 1 3) (part_eq_or_disjoint π 2 3)
  have e : π.parts = {π.part 0, π.part 1, π.part 2, π.part 3} := by
    rw [parts_eq_image_part]
    ext J
    simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      fin_cases a <;> simp
    · rintro (h | h | h | h)
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
      · exact ⟨3, h.symm⟩
  rw [e]
  exact h
theorem sum_partitionsFinTwo_partitionWeight (m : Finset (Fin 2) → ℝ) :
    ∑ P ∈ partitionsFinTwo, partitionWeight m P = m {0, 1} - m {0} * m {1} := by
  simp (disch := decide +kernel) only [partitionsFinTwo, partitionWeight, sum_insert, sum_singleton,
    card_insert_of_notMem, card_singleton, prod_insert, prod_singleton]
  norm_num [Nat.factorial]
  ring
theorem sum_partitionsFinThree_partitionWeight (m : Finset (Fin 3) → ℝ) :
    ∑ P ∈ partitionsFinThree, partitionWeight m P =
    m {0, 1, 2} - m {0, 1} * m {2} - m {0, 2} * m {1} - m {1, 2} * m {0} +
      2 * (m {0} * m {1} * m {2}) := by
  simp (disch := decide +kernel) only [partitionsFinThree, partitionWeight, sum_insert, sum_singleton,
    card_insert_of_notMem, card_singleton, prod_insert, prod_singleton]
  norm_num [Nat.factorial]
  ring
theorem sum_partitionsFinFour_partitionWeight (m : Finset (Fin 4) → ℝ) :
    ∑ P ∈ partitionsFinFour, partitionWeight m P =
    m {0, 1, 2, 3} - m {0, 1, 2} * m {3} - m {0, 1, 3} * m {2} - m {0, 2, 3} * m {1} -
      m {1, 2, 3} * m {0} - m {0, 1} * m {2, 3} - m {0, 2} * m {1, 3} - m {0, 3} * m {1, 2} +
      2 * (m {0, 1} * m {2} * m {3} + m {0, 2} * m {1} * m {3} + m {0, 3} * m {1} * m {2} +
        m {1, 2} * m {0} * m {3} + m {1, 3} * m {0} * m {2} + m {2, 3} * m {0} * m {1}) -
      6 * (m {0} * m {1} * m {2} * m {3}) := by
  simp (disch := decide +kernel) only [partitionsFinFour, partitionWeight, sum_insert, sum_singleton,
    card_insert_of_notMem, card_singleton, prod_insert, prod_singleton]
  norm_num [Nat.factorial]
  ring
theorem lowOrderCumulantFormulas_holds : lowOrderCumulantFormulas := by
  intro ι _ r Ψ
  refine ⟨fun H => ?_, fun H => ?_, fun H => ?_⟩
  · unfold cumulantFromMoments
    rw [sum_finpartition_eq_sum_partitionWeight partitionsFinTwo (fun P hP =>
      exists_finpartition_parts_eq P (partitionsFinTwo_isPartition P hP).1
      (partitionsFinTwo_isPartition P hP).2.1 (partitionsFinTwo_isPartition P hP).2.2)
      parts_mem_partitionsFinTwo (fun J => ballExpectation r Ψ fun η => ∏ l ∈ J, H l η),
      sum_partitionsFinTwo_partitionWeight]
    unfold ballCovariance
    simp (disch := decide +kernel) only [prod_insert, prod_singleton]
  · unfold cumulantFromMoments
    rw [sum_finpartition_eq_sum_partitionWeight partitionsFinThree (fun P hP =>
      exists_finpartition_parts_eq P (partitionsFinThree_isPartition P hP).1
      (partitionsFinThree_isPartition P hP).2.1 (partitionsFinThree_isPartition P hP).2.2)
      parts_mem_partitionsFinThree (fun J => ballExpectation r Ψ fun η => ∏ l ∈ J, H l η),
      sum_partitionsFinThree_partitionWeight]
    unfold ballThirdCumulant
    simp (disch := decide +kernel) only [prod_insert, prod_singleton, mul_assoc]
  · unfold cumulantFromMoments
    rw [sum_finpartition_eq_sum_partitionWeight partitionsFinFour (fun P hP =>
      exists_finpartition_parts_eq P (partitionsFinFour_isPartition P hP).1
      (partitionsFinFour_isPartition P hP).2.1 (partitionsFinFour_isPartition P hP).2.2)
      parts_mem_partitionsFinFour (fun J => ballExpectation r Ψ fun η => ∏ l ∈ J, H l η),
      sum_partitionsFinFour_partitionWeight]
    unfold ballFourthCumulant
    simp (disch := decide +kernel) only [prod_insert, prod_singleton, mul_assoc]
end YangMills.Construction.Cumulants
end
