import YangMills.Construction.GeneralTorus.CubePartitions
import YangMills.Construction.GeneralTorus.ShellsCubesAndScaledDistance
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace GeneralTorus.ChainStructureProof
open CubePartitions
section Scales
variable (D : ScaleData)
theorem odd_L : Odd D.L := D.blocking.odd_blockingFactor
theorem L_pos : 0 < D.L := (odd_L D).pos
theorem odd_blockCount : Odd D.blockCount := by
  obtain ⟨k, hk⟩ := D.blockCount_pow
  rw [hk]
  exact (odd_L D).pow
theorem blockCount_pos : 0 < D.blockCount := (odd_blockCount D).pos
theorem levelSpacing_pos (n : ℕ) : 0 < D.levelSpacing n := by
  have : (0 : ℝ) < D.L := by exact_mod_cast L_pos D
  have := D.baseSpacing_pos
  unfold ScaleData.levelSpacing
  positivity
theorem levelSpacing_eq_pow_mul {m n : ℕ} (h : m ≤ n) :
    D.levelSpacing n = ((D.L ^ (n - m) : ℕ) : ℝ) * D.levelSpacing m := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [ScaleData.levelSpacing, Nat.add_sub_cancel_left, Nat.cast_pow, pow_add]
  ring
theorem blockLength_eq_mul_levelSpacing {m n : ℕ} (h : m ≤ n) :
    D.blockLength n = ((D.blockCount * D.L ^ (n - m) : ℕ) : ℝ) * D.levelSpacing m := by
  rw [ScaleData.blockLength, levelSpacing_eq_pow_mul D h]
  push_cast
  ring
theorem levelSpacing_zero : D.levelSpacing 0 = D.baseSpacing := by simp [ScaleData.levelSpacing]
end Scales
theorem isEvenMultipleOf_of_natCast_mul {S s : ℝ} {k : ℕ} (hk : 0 < k)
    (h : IsEvenMultipleOf S ((k : ℝ) * s)) : IsEvenMultipleOf S s := by
  obtain ⟨j, hj, e⟩ := h
  refine ⟨j * k, Nat.mul_pos hj hk, ?_⟩
  rw [e]
  push_cast
  ring
variable {D : ScaleData}
theorem admitsPartition_of_natCast_mul {s : ℝ} {k : ℕ} (hk : 0 < k) (hs : 0 < s)
    (h : D.AdmitsPartition ((k : ℝ) * s)) : D.AdmitsPartition s :=
  ⟨hs, isEvenMultipleOf_of_natCast_mul hk h.2⟩
theorem admitsPartition_levelSpacing_of_le {m n : ℕ} (h : m ≤ n)
    (hf : D.AdmitsPartition (D.levelSpacing n)) : D.AdmitsPartition (D.levelSpacing m) := by
  rw [levelSpacing_eq_pow_mul D h] at hf
  exact admitsPartition_of_natCast_mul (pow_pos (L_pos D) _) (levelSpacing_pos D m) hf
theorem admitsPartition_levelSpacing_lastLevel : D.AdmitsPartition (D.levelSpacing D.lastLevel) :=
  ⟨levelSpacing_pos D _, D.torusSide_evenMultiple⟩
theorem admitsPartition_levelSpacing_of_le_lastLevel {n : ℕ} (h : n ≤ D.lastLevel) :
    D.AdmitsPartition (D.levelSpacing n) :=
  admitsPartition_levelSpacing_of_le h admitsPartition_levelSpacing_lastLevel
theorem mem_spacingLattice_iff {S s : ℝ} {x : Torus4 S} :
    x ∈ spacingLattice S s ↔ ∃ k : Fin 4 → ℤ, x = torusProj S fun μ => s * (k μ : ℝ) := Iff.rfl
theorem of_mem_cubePartition {s : ℝ} {Q : Set D.Space} (hQ : Q ∈ D.cubePartition s) :
    D.AdmitsPartition s ∧ ∃ y ∈ spacingLattice D.torusSide s, Q = supCube s y := hQ
theorem supCube_mem_cubePartition {s : ℝ} (hs : D.AdmitsPartition s) {y : D.Space}
    (hy : y ∈ spacingLattice D.torusSide s) : supCube s y ∈ D.cubePartition s := ⟨hs, y, hy, rfl⟩
section Partitions
variable (hP : CubePartitionFacts)
include hP
theorem partitionCubes_of_admits {s : ℝ} (hs : D.AdmitsPartition s) : PartitionCubes D s :=
  (hP D s 1 hs.1 le_rfl odd_one (by simpa using hs.2)).1
theorem closureOfDifference_of_admits {s : ℝ} (hs : D.AdmitsPartition s) :
    ClosureOfDifference D s :=
  (hP D s 1 hs.1 le_rfl odd_one (by simpa using hs.2)).2.2.2.2.1
theorem center_mem_interior {s : ℝ} (hs : D.AdmitsPartition s) {y : D.Space}
    (hy : y ∈ spacingLattice D.torusSide s) : y ∈ interior (supCube s y) :=
  (partitionCubes_of_admits hP hs).2.2.2.2.2.1 y hy
theorem eq_of_mem_interior_of_mem {s : ℝ} (hs : D.AdmitsPartition s) {Q Q' : Set D.Space}
    (hQ : Q ∈ D.cubePartition s) (hQ' : Q' ∈ D.cubePartition s) {x : D.Space}
    (hx : x ∈ interior Q) (hx' : x ∈ Q') : Q' = Q :=
  (partitionCubes_of_admits hP hs).2.2.2.2.2.2 Q hQ Q' hQ' x hx hx'
end Partitions
namespace Chain
variable (B : SeparatedChain D)
theorem set_antitone {i j : ℕ} (hij : i ≤ j) : B.set j ⊆ B.set i := by
  by_cases hj : D.lastLevel < j
  · rw [B.eq_empty_of_gt j hj]
    exact empty_subset _
  · replace hj := not_lt.1 hj
    induction j, hij using Nat.le_induction with
    | base => exact Subset.rfl
    | succ j hij ih => exact (B.mono j (by omega)).trans (ih (by omega))
theorem le_lastLevel_of_nonempty {j : ℕ} (hne : (B.set j).Nonempty) : j ≤ D.lastLevel := by
  by_contra h
  replace h := not_le.1 h
  rw [B.eq_empty_of_gt j h] at hne
  exact not_nonempty_empty hne
theorem isUnionOfCubes_empty {π : Set (Set D.Space)} : IsUnionOfCubes π (∅ : Set D.Space) :=
  ⟨∅, empty_subset _, sUnion_empty.symm⟩
theorem admitsPartition_of_nonempty {j : ℕ} (hne : (B.set j).Nonempty) :
    D.AdmitsPartition (D.blockLength j) := by
  obtain ⟨C, hC, e⟩ := B.cubeUnion j (le_lastLevel_of_nonempty B hne) hne
  rw [e] at hne
  obtain ⟨x, Q, hQ, -⟩ := hne
  exact (of_mem_cubePartition (hC hQ)).1
variable (hP : CubePartitionFacts)
include hP
theorem cubeUnion_levelSpacing {m j : ℕ} (hmj : m ≤ j) (hne : (B.set j).Nonempty) :
    IsUnionOfCubes (D.cubePartition (D.levelSpacing m)) (B.set j) ∧
    (∀ y ∈ spacingLattice D.torusSide (D.levelSpacing m), y ∈ B.set j →
      supCube (D.levelSpacing m) y ⊆ B.set j) ∧
    ∀ y ∈ spacingLattice D.torusSide (D.levelSpacing m), y ∉ B.set j →
      Disjoint (interior (supCube (D.levelSpacing m) y)) (B.set j) := by
  have hf := admitsPartition_of_nonempty B hne
  have e := blockLength_eq_mul_levelSpacing D hmj
  have hodd : Odd (D.blockCount * D.L ^ (j - m)) :=
    (odd_blockCount D).mul (odd_L D).pow
  have hm : IsEvenMultipleOf D.torusSide
      (((D.blockCount * D.L ^ (j - m) : ℕ) : ℝ) * D.levelSpacing m) := e ▸ hf.2
  have h := (hP D (D.levelSpacing m) _ (levelSpacing_pos D m) hodd.pos hodd hm).2.2.2.1
  unfold CoarseUnionsAreFineUnions at h
  rw [← e] at h
  exact h _ (B.cubeUnion j (le_lastLevel_of_nonempty B hne) hne)
theorem isUnionOfCubes_levelSpacing {m j : ℕ} (hmj : m ≤ j) :
    IsUnionOfCubes (D.cubePartition (D.levelSpacing m)) (B.set j) := by
  by_cases hne : (B.set j).Nonempty
  · exact (cubeUnion_levelSpacing B hP hmj hne).1
  · rw [not_nonempty_iff_eq_empty.1 hne]
    exact isUnionOfCubes_empty
theorem supCube_subset_set {m j : ℕ} (hmj : m ≤ j) {y : D.Space}
    (hy : y ∈ spacingLattice D.torusSide (D.levelSpacing m)) (hyj : y ∈ B.set j) :
    supCube (D.levelSpacing m) y ⊆ B.set j :=
  (cubeUnion_levelSpacing B hP hmj ⟨y, hyj⟩).2.1 y hy hyj
theorem shell_eq_sUnion {n : ℕ} (hn : n ≤ D.lastLevel) :
    B.shell n =
      ⋃₀ {Q ∈ D.cubePartition (D.levelSpacing n) | Q ⊆ B.set n ∧ ¬Q ⊆ B.set (n + 1)} := by
  have hf := admitsPartition_levelSpacing_of_le_lastLevel hn
  by_cases h : n < D.lastLevel
  · rw [SeparatedChain.shell, if_pos h]
    exact ((closureOfDifference_of_admits hP hf).1 _ _ (isUnionOfCubes_levelSpacing B hP le_rfl)
      (isUnionOfCubes_levelSpacing B hP (Nat.le_succ n)) (B.mono n h)).1
  · have hnt : n = D.lastLevel := le_antisymm hn (not_lt.1 h)
    rw [SeparatedChain.shell, if_neg h, if_pos hnt, B.eq_empty_of_gt (n + 1) (by omega)]
    obtain ⟨C, hC, e⟩ := isUnionOfCubes_levelSpacing B hP (le_refl n)
    apply Subset.antisymm
    · intro x hx
      have hx' := hx
      rw [e] at hx'
      obtain ⟨Q, hQ, hxQ⟩ := hx'
      refine ⟨Q, ⟨hC hQ, ?_, fun hsub => hsub hxQ⟩, hxQ⟩
      rw [e]
      exact subset_sUnion_of_mem hQ
    · exact sUnion_subset fun Q hQ => hQ.2.1
omit hP in
theorem shell_eq_empty {n : ℕ} (hn : D.lastLevel < n) : B.shell n = ∅ := by
  rw [SeparatedChain.shell, if_neg (by omega), if_neg (by omega)]
theorem mem_shellSites_iff {n : ℕ} (hn : n ≤ D.lastLevel) {y : D.Space} :
    y ∈ B.shellSites n ↔
      y ∈ (D.levelSublattice n : Set D.Space) ∧ y ∈ B.set n ∧ y ∉ B.set (n + 1) := by
  have hf := admitsPartition_levelSpacing_of_le_lastLevel hn
  constructor
  · rintro ⟨hy, hyl⟩
    rw [shell_eq_sUnion B hP hn] at hyl
    obtain ⟨Q, ⟨hQ, hQn, hQn'⟩, hyQ⟩ := hyl
    have hcube : Q = supCube (D.levelSpacing n) y :=
      eq_of_mem_interior_of_mem hP hf (supCube_mem_cubePartition hf hy) hQ
        (center_mem_interior hP hf hy) hyQ
    refine ⟨hy, hQn hyQ, fun hy' => hQn' ?_⟩
    rw [hcube]
    exact supCube_subset_set B hP (Nat.le_succ n) hy hy'
  · rintro ⟨hy, hyn, hyn'⟩
    refine ⟨hy, ?_⟩
    rw [shell_eq_sUnion B hP hn]
    have hmem := interior_subset (center_mem_interior hP hf hy)
    exact ⟨supCube (D.levelSpacing n) y,
      ⟨supCube_mem_cubePartition hf hy, supCube_subset_set B hP le_rfl hy hyn,
        fun hsub => hyn' (hsub hmem)⟩, hmem⟩
omit hP in
theorem le_lastLevel_of_mem_shellSites {n : ℕ} {y : D.Space} (hy : y ∈ B.shellSites n) :
    n ≤ D.lastLevel := by
  by_contra h
  replace h := not_le.1 h
  have := hy.2
  rw [shell_eq_empty B h] at this
  exact this
theorem level_eq_of_mem_shellSites {n n' : ℕ} {y : D.Space} (hy : y ∈ B.shellSites n)
    (hy' : y ∈ B.shellSites n') : n' = n := by
  have h1 := (mem_shellSites_iff B hP (le_lastLevel_of_mem_shellSites B hy)).1 hy
  have h2 := (mem_shellSites_iff B hP (le_lastLevel_of_mem_shellSites B hy')).1 hy'
  rcases lt_trichotomy n' n with h | h | h
  · exact absurd (set_antitone B h h1.2.1) h2.2.2
  · exact h
  · exact absurd (set_antitone B h h2.2.1) h1.2.2
theorem localSpacing_eq {n : ℕ} {y : D.Space} (hy : y ∈ B.shellSites n) :
    B.localSpacing y = D.levelSpacing n := by
  have : {i | y ∈ B.shellSites i} = {n} := by
    ext i
    exact ⟨fun hi => level_eq_of_mem_shellSites B hP hy hi,
      fun hi => by rw [mem_singleton_iff.1 hi]; exact hy⟩
  rw [SeparatedChain.localSpacing, this, csInf_singleton]
end Chain
open Chain
section Cubes
variable (hP : CubePartitionFacts)
include hP
end Cubes
section Distance
variable (B : SeparatedChain D)
theorem torusProj_surjective (x : D.Space) : ∃ v, torusProj D.torusSide v = x := by
  have : ∀ μ, ∃ a : ℝ, (a : AddCircle D.torusSide) = x μ := fun μ =>
    QuotientAddGroup.mk_surjective (x μ)
  choose v hv using this
  exact ⟨v, funext hv⟩
theorem continuous_pointAt (s : LiftedSegment) : Continuous (s.pointAt D.torusSide) := by
  unfold LiftedSegment.pointAt torusProj
  refine continuous_pi fun μ => ?_
  exact (AddCircle.continuous_mk' D.torusSide).comp (by fun_prop)
theorem segmentsSupport_singleton (s : LiftedSegment) :
    segmentsSupport D.torusSide [s] = s.support D.torusSide := by
  simp [segmentsSupport]
theorem segmentsSupport_append (Γ Γ' : List LiftedSegment) :
    segmentsSupport D.torusSide (Γ ++ Γ') =
      segmentsSupport D.torusSide Γ ∪ segmentsSupport D.torusSide Γ' := by
  simp only [segmentsSupport, List.mem_append]
  ext x
  simp only [mem_iUnion, mem_union, exists_prop]
  constructor
  · rintro ⟨s, hs | hs, hx⟩
    · exact Or.inl ⟨s, hs, hx⟩
    · exact Or.inr ⟨s, hs, hx⟩
  · rintro (⟨s, hs, hx⟩ | ⟨s, hs, hx⟩)
    · exact ⟨s, Or.inl hs, hx⟩
    · exact ⟨s, Or.inr hs, hx⟩
theorem pathLengthIn_append (Γ Γ' : List LiftedSegment) (A : Set D.Space) :
    pathLengthIn D.torusSide (Γ ++ Γ') A =
      pathLengthIn D.torusSide Γ A + pathLengthIn D.torusSide Γ' A := by
  simp [pathLengthIn, List.map_append, List.sum_append]
theorem l1NormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ l1NormVec v :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
theorem pathLengthIn_nonneg (Γ : List LiftedSegment) (A : Set D.Space) :
    0 ≤ pathLengthIn D.torusSide Γ A := by
  unfold pathLengthIn
  refine List.sum_nonneg ?_
  intro r hr
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hr
  exact mul_nonneg (l1NormVec_nonneg _) ENNReal.toReal_nonneg
end Distance
end GeneralTorus.ChainStructureProof
end YangMills.Construction
end
