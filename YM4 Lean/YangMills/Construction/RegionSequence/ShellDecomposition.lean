import YangMills.Construction.RegionSequence.AvgOpWeightSum
import YangMills.Construction.RegionSequence.ShellsAndCells
import YangMills.Construction.Torus.PartitionsShellsCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RegionSequence.ShellDecomposition
open Torus
variable {𝒮 : NestedRegions}
theorem blockFactor_pos (𝒮 : NestedRegions) : (0 : ℝ) < 𝒮.L := by
  have := 𝒮.thirteen_le_L
  exact_mod_cast (by omega : 0 < 𝒮.L)
theorem scale_pos (𝒮 : NestedRegions) (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem scale_mono (𝒮 : NestedRegions) {a b : ℕ} (h : a ≤ b) : 𝒮.scale a ≤ 𝒮.scale b := by
  rw [𝒮.scale_eq_pow_mul, 𝒮.scale_eq_pow_mul]
  have hL : (1 : ℝ) ≤ 𝒮.L := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 1 ≤ 𝒮.L)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL h) 𝒮.ξ_pos.le
theorem isNatAtLeastTwo_side_div {j : ℕ} (hj : j ≤ 𝒮.s) :
    IsNatAtLeastTwo (𝒮.side / scaleSpacing 𝒮.L 𝒮.ξ (j : ℤ)) := by
  obtain ⟨k, hk⟩ := 𝒮.side_mem_zmultiples
  have hLp := blockFactor_pos 𝒮
  have hξ := 𝒮.ξ_pos
  have hsp : scaleSpacing 𝒮.L 𝒮.ξ (𝒮.s : ℤ) = (𝒮.L : ℝ) ^ 𝒮.s * 𝒮.ξ := by simp [scaleSpacing]
  have hjp : scaleSpacing 𝒮.L 𝒮.ξ (j : ℤ) = (𝒮.L : ℝ) ^ j * 𝒮.ξ := by simp [scaleSpacing]
  have hk0 : 0 < k := by
    by_contra hc
    have hc' : (k : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp hc
    have hpos : 0 < 2 * scaleSpacing 𝒮.L 𝒮.ξ (𝒮.s : ℤ) := by
      rw [hsp]; positivity
    have := 𝒮.side_pos
    rw [hk] at this
    nlinarith
  lift k to ℕ using hk0.le
  have hk1 : 1 ≤ k := by exact_mod_cast hk0
  have hpow : 1 ≤ 𝒮.L ^ (𝒮.s - j) := Nat.one_le_pow _ _ (by have := 𝒮.thirteen_le_L; omega)
  refine ⟨2 * k * 𝒮.L ^ (𝒮.s - j), ?_, ?_⟩
  · nlinarith
  · have hs : (𝒮.L : ℝ) ^ 𝒮.s = (𝒮.L : ℝ) ^ (𝒮.s - j) * (𝒮.L : ℝ) ^ j := by
      rw [← pow_add]; congr 1; omega
    rw [hk, hsp, hjp, hs]
    push_cast
    have h1 : (𝒮.L : ℝ) ^ j ≠ 0 := (pow_pos hLp j).ne'
    field_simp
theorem partitionFacts (hT : PartitionsHold) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ 𝒮.s) : NestedPartitionFacts 4 𝒮.L 𝒮.ξ 𝒮.side (𝒮.scale j) (𝒮.scale i) :=
  (hT 4 𝒮.L 1 1 ⟨by norm_num, by have := 𝒮.thirteen_le_L; omega, 𝒮.odd_L, one_pos, le_rfl⟩
    𝒮.ξ 𝒮.side 𝒮.ξ_pos 𝒮.side_pos).2.1 i j (by exact_mod_cast hij) (isNatAtLeastTwo_side_div hj)
theorem succ_subset {j : ℕ} (hj : j ≤ 𝒮.s) : 𝒮.Ω (j + 1) ⊆ 𝒮.Ω j := by
  rcases hj.lt_or_eq with h | rfl
  · exact 𝒮.Ω_succ_subset j h
  · rw [𝒮.Ω_eq_empty _ (Nat.lt_succ_self _)]
    exact empty_subset _
theorem Ω_antitone {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 𝒮.s) : 𝒮.Ω b ⊆ 𝒮.Ω a := by
  induction b, hab using Nat.le_induction with
  | base => exact Subset.rfl
  | succ n hn ih => exact (succ_subset (by omega)).trans (ih (by omega))
theorem isCubeUnion_succ (hT : PartitionsHold) {j : ℕ} (hj : j ≤ 𝒮.s) :
    𝒮.IsCubeUnionAt j (𝒮.Ω (j + 1)) := by
  rcases hj.lt_or_eq with h | rfl
  · exact (partitionFacts hT (Nat.le_succ j) h).isCubeUnion_finer _ (𝒮.isCubeUnion_Ω _ h)
  · rw [𝒮.Ω_eq_empty _ (Nat.lt_succ_self _)]
    exact ⟨∅, empty_subset _, sUnion_empty.symm⟩
theorem mem_cubeAt_self {σ : ℝ} (hσ : 0 ≤ σ) (c : 𝒮.Point) : c ∈ cubeAt c σ := by
  have h : supNorm (c - c) ≤ 0 := by
    rw [sub_self]
    apply csInf_le
    · exact ⟨0, by rintro r ⟨v, -, rfl⟩; exact norm_nonneg v⟩
    · exact ⟨0, by funext μ; simp [torusProj], by simp⟩
  change supNorm (c - c) ≤ σ / 2
  linarith
theorem cubeAt_scale_mono (𝒮 : NestedRegions) {a b : ℕ} (h : a ≤ b) (y : 𝒮.Point) :
    cubeAt y (𝒮.scale a) ⊆ cubeAt y (𝒮.scale b) := by
  intro p hp
  have h1 := scale_mono 𝒮 h
  change supNorm (p - y) ≤ _ at hp
  change supNorm (p - y) ≤ _
  linarith
theorem eq_cubeAt_of_mem (hT : PartitionsHold) {j : ℕ} (hj : j ≤ 𝒮.s)
    {y : 𝒮.Point} (hy : y ∈ spacingLattice 4 𝒮.side (𝒮.scale j)) {Q : Set 𝒮.Point}
    (hQ : Q ∈ 𝒮.cubePartitionAt j) (hyQ : y ∈ Q) : Q = cubeAt y (𝒮.scale j) := by
  have F := partitionFacts (𝒮 := 𝒮) hT le_rfl hj
  obtain ⟨c, hc, rfl⟩ := hQ
  by_contra hne
  have hint := F.grid_subset_interior c hc ⟨hy, hyQ⟩
  exact F.not_mem_of_mem_interior _ ⟨c, hc, rfl⟩ _ ⟨y, hy, rfl⟩ (Ne.symm hne) y hint
    (mem_cubeAt_self (scale_pos 𝒮 j).le y)
abbrev shellCubes (𝒮 : NestedRegions) (j : ℕ) : Set (Set 𝒮.Point) :=
  {Q ∈ 𝒮.cubePartitionAt j | Q ⊆ 𝒮.Ω j ∧ ¬ Q ⊆ 𝒮.Ω (j + 1)}
theorem shellOf_eq_sUnion (hT : PartitionsHold) {j : ℕ} (hj : j ≤ 𝒮.s) :
    𝒮.shellOf j = ⋃₀ shellCubes 𝒮 j :=
  (partitionFacts hT le_rfl hj).closure_sdiff _ _ (𝒮.isCubeUnion_Ω j hj) (isCubeUnion_succ hT hj)
    (succ_subset hj)
theorem le_s_of_mem_centresAt {j : ℕ} {y : 𝒮.Point} (hy : y ∈ 𝒮.centresAt j) : j ≤ 𝒮.s := by
  by_contra hc
  have h : 𝒮.s < j := not_le.mp hc
  have hy2 : y ∈ shell 𝒮.Ω j := hy.2.2
  simp [shell, 𝒮.Ω_eq_empty j h] at hy2
theorem le_lastNonemptyIndex {j : ℕ} (h : (𝒮.Ω j).Nonempty) : j ≤ lastNonemptyIndex 𝒮.Ω := by
  refine le_csSup ⟨𝒮.s, ?_⟩ h
  intro n hn
  by_contra hc
  have hn' : (𝒮.Ω n).Nonempty := hn
  rw [𝒮.Ω_eq_empty n (not_le.mp hc)] at hn'
  exact not_nonempty_empty hn'
theorem cubeAt_mem_shellCubes (hT : PartitionsHold) {j : ℕ}
    {y : 𝒮.Point} (hy : y ∈ 𝒮.centresAt j) : cubeAt y (𝒮.scale j) ∈ shellCubes 𝒮 j := by
  have hj := le_s_of_mem_centresAt hy
  have hl : y ∈ 𝒮.shellOf j := hy.2.2
  rw [shellOf_eq_sUnion hT hj] at hl
  obtain ⟨Q, hQ, hyQ⟩ := hl
  have hlat : y ∈ spacingLattice 4 𝒮.side (𝒮.scale j) := hy.2.1
  rw [← eq_cubeAt_of_mem hT hj hlat hQ.1 hyQ]
  exact hQ
theorem centresAt_unique (hT : PartitionsHold) {a b : ℕ} (hab : a < b)
    {y : 𝒮.Point} (ha : y ∈ 𝒮.centresAt a) (hb : y ∈ 𝒮.centresAt b) : False := by
  have hbs := le_s_of_mem_centresAt hb
  have h1 := cubeAt_mem_shellCubes hT ha
  have h2 := cubeAt_mem_shellCubes hT hb
  exact h1.2.2 ((cubeAt_scale_mono 𝒮 hab.le y).trans (h2.2.1.trans (Ω_antitone hab hbs)))
theorem level_eq (hT : PartitionsHold) {j : ℕ} {y : 𝒮.Point}
    (hy : y ∈ 𝒮.centresAt j) : 𝒮.level y = j := by
  have hne : {n | y ∈ shellSites 𝒮.L 𝒮.ξ 𝒮.Ω n}.Nonempty := ⟨j, hy⟩
  have hmem : 𝒮.level y ∈ {n | y ∈ shellSites 𝒮.L 𝒮.ξ 𝒮.Ω n} := Nat.sInf_mem hne
  have hle : 𝒮.level y ≤ j := Nat.sInf_le hy
  rcases hle.lt_or_eq with h | h
  · exact (centresAt_unique hT h hmem hy).elim
  · exact h
theorem cellOf_eq (hT : PartitionsHold) {j : ℕ} {y : 𝒮.Point}
    (hy : y ∈ 𝒮.centresAt j) : 𝒮.cellOf y = cubeAt y (𝒮.scale j) := by
  have h : shellIndex 𝒮.L 𝒮.ξ 𝒮.Ω y = j := level_eq hT hy
  simp only [NestedRegions.cellOf, siteCube, shellSpacing, h]
  rfl
theorem cellOf_mem_shellCubes (hT : PartitionsHold) {j : ℕ} {y : 𝒮.Point}
    (hy : y ∈ 𝒮.centresAt j) : 𝒮.cellOf y ∈ shellCubes 𝒮 j := by
  rw [cellOf_eq hT hy]
  exact cubeAt_mem_shellCubes hT hy
theorem disjoint_interior_succ (hT : PartitionsHold) {j : ℕ} (hj : j ≤ 𝒮.s)
    {Q : Set 𝒮.Point} (hQ : Q ∈ shellCubes 𝒮 j) : Disjoint (interior Q) (𝒮.Ω (j + 1)) :=
  (partitionFacts hT le_rfl hj).disjoint_interior _ _ (𝒮.isCubeUnion_Ω j hj)
    (isCubeUnion_succ hT hj) (succ_subset hj) Q hQ.1 hQ.2.1 hQ.2.2
theorem disjoint_interior_of_lt (hT : PartitionsHold) {a b : ℕ} (hab : a < b)
    {y y' : 𝒮.Point} (hy : y ∈ 𝒮.centresAt a) (hy' : y' ∈ 𝒮.centresAt b) :
    Disjoint (interior (𝒮.cellOf y)) (interior (𝒮.cellOf y')) := by
  have h1 := disjoint_interior_succ hT (le_s_of_mem_centresAt hy) (cellOf_mem_shellCubes hT hy)
  have h2 : interior (𝒮.cellOf y') ⊆ 𝒮.Ω (a + 1) :=
    interior_subset.trans
      ((cellOf_mem_shellCubes hT hy').2.1.trans (Ω_antitone hab (le_s_of_mem_centresAt hy')))
  exact h1.mono_right h2
end YangMills.Construction.RegionSequence.ShellDecomposition
end
