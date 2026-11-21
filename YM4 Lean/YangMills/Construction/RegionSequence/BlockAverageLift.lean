import YangMills.Construction.RegionSequence.BlockAverageAdjoint
import YangMills.Construction.RegionSequence.CubePartitions
import YangMills.Construction.RegionSequence.DifferenceAdjointsByParts
import YangMills.Construction.RegionSequence.ShellsAndCells
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus
namespace RegionSequence.BlockAverageLift
open NestedRegions
theorem finite_spacingLattice (hT : Torus.TorusLengthsStatement) (𝒮 : NestedRegions) {n : ℕ}
    (hn : n ≤ 𝒮.s) : (spacingLattice 4 𝒮.side (scaleSpacing 𝒮.L 𝒮.ξ n) : Set 𝒮.Point).Finite := by
  have hLn : 0 < 𝒮.L := by have := 𝒮.thirteen_le_L; omega
  have hL : (0 : ℝ) < 𝒮.L := by exact_mod_cast hLn
  have hσ : ∀ i : ℕ, 0 < scaleSpacing 𝒮.L 𝒮.ξ i := fun i => mul_pos (zpow_pos hL _) 𝒮.ξ_pos
  obtain ⟨k, hk⟩ := 𝒮.side_mem_zmultiples
  have hk0 : 0 < k := by
    by_contra h
    have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast not_lt.1 h
    have h1 := mul_nonpos_of_nonpos_of_nonneg hk' (mul_pos two_pos (hσ 𝒮.s)).le
    have h2 := 𝒮.side_pos
    rw [hk] at h2
    exact absurd h2 (not_lt.2 h1)
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m := ⟨k.toNat, (Int.toNat_of_nonneg hk0.le).symm⟩
  have hm : 0 < m := by exact_mod_cast hk0
  have hpow : scaleSpacing 𝒮.L 𝒮.ξ (𝒮.s : ℤ) =
      (𝒮.L : ℝ) ^ (𝒮.s - n) * scaleSpacing 𝒮.L 𝒮.ξ (n : ℤ) := by
    simp only [scaleSpacing, zpow_natCast]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
  have hside : 𝒮.side = ((m * 2 * 𝒮.L ^ (𝒮.s - n) : ℕ) : ℝ) * scaleSpacing 𝒮.L 𝒮.ξ (n : ℤ) := by
    rw [hk, hpow]
    push_cast
    ring
  exact (((hT 4 𝒮.side 𝒮.side_pos).2 _ _ (hσ n)
    (Nat.mul_pos (Nat.mul_pos hm two_pos) (pow_pos hLn _)) hside)).finite
theorem finite_fineSite (hT : Torus.TorusLengthsStatement) (𝒮 : NestedRegions) :
    Finite 𝒮.FineSite := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineSite <;> assumption
theorem finsum_mem_eq_sum_if {α : Type} [Fintype α] (t : Set α) [DecidablePred (· ∈ t)]
    (f : α → ℝ) : ∑ᶠ x ∈ t, f x = ∑ x, if x ∈ t then f x else 0 := by
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun x _ => Set.indicator_apply t f x
variable {𝒮 : NestedRegions}
theorem level_facts {y : 𝒮.Point} (hy : y ∈ 𝒮.allCentres) :
    𝒮.level y ≤ 𝒮.s ∧ y ∈ spacingLattice 4 𝒮.side (𝒮.scale (𝒮.level y)) := by
  obtain ⟨n, hn, hyn⟩ := hy
  have hne : {m | y ∈ shellSites 𝒮.L 𝒮.ξ 𝒮.Ω m}.Nonempty := ⟨n, hyn⟩
  have hmem := Nat.sInf_mem hne
  exact ⟨(Nat.sInf_le hyn).trans hn, hmem.2.1⟩
theorem centreOfSite_spec (hC : RegionSequence.ShellCells 𝒮) (x : 𝒮.FineSite)
    (hx : (x : 𝒮.Point) ∈ 𝒮.Ω 0) :
    𝒮.centreOfSite x ∈ 𝒮.allCentres ∧ (x : 𝒮.Point) ∈ 𝒮.cellOf (𝒮.centreOfSite x) := by
  obtain ⟨y, hy, hint, -⟩ := hC.fineSite_mem_unique x hx
  exact Classical.epsilon_spec (p := fun y => y ∈ 𝒮.allCentres ∧ (x : 𝒮.Point) ∈ 𝒮.cellOf y)
    ⟨y, hy, interior_subset hint⟩
end RegionSequence.BlockAverageLift
end YangMills.Construction
