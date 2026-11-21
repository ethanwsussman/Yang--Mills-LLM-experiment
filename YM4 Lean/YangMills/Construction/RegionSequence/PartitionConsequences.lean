import YangMills.Construction.RegionSequence.AvgOpWeightSum
import YangMills.Construction.RegionSequence.CubePartitions
import YangMills.Construction.Torus.PartitionsShellsCubes
import YangMills.Construction.Torus.TorusLengths
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RegionSequence.PartitionConsequences
open Torus Dirichlet
variable (𝒮 : NestedRegions)
theorem one_le_L : (1 : ℝ) ≤ 𝒮.L := by
  have h := 𝒮.thirteen_le_L
  exact_mod_cast (by omega : 1 ≤ 𝒮.L)
theorem scale_pos (i : ℕ) : 0 < 𝒮.scale i := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem scale_eq_pow_mul_scale {i i' : ℕ} (h : i ≤ i') :
    𝒮.scale i' = (𝒮.L : ℝ) ^ (i' - i) * 𝒮.scale i := by
  rw [𝒮.scale_eq_pow_mul, 𝒮.scale_eq_pow_mul, ← mul_assoc, ← pow_add, Nat.sub_add_cancel h]
theorem isPartitionLevel_of_le {i i' : ℕ} (hii : i ≤ i') (hf : 𝒮.IsPartitionLevel i') :
    𝒮.IsPartitionLevel i := by
  obtain ⟨k, hk, e⟩ := hf
  have hσ := scale_pos 𝒮 i
  have hL : (0 : ℝ) < 𝒮.L := lt_of_lt_of_le one_pos (one_le_L 𝒮)
  have hLz : (1 : ℤ) ≤ (𝒮.L : ℤ) ^ (i' - i) := by
    apply one_le_pow₀
    have h := 𝒮.thirteen_le_L
    omega
  refine ⟨k * (𝒮.L : ℤ) ^ (i' - i), ?_, ?_⟩
  · nlinarith
  · have hp : ((𝒮.L : ℝ) ^ (i' - i)) ≠ 0 := (pow_pos hL _).ne'
    rw [scale_eq_pow_mul_scale 𝒮 hii] at e
    push_cast
    rw [← e]
    field_simp
theorem isPartitionLevel_of_le_s {n : ℕ} (hn : n ≤ 𝒮.s) : 𝒮.IsPartitionLevel n := by
  obtain ⟨k, hk⟩ := 𝒮.side_mem_zmultiples
  have hσ := scale_pos 𝒮 n
  have hs := scale_pos 𝒮 𝒮.s
  have hL : (0 : ℝ) < 𝒮.L := lt_of_lt_of_le one_pos (one_le_L 𝒮)
  have hk' : 𝒮.side = (k : ℝ) * (2 * 𝒮.scale 𝒮.s) := hk
  have hkpos : (0 : ℤ) < k := by
    have h1 : (0 : ℝ) < (k : ℝ) * (2 * 𝒮.scale 𝒮.s) := hk' ▸ 𝒮.side_pos
    have h2 : (0 : ℝ) < k := (mul_pos_iff_of_pos_right (by positivity)).1 h1
    exact_mod_cast h2
  have hLz : (1 : ℤ) ≤ (𝒮.L : ℤ) ^ (𝒮.s - n) := by
    apply one_le_pow₀
    have h := 𝒮.thirteen_le_L
    omega
  refine ⟨2 * k * (𝒮.L : ℤ) ^ (𝒮.s - n), ?_, ?_⟩
  · nlinarith
  · rw [hk', scale_eq_pow_mul_scale 𝒮 hn]
    push_cast
    field_simp
theorem isNatAtLeastTwo {i : ℕ} (hf : 𝒮.IsPartitionLevel i) :
    IsNatAtLeastTwo (𝒮.side / scaleSpacing 𝒮.L 𝒮.ξ (i : ℤ)) := by
  obtain ⟨k, hk, e⟩ := hf
  refine ⟨k.toNat, by omega, ?_⟩
  have e' : 𝒮.side / scaleSpacing 𝒮.L 𝒮.ξ (i : ℤ) = (k : ℝ) := e
  have hc : ((k.toNat : ℤ)) = k := Int.toNat_of_nonneg (by omega)
  rw [e']
  exact_mod_cast hc.symm
theorem parameters : Parameters 4 𝒮.L 1 1 where
  three_le_dim := by norm_num
  three_le_blockFactor := by
    have h := 𝒮.thirteen_le_L
    omega
  odd_blockFactor := 𝒮.odd_L
  lower_pos := one_pos
  lower_le_upper := le_rfl
theorem nestedPartitionFacts (h : PartitionsHold) {i i' : ℕ} (hii : i ≤ i')
    (hf : 𝒮.IsPartitionLevel i') :
    NestedPartitionFacts 4 𝒮.L 𝒮.ξ 𝒮.side (𝒮.scale i') (𝒮.scale i) :=
  (h 4 𝒮.L 1 1 (parameters 𝒮) 𝒮.ξ 𝒮.side 𝒮.ξ_pos 𝒮.side_pos).2.1 (i : ℤ) (i' : ℤ)
    (by exact_mod_cast hii) (isNatAtLeastTwo 𝒮 hf)
end YangMills.Construction.RegionSequence.PartitionConsequences
end
