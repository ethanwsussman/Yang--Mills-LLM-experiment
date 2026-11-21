import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.CubesAndCutoffs
import YangMills.Construction.Torus.TorusLengths
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PartitionCubes
open RegionSequence Torus
variable {S : NestedRegions} {M : ℕ}
theorem exists_side_eq_mul_cubeSide {K m R₁ : ℕ} (hS : S.IsLevelUnitChain K m M R₁) {n : ℕ}
    (hn : n ≤ topLevel S) :
    0 < cubeSide S M n ∧ ∃ j : ℕ, 0 < j ∧ S.side = (j : ℝ) * cubeSide S M n := by
  have hsep := hS.separated
  have hL : 0 < S.L := by
    have := S.thirteen_le_L
    omega
  have hM : 0 < M := lt_of_lt_of_le hL hsep.blockSize_isPowerGe.1
  obtain ⟨k, hk, hside⟩ := hsep.period_eq_even_mul
  obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨?_, 2 * (k * S.L ^ i), Nat.mul_pos two_pos (Nat.mul_pos hk (pow_pos hL i)), ?_⟩
  · have hL' : (0 : ℝ) < S.L := by exact_mod_cast hL
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    simp only [cubeSide, NestedRegions.scale, scaleSpacing, zpow_natCast]
    exact mul_pos hM' (mul_pos (pow_pos hL' n) S.ξ_pos)
  · have hi' : lastNonemptyIndex S.Ω = n + i := hi
    rw [hside, hi']
    simp only [cubeSide, NestedRegions.scale, scaleSpacing, zpow_natCast]
    push_cast
    ring
theorem cornerSet_finite (hl : TorusLengthsStatement) {K m R₁ : ℕ}
    (hS : S.IsLevelUnitChain K m M R₁) {n : ℕ} (hn : n ≤ topLevel S) :
    (cornerSet S M n).Finite := by
  obtain ⟨hσ, j, hj, hside⟩ := exists_side_eq_mul_cubeSide hS hn
  have hlat := ((hl 4 S.side S.side_pos).2 (cubeSide S M n) j hσ hj hside).finite
  have hε : {ε : Fin 4 → ℝ | ∀ μ, ε μ = 1 ∨ ε μ = -1}.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin 4 => ({1, -1} : Set ℝ))
      fun _ => Set.toFinite _).subset ?_
    intro ε h μ _
    simpa using h μ
  refine (hlat.image2 (fun (c : S.Point) (ε : Fin 4 → ℝ) =>
    c + torusProj 4 S.side fun μ => ε μ * (cubeSide S M n / 2)) hε).subset ?_
  rintro z ⟨c, hc, ε, hε', rfl⟩
  exact ⟨c, hc, ε, hε', rfl⟩
end YangMills.Construction.PartitionCubes
end
