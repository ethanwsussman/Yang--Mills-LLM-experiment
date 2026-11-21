import YangMills.Construction.RegionSequence.DifferenceAdjoints
import YangMills.Construction.Torus.TorusLengths
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Dirichlet
namespace RegionSequence.DifferenceAdjointsByParts
open NestedRegions
theorem finite_fineSite (h : Torus.TorusLengthsStatement) (𝒮 : NestedRegions) :
    Finite 𝒮.FineSite := by
  obtain ⟨k, hk⟩ := 𝒮.side_mem_zmultiples
  have L_pos : 0 < 𝒮.L := lt_of_lt_of_le (by norm_num) 𝒮.thirteen_le_L
  have step_pos : 0 < 2 * Torus.scaleSpacing 𝒮.L 𝒮.ξ 𝒮.s := by
    unfold Torus.scaleSpacing
    have : (0 : ℝ) < 𝒮.L := Nat.cast_pos.2 L_pos
    have := 𝒮.ξ_pos
    positivity
  have k_pos : (0 : ℝ) < k := by
    have side := 𝒮.side_pos
    rw [hk] at side
    exact pos_of_mul_pos_left side step_pos.le
  lift k to ℕ using (by exact_mod_cast k_pos.le)
  have count_pos : 0 < k * 2 * 𝒮.L ^ 𝒮.s := by
    have : 0 < k := by exact_mod_cast k_pos
    positivity
  refine ((h 4 𝒮.side 𝒮.side_pos).2 𝒮.ξ (k * 2 * 𝒮.L ^ 𝒮.s) 𝒮.ξ_pos count_pos ?_).finite.to_subtype
  rw [hk, Torus.scaleSpacing, zpow_natCast]
  push_cast
  ring
theorem finite_fineBond (h : Torus.TorusLengthsStatement) (𝒮 : NestedRegions) :
    Finite 𝒮.FineBond := by
  have := finite_fineSite h 𝒮
  refine Finite.of_injective (fun b : 𝒮.FineBond => (b.source, b.dir)) ?_
  rintro ⟨x, μ⟩ ⟨y, ν⟩ hxy
  simp only [Prod.mk.injEq] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  rfl
variable {𝒮 : NestedRegions}
end RegionSequence.DifferenceAdjointsByParts
end YangMills.Construction
