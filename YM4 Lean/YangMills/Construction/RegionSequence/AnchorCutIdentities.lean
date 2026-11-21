import YangMills.Construction.RegionSequence.BlockAverageLift
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus
namespace RegionSequence.AnchorCutIdentities
open NestedRegions
variable {𝒮 : NestedRegions}
theorem supNorm_target_sub_source (b : 𝒮.FineBond) :
    supNorm ((b.target : 𝒮.Point) - (b.source : 𝒮.Point)) ≤ 𝒮.ξ := by
  refine csInf_le ⟨0, ?_⟩ ⟨Pi.single b.dir 𝒮.ξ, ?_, ?_⟩
  · rintro r ⟨v, -, rfl⟩
    exact norm_nonneg v
  · simp [LatticeBond.target, unitStep]
  · rw [Pi.norm_single, Real.norm_eq_abs, abs_of_pos 𝒮.ξ_pos]
end RegionSequence.AnchorCutIdentities
end YangMills.Construction
