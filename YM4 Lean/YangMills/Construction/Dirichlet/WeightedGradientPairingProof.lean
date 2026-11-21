import YangMills.Construction.Dirichlet.CollarGeometry
import YangMills.Construction.Dirichlet.CentresAndCells
import YangMills.Construction.WeightedGreen.DecayRateDefs
import YangMills.Construction.Dirichlet.WeightedLengthEstimates
import YangMills.Construction.WeightedGreen.DecayRateBounds
import Mathlib
set_option autoImplicit false
open Classical
open YangMills.Construction.Torus YangMills.Construction.WeightedGreen
noncomputable section
namespace YangMills.Construction.Dirichlet.WeightedGradient
variable {d : ℕ} {S ξ : ℝ}
theorem finsum_mem_eq_sum_indicator {ι : Type*} [Fintype ι] (s : Set ι) (f : ι → ℝ) :
    ∑ᶠ b ∈ s, f b = ∑ b, s.indicator f b := by
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
end YangMills.Construction.Dirichlet.WeightedGradient
