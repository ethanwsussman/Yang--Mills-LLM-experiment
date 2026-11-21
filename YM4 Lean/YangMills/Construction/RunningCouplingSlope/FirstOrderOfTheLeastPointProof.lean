import YangMills.Construction.RunningCouplingSlope.BranchOfLeastPoints
import YangMills.Construction.RunningCouplingSlope.FirstOrderSystemOfABranch
import YangMills.Construction.RunningCouplingSlope.SolutionOfTheFirstOrderSystem
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
theorem minimizerFirstVariation_of_branch (hB : FirstVariationExists) (hS : FirstVariationSolvesSystem)
    (hT : FirstOrderSystemSolution) : MinimizerFirstVariation :=
  fun a ha L hL k n hk hn B => ⟨hB a ha L hL k n hk hn B,
    fun t ht => hT a ha L hL k n hk hn B t (hS a ha L hL k n hk hn B t ht)⟩
end YangMills.Construction.RunningCouplingSlope
end
