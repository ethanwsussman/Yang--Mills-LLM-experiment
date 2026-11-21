import YangMills.Construction.EuclideanFunctionals.PlateVectorsAndFunctionsOnTheShiftedTubes
import YangMills.Construction.ForwardTube.ArgumentsOfTheGramKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ForwardTube.GramArgsInShiftedTubes
def Holds : Prop :=
  ∀ (n m : ℕ) (η : ℝ), 0 < η → η ≤ 1 → 2 ≤ n + m →
    ∀ x ∈ shiftedForwardTube n η, ∀ y ∈ shiftedForwardTube m η,
      gramKernelArgs x y ∈ shiftedForwardTubePow (n + m - 1) η
end YangMills.Construction.ForwardTube.GramArgsInShiftedTubes
end
