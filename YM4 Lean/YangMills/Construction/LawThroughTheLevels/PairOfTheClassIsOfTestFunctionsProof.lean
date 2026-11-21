import YangMills.Construction.LawThroughTheLevels.PairOfTheClassIsOfTestFunctions
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Scales
theorem isCompact_closedBallR4 (c : Fin 4 → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (YangMills.Construction.TestFunctions.closedBallR4 c R) := by apply _root_.YangMills.Construction.TestPairs.isCompact_closedBallR4 <;> assumption
theorem separatedPairsAreTestFunctions_holds : SeparatedPairsAreTestFunctionsStatement := by
  rintro d ϑ f h hd ⟨x₁, x₂, h₁, h₂, -, -⟩
  exact ⟨⟨h₁.1, (isCompact_closedBallR4 x₁ hd).of_isClosed_subset (isClosed_tsupport f) h₁.2.2.2.1⟩,
    ⟨h₂.1, (isCompact_closedBallR4 x₂ hd).of_isClosed_subset (isClosed_tsupport h) h₂.2.2.2.1⟩⟩
end YangMills.Construction.Scales
end
