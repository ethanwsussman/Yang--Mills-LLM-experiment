import YangMills.Construction.ConfigurationSpace.ShellCenterCount
import YangMills.Construction.ConfigurationSpace.WhitneyCubeBoxBounds
import YangMills.Construction.ConfigurationSpace.WhitneyPartitionOfUnity
import YangMills.Construction.ConfigurationSpace.WhitneyPieceBounds
import YangMills.Construction.ConfigurationSpace.WhitneyPieceDerivBound
import YangMills.Construction.ConfigurationSpace.WhitneyPieceSupport
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
open YangMills.Construction.WhitneyScales
theorem whitneyPieceBounds_of
    (hS : WhitneyPieceSupportProperties)
    (hU : WhitneyPartitionOfUnityProperty)
    (hD : WhitneyPieceDerivBound)
    (hC : WhitneyCubeBoxBounds)
    (hN : ShellCenterCountBound) :
    WhitneyPieceBounds := by
  intro n hn
  refine ⟨?_, ?_, hU n hn, fun _ => rfl, hC n hn, hN n hn⟩
  · intro j z i
    have hu : 0 ≤ whitneySide j := by
      have := isWhitneyRatio_whitneyRatio.1
      unfold whitneySide whitneyScale
      positivity
    constructor
    · intro y hy
      simp only [innerCube, middleCube, closedCubeAt, Set.mem_ofPred_eq] at hy ⊢
      linarith
    · intro y hy
      simp only [outerCube, middleCube, closedCubeAt, Set.mem_ofPred_eq] at hy ⊢
      linarith
  · intro j z
    obtain ⟨a, b, c, d, e, f, g⟩ := hS n hn j z
    exact ⟨a, b, c, d, e, f, g, hD n hn j z⟩
end YangMills.Construction.ConfigurationSpace
end
