import YangMills.Construction.Towers.TheTwoOperatorFunctionsAsFunctionsOfValues
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.LocalKernelFunctions
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.FieldValueFunctions
def ThreeKernelsLocal : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
    ∀ k : ℕ, 1 ≤ k →
    ∃ ρ : ℝ,
      IsLocalWith (YangMills.Construction.Tower.FullSpace.fieldPeriodicData L k hL)
        (colourVertices L k 0) (colourEdges L k 0) (covDiffFn L k hL) ρ 19 ∧
      IsLocalWith (YangMills.Construction.Tower.FullSpace.fieldPeriodicData L k hL)
        (colourVertices L k 0) (colourVertices L k k) (averageKernelFn L k hL) ρ 19 ∧
      IsLocalWith (YangMills.Construction.Tower.FullSpace.fieldPeriodicData L k hL)
        (colourEdges L k 0) (colourEdges L k k) (covariantAverageFn L k hL) ρ 19
end YangMills.Construction.Tower.FullSpace.LocalKernelFunctions
end
