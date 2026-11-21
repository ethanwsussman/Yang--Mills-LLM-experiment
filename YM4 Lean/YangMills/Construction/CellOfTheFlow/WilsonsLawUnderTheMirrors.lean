import YangMills.Construction.CellOfTheFlow.MirrorCopiesOfAGrid
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusFields WeightedResponses
def wilsonLawReflectionInvariantStatement : Prop :=
  ∀ (β : ℝ) (m : ℕ) [NeZero m] (G : CellGrid) (i i' : Fin 4 → ℤ) (F : TorusField m → ℝ), 0 < β → G.Compatible m →
    Measurable F → (∃ M, ∀ W, |F W| ≤ M) →
    ∫ W, F (pullbackBy (G.reflectionTo i i') W) ∂(wilsonLaw β m) = ∫ W, F W ∂(wilsonLaw β m)
end YangMills.Construction.CellWindows
end
