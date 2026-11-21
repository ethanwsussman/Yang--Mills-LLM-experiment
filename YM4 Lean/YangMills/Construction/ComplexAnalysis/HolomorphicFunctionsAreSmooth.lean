import YangMills.Construction.Lattice.ToriLatticesNormsAndFunctionsOfFinitelyManyVariables
import Mathlib
set_option autoImplicit false
open scoped ContDiff
namespace YangMills.Construction.SeveralComplexVariables.HolomorphicContDiff
def Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (W : Set (ι → ℂ)) (g : (ι → ℂ) → ℂ),
    IsHolomorphicOnOpen W g → ContDiffOn ℂ ∞ g W
end YangMills.Construction.SeveralComplexVariables.HolomorphicContDiff
