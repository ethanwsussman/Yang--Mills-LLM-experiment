import YangMills.Construction.Towers.TheSignsOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ChosenProlongDerivAtIdentity : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ i n : ℕ, 0 < n →
    ∀ B ∈ edgeFormSpace L n (i + 1) (i + 1),
    leftDifferential (chosenProlong L n (i + 1) i) (trivialField L n (i + 1) (i + 1)) B =
      linearSmoothingIter L n (i + 1) i
        (leftDifferential (chosenProlongComp L n (i + 1) (i + 1))
          (trivialField L n (i + 1) (i + 1)) B)
end YangMills.Construction.Tower
end
