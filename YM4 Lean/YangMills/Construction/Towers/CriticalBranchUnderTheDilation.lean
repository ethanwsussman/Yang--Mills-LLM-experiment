import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.TheSignsOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ChosenBranchScaling : Prop :=
  ∀ (L n k j : ℕ) (hL : 0 < L) (hj : j ≤ k), Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    1 ≤ j →
    (∀ l ≤ j, EventuallyNearIdentity (fieldSpace L (scaledExponent n k j) j l) fun W =>
      transportTotalScalar (scaleEdge (n := n) hL hj l) (chosenEnergy L n k l) W =
        chosenEnergy L (scaledExponent n k j) j l W) ∧
    ∀ l < j, EventuallyNearIdentity (fieldSpace L (scaledExponent n k j) j (l + 1)) fun W =>
      transportTotalFunValued (scaleEdge (n := n) hL hj (l + 1))
          (scaleEdge (n := n) hL hj l) (chosenProlong L n k l) W =
        chosenProlong L (scaledExponent n k j) j l W
end YangMills.Construction.Tower
end
