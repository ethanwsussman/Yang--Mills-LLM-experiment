import YangMills.Construction.Towers.TheSignsOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower
def ChosenProlongCompTendsto : Prop :=
  ∀ L n k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k →
    Tendsto (chosenProlongComp L n k j)
      (𝓝[fieldSpace L n k j] trivialField L n k j)
      (𝓝[fieldSpace L n k 0] trivialField L n k 0)
end YangMills.Construction.Tower
end
