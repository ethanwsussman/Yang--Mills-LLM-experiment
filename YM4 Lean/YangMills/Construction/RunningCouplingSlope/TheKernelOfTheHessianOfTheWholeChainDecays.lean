import YangMills.Construction.RunningCouplingSlope.HessianOfTheWholeChain
import YangMills.Construction.RunningCouplingSlope.TriplesCarriedByACell
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def HessianKernelDecays : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ C θ : ℝ, 0 ≤ C ∧ 0 < θ ∧ ∀ᶠ n in atTop,
      ∀ (x x' : Tower.Vertex L n k k) (σ σ' : LevelTriple L n k),
        TripleSupportedInCell x σ → TripleSupportedInCell x' σ' →
        |hessianOfFreeEnergy a σ σ'| ≤ C * Real.exp (-(θ * cellDist x x')) *
          Real.sqrt (tripleNormSq σ) * Real.sqrt (tripleNormSq σ')
end YangMills.Construction.RunningCouplingSlope
end
