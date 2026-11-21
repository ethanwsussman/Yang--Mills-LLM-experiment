import YangMills.Construction.LawByMomentsOfTheFlow.PotentialOfAPlaquetteByAGreenFunction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.PeriodicLattice.VectorClasses
def torusSecondDiffNearLatticeStatement : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ (ν ν' : Fin 4) (z : Fin 4 → ℤ), (∀ μ, |(z μ : ℝ)| ≤ (n : ℝ) / 2) →
    |secondDiffMatrix (fun w => (greenOnVectors n w).re) z ν ν' -
        secondDiffMatrix latticeGreen z ν ν'| ≤ C * ((n : ℝ) ^ 4)⁻¹
end YangMills.Construction.MomentLaw
end
