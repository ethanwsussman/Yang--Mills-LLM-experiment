import YangMills.Construction.RunningCouplingSlope.HessianOfTheWholeChain
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def HessianOfFreeEnergyBounded : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ᶠ n in atTop,
      (∀ σ σ' : LevelTriple L n k, |hessianOfFreeEnergy a σ σ'| ≤
        C * Real.sqrt (tripleNormSq σ) * Real.sqrt (tripleNormSq σ')) ∧
      ∀ (A : Tower.edgeFormSpace L n k 0) (σ' : LevelTriple L n k),
        |hessianOfFreeEnergy a (backgroundOnlyTriple A) σ'| ≤
          C * (Real.sqrt (backgroundCurvatureNormSq A) +
            Real.exp (-(c * (2 * (L : ℝ) ^ n))) * Real.sqrt (tripleNormSq (backgroundOnlyTriple A))) *
            Real.sqrt (tripleNormSq σ')
end YangMills.Construction.RunningCouplingSlope
end
