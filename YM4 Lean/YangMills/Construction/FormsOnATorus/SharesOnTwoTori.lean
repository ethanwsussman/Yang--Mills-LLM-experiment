import YangMills.Construction.ClusterExpansionOfAStep.ConstantsOfTheColdChain
import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TorusComparison
def FlatSharesOnTwoTori : Prop :=
  ∀ (a δ : ℝ) (L : ℕ) (lam ρ σA cg : ℝ) (N : ℕ → ℝ), 0 < a → Odd L →
    ColdChain.ColdChainConstants a δ L lam ρ σA cg N →
    ∃ D : ℝ, 0 < D ∧
      (∀ (t n : ℕ) [NeZero n], 64 ≤ n →
        (TorusFields.actionAtLevel a L t (Finset.univ : Finset (TorusFields.TorusSite n)) =
          fun W => ∑ y, StepCosts.levelShare a L t Finset.univ y W) ∧
        (∀ y : TorusFields.TorusSite n,
          TorusFields.ContDiffThreeAt (StepCosts.levelShare a L t Finset.univ y) (TorusFields.trivialField n)) ∧
        ∀ (k : ℕ) (c : Fin k → TorusFields.TorusBond n) (Xs : Fin k → BlockAverages.imaginaryQuaternions) (l₀ : Fin k)
          (y : TorusFields.TorusSite n), 1 ≤ k → k ≤ 3 → BlockAverages.AreUnitVectors Xs →
          |TorusFields.mixedDeriv (StepCosts.levelShare a L t Finset.univ y) (TorusFields.trivialField n) c Xs| ≤
            D * Real.exp (-δ * TorusFields.supDist y (c l₀).1)) ∧
      ∀ (t n n' : ℕ) [NeZero n] [NeZero n'] (z : TorusFields.TorusSite n) (z' : TorusFields.TorusSite n') (m r : ℕ),
        64 ≤ n → 64 ≤ n' → 2 * m + 2 < n → 2 * m + 2 < n' → 4 * r + 4 ≤ m →
        ∀ (k : ℕ) (c : Fin k → (Fin 4 → ℤ) × Fin 4) (Xs : Fin k → BlockAverages.imaginaryQuaternions), 1 ≤ k → k ≤ 2 →
          BlockAverages.AreUnitVectors Xs →
          (∀ l, TorusFields.OffsetInBox r (c l).1) →
          |TorusFields.mixedDeriv (StepCosts.levelShare a L t Finset.univ z) (TorusFields.trivialField n)
                (fun l => TorusLumps.bondFrom z (c l)) Xs -
              TorusFields.mixedDeriv (StepCosts.levelShare a L t Finset.univ z') (TorusFields.trivialField n')
                (fun l => TorusLumps.bondFrom z' (c l)) Xs| ≤
            D * Real.exp (-δ * m)
end YangMills.Construction.TorusComparison
end
