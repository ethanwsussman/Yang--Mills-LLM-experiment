import YangMills.Construction.ClusterExpansionOfAStep.ActionAlongMoves
import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TorusComparison
def FlatActionDerivativesAgree : Prop :=
  ∀ (a δ : ℝ) (L : ℕ) (lam ρ σA cg : ℝ) (N : ℕ → ℝ), 0 < a → Odd L →
    ColdChain.ColdChainConstants a δ L lam ρ σA cg N →
    ∃ C : ℝ, 0 < C ∧ ∀ (t n n' : ℕ) [NeZero n] [NeZero n'] (X : Finset (TorusFields.TorusSite n))
      (X' : Finset (TorusFields.TorusSite n')) (z : TorusFields.TorusSite n) (z' : TorusFields.TorusSite n') (m r : ℕ),
      64 ≤ n → 64 ≤ n' → LevelAction.IsRegularRegion X 1024 → LevelAction.IsRegularRegion X' 1024 →
      4 * m + 2 < n → 4 * m + 2 < n' → 4 * r + 4 ≤ m →
      (∀ h, TorusFields.OffsetInBox (2 * m) h →
        (z + TorusFields.siteOfInt h ∈ X ↔ z' + TorusFields.siteOfInt h ∈ X')) →
      ∀ (k : ℕ) (c : Fin k → (Fin 4 → ℤ) × Fin 4) (Xs : Fin k → BlockAverages.imaginaryQuaternions), 1 ≤ k → k ≤ 2 →
        BlockAverages.AreUnitVectors Xs →
        (∀ l, TorusFields.OffsetInBox r (c l).1) →
        |TorusFields.mixedDeriv (TorusFields.actionAtLevel a L t X) (TorusFields.trivialField n)
              (fun l => TorusLumps.bondFrom z (c l)) Xs -
            TorusFields.mixedDeriv (TorusFields.actionAtLevel a L t X') (TorusFields.trivialField n')
              (fun l => TorusLumps.bondFrom z' (c l)) Xs| ≤
          C * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8)
end YangMills.Construction.TorusComparison
end
