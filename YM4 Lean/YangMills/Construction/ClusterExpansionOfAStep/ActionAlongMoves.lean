import YangMills.Construction.ClusterExpansionOfAStep.ConstantsOfTheColdChain
import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace LevelAction
open TorusFields BlockAverages ColdChain
variable {n : ℕ}
def IsRegularRegion (X : Finset (TorusSite n)) (m : ℕ) : Prop :=
  ∀ z : TorusSite n, ∃ ε : Fin 4 → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    ∀ q ∈ X, supDist q z ≤ m → ∀ h : Fin 4 → ℤ, (∀ i, 0 ≤ ε i * h i) → (∀ i, |h i| ≤ (m : ℤ)) →
      q + siteOfInt h ∈ X
def IsColdOn [NeZero n] (s : ℝ) (X : Finset (TorusSite n)) (W : TorusField n) : Prop :=
  ∀ p ∈ plaquettesIn X, curvature W p.1 p.2.1 p.2.2 < s
def bondListSpread {k : ℕ} (c : Fin k → TorusBond n) : ℕ :=
  Finset.univ.sup fun l : Fin k => Finset.univ.sup fun l' : Fin k => supDist (c l).1 (c l').1
def ActionSmoothAlongMoves : Prop :=
  ∀ (a δ : ℝ) (L : ℕ) (lam ρ σA cg : ℝ) (N : ℕ → ℝ), 0 < a → Odd L → ColdChainConstants a δ L lam ρ σA cg N →
    ∃ C : ℝ, 0 < C ∧ ∀ (t n : ℕ) [NeZero n], 64 ≤ n → ∀ (X : Finset (TorusSite n)) (W : TorusField n),
      IsRegularRegion X 1024 → IsColdOn σA X W →
        ContDiffThreeAt (actionAtLevel a L t X) W ∧
        (∀ (k : ℕ) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors Xs →
          |mixedDeriv (actionAtLevel a L t X) W c Xs| ≤ C * Real.exp (-δ * bondListSpread c)) ∧
        ∀ (X' : Finset (TorusSite n)) (W' : TorusField n) (z : TorusSite n) (m : ℕ),
          IsRegularRegion X' 1024 → IsColdOn σA X' W' →
          2 * m + 2 < n → (∀ y, supDist y z ≤ 2 * m → (y ∈ X ↔ y ∈ X')) →
          (∀ y i, supDist y z ≤ 2 * m → supDist (y + TorusFields.unitStep n i) z ≤ 2 * m → W y i = W' y i) →
          ∀ (k : ℕ) (c : Fin k → TorusBond n) (Xs : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 2 → AreUnitVectors Xs →
            (∀ l, 4 * supDist (c l).1 z + 4 ≤ m) →
            |mixedDeriv (actionAtLevel a L t X) W c Xs - mixedDeriv (actionAtLevel a L t X') W' c Xs| ≤
              C * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8)
end LevelAction
end YangMills.Construction
end
