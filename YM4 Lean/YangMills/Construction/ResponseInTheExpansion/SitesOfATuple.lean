import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import YangMills.Construction.ResponseInTheExpansion.SeveralSupportsInOneStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.WeightedResponses
abbrev blockMeanOfFunction (ℓ : StepParameters) (k m : ℕ) (f : PeriodicLattice.FourTorus ℓ.side m → ℝ)
    (z : TorusSite (2 * ℓ.side ^ m)) : ℝ :=
  blockMean ℓ.side k (2 * ℓ.side ^ m) z (testWeight ℓ.side k m f)
def InUnitCell {N : ℕ} (z : TorusSite N) (u : Fin 4 → ℝ) : Prop := ∀ μ, ((z μ).val : ℝ) ≤ u μ ∧ u μ < (z μ).val + 1
def tupleSupportSitesStatement : Prop :=
  ∀ (ℓ : StepParameters), Odd ℓ.side → ∀ (k m p : ℕ) (n vt : ℝ) (f : Fin p → PeriodicLattice.FourTorus ℓ.side m → ℝ),
    0 < vt → 16 ≤ n → 64 * n ≤ 2 * (ℓ.side : ℝ) ^ m → IsSeparatedTestTuple ℓ m n vt f →
    ∃ D : Fin p → Finset (TorusSite (2 * ℓ.side ^ m)),
      (∀ i, weightSupportSites ℓ.side k (2 * ℓ.side ^ m) (testWeight ℓ.side k m (f i)) ⊆ D i) ∧
      (∀ i, ((D i).card : ℝ) ≤ (64 * n) ^ 4) ∧
      (∀ i j, i ≠ j → ∀ z ∈ D i, ∀ z' ∈ D j, ∃ μ, n / 3 - 2 ≤ |LinearResponse.torusDisplacement z z' μ|) ∧
      (∀ i j, ∀ z ∈ D i, ∀ z' ∈ D j, ∀ μ, |LinearResponse.torusDisplacement z z' μ| ≤ 10 * n + 2) ∧
      (∀ i, ∀ z ∈ D i, ∀ u, InUnitCell z u →
        |blockMeanOfFunction ℓ k m (f i) z - f i (TorusMetric.torusProj (PeriodicLattice.torusSide ℓ.side m) u)| ≤ 4 / (vt * n)) ∧
      (∀ i z, z ∉ D i → ∀ u, InUnitCell z u → f i (TorusMetric.torusProj (PeriodicLattice.torusSide ℓ.side m) u) = 0) ∧
      (∀ i z, |blockMeanOfFunction ℓ k m (f i) z| ≤ 1) ∧
      (∀ i z, z ∉ weightSupportSites ℓ.side k (2 * ℓ.side ^ m) (testWeight ℓ.side k m (f i)) →
        blockMeanOfFunction ℓ k m (f i) z = 0) ∧
      (∀ i x, |f i x| ≤ 1) ∧
      ∀ i, Continuous fun v : Fin 4 → ℝ => f i (TorusMetric.torusProj (PeriodicLattice.torusSide ℓ.side m) v)
end YangMills.Construction.ResponseInTheExpansion
end
