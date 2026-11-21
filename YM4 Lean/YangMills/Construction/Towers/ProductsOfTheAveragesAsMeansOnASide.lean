import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.LinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open PeriodicLattice (FourTorus refinedBlock crossingPath sitesIn)
open Matrices
namespace Tower.IteratedSmoothingMeans
structure BlockMeanProperties (L m k n j : ℕ) : Prop where
  vertexSmoothing_iterate_eq :
    ∀ P : (∀ l, j - n ≤ l → (Vertex L m k (j - n) → ComplexMatrix2) → Vertex L m k l →
        ComplexMatrix2),
      (∀ h, P (j - n) h = id) →
      (∀ l (h : j - n ≤ l) (h' : j - n ≤ l + 1), P (l + 1) h' = vertexSmoothing L m k l ∘ P l h) →
      ∀ (f : Vertex L m k (j - n) → ComplexMatrix2) (y : Vertex L m k j),
        P j (Nat.sub_le j n) f y = ((L : ℂ) ^ (4 * n))⁻¹ •
          ∑ᶠ x ∈ (sitesIn (refinedBlock n y) : Set (Vertex L m k (j - n))), f x
  crossingSmoothing_iterate_eq :
    ∀ P : (∀ l, j - n ≤ l → (Edge L m k (j - n) → ComplexMatrix2) → Edge L m k l →
        ComplexMatrix2),
      (∀ h, P (j - n) h = id) →
      (∀ l (h : j - n ≤ l) (h' : j - n ≤ l + 1), P (l + 1) h' = crossingSmoothing L m k l ∘ P l h) →
      ∀ (B : Edge L m k (j - n) → ComplexMatrix2) (c : Edge L m k j),
        P j (Nat.sub_le j n) B c = ((L : ℂ) ^ (4 * n))⁻¹ •
          ∑ᶠ x ∈ (sitesIn (refinedBlock n c.source) : Set (Vertex L m k (j - n))),
            edgeFormPathSum B (crossingPath c x)
  crossingPath_length : ∀ (c : Edge L m k j) (x : Vertex L m k (j - n)),
    (x : FourTorus L m) ∈ refinedBlock n c.source → (crossingPath c x).length = L ^ n
  maxOperatorNorm_iterate_le :
    ∀ P : (∀ l, j - n ≤ l → (Edge L m k (j - n) → ComplexMatrix2) → Edge L m k l →
        ComplexMatrix2),
      (∀ h, P (j - n) h = id) →
      (∀ l (h : j - n ≤ l) (h' : j - n ≤ l + 1), P (l + 1) h' = crossingSmoothing L m k l ∘ P l h) →
      ∀ B : Edge L m k (j - n) → ComplexMatrix2,
        maxOperatorNorm (P j (Nat.sub_le j n) B) ≤ (L : ℝ≥0∞) ^ n * maxOperatorNorm B
def IteratedMeansStatement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m k n j : ℕ, 0 < m → 1 ≤ k → n ≤ j →
    j ≤ k → BlockMeanProperties L m k n j
end Tower.IteratedSmoothingMeans
end YangMills.Construction
end
