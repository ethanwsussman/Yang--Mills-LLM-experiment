import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.LinearMapsAtTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IteratedSmoothing
structure MeansBetweenLevels (L k n j : ℕ) : Prop where
  vertexSmoothing_iterate_eq :
    ∀ P : (∀ l, j - n ≤ l → (Vertex L k (j - n) → Matrices.ComplexMatrix2) → Vertex L k l →
        Matrices.ComplexMatrix2),
      (∀ h, P (j - n) h = id) →
      (∀ l (h : j - n ≤ l) (h' : j - n ≤ l + 1),
        P (l + 1) h' = vertexSmoothing (a := meshAt L k (l + 1)) L ∘ P l h) →
      ∀ (f : Vertex L k (j - n) → Matrices.ComplexMatrix2) (y : Vertex L k j),
        P j (Nat.sub_le j n) f y = ((L : ℂ) ^ (4 * n))⁻¹ •
          ∑ᶠ x ∈ {x : Vertex L k (j - n) |
            (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n y}, f x
  crossingSmoothing_iterate_eq :
    ∀ P : (∀ l, j - n ≤ l → (Edge L k (j - n) → Matrices.ComplexMatrix2) → Edge L k l →
        Matrices.ComplexMatrix2),
      (∀ h, P (j - n) h = id) →
      (∀ l (h : j - n ≤ l) (h' : j - n ≤ l + 1),
        P (l + 1) h' = crossingSmoothing (a := meshAt L k (l + 1)) L ∘ P l h) →
      ∀ (B : Edge L k (j - n) → Matrices.ComplexMatrix2) (c : Edge L k j),
        P j (Nat.sub_le j n) B c = ((L : ℂ) ^ (4 * n))⁻¹ •
          ∑ᶠ x ∈ {x : Vertex L k (j - n) |
            (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial},
            edgeFormPathSum B (crossingPath c x)
  crossingPath_length : ∀ (c : Edge L k j) (x : Vertex L k (j - n)),
    (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial →
      (crossingPath c x).length = L ^ n
  maxOperatorNorm_crossingSmoothing_iterate_le :
    ∀ P : (∀ l, j - n ≤ l → (Edge L k (j - n) → Matrices.ComplexMatrix2) → Edge L k l →
        Matrices.ComplexMatrix2),
      (∀ h, P (j - n) h = id) →
      (∀ l (h : j - n ≤ l) (h' : j - n ≤ l + 1),
        P (l + 1) h' = crossingSmoothing (a := meshAt L k (l + 1)) L ∘ P l h) →
      ∀ B : Edge L k (j - n) → Matrices.ComplexMatrix2,
        maxOperatorNorm (P j (Nat.sub_le j n) B) ≤ (L : ℝ≥0∞) ^ n * maxOperatorNorm B
def IteratedSmoothingAsMeans : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n j : ℕ, 1 ≤ k → n ≤ j → j ≤ k →
    MeansBetweenLevels L k n j
end YangMills.Construction.Tower.FullSpace.IteratedSmoothing
end
