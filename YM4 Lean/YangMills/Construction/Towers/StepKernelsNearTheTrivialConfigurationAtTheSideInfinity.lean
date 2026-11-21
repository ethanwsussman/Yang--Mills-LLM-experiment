import YangMills.Construction.Towers.StepKernelsOfTheIteratedAveragesAtTheSideInfinity
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.StepKernelsNearIdentity
open YangMills.Construction.Tower.FullSpace.StepKernels (singleLinkForm positiveDoubleCubeLinks)
open Matrices
variable {L k j : ℕ}
structure NearIdentityBounds (V : Edge L k j → ComplexMatrix2) (c : Edge L k (j + 1))
    (s : ℝ) : Prop where
  kernel_le : ∀ e ∈ positiveDoubleCubeLinks c, ∀ X : ↥ComplexMatrix2.traceless,
    ComplexMatrix2.operatorNorm (covariantSmoothingDeriv V (singleLinkForm e (X : ComplexMatrix2)) c -
        covariantSmoothingDeriv (L := L) (k := k) (j := j) (fun _ => 1)
          (singleLinkForm e (X : ComplexMatrix2)) c) ≤
      1280 * (polydiscRadius L)⁻¹ ^ 2 * s * ComplexMatrix2.operatorNorm (X : ComplexMatrix2)
  conj_le : ∀ y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))),
    ∀ x ∈ cubeVertices L (meshAt L k j) y, ∀ X : ↥ComplexMatrix2.traceless,
      ComplexMatrix2.operatorNorm (ComplexMatrix2.conjugateBy (complexContourMean L V y x)
          (X : ComplexMatrix2) - (X : ComplexMatrix2)) ≤
        1280 * (polydiscRadius L)⁻¹ ^ 2 * s * ComplexMatrix2.operatorNorm (X : ComplexMatrix2)
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k →
    ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
      ∀ V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
        (∀ e, ComplexMatrix2.operatorNorm (V e - 1) < polydiscRadius L / 2) →
        ∀ s : ℝ, (∀ e ∈ doubleCubeLinks L (meshAt L k j) c,
            ComplexMatrix2.operatorNorm (V e - 1) ≤ s) →
          NearIdentityBounds V c s
end YangMills.Construction.Tower.FullSpace.StepKernelsNearIdentity
end
