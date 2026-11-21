import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.StepKernels
def singleLinkForm {a : ℝ} (b : InfiniteLattice.Link a) (X : Matrices.ComplexMatrix2) :
    InfiniteLattice.Link a → Matrices.ComplexMatrix2 :=
  open Classical in extendOddly fun b' => if b' = b then X else 0
def IsBoundedTracelessEndo (f : Matrices.ComplexMatrix2 → Matrices.ComplexMatrix2) (C : ℝ) :
    Prop :=
  ∃ T : ↥Matrices.ComplexMatrix2.traceless →ₗ[ℂ] ↥Matrices.ComplexMatrix2.traceless,
    (∀ X : ↥Matrices.ComplexMatrix2.traceless, (T X : Matrices.ComplexMatrix2) = f X) ∧
    ∀ X : ↥Matrices.ComplexMatrix2.traceless,
      Matrices.ComplexMatrix2.operatorNorm (T X : Matrices.ComplexMatrix2) ≤
        C * Matrices.ComplexMatrix2.operatorNorm (X : Matrices.ComplexMatrix2)
variable {L k j : ℕ}
def positiveDoubleCubeLinks (c : Edge L k (j + 1)) : Set (Edge L k j) :=
  {b | b ∈ doubleCubeLinks L (meshAt L k j) c ∧ b.IsPositivelyOriented}
structure StepKernelsAt (V : Edge L k j → Matrices.ComplexMatrix2) (c : Edge L k (j + 1)) :
    Prop where
  sum_eq_finsum : ∀ B ∈ complexEdgeForms (meshAt L k j),
    covariantSmoothingDeriv V B c =
      ∑ᶠ b ∈ positiveDoubleCubeLinks c, covariantSmoothingDeriv V (singleLinkForm b (B b)) c
  kernel_bound : ∀ b ∈ positiveDoubleCubeLinks c,
    IsBoundedTracelessEndo (fun X => covariantSmoothingDeriv V (singleLinkForm b X) c)
      (80 * (polydiscRadius L)⁻¹)
  conj_bound : ∀ y ∈ ({c.initial, c.terminal} : Set (Vertex L k (j + 1))),
    ∀ x ∈ cubeVertices L (meshAt L k j) y,
      IsBoundedTracelessEndo
        (Matrices.ComplexMatrix2.conjugateBy (complexContourMean L V y x)) 3
def StepKernelBounds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k →
    ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
      ∀ V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
        (∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < 3 / 4 * polydiscRadius L) →
          StepKernelsAt V c
end YangMills.Construction.Tower.FullSpace.StepKernels
end
