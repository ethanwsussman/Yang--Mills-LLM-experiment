import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
namespace StepKernels
variable {L n k j : ℕ}
def singleBondForm (b : Edge L n k j) (X : Matrices.ComplexMatrix2) :
    Edge L n k j → Matrices.ComplexMatrix2 :=
  open Classical in extendOddly fun b' => if b' = b then X else 0
def positiveDoubleBlockEdges (c : Edge L n k (j + 1)) : Set (Edge L n k j) :=
  {b | b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) ∧ b.IsPositivelyOriented}
def stepKernel (V : Edge L n k j → Matrices.ComplexMatrix2) (c : Edge L n k (j + 1))
    (b : Edge L n k j) : Matrices.ComplexMatrix2 → Matrices.ComplexMatrix2 :=
  fun X => covariantSmoothingDeriv V (singleBondForm b X) c
structure IsBoundedTracelessEndo (T : Matrices.ComplexMatrix2 → Matrices.ComplexMatrix2)
    (C : ℝ) : Prop where
  mapsTo : ∀ X ∈ Matrices.ComplexMatrix2.traceless, T X ∈ Matrices.ComplexMatrix2.traceless
  map_add : ∀ X ∈ Matrices.ComplexMatrix2.traceless, ∀ Y ∈ Matrices.ComplexMatrix2.traceless,
    T (X + Y) = T X + T Y
  map_smul : ∀ z : ℂ, ∀ X ∈ Matrices.ComplexMatrix2.traceless, T (z • X) = z • T X
  norm_le : ∀ X ∈ Matrices.ComplexMatrix2.traceless,
    Matrices.ComplexMatrix2.operatorNorm (T X) ≤ C * Matrices.ComplexMatrix2.operatorNorm X
def StepKernelBounds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j < k →
    ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
        (∀ b, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < 3 / 4 * polydiscRadius L) →
          (∀ B ∈ complexEdgeForms L n k j,
            covariantSmoothingDeriv V B c =
              ∑ᶠ b ∈ positiveDoubleBlockEdges c, stepKernel V c b (B b)) ∧
          (∀ b ∈ positiveDoubleBlockEdges c,
            IsBoundedTracelessEndo (stepKernel V c b) (80 * (polydiscRadius L)⁻¹)) ∧
          ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
            ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
              IsBoundedTracelessEndo
                (Matrices.ComplexMatrix2.conjugateBy
                  (PeriodicLattice.complexMeanContourHolonomy V y x)) 3
end StepKernels
end YangMills.Construction.Tower
end
