import YangMills.Construction.Towers.StepKernelsOfTheCovariantAveragesOnASide
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace NearIdentityStepKernels
open YangMills.Construction.Tower.StepKernels
open Matrices
variable {L n k j : ℕ}
def doubleBlockDistToOne (V : Edge L n k j → ComplexMatrix2) (c : Edge L n k (j + 1)) : ℝ :=
  sSup ((fun e => ComplexMatrix2.operatorNorm (V e - 1)) ''
    (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)))
def StepKernelNearIdentityBound : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j < k →
    ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      ∀ V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
        (∀ e, ComplexMatrix2.operatorNorm (V e - 1) < polydiscRadius L / 2) →
          (∀ e ∈ positiveDoubleBlockEdges c, ∀ X ∈ ComplexMatrix2.traceless,
            ComplexMatrix2.operatorNorm (stepKernel V c e X - stepKernel (fun _ => 1) c e X) ≤
              1280 * (polydiscRadius L)⁻¹ ^ 2 * doubleBlockDistToOne V c *
                ComplexMatrix2.operatorNorm X) ∧
          ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
            ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
              ∀ X ∈ ComplexMatrix2.traceless,
                ComplexMatrix2.operatorNorm
                    (ComplexMatrix2.conjugateBy
                      (PeriodicLattice.complexMeanContourHolonomy V y x) X - X) ≤
                  1280 * (polydiscRadius L)⁻¹ ^ 2 * doubleBlockDistToOne V c *
                    ComplexMatrix2.operatorNorm X
end NearIdentityStepKernels
end Tower
end YangMills.Construction
end
