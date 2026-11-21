import YangMills.Construction.TransferOperators.ObjectsOfAnInsertionOfContractionsBetweenLayers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice SpinHarmonics
open scoped ComplexOrder
namespace TransferOperators
namespace CubicPeriodSublattice
variable (Γ : CubicPeriodSublattice) {μ : Fin 4} (B : Block μ)
def ExpShiftIntegrandEqProdKernels (β : ℝ) (Ξ : B.L2Operator) (i : ℤ)
    (Q' : AddSubgroup (LatticePoint 1)) : Prop :=
  ∀ U : Γ.lattice.QuotientField,
    ((Real.exp (Γ.lattice.cosetSumOfShifts Q' (B.logKernelRatio β Ξ i) U) *
        Γ.lattice.boltzmannWeight β U : ℝ) : ℂ) =
      ∏ j : ZMod Γ.side,
        Complex.exp (-Γ.sliceEnergy β (Γ.sliceField (μ := μ) U j)) *
          sqrtKernelSandwich β (Γ.levelProductOp B Ξ i Q' j)
            (Γ.sliceField (μ := μ) U j)
            (Γ.orbitGaugeAct (Γ.temporalSliceField (μ := μ) U j)
              (Γ.sliceField (μ := μ) U (j + 1)))
end CubicPeriodSublattice
namespace ExpShiftIntegrand
def ProdStatement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (μ : Fin 4) (B : Block μ) (Ξ : B.L2Operator),
    ‖Ξ‖ ≤ 1 → IsRealPreserving Ξ →
    (∀ g : B.vertices → Matrices.ComplexMatrix2.specialUnitary, Commute Ξ (blockGaugeRep B g)) →
    (∀ u u' : ↥(B.links : Set (SliceLink μ)) → Matrices.ComplexMatrix2.specialUnitary,
      0 < sqrtKernelSandwich β Ξ u u') →
    ∀ (i : ℤ) (Q' : AddSubgroup (LatticePoint 1)), Q'.FiniteIndex → B.PairwiseDisjointShifts i Q' →
      ∀ Γ : CubicPeriodSublattice, Γ.lattice.periods ≤ Q' →
        Γ.ExpShiftIntegrandEqProdKernels B β Ξ i Q'
end ExpShiftIntegrand
end TransferOperators
end YangMills.Construction
end
