import YangMills.Construction.Towers.ChargedFormOfTheConstantFieldDefs
import YangMills.Construction.Towers.LogarithmsSectorsAndDensityDefs
import YangMills.Construction.Towers.TheCoefficientAsAResponseToAConstantField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open UnitLatticeL2
namespace ConstantFieldSymbols
open AbelianFieldDensity AbelianFieldDensity.SectorDecomposition
def ChargedSectorClaim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ f : ℝ, |f| ≤ Real.pi / 2 →
    ∃ S : VectorL2 L 4 →L[ℂ] VectorL2 L 4, IsSelfAdjointOp S ∧
      (∀ v : VectorL2 L 4,
        AbelianFieldDensity.massiveOp (scaledLinearAngle L f) (edgeTensor v raisingPauli) =
          edgeTensor (S v) raisingPauli) ∧
      ∀ w : VectorL2 L 4, (Function.support fun x => w x).Finite →
        ∃ B : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2, IsLieFormOf w B ∧
          FullSpace.HasFiniteEdgeSupport B ∧
          FullSpace.finiteEdgePairing B
              (FullSpace.abelianMassiveHessian (scaledLinearAngle L f) B) =
            (((inner ℂ w (S w) : ℂ).re : ℝ) : ℂ)
end ConstantFieldSymbols
end YangMills.Construction.Tower
end
