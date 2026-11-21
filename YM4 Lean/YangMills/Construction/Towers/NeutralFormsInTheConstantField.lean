import YangMills.Construction.Towers.SymbolsOfTheConstantField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
def NeutralSectorOperator : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ f : ℝ, |f| ≤ Real.pi / 2 →
    ∀ v : Tower.UnitLatticeL2.VectorL2 L 4,
    Tower.AbelianFieldDensity.massiveOp (Tower.AbelianFieldDensity.scaledLinearAngle L f)
        (Tower.AbelianFieldDensity.SectorDecomposition.edgeTensor v
          (Matrices.ComplexMatrix2.pauliFamily 2)) =
      Tower.AbelianFieldDensity.SectorDecomposition.edgeTensor
        (Tower.MagneticWeyl.weylQuant L 0 (neutralSectorSymbol f) v)
        (Matrices.ComplexMatrix2.pauliFamily 2)
end YangMills.Construction.Tower.ConstantFieldSymbols
end
