import YangMills.Construction.Towers.SecondOrderInTheFlux
import YangMills.Construction.Towers.SymbolsOfTheConstantField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
open OperatorCalculus UnitLatticeL2
open InfiniteLattice (AmbientSpace)
open MagneticWeyl MagneticWeyl.FluxSecondOrder AbelianFieldDensity AbelianFieldDensity.SectorDecomposition
def densitySectorDecomposition : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z → ∃ c : ℂ, ∀ f : ℝ,
    |f| ≤ Real.pi / 2 → 24 * |Real.sin f| ≤ z / 2 →
      DensityDefined z (scaledLinearAngle L f) ∧
      IsBoundedBelowBy (addScalar (weylQuant L (2 * f) scalarMultiplier) z) (z / 2) ∧
      ∀ a : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ,
        (∀ v : VectorL2 L 4,
          AbelianFieldDensity.massiveOp (scaledLinearAngle L f) (edgeTensor v raisingPauli) =
            edgeTensor (weylQuant L (2 * f) a v) raisingPauli) →
        IsBoundedBelowBy (addScalar (weylQuant L (2 * f) a) z) (z / 2) ∧
          densityAt z (scaledLinearAngle L f) (0 : FullSpace.Vertex L 0 0) =
            c + 2 * logTrace L z (2 * f) scalarMultiplier -
              1 / 2 * logTrace L z 0 (neutralSectorSymbol f) -
              logTrace L z (2 * f) a
end YangMills.Construction.Tower.ConstantFieldSymbols
end
