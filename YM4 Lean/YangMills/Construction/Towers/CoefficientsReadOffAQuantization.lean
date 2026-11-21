import YangMills.Construction.Towers.TheDensityOfAnAbelianField
import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tower.UnitLatticeL2 Tower.UnitaryCombinations Tower.AbelianFieldDensity OneLoopNotation
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (torusAverage castVec)
namespace Tower
open MagneticWeyl in
def FourierCoeffsFromQuantization : Prop :=
  ∀ (L : ℕ) (φ : ℝ),
    (∀ (N' N'' : ℕ) [NeZero N'] [NeZero N''] (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ),
      IsWeylSymbol a →
      (∀ n : Fin 4 → ℤ, fourierCoeff a n =
        matrixAtZero ((matMulUnitaryOp (1 : Matrix (Fin N') (Fin N') ℂ)
          (magneticWeyl L φ (-n))).comp (weylQuant L φ a))) ∧
      ∀ v : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ, IsWeylSymbol v →
        weylQuant L φ a = weylQuant L φ v → a = v) ∧
    ∀ (N' : ℕ) [NeZero N'] (a : AmbientSpace → Matrix (Fin N') (Fin N') ℂ), IsWeylSymbol a →
      vecTraceAt (weylQuant L φ a) 0 = Matrices.RectangularMatrix.diagSum (fourierCoeff a 0) ∧
      Matrices.RectangularMatrix.diagSum (fourierCoeff a 0) =
        torusAverage fun q => Matrices.RectangularMatrix.diagSum (a q)
end Tower
end YangMills.Construction
end
