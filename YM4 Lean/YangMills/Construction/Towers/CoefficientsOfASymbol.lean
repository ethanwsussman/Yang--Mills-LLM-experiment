import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tower.UnitLatticeL2 Tower.UnitaryCombinations OneLoopNotation
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (torusAverage castVec)
namespace Tower
open MagneticWeyl in
def FourierCoeffsOfSymbol : Prop :=
  ∀ (N' N'' : ℕ) [NeZero N'] [NeZero N''] (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ),
    (HasAbsSummableFourier a →
      HasFourierExpansion (fourierCoeff a) a ∧
        (Summable fun n => Matrices.RectangularMatrix.opNormValue (fourierCoeff a n)) ∧
        ∀ c : (Fin 4 → ℤ) → Matrix (Fin N') (Fin N'') ℂ, HasFourierExpansion c a →
          (Summable fun n => Matrices.RectangularMatrix.opNormValue (c n)) → c = fourierCoeff a) ∧
    (IsWeylSymbol a → HasAbsSummableFourier a ∧ ∀ k : ℕ, k ≤ 3 → Summable fun n =>
      Matrices.RectangularMatrix.opNormValue (fourierCoeff a n) *
        (1 + TorusMetric.euclidNormVec (castVec n)) ^ k)
end Tower
end YangMills.Construction
end
