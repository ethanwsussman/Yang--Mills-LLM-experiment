import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace Tower
open MagneticWeyl UnitaryCombinations OneLoopNotation in
def WeylQuantHasSum : Prop :=
  ∀ (L : ℕ) (φ : ℝ) (N' N'' : ℕ) [NeZero N'] [NeZero N'']
    (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ), HasAbsSummableFourier a →
    HasSum (fun n => matMulUnitaryOp (fourierCoeff a n) (magneticWeyl L φ n))
      (weylQuant L φ a) ∧
    opNormOf (weylQuant L φ a) ≤ weightedCoeffNorm 0 a
end Tower
end YangMills.Construction
end
