import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (castVec)
namespace Tower
open MagneticWeyl in
def MoyalProductBounds : Prop :=
  ∀ (φ : ℝ) (N' N'' N''' : ℕ) [NeZero N'] [NeZero N''] [NeZero N''']
    (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) (b : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ),
    IsWeylSymbol a → IsWeylSymbol b →
    (∀ j : ℕ, j ≤ 3 →
      Summable (fun n => Matrices.RectangularMatrix.opNormValue (moyalCoeff φ a b n) *
        (1 + TorusMetric.euclidNormVec (castVec n)) ^ j) ∧
      ∑' n, Matrices.RectangularMatrix.opNormValue (moyalCoeff φ a b n) *
        (1 + TorusMetric.euclidNormVec (castVec n)) ^ j ≤ weightedCoeffNorm j a * weightedCoeffNorm j b) ∧
    HasFourierExpansion (moyalCoeff φ a b) (moyalProduct φ a b) ∧
    IsWeylSymbol (moyalProduct φ a b) ∧
    fourierCoeff (moyalProduct φ a b) = moyalCoeff φ a b ∧
    ∀ j : ℕ, j ≤ 3 → weightedCoeffNorm j (moyalProduct φ a b) ≤ weightedCoeffNorm j a * weightedCoeffNorm j b
end Tower
end YangMills.Construction
end
