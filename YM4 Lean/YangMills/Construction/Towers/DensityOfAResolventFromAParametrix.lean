import YangMills.Construction.Towers.TheDensityOfAnAbelianField
import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open OperatorCalculus Tower.UnitLatticeL2
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (torusAverage)
namespace Tower.MagneticWeyl
def ResolventDensityViaParametrix : Prop :=
  ∀ (L N' : ℕ) [NeZero N'] (φ z w : ℝ), 0 < z → 0 ≤ w →
    ∀ σ ρ e : AmbientSpace → Matrix (Fin N') (Fin N') ℂ, IsWeylSymbol σ → IsWeylSymbol ρ →
      IsWeylSymbol e →
      (∀ q, pointwiseAdjoint σ q = σ q) →
      IsBoundedBelowBy (addScalar (weylQuant L φ σ) z) (z / 2) →
      moyalProduct φ ρ (fun q => σ q + ((z + w : ℝ) : ℂ) • (1 : Matrix (Fin N') (Fin N') ℂ)) =
        (fun q => 1 + e q) →
      ‖AbelianFieldDensity.vecTraceAt
          (inverseOp (addScalar (addScalar (weylQuant L φ σ) z) w)) 0 -
        torusAverage fun q => Matrices.RectangularMatrix.diagSum (ρ q)‖ ≤
      (N' : ℝ) * weightedCoeffNorm 0 e * (z / 2 + w)⁻¹
end Tower.MagneticWeyl
end YangMills.Construction
end
