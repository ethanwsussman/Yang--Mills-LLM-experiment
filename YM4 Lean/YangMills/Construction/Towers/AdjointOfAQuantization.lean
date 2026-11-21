import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open MagneticWeyl in
def WeylQuantAdjoint : Prop :=
  ∀ (L : ℕ) (φ : ℝ) (N' N'' : ℕ) [NeZero N'] [NeZero N'']
    (a : InfiniteLattice.AmbientSpace → Matrix (Fin N') (Fin N'') ℂ), IsWeylSymbol a →
    IsWeylSymbol (pointwiseAdjoint a) ∧
    UnitLatticeL2.opAdjoint (weylQuant L φ a) = weylQuant L φ (pointwiseAdjoint a)
end YangMills.Construction.Tower
end
