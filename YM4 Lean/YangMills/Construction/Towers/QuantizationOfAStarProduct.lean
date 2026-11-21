import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace Tower
open MagneticWeyl in
def WeylQuantMoyalProduct : Prop :=
  ∀ (L : ℕ) (φ : ℝ) (N' N'' N''' : ℕ) [NeZero N'] [NeZero N''] [NeZero N''']
    (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) (b : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ),
    IsWeylSymbol a → IsWeylSymbol b →
    (weylQuant L φ a).comp (weylQuant L φ b) = weylQuant L φ (moyalProduct φ a b)
end Tower
end YangMills.Construction
end
