import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace Tower
open MagneticWeyl in
def MoyalProductWithConstant : Prop :=
  ∀ (φ : ℝ) (N' N'' : ℕ) [NeZero N'] [NeZero N''] (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ),
    IsWeylSymbol a → ∀ (M : ℕ) [NeZero M],
      (∀ c : Matrix (Fin N'') (Fin M) ℂ, moyalProduct φ a (fun _ => c) = fun q => a q * c) ∧
      ∀ c : Matrix (Fin M) (Fin N') ℂ, moyalProduct φ (fun _ => c) a = fun q => c * a q
end Tower
end YangMills.Construction
end
