import YangMills.Construction.Towers.ChargedFormOfTheConstantFieldDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
def PairsFormIsWeylForm : Prop :=
  ∀ (ι : Type) [Fintype ι] (P : ι → TermPair) (L : ℕ) (φ : ℝ) (w : UnitLatticeL2.VectorL2 L 4),
    pairsForm P L φ w = inner ℂ w (MagneticWeyl.weylQuant L φ (pairsSymbol P φ) w)
end YangMills.Construction.Tower.ConstantFieldSymbols
end
