import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open MagneticWeyl UnitaryCombinations OneLoopNotation in
def MagneticWeylRelations : Prop :=
  ∀ (L : ℕ) (φ : ℝ) (m m' : Fin 4 → ℤ),
    (∀ w : ScalarL2 L, magneticWeyl L φ m (magneticWeyl L φ m' w) =
      Complex.exp (Complex.I / 2 * (φ : ℂ) * (symplecticForm m m' : ℂ)) • magneticWeyl L φ (m + m') w) ∧
    (∀ w : ScalarL2 L, magneticWeyl L φ 0 w = w) ∧
    (∀ f g : ScalarL2 L,
      inner ℂ (magneticWeyl L φ (-m) f) g = inner ℂ f (magneticWeyl L φ m g)) ∧
    ∀ v : EuclideanSpace ℂ (Fin 1),
      magneticWeyl L φ m (vectorAtZero L v) 0 = (kronecker m 0 : ℂ) • v
end YangMills.Construction.Tower
end
