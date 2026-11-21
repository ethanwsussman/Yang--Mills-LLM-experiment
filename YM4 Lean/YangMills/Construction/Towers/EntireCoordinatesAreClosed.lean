import YangMills.Construction.Towers.EntireCoordinatesOfAField
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
open EntireDependence
def EntireDependenceClosed : Prop :=
  ∀ (F : PeriodicOperators.PeriodicData) (S : Finset F.Carrier),
    (∀ c : ℂ, IsEntireOn F S fun _ => c) ∧
    (∀ κ ∈ S, IsEntireOn F S fun ζ => ζ κ) ∧
    (∀ g g', IsEntireOn F S g → IsEntireOn F S g' →
      IsEntireOn F S (fun ζ => g ζ + g' ζ) ∧ IsEntireOn F S (fun ζ => g ζ * g' ζ)) ∧
    (∀ S' g, S ⊆ S' → IsEntireOn F S g → IsEntireOn F S' g)
end YangMills.Construction.Tower.FullSpace
end
