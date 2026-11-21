import YangMills.Construction.TorusOrFourSpace.NeighbourhoodsOfACompactSet
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.DiagonalLimits
variable (D : Params) (E : Kind)
abbrev openNhdWidth (S : Set (E.Pt D)) (hS : Kind.IsCompactQ D E S) (η : ℝ)
    (hη : 0 < η) : Set (E.Pt D) :=
  Kind.openThickening D E S hS η hη
abbrev closedNhdWidth (S : Set (E.Pt D)) (hS : Kind.IsCompactQ D E S) (η : ℝ)
    (hη : 0 < η) : Set (E.Pt D) :=
  Kind.closedThickening D E S hS η hη
end YangMills.Construction.PeriodicSpace.DiagonalLimits
