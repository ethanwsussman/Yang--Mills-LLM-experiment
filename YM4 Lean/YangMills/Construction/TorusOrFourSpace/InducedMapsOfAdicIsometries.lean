import YangMills.Construction.TorusOrFourSpace.AdicIsometriesInducedMapsAndActions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.AdicInducedMaps
open PeriodicLattice (SignedFrame)
variable (D : Params) (E : Kind)
abbrev adicLat (j : ℕ) : AddSubgroup (Fin 4 → ℝ) :=
  InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize D.L (j : ℤ))
abbrev shiftedFrameMap (a : Fin 4 → ℝ) (w : SignedFrame) : (Fin 4 → ℝ) → Fin 4 → ℝ :=
  translateR4 a ∘ w.actOnVector
def AdicPointsEqIUnion : Prop :=
  adicPoints4 D.L = ⋃ j : ℕ, (adicLat D j : Set (Fin 4 → ℝ))
def AdicLatMono : Prop :=
  ∀ j j' : ℕ, j ≤ j' → (adicLat D j : Set (Fin 4 → ℝ)) ⊆ adicLat D j'
def EventuallyMemAdicLat : Prop :=
  ∀ a ∈ adicPoints4 D.L, ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → a ∈ adicLat D j
def FrameMovesPeriods : Prop :=
  ∀ a ∈ adicPoints4 D.L, ∀ w : SignedFrame, ∀ x : Fin 4 → ℝ, ∀ k ∈ E.periodGroup D,
    shiftedFrameMap a w (x + k) = shiftedFrameMap a w x + w.actOnVector k ∧
      w.actOnVector k ∈ E.periodGroup D
def QuotConstOnCosets : Prop :=
  ∀ a ∈ adicPoints4 D.L, ∀ w : SignedFrame, ∀ x : Fin 4 → ℝ, ∀ k ∈ E.periodGroup D,
    E.quotMap D (shiftedFrameMap a w (x + k)) = E.quotMap D (shiftedFrameMap a w x)
def ExistsUniqueDescended : Prop :=
  ∀ a ∈ adicPoints4 D.L, ∀ w : SignedFrame,
    ∃! r : E.Pt D → E.Pt D, Kind.InducedBy D E (shiftedFrameMap a w) r
def DescendedOnTorus : Prop :=
  ∀ a ∈ adicPoints4 D.L, ∀ w : SignedFrame,
    Kind.descendedMap D Kind.torus (shiftedFrameMap a w) =
      fun y => Kind.signedFrameMap D Kind.torus w y + Kind.quotMap D Kind.torus a
def AdicIsoEqFrameAddConst : Prop :=
  ∀ r ∈ Kind.adicIsometriesQ D E, ∃ w : SignedFrame, ∃ b ∈ E.quotMap D '' adicPoints4 D.L,
    r = fun y => Kind.signedFrameMap D E w y + b
def AdicLatticesAndInducedMaps : Prop :=
  ∀ (D : Params) (E : Kind),
    AdicPointsEqIUnion D ∧ AdicLatMono D ∧
      EventuallyMemAdicLat D ∧ FrameMovesPeriods D E ∧
      QuotConstOnCosets D E ∧ ExistsUniqueDescended D E ∧
      DescendedOnTorus D ∧ AdicIsoEqFrameAddConst D E
end YangMills.Construction.PeriodicSpace.AdicInducedMaps
