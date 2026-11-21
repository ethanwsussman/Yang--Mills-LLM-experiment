import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import YangMills.Construction.Towers.TheSettingOfTheRemainder
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions
open PeriodicOperators
def IsLocalEntire (L k : ℕ) (I I' : PeriodicData)
    (T : ((remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) : Prop :=
  IsLocalOpFun (remainderIndex L k) I I' T ∧
    HasEntireKernelEntries (remainderIndex L k) I I' T
def IsLocalBelowNorm (L k : ℕ) (I I' : PeriodicData)
    (T : ((remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) (a : ℝ) : Prop :=
  ∃ ρ R : ℝ, IsLocalWith (remainderIndex L k) I I' T ρ R ∧
    ∀ ζ, IsSupBelow (remainderIndex L k) ζ ρ →
      maxOperatorNorm ((edgePauliCoordinates L k 0).ofCoeffs ζ) < ENNReal.ofReal a
section Pairs
variable {I I' : PeriodicData}
def IsHolomorphicInMomentumPair
    (S : Set (Coordinates.ComplexCoordinates 4 × Coordinates.ComplexCoordinates 4))
    (A : Coordinates.ComplexCoordinates 4 → Coordinates.ComplexCoordinates 4 → QuotHom I I') :
    Prop :=
  HoldsOnAppended (n := 4) (n' := 4) (fun O M => QuotHomFamilyHolomorphicOn O M) S
    fun q => A q.2 q.1
end Pairs
def JetComponentsHolomorphic (L k : ℕ) (I I' : PeriodicData) : Prop :=
  ∀ T : ((remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ,
    IsLocalOpFun (remainderIndex L k) I I' T →
    ∀ (O : Set (Coordinates.ComplexCoordinates 4)) (εp εm : Coordinates.ComplexCoordinates 4 →
        (remainderIndex L k).UnitQuot → ℂ),
      HolomorphicOnEntrywise quotFnEntries O εp →
      HolomorphicOnEntrywise quotFnEntries O εm →
      IsHolomorphicInMomentumPair (univ ×ˢ O)
          (fun p => (jetAlong (remainderIndex L k) I I' T p (εp p) (εm p)).f00) ∧
        IsHolomorphicInMomentumPair (univ ×ˢ O)
          (fun p => (jetAlong (remainderIndex L k) I I' T p (εp p) (εm p)).f10) ∧
        IsHolomorphicInMomentumPair (univ ×ˢ O)
          (fun p => (jetAlong (remainderIndex L k) I I' T p (εp p) (εm p)).f01) ∧
        IsHolomorphicInMomentumPair (univ ×ˢ O)
          (fun p => (jetAlong (remainderIndex L k) I I' T p (εp p) (εm p)).f11)
section Families
variable {I I' : PeriodicData}
def ComponentOpenDomain (P : Set (Coordinates.ComplexCoordinates 4))
    (D : Coordinates.ComplexCoordinates 4 → Set (Fin 4 → ℂ))
    (A : Coordinates.ComplexCoordinates 4 → Coordinates.ComplexCoordinates 4 → QuotHom I I') :
    Prop :=
  ∃ W : Set (Coordinates.ComplexCoordinates 4 × Coordinates.ComplexCoordinates 4),
    (∀ q ∈ W, q.2 ∈ P) ∧ (∀ p ∈ P, ∀ κ ∈ D p, (κ, p) ∈ W) ∧ IsHolomorphicInMomentumPair W A
structure JetFamilyHolomorphic (δ : ℝ) (P : Set (Coordinates.ComplexCoordinates 4))
    (T : Coordinates.ComplexCoordinates 4 → JetQuad I I') : Prop where
  is_jet : ∀ p ∈ P, JetQuad.IsJet δ p (T p)
  open00 : ComponentOpenDomain P (fun _ => imStrip (2 * δ)) fun p => (T p).f00
  open10 : ComponentOpenDomain P (fun p => stripAddShift δ p) fun p => (T p).f10
  open01 : ComponentOpenDomain P (fun p => stripSubShift δ p) fun p => (T p).f01
  open11 : ComponentOpenDomain P (fun _ => realDualPoints) fun p => (T p).f11
end Families
end YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions
end
