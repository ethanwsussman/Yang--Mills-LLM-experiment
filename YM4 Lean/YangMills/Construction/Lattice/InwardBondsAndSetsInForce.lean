import YangMills.Construction.Lattice.TowersAndMinimalConfigurations
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def IsActiveSetSetting (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) : Prop :=
  k ≤ K ∧ IsDeterminingChain K k Ω
def chainWithEmptyTail (k : ℕ) (Ω : ℕ → Set (FourTorus L m)) : ℕ → Set (FourTorus L m) :=
  Function.update Ω (k + 1) ∅
def IsInwardPointingBond (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) (j : ℕ)
    (b : BondAtLevel L m K j) : Prop :=
  j < k ∧ b ∈ determiningBondsAt K k Ω j ∧ b ∈ bondsMeeting (Ω (j + 1))
def inwardPointingBonds (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) :
    Set (Σ j : ℕ, BondAtLevel L m K j) :=
  {q | IsInwardPointingBond K k Ω q.1 q.2}
def IsReverseClosedInwardFamily (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (F : Set (Σ j : ℕ, BondAtLevel L m K j)) : Prop :=
  F ⊆ inwardPointingBonds K k Ω ∧
    ∀ q ∈ F, (⟨q.1, q.2.opposite⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ F
def determiningBondSetDiff (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (F : Set (Σ j : ℕ, BondAtLevel L m K j)) : Set (Σ j : ℕ, BondAtLevel L m K j) :=
  determiningBondSet K k Ω \ F
def determiningBondsAtDiff (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (F : Set (Σ j : ℕ, BondAtLevel L m K j)) (j : ℕ) : Set (BondAtLevel L m K j) :=
  {b | b ∈ determiningBondsAt K k Ω j ∧ (⟨j, b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∉ F}
def activeBondSet (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) :
    Set (Σ j : ℕ, BondAtLevel L m K j) :=
  determiningBondSet K k Ω \ inwardPointingBonds K k Ω
def activeBondsAt (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) (j : ℕ) :
    Set (BondAtLevel L m K j) :=
  {b | b ∈ determiningBondsAt K k Ω j ∧
    (⟨j, b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∉ inwardPointingBonds K k Ω}
end YangMills.Construction.PeriodicLattice
