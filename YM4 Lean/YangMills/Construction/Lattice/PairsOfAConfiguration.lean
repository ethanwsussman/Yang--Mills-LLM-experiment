import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open Matrices
variable {L m : ℕ}
abbrev finestBondsMeeting (K : ℕ) (X : Set (FourTorus L m)) : Set (BondAtLevel L m K 0) :=
  bondsMeeting X
abbrev PositiveFinestBondOf (K : ℕ) (X : Set (FourTorus L m)) : Type :=
  PositiveBondOf (finestBondsMeeting K X)
def fieldCurrentPairs (K : ℕ) (X : Set (FourTorus L m)) :
    Set (PositiveFinestBondOf K X ⊕ PositiveFinestBondOf K X → ComplexMatrix2) :=
  GroupLieProduct (PositiveFinestBondOf K X) (PositiveFinestBondOf K X)
def pairOf {K : ℕ} {X : Set (FourTorus L m)} (V J : PositiveFinestBondOf K X → ComplexMatrix2) :
    PositiveFinestBondOf K X ⊕ PositiveFinestBondOf K X → ComplexMatrix2 :=
  Sum.elim V J
end PeriodicLattice
end YangMills.Construction
