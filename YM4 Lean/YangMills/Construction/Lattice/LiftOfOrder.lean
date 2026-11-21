import YangMills.Construction.Lattice.LiftOfBlockFields
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K k : ℕ}
def IsInsideBlockAt (j : ℕ) (y : SiteAtLevel L m K k) (b : BondAtLevel L m K j) : Prop :=
  (b.source : FourTorus L m) ∈ blockAtLevel j y ∧ (b.target : FourTorus L m) ∈ blockAtLevel j y
abbrev bondsInsideOrOverCoarse (j : ℕ) (C : Set (BondAtLevel L m K k)) :
    Set (BondAtLevel L m K j) :=
  liftSupport j C
abbrev orderLift (j : ℕ) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel L m K j → Matrices.ComplexMatrix2 :=
  liftToFinerLevel j V
def bareLiftFromLevel :
    {k : ℕ} → (BondAtLevel L m K k → Matrices.ComplexMatrix2) →
      BondAtLevel L m K 0 → Matrices.ComplexMatrix2
  | 0, V => V
  | _ + 1, V => bareLift V
end PeriodicLattice
end YangMills.Construction
