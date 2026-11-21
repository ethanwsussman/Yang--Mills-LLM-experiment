import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
structure SecondDifference (L m K : ℕ) where
  base : SiteAtLevel L m K 0
  firstDir : Fin 4
  secondDir : Fin 4
namespace SecondDifference
def leadingBond (d : SecondDifference L m K) : BondAtLevel L m K 0 :=
  Bond.forwardFrom d.base d.secondDir
def shiftedBond (d : SecondDifference L m K) : BondAtLevel L m K 0 :=
  Bond.forwardFrom (d.base + unitStep L m (levelDepth K 0) d.firstDir) d.secondDir
end SecondDifference
inductive CorneredObject (L m K : ℕ) where
  | ofSite (x : SiteAtLevel L m K 0)
  | ofBond (b : BondAtLevel L m K 0)
  | ofPlaquette (p : PlaquetteAtLevel L m K 0)
  | ofDifference (d : SecondDifference L m K)
  | ofFinset (s : Finset (SiteAtLevel L m K 0)) (hs : s.Nonempty)
namespace CorneredObject
def cornerSet : CorneredObject L m K → Set (SiteAtLevel L m K 0)
  | ofSite x => {x}
  | ofBond b => {b.source, b.target}
  | ofPlaquette p => p.vertices
  | ofDifference d =>
      {d.leadingBond.source, d.leadingBond.target, d.shiftedBond.source, d.shiftedBond.target}
  | ofFinset s _ => ↑s
def LiesIn (X : Set (FourTorus L m)) (e : CorneredObject L m K) : Prop :=
  ∀ c ∈ e.cornerSet, (c : FourTorus L m) ∈ X
def cornersWithin (e : CorneredObject L m K) (Ω : Set (FourTorus L m)) :
    Set (SiteAtLevel L m K 0) :=
  {c | c ∈ e.cornerSet ∧ (c : FourTorus L m) ∈ Ω}
def localLevel (k : ℕ) (Ω : ℕ → Set (FourTorus L m)) (e : CorneredObject L m K) : ℕ :=
  sSup {j | j ≤ k ∧ (e.cornersWithin (Ω j)).Nonempty}
def localMesh (k : ℕ) (Ω : ℕ → Set (FourTorus L m)) (e : CorneredObject L m K) : ℝ :=
  (L : ℝ) ^ e.localLevel k Ω * finestMeshInLevelUnits L k
end CorneredObject
def IsFullBondIn (X : Set (FourTorus L m)) (b : BondAtLevel L m K 0) : Prop :=
  (CorneredObject.ofBond b).LiesIn X ∧
    ∀ p : PlaquetteAtLevel L m K 0, (b ∈ p.boundaryBonds ∨ b.opposite ∈ p.boundaryBonds) →
      (CorneredObject.ofPlaquette p).LiesIn X
end YangMills.Construction.PeriodicLattice
