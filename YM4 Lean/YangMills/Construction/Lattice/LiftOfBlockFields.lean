import YangMills.Construction.Lattice.BlockAveraging
import YangMills.Construction.Lattice.LevelCubesAndBlocks
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
variable {L m K k : ℕ}
def EndsInOneBlock (k : ℕ) {i : ℕ} (b : BondAtLevel L m K i) : Prop :=
  ∃ y : SiteAtLevel L m K k,
    (b.source : FourTorus L m) ∈ blockAtLevel i y ∧ (b.target : FourTorus L m) ∈ blockAtLevel i y
def CoversBond {i : ℕ} (c : BondAtLevel L m K k) (b : BondAtLevel L m K i) : Prop :=
  (b.source : FourTorus L m) ∈ blockAtLevel i c.source ∧
    (b.target : FourTorus L m) ∈ blockAtLevel i c.target
def coveredBond (k : ℕ) {i : ℕ} (b : BondAtLevel L m K i) : BondAtLevel L m K k :=
  Classical.epsilon fun c => CoversBond c b
def liftToFinerLevel (i : ℕ) (V : BondAtLevel L m K k → ComplexMatrix2) (b : BondAtLevel L m K i) :
    ComplexMatrix2 :=
  open Classical in
  if EndsInOneBlock k b then 1 else V (coveredBond k b)
def bareLift (V : BondAtLevel L m K k → ComplexMatrix2) : BondAtLevel L m K 0 → ComplexMatrix2 :=
  liftToFinerLevel 0 V
def coveringBonds (i : ℕ) (ℬ : Set (BondAtLevel L m K k)) : Set (BondAtLevel L m K i) :=
  {b | ∃ c ∈ ℬ, CoversBond c b}
def liftSupport (i : ℕ) (ℬ : Set (BondAtLevel L m K k)) : Set (BondAtLevel L m K i) :=
  {b | EndsInOneBlock k b} ∪ coveringBonds i ℬ
def averagedLift (ω : ℝ) (j : ℕ) (V : BondAtLevel L m K k → ComplexMatrix2) :
    BondAtLevel L m K j → ComplexMatrix2 :=
  blockFieldAtLevel ω j (bareLift V)
def familyMemberLift (ω : ℝ) (i j : ℕ) (W : ∀ n, BondAtLevel L m K n → ComplexMatrix2) :
    BondAtLevel L m K i → ComplexMatrix2 :=
  averagedLift ω i (W j)
end YangMills.Construction.PeriodicLattice
