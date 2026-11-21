import YangMills.Construction.Lattice.ConnectedDeterminingSets
import YangMills.Construction.Lattice.MinimalOrbitsOfSetsInForce
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def IsLiftableField (K k : ℕ) (B : Set (BondAtLevel L m K k))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) : Prop :=
  1 ≤ k ∧ k ≤ K ∧ IsReversalClosed B ∧ IsGaugeField compactGaugeGroup B V
def InducedDatumDefined {K k : ℕ} (Ω : ℕ → Set (FourTorus L m))
    (B : Set (BondAtLevel L m K k)) : Prop :=
  IsActiveSetSetting K k Ω ∧ IsCompleteSequence K k Ω ∧
    ∀ q ∈ activeBondSet K k Ω, bareBondsInBlockPair q.2 ⊆ liftSupport 0 B
def inducedActiveDatum {K k : ℕ} (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) (j : ℕ) :
    BondAtLevel L m K j → Matrices.ComplexMatrix2 :=
  activeAveragingMap (bareLift V) j
def IsMinimalDeterminingSetHyp (K k n : ℕ) (X : Set (FourTorus L m)) : Prop :=
  1 ≤ k ∧ k ≤ K ∧ IsRegionAtLevel K n 0 X ∧ ∀ j, 1 ≤ j → j ≤ k → n + j ≤ m + K
def minimalDeterminingSet (K k n : ℕ) (X : Set (FourTorus L m)) :
    Set (Σ q : ℕ, BondAtLevel L m K q) :=
  activeBondSet K k (shrinkingTower K n 0 X)
def IsLocalizedBackgroundHyp (K k n : ℕ) (X : Set (FourTorus L m))
    (B : Set (BondAtLevel L m K k)) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) : Prop :=
  IsLiftableField K k B V ∧ IsMinimalDeterminingSetHyp K k n X ∧
    InducedDatumDefined (shrinkingTower K n 0 X) B
def IsLocalizedBackground (ε : ℝ) (K k n : ℕ) (X : Set (FourTorus L m))
    (B : Set (BondAtLevel L m K k)) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  IsLocalizedBackgroundHyp K k n X B V ∧
    IsActiveMinimalField ε K k (shrinkingTower K n 0 X) (inducedActiveDatum V) U
def chosenLocalizedBackground (ε : ℝ) (K k n : ℕ) (X : Set (FourTorus L m))
    (B : Set (BondAtLevel L m K k)) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  Classical.epsilon (IsLocalizedBackground ε K k n X B V)
def IsGluedHyp (K k n j : ℕ) (Ω : ℕ → Set (FourTorus L m)) (W : Set (FourTorus L m))
    (V : ∀ i : ℕ, BondAtLevel L m K i → Matrices.ComplexMatrix2) : Prop :=
  1 ≤ k ∧ IsGluableRegion K k n j Ω W ∧ IsActiveLinkDatum K k Ω V
end PeriodicLattice
end YangMills.Construction
