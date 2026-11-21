import YangMills.Construction.Lattice.BackgroundAndRecursionOfAStep
import YangMills.Construction.Lattice.ConnectedDeterminingSets
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.ParameterChoice
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def collarLayerOfBond {K i : ℕ} (k n : ℕ) (Ω : ℕ → Set (FourTorus L m)) (S : Finset ℕ)
    (A : ℕ → Set (FourTorus L m)) (e : BondAtLevel L m K i) : ℕ :=
  Classical.epsilon fun l => l ∈ S ∧ ∃ C, IsCollarComponentInShell K k n Ω S A C l ∧
    ((e.source : FourTorus L m) ∈ C ∨ (e.target : FourTorus L m) ∈ C)
def multiShellGluedData (K k n : ℕ) (Ω : ℕ → Set (FourTorus L m)) (S : Finset ℕ)
    (A : ℕ → Set (FourTorus L m)) (V : ∀ i : ℕ, BondAtLevel L m K i → Matrices.ComplexMatrix2)
    (i : ℕ) : BondAtLevel L m K i → Matrices.ComplexMatrix2 :=
  open Classical in
  fun e => if e ∈ activeBondsAt K k Ω i then V i e
    else familyMemberLift (Averaging.smoothingRadius L) i (collarLayerOfBond k n Ω S A e) V e
namespace CubesOfStep
variable (c : ChoiceUpToDegreeConstants) {m : ℕ} {K : ℕ} (x : ℕ → ℝ)
def stripLogSize : ℕ := Nat.log c.L c.M₁
def stripPieces {k : ℕ} (S : LabelAtLevel c m K x (k + 2)) (l : ℕ) : Set (FourTorus c.L m) :=
  open Classical in
  if l = k + 2 then S.largeField ⟨k + 2, by simp⟩ else (S.atScale ⟨k + 1, by simp⟩).smallFieldRegion
def stripLocalRegion : ∀ {k : ℕ}, LabelAtLevel c m K x (k + 1) → Set (FourTorus c.L m)
  | 0, S => S.largeField ⟨1, by simp⟩
  | k + 1, S => partsMeet K (stripLogSize c) {k + 1, k + 2} (stripPieces c x S)
def stripGluedChain : ∀ {k : ℕ}, LabelAtLevel c m K x (k + 1) → ℕ → Set (FourTorus c.L m)
  | 0, S => gluedChain K (stripLogSize c) 1 S.domainSeq (stripLocalRegion c x S)
  | k + 1, S => multiShellGluedChain K (k + 2) (stripLogSize c) S.domainSeq {k + 1, k + 2}
      (stripPieces c x S)
def stripGluedActiveSet : ∀ {k : ℕ}, LabelAtLevel c m K x (k + 1) →
    Set (Σ q : ℕ, BondAtLevel c.L m K q)
  | 0, S => gluedActiveSet K 1 (stripLogSize c) 1 S.domainSeq (stripLocalRegion c x S)
  | k + 1, S => multiShellGluedActiveSet K (k + 2) (stripLogSize c) S.domainSeq {k + 1, k + 2}
      (stripPieces c x S)
def stripFieldFamily {k : ℕ} (D : StepData c.L m K k) :
    ∀ j : ℕ, BondAtLevel c.L m K j → Matrices.ComplexMatrix2 :=
  Function.update (fieldDatum c D D.current) (k + 1) D.next
def stripGluedData : ∀ {k : ℕ}, LabelAtLevel c m K x (k + 1) → StepData c.L m K k →
    ∀ j : ℕ, BondAtLevel c.L m K j → Matrices.ComplexMatrix2
  | 0, S, D => gluedBoundaryData K 1 1 S.domainSeq (stripFieldFamily c D)
  | k + 1, S, D => multiShellGluedData K (k + 2) (stripLogSize c) S.domainSeq {k + 1, k + 2}
      (stripPieces c x S) (stripFieldFamily c D)
variable {k : ℕ} (S : LabelAtLevel c m K x (k + 1)) (D : StepData c.L m K k)
def stripMarked : Set (FourTorus c.L m) := (S.atScale ⟨k + 1, by simp⟩).markedSet
def stripInteriorBonds : Set (BondAtLevel c.L m K k) := nonPivotBonds K k (stripMarked c x S)
def stripBlockSites : Set (SiteAtLevel c.L m K (k + 1)) :=
  {y | y ∈ (sitesIn (stripLocalRegion c x S) : Set (SiteAtLevel c.L m K (k + 1))) ∧
    ∃ e ∈ stripInteriorBonds c x S,
      e.source ∈ sitesInBlock (levelDepth K k) y ∨ e.target ∈ sitesInBlock (levelDepth K k) y}
def stripCriticalConfigs : Set (BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2) :=
  regularConstrainedCriticalSet (Averaging.smoothingRadius c.L) c.εv K (k + 1)
    (stripGluedChain c x S) (stripGluedActiveSet c x S) (stripGluedData c x S D)
def stripAveraged (U : BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2) :
    BondAtLevel c.L m K k → Matrices.ComplexMatrix2 :=
  averagingOnDeterminingSet (Averaging.smoothingRadius c.L) K (stripLocalRegion c x S) U k
def LocalStripBackgroundExists : Prop :=
  HasUniqueCriticalOrbit (Averaging.smoothingRadius c.L) c.εv K (k + 1) (stripGluedChain c x S)
      (stripGluedActiveSet c x S) (stripGluedData c x S D) ∧
    (∀ y ∈ stripBlockSites c x S, ∀ z ∈ sitesInBlock (levelDepth K k) y,
      (∀ y' ∈ stripBlockSites c x S, (y' : FourTorus c.L m) ≠ z) →
        ¬IsEndpointOf (stripGluedActiveSet c x S) (z : FourTorus c.L m)) ∧
    ∀ U ∈ stripCriticalConfigs c x S D, ∀ y ∈ stripBlockSites c x S,
      ∀ z ∈ sitesInBlock (levelDepth K k) y, HasContourMean (stripAveraged c x S U) y z
def IsLocalBackgroundRep (U : BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  U ∈ stripCriticalConfigs c x S D ∧
    IsBlockAxialGauge K k (stripBlockSites c x S) (stripAveraged c x S U)
def localStripBackground : BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2 :=
  Classical.epsilon (IsLocalBackgroundRep c x S D)
def localStripAveraged : BondAtLevel c.L m K k → Matrices.ComplexMatrix2 :=
  stripAveraged c x S (localStripBackground c x S D)
def backgroundShiftLog (e : BondAtLevel c.L m K k) : Matrices.ComplexMatrix2 :=
  Complex.I⁻¹ • Matrices.ComplexMatrix2.unitaryLog
    (backgroundField c D e * (localStripAveraged c x S D e)⁻¹)
def stripInitialRegion : Set (FourTorus c.L m) := stripGluedChain c x S 0
def stripExtraEndpoints : Set (SiteAtLevel c.L m K k) :=
  {z | (∃ y ∈ stripBlockSites c x S, z ∈ sitesInBlock (levelDepth K k) y) ∧
    (∀ y ∈ stripBlockSites c x S, (y : FourTorus c.L m) ≠ z) ∧
    IsEndpointOf (stripGluedActiveSet c x S) (z : FourTorus c.L m)}
def stripInitialAveraged (U : BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2) :
    BondAtLevel c.L m K k → Matrices.ComplexMatrix2 :=
  averagingOnDeterminingSet (Averaging.smoothingRadius c.L) K (stripInitialRegion c x S) U k
def IsLocalBackgroundRepOffEndpoints (U : BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2) :
    Prop :=
  U ∈ stripCriticalConfigs c x S D ∧ ∀ y ∈ stripBlockSites c x S,
    ∀ z ∈ sitesInBlock (levelDepth K k) y,
    z ∉ stripExtraEndpoints c x S → HasContourMean (stripInitialAveraged c x S U) y z ∧
      meanContourHolonomy (stripInitialAveraged c x S U) y z = 1
def localStripBackgroundOffEndpoints : BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2 :=
  Classical.epsilon (IsLocalBackgroundRepOffEndpoints c x S D)
def localStripAveragedOffEndpoints : BondAtLevel c.L m K k → Matrices.ComplexMatrix2 :=
  stripInitialAveraged c x S (localStripBackgroundOffEndpoints c x S D)
def backgroundShiftLogOffEndpoints (e : BondAtLevel c.L m K k) : Matrices.ComplexMatrix2 :=
  Complex.I⁻¹ • Matrices.ComplexMatrix2.unitaryLog
    (backgroundField c D e * (localStripAveragedOffEndpoints c x S D e)⁻¹)
end CubesOfStep
end YangMills.Construction.PeriodicLattice
