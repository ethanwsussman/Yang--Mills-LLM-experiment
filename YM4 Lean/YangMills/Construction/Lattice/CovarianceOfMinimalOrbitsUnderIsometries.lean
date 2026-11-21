import YangMills.Construction.Lattice.ActionsOnFamiliesLabelsHistoriesAndOperators
import YangMills.Construction.Lattice.CovarianceOfTheAveragingMaps
import YangMills.Construction.Lattice.LocalisedBackgroundsOfSetsInForce
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def IsTowerFromIndex (K k n : ℕ) (i : ℤ) (X : Set (FourTorus L m)) : Prop :=
  i ≤ scaledCubeIndex K k n ∧ ∃ c : ℤ, i ≤ c ∧ c ≤ scaledCubeIndex K 0 n ∧ IsPartitionRegion c X
def ActiveMinimalOrbitTransports (σ : FourTorus L m ≃ FourTorus L m) (ε : ℝ) (K k : ℕ)
    (Ω Ω' : ℕ → Set (FourTorus L m))
    (V V' : ∀ q : ℕ, BondAtLevel L m K q → Matrices.ComplexMatrix2)
    (U U' : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  (HasMinimalOrbit ε K k Ω' V' ↔ HasMinimalOrbit ε K k Ω V) ∧
    (HasMinimalOrbit ε K k Ω V →
      endpointFixingOrbit Ω' (activeBondSet K k Ω') U' =
        transportGaugeField σ '' endpointFixingOrbit Ω (activeBondSet K k Ω) U)
def CriticalOrbitTransports (σ : FourTorus L m ≃ FourTorus L m) (ε : ℝ) (K k : ℕ)
    (Ω Ω' : ℕ → Set (FourTorus L m))
    (V V' : ∀ q : ℕ, BondAtLevel L m K q → Matrices.ComplexMatrix2)
    (U U' : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  (CriticalFieldsFormOneOrbit (Averaging.smoothingRadius L) ε K k Ω' V' ↔
      CriticalFieldsFormOneOrbit (Averaging.smoothingRadius L) ε K k Ω V) ∧
    (CriticalFieldsFormOneOrbit (Averaging.smoothingRadius L) ε K k Ω V →
      residualGaugeOrbit K k Ω' U' = transportGaugeField σ '' residualGaugeOrbit K k Ω U)
def ConstraintSetsTransport (σ : FourTorus L m ≃ FourTorus L m) (ε : ℝ) (K k : ℕ)
    (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ q : ℕ, BondAtLevel L m K q → Matrices.ComplexMatrix2) : Prop :=
  (IsCompleteSequence K k (imageChain σ Ω) ↔ IsCompleteSequence K k Ω) ∧
    activeConstraintSet K k (imageChain σ Ω) (datumImage σ V) =
      transportGaugeField σ '' activeConstraintSet K k Ω V ∧
    endpointFixingGaugeGroup (imageChain σ Ω) (activeBondSet K k (imageChain σ Ω)) =
      transportSiteFunction σ '' endpointFixingGaugeGroup Ω (activeBondSet K k Ω) ∧
    activeRegularCriticalSet ε K k (imageChain σ Ω) (datumImage σ V) =
      transportGaugeField σ '' activeRegularCriticalSet ε K k Ω V
def FieldTransports (σ : FourTorus L m ≃ FourTorus L m) (ε : ℝ) (K k : ℕ)
    (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ q : ℕ, BondAtLevel L m K q → Matrices.ComplexMatrix2)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  (IsRegularField ε K k (imageChain σ Ω) (transportGaugeField σ U) ↔
      IsRegularField ε K k Ω U) ∧
    (IsActiveCritical K k (imageChain σ Ω) (datumImage σ V) (transportGaugeField σ U) ↔
      IsActiveCritical K k Ω V U) ∧
    ∀ e : BondAtLevel L m K 0, HasCurrentAt K (imageChain σ Ω 0) e →
      yangMillsCurrent (finestMeshInLevelUnits L k) (transportGaugeField σ U) e =
        twistedTransportForm σ U (yangMillsCurrent (finestMeshInLevelUnits L k) U) e
def IsometryCovarianceOfMinimalOrbits : Prop :=
  ∀ (L m K : ℕ) (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) (ε : ℝ),
    Conventions.IsAdmissibleBlockingFactor L → 0 < m → -(m : ℤ) ≤ i →
    σ ∈ latticeIsometries L m i → 0 < ε →
    (∀ (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
        (V : ∀ q : ℕ, BondAtLevel L m K q → Matrices.ComplexMatrix2),
      IsDeterminingChainFrom K k i Ω → IsActiveLinkDatum K k Ω V →
        ConstraintSetsTransport σ ε K k Ω V ∧
        (∀ U ∈ gaugeFieldsInside K (Ω 0), FieldTransports σ ε K k Ω V U) ∧
        ActiveMinimalOrbitTransports σ ε K k Ω (imageChain σ Ω) V (datumImage σ V)
          (activeMinimalField ε K k Ω V)
          (activeMinimalField ε K k (imageChain σ Ω) (datumImage σ V))) ∧
    (∀ (k : ℕ) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2),
      k ≤ K → i ≤ levelDepth K k → IsGaugeField compactGaugeGroup univ V →
        CriticalOrbitTransports σ ε K k (fun _ => univ) (fun _ => univ) (datumOnLevel K k V)
          (datumOnLevel K k (transportGaugeField σ V))
          (backgroundField (Averaging.smoothingRadius L) ε K k V)
          (backgroundField (Averaging.smoothingRadius L) ε K k (transportGaugeField σ V))) ∧
    (∀ (k m' : ℕ) (c : ℕ → ℕ) (S S' : ScaleLabel L m K m' c k)
        (V : ∀ q : ℕ, BondAtLevel L m K q → Matrices.ComplexMatrix2),
      IsScaleLabelImage σ S S' → IsDeterminingChainFrom K k i (domainChain S.domainSeq) →
        (IsDeterminingDatum K k (domainChain S.domainSeq) V →
          CriticalOrbitTransports σ ε K k (domainChain S.domainSeq) (domainChain S'.domainSeq) V
            (datumImage σ V) (domainBackground (Averaging.smoothingRadius L) ε K k S.domainSeq V)
            (domainBackground (Averaging.smoothingRadius L) ε K k S'.domainSeq (datumImage σ V))) ∧
        (IsActiveLinkDatum K k (domainChain S.domainSeq) V →
          ActiveMinimalOrbitTransports σ ε K k (domainChain S.domainSeq)
            (domainChain S'.domainSeq) V (datumImage σ V)
            (activeMinimalField ε K k (domainChain S.domainSeq) V)
            (activeMinimalField ε K k (domainChain S'.domainSeq) (datumImage σ V)))) ∧
    (∀ (k n : ℕ) (X : Set (FourTorus L m)) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2),
      IsTowerFromIndex K k n i X → IsGaugeField compactGaugeGroup univ V →
        (IsMinimalDeterminingSetHyp K k n X →
          CriticalOrbitTransports σ ε K k (shrinkingTower K n 0 X) (shrinkingTower K n 0 (σ '' X))
            (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X (bareLift V))
            (averagingOnDeterminingSet (Averaging.smoothingRadius L) K (σ '' X)
              (bareLift (transportGaugeField σ V)))
            (localizedBackground (Averaging.smoothingRadius L) ε K k n X V)
            (localizedBackground (Averaging.smoothingRadius L) ε K k n (σ '' X)
              (transportGaugeField σ V))) ∧
        (IsLocalizedBackgroundHyp K k n X univ V →
          IsLocalizedBackgroundHyp K k n (σ '' X) univ (transportGaugeField σ V) ∧
          ActiveMinimalOrbitTransports σ ε K k (shrinkingTower K n 0 X)
            (shrinkingTower K n 0 (σ '' X))
            (inducedActiveDatum V) (inducedActiveDatum (transportGaugeField σ V))
            (chosenLocalizedBackground ε K k n X univ V)
            (chosenLocalizedBackground ε K k n (σ '' X) univ (transportGaugeField σ V)))) ∧
    (∀ (k n p : ℕ) (Ω : ℕ → Set (FourTorus L m)) (W : Set (FourTorus L m))
        (V : ∀ q : ℕ, BondAtLevel L m K q → Matrices.ComplexMatrix2),
      IsDeterminingChainFrom K k i Ω → i ≤ scaledCubeIndex K p n →
        IsGluedHyp K k n p Ω W V →
        (HasGluedCriticalOrbit ε K k n p (imageChain σ Ω) (σ '' W) (datumImage σ V) ↔
          HasGluedCriticalOrbit ε K k n p Ω W V) ∧
        (HasGluedCriticalOrbit ε K k n p Ω W V →
          endpointFixingOrbit (gluedChain K n p (imageChain σ Ω) (σ '' W))
              (gluedActiveSet K k n p (imageChain σ Ω) (σ '' W))
              (gluedCriticalConfiguration ε K k n p (imageChain σ Ω) (σ '' W)
                (datumImage σ V)) =
            transportGaugeField σ '' endpointFixingOrbit (gluedChain K n p Ω W)
              (gluedActiveSet K k n p Ω W) (gluedCriticalConfiguration ε K k n p Ω W V)))
end YangMills.Construction.PeriodicLattice
end
