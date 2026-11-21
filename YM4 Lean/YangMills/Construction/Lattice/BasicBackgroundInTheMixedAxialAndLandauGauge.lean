import YangMills.Construction.Lattice.BondSetsOfSequences
import YangMills.Construction.Lattice.LandauGaugeRelativeToABackground
import YangMills.Construction.Lattice.LocalisedBackgroundsOfSetsInForce
import YangMills.Construction.Lattice.TowerAxialGaugeOutsideNodesInAFrame
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def boxAverageLog (K k n : ℕ) (Λ : Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    ActiveFamily L m K k (shrinkingTower K n 0 Λ) :=
  fun q => Matrices.ComplexMatrix2.unitaryLieLog
    (activeAveragingMap (extendByOne (bondsInside Λ) U) q.1.1 q.1.2)
def BoxAverageLogDefined (K k n : ℕ) (Λ : Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  ∀ q : PositiveBondIn (activeBondSet K k (shrinkingTower K n 0 Λ)),
    activeAveragingMap (extendByOne (bondsInside Λ) U) q.1.1 q.1.2 ∈
      Matrices.ComplexMatrix2.unitaryLogDomain
def framedBoxLandauPotential (ε α : ℝ) (r : SignedFrame) (K k n : ℕ) (Λ : Set (FourTorus L m))
    (B : ActiveFamily L m K k (shrinkingTower K n 0 Λ)) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  landauGaugeForm (Averaging.smoothingRadius L) (finestMeshInLevelUnits L k) α k
    (shrinkingTower K n 0 Λ)
    (framedAxialRepresentativeAtOne ε r K k (shrinkingTower K n 0 Λ)
      (activeBondSet K k (shrinkingTower K n 0 Λ)) (trivialBondData K))
    (framedAxialRepresentativeAtOne ε r K k (shrinkingTower K n 0 Λ)
      (activeBondSet K k (shrinkingTower K n 0 Λ)) (expTwistedDatum B (trivialBondData K)))
def FramedBoxLandauPotentialDefined (ε α : ℝ) (r : SignedFrame) (K k n : ℕ)
    (Λ : Set (FourTorus L m)) (B : ActiveFamily L m K k (shrinkingTower K n 0 Λ)) : Prop :=
  IsRealFamily B ∧
    HasFramedAxialRepresentative ε r K k (shrinkingTower K n 0 Λ)
      (activeBondSet K k (shrinkingTower K n 0 Λ)) (trivialBondData K) trivialGaugeField ∧
    HasFramedAxialRepresentative ε r K k (shrinkingTower K n 0 Λ)
      (activeBondSet K k (shrinkingTower K n 0 Λ)) (expTwistedDatum B (trivialBondData K))
      trivialGaugeField ∧
    ExistsUniqueSmallFieldLandauPair (Averaging.smoothingRadius L) (finestMeshInLevelUnits L k) α k
      (shrinkingTower K n 0 Λ)
      (framedAxialRepresentativeAtOne ε r K k (shrinkingTower K n 0 Λ)
        (activeBondSet K k (shrinkingTower K n 0 Λ)) (trivialBondData K))
      (framedAxialRepresentativeAtOne ε r K k (shrinkingTower K n 0 Λ)
        (activeBondSet K k (shrinkingTower K n 0 Λ)) (expTwistedDatum B (trivialBondData K)))
structure IsMixedAxialLandauBackground (ε α : ℝ) (r : SignedFrame) (K k n : ℕ)
    (X Λ : Set (FourTorus L m)) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop where
  localized : IsLocalizedBackground ε K k n X univ V U
  average_eq : ∀ b : BondAtLevel L m K k, b.LiesIn (sitesIn Λ) → activeAveragingMap U k b = V b
  boxAxialGauge : ∀ b ∈ rotatedAxialBoxTree r (levelDepth K k) (sitesIn Λ), b.LiesIn (sitesIn Λ) →
    activeAveragingMap U k b = 1
  blockAxialGauge : ∀ q < k, IsBlockAxialGauge K q (sitesIn Λ) (activeAveragingMap U q)
  log_defined : BoxAverageLogDefined K k n Λ U
  potential_defined :
    FramedBoxLandauPotentialDefined ε α r K k n Λ (boxAverageLog K k n Λ U)
  landauGauge : ∃ u : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2,
    IsGaugeTransformSupportedIn X u ∧
    ∀ b ∈ (bondsInside Λ : Set (BondAtLevel L m K 0)), gaugeTransform u U b =
      expGaugeField (meshScaledForm (finestMeshInLevelUnits L k)
        (framedBoxLandauPotential ε α r K k n Λ (boxAverageLog K k n Λ U))) b
end YangMills.Construction.PeriodicLattice
