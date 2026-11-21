import YangMills.Construction.Lattice.BlockAxialGaugeOutsideTheNodes
import YangMills.Construction.Lattice.InwardBondsAndSetsInForce
import YangMills.Construction.Parameters.ConstructionParameters
import YangMills.Construction.Thresholds.DegreeFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace CubesOfStep
open Matrices
variable (c : ParameterChoice.ChoiceUpToDegreeConstants) {m : ℕ} (K : ℕ) (x : ℕ → ℝ)
def partitionIndexOfSize (L K k s : ℕ) : ℤ := scaledCubeIndex K k (Nat.log L s)
def blockSizeAt (j : ℕ) : ℕ := Thresholds.minBlockSize c.L c.r x j
def secondSize : ℕ := ParameterChoice.secondCubeSize c.L c.M₁
def coarseCubeSide (k : ℕ) : ℕ := c.L * c.M * blockSizeAt c x (k + 1)
def coarsePartitionIndex (k : ℕ) : ℤ := partitionIndexOfSize c.L K k (coarseCubeSide c x k)
def testPartitionIndex (k : ℕ) : ℤ :=
  partitionIndexOfSize c.L K k (c.L ^ 2 * secondSize c * blockSizeAt c x (k + 1))
def testCollarIndex (k : ℕ) : ℤ :=
  partitionIndexOfSize c.L K k (c.L * secondSize c * blockSizeAt c x (k + 1))
def densityPartitionIndex (k : ℕ) : ℤ :=
  partitionIndexOfSize c.L K k (c.L * secondSize c * blockSizeAt c x k)
def densityCollarIndex (k : ℕ) : ℤ :=
  partitionIndexOfSize c.L K k (secondSize c * blockSizeAt c x k)
def coarsePartition (k : ℕ) : Set (Set (FourTorus c.L m)) :=
  standardCubePartition c.L m (coarsePartitionIndex c K x k)
def testPartition (k : ℕ) : Set (Set (FourTorus c.L m)) :=
  standardCubePartition c.L m (testPartitionIndex c K x k)
def densityPartition (k : ℕ) : Set (Set (FourTorus c.L m)) :=
  standardCubePartition c.L m (densityPartitionIndex c K x k)
def coarseCollar (k : ℕ) (X : Set (FourTorus c.L m)) (a : ℤ) : Set (FourTorus c.L m) :=
  layerEnlargement (coarsePartitionIndex c K x k) X a
def coarseCubeHull (k : ℕ) (Y : Set (FourTorus c.L m)) : Set (FourTorus c.L m) :=
  cubeHull (coarsePartitionIndex c K x k) Y
def testCollar (k : ℕ) (Q : Set (FourTorus c.L m)) (a : ℤ) : Set (FourTorus c.L m) :=
  layerEnlargement (testCollarIndex c K x k) Q a
def densityCollar (k : ℕ) (Q : Set (FourTorus c.L m)) (a : ℤ) : Set (FourTorus c.L m) :=
  layerEnlargement (densityCollarIndex c K x k) Q a
def determiningTower (X : Set (FourTorus c.L m)) : ℕ → Set (FourTorus c.L m) :=
  shrinkingTower K (Nat.log c.L c.M₁) 0 X
def minimalDeterminingSet (j : ℕ) (X : Set (FourTorus c.L m)) :
    Set (Σ q : ℕ, BondAtLevel c.L m K q) :=
  activeBondSet K j (determiningTower c K X)
def liftedFamily {k : ℕ} (X : Set (FourTorus c.L m)) (V : BondAtLevel c.L m K k → ComplexMatrix2) :
    ∀ j : ℕ, BondAtLevel c.L m K j → ComplexMatrix2 :=
  averagingOnDeterminingSet (Averaging.smoothingRadius c.L) K X (bareLift V)
def LocalBackgroundExists {j : ℕ} (X : Set (FourTorus c.L m))
    (V : BondAtLevel c.L m K j → ComplexMatrix2) : Prop :=
  HasUniqueCriticalOrbit (Averaging.smoothingRadius c.L) c.εv K j (determiningTower c K X)
    (minimalDeterminingSet c K j X) (liftedFamily c K X V)
def localCriticalSet {j : ℕ} (X : Set (FourTorus c.L m))
    (V : BondAtLevel c.L m K j → ComplexMatrix2) : Set (BondAtLevel c.L m K 0 → ComplexMatrix2) :=
  regularConstrainedCriticalSet (Averaging.smoothingRadius c.L) c.εv K j (determiningTower c K X)
    (minimalDeterminingSet c K j X) (liftedFamily c K X V)
def localBackground {j : ℕ} (X : Set (FourTorus c.L m))
    (V : BondAtLevel c.L m K j → ComplexMatrix2) : BondAtLevel c.L m K 0 → ComplexMatrix2 :=
  Classical.epsilon fun U => U ∈ localCriticalSet c K X V
def axialGaugeSites (k : ℕ) (Q : Set (FourTorus c.L m)) : Set (SiteAtLevel c.L m K (k + 1)) :=
  sitesIn (testCollar c K x k Q 3)
def testCubeCriticalSet (k : ℕ) (Q : Set (FourTorus c.L m))
    (V : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) :
    Set (BondAtLevel c.L m K 0 → ComplexMatrix2) :=
  localCriticalSet c K (testCollar c K x k Q 4) V
def testCubeAverage (k : ℕ) (Q : Set (FourTorus c.L m)) (U : BondAtLevel c.L m K 0 → ComplexMatrix2) :
    BondAtLevel c.L m K k → ComplexMatrix2 :=
  averagingOnDeterminingSet (Averaging.smoothingRadius c.L) K (testCollar c K x k Q 4) U k
def AxialBackgroundDefined (k : ℕ) (Q : Set (FourTorus c.L m))
    (V : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) : Prop :=
  LocalBackgroundExists c K (testCollar c K x k Q 4) V ∧
    (∀ y ∈ axialGaugeSites c K x k Q, ∀ z ∈ sitesInBlock (levelDepth K k) y,
      (∀ y' ∈ axialGaugeSites c K x k Q, (y' : FourTorus c.L m) ≠ z) →
        ¬IsEndpointOf (minimalDeterminingSet c K (k + 1) (testCollar c K x k Q 4))
          (z : FourTorus c.L m)) ∧
    ∀ U ∈ testCubeCriticalSet c K x k Q V, ∀ y ∈ axialGaugeSites c K x k Q,
      ∀ z ∈ sitesInBlock (levelDepth K k) y, HasContourMean (testCubeAverage c K x k Q U) y z
def IsAxialGaugeRepresentative (k : ℕ) (Q : Set (FourTorus c.L m))
    (V : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) (U : BondAtLevel c.L m K 0 → ComplexMatrix2) :
    Prop :=
  U ∈ testCubeCriticalSet c K x k Q V ∧
    IsBlockAxialGauge K k (axialGaugeSites c K x k Q) (testCubeAverage c K x k Q U)
def axialGaugeBackground (k : ℕ) (Q : Set (FourTorus c.L m))
    (V : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) : BondAtLevel c.L m K k → ComplexMatrix2 :=
  testCubeAverage c K x k Q (Classical.epsilon (IsAxialGaugeRepresentative c K x k Q V))
def PlaquettesNearIdentity (U : BondAtLevel c.L m K 0 → ComplexMatrix2) (X : Set (FourTorus c.L m))
    (a : ℝ) : Prop :=
  ∀ p ∈ (plaquettesInside X : Set (PlaquetteAtLevel c.L m K 0)),
    ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) < a
def plaquetteBound (j : ℕ) : ℝ :=
  Thresholds.epsThreshold c.A₀ c.𝔭₀ x j * finestMeshInLevelUnits c.L j ^ 2
def plaquetteIndicator (k : ℕ) (V : BondAtLevel c.L m K (k + 1) → ComplexMatrix2)
    (Q : Set (FourTorus c.L m)) : ℝ :=
  open Classical in
  if LocalBackgroundExists c K (testCollar c K x k Q 4) V ∧
      PlaquettesNearIdentity c K (localBackground c K (testCollar c K x k Q 4) V)
        (testCollar c K x k Q 1) (plaquetteBound c x (k + 1))
  then 1 else 0
def fluctuationIndicator (k : ℕ) (Vk : BondAtLevel c.L m K k → ComplexMatrix2)
    (Vt : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) (Q : Set (FourTorus c.L m)) : ℝ :=
  open Classical in
  if AxialBackgroundDefined c K x k Q Vt ∧
      ∀ b ∈ nonPivotBonds K k (testCollar c K x k Q 2),
        ComplexMatrix2.operatorNorm (Vk b * (axialGaugeBackground c K x k Q Vt b)⁻¹ - 1) <
          2 * Thresholds.deltaThreshold c.A₀ c.A₁ c.𝔭₀ x k
  then 1 else 0
def densityTestField : ∀ k : ℕ, (BondAtLevel c.L m K k → ComplexMatrix2) → Set (FourTorus c.L m) →
    BondAtLevel c.L m K 0 → ComplexMatrix2
  | 0, V, _ => V
  | k + 1, V, Q => localBackground c K (densityCollar c K x (k + 1) Q 4) V
def DensityTestFieldDefined :
    ∀ k : ℕ, (BondAtLevel c.L m K k → ComplexMatrix2) → Set (FourTorus c.L m) → Prop
  | 0, _, _ => True
  | k + 1, V, Q => LocalBackgroundExists c K (densityCollar c K x (k + 1) Q 4) V
def densityCubeIndicator (k : ℕ) (V : BondAtLevel c.L m K k → ComplexMatrix2)
    (Q : Set (FourTorus c.L m)) : ℝ :=
  open Classical in
  if DensityTestFieldDefined c K x k V Q ∧
      PlaquettesNearIdentity c K (densityTestField c K x k V Q) (densityCollar c K x k Q 1)
        (plaquetteBound c x k)
  then 1 else 0
def densityIndicator (k : ℕ) (V : BondAtLevel c.L m K k → ComplexMatrix2)
    (Y : Set (FourTorus c.L m)) : ℝ :=
  ∏ᶠ Q ∈ partitionCubesIn (densityPartitionIndex c K x k) Y, densityCubeIndicator c K x k V Q
def densityIndicatorCompl (k : ℕ) (V : BondAtLevel c.L m K k → ComplexMatrix2)
    (Y : Set (FourTorus c.L m)) : ℝ :=
  1 - densityIndicator c K x k V Y
end CubesOfStep
end PeriodicLattice
end YangMills.Construction
