import YangMills.Construction.Lattice.ExclusiveAndInclusiveConventionsAndAdmittedSets
import YangMills.Construction.Lattice.SmallFieldDomainOfAStep
import YangMills.Construction.Lattice.SupDistancesOfCells
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace CubesOfStep
open Set YangMills.Construction.ParameterChoice YangMills.Construction.Matrices
open scoped ENNReal
structure StepData (L m K k : ℕ) where
  domains : ℕ → Set (FourTorus L m)
  region : Set (FourTorus L m)
  lowerFields : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2
  current : BondAtLevel L m K k → ComplexMatrix2
  next : BondAtLevel L m K (k + 1) → ComplexMatrix2
variable (c : ChoiceUpToDegreeConstants) {m : ℕ} (K : ℕ) (x : ℕ → ℝ)
variable {K} {k : ℕ} (D : StepData c.L m K k)
def touchingBonds : Set (BondAtLevel c.L m K k) := bondsMeeting D.region
def backgroundFibre : Set (BondAtLevel c.L m K k → ComplexMatrix2) :=
  {V | V ∈ gaugeFieldsAtLevel c.L m K k ∧ (∀ b ∉ touchingBonds c D, V b = D.current b) ∧
    (∀ e ∈ (bondsMeeting D.region : Set (BondAtLevel c.L m K (k + 1))),
      blockAverageStep (Averaging.smoothingRadius c.L) k V e = D.next e) ∧
    IsBlockAxialGauge K k (sitesIn D.region) V}
def fieldDatum (V : BondAtLevel c.L m K k → ComplexMatrix2) :
    ∀ j : ℕ, BondAtLevel c.L m K j → ComplexMatrix2 :=
  Function.update D.lowerFields k V
def regularFibre : Set (BondAtLevel c.L m K k → ComplexMatrix2) :=
  {V | V ∈ backgroundFibre c D ∧
    HasUniqueCriticalOrbit (Averaging.smoothingRadius c.L) c.εv K k D.domains
      (activeBondSet K k D.domains) (fieldDatum c D V)}
def backgroundOf (V : BondAtLevel c.L m K k → ComplexMatrix2) : BondAtLevel c.L m K 0 → ComplexMatrix2 :=
  minimalFieldOn c.εv K k D.domains (activeBondSet K k D.domains) (fieldDatum c D V)
def IsBackgroundMinimizer (V : BondAtLevel c.L m K k → ComplexMatrix2) : Prop :=
  V ∈ regularFibre c D ∧ ∀ V' ∈ regularFibre c D,
    wilsonAction (backgroundOf c D V) ≤ wilsonAction (backgroundOf c D V')
def HasUniqueBackgroundMinimizer : Prop := ∃! V, IsBackgroundMinimizer c D V
def backgroundField : BondAtLevel c.L m K k → ComplexMatrix2 :=
  open Classical in
  fun b => if b ∈ touchingBonds c D then Classical.epsilon (IsBackgroundMinimizer c D) b
    else D.current b
def freeVariableBonds : Set (BondAtLevel c.L m K k) := nonPivotBonds K k D.region
def FluctuationDefined (b : BondAtLevel c.L m K k) : Prop :=
  HasUniqueBackgroundMinimizer c D ∧ b ∈ touchingBonds c D ∧
    D.current b * (backgroundField c D b)⁻¹ ≠ -1
def fluctuation (b : BondAtLevel c.L m K k) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.unitaryLog (D.current b * (backgroundField c D b)⁻¹)
def shrunkDomain : Set (FourTorus c.L m) := coarseCollar c K x k D.region (-1)
def boundaryStrip : Set (FourTorus c.L m) :=
  regionDiff (coarsePartitionIndex c K x k) D.region (shrunkDomain c x D)
def shrunkDomainCubes : Set (Set (FourTorus c.L m)) :=
  partitionCubesIn (coarsePartitionIndex c K x k) (shrunkDomain c x D)
def freeBondsWithin (Y : Set (FourTorus c.L m)) : Set (BondAtLevel c.L m K k) :=
  freeVariableBonds c D ∩ PeriodicLattice.bondsInside Y
def freeBondsCrossing (Y : Set (FourTorus c.L m)) : Set (BondAtLevel c.L m K k) :=
  {b | b ∈ freeVariableBonds c D ∧
    Xor ((b.source : FourTorus c.L m) ∈ Y) ((b.target : FourTorus c.L m) ∈ Y)}
def freeBondsOutside (Y : Set (FourTorus c.L m)) : Set (BondAtLevel c.L m K k) :=
  freeVariableBonds c D \ freeBondsWithin c D Y
def distToFreeBondsWithin (b : BondAtLevel c.L m K k) (Y : Set (FourTorus c.L m)) : ℝ≥0∞ :=
  ⨅ b' ∈ freeBondsWithin c D Y, bondSupDist K k b b'
def bondCollar (Y : Set (FourTorus c.L m)) : Set (BondAtLevel c.L m K k) :=
  {b | b ∈ freeBondsOutside c D Y \ freeBondsCrossing c D Y ∧
    distToFreeBondsWithin c D b Y ≤ (c.ϖT : ℝ≥0∞)}
def FluctuationLt (b : BondAtLevel c.L m K k) (a : ℝ) : Prop :=
  FluctuationDefined c D b ∧ ComplexMatrix2.operatorNorm (fluctuation c D b) < a
def bondIndicator (b : BondAtLevel c.L m K k) : ℝ :=
  open Classical in
  if FluctuationLt c D b (Thresholds.deltaThreshold c.A₀ c.A₁ c.𝔭₀ x k) then 1 else 0
def narrowBondIndicator (b : BondAtLevel c.L m K k) : ℝ :=
  open Classical in
  if FluctuationLt c D b (Thresholds.deltaFlatThreshold c.A₀ c.A₁ c.Θ₁ c.𝔭₀ x k) then 1 else 0
def middleBondIndicator (b : BondAtLevel c.L m K k) : ℝ :=
  bondIndicator c x D b - narrowBondIndicator c x D b
def cubeRimBonds (Q : Set (FourTorus c.L m)) : Set (BondAtLevel c.L m K k) :=
  (nonPivotBonds K k Q \ nonPivotBonds K k (boundaryStrip c x D)) ∩ freeVariableBonds c D
def cubeIndicator (Q : Set (FourTorus c.L m)) : ℝ :=
  open Classical in
  if ∀ b ∈ nonPivotBonds K k (testCollar c K x k Q 2),
      FluctuationLt c D b (Thresholds.deltaThreshold c.A₀ c.A₁ c.𝔭₀ x k)
  then 1 else 0
def largeFieldCandidates : Set (Set (FourTorus c.L m)) :=
  unionsOfTestCubes c K x k (shrunkDomain c x D)
def complementInShrunk (R : Set (FourTorus c.L m)) : Set (FourTorus c.L m) :=
  regionDiff (testPartitionIndex c K x k) (shrunkDomain c x D) R
def regionIndicatorCompl (R : Set (FourTorus c.L m)) : ℝ :=
  ∏ᶠ Q ∈ partitionCubesIn (testPartitionIndex c K x k) R, (1 - cubeIndicator c x D Q)
def checkedBonds (R : Set (FourTorus c.L m)) : Set (BondAtLevel c.L m K k) :=
  ⋃ Q ∈ partitionCubesIn (testPartitionIndex c K x k) (complementInShrunk c x D R),
    nonPivotBonds K k (testCollar c K x k Q 2)
def enlargedLargeFieldRegion (C : Set (Set (FourTorus c.L m))) : Set (FourTorus c.L m) :=
  coarseCollar c K x k (complementRegion (coarsePartitionIndex c K x k) D.region) 2 ∪
    coarseCollar c K x k (⋃₀ C) 1
def rimCubes (Z : Set (FourTorus c.L m)) : Set (Set (FourTorus c.L m)) :=
  {Q | Q ∈ shrunkDomainCubes c x D ∧ Q ⊆ Z ∧
    ∃ Q' ∈ partitionCubesIn (coarsePartitionIndex c K x k)
        (complementRegion (coarsePartitionIndex c K x k) Z),
      CubesMeet Q Q'}
def cubesMeetingBonds (J : Set (BondAtLevel c.L m K k)) : Set (Set (FourTorus c.L m)) :=
  {Q | Q ∈ shrunkDomainCubes c x D ∧
    ∃ b ∈ J, (b.source : FourTorus c.L m) ∈ Q ∨ (b.target : FourTorus c.L m) ∈ Q}
structure ExpansionStage (L m K k : ℕ) where
  cubes : Set (Set (FourTorus L m))
  region : Set (FourTorus L m)
  seenBonds : Set (BondAtLevel L m K k)
  seenCubes : Set (Set (FourTorus L m))
structure ExpansionAnswers (L m K k : ℕ) where
  bonds : Set (BondAtLevel L m K k)
  cubes : Set (Set (FourTorus L m))
def freshCollarBonds (s : ExpansionStage c.L m K k) : Set (BondAtLevel c.L m K k) :=
  bondCollar c D (complementRegion (coarsePartitionIndex c K x k) s.region) \ s.seenBonds
def freshRimCubes (s : ExpansionStage c.L m K k) : Set (Set (FourTorus c.L m)) :=
  rimCubes c x D s.region \ s.seenCubes
def flaggedCollarBonds (a : ExpansionAnswers c.L m K k) (s : ExpansionStage c.L m K k) :
    Set (BondAtLevel c.L m K k) :=
  freshCollarBonds c x D s ∩ a.bonds
def flaggedRimCubes (a : ExpansionAnswers c.L m K k) (s : ExpansionStage c.L m K k) :
    Set (Set (FourTorus c.L m)) :=
  freshRimCubes c x D s ∩ a.cubes
def initialStage (R : Set (FourTorus c.L m)) : ExpansionStage c.L m K k where
  cubes := partitionCubesIn (coarsePartitionIndex c K x k) (coarseCubeHull c K x k R)
  region := boxClosure (coarsePartitionIndex c K x k) (enlargedLargeFieldRegion c x D
    (partitionCubesIn (coarsePartitionIndex c K x k) (coarseCubeHull c K x k R)))
  seenBonds := ∅
  seenCubes := ∅
def succStage (a : ExpansionAnswers c.L m K k) (s : ExpansionStage c.L m K k) :
    ExpansionStage c.L m K k where
  cubes := s.cubes ∪ cubesMeetingBonds c x D (flaggedCollarBonds c x D a s) ∪
    flaggedRimCubes c x D a s
  region := boxClosure (coarsePartitionIndex c K x k) (s.region ∪ enlargedLargeFieldRegion c x D
    (s.cubes ∪ cubesMeetingBonds c x D (flaggedCollarBonds c x D a s) ∪ flaggedRimCubes c x D a s))
  seenBonds := s.seenBonds ∪ freshCollarBonds c x D s
  seenCubes := s.seenCubes ∪ freshRimCubes c x D s
def stageAt (a : ExpansionAnswers c.L m K k) (R : Set (FourTorus c.L m)) :
    ℕ → ExpansionStage c.L m K k
  | 0 => initialStage c x D R
  | n + 1 => succStage c x D a (stageAt a R n)
def haltingIndex (a : ExpansionAnswers c.L m K k) (R : Set (FourTorus c.L m)) : ℕ :=
  sInf {n | flaggedCollarBonds c x D a (stageAt c x D a R n) = ∅ ∧
    flaggedRimCubes c x D a (stageAt c x D a R n) = ∅}
def visitedBonds (a : ExpansionAnswers c.L m K k) (R : Set (FourTorus c.L m)) :
    Set (BondAtLevel c.L m K k) :=
  ⋃ n ∈ Iic (haltingIndex c x D a R), freshCollarBonds c x D (stageAt c x D a R n)
def visitedCubes (a : ExpansionAnswers c.L m K k) (R : Set (FourTorus c.L m)) :
    Set (Set (FourTorus c.L m)) :=
  ⋃ n ∈ Iic (haltingIndex c x D a R), freshRimCubes c x D (stageAt c x D a R n)
structure ExpansionOutcome (L m K k : ℕ) where
  region : Set (FourTorus L m)
  bonds : Set (BondAtLevel L m K k)
  cubes : Set (Set (FourTorus L m))
def ExpansionOutcome.toAnswers {L m K k : ℕ} (Ξ : ExpansionOutcome L m K k) :
    ExpansionAnswers L m K k :=
  ⟨Ξ.bonds, Ξ.cubes⟩
def IsAdmissible (Ξ : ExpansionOutcome c.L m K k) : Prop :=
  Ξ.region ∈ largeFieldCandidates c x D ∧ Ξ.bonds ⊆ visitedBonds c x D Ξ.toAnswers Ξ.region ∧
    Ξ.cubes ⊆ visitedCubes c x D Ξ.toAnswers Ξ.region
def haltingRegion (Ξ : ExpansionOutcome c.L m K k) : Set (FourTorus c.L m) :=
  (stageAt c x D Ξ.toAnswers Ξ.region (haltingIndex c x D Ξ.toAnswers Ξ.region)).region
def largeFieldRegionAfter (Ξ : ExpansionOutcome c.L m K k) : Set (FourTorus c.L m) :=
  haltingRegion c x D Ξ
def smallFieldRegionAfter (Ξ : ExpansionOutcome c.L m K k) : Set (FourTorus c.L m) :=
  complementRegion (coarsePartitionIndex c K x k) (haltingRegion c x D Ξ)
def markedSet (Ξ : ExpansionOutcome c.L m K k) : Set (FourTorus c.L m) :=
  boundaryStrip c x D ∪ Ξ.region
def scaleDataAfter (Ξ : ExpansionOutcome c.L m K k) : ScaleData c.L m :=
  ⟨D.region, smallFieldRegionAfter c x D Ξ, markedSet c x D Ξ⟩
def IsSuccLabel (S : LabelAtLevel c m K x k) (S' : LabelAtLevel c m K x (k + 1))
    (Ξ : ExpansionOutcome c.L m K k) : Prop :=
  (∀ (j : ScaleIndex k) (j' : ScaleIndex (k + 1)), (j' : ℕ) = j → S'.atScale j' = S.atScale j) ∧
    ∀ j' : ScaleIndex (k + 1), (j' : ℕ) = k + 1 → S'.atScale j' = scaleDataAfter c x D Ξ
def creationRegion (P' Q' : Set (FourTorus c.L m)) (Ξ : ExpansionOutcome c.L m K k) :
    Set (FourTorus c.L m) :=
  P' ∪ Q' ∪ coarseCubeHull c K x k Ξ.region ∪ ⋃₀ cubesMeetingBonds c x D Ξ.bonds ∪ ⋃₀ Ξ.cubes
section RimSplit
variable (c : ChoiceUpToRadii) {m : ℕ} {K : ℕ} (x : ℕ → ℝ) {k : ℕ}
  (D : StepData c.L m K k)
def rimIndicator (Q : Set (FourTorus c.L m)) : ℝ :=
  open Classical in
  if ∀ b ∈ cubeRimBonds c.toChoiceUpToDegreeConstants x D Q,
      FluctuationLt c.toChoiceUpToDegreeConstants D b
        (c.θc * Thresholds.deltaThreshold c.A₀ c.A₁ c.𝔭₀ x k)
  then 1 else 0
def partitionTerm (Ξ : ExpansionOutcome c.L m K k) : ℝ :=
  regionIndicatorCompl c.toChoiceUpToDegreeConstants x D Ξ.region *
    (∏ᶠ b ∈ checkedBonds c.toChoiceUpToDegreeConstants x D Ξ.region \
        visitedBonds c.toChoiceUpToDegreeConstants x D Ξ.toAnswers Ξ.region,
      bondIndicator c.toChoiceUpToDegreeConstants x D b) *
    (∏ᶠ b ∈ Ξ.bonds, middleBondIndicator c.toChoiceUpToDegreeConstants x D b) *
    (∏ᶠ b ∈ visitedBonds c.toChoiceUpToDegreeConstants x D Ξ.toAnswers Ξ.region \ Ξ.bonds,
      narrowBondIndicator c.toChoiceUpToDegreeConstants x D b) *
    (∏ᶠ Q ∈ Ξ.cubes, (1 - rimIndicator c x D Q)) *
    ∏ᶠ Q ∈ visitedCubes c.toChoiceUpToDegreeConstants x D Ξ.toAnswers Ξ.region \ Ξ.cubes,
      rimIndicator c x D Q
end RimSplit
end CubesOfStep
end PeriodicLattice
end YangMills.Construction
