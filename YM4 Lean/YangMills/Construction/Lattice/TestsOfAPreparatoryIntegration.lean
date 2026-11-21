import YangMills.Construction.LargeFieldOperation.CollarsAndBondsOfAStage
import YangMills.Construction.Lattice.OneStepAndLargeFieldOperationsAtAPoint
import YangMills.Construction.Lattice.RegularityTestsOfTheStages
import YangMills.Construction.Lattice.ValueOfTheSourceOnAPivotBond
import Mathlib
set_option autoImplicit false
open Set MeasureTheory YangMills.Construction.ParameterChoice
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CubesOfStep
abbrev stageLevel (c : ChoiceUpToDegreeConstants) (x : ℕ → ℝ) (k n : ℕ) : ℕ :=
  ScaleLabel.collarStepLevel c.L c.r x k n
section Indicators
variable (c : ChoiceUpToDegreeConstants) {m K : ℕ} (x : ℕ → ℝ) {j : ℕ} (D : StepData c.L m K j)
def fluctuationBondsNear (q : Set (FourTorus c.L m)) : Set (BondAtLevel c.L m K j) :=
  nonPivotBonds K j (testCollar c K x j q 2) ∩ freeVariableBonds c D
def cubeFluctuationIndicator (q : Set (FourTorus c.L m)) : ℝ :=
  open Classical in
  if ∀ b ∈ fluctuationBondsNear c x D q,
      FluctuationLt c D b (Thresholds.deltaThreshold c.A₀ c.A₁ c.𝔭₀ x j)
  then 1 else 0
def stripLayerIndicator (X : Set (FourTorus c.L m)) : ℝ :=
  ∏ᶠ q ∈ partitionCubesIn (testPartitionIndex c K x j) (boundaryStrip c x D ∩ X),
    cubeFluctuationIndicator c x D q
variable {k : ℕ} (S : LabelAtLevel c m K x k)
def cubeIndicatorOffSmallField (q : Set (FourTorus c.L m)) : ℝ :=
  open Classical in
  if ∀ b ∈ fluctuationBondsNear c x D q \ bondsMeeting (smallFieldRegionAt c S j),
      FluctuationLt c D b (Thresholds.deltaThreshold c.A₀ c.A₁ c.𝔭₀ x j)
  then 1 else 0
def regionIndicatorOffSmallField (X : Set (FourTorus c.L m)) : ℝ :=
  ∏ᶠ q ∈ partitionCubesIn (testPartitionIndex c K x j) (domainLargeFieldWithin c S j X),
    cubeIndicatorOffSmallField c x D S q
end Indicators
section Completed
variable (c : ChoiceUpToRadii) {m K : ℕ} (x : ℕ → ℝ) {j : ℕ} (D : StepData c.L m K j)
  {k : ℕ} (S : LabelAtLevel c.toChoiceUpToDegreeConstants m K x k) (Ξ : ExpansionOutcome c.L m K j)
def completedFluctuationIndicator (X : Set (FourTorus c.L m)) : ℝ :=
  regionIndicatorOffSmallField c.toChoiceUpToDegreeConstants x D S X *
    (∏ᶠ b ∈ visitedBonds c.toChoiceUpToDegreeConstants x D Ξ.toAnswers Ξ.region ∩
        bondsInside (domainLargeFieldWithin c.toChoiceUpToDegreeConstants S j X),
      narrowBondIndicator c.toChoiceUpToDegreeConstants x D b) *
    ∏ᶠ q ∈ visitedCubes c.toChoiceUpToDegreeConstants x D Ξ.toAnswers Ξ.region ∩
        powerset (domainLargeFieldWithin c.toChoiceUpToDegreeConstants S j X),
      rimIndicator c x D q
end Completed
section Stage
variable (c : ChoiceUpToDegreeConstants) {m K : ℕ} (x : ℕ → ℝ) {k : ℕ}
  (S : LabelAtLevel c m K x k) (Q : Set (Set (FourTorus c.L m))) (n : ℕ)
def nextDomainComplement : Set (FourTorus c.L m) :=
  complementRegion (coarseCubeIndex K (Nat.log c.L c.M) (stageLevel c x k n + 1))
    (S.domainSeq (stageLevel c x k n + 1))
def collarRegion : Set (FourTorus c.L m) :=
  regionDiff (coarseCubeIndex K (Nat.log c.L c.M) (stageLevel c x k n + 1))
    (nextDomainComplement c x S n) (S.trimmedRegion c.r x Q (stageLevel c x k n + 1))
def widerCollarRegion : Set (FourTorus c.L m) :=
  regionDiff (coarseCubeIndex K (Nat.log c.L c.M) (stageLevel c x k n))
    (nextDomainComplement c x S n) (S.trimmedRegion c.r x Q (stageLevel c x k n))
def farCollarRegion : Set (FourTorus c.L m) :=
  regionDiff (coarseCubeIndex K (Nat.log c.L c.M) (stageLevel c x k n + 1))
    (complementRegion (nestedCubeIndex c.L c.r x K (Nat.log c.L c.M) (stageLevel c x k n + 1))
      (layerEnlargement (nestedCubeIndex c.L c.r x K (Nat.log c.L c.M) (stageLevel c x k n + 1))
        (S.domainSeq (stageLevel c x k n + 1)) 3))
    (S.trimmedRegion c.r x Q (stageLevel c x k n + 1))
def newGaugeSites (X : Set (FourTorus c.L m)) : Set (SiteAtLevel c.L m K (stageLevel c x k n + 1)) :=
  sitesIn (farCollarRegion c x S Q n ∩ X)
def collarSites (X : Set (FourTorus c.L m)) : Set (SiteAtLevel c.L m K (stageLevel c x k n + 1)) :=
  sitesIn (collarRegion c x S Q n ∩ X)
def collarGaugeWeight (X : Set (FourTorus c.L m)) (V : AllLevelFields c.L m K) : ℝ :=
  ∏ᶠ y ∈ collarSites c x S Q n X,
    ∏ᶠ z ∈ blockSitesExceptCenter K (stageLevel c x k n) y,
      (axialNormalizer (x (stageLevel c x k n))
          (Thresholds.epsThreshold c.A₀ c.𝔭₀ x (stageLevel c x k n)))⁻¹ *
        Real.exp (-x (stageLevel c x k n) *
          traceDeficit (meanContourHolonomy (V (stageLevel c x k n)) y z))
def finalDensityIndicator (V : AllLevelFields c.L m K) : ℝ :=
  densityIndicator c K x k (V k)
    (layerEnlargement (nestedCubeIndex c.L c.r x K (Nat.log c.L c.M) k) (S.domainSeq k) 4)
def collarBlockSites (X : Set (FourTorus c.L m)) : Set (SiteAtLevel c.L m K (stageLevel c x k n)) :=
  ⋃ y ∈ collarSites c x S Q n X, sitesInBlock (levelDepth K (stageLevel c x k n)) y
def sitesAdjacentToCollar (X : Set (FourTorus c.L m)) :
    Set (SiteAtLevel c.L m K (stageLevel c x k n + 1)) :=
  {y | y ∈ (sitesIn (S.domainSeq (stageLevel c x k n + 1)) :
        Set (SiteAtLevel c.L m K (stageLevel c x k n + 1))) ∧
    ∃ b : BondAtLevel c.L m K (stageLevel c x k n),
      (b.source ∈ sitesInBlock (levelDepth K (stageLevel c x k n)) y ∧
          b.target ∈ collarBlockSites c x S Q n X) ∨
        (b.target ∈ sitesInBlock (levelDepth K (stageLevel c x k n)) y ∧
          b.source ∈ collarBlockSites c x S Q n X)}
def stageGaugeSites (X : Set (FourTorus c.L m)) :
    Set (SiteAtLevel c.L m K (stageLevel c x k n + 1)) :=
  collarSites c x S Q n X ∪ sitesAdjacentToCollar c x S Q n X
def IsStageRepresentative (V : AllLevelFields c.L m K)
    (U : BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  IsBlockAxialOrbitRepresentative (Averaging.smoothingRadius c.L) c.εv K k (stageLevel c x k n)
    (S.stagedDomain c.r x Q (n + 1)) (activeBondSet K k (S.stagedDomain c.r x Q (n + 1)))
    (stageGaugeSites c x S Q n (⋃₀ Q)) V U
def StageAverageExists (V : AllLevelFields c.L m K) : Prop :=
  ∃ U, IsStageRepresentative c x S Q n V U
def stageRepresentative (V : AllLevelFields c.L m K) :
    BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2 :=
  Classical.epsilon (IsStageRepresentative c x S Q n V)
def stageMean (V : AllLevelFields c.L m K) :
    BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2 :=
  averagingOnDeterminingSet (Averaging.smoothingRadius c.L) K (S.stagedDomain c.r x Q (n + 1) 0)
    (stageRepresentative c x S Q n V) (stageLevel c x k n)
def localMean (X : Set (FourTorus c.L m)) (V : AllLevelFields c.L m K) :
    BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2 :=
  averagingOnDeterminingSet (Averaging.smoothingRadius c.L) K X
    (stageBackground c x S Q (n + 1) X V) (stageLevel c x k n)
def IsLocalRepresentative (X : Set (FourTorus c.L m)) (V : AllLevelFields c.L m K)
    (U : BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  IsBlockAxialOrbitRepresentative (Averaging.smoothingRadius c.L) c.εv K k (stageLevel c x k n)
    (gluedChain K (Nat.log c.L c.M₁) k (S.stagedDomain c.r x Q (n + 1)) X)
    (gluedActiveSet K k (Nat.log c.L c.M₁) k (S.stagedDomain c.r x Q (n + 1)) X)
    (stageGaugeSites c x S Q n X) (gluedBoundaryData K k k (S.stagedDomain c.r x Q (n + 1)) V) U
def LocalMeanExists (X : Set (FourTorus c.L m)) (V : AllLevelFields c.L m K) : Prop :=
  ∃ U, IsLocalRepresentative c x S Q n X V U
def localMeanInGauge (X : Set (FourTorus c.L m)) (V : AllLevelFields c.L m K) :
    BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2 :=
  averagingOnDeterminingSet (Averaging.smoothingRadius c.L) K
    (gluedChain K (Nat.log c.L c.M₁) k (S.stagedDomain c.r x Q (n + 1)) X 0)
    (Classical.epsilon (IsLocalRepresentative c x S Q n X V)) (stageLevel c x k n)
def collarTestBonds (X : Set (FourTorus c.L m)) : Set (BondAtLevel c.L m K (stageLevel c x k n)) :=
  nonPivotBonds K (stageLevel c x k n) (collarRegion c x S Q n) ∩ bondsMeeting X
def IsCloseOnCollar (X : Set (FourTorus c.L m))
    (W : BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2)
    (V : AllLevelFields c.L m K) : Prop :=
  ∀ b ∈ collarTestBonds c x S Q n X,
    Matrices.ComplexMatrix2.operatorNorm (V (stageLevel c x k n) b * (W b)⁻¹ - 1) <
      2 * Thresholds.deltaPrimeThreshold c.A₁ c.𝔭₁ x (stageLevel c x k n)
def approxCollarIndicatorOfBackground (X : Set (FourTorus c.L m)) (V : AllLevelFields c.L m K) :
    ℝ :=
  open Classical in
  if StageBackgroundExists c x S Q (n + 1) X V ∧
      IsCloseOnCollar c x S Q n X (localMean c x S Q n X V) V
  then 1 else 0
def approxCollarIndicatorInGauge (X : Set (FourTorus c.L m)) (V : AllLevelFields c.L m K) : ℝ :=
  open Classical in
  if LocalMeanExists c x S Q n X V ∧
      IsCloseOnCollar c x S Q n X (localMeanInGauge c x S Q n X V) V
  then 1 else 0
def prodOverComponents (f : Set (FourTorus c.L m) → ℝ) : ℝ := ∏ᶠ X ∈ Q, f X
def collarFieldBonds : Set (BondAtLevel c.L m K (stageLevel c x k n)) :=
  bondsMeeting (widerCollarRegion c x S Q n) ∩ bondsMeeting (⋃₀ Q)
def collarPart (X : Set (FourTorus c.L m)) : Set (FourTorus c.L m) :=
  (nextDomainComplement c x S n \ S.trimmedRegion c.r x Q (stageLevel c x k n + 1)) ∩ X
def collarPositiveBonds : Set (BondAtLevel c.L m K (stageLevel c x k n + 1)) :=
  {e | (∃ X ∈ Q, e ∈ bondsMeetingAvoiding (stageLevel c x k n + 1) (collarPart c x S Q n X)
    (S.domainSeq (stageLevel c x k n + 1))) ∧ e.IsPositivelyOriented}
def collarEliminated (p B : BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2) :
    BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2 :=
  (Thresholds.couplingAt x (stageLevel c x k n) : ℂ) •
    eliminate p (collarPositiveBonds c x S Q n) B
def collarSourceField (e : BondAtLevel c.L m K (stageLevel c x k n + 1))
    (B : BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2) :
    LieBondField (setWithoutPivot e) :=
  fun b => toTraceless ((Thresholds.couplingAt x (stageLevel c x k n) : ℂ) • B b.1)
open Classical in
def collarTwistForm (p B : BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2) :
    BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2 := fun b =>
  if h : ∃ e ∈ collarPositiveBonds c x S Q n, b = pivot e then
    (pivotSourceAt h.choose p (collarSourceField c x n h.choose B) : Matrices.ComplexMatrix2)
  else if h' : ∃ e ∈ collarPositiveBonds c x S Q n, b.opposite = pivot e then
    -(pivotSourceAt h'.choose p (collarSourceField c x n h'.choose B) : Matrices.ComplexMatrix2)
  else (Thresholds.couplingAt x (stageLevel c x k n) : ℂ) • B b
def collarSubstitute (V : AllLevelFields c.L m K)
    (B : BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2) :
    BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2 :=
  expTwist (collarTwistForm c x S Q n (stageMean c x S Q n V) B) (stageMean c x S Q n V)
def HasSmallLogOnCollar (X : Set (FourTorus c.L m))
    (W : BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2)
    (V : AllLevelFields c.L m K) : Prop :=
  ∀ b ∈ collarTestBonds c x S Q n X,
    V (stageLevel c x k n) b * (W b)⁻¹ ≠ -1 ∧
      Matrices.ComplexMatrix2.operatorNorm
          (Complex.I⁻¹ • Matrices.ComplexMatrix2.unitaryLog (V (stageLevel c x k n) b * (W b)⁻¹)) <
        Thresholds.deltaPrimeThreshold c.A₁ c.𝔭₁ x (stageLevel c x k n)
def collarSmallIndicator (X : Set (FourTorus c.L m)) (V : AllLevelFields c.L m K) : ℝ :=
  open Classical in
  if StageAverageExists c x S Q n V ∧
      HasSmallLogOnCollar c x S Q n X (stageMean c x S Q n V) V
  then 1 else 0
def collarSmallIndicatorLocal (X : Set (FourTorus c.L m)) (V : AllLevelFields c.L m K) : ℝ :=
  open Classical in
  if LocalMeanExists c x S Q n X V ∧
      HasSmallLogOnCollar c x S Q n X (localMeanInGauge c x S Q n X V) V
  then 1 else 0
end Stage
section LabelHistories
variable {E : ℕ → Type}
def historyOutcome {c : ChoiceUpToDegreeConstants} {m K : ℕ} {x : ℕ → ℝ} {k : ℕ}
    (h : LabelHistory c m K x E k) (j : ℕ) : ExpansionOutcome c.L m K j :=
  if hj : j < k then (h.stepEntry j hj).trace.outcome else ⟨∅, ∅, ∅⟩
def stageCompletedIndicator (c : ChoiceUpToRadii) {m K : ℕ} (x : ℕ → ℝ) {k : ℕ}
    (h : LabelHistory c.toChoiceUpToDegreeConstants m K x E k) (n : ℕ) (X : Set (FourTorus c.L m))
    (V : AllLevelFields c.L m K) : ℝ :=
  completedFluctuationIndicator c x
    (stepDataOfFields c.toChoiceUpToDegreeConstants h.finalLabel
      (stageLevel c.toChoiceUpToDegreeConstants x k n) V)
    h.finalLabel (historyOutcome h (stageLevel c.toChoiceUpToDegreeConstants x k n)) X
end LabelHistories
end YangMills.Construction.PeriodicLattice.CubesOfStep
