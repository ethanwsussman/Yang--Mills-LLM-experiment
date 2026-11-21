import YangMills.Construction.Lattice.BondwiseAverage
import YangMills.Construction.Lattice.ChangeOfVariablesOnTheStrip
import YangMills.Construction.Lattice.DensityTestsCarriedByATerm
import YangMills.Construction.Lattice.GaugeFixingFactor
import YangMills.Construction.Lattice.HistoriesCreationAndAges
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.ParameterChoice
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CubesOfStep
structure PartitionOfUnityOutcome (L m : ℕ) where
  densityPart : Set (FourTorus L m)
  plaquettePart : Set (FourTorus L m)
  fluctuationPart : Set (FourTorus L m)
instance instNonemptyPartitionOfUnityOutcome {L m : ℕ} : Nonempty (PartitionOfUnityOutcome L m) :=
  ⟨⟨∅, ∅, ∅⟩⟩
def PartitionOfUnityOutcome.restrictTo {L m : ℕ} (o : PartitionOfUnityOutcome L m)
    (X : Set (FourTorus L m)) : PartitionOfUnityOutcome L m :=
  ⟨o.densityPart ∩ X, o.plaquettePart ∩ X, o.fluctuationPart ∩ X⟩
def partitionTermFactor {L m : ℕ} (i : ℤ) (f : Set (FourTorus L m) → ℝ)
    (R P Y : Set (FourTorus L m)) : ℝ :=
  (∏ᶠ Q ∈ (partitionCubesIn i R \ partitionCubesIn i P) ∩ powerset Y, f Q) *
    ∏ᶠ Q ∈ partitionCubesIn i P ∩ powerset Y, (1 - f Q)
section Resummed
variable (c : ChoiceUpToDegreeConstants) {m : ℕ} (K : ℕ) (x : ℕ → ℝ) {k : ℕ}
def outcomePlaquetteRegion (S : LabelAtLevel c m K x k) (o : PartitionOfUnityOutcome c.L m) :
    Set (FourTorus c.L m) :=
  if k = 0 then
    complementRegion (coarsePartitionIndex c K x 0)
      (coarseCollar c K x 0 (coarseCubeHull c K x 0 o.densityPart) 1)
  else plaquetteTestRegion c K x k (incomingRegion c K x S)
def outcomeGaugeRegion (S : LabelAtLevel c m K x k) (o : PartitionOfUnityOutcome c.L m) :
    Set (FourTorus c.L m) :=
  if k = 0 then
    gaugeFixedRegion c K x 0 o.plaquettePart
      (coarseCollar c K x 0 (coarseCubeHull c K x 0 o.densityPart) 2)
  else stepGaugeFixedRegion c K x k o.plaquettePart (incomingRegion c K x S)
def IsPartitionOutcome (S : LabelAtLevel c m K x k) (Ω : Set (FourTorus c.L m))
    (o : PartitionOfUnityOutcome c.L m) : Prop :=
  (k = 0 → ∃ C ⊆ densityPartition c K x 0, o.densityPart = ⋃₀ C) ∧ (k ≠ 0 → o.densityPart = ∅) ∧
    o.plaquettePart ∈ unionsOfTestCubes c K x k (outcomePlaquetteRegion c K x S o) ∧
    o.fluctuationPart ∈
      unionsOfTestCubes c K x k (fluctuationTestRegion c K x k (outcomeGaugeRegion c K x S o)) ∧
    Ω = smallFieldRegion c K x k (outcomeGaugeRegion c K x S o) o.fluctuationPart
variable {c K x} {E : ℕ → Type}
def LabelHistory.heldDensityCubes : ∀ {k : ℕ}, LabelHistory c m K x E k → Set (Set (FourTorus c.L m))
  | _, .initial => ∅
  | k + 1, .extend _ _ o =>
    untouchedDensityCubes c K x (k + 1) (o.label.domainSeq (k + 1)) o.outcome.classTwo
variable (c K x)
def localizedStepFactors (h : LabelHistory c m K x E k) (Y : Set (FourTorus c.L m))
    (Vk : BondAtLevel c.L m K k → Matrices.ComplexMatrix2)
    (Vt : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2)
    (o : PartitionOfUnityOutcome c.L m) : ℝ :=
  partitionTermFactor (testPartitionIndex c K x k) (plaquetteIndicator c K x k Vt)
      (outcomePlaquetteRegion c K x h.finalLabel o) o.plaquettePart Y *
    partitionTermFactor (testPartitionIndex c K x k) (fluctuationIndicator c K x k Vk Vt)
      (fluctuationTestRegion c K x k (outcomeGaugeRegion c K x h.finalLabel o)) o.fluctuationPart Y *
    axialGaugeFactor c.A₀ c.𝔭₀ x K k Vk
      (gaugeFixedSites c K k (outcomeGaugeRegion c K x h.finalLabel o) ∩ gaugeFixedSites c K k Y) *
    (if k = 0 then
        partitionTermFactor (densityPartitionIndex c K x k) (densityCubeIndicator c K x k Vk) univ
          o.densityPart Y
      else 1) *
    ∏ᶠ Q ∈ h.heldDensityCubes ∩ powerset Y, densityCubeIndicator c K x k Vk Q
def resummedStepFactors (h : LabelHistory c m K x E k) (Ω Y X : Set (FourTorus c.L m))
    (Vk : BondAtLevel c.L m K k → Matrices.ComplexMatrix2)
    (Vt : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) : ℝ :=
  ∑ᶠ r ∈ (fun o : PartitionOfUnityOutcome c.L m => o.restrictTo X) ''
      {o | IsPartitionOutcome c K x h.finalLabel Ω o},
    localizedStepFactors c K x h Y Vk Vt
      (Classical.epsilon fun o => IsPartitionOutcome c K x h.finalLabel Ω o ∧ o.restrictTo X = r)
end Resummed
section Split
variable {m K k : ℕ}
def fluctuationIndicatorOfBondIndicator (c : ChoiceUpToDegreeConstants) (x : ℕ → ℝ)
    (S : LabelAtLevel c m K x (k + 1)) (D : StepData c.L m K k) (R : Set (FourTorus c.L m))
    (T : (BondAtLevel c.L m K k → Matrices.ComplexMatrix2) → BondAtLevel c.L m K k → ℝ)
    (W : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) (Q : Set (FourTorus c.L m)) : ℝ :=
  open Classical in
  if AxialBackgroundDefined c K x k Q D.next ∧
      ∀ e ∈ nonPivotBonds K k (testCollar c K x k Q 2),
        if e.positivelyOriented ∈ changedBonds c x S D R ∧
            bondCutoffWeight c x S D R e.positivelyOriented (W e.positivelyOriented) = 1 ∧
            W e.positivelyOriented ≠ -1 then
          T (newFluctuationLog c x S D R W) e = 1
        else
          Matrices.ComplexMatrix2.operatorNorm
              (D.current e * (axialGaugeBackground c K x k Q D.next e)⁻¹ - 1) <
            2 * Thresholds.deltaThreshold c.A₀ c.A₁ c.𝔭₀ x k
  then 1 else 0
def fluctuationIndicatorNewVariables (c : ChoiceUpToDegreeConstants) (x : ℕ → ℝ)
    (S : LabelAtLevel c m K x (k + 1)) (D : StepData c.L m K k) (R : Set (FourTorus c.L m))
    (W : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) (Q : Set (FourTorus c.L m)) : ℝ :=
  fluctuationIndicatorOfBondIndicator c x S D R
    (orientedSmallFieldIndicator c x S D R D.next Q) W Q
def fluctuationIndicatorNewVariablesOffEndpoints (c : ChoiceUpToDegreeConstants) (x : ℕ → ℝ)
    (S : LabelAtLevel c m K x (k + 1)) (D : StepData c.L m K k) (R : Set (FourTorus c.L m))
    (W : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) (Q : Set (FourTorus c.L m)) : ℝ :=
  fluctuationIndicatorOfBondIndicator c x S D R
    (orientedSmallFieldIndicatorOffEndpoints c x S D R D.next Q) W Q
variable (c : ChoiceUpToRadii) (x : ℕ → ℝ) (D : StepData c.L m K k)
def splitFactorsLocalized (Ξ : ExpansionOutcome c.L m K k) (Y : Set (FourTorus c.L m)) : ℝ :=
  (∏ᶠ Q ∈ partitionCubesIn (testPartitionIndex c.toChoiceUpToDegreeConstants K x k) Ξ.region ∩
        powerset Y,
      (1 - cubeIndicator c.toChoiceUpToDegreeConstants x D Q)) *
    (∏ᶠ e ∈ (checkedBonds c.toChoiceUpToDegreeConstants x D Ξ.region \
          visitedBonds c.toChoiceUpToDegreeConstants x D Ξ.toAnswers Ξ.region) ∩ bondsInside Y,
      bondIndicator c.toChoiceUpToDegreeConstants x D e) *
    (∏ᶠ e ∈ Ξ.bonds ∩ bondsInside Y, middleBondIndicator c.toChoiceUpToDegreeConstants x D e) *
    (∏ᶠ e ∈ (visitedBonds c.toChoiceUpToDegreeConstants x D Ξ.toAnswers Ξ.region \ Ξ.bonds) ∩
        bondsInside Y,
      narrowBondIndicator c.toChoiceUpToDegreeConstants x D e) *
    (∏ᶠ Q ∈ Ξ.cubes ∩ powerset Y, (1 - rimIndicator c x D Q)) *
    ∏ᶠ Q ∈ (visitedCubes c.toChoiceUpToDegreeConstants x D Ξ.toAnswers Ξ.region \ Ξ.cubes) ∩
        powerset Y,
      rimIndicator c x D Q
def localizedSplitFactors (S : LabelAtLevel c.toChoiceUpToDegreeConstants m K x (k + 1))
    (Ξ : ExpansionOutcome c.L m K k) (Ω Y : Set (FourTorus c.L m))
    (W : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) : ℝ :=
  splitFactorsLocalized c x D Ξ Y *
    ∏ᶠ Q ∈ partitionCubesIn (testPartitionIndex c.toChoiceUpToDegreeConstants K x k) Ω ∩ powerset Y,
      fluctuationIndicatorNewVariables c.toChoiceUpToDegreeConstants x S D Ξ.region W Q
def localizedSplitFactorsOffEndpoints (S : LabelAtLevel c.toChoiceUpToDegreeConstants m K x (k + 1))
    (Ξ : ExpansionOutcome c.L m K k) (Ω Y : Set (FourTorus c.L m))
    (W : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) : ℝ :=
  splitFactorsLocalized c x D Ξ Y *
    ∏ᶠ Q ∈ partitionCubesIn (testPartitionIndex c.toChoiceUpToDegreeConstants K x k) Ω ∩ powerset Y,
      fluctuationIndicatorNewVariablesOffEndpoints c.toChoiceUpToDegreeConstants x S D Ξ.region W Q
end Split
end YangMills.Construction.PeriodicLattice.CubesOfStep
