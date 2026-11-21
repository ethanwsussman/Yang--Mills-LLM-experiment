import YangMills.Construction.Lattice.LocalisedBackgroundOfTheStrip
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CubesOfStep
open Matrices ParameterChoice
def IsCollarCutoffShape (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ici 0) ∧ MapsTo f (Ici 0) (Icc 0 1) ∧ (∀ s ∈ Icc (0 : ℝ) (4 / 3), f s = 0) ∧
    ∀ s ∈ Ici (5 / 3 : ℝ), f s = 1
def collarCutoffShape : ℝ → ℝ := Classical.epsilon IsCollarCutoffShape
variable (c : ChoiceUpToDegreeConstants) {m K : ℕ} (x : ℕ → ℝ) {k : ℕ}
def collarCutoff (k : ℕ) (a : ComplexMatrix2) : ℝ :=
  collarCutoffShape (ComplexMatrix2.operatorNorm a / Thresholds.deltaThreshold c.A₀ c.A₁ c.𝔭₀ x k)
variable (S : LabelAtLevel c m K x (k + 1)) (D : StepData c.L m K k) (R : Set (FourTorus c.L m))
def smallFieldBonds : Set (BondAtLevel c.L m K k) :=
  ⋃ Q ∈ partitionCubesIn (testPartitionIndex c K x k)
      (regionDiff (testPartitionIndex c K x k) (shrunkDomain c x D) R),
    nonPivotBonds K k (testCollar c K x k Q 2)
def largeFieldNeighbourBonds : Set (BondAtLevel c.L m K k) :=
  ⋃ Q ∈ partitionCubesIn (testPartitionIndex c K x k) R, nonPivotBonds K k (testCollar c K x k Q 2)
def cutoffRegion : Set (BondAtLevel c.L m K k) :=
  (stripInteriorBonds c x S ∩ largeFieldNeighbourBonds c x R) \ smallFieldBonds c x D R
def freeRegion : Set (BondAtLevel c.L m K k) :=
  stripInteriorBonds c x S \ (smallFieldBonds c x D R ∪ largeFieldNeighbourBonds c x R)
def bondCutoffWeight (b : BondAtLevel c.L m K k) (W : ComplexMatrix2) : ℝ :=
  open Classical in
  if b ∈ cutoffRegion c x S D R then
    if W = -1 then 1 else collarCutoff c x k (Complex.I⁻¹ • ComplexMatrix2.unitaryLog W)
  else 1
def shiftedBondMap (H : ComplexMatrix2) (b : BondAtLevel c.L m K k) (W : ComplexMatrix2) :
    ComplexMatrix2 :=
  W * ComplexMatrix2.matExp (-(Complex.I * (bondCutoffWeight c x S D R b W : ℂ)) • H) *
    ComplexMatrix2.matExp (Complex.I • H)
def changedBonds : Set (BondAtLevel c.L m K k) :=
  cutoffRegion c x S D R ∪ freeRegion c x S D R
def shiftedSubstitutionOriented (H B W : BondAtLevel c.L m K k → ComplexMatrix2) :
    BondAtLevel c.L m K k → ComplexMatrix2 :=
  open Classical in
  fun b => if b.IsPositivelyOriented then
      (if b ∈ changedBonds c x S D R then shiftedBondMap c x S D R (H b) b (W b) * B b else W b)
    else if b.opposite ∈ changedBonds c x S D R then
      (shiftedBondMap c x S D R (H b.opposite) b.opposite (W b.opposite) * B b.opposite)⁻¹
    else W b
def collarSubstitutionOriented (W : BondAtLevel c.L m K k → ComplexMatrix2) :
    BondAtLevel c.L m K k → ComplexMatrix2 :=
  shiftedSubstitutionOriented c x S D R (backgroundShiftLog c x S D)
    (localStripAveraged c x S D) W
def collarSubstitutionOrientedOffEndpoints (W : BondAtLevel c.L m K k → ComplexMatrix2) :
    BondAtLevel c.L m K k → ComplexMatrix2 :=
  shiftedSubstitutionOriented c x S D R (backgroundShiftLogOffEndpoints c x S D)
    (localStripAveragedOffEndpoints c x S D) W
def newFluctuationLog (W : BondAtLevel c.L m K k → ComplexMatrix2) (b : BondAtLevel c.L m K k) :
    ComplexMatrix2 :=
  open Classical in
  if b ∈ changedBonds c x S D R then Complex.I⁻¹ • ComplexMatrix2.unitaryLog (W b)
  else Complex.I⁻¹ • ComplexMatrix2.unitaryLog (W b * (backgroundField c D b)⁻¹)
def smallFieldIndicatorAt (B : ComplexMatrix2) (Vt : BondAtLevel c.L m K (k + 1) → ComplexMatrix2)
    (Q : Set (FourTorus c.L m)) (A : ComplexMatrix2) (b : BondAtLevel c.L m K k) : ℝ :=
  open Classical in
  if AxialBackgroundDefined c K x k Q Vt ∧
      ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp (Complex.I • A) * B *
          (axialGaugeBackground c K x k Q Vt b)⁻¹ - 1) <
        2 * Thresholds.deltaThreshold c.A₀ c.A₁ c.𝔭₀ x k
  then 1 else 0
def orientedSmallFieldIndicatorAt (B : BondAtLevel c.L m K k → ComplexMatrix2)
    (Vt : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) (Q : Set (FourTorus c.L m))
    (A : BondAtLevel c.L m K k → ComplexMatrix2) (b : BondAtLevel c.L m K k) : ℝ :=
  open Classical in
  if ¬b.IsPositivelyOriented ∧ b.opposite ∈ changedBonds c x S D R then
    if AxialBackgroundDefined c K x k Q Vt ∧
        ComplexMatrix2.operatorNorm
            ((ComplexMatrix2.matExp (Complex.I • A b.opposite) * B b.opposite)⁻¹ *
              (axialGaugeBackground c K x k Q Vt b)⁻¹ - 1) <
          2 * Thresholds.deltaThreshold c.A₀ c.A₁ c.𝔭₀ x k
    then 1 else 0
  else smallFieldIndicatorAt c x (B b) Vt Q (A b) b
def orientedSmallFieldIndicator (Vt : BondAtLevel c.L m K (k + 1) → ComplexMatrix2)
    (Q : Set (FourTorus c.L m)) (A : BondAtLevel c.L m K k → ComplexMatrix2)
    (b : BondAtLevel c.L m K k) : ℝ :=
  orientedSmallFieldIndicatorAt c x S D R (localStripAveraged c x S D) Vt Q A b
def orientedSmallFieldIndicatorOffEndpoints (Vt : BondAtLevel c.L m K (k + 1) → ComplexMatrix2)
    (Q : Set (FourTorus c.L m)) (A : BondAtLevel c.L m K k → ComplexMatrix2)
    (b : BondAtLevel c.L m K k) : ℝ :=
  orientedSmallFieldIndicatorAt c x S D R (localStripAveragedOffEndpoints c x S D) Vt Q A b
end YangMills.Construction.PeriodicLattice.CubesOfStep
