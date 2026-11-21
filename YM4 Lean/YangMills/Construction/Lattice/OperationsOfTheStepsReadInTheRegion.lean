import YangMills.Construction.Lattice.PartitionsRegionsAndCellsAlongAReferenceSequence
import YangMills.Construction.Lattice.ProductFormOfTheOperationOnAClassComponent
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.ParameterChoice YangMills.Construction.CellRegions
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CubesOfStep
section Resummed
variable (c : ChoiceUpToDegreeConstants) {m : ℕ} (K : ℕ) (x : ℕ → ℝ) {k : ℕ}
def outcomeRegion (S : LabelAtLevel c m K x k) (o : PartitionOfUnityOutcome c.L m) :
    Set (FourTorus c.L m) :=
  smallFieldRegion c K x k (outcomeGaugeRegion c K x S o) o.fluctuationPart
def FixesDomainWithin (S : LabelAtLevel c m K x k) (Ω X : Set (FourTorus c.L m))
    (o : PartitionOfUnityOutcome c.L m) : Prop :=
  IsPartitionOutcome c K x S (outcomeRegion c K x S o) o ∧
    cellInf K (outcomeRegion c K x S o) X = cellInf K Ω X
variable {c K x} {E : ℕ → Type}
variable (c K x)
def resummedStepFactorsWithin (h : LabelHistory c m K x E k) (Ω Y X : Set (FourTorus c.L m))
    (Vk : BondAtLevel c.L m K k → Matrices.ComplexMatrix2)
    (Vt : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) : ℝ :=
  ∑ᶠ r ∈ (fun o : PartitionOfUnityOutcome c.L m => o.restrictTo X) ''
      {o | FixesDomainWithin c K x h.finalLabel Ω X o},
    localizedStepFactors c K x h Y Vk Vt
      (Classical.epsilon fun o => FixesDomainWithin c K x h.finalLabel Ω X o ∧ o.restrictTo X = r)
end Resummed
section Operations
variable {m K : ℕ} (c : ChoiceUpToRadii) (x : ℕ → ℝ) {E : ℕ → Type} {k : ℕ}
  (p : ∀ j, StepData c.L m K j → BondAtLevel c.L m K j → Matrices.ComplexMatrix2)
  (τ : BackgroundVariant)
  (h : LabelHistory c.toChoiceUpToDegreeConstants m K x E k) {j : ℕ} (hj : j < k)
  (X : Set (FourTorus c.L m))
def stepWeightWithin (B : BondAtLevel c.L m K j → Matrices.ComplexMatrix2)
    (V : AllLevelFields c.L m K) : ℂ :=
  let D := stepDataOfFields c.toChoiceUpToDegreeConstants h.finalLabel j V
  ((resummedStepFactorsWithin c.toChoiceUpToDegreeConstants K x (h.stepEntry j hj).prior
      (h.finalLabel.domainSeq (j + 1))
      (domainComplementWithin c.toChoiceUpToDegreeConstants h.finalLabel j X) X
      (V j) (V (j + 1)) : ℝ) : ℂ) *
    ((eliminationWeightProd (backgroundField c.toChoiceUpToDegreeConstants D)
      (eliminatedBonds c.toChoiceUpToDegreeConstants h.finalLabel j X) : ℝ) : ℂ) *
    ((splitFactorsOfVariant c x τ D (h.stepEntry j hj).trace.label (h.stepEntry j hj).trace.outcome
      (h.finalLabel.domainSeq (j + 1))
      (domainLargeFieldWithin c.toChoiceUpToDegreeConstants h.finalLabel j X)
      (newVariables c.toChoiceUpToDegreeConstants x (h.stepEntry j hj).trace.label D
        (h.stepEntry j hj).trace.outcome.region (p j D) B) : ℝ) : ℂ) *
    Complex.exp (-(1 / 2) *
      conditionalFormPart c.toChoiceUpToDegreeConstants h.finalLabel X D (p j D) B)
end Operations
section Product
variable {m K : ℕ} (c : ChoiceUpToRadii) (x : ℕ → ℝ) {E : ℕ → Type} {k : ℕ}
  (τ : BackgroundVariant) (h : LabelHistory c.toChoiceUpToDegreeConstants m K x E k)
  (X : Set (FourTorus c.L m))
def largeFieldOperationWithin (Φ : FieldFunctional c.L m K) : FieldFunctional c.L m K :=
  fun G W =>
    iteratedStepIntegral c x h X W
      (fun A => Φ (fun V => (∏ j : Fin k,
          stepWeightWithin c x (stepBasePoints c) τ h j.2 X (A j).2 V) * G V)
        (allStepsFields c x (stepBasePoints c) τ h X A W))
      k le_rfl (placeholderVariables c x h X)
def lowerStepsProductWithin (l : ℕ) (hl : l ≤ k) (Y : Set (FourTorus c.L m)) :
    LowerOperation c.L m K :=
  { lowerStepsProduct c x τ h l hl Y with
    factor := fun A V => ∏ j : Fin l,
      stepWeightWithin c x (stepBasePoints c) τ h (lt_of_lt_of_le j.2 hl) Y
        (A ⟨j, lt_of_lt_of_le j.2 hl⟩).2 V }
end Product
end YangMills.Construction.PeriodicLattice.CubesOfStep
