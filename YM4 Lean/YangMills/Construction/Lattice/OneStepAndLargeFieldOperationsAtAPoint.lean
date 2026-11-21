import YangMills.Construction.Lattice.FluctuationCovarianceOfAStepAtAPoint
import YangMills.Construction.Lattice.FunctionsCarriedByAOneStepOperation
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice.CubesOfStep
abbrev AllLevelFields (L m K : ℕ) : Type := ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2
abbrev FieldFunctional (L m K : ℕ) : Type := (AllLevelFields L m K → ℂ) → AllLevelFields L m K → ℂ
def assignOnBonds {L m : ℕ} {j : ℤ} (Y : Set (Bond L m j))
    (w : {b : Bond L m j // b ∈ Y ∧ b.IsPositivelyOriented} → ComplexMatrix2)
    (V : Bond L m j → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  open Classical in
  fun b => if hb : b ∈ Y ∧ b.IsPositivelyOriented then w ⟨b, hb⟩
    else if hb' : b.opposite ∈ Y ∧ b.opposite.IsPositivelyOriented then (w ⟨b.opposite, hb'⟩)⁻¹
    else V b
def complexPairedSpaceIntegral {F : Type*} [AddCommGroup F] [Module ℝ F] (P : F → F → ℝ)
    (E : Set F) (Ψ : F → ℂ) : ℂ :=
  (pairedSpaceIntegral P E (fun v => (Ψ v).re) : ℂ) +
    Complex.I * (pairedSpaceIntegral P E (fun v => (Ψ v).im) : ℂ)
section Regions
variable (c : ParameterChoice.ChoiceUpToDegreeConstants) {m K : ℕ} {x : ℕ → ℝ} {k : ℕ}
  (S : LabelAtLevel c m K x k) (j : ℕ) (X : Set (FourTorus c.L m))
def IsUnionOfLargeFieldParts : Prop :=
  ∃ C ⊆ regionComponents (coarseCubeIndex K (Nat.log c.L c.M) k) (S.largeFieldOrEmpty k),
    X = ⋃₀ C
def smallFieldRegionAt : Set (FourTorus c.L m) :=
  open Classical in
  if hs : j + 1 ∈ Set.Icc 1 k then (S.atScale ⟨j + 1, hs⟩).smallFieldRegion else ∅
def domainComplementWithin : Set (FourTorus c.L m) :=
  complementRegion (coarseCubeIndex K (Nat.log c.L c.M) (j + 1)) (S.domainSeq (j + 1)) ∩ X
def domainLargeFieldWithin : Set (FourTorus c.L m) :=
  S.domainSeq (j + 1) ∩ S.largeFieldOrEmpty (j + 1) ∩ X
def largeFieldWithin : Set (FourTorus c.L m) := S.largeFieldOrEmpty (j + 1) ∩ X
def haarIntegratedBonds : Set (BondAtLevel c.L m K j) :=
  determiningBondsAt K k S.domainSeq j ∩ bondsInside (domainComplementWithin c S j X)
def averagedBonds : Set (BondAtLevel c.L m K (j + 1)) :=
  bondsInside (domainComplementWithin c S j X)
def eliminatedBonds : Set (BondAtLevel c.L m K (j + 1)) :=
  {e | e ∈ determiningBondsAt K k S.domainSeq (j + 1) ∧ e ∈ bondsInside (largeFieldWithin c S j X) ∧
    e.IsPositivelyOriented}
def stepDataOfFields (U : AllLevelFields c.L m K) : StepData c.L m K j :=
  ⟨S.domainSeq, S.domainSeq (j + 1), U, U j, U (j + 1)⟩
variable {j}
def fluctuationBondsWithin (D : StepData c.L m K j) (Y : Set (FourTorus c.L m)) :
    Set (BondAtLevel c.L m K j) :=
  bondsMeeting Y ∩ (freeVariableBonds c D \ bondsMeeting (smallFieldRegionAt c S j))
def conditionalFormPart (D : StepData c.L m K j) (p : BondAtLevel c.L m K j → ComplexMatrix2)
    (A : BondAtLevel c.L m K j → ComplexMatrix2) : ℂ :=
  ∑ᶠ C ∈ {C | C ∈ regionComponents (coarseCubeIndex K (Nat.log c.L c.M) (j + 1))
      (S.domainSeq (j + 1) ∩ S.largeFieldOrEmpty (j + 1)) ∧ C ⊆ X},
    conditionalForm c D p (bondsMeeting (smallFieldRegionAt c S j) ∩ freeVariableBonds c D)
      (restrictForm c (fluctuationBondsWithin c S D C) A)
end Regions
section EvaluationMaps
variable (c : ParameterChoice.ChoiceUpToDegreeConstants) {m K : ℕ} (x : ℕ → ℝ) {j : ℕ}
  (S : LabelAtLevel c m K x (j + 1)) (D : StepData c.L m K j) (R : Set (FourTorus c.L m))
  (p B : BondAtLevel c.L m K j → ComplexMatrix2)
def newVariables : BondAtLevel c.L m K j → ComplexMatrix2 :=
  open Classical in
  fun b => if b ∈ changedBonds c x S D R then
      ComplexMatrix2.matExp (Complex.I • ((Thresholds.couplingAt x j : ℂ) • B b))
    else expTwist (linearizedVariable c D p x B) (backgroundField c D) b
def fluctuationField : BondAtLevel c.L m K j → ComplexMatrix2 :=
  collarSubstitutionOriented c x S D R (newVariables c x S D R p B)
def fluctuationFieldOffEndpoints : BondAtLevel c.L m K j → ComplexMatrix2 :=
  collarSubstitutionOrientedOffEndpoints c x S D R (newVariables c x S D R p B)
end EvaluationMaps
section Operations
variable {m K : ℕ}
inductive BackgroundVariant where
  | original
  | offEndpoints
structure HistoryStep (c : ParameterChoice.ChoiceUpToDegreeConstants) (m K : ℕ) (x : ℕ → ℝ)
    (E : ℕ → Type) (j : ℕ) where
  prior : LabelHistory c m K x E j
  trace : StepTrace c m K x j
def LabelHistory.stepEntry {c : ParameterChoice.ChoiceUpToDegreeConstants} {x : ℕ → ℝ}
    {E : ℕ → Type} :
    ∀ {k : ℕ}, LabelHistory c m K x E k → ∀ j, j < k → HistoryStep c m K x E j
  | _, .initial, _, hj => absurd hj (Nat.not_lt_zero _)
  | k + 1, .extend H t _, j, hj =>
    if e : j = k then e ▸ ⟨H, t⟩ else H.stepEntry j (by omega)
variable (c : ParameterChoice.ChoiceUpToRadii) (x : ℕ → ℝ) {E : ℕ → Type} {k : ℕ}
  (p : ∀ j, StepData c.L m K j → BondAtLevel c.L m K j → ComplexMatrix2)
  (τ : BackgroundVariant)
  (h : LabelHistory c.toChoiceUpToDegreeConstants m K x E k) {j : ℕ} (hj : j < k)
  (X : Set (FourTorus c.L m))
def fluctuationFieldOfVariant (S : LabelAtLevel c.toChoiceUpToDegreeConstants m K x (j + 1))
    (D : StepData c.L m K j) (R : Set (FourTorus c.L m))
    (q B : BondAtLevel c.L m K j → ComplexMatrix2) : BondAtLevel c.L m K j → ComplexMatrix2 :=
  match τ with
  | .original => fluctuationField c.toChoiceUpToDegreeConstants x S D R q B
  | .offEndpoints => fluctuationFieldOffEndpoints c.toChoiceUpToDegreeConstants x S D R q B
def splitFactorsOfVariant (D : StepData c.L m K j)
    (S : LabelAtLevel c.toChoiceUpToDegreeConstants m K x (j + 1)) (O : ExpansionOutcome c.L m K j)
    (Ω Y : Set (FourTorus c.L m)) (U : BondAtLevel c.L m K j → ComplexMatrix2) : ℝ :=
  match τ with
  | .original => localizedSplitFactors c x D S O Ω Y U
  | .offEndpoints => localizedSplitFactorsOffEndpoints c x D S O Ω Y U
def fieldsReadFromFluctuation (V : AllLevelFields c.L m K) (B : BondAtLevel c.L m K j → ComplexMatrix2) :
    AllLevelFields c.L m K :=
  let D := stepDataOfFields c.toChoiceUpToDegreeConstants h.finalLabel j V
  Function.update V j
    (open Classical in fun b =>
      if b ∈ (bondsMeeting (h.finalLabel.domainSeq (j + 1) ∩ X) : Set (BondAtLevel c.L m K j)) then
        fluctuationFieldOfVariant c x τ (h.stepEntry j hj).trace.label D
          (h.stepEntry j hj).trace.outcome.region (p j D) B b
      else V j b)
def operationWeight (B : BondAtLevel c.L m K j → ComplexMatrix2) (V : AllLevelFields c.L m K) : ℂ :=
  let D := stepDataOfFields c.toChoiceUpToDegreeConstants h.finalLabel j V
  ((resummedStepFactors c.toChoiceUpToDegreeConstants K x (h.stepEntry j hj).prior
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
variable {m K : ℕ} (c : ParameterChoice.ChoiceUpToRadii) (x : ℕ → ℝ) {E : ℕ → Type} {k : ℕ}
  (p : ∀ j, StepData c.L m K j → BondAtLevel c.L m K j → ComplexMatrix2) (τ : BackgroundVariant)
  (h : LabelHistory c.toChoiceUpToDegreeConstants m K x E k) (X : Set (FourTorus c.L m))
abbrev StepVariables (j : ℕ) : Type :=
  ({b : BondAtLevel c.L m K j //
    b ∈ haarIntegratedBonds c.toChoiceUpToDegreeConstants h.finalLabel j X ∧
      b.IsPositivelyOriented} → ComplexMatrix2.specialUnitary) ×
    (BondAtLevel c.L m K j → ComplexMatrix2)
abbrev AllStepVariables : Type := ∀ j : Fin k, StepVariables c x h X j
def placeholderVariables : AllStepVariables c x h X := fun _ => (fun _ => 1, fun _ _ => 0)
variable {c x h X}
def assignHaarValues (A : AllStepVariables c x h X) (j : ℕ) (U : BondAtLevel c.L m K j → ComplexMatrix2) :
    BondAtLevel c.L m K j → ComplexMatrix2 :=
  if hj : j < k then
    assignOnBonds (haarIntegratedBonds c.toChoiceUpToDegreeConstants h.finalLabel j X)
      (fun b => ((A ⟨j, hj⟩).1 b : ComplexMatrix2)) U
  else U
variable (h X) in
def assignAverages (j : ℕ) (U : BondAtLevel c.L m K j → ComplexMatrix2)
    (U' : BondAtLevel c.L m K (j + 1) → ComplexMatrix2) : BondAtLevel c.L m K (j + 1) → ComplexMatrix2 :=
  if j < k then
    assignOnBonds (averagedBonds c.toChoiceUpToDegreeConstants h.finalLabel j X)
      (fun e => blockAverageStep (Averaging.smoothingRadius c.L) j U e.1) U'
  else U'
def fieldsUpward (A : AllStepVariables c x h X) (U : AllLevelFields c.L m K) : AllLevelFields c.L m K
  | 0 => assignHaarValues A 0 (U 0)
  | n + 1 => assignHaarValues A (n + 1) (assignAverages h X n (fieldsUpward A U n) (U (n + 1)))
variable (c x h X)
def fieldsDownward (A : AllStepVariables c x h X) :
    ∀ n, n ≤ k → AllLevelFields c.L m K → AllLevelFields c.L m K
  | 0, _, V => V
  | n + 1, hn, V =>
    fieldsDownward A n (by omega)
      (fieldsReadFromFluctuation c x p τ h (j := n) (by omega) X V (A ⟨n, by omega⟩).2)
def allStepsFields (A : AllStepVariables c x h X) (U : AllLevelFields c.L m K) :
    AllLevelFields c.L m K :=
  fieldsDownward c x p τ h X A k le_rfl (fieldsUpward A U)
def iteratedStepIntegral (U : AllLevelFields c.L m K) (Ψ : AllStepVariables c x h X → ℂ) :
    ∀ n, n ≤ k → AllStepVariables c x h X → ℂ
  | 0, _, A => Ψ A
  | n + 1, hn, A =>
    ∫ v, complexPairedSpaceIntegral unitBondInner
        (realBondFormsOn (fluctuationBondsWithin c.toChoiceUpToDegreeConstants h.finalLabel
          (stepDataOfFields c.toChoiceUpToDegreeConstants h.finalLabel n U)
          (domainLargeFieldWithin c.toChoiceUpToDegreeConstants h.finalLabel n X)))
        (fun B => iteratedStepIntegral U Ψ n (by omega)
          (Function.update A ⟨n, by omega⟩ (v, B)))
      ∂ComplexMatrix2.haarPi {b : BondAtLevel c.L m K n //
        b ∈ haarIntegratedBonds c.toChoiceUpToDegreeConstants h.finalLabel n X ∧
          b.IsPositivelyOriented}
end Product
end PeriodicLattice.CubesOfStep
end YangMills.Construction
