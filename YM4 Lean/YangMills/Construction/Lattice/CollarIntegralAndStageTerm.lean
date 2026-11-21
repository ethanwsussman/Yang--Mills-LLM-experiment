import YangMills.Construction.Lattice.AnalyticitySpacesOfTheStages
import YangMills.Construction.Lattice.ObjectsOfAStepStepFunctionalAndInteractionByOrigin
import YangMills.Construction.Lattice.OneStepAndLargeFieldOperations
import YangMills.Construction.Lattice.ScalingAndGaugeConstantOfAStep
import YangMills.Construction.Lattice.SmallFieldRegionsOfTheStages
import YangMills.Construction.Lattice.TestsOfAPreparatoryIntegration
import YangMills.Construction.Matrices.HaarExpChartDensity
import YangMills.Construction.PolymerActivities.EffectiveActionOfALabel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CubesOfStep
open Set Filter Topology ParameterChoice
def flowIncrement (x : ℕ → ℝ) (j : ℕ) : ℝ := x (j - 1) - x j
def profileExponent (c : ChoiceUpToDegreeConstants) (x : ℕ → ℝ) (j : ℕ) : ℕ :=
  Nat.log c.L (Thresholds.minBlockSize c.L c.r x j)
section Collar
variable (c : ChoiceUpToDegreeConstants) {m K : ℕ} (x : ℕ → ℝ) {k : ℕ}
  (S : LabelAtLevel c m K x k) (Q : Set (Set (FourTorus c.L m))) (n : ℕ)
def stageInvCoupling : FourTorus c.L m → ℝ :=
  localInverseCoupling K (Nat.log c.L c.M) (x 0) (flowIncrement x) (profileExponent c x)
    (S.stageSmallFieldRegion c.r x Q n) k
def collarWilsonCoeff (y : FourTorus c.L m) : ℝ :=
  stageInvCoupling c x S Q n y - x (stageLevel c x k n)
def stageWilsonCoeff (y : FourTorus c.L m) : ℝ :=
  stageInvCoupling c x S Q (n + 1) y - stageInvCoupling c x S Q n y
def withCollarVariable (V' : BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2)
    (W : AllLevelFields c.L m K) : AllLevelFields c.L m K :=
  Function.update W (stageLevel c x k n)
    (open Classical in fun e =>
      if e ∈ collarFieldBonds c x S Q n then V' e else W (stageLevel c x k n) e)
def collarStageBackground (V' : BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2)
    (W : AllLevelFields c.L m K) : BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2 :=
  S.stageBackgroundField c.εv c.r x Q n (withCollarVariable c x S Q n V' W)
def followingStageBackground (W : AllLevelFields c.L m K) :
    BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2 :=
  S.stageBackgroundField c.εv c.r x Q (n + 1) W
def criticalFields (W : AllLevelFields c.L m K) : AllLevelFields c.L m K :=
  withCollarVariable c x S Q n (stageMean c x S Q n W) W
def collarPath (W : AllLevelFields c.L m K)
    (B : BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2)
    (s : ℝ) : BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2 :=
  let p := stageMean c x S Q n W
  let Γ := collarPositiveBonds c x S Q n
  let A := (s : ℂ) • eliminate p Γ B
  expTwist (A - extendForm (pivotCorrectionLift p Γ (linearizingCorrection p Γ fun e => A e.1))) p
def collarEnergy (W : AllLevelFields c.L m K)
    (V' : BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2) : ℝ :=
  wilsonAction (collarStageBackground c x S Q n V' W) +
    axialGaugeFunction K (stageLevel c x k n) (collarSites c x S Q n (⋃₀ Q)) V'
def collarHessianForm (W : AllLevelFields c.L m K)
    (B : BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2) : ℝ :=
  iteratedDeriv 2 (fun s : ℝ => collarEnergy c x S Q n W (collarPath c x S Q n W B s)) 0
def collarIntegrationBonds : Set (BondAtLevel c.L m K (stageLevel c x k n)) :=
  nonPivotBonds K (stageLevel c x k n) (collarRegion c x S Q n ∩ ⋃₀ Q) \
    bondsMeeting (S.domainSeq (stageLevel c x k n + 1))
def collarEliminationWeight (W : AllLevelFields c.L m K) : ℝ :=
  eliminationWeightProd (stageMean c x S Q n W) (collarPositiveBonds c x S Q n)
def collarLinearTraceLog (W : AllLevelFields c.L m K)
    (B : BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2) : ℂ :=
  traceLogChartJacobian (stageMean c x S Q n W) (collarPositiveBonds c x S Q n)
    fun e => collarEliminated c x S Q n (stageMean c x S Q n W) B e.1
def collarHaarLogDensity (W : AllLevelFields c.L m K)
    (B : BondAtLevel c.L m K (stageLevel c x k n) → Matrices.ComplexMatrix2) : ℝ :=
  ∑ᶠ e ∈ {e : BondAtLevel c.L m K (stageLevel c x k n) |
      e ∈ collarFieldBonds c x S Q n ∧ e.IsPositivelyOriented},
    Real.log (Matrices.ComplexMatrix2.haarExpDensity
        (collarTwistForm c x S Q n (stageMean c x S Q n W) B e) /
      Matrices.ComplexMatrix2.haarChartDensity)
def collarScaleConstant : ℝ :=
  (Real.log Matrices.ComplexMatrix2.haarChartDensity -
      (1 / 2) * (Matrices.ComplexMatrix2.realLieDimension : ℝ) * Real.log (x (stageLevel c x k n))) *
    ({e : BondAtLevel c.L m K (stageLevel c x k n) |
      e ∈ collarIntegrationBonds c x S Q n ∧ e.IsPositivelyOriented}.ncard : ℝ)
end Collar
section Stage
variable (T : DerivedConstants) (a : FullChoice) {m K : ℕ} (x : ℕ → ℝ) {E : ℕ → Type}
  {k : ℕ}
abbrev radiiChoice : ChoiceUpToRadii :=
  a.toChoiceUpToRadii
abbrev degreeChoice : ChoiceUpToDegreeConstants :=
  (radiiChoice a).toChoiceUpToDegreeConstants
abbrev LocalizedStageTerms {L m K k : ℕ} (𝔅 : StoredBonds L m K k) : Type :=
  ℕ → Set (FourTorus L m) → (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) → 𝔅.FieldSystem → ℂ
inductive StageActionVariant where
  | original
  | withWilsonTerm
variable (S : LabelAtLevel (degreeChoice a) m K x k)
  {𝔅 : StoredBonds a.L m K k} (D : AnalyticityConstants.EffectiveActionData a.L m K 𝔅)
  (Qs : ℕ → Set (Set (FourTorus a.L m))) (C : LocalizedStageTerms 𝔅)
def actionTermsSum (U : BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2) (𝔣 : 𝔅.FieldSystem) : ℂ :=
  (AnalyticityConstants.ofChoice T a).regularPart (flowIncrement x)
      (profileExponent (degreeChoice a) x) S D U +
    (AnalyticityConstants.ofChoice T a).remainderPart (profileExponent (degreeChoice a) x) S D U +
    (AnalyticityConstants.ofChoice T a).boundaryPart S D U 𝔣
def baseAction (U : BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2) (𝔣 : 𝔅.FieldSystem) : ℂ :=
  (AnalyticityConstants.ofChoice T a).effectiveAction (x 0) (flowIncrement x)
    (profileExponent (degreeChoice a) x) S D U 𝔣
def IsStageTermDomain (Q : Set (Set (FourTorus a.L m))) (n : ℕ) (X : Set (FourTorus a.L m)) : Prop :=
  (AnalyticityConstants.ofChoice T a).IsStageLocalizationDomain a.r x S (n + 1) X ∧
    (X ∩ S.collarRegion a.r x Q n).Nonempty
def localizedTermsSum (n : ℕ) (U : BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2)
    (𝔣 : 𝔅.FieldSystem) : ℂ :=
  ∑ᶠ X ∈ {X | IsStageTermDomain T a x S (Qs n) n X}, C (n + 1) X U 𝔣
def stageTermsSum : ℕ → (BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2) → 𝔅.FieldSystem → ℂ
  | 0, _, _ => 0
  | n + 1, U, 𝔣 => stageTermsSum n U 𝔣 + localizedTermsSum T a x S Qs C n U 𝔣
def stageConstantsSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    stepScalingGaugeConstant a.A₀ a.𝔭₀ x K (stageLevel (degreeChoice a) x k i)
      (collarRegion (degreeChoice a) x S (Qs i) i ∩ ⋃₀ Qs i)
def stageActionAt (φ : StageActionVariant) (n : ℕ) (U : BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2)
    (𝔣 : 𝔅.FieldSystem) : ℂ :=
  match φ with
  | .original => baseAction T a x S D U 𝔣 + stageTermsSum T a x S Qs C n U 𝔣
  | .withWilsonTerm =>
    -variableCouplingEnergy (stageInvCoupling (degreeChoice a) x S (Qs n) n) U +
      actionTermsSum T a x S D U 𝔣 + stageTermsSum T a x S Qs C n U 𝔣 - D.vacuumEnergy +
      ((stageConstantsSum a x S Qs n : ℝ) : ℂ)
def stageFluctBonds (Q : Set (Set (FourTorus a.L m))) (n : ℕ) (W : AllLevelFields a.L m K) :
    Set (BondAtLevel a.L m K (stageLevel (degreeChoice a) x k n)) :=
  fluctuationBondsWithin (degreeChoice a) S
    (stepDataOfFields (degreeChoice a) S (stageLevel (degreeChoice a) x k n) W)
    (domainLargeFieldWithin (degreeChoice a) S (stageLevel (degreeChoice a) x k n) (⋃₀ Q))
def storedWithStage (Q : Set (Set (FourTorus a.L m))) (n : ℕ) (W : AllLevelFields a.L m K)
    (A : BondAtLevel a.L m K (stageLevel (degreeChoice a) x k n) → Matrices.ComplexMatrix2)
    (𝔣 : 𝔅.FieldSystem) : 𝔅.FieldSystem :=
  open Classical in
  if hj : stageLevel (degreeChoice a) x k n < k then
    Function.update 𝔣 ⟨stageLevel (degreeChoice a) x k n, hj⟩ fun e =>
      if he : e.1 ∈ stageFluctBonds a x S Q n W ∧
          ((Thresholds.couplingAt x (stageLevel (degreeChoice a) x k n) : ℂ) • A e.1) ∈
            Matrices.ComplexMatrix2.hermitianTraceless
      then ⟨_, he.2⟩
      else 𝔣 ⟨stageLevel (degreeChoice a) x k n, hj⟩ e
  else 𝔣
def storedClearedUpTo (W : AllLevelFields a.L m K) (𝔣 : 𝔅.FieldSystem) :
    ℕ → 𝔅.FieldSystem
  | 0 => 𝔣
  | n + 1 => storedWithStage a x S (Qs n) n W 0 (storedClearedUpTo W 𝔣 n)
variable (n : ℕ) (W : AllLevelFields a.L m K) (𝔣 : 𝔅.FieldSystem)
  (A B : BondAtLevel a.L m K (stageLevel (degreeChoice a) x k n) → Matrices.ComplexMatrix2)
def integrandStored : 𝔅.FieldSystem :=
  storedWithStage a x S (Qs n) n W A (storedClearedUpTo a x S Qs W 𝔣 n)
def integrandBackground : BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2 :=
  collarStageBackground (degreeChoice a) x S (Qs n) n
    (collarSubstitute (degreeChoice a) x S (Qs n) n W B) W
def fluctuationQuadForm (F : AllLevelFields a.L m K) : ℂ :=
  conditionalFormPart (degreeChoice a) S (⋃₀ Qs n)
    (stepDataOfFields (degreeChoice a) S (stageLevel (degreeChoice a) x k n) F)
    (stepBasePoints (radiiChoice a) (stageLevel (degreeChoice a) x k n)
      (stepDataOfFields (degreeChoice a) S (stageLevel (degreeChoice a) x k n) F)) A
def stageEliminationWeight (F : AllLevelFields a.L m K) : ℝ :=
  eliminationWeightProd
    (backgroundField (degreeChoice a)
      (stepDataOfFields (degreeChoice a) S (stageLevel (degreeChoice a) x k n) F))
    (eliminatedBonds (degreeChoice a) S (stageLevel (degreeChoice a) x k n) (⋃₀ Qs n))
def collarBraceTerm : ℂ :=
  let U := integrandBackground a x S Qs n W B
  let U₁ := followingStageBackground (degreeChoice a) x S (Qs n) n W
  let 𝔣₁ := integrandStored a x S Qs n W 𝔣 A
  let 𝔣₀ := storedClearedUpTo a x S Qs W 𝔣 (n + 1)
  (actionTermsSum T a x S D U 𝔣₁ + stageTermsSum T a x S Qs C n U 𝔣₁) -
      (actionTermsSum T a x S D U₁ 𝔣₀ + stageTermsSum T a x S Qs C n U₁ 𝔣₀) -
    variableCouplingEnergy (collarWilsonCoeff (degreeChoice a) x S (Qs n) n) U +
    variableCouplingEnergy (collarWilsonCoeff (degreeChoice a) x S (Qs n) n) U₁
def prefactorExponent (φ : StageActionVariant) : ℂ :=
  stageActionAt T a x S D Qs C φ n (followingStageBackground (degreeChoice a) x S (Qs n) n W)
      (storedClearedUpTo a x S Qs W 𝔣 (n + 1)) +
    ((stepScalingGaugeConstant a.A₀ a.𝔭₀ x K (stageLevel (degreeChoice a) x k n)
      (collarRegion (degreeChoice a) x S (Qs n) n ∩ ⋃₀ Qs n) : ℝ) : ℂ)
def collarDensityLog (φ : StageActionVariant) : ℂ :=
  let V' := collarSubstitute (degreeChoice a) x S (Qs n) n W B
  stageActionAt T a x S D Qs C φ n (integrandBackground a x S Qs n W B)
      (integrandStored a x S Qs n W 𝔣 A) +
    ((Real.log (collarGaugeWeight (degreeChoice a) x S (Qs n) n (⋃₀ Qs n)
        (withCollarVariable (degreeChoice a) x S (Qs n) n V' W)) : ℝ) : ℂ) -
    (1 / 2) * fluctuationQuadForm a x S Qs n A (withCollarVariable (degreeChoice a) x S (Qs n) n V' W) +
    ((Real.log (stageEliminationWeight a x S Qs n
        (withCollarVariable (degreeChoice a) x S (Qs n) n V' W)) : ℝ) : ℂ) +
    collarLinearTraceLog (degreeChoice a) x S (Qs n) n W B +
    ((collarHaarLogDensity (degreeChoice a) x S (Qs n) n W B : ℝ) : ℂ) +
    ((collarScaleConstant (degreeChoice a) x S (Qs n) n : ℝ) : ℂ)
def stageInteractionTerm (φ : StageActionVariant) : ℂ :=
  collarDensityLog T a x S D Qs C n W 𝔣 A B φ - prefactorExponent T a x S D Qs C n W 𝔣 φ +
    (1 / 2) * fluctuationQuadForm a x S Qs n A (criticalFields (degreeChoice a) x S (Qs n) n W) +
    (1 / 2) * (collarHessianForm (degreeChoice a) x S (Qs n) n W B : ℂ) -
    collarBraceTerm T a x S D Qs C n W 𝔣 A B
variable (τ : BackgroundVariant) (h : LabelHistory (degreeChoice a) m K x E k)
  (φ : StageActionVariant)
def stageCollarIntegral (hj : stageLevel (degreeChoice a) x k n < k) : ℂ :=
  let F := criticalFields (degreeChoice a) x h.finalLabel (Qs n) n W
  complexPairedSpaceIntegral unitBondInner
    (realBondFormsOn (stageFluctBonds a x h.finalLabel (Qs n) n W)) fun A =>
      ((stageCompletedIndicator (radiiChoice a) x h n (⋃₀ Qs n)
          (fieldsReadFromFluctuation (radiiChoice a) x
            (stepBasePoints (radiiChoice a)) τ h hj (⋃₀ Qs n) F A) : ℝ) : ℂ) *
        Complex.exp (-(1 / 2) * fluctuationQuadForm a x h.finalLabel Qs n A F) *
        ((collarEliminationWeight (degreeChoice a) x h.finalLabel (Qs n) n W : ℝ) : ℂ) *
        complexPairedSpaceIntegral unitBondInner
          (realBondFormsOn (collarIntegrationBonds (degreeChoice a) x h.finalLabel (Qs n) n)) fun B =>
            ((prodOverComponents (degreeChoice a) (Qs n) fun X =>
                collarSmallIndicator (degreeChoice a) x h.finalLabel (Qs n) n X
                  (withCollarVariable (degreeChoice a) x h.finalLabel (Qs n) n
                    (collarSubstitute (degreeChoice a) x h.finalLabel (Qs n) n W B) W) : ℝ) : ℂ) *
              Complex.exp
                (-(1 / 2) * (collarHessianForm (degreeChoice a) x h.finalLabel (Qs n) n W B : ℂ) +
                  stageInteractionTerm T a x h.finalLabel D Qs C n W 𝔣 A B φ +
                  collarBraceTerm T a x h.finalLabel D Qs C n W 𝔣 A B)
def stageTermWilson (S : LabelAtLevel (degreeChoice a) m K x k) : ℂ :=
  variableCouplingEnergy (stageWilsonCoeff (degreeChoice a) x S (Qs n) n)
    (followingStageBackground (degreeChoice a) x S (Qs n) n W)
def IsStageTermValue (hj : stageLevel (degreeChoice a) x k n < k) (v : ℂ) : Prop :=
  Complex.exp (v - stageTermWilson a x Qs n W h.finalLabel) =
    stageCollarIntegral T a x D Qs C n W 𝔣 τ h φ hj
omit W 𝔣 in
def StageTermsAreLocal : Prop :=
  ∀ X, IsStageTermDomain T a x S (Qs n) n X →
    ∀ (U U' : BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2) (𝔤 𝔤' : 𝔅.FieldSystem),
      restrictPairTo X (configurationPair k U) = restrictPairTo X (configurationPair k U') →
      𝔅.restrictNear X 𝔤 = 𝔅.restrictNear X 𝔤' →
      C (n + 1) X U 𝔤 = C (n + 1) X U' 𝔤'
omit W 𝔣 in
def IsStageLocalization (F : Set (AllLevelFields a.L m K × 𝔅.FieldSystem))
    (hj : stageLevel (degreeChoice a) x k n < k) : Prop :=
  StageTermsAreLocal T a x h.finalLabel Qs C n ∧
    ∀ q ∈ F, IsStageTermValue T a x D Qs C n q.1 q.2 τ h φ hj
      (localizedTermsSum T a x h.finalLabel Qs C n
        (followingStageBackground (degreeChoice a) x h.finalLabel (Qs n) n q.1)
        (storedClearedUpTo a x h.finalLabel Qs q.1 q.2 (n + 1)))
omit n W 𝔣 in
def IsStagesLocalization (F : ℕ → Set (AllLevelFields a.L m K × 𝔅.FieldSystem)) : Prop :=
  ∀ n (hj : stageLevel (degreeChoice a) x k n < k), n < Thresholds.delayDepth a.L a.r x k →
    IsStageLocalization T a x D Qs C n τ h φ (F n) hj
end Stage
end YangMills.Construction.PeriodicLattice.CubesOfStep
