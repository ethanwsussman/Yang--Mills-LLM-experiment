import YangMills.Construction.MinkowskiSpace.ConditionsOnAFunctionalForAFieldForm
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction
namespace TimeTranslations
open ProjectionMeasures OneLoopNotation PVMCalculus FieldForms FieldFormConditions
  SeparatedTuples ReflectionPositivity.TupleForm ReflectionPositivity.FormProperties
def subConeSet : FourBorelSet :=
  ⟨{p | p 0 < MinkowskiSpace.spaceNorm (MinkowskiSpace.spacePart p)},
    (isOpen_lt (continuous_apply 0)
      (by unfold MinkowskiSpace.spaceNorm MinkowskiSpace.spacePart; fun_prop)).measurableSet⟩
def laplaceFourierKernel (t : ℝ) (v : Fin 3 → ℝ) (p : Fin 4 → ℝ) : ℂ :=
  Complex.exp (-(t : ℂ) * (p 0 : ℂ) +
    Complex.I * ((∑ i, v i * MinkowskiSpace.spacePart p i : ℝ) : ℂ))
def timeSpaceVec (t : ℝ) (v : Fin 3 → ℝ) : Fin 4 → ℝ :=
  t • timeUnitVec + ![v 0, v 1, v 2, 0]
def flipSpace (p : Fin 4 → ℝ) : Fin 4 → ℝ :=
  MinkowskiSpace.mkTimeSpace (p 0) (-MinkowskiSpace.spacePart p)
theorem measurable_flipSpace : Measurable flipSpace := by
  refine measurable_pi_lambda _ fun μ => ?_
  refine Fin.cases ?_ (fun i => ?_) μ
  · exact measurable_pi_apply 0
  · exact (measurable_pi_apply i.succ).neg
variable (sigma : TestSpaces.SepTuple → ℝ)
def IntertwinesShifts (P : FourBorelSet → BddOp (StateSpace sigma)) : Prop :=
  ∀ (F : PositiveSpan) (t : ℝ) (v : Fin 3 → ℝ), 0 ≤ t →
    pvmIntegral P (MinkowskiSpace.closedFutureCone.indicator (laplaceFourierKernel t v))
        (stateOf sigma F) =
      stateOf sigma (shiftedSpan (timeSpaceVec t v) F)
def PushforwardIsTranslationMeasure : Prop :=
  ∀ P : FourBorelSet → BddOp (StateSpace sigma), IsPVM P →
    P subConeSet = 0 → IntertwinesShifts sigma P →
      IsTranslationMeasure sigma (pushforward P flipSpace measurable_flipSpace)
def FixedIffOriginFixed : Prop :=
  ∀ E : FourBorelSet → BddOp (StateSpace sigma), IsTranslationMeasure sigma E →
    (∀ χ : StateSpace sigma,
      ((∀ t : ℝ, 0 ≤ t → spectralTranslation E (imagTimeShift t) χ = χ) ↔
          ∃ t : ℝ, 0 < t ∧ spectralTranslation E (imagTimeShift t) χ = χ) ∧
        ((∃ t : ℝ, 0 < t ∧ spectralTranslation E (imagTimeShift t) χ = χ) ↔
          E originBorel χ = χ)) ∧
    ∀ χ : StateSpace sigma,
      Tendsto (fun t : ℝ => spectralTranslation E (imagTimeShift t) χ) atTop
        (𝓝 (E originBorel χ))
def TimeClustering : Prop :=
  ∀ X Y : supportedIn TimeAxis.upperHalfSpace,
    Tendsto
      (fun t : ℝ => sigma (TupleLists.ofList
        (SepTuple.juxt (push TimeAxis.timeReflection X.1) (push (translate (t • timeUnitVec)) Y.1))))
      atTop
      (𝓝 (sigma (TupleLists.ofList (push TimeAxis.timeReflection X.1)) *
        sigma (TupleLists.ofList Y.1)))
def ClusteringUniqueVacuum : Prop :=
  ∀ E : FourBorelSet → BddOp (StateSpace sigma), IsTranslationMeasure sigma E →
    TimeClustering sigma →
      (∀ χ : StateSpace sigma, E originBorel χ = inner ℂ (vacuumState sigma) χ • vacuumState sigma) ∧
        ∀ χ : StateSpace sigma,
          (∀ t : ℝ, 0 ≤ t → spectralTranslation E (imagTimeShift t) χ = χ) →
            ∃ c : ℂ, χ = c • vacuumState sigma
end TimeTranslations
open TimeTranslations in
def TimeTranslations.MeasureAndFixedVectors : Prop :=
  ∀ sigma : TestSpaces.SepTuple → ℝ, TestSpaces.IsSepFunctional sigma →
    FieldFormConditions.PairingPosSemidef sigma →
      PushforwardIsTranslationMeasure sigma ∧ FixedIffOriginFixed sigma ∧
        ClusteringUniqueVacuum sigma
end YangMills.Construction
end
