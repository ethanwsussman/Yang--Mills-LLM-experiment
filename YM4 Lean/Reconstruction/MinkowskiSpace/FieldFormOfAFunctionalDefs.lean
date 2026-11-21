import Reconstruction.Continuum.KernelsThatGiveBackAFunctionFromItsThirdDerivatives
import YangMills.Construction.MinkowskiSpace.ConditionsOnAFunctionalForAFieldForm
import Reconstruction.MinkowskiSpace.SchwingerFunctionsOfAEuclideanFieldForm
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.InsertedFieldForm
open SeparatedTuples ReflectionPositivity.TupleForm ReflectionPositivity.FormProperties
  FieldFormConditions ProjectionMeasures HilbertToolkit OneLoopNotation MinkowskiSpace FieldForms
variable (sigma : TestSpaces.SepTuple → ℝ)
def realWickPoint (a : Fin 4 → ℝ) : ComplexVec4 := wickMap (toComplex a)
def insertionDensity (E : FourBorelSet → BddOp (StateSpace sigma))
    (A : ℝ → BddOp (StateSpace sigma)) (c s : ℝ) (χ : StateSpace sigma) (y : Fin 4 → ℝ) :
    StateSpace sigma :=
  (spectralTranslation E (realWickPoint (y - s • timeUnitVec)) * A s *
    spectralTranslation E (realWickPoint ((c - s) • timeUnitVec - y))) χ
def HasInsertionIntegral (E : FourBorelSet → BddOp (StateSpace sigma))
    (A : ℝ → BddOp (StateSpace sigma)) : Prop :=
  ∀ c s : ℝ, 0 < c → 0 < s → s < c / 2 →
    ∀ h : (Fin 4 → ℝ) → ℂ, h ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) →
      (∀ y ∈ tsupport h, s < y TimeAxis.timeIdx ∧ y TimeAxis.timeIdx < c - s) →
      ∀ F : PositiveSpan,
        ∃ hm : formalMul (WightmanReconstruction.complexTuple h)
            (shiftedSpan (c • timeUnitVec) F).1 ∈ spanIn TimeAxis.upperHalfSpace,
          HasWeakIntegrandData (tsupport h)
              (insertionDensity sigma E A c s (stateOf sigma F)) h ∧
            stateOf sigma ⟨_, hm⟩ =
              weakInt (tsupport h)
                (insertionDensity sigma E A c s (stateOf sigma F)) h
def formExponent (p : ℝ) : ℝ := p + 5
def formConstant (p C : ℝ) : ℝ :=
  (3 : ℝ) ^ (p + 5) * 7 ^ 4 * 8 ^ 5 * CubeKernels.cubeKernelConst * C
def realStateVector (E : FourBorelSet → BddOp (StateSpace sigma))
    (A : ℝ → BddOp (StateSpace sigma)) (m : ℕ) (x : TestSpaces.PointTuple (m + 1)) :
    StateSpace sigma :=
  stateVector E (vacuumState sigma) A (m + 1) (wickMapTuple (tupleToComplex x))
def HasTimeOrderedIntegral (E : FourBorelSet → BddOp (StateSpace sigma))
    (A : ℝ → BddOp (StateSpace sigma)) : Prop :=
  ∀ (m : ℕ) (X : TestSpaces.SepTupleOfCard (m + 1))
    (hX : TupleLists.toList ⟨m + 1, X⟩ ∈ supportedIn TimeAxis.upperHalfSpace),
    WightmanReconstruction.IsTimeOrdered X.1 →
      HasWeakIntegrandData (tsupport (TestSpaces.tensorProdComplex X.1))
          (realStateVector sigma E A m) (TestSpaces.tensorProdComplex X.1) ∧
        stateOf sigma (spanBasisIn TimeAxis.upperHalfSpace ⟨_, hX⟩) =
          weakInt (tsupport (TestSpaces.tensorProdComplex X.1))
            (realStateVector sigma E A m) (TestSpaces.tensorProdComplex X.1)
def RepresentsEuclideanSchwinger (E : FourBorelSet → BddOp (StateSpace sigma))
    (A : ℝ → BddOp (StateSpace sigma)) : Prop :=
  RepresentsFunctional E (vacuumState sigma) A sigma ∧ IsEuclidean E (vacuumState sigma) A ∧
    ∀ (m : ℕ) (X : TestSpaces.SepTupleOfCard (m + 1)),
      ((sigma ⟨m + 1, X⟩ : ℝ) : ℂ) =
        integralSchwinger E (vacuumState sigma) A m (TestSpaces.tensorProdComplex X.1)
structure Hypotheses (E : FourBorelSet → BddOp (StateSpace sigma)) (p C : ℝ) : Prop where
  isSepFunctional : TestSpaces.IsSepFunctional sigma
  symmInvariant : IsSymmetricInvariant sigma
  posSemidef : PairingPosSemidef sigma
  translationMeasure : IsTranslationMeasure sigma E
  exponent_nonneg : 0 ≤ p
  one_le_const : 1 ≤ C
  insertion_bound : InsertionBound sigma p C
def translateFun (a : Fin 4 → ℝ) (f : (Fin 4 → ℝ) → ℂ) : (Fin 4 → ℝ) → ℂ := fun x => f (x - a)
open Classical in
def insertedState (f : (Fin 4 → ℝ) → ℂ) (v : Fin 4 → ℝ) (F : PositiveSpan) :
    StateSpace sigma :=
  if h : formalMul (WightmanReconstruction.complexTuple f) (shiftedSpan v F).1 ∈
      spanIn TimeAxis.upperHalfSpace then stateOf sigma ⟨_, h⟩ else 0
structure IsAdmissible (η : ℝ) (f : (Fin 4 → ℝ) → ℂ) : Prop where
  mem : f ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))
  tsupport_time : ∀ x ∈ tsupport f, η ≤ x TimeAxis.timeIdx ∧ x TimeAxis.timeIdx ≤ 3 * η
  diam_le : ∀ x ∈ tsupport f, ∀ y ∈ tsupport f, TorusMetric.euclidNormVec (x - y) ≤ 1
def IsInsertionOp (η : ℝ) (f : (Fin 4 → ℝ) → ℂ) (a : BddOp (StateSpace sigma)) : Prop :=
  ∀ F : PositiveSpan,
    a (stateOf sigma F) = insertedState sigma f ((4 * η) • timeUnitVec) F
def insertionOp (η : ℝ) (f : (Fin 4 → ℝ) → ℂ) : BddOp (StateSpace sigma) :=
  Classical.epsilon (IsInsertionOp sigma η f)
def scaledKernel (η : ℝ) (Γ : Finset (Fin 4)) : (Fin 4 → ℝ) → ℂ :=
  fun x => (CubeKernels.cubeKernel Γ (η / 8) x : ℂ)
def kernelInsertion (η : ℝ) (Γ : Finset (Fin 4)) : BddOp (StateSpace sigma) :=
  insertionOp sigma η (translateFun ((2 * η) • timeUnitVec) (scaledKernel η Γ))
def conjKernelInsertion (E : FourBorelSet → BddOp (StateSpace sigma)) (η : ℝ)
    (Γ : Finset (Fin 4)) (a : Fin 4 → ℝ) : BddOp (StateSpace sigma) :=
  spectralTranslation E (realWickPoint (η • timeUnitVec + a)) * kernelInsertion sigma η Γ *
    spectralTranslation E (realWickPoint (η • timeUnitVec - a))
def smoothedPairing (E : FourBorelSet → BddOp (StateSpace sigma)) (η : ℝ)
    (a : Fin 4 → ℝ) (χ χ' : StateSpace sigma) : ℂ :=
  ∑ Γ : Finset (Fin 4), (-1 : ℂ) ^ Γ.card *
    CubeKernels.cubedPartial Γ
      (fun a' => ⟪χ, conjKernelInsertion sigma E η Γ a' χ'⟫_ℂ) a
def smoothedFieldOp (E : FourBorelSet → BddOp (StateSpace sigma)) (η : ℝ) (a : Fin 4 → ℝ) :
    BddOp (StateSpace sigma) :=
  Classical.epsilon (RepresentsForm fun χ χ' => smoothedPairing sigma E η a χ χ')
def smoothedFieldConst (C : ℝ) : ℝ :=
  7 ^ 4 * 8 ^ 5 * CubeKernels.cubeKernelConst * C
def centralBox (η : ℝ) : Set (Fin 4 → ℝ) :=
  {a | |a TimeAxis.timeIdx| < η / 4 ∧ TorusMetric.euclidNormVec a < 1 / 4}
def timeSlab (c : ℝ) : Set (Fin 4 → ℝ) :=
  {y | 0 < y TimeAxis.timeIdx ∧ y TimeAxis.timeIdx < c}
structure IsFieldDensity (E : FourBorelSet → BddOp (StateSpace sigma))
    (G : ℝ → (Fin 4 → ℝ) → BddOp (StateSpace sigma)) : Prop where
  continuousOn_inner : ∀ (c : ℝ) (χ χ' : StateSpace sigma), 0 < c →
    ContinuousOn (fun y => ⟪χ, G c y χ'⟫_ℂ) (timeSlab c)
  eq_conj : ∀ (c η : ℝ) (y : Fin 4 → ℝ), 0 < η → η ≤ 1 → 3 * η ≤ y TimeAxis.timeIdx →
    3 * η ≤ c - y TimeAxis.timeIdx →
      G c y = spectralTranslation E (realWickPoint (y - (3 * η) • timeUnitVec)) *
        smoothedFieldOp sigma E η 0 *
          spectralTranslation E (realWickPoint ((c - 3 * η) • timeUnitVec - y))
  inner_insertedState : ∀ (c : ℝ) (h : (Fin 4 → ℝ) → ℂ) (F : PositiveSpan) (χ : StateSpace sigma),
    0 < c → h ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) → tsupport h ⊆ timeSlab c →
      ⟪χ, insertedState sigma h (c • timeUnitVec) F⟫_ℂ =
        ∫ y in tsupport h, h y * ⟪χ, G c y (stateOf sigma F)⟫_ℂ
def midpointField (G : ℝ → (Fin 4 → ℝ) → BddOp (StateSpace sigma)) (s : ℝ) :
    BddOp (StateSpace sigma) :=
  G (2 * s) (s • timeUnitVec)
end YangMills.Construction.InsertedFieldForm
end
