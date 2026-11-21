import Reconstruction.Continuum.RulesOfTheActionsOfMotionsOnFunctionsTuplesAndTensors
import YangMills.Construction.Continuum.TestSpacesAndNormsOfTheAxiomsOnSchwartzFunctions
import YangMills.Construction.Continuum.TranslationsAsMotionsAndSmoothSeparatedTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MotionComposition
open Motions TestSpaces TestFunctionOps SchwartzAxioms SmoothSeparatedTuples HyperplaneReflection
open UpperHalfTensors (compMotion)
open TorusMetric (euclidNormVec)
def translationFactor (n k : ℕ) (v : Fin 4 → ℝ) : ℝ :=
  (2 + 2 * (n : ℝ) * euclidNormVec v ^ 2) ^ ((k : ℝ) / 2)
def tupleComponentFun (X : SeparatedTuples.SepTuple) : Fin X.1.length → SeparatedTuples.RealValued := X.1.get
def IsListOf (Y : SeparatedTuples.SepTuple) {q : ℕ} (f : Fin q → SeparatedTuples.RealValued) : Prop :=
  Y.1 = List.ofFn f
def CompAndTranslationBound (n k : ℕ) (φ : PointTuple n → ℂ) : Prop :=
  (∀ r r' : RigidMotion,
    actOnFun r (actOnFun r' φ) = actOnFun (compMotion r r') φ) ∧
  ∀ v : Fin 4 → ℝ,
    weightedSeminorm k (translateFun v φ) ≤
      ENNReal.ofReal (translationFactor n k v) * weightedSeminorm k φ
def TranslationsPreservePositive (n : ℕ) : Prop :=
  (∀ t : ℝ, 0 ≤ t →
    Set.MapsTo (translateFun (t • timeUnitVector)) (positiveTimeSchwartz n)
      (positiveTimeSchwartz n)) ∧
  ∀ v : Fin 4 → ℝ, TimeAxis.IsPurelySpatial v →
    translateFun v '' positiveTimeSchwartz n = positiveTimeSchwartz n
def ReflectConjTranslations {n : ℕ} (φ : PointTuple n → ℂ) : Prop :=
  (∀ t : ℝ, reflectConj (translateFun (t • timeUnitVector) φ) =
    translateFun ((-t) • timeUnitVector) (reflectConj φ)) ∧
  ∀ v : Fin 4 → ℝ, TimeAxis.IsPurelySpatial v →
    reflectConj (translateFun v φ) = translateFun v (reflectConj φ)
def MotionsDistributeOverTensor : Prop :=
  ∀ (q q' : ℕ) (χ : TensorVal ℂ q) (ψ : TensorVal ℂ q') (r : RigidMotion),
    actOnTensorVal r (tensorVal χ ψ) = tensorVal (actOnTensorVal r χ) (actOnTensorVal r ψ)
def TupleTranslation (X : SeparatedTuples.SepTuple) (w : Fin 4 → ℝ) : Prop :=
  (∃ Y ∈ SeparatedTuples.supportedIn TimeAxis.upperHalfSpace,
    IsListOf Y (translateFamily w (tupleComponentFun X)) ∧
      SeparatedTuples.SepTuple.size Y = SeparatedTuples.SepTuple.size X) ∧
  (X ∈ smoothSupportedIn TimeAxis.upperHalfSpace →
    (∃ Y ∈ smoothSupportedIn TimeAxis.upperHalfSpace,
      IsListOf Y (translateFamily w (tupleComponentFun X))) ∧
    tupleTensor (complexify (translateFamily w (tupleComponentFun X))) =
      translateTensorVal w (tupleTensor (complexify (tupleComponentFun X))))
def CompositionTranslationStatement : Prop :=
  (∀ n k : ℕ, 0 < n → 0 < k → ∀ φ ∈ schwartzSet n, CompAndTranslationBound n k φ) ∧
  (∀ n : ℕ, 0 < n → TranslationsPreservePositive n ∧ ∀ φ ∈ schwartzSet n, ReflectConjTranslations φ) ∧
  MotionsDistributeOverTensor ∧
  ∀ (X : SeparatedTuples.SepTuple) (w : Fin 4 → ℝ), X ∈ SeparatedTuples.supportedIn TimeAxis.upperHalfSpace →
    0 ≤ TimeAxis.timeComponent w → TupleTranslation X w
end YangMills.Construction.MotionComposition
end
