import YangMills.Construction.Continuum.IsometriesOfFourSpaceAndOfATorusReflectionsAndInducedMaps
import YangMills.Construction.GrowingTori.TuplesClassesAndAdmissibleFamiliesOfFourSpace
import YangMills.Construction.ReflectionPositivity.SharpNormAndModulusOfAFunctionOfClassC1
import Mathlib
set_option autoImplicit false
open scoped ENNReal NNReal ContDiff Topology
open YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient (ScaleParam compactC1 gradOsc
  gradSup smoothModulus normSharp)
open YangMills.Construction.TorusTransport (IsEuclideanMotion hyperoctahedral orthoAffine
  hyperplaneReflect timeReflect familyComp basisVec)
noncomputable section
namespace YangMills.Construction.ToriLimits
def transportDataAt (D : ReflectionPositivity.AxisMirror.MirrorData) (M : ScaleParam) :
    TorusTransport.TransportData :=
  ⟨D.toStandingParameters, M.1, M.2⟩
def swapWithTime (μ : Fin 4) : Equiv.Perm (Fin 4 → ℝ) :=
  (Equiv.swap μ 3).arrowCongr (Equiv.refl ℝ)
def toTimeMirrorMotion (μ : Fin 4) (c : ℝ) : Equiv.Perm (Fin 4 → ℝ) :=
  (Equiv.subRight (c • basisVec μ)).trans (swapWithTime μ)
def SmoothModulusMonoTendsZero {D : ReflectionPositivity.AxisMirror.MirrorData} (M : ScaleParam)
    (f : compactC1 D ℝ .euclidean) : Prop :=
  Monotone (smoothModulus M f) ∧ Filter.Tendsto (smoothModulus M f) (𝓝[>] 0) (𝓝 0)
def NormSharpTranslateBound (D : ReflectionPositivity.AxisMirror.MirrorData) (M : ScaleParam)
    (f : compactC1 D ℝ .euclidean) : Prop :=
  (∀ a b : Fin 4 → ℝ,
    normSharp D M .euclidean
        (TorusTransport.Domain.translateFn (transportDataAt D M) .euclidean a
            (f.1 : (Fin 4 → ℝ) → ℝ) -
          TorusTransport.Domain.translateFn (transportDataAt D M) .euclidean b
            (f.1 : (Fin 4 → ℝ) → ℝ)) ≤
      smoothModulus M f
        (ReflectionPositivity.AxisMirror.Ambient.metric D .euclidean a b).toNNReal) ∧
  ∀ δ : ℝ≥0, smoothModulus M f δ =
    max ((gradSup f).toReal * δ) (40 * (M : ℝ) * (gradOsc f δ).toReal)
def OrthoAffineIsIsometry (D : ReflectionPositivity.AxisMirror.MirrorData)
    (S : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) : Prop :=
  ∃ e : Equiv.Perm (Fin 4 → ℝ), ⇑e = orthoAffine S v ∧
    AmbientPoints.IsDistIsometry (s := D.toStandingParameters) (E := .euclidean) e
def OrthoAffinePreservesModulus {D : ReflectionPositivity.AxisMirror.MirrorData} (M : ScaleParam)
    (f : compactC1 D ℝ .euclidean) (S : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) : Prop :=
  ∃ hf : ((f.1 : (Fin 4 → ℝ) → ℝ) ∘ orthoAffine S v) ∈ compactC1 D ℝ .euclidean,
    smoothModulus M ⟨_, hf⟩ = smoothModulus M f
def OrthoAffinePreservesLipschitz (D : ReflectionPositivity.AxisMirror.MirrorData)
    (M : ScaleParam) (S : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) : Prop :=
  ∀ g : RealFn, LipschitzR4 g → IsCompact (fnSupport g) →
    fnSupport (g ∘ orthoAffine S v) = orthoAffine S v ⁻¹' fnSupport g ∧
    TestFunctions.uniformNorm (g ∘ orthoAffine S v) = TestFunctions.uniformNorm g ∧
    lipConst (g ∘ orthoAffine S v) = lipConst g ∧
    normSharp D M .euclidean (g ∘ orthoAffine S v) = normSharp D M .euclidean g ∧
    (ContDiff ℝ 1 g → ContDiff ℝ 1 (g ∘ orthoAffine S v)) ∧
    (ContDiff ℝ ∞ g → ContDiff ℝ ∞ (g ∘ orthoAffine S v))
def OrthoAffinePreservesAdmissible (D : ReflectionPositivity.AxisMirror.MirrorData)
    (S : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) : Prop :=
  ∀ (q : ℕ) (hq : 1 ≤ q) (d R : ℝ) (hd : 0 < d) (hR : 0 < R) (A : Fin q → Set (Fin 4 → ℝ)),
    AdmissibleSets hq d R hd hR A →
      AdmissibleSets hq d R hd hR (fun l => orthoAffine S v ⁻¹' A l) ∧
      (fun g : Fin q → RealFn => familyComp g (orthoAffine S v)) ''
          Set.univ.pi (fun l => c1SuppIn D.toStandingParameters (A l)) =
        Set.univ.pi (fun l => c1SuppIn D.toStandingParameters (orthoAffine S v ⁻¹' A l))
def OrthoAffinePreservesSepTuples (D : ReflectionPositivity.AxisMirror.MirrorData)
    (S : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) : Prop :=
  (∀ n : ℕ,
    (fun g : Fin n → RealFn => familyComp g (orthoAffine S v)) ''
        sepTuplesR4 D.toStandingParameters n =
      sepTuplesR4 D.toStandingParameters n) ∧
  ∀ (n : ℕ) (hn : 2 ≤ n) (g : Fin n → RealFn),
    g ∈ sepTuplesR4 D.toStandingParameters n →
      ∃ (hg : IsSepLipTuple g) (hs : IsSepLipTuple (familyComp g (orthoAffine S v))),
        minSuppGap hn (familyComp g (orthoAffine S v)) hs = minSuppGap hn g hg
def ParallelReflectTranslate (D : ReflectionPositivity.AxisMirror.MirrorData) (M : ScaleParam)
    (μ : Fin 4) (c c' : ℝ) : Prop :=
  ∀ (Z : Type) [Zero Z] (g : (Fin 4 → ℝ) → Z),
    g ∘ hyperplaneReflect μ c' =
        TorusTransport.Domain.translateFn (transportDataAt D M) .euclidean
          ((2 * (c' - c)) • basisVec μ) (g ∘ hyperplaneReflect μ c) ∧
      fnSupport (g ∘ hyperplaneReflect μ c') =
        (fun y => y + (2 * (c' - c)) • basisVec μ) '' (hyperplaneReflect μ c '' fnSupport g)
def ParallelReflectNormSharpBound {D : ReflectionPositivity.AxisMirror.MirrorData}
    (M : ScaleParam) (f : compactC1 D ℝ .euclidean) (μ : Fin 4) (c c' : ℝ) : Prop :=
  normSharp D M .euclidean
      ((f.1 : (Fin 4 → ℝ) → ℝ) ∘ hyperplaneReflect μ c' -
        (f.1 : (Fin 4 → ℝ) → ℝ) ∘ hyperplaneReflect μ c) ≤
    smoothModulus M f (2 * |c' - c|).toNNReal
def ConjugatesToTimeReflect (μ : Fin 4) (c : ℝ) : Prop :=
  swapWithTime μ ∈ hyperoctahedral ∧
    toTimeMirrorMotion μ c ∈ TorusPeriodization.euclideanMotions ∧
    toTimeMirrorMotion μ c '' {x | c < x μ} = {x | 0 < x 3} ∧
    toTimeMirrorMotion μ c ∘ hyperplaneReflect μ c = timeReflect ∘ toTimeMirrorMotion μ c ∧
    hyperplaneReflect μ c ∘ (toTimeMirrorMotion μ c).symm =
      (toTimeMirrorMotion μ c).symm ∘ timeReflect
def EuclideanSymmetryFacts.Statement : Prop :=
  ∀ (D : ReflectionPositivity.AxisMirror.MirrorData) (M : ScaleParam),
    (∀ f : compactC1 D ℝ .euclidean,
      SmoothModulusMonoTendsZero M f ∧
      NormSharpTranslateBound D M f ∧
      (∀ S ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∀ v, OrthoAffinePreservesModulus M f S v) ∧
      ∀ (μ : Fin 4) (c c' : ℝ), ParallelReflectNormSharpBound M f μ c c') ∧
    (∀ s ∈ TorusPeriodization.euclideanMotions, IsEuclideanMotion ⇑s) ∧
    (∀ S ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∀ v : Fin 4 → ℝ,
      OrthoAffineIsIsometry D S v ∧
      OrthoAffinePreservesLipschitz D M S v ∧
      OrthoAffinePreservesAdmissible D S v ∧
      OrthoAffinePreservesSepTuples D S v) ∧
    (∀ (μ : Fin 4) (c c' : ℝ), ParallelReflectTranslate D M μ c c') ∧
    ∀ (μ : Fin 4) (c : ℝ), ConjugatesToTimeReflect μ c
end YangMills.Construction.ToriLimits
end
