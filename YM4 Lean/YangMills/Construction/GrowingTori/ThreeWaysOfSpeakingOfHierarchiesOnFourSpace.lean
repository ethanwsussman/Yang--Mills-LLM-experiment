import YangMills.Construction.Continuum.DistributionFormedFromAFamilyOfDistributions
import YangMills.Construction.Continuum.TensorsAboveTheMirrorAndTheirFiniteSequences
import YangMills.Construction.GrowingTori.LinearExtensionToTensorsOfFourSpace
import YangMills.Construction.GrowingTori.TranslationsAndTheTranslationModulus
import YangMills.Construction.TorusOrFourSpace.CentredFunctionalsOnTensors
import YangMills.Construction.TorusOrFourSpace.EvaluationsAtDegenerateArguments
import Mathlib
set_option autoImplicit false
open TopologicalSpace
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open PeriodicSpace TorusTransport.TestFunctionOrders
namespace ToriLimits
abbrev HierarchyEquicontinuous {Y : PeriodicSpace.Params} (Φ : EuclidHierarchy Y)
    (C : BoundFamily) : Prop :=
  Kind.Hierarchy.SatisfiesSepEstimate Φ C
def SatisfiesShiftEstimate (D : Setup) {Y : PeriodicSpace.Params} (C : BoundFamily)
    (Φ : EuclidHierarchy Y) {n : ℕ} (_hn : 2 ≤ n) : Prop :=
  ∀ (f : Kind.sepC1Tuples Y .euclidean n) (R : ℝ) (hR : 0 < R),
    BallSupported R hR f.1 →
    ∀ d : ℝ, Kind.IsGapValue Y .euclidean f.1 d →
    ∀ a b : Fin 4 → ℝ, TorusMetric.euclidNormVec (a - b) ≤ d / 4 →
      |Φ.evalSigma ⟨n, GrowingTori.shiftFamily a f.1⟩ -
          Φ.evalSigma ⟨n, GrowingTori.shiftFamily b f.1⟩| ≤
        C.val n (d / 2) (R + d / 4) *
          ∑ i, D.params.toGrowth.shiftModulus (f.1 i) (TorusMetric.euclidNormVec (a - b)) *
            ∏ l ∈ Finset.univ.erase i, 2 * TestFunctions.sharpNormR4 (D.M : ℝ) (f.1 l)
def openHalfSpace (μ : Fin 4) (c : ℝ) : Opens (Fin 4 → ℝ) where
  carrier := {x | c < x μ}
  is_open' := isOpen_lt continuous_const (continuous_apply μ)
def sepTensorSubmodule (Y : PeriodicSpace.Params) (O : Set (Fin 4 → ℝ)) :
    (q : ℕ) → Submodule ℂ (OrderedTestFun q)
  | 0 => ⊤
  | q + 1 => sepTensorSpanOn Y (q + 1) O
def finiteSeqsAbove (Y : PeriodicSpace.Params) (μ : Fin 4) (c : ℝ) : Submodule ℂ TestFamily where
  carrier := {F | (∀ q, F q ∈ sepTensorSubmodule Y (openHalfSpace μ c : Set (Fin 4 → ℝ)) q) ∧
    ∃ N, ∀ q, N ≤ q → F q = 0}
  add_mem' := by
    rintro F G ⟨hF, N, hN⟩ ⟨hG, N', hN'⟩
    refine ⟨fun q => Submodule.add_mem _ (hF q) (hG q), max N N', fun q hq => ?_⟩
    rw [Pi.add_apply, hN q (le_trans (le_max_left _ _) hq), hN' q (le_trans (le_max_right _ _) hq),
      add_zero]
  zero_mem' := ⟨fun q => Submodule.zero_mem _, 0, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c F ⟨hF, N, hN⟩
    refine ⟨fun q => Submodule.smul_mem _ c (hF q), N, fun q hq => ?_⟩
    rw [Pi.smul_apply, hN q hq, smul_zero]
def thetaReflect (μ : Fin 4) (c : ℝ) (F : TestFamily) : TestFamily :=
  fun _ => CentredTensorMoments.conjReflectTest μ c (F _)
def reflectedTensor (μ : Fin 4) (c : ℝ) (F F' : TestFamily) (q q' : ℕ) : GradedTestFun :=
  gradedTensor ⟨q, thetaReflect μ c F q⟩ ⟨q', F' q'⟩
theorem realTensor_mem_sepTensorSpanOn (Y : PeriodicSpace.Params) {q : ℕ}
    (X : Kind.sepC1Tuples Y .euclidean q) :
    TensorExtension.realTensor Y X.1 ∈ sepTensorSpanOn Y q Set.univ :=
  Submodule.subset_span ⟨X.1, ⟨X.2, fun _ => Set.subset_univ _⟩, rfl⟩
variable {Y : PeriodicSpace.Params}
def IsMomentExtension (Φ : EuclidHierarchy Y) {q : ℕ}
    (T : sepTensorSpanOn Y q Set.univ →ₗ[ℂ] ℂ) : Prop :=
  ∀ X : Kind.sepC1Tuples Y .euclidean q,
    T ⟨_, realTensor_mem_sepTensorSpanOn Y X⟩ = ((Φ.partitionMoment X : ℝ) : ℂ)
def momentExtension (Φ : EuclidHierarchy Y) :
    (q : ℕ) → sepTensorSubmodule Y Set.univ q →ₗ[ℂ] ℂ
  | 0 => ReflectionSpaces.orderZeroMoments ∘ₗ Submodule.subtype _
  | q + 1 => Classical.epsilon (IsMomentExtension Φ (q := q + 1))
open Classical in
def momentExtensionAt (Φ : EuclidHierarchy Y) (A : GradedTestFun) : ℂ :=
  if h : A.2 ∈ sepTensorSubmodule Y Set.univ A.1 then
    momentExtension Φ A.1 ⟨A.2, h⟩
  else 0
def reflectionForm (Φ : EuclidHierarchy Y) (μ : Fin 4) (c : ℝ) (F F' : TestFamily) : ℂ :=
  ∑ᶠ p : ℕ × ℕ, momentExtensionAt Φ (reflectedTensor μ c F F' p.1 p.2)
open Continuum.BlockProducts ReflectionSpaces.Euclidean
def flatCoordinates : (A : GradedTestFun) → Coord (4 * A.1) → ℂ
  | ⟨0, c⟩, _ => c
  | ⟨_ + 1, F⟩, x => F (pointAt x)
def IsOffDiagonalTest (A : GradedTestFun) : Prop :=
  flatCoordinates A ∈ testFunctionSpace (configSpace A.1)
open Classical in
def assembledDistributionAt (u : DistribFamily) : GradedTestFun → ℂ
  | ⟨0, c⟩ => assembledFormZero c
  | ⟨q + 1, F⟩ =>
    if h : IsOffDiagonalTest ⟨q + 1, F⟩ then assembledForm (q + 1) u ⟨_, h⟩ else 0
def ReflectedTensorsSeparated (Y : PeriodicSpace.Params) (μ : Fin 4) (c : ℝ) : Prop :=
  ∀ F ∈ finiteSeqsAbove Y μ c, ∀ F' ∈ finiteSeqsAbove Y μ c, ∀ q q' : ℕ,
    (reflectedTensor μ c F F' q q').2 ∈
      sepTensorSubmodule Y Set.univ (reflectedTensor μ c F F' q q').1
def ReflectionFormPositive (Φ : EuclidHierarchy Y) (μ : Fin 4) (c : ℝ) : Prop :=
  (∀ F ∈ finiteSeqsAbove Y μ c, ∀ G ∈ finiteSeqsAbove Y μ c,
    ∀ H ∈ finiteSeqsAbove Y μ c, ∀ a b : ℂ,
      reflectionForm Φ μ c F (a • G + b • H) =
        a * reflectionForm Φ μ c F G + b * reflectionForm Φ μ c F H) ∧
  (∀ F ∈ finiteSeqsAbove Y μ c, ∀ G ∈ finiteSeqsAbove Y μ c,
    ∀ H ∈ finiteSeqsAbove Y μ c, ∀ a b : ℂ,
      reflectionForm Φ μ c (a • F + b • G) H =
        conj a * reflectionForm Φ μ c F H + conj b * reflectionForm Φ μ c G H) ∧
  (∀ F ∈ finiteSeqsAbove Y μ c, ∀ F' ∈ finiteSeqsAbove Y μ c,
    reflectionForm Φ μ c F' F = conj (reflectionForm Φ μ c F F')) ∧
  ∀ F ∈ finiteSeqsAbove Y μ c, IsNonnegComplex (reflectionForm Φ μ c F F)
def AssembledDistributionPositive (u : DistribFamily) (μ : Fin 4) (c : ℝ) : Prop :=
  ∀ (q₀ : ℕ) (F : TestFamily),
    (∀ q : ℕ, q + 1 ≤ q₀ → F (q + 1) ∈ Distributions.testFunctionSpace
      (Distributions.offDiagonalPower (openHalfSpace μ c) (q + 1))) →
    (∀ q q' : ℕ, q ≤ q₀ → q' ≤ q₀ → IsOffDiagonalTest (reflectedTensor μ c F F q q')) ∧
    IsNonnegComplex
      (∑ q ∈ Finset.range (q₀ + 1), ∑ q' ∈ Finset.range (q₀ + 1),
        assembledDistributionAt u (reflectedTensor μ c F F q q'))
def ReflectionPositiveAt (Φ : EuclidHierarchy Y) (u : DistribFamily) (μ : Fin 4) (c : ℝ) :
    Prop :=
  ReflectedTensorsSeparated Y μ c ∧ ReflectionFormPositive Φ μ c ∧
    AssembledDistributionPositive u μ c
end ToriLimits
end YangMills.Construction
end
