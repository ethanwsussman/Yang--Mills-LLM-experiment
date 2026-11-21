import YangMills.Construction.FamiliesOfLimits.EveryFamilyOfLimitsIsALimitAlongGrowingVolumes
import YangMills.Construction.FamiliesOfLimits.HilbertSpaceOnTuples
import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes
import YangMills.Construction.Torus.MirrorsAtRealPositionsAndReflectionPositivityOfAMapOnTuples
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open AmbientPoints ToriLimits ToriLimits.GrowingVolumeLimits
open TorusTransport.TestFunctionOrders
namespace FamiliesOfLimits.CoordinateMirrorPositivity
abbrev axisMirror (μ : Fin 4) (c : ℝ) : AmbientMirror .euclidean :=
  AmbientMirror.ofAxisLevel .euclidean μ c
abbrev PositiveSideTuples (s : Conventions.StandingParameters) (μ : Fin 4) (c : ℝ) : Type :=
  ↥(AmbientMirror.separatedIn (AmbientMirror.positiveSide s .euclidean (axisMirror μ c)))
variable {s : Conventions.StandingParameters}
def tensorSeq (X : FunctionTuple s .euclidean) : TestFamily :=
  Pi.single X.1 (CentredTensorMoments.realTupleTensor X.2)
def combinationSeq {r : ℕ} (X : Fin r → FunctionTuple s .euclidean) (a : Fin r → ℂ) :
    TestFamily :=
  fun q => ∑ i with (X i).1 = q, a i • tensorSeq (X i) q
structure ExpansionsHold {Y : PeriodicSpace.Params} (Ξ : EuclidHierarchy Y)
    (σ : allSeparatedTuples s .euclidean → ℝ) (μ : Fin 4) (c : ℝ) {r : ℕ}
    (X : Fin r → PositiveSideTuples s μ c) (a : Fin r → ℂ) : Prop where
  reflected_eq : ∀ q, thetaReflect μ c (combinationSeq (fun i => (X i).1) a) q =
    ∑ i with (X i).1.1 = q, conj (a i) •
      tensorSeq (AmbientMirror.reflectTuple s .euclidean (axisMirror μ c) (X i).1) q
  tensor_eq : ∀ q q', reflectedTensor μ c (combinationSeq (fun i => (X i).1) a)
      (combinationSeq (fun i => (X i).1) a) q q' =
    ⟨q + q', ∑ i with (X i).1.1 = q, ∑ k with (X k).1.1 = q', (conj (a i) * a k) •
      tensorSeq (AmbientMirror.reflectAppend s .euclidean (axisMirror μ c) (X i) (X k)).1
        (q + q')⟩
  sum_eq : reflectionForm Ξ μ c (combinationSeq (fun i => (X i).1) a)
      (combinationSeq (fun i => (X i).1) a) =
    AmbientMirror.gramSum s .euclidean (axisMirror μ c) σ X a
  sum_nonneg : PeriodicSpace.IsNonnegComplex
    (AmbientMirror.gramSum s .euclidean (axisMirror μ c) σ X a)
def Holds : Prop :=
  ∀ (D : Setup) (T : ToriSequence D) (C : PeriodicSpace.BoundFamily)
    (J : Sequences.PNatIndexSet) (Ξ : D.LimitHierarchy), LimitRequirements T C J Ξ →
    ∀ (s : Conventions.StandingParameters) (S : SeparatedTupleFunctions s),
      LimitFamilyAsVolumeLimit.HierarchyAgrees Ξ S →
        (∀ (X : allSeparatedTuples s .euclidean)
          (hX : X.1.2 ∈ PeriodicSpace.Kind.sepC1Tuples D.euclidParams .euclidean X.1.1),
          Ξ.partitionMoment ⟨X.1.2, hX⟩ = TupleHilbert.centredMap S X) ∧
        (∀ q : ℕ, 1 ≤ q → ∃! T, IsMomentExtension Ξ (q := q) T) ∧
        (∀ q : ℕ, IsMomentExtension Ξ (momentExtension Ξ (q + 1))) ∧
        ∀ (μ : Fin 4) (c : ℝ),
          (∀ (r : ℕ) (X : Fin r → PositiveSideTuples s μ c) (a : Fin r → ℂ),
            ExpansionsHold Ξ (TupleHilbert.centredMap S) μ c X a) ∧
          AmbientMirror.IsReflectionPositive s .euclidean (axisMirror μ c)
            (TupleHilbert.centredMap S)
end FamiliesOfLimits.CoordinateMirrorPositivity
end YangMills.Construction
end
