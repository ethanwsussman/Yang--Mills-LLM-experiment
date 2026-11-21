import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.ObservablesOnTheClosedSideOfAMirrorAndStates
import YangMills.Construction.InfiniteLattice.SignsOfStatesTuplesAndNormsAtACutoff
import YangMills.Construction.Probability.BoundedRealRandomVariable
import YangMills.Construction.ReflectionPositivity.LipschitzTuplesIsometriesOnFunctionsTensorsAndPartitions
import YangMills.Construction.SourcesAndGluing.SharpNormAgainstC1Norm
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.AtCutoff.SignFacts
open YangMills.Construction.ReflectionPositivity.AxisMirror
def IsLinearSubset {V : Type*} [AddCommGroup V] [Module ℝ V] (A : Set V) : Prop :=
  ∃ W : Submodule ℝ V, (W : Set V) = A
variable (D : MirrorData)
def IsAffineRealization (r : Ambient.IsometryEquiv D .euclidean)
    (w : InfiniteLattice.AmbientSpace ≃ₗ[ℝ] InfiniteLattice.AmbientSpace) (v : Fin 4 → ℝ) : Prop :=
  ∀ x : Fin 4 → ℝ, @Eq (Fin 4 → ℝ) (r.toEquiv x) (w x + v)
def IsometryFacts : Prop :=
  ∀ r : Ambient.IsometryEquiv D .euclidean,
    MetricNotions.IsContinuousWrt (Ambient.metric D .euclidean) (Ambient.metric D .euclidean)
        r.toEquiv ∧
      MetricNotions.IsContinuousWrt (Ambient.metric D .euclidean) (Ambient.metric D .euclidean)
        r.toEquiv.symm ∧
      ∀ (𝕜 : Type) [RCLike 𝕜] (f : Ambient.euclidean.Point D → 𝕜),
        Ambient.closedSupport D .euclidean (r.mapFn f) = r.toEquiv '' Ambient.closedSupport D .euclidean f ∧
          (MetricNotions.IsCompactWrt (Ambient.metric D .euclidean)
              (Ambient.closedSupport D .euclidean f) →
            MetricNotions.IsCompactWrt (Ambient.metric D .euclidean)
              (r.toEquiv '' Ambient.closedSupport D .euclidean f))
def AffineMapFacts : Prop :=
  ∀ w ∈ InfiniteLattice.hyperoctahedralLinearGroup, ∀ v : Fin 4 → ℝ,
    (∃ r : Ambient.IsometryEquiv D .euclidean, IsAffineRealization D r w v) ∧
      ∀ r : Ambient.IsometryEquiv D .euclidean, IsAffineRealization D r w v →
        (∀ f : Ambient.euclidean.Point D → ℝ, Ambient.IsC1 D .euclidean f →
          Ambient.IsC1 D .euclidean (r.mapFn f)) ∧
        ∀ (n : ℕ) (X : Ambient.FnList D .euclidean), X ∈ Ambient.separatedN D .euclidean n →
          r.mapList X ∈ Ambient.separatedN D .euclidean n
def C1ClassFacts (E : Ambient) : Prop :=
  (∀ A : Set (E.Point D), IsLinearSubset (cOneIn D E A)) ∧
    ∀ n : ℕ, 1 ≤ n → ∀ A : Fin n → Set (E.Point D), PairwisePosSeparated D E A →
      ∀ f : Fin n → E.Point D → ℝ, (∀ i, f i ∈ cOneIn D E (A i)) →
        List.ofFn f ∈ Ambient.separatedN D E n
def BoundedLipschitz (E : Ambient) : Prop :=
  ∀ f ∈ cOneIn D E Set.univ,
    TestFunctions.IsBoundedFun f ∧ TestFunctions.IsLipschitzFor (Ambient.metric D E) f
def NormBoundsR4 : Prop :=
  ∀ f : (Fin 4 → ℝ) → ℝ, f ∈ cOneIn D .euclidean Set.univ →
    SourcesAndGluing.HasFiniteC1NormR4 f ∧
      TestFunctions.lipConstR4 f ≤ 2 * TestFunctions.c1NormR4 f ∧
      ∀ M : ℝ, 1 ≤ M → TestFunctions.sharpNormR4 M f ≤ 80 * M * TestFunctions.c1NormR4 f
def SmearedObservableFacts : Prop :=
  IsLinearSubset boundedBorelCompactSupport ∧
    (∀ (A : Set (Fin 4 → ℝ)) (f : (Fin 4 → ℝ) → ℝ), f ∈ cOneIn D .euclidean A →
      f ∈ boundedBorelCompactSupport) ∧
    (∀ f ∈ boundedBorelCompactSupport,
      Probability.IsBoundedRealRV
        fun U : FieldSpace D => InfiniteLattice.smearedEnergy f U) ∧
    ∀ f ∈ boundedBorelCompactSupport, ∀ g ∈ boundedBorelCompactSupport, ∀ s t : ℝ,
      (fun U : FieldSpace D => InfiniteLattice.smearedEnergy (s • f + t • g) U) =
        s • (fun U : FieldSpace D => InfiniteLattice.smearedEnergy f U) +
          t • fun U : FieldSpace D => InfiniteLattice.smearedEnergy g U
def StateConnectedFunctions : Prop :=
  ∀ ν : Measure (FieldSpace D), InfiniteLattice.IsLatticeState ν →
    (∀ n : ℕ, 2 ≤ n → ∀ f : Fin n → InfiniteLattice.AmbientSpace → ℝ,
      (∀ i, f i ∈ boundedBorelCompactSupport) →
        (InfiniteLattice.PeriodicTorusMeasures.measureConnectedFunction ν f).im = 0) ∧
    ∀ (q : ℕ) (h : Fin q → InfiniteLattice.AmbientSpace → ℝ),
      (∀ l, h l ∈ boundedBorelCompactSupport) →
        ((InfiniteLattice.PeriodicTorusMeasures.measureCentredMoment ν (List.ofFn h) : ℝ) : ℂ) =
          connectedPartitionSum ν h
def SignFactsHold : Prop :=
  ∀ D : MirrorData,
    IsometryFacts D ∧ AffineMapFacts D ∧ (∀ E : Ambient, C1ClassFacts D E) ∧
      (∀ E : Ambient, BoundedLipschitz D E) ∧ NormBoundsR4 D ∧ SmearedObservableFacts D ∧
      StateConnectedFunctions D
end YangMills.Construction.AtCutoff.SignFacts
end
