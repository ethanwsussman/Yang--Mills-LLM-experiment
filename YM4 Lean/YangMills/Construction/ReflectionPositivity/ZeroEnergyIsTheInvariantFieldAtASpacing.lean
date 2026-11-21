import YangMills.Construction.ReflectionPositivity.OneLatticeAtEverySpacing
import YangMills.Construction.ReflectionPositivity.PicturesCubeVectorsAndReflectionSizesAtASpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField LatticePoint IsBoundedObservable IsLocalObservable
  regionObservables closedHalfSpace axisStep shift shiftInvariantSigma condExpShiftInvariant)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet coordinateReflect)
def IsStepInvariantSet (a : ℝ) (μ : Fin 4) (I : Set (GaugeField a)) : Prop :=
  MeasurableSet I ∧
    (shift (axisStep a μ)).actOn (I.indicator (1 : GaugeField a → ℂ)) = I.indicator 1
@[reducible] def axisStepInvariantSigma (a : ℝ) (μ : Fin 4) : MeasurableSpace (GaugeField a) where
  MeasurableSet' := IsStepInvariantSet a μ
  measurableSet_empty := ⟨MeasurableSet.empty,
    ((shift (axisStep a μ)).actOn_indicator_eq_iff ∅).mpr rfl⟩
  measurableSet_compl E hE := ⟨hE.1.compl,
    ((shift (axisStep a μ)).actOn_indicator_eq_iff Eᶜ).mpr (by
      rw [Set.preimage_compl,
        ((shift (axisStep a μ)).actOn_indicator_eq_iff E).mp hE.2])⟩
  measurableSet_iUnion g hg := ⟨MeasurableSet.iUnion fun k => (hg k).1,
    ((shift (axisStep a μ)).actOn_indicator_eq_iff (⋃ k, g k)).mpr (by
      rw [Set.preimage_iUnion]
      exact Set.iUnion_congr fun k =>
        ((shift (axisStep a μ)).actOn_indicator_eq_iff (g k)).mp (hg k).2)⟩
def GroundStatesShiftInvariantAtMesh : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (ν : BorelProb a), ν ∈ reflectionPositiveSet a → ∀ μ : Fin 4,
    (∀ F H : GaugeField a → ℂ,
      IsLocalObservable F → F ∈ regionObservables a (closedHalfSpace μ) →
      IsLocalObservable H → H ∈ regionObservables a (closedHalfSpace μ) →
      inner ℂ (ScaledPair.obsClass ν.1 μ ha F)
          (ScaledPair.groundProjection ν.1 μ
            (ScaledPair.obsClass ν.1 μ ha H)) =
        ∫ U, conj (condExpShiftInvariant ν.1 F U) * condExpShiftInvariant ν.1 H U ∂ν.1) ∧
    (∀ G : GaugeField a → ℂ, IsBoundedObservable G → ∀ v : LatticePoint a,
      condExpShiftInvariant ν.1 ((coordinateReflect a μ).actOn G) =ᵐ[ν.1]
          condExpShiftInvariant ν.1 G ∧
        condExpShiftInvariant ν.1 G =ᵐ[ν.1]
          condExpShiftInvariant ν.1 ((shift v).actOn G)) ∧
    shiftInvariantSigma a ≤ axisStepInvariantSigma a μ ∧
    (∀ E : Set (GaugeField a), MeasurableSet[axisStepInvariantSigma a μ] E →
      ∃ E' : Set (GaugeField a), MeasurableSet[shiftInvariantSigma a] E' ∧
        ν.1 (symmDiff E E') = 0) ∧
    (∀ J : GaugeField a → ℂ, IsBoundedObservable J →
      (shift (axisStep a μ)).actOn J = J →
      ∃ J' : GaugeField a → ℂ, Measurable[shiftInvariantSigma a] J' ∧ J =ᵐ[ν.1] J')
end YangMills.Construction.ReflectionPositivity.DirectionPictures
