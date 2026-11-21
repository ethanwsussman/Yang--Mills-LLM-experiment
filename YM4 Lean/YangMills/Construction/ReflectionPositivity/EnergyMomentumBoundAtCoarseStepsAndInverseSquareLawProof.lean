import YangMills.Construction.ReflectionPositiveLimits.PeriodicGibbsStatesAndLatticeApproximationsProof
import YangMills.Construction.InfiniteLattice.AllMirrorsOfPeriodicGibbsStates
import YangMills.Construction.ReflectionPositivity.CoarseStepsAtASpacing
import YangMills.Construction.ReflectionPositivity.DecayAndLawAtASpacing
import YangMills.Construction.ReflectionPositivity.EnergyMomentumBoundAtCoarseStepsAndInverseSquareLaw
import YangMills.Construction.ReflectionPositivity.HomogeneityOfDegreeZeroOfTheLaw
import YangMills.Construction.ReflectionPositivity.ReflectionSizesAtASpacing
import YangMills.Construction.ReflectionPositivity.WeakClosednessOfTheClassAtASpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare
open YangMills.Construction.InfiniteLattice (GaugeField regionObservables IsLocalObservable)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (MirrorPair)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet)
open YangMills.Construction.LatticeConventions (NormalHyperplane)
variable {a : ℝ}
def planeOfMirror (P : MirrorPair a) : NormalHyperplane where
  normal := P.normal
  level := P.height
  normal_valid := by
    rcases P.admissible with ⟨⟨μ, h⟩, -⟩ | ⟨⟨μ, κ, hne, h⟩, -⟩
    · exact Or.inl ⟨μ, h⟩
    · exact Or.inr ⟨μ, κ, hne, h⟩
theorem single_ne_add_and_sub (μ κ l : Fin 4) :
    (Pi.single μ 1 : Fin 4 → ℝ) ≠ Pi.single κ 1 + Pi.single l 1 ∧
      (Pi.single μ 1 : Fin 4 → ℝ) ≠ Pi.single κ 1 - Pi.single l 1 := by
  constructor <;> intro h <;>
    · have := congrArg (fun v : Fin 4 → ℝ => ∑ i, v i) h
      norm_num [Finset.sum_add_distrib, Finset.sum_sub_distrib] at this
theorem isLatticeMirror_planeOfMirror (P : MirrorPair a) :
    (planeOfMirror P).IsLatticeMirror a := by apply _root_.YangMills.Construction.ReflectionPositivity.PeriodicGibbs.toNormalHyperplane_isLatticeMirror <;> assumption
theorem reflectSymmetry_planeOfMirror (P : MirrorPair a) :
    NormalHyperplane.reflectSymmetry (isLatticeMirror_planeOfMirror P) = P.reflect := by
  have h : (NormalHyperplane.reflectSymmetry (isLatticeMirror_planeOfMirror P)).toFun =
      P.reflect.toFun :=
    NormalHyperplane.reflect_eq_hyperplaneReflect (planeOfMirror P)
  cases hr : NormalHyperplane.reflectSymmetry (isLatticeMirror_planeOfMirror P)
  cases hp : P.reflect
  rw [hr, hp] at h
  cases h
  rfl
theorem periodicGibbs_reflectionPositive
    (hall : InfiniteLattice.PeriodicGibbsSymmetries.Statement)
    (ha : 0 < a) : PeriodicGibbsReflectionPositive a := by
  intro β hβ ν hν
  obtain ⟨hmir, hset, -⟩ := hall a ha β hβ
  have hν' : ν.1 ∈ InfiniteLattice.PeriodicGibbsSymmetries.periodicStates a β := hν
  rw [hset] at hν'
  refine ⟨hν'.2, fun P F hl hF => ?_⟩
  have h := ((hmir ν.1 hν).2 (planeOfMirror P) (isLatticeMirror_planeOfMirror P)).2.1 F hF
  have he : LatticeConventions.MirrorSideIndependence.reflectedPairing
      (isLatticeMirror_planeOfMirror P) ν.1 F =
        ν.integral fun U => conj (P.reflect.actOn F U) * F U := by
    rw [LatticeConventions.MirrorSideIndependence.reflectedPairing,
      reflectSymmetry_planeOfMirror]
    rfl
  rw [← he]
  exact h
theorem combinedBound_holds (hcoarse : CoarseStepsEveryMesh)
    (hsizes : ReflectionSizeBoundsAtMesh)
    (hlaw : SpacingDecayAndLaw.Statement)
    (hhom : SpacingInvariance.Holds)
    (hclosed : WeakClosedEveryMesh)
    (hall : InfiniteLattice.PeriodicGibbsSymmetries.Statement) : CombinedBound := by
  intro a ha
  refine ⟨fun ν hν => ⟨hcoarse a ha ν hν, hsizes a ha ν hν, fun r A hA B hB μ => ?_⟩,
    hclosed a ha, periodicGibbs_reflectionPositive hall ha⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hlaw a ha ν hν r A hA B hB μ
  exact ⟨h₁, h₂, h₃, h₄, h₅, hhom a ha ν hν r A hA B hB μ⟩
end YangMills.Construction.ReflectionPositivity.DirectionPictures.CoarseStepsInverseSquare
