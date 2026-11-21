import YangMills.Construction.ReflectionPositiveLimits.LatticeApproximationsRepresentativesAndLimits
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
def latticeSymmetryToEuclid {a : ℝ} (s : InfiniteLattice.LatticeSymmetry a) : EuclidIsometry :=
  ⟨s.toFun, s.preservesDist⟩
namespace LatticeSequence
variable {L : ℕ} (A : LatticeSequence L) (j : ℕ+)
abbrev mesh : ℝ := PeriodicLattice.meshSize L ((A.level j : ℕ) : ℤ)
def complexRep (X : Tuple) : A.Fields j → ℂ :=
  fun U => ((A.rep j X U : ℝ) : ℂ)
def SmearedFiniteAndContinuous : Prop :=
  ∀ f ∈ continuousCompact,
    {p : InfiniteLattice.ElementaryPlaquette (A.mesh j) | (fun U : A.Fields j =>
      f p.center * (InfiniteLattice.faceEnergy U p - A.shift j)) ≠ 0}.Finite ∧
    Continuous (A.smeared j f)
def RepContinuousLocal : Prop :=
  ∀ X : Tuple, A.complexRep j X ∈ GibbsAtFixedSpacing.continuousLocal (A.mesh j)
def RepLocalizedNearSupports : Prop :=
  ∀ X : Tuple,
    ((⋃ f ∈ X.1, tsupport f).Nonempty → A.complexRep j X ∈
      InfiniteLattice.regionObservables (A.mesh j)
        {x | maxNormInfDist x (⋃ f ∈ X.1, tsupport f) ≤ A.mesh j / 2}) ∧
    ((⋃ f ∈ X.1, tsupport f) = ∅ → ∃ c : ℝ, ∀ U, A.rep j X U = c)
def RepCommutesWithSymmetries : Prop :=
  ∀ (r : InfiniteLattice.LatticeSymmetry (A.mesh j)) (Z : TupleComb),
    r.actOn (A.repComb j Z) =
      A.repComb j (pushComb (latticeSymmetryToEuclid r) Z)
def RepConcatEqMul : Prop :=
  ∀ (X Y : Tuple) (h : Concatenable X Y),
    A.rep j (concat X Y h) = A.rep j X * A.rep j Y
def RepConjEqConj : Prop :=
  ∀ Z : TupleComb, A.repComb j (conjComb Z) =
    fun U => conj (A.repComb j Z U)
def RepCommutesWithShifts : Prop :=
  ∀ (v : InfiniteLattice.LatticePoint (A.mesh j)) (X : Tuple),
    (InfiniteLattice.shift v).actOn (A.rep j X) =
      A.rep j (push (EuclidIsometry.translate v) X)
def RepCommutesWithMirrors : Prop :=
  ∀ (P : MirrorHyperplanes.MirrorPair (A.mesh j)) (X : Tuple),
    P.reflect.actOn (A.rep j X) =
      A.rep j (push (latticeSymmetryToEuclid P.reflect) X)
def RepCommutesWithHyperoctahedral : Prop :=
  ∀ w ∈ hyperoctahedral, ∃ r : InfiniteLattice.LatticeSymmetry (A.mesh j), r.toFun = ⇑w ∧
    ∀ X : Tuple, r.actOn (A.rep j X) =
      A.rep j (push (latticeSymmetryToEuclid r) X)
def CenteringAtPlaquetteMean : Prop :=
  ∀ μ : GibbsAtFixedSpacing.BorelProb (A.mesh j),
    (∀ p q : InfiniteLattice.ElementaryPlaquette (A.mesh j),
      ∫ U, InfiniteLattice.faceEnergy U p ∂μ.1 = ∫ U, InfiniteLattice.faceEnergy U q ∂μ.1) →
    (∀ p : InfiniteLattice.ElementaryPlaquette (A.mesh j),
      A.shift j = ∫ U, InfiniteLattice.faceEnergy U p ∂μ.1) →
    (∀ f ∈ continuousCompact, A.smeared j f =
      fun U => InfiniteLattice.smearedEnergy f U - ∫ V, InfiniteLattice.smearedEnergy f V ∂μ.1) ∧
    ∀ X : Tuple, A.rep j X = centeredProduct L (A.level j : ℕ) μ X
end LatticeSequence
namespace TupleRepresentatives
def Statement : Prop :=
  ∀ L : ℕ, Odd L → 13 ≤ L → ∀ (A : LatticeSequence L) (j : ℕ+),
    A.SmearedFiniteAndContinuous j ∧
    A.RepContinuousLocal j ∧
    A.RepLocalizedNearSupports j ∧
    A.RepCommutesWithSymmetries j ∧
    A.RepConcatEqMul j ∧
    A.RepConjEqConj j ∧
    A.RepCommutesWithShifts j ∧
    A.RepCommutesWithMirrors j ∧
    A.RepCommutesWithHyperoctahedral j ∧
    IsPermInvariant (A.mean j) ∧
    IsSlotLinear (A.mean j) ∧
    A.CenteringAtPlaquetteMean j
end TupleRepresentatives
end YangMills.Construction.ReflectionPositivity
