import YangMills.Construction.Conventions.ContinuumLimitsOfLatticeApproximationsDefs
import YangMills.Construction.InfiniteLattice.ObservablesAndIsometriesAtOneSpacing
import YangMills.Construction.Lattice.ActionOfLatticeIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity.RepresentativeCovariance
open SeparatedTupleFunctionals (contCompactSupp)
open InfiniteLattice (LatticeSymmetry ElementaryPlaquette AmbientSpace refinedSpacing
  affineHyperoctahedralMaps boundedRegionObservables faceEnergy)
open LimitConventions (ApproxTriple supDist)
open SeparatedTuples (FormalSpan TupleFunctional SepTuple pushSpan conjugation)
variable {L : ℕ}
def supportHalo (a : ℝ) (X : SepTuple) : Set AmbientSpace :=
  {x | supDist x (⋃ f ∈ X.1, tsupport f) ≤ ENNReal.ofReal (a / 2)}
def SymmetriesTransportField (T : ApproxTriple L) (j : ℕ+) : Prop :=
  ∀ r : LatticeSymmetry (refinedSpacing L (T.cutoff j)),
    r.toFun ∈ affineHyperoctahedralMaps (refinedSpacing L (T.cutoff j)) ∧
    (∀ p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)),
      (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet) ∧
    Function.Bijective r.plaquetteMap ∧
    (∀ p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)),
      (r.plaquetteMap p).center = r.toFun p.center) ∧
    (∀ p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)),
      r.actOn (fun U : InfiniteLattice.RefinedGaugeField L (T.cutoff j) =>
        faceEnergy U p) =
        fun U : InfiniteLattice.RefinedGaugeField L (T.cutoff j) =>
          faceEnergy U (r.plaquetteMap p)) ∧
    ∀ f ∈ contCompactSupp ℝ,
      r.actOn (T.smearedField j f) = T.smearedField j (r.pushforwardFun f)
def RepsCompatible (T : ApproxTriple L) (j : ℕ+) : Prop :=
  (∀ (r : LatticeSymmetry (refinedSpacing L (T.cutoff j))) (Z : FormalSpan),
    r.actOn (T.spanRep j Z) =
      T.spanRep j (pushSpan r.toFun Z)) ∧
  (∀ X Y : SepTuple, SepTuple.Composable X Y →
    T.tupleRep j (SepTuple.juxt X Y) =
      T.tupleRep j X * T.tupleRep j Y) ∧
  ∀ Z : FormalSpan,
    (fun U => conj (T.spanRep j Z U)) =
      T.spanRep j (conjugation Z)
def RepsLocalized (T : ApproxTriple L) (j : ℕ+) : Prop :=
  ∀ X : SepTuple,
    Continuous (T.tupleRep j X) ∧
    (fun U => (T.tupleRep j X U : ℂ)) ∈
      boundedRegionObservables (refinedSpacing L (T.cutoff j))
        (supportHalo (refinedSpacing L (T.cutoff j)) X) ∧
    Bornology.IsBounded (supportHalo (refinedSpacing L (T.cutoff j)) X)
def FieldLinearExpectationsMultilinear (T : ApproxTriple L) (j : ℕ+) : Prop :=
  (∀ f ∈ contCompactSupp ℝ, ∀ f' ∈ contCompactSupp ℝ, ∀ α α' : ℝ,
    T.smearedField j (α • f + α' • f') = α • T.smearedField j f + α' • T.smearedField j f') ∧
  ∃ σ : TupleFunctional, (∀ X : SepTuple, σ X = ∫ U, T.tupleRep j X U ∂T.state j) ∧
    σ.IsPermInvariant ∧ σ.IsEntrywiseLinear
def RepresentativesCovariantAndLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ (T : ApproxTriple L) (j : ℕ+),
    SymmetriesTransportField T j ∧ RepsCompatible T j ∧
      RepsLocalized T j ∧ FieldLinearExpectationsMultilinear T j
end ReflectionPositivity.RepresentativeCovariance
end YangMills.Construction
end
