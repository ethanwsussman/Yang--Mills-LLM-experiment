import YangMills.Construction.HilbertSpaces.CommutingPairsOfAContractionAndAUnitary
import YangMills.Construction.InfiniteLattice.ConditionsOfTheReconstructionAtALatticeMirror
import YangMills.Construction.InfiniteLattice.HilbertSpaceAtALatticeMirror
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAtAMirrorGivenWithANormal
import Mathlib
set_option autoImplicit false
open MeasureTheory
open YangMills.Construction.OneLoopNotation YangMills.Construction.ComplexHilbert YangMills.Construction.ContractionUnitary
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction
namespace LatticeConventions
namespace NormalHyperplane
open InfiniteLattice (GaugeField IsSymmetricUnder LatticePoint observableSupNorm shift)
variable {a : ℝ} {Q : NormalHyperplane}
def TransportsClassesBy (hQ : Q.IsLatticeMirror a) (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] (v : LatticePoint a) (B : BddOp (MirrorHilbertSpace hQ ν)) :
    Prop :=
  ∀ F : upperObservables a Q, ∃ F' : upperObservables a Q,
    F'.1 = (shift v).actOn F.1 ∧
      B (mirrorClass hQ ν F) = mirrorClass hQ ν F'
def stepOperator (hQ : Q.IsLatticeMirror a) (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] (h : LatticePoint a) : BddOp (MirrorHilbertSpace hQ ν) :=
  Classical.epsilon (TransportsClassesBy hQ ν h)
def vectorUnitary (hQ : Q.IsLatticeMirror a) (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] (w : LatticePoint a) : BddOp (MirrorHilbertSpace hQ ν) :=
  Classical.epsilon fun V : BddOp (MirrorHilbertSpace hQ ν) =>
    TransportsClassesBy hQ ν w V ∧
      IsUnitaryMap (V : MirrorHilbertSpace hQ ν →ₗ[ℂ] MirrorHilbertSpace hQ ν)
def ReflectionInvariantAndClassBounded (hQ : Q.IsLatticeMirror a)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] : Prop :=
  IsSymmetricUnder ν (reflectSymmetry hQ) ∧
    ∀ F : upperObservables a Q, ‖mirrorClass hQ ν F‖ ≤ observableSupNorm F.1
def StepIsPositiveContraction (hQ : Q.IsLatticeMirror a) (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] (h : LatticePoint a) : Prop :=
  TransportsClassesBy hQ ν h (stepOperator hQ ν h) ∧
    (∀ B, TransportsClassesBy hQ ν h B → B = stepOperator hQ ν h) ∧
    IsSymmetricOp (stepOperator hQ ν h) ∧
    OpGE (stepOperator hQ ν h) 0 ∧
    OpLE (stepOperator hQ ν h) (idOp (MirrorHilbertSpace hQ ν))
def VectorIsUnitary (hQ : Q.IsLatticeMirror a) (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] (w : LatticePoint a) : Prop :=
  TransportsClassesBy hQ ν w (vectorUnitary hQ ν w) ∧
    IsUnitaryMap (vectorUnitary hQ ν w :
      MirrorHilbertSpace hQ ν →ₗ[ℂ] MirrorHilbertSpace hQ ν) ∧
    ∀ V : BddOp (MirrorHilbertSpace hQ ν), TransportsClassesBy hQ ν w V →
      IsUnitaryMap (V : MirrorHilbertSpace hQ ν →ₗ[ℂ] MirrorHilbertSpace hQ ν) →
        V = vectorUnitary hQ ν w
def CommuteWithMatrixElements (hQ : Q.IsLatticeMirror a)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] (h : LatticePoint a) {k : ℕ}
    (w : Fin k → LatticePoint a) : Prop :=
  (∀ i, Commute (stepOperator hQ ν h) (vectorUnitary hQ ν (w i))) ∧
    (∀ i j, Commute (vectorUnitary hQ ν (w i)) (vectorUnitary hQ ν (w j))) ∧
    ∀ (F F' : upperObservables a Q) (n : ℕ) (y : Fin k → ℤ),
      ⟪mirrorClass hQ ν F,
          (stepOperator hQ ν h ^ n *
            (List.ofFn fun i => zpowOp (vectorUnitary hQ ν (w i)) (y i)).prod)
            (mirrorClass hQ ν F')⟫_ℂ =
        ∫ U, conjFun ((reflectSymmetry hQ).actOn F.1) U *
          (shift (n • h + ∑ i, y i • w i)).actOn F'.1 U ∂ν
end NormalHyperplane
open NormalHyperplane
def MirrorReconstruction : Prop :=
  ∀ (a : Spacing) (S S' : NormalHyperplane) (hS : S.IsLatticeMirror (a : ℝ))
    (hS' : S'.IsLatticeMirror (a : ℝ)) (h : InfiniteLattice.LatticePoint (a : ℝ)) (k : ℕ)
    (w : Fin k → InfiniteLattice.LatticePoint (a : ℝ))
    (ν : Measure (InfiniteLattice.GaugeField (a : ℝ))) [IsProbabilityMeasure ν],
    MirrorReconstructionHyps (a : ℝ) S (h : Point) S' (fun i => (w i : Point)) →
    InfiniteLattice.IsSymmetricUnder ν (InfiniteLattice.shift h) →
    (∀ i, InfiniteLattice.IsSymmetricUnder ν (InfiniteLattice.shift (w i))) →
    IsReflectionPositiveAcrossMirror hS ν →
    IsReflectionPositiveAcrossMirror hS' ν →
    ReflectionInvariantAndClassBounded hS ν ∧
      StepIsPositiveContraction hS ν h ∧
      (∀ i, VectorIsUnitary hS ν (w i)) ∧
      CommuteWithMatrixElements hS ν h w
end LatticeConventions
end YangMills.Construction
end
