import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.ReflectionPositivity.TwoSidesOfALinkMirrorAndTheirAlgebras
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity
namespace CutoffMirrors
def relabelInvert {A A' : Type} (τ : A' ≃ A) (ε : A' → ℤˣ)
    (g : A → Matrices.ComplexMatrix2.specialUnitary) : A' → Matrices.ComplexMatrix2.specialUnitary :=
  fun b' => g (τ b') ^ ((ε b' : ℤˣ) : ℤ)
def IsBoundedBorel {X E : Type*} [TopologicalSpace X] [MeasurableSpace E] [Norm E]
    (φ : X → E) : Prop :=
  Measurable[borel X] φ ∧ TestFunctions.IsBoundedFun φ
def RelabelInvertIntegralEq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {A A' : Type} [Finite A] [Finite A'] (τ : A' ≃ A) (ε : A' → ℤˣ) : Prop :=
  ∀ φ : (A' → Matrices.ComplexMatrix2.specialUnitary) → E, IsBoundedBorel φ →
    IsBoundedBorel (φ ∘ relabelInvert τ ε) ∧
      ∫ g, φ (relabelInvert τ ε g) ∂Matrices.ComplexMatrix2.haarPi A =
        ∫ h, φ h ∂Matrices.ComplexMatrix2.haarPi A'
def RelabelInvertMeasurePreserving : Prop :=
  ∀ (A A' : Type) [Finite A] [Finite A'] (τ : A' ≃ A) (ε : A' → ℤˣ),
    IsHomeomorph (relabelInvert τ ε) ∧
      Measure.map (relabelInvert τ ε) (Matrices.ComplexMatrix2.haarPi A) =
        Matrices.ComplexMatrix2.haarPi A' ∧
      RelabelInvertIntegralEq ℝ τ ε ∧ RelabelInvertIntegralEq ℂ τ ε
namespace MirrorData
variable (D : MirrorData)
abbrev PositiveEdge : Type := PeriodicLattice.PositivelyOrientedBond D.L D.m (D.K : ℕ)
def linkVar (b : D.Edge) (U : D.FieldSpace) : Matrices.ComplexMatrix2.specialUnitary :=
  ⟨U.1 b, U.2.1 b (mem_univ _)⟩
def positiveEdgeValues (U : D.FieldSpace) : D.PositiveEdge → Matrices.ComplexMatrix2.specialUnitary :=
  fun b => D.linkVar b.1 U
@[reducible] def productTopology : TopologicalSpace D.FieldSpace :=
  .induced D.positiveEdgeValues inferInstance
def ContinuousForProduct {Y : Type*} [TopologicalSpace Y] (F : D.FieldSpace → Y) : Prop :=
  Continuous[D.productTopology, inferInstance] F
def faceCount : ℕ := Nat.card D.Face
def gibbsMeasureOnFields : Measure D.FieldSpace :=
  (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling).comap Subtype.val
def FieldSpaceIsProduct : Prop :=
  Finite D.Vertex ∧ Finite D.Edge ∧ Finite D.Face ∧
    Function.Bijective D.positiveEdgeValues ∧
    CompactSpace (D.PositiveEdge → Matrices.ComplexMatrix2.specialUnitary) ∧
    TopologicalSpace.MetrizableSpace (D.PositiveEdge → Matrices.ComplexMatrix2.specialUnitary) ∧
    D.productTopology = (inferInstance : TopologicalSpace D.FieldSpace) ∧
    MeasurableSpace.comap D.positiveEdgeValues
        (borel (D.PositiveEdge → Matrices.ComplexMatrix2.specialUnitary)) =
      (inferInstance : MeasurableSpace D.FieldSpace) ∧
    (∀ U : D.FieldSpace,
      PeriodicLattice.gaugeFieldOfPositive (D.positiveEdgeValues U) = U.1) ∧
    ∀ b : D.Edge, D.ContinuousForProduct (D.linkVar b)
def EnergiesBoundedAndMeasureProbability : Prop :=
  (∀ p : D.Face,
    D.ContinuousForProduct (fun U : D.FieldSpace => PeriodicLattice.plaquetteCost U.1 p) ∧
      ∀ U : D.FieldSpace, PeriodicLattice.plaquetteCost U.1 p ∈ Icc (0 : ℝ) 2) ∧
    (∀ f : D.Torus → ℝ,
      D.ContinuousForProduct (fun U : D.FieldSpace => PeriodicLattice.smearedObservable f U.1) ∧
        TestFunctions.IsBoundedFun fun U : D.FieldSpace => PeriodicLattice.smearedObservable f U.1) ∧
    (∀ f : D.Torus → ℂ,
      D.ContinuousForProduct (fun U : D.FieldSpace => PeriodicLattice.smearedObservable f U.1) ∧
        (TestFunctions.IsBoundedFun fun U : D.FieldSpace => PeriodicLattice.smearedObservable f U.1) ∧
        ((∀ x, (f x).im = 0) →
          ∀ U : D.FieldSpace, (PeriodicLattice.smearedObservable f U.1).im = 0)) ∧
    D.ContinuousForProduct (fun U : D.FieldSpace => PeriodicLattice.wilsonAction U.1) ∧
    D.ContinuousForProduct (fun U : D.FieldSpace => PeriodicLattice.boltzmannWeight D.coupling U.1) ∧
    (∀ U : D.FieldSpace, 0 ≤ PeriodicLattice.wilsonAction U.1 ∧
      PeriodicLattice.wilsonAction U.1 ≤ 2 * (D.faceCount : ℝ)) ∧
    Real.exp (-2 * D.coupling * (D.faceCount : ℝ)) ≤
      PeriodicLattice.partitionFunction D.L D.m D.K D.coupling ∧
    PeriodicLattice.partitionFunction D.L D.m D.K D.coupling ≤ 1 ∧
    0 < PeriodicLattice.partitionFunction D.L D.m D.K D.coupling ∧
    Integrable (PeriodicLattice.boltzmannWeight D.coupling)
      (PeriodicLattice.productHaarMeasure D.L D.m (D.K : ℕ)) ∧
    IsProbabilityMeasure (PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.coupling) ∧
    IsProbabilityMeasure D.gibbsMeasureOnFields
end MirrorData
namespace FieldSpaceAndFaceEnergies
def Statement : Prop :=
  ∀ D : MirrorData, D.FieldSpaceIsProduct ∧ RelabelInvertMeasurePreserving ∧
    D.EnergiesBoundedAndMeasureProbability
end FieldSpaceAndFaceEnergies
end CutoffMirrors
end ReflectionPositivity
end YangMills.Construction
end
