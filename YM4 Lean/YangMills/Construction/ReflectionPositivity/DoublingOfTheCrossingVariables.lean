import YangMills.Construction.ReflectionPositivity.CoordinatesDoubledSpaceAndFunctionalsOfALinkMirror
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors
namespace MirrorData
variable (D : MirrorData)
def fieldHaar : Measure D.FieldSpace :=
  (PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)).comap Subtype.val
end MirrorData
namespace LinkLevel
variable {D : MirrorData} (C : LinkLevel D)
def splitCoords (U : D.FieldSpace) :
    (C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary) ×
      (C.halfEdges .neg → Matrices.ComplexMatrix2.specialUnitary) ×
      (C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary) :=
  (C.halfCoords .pos U, C.halfCoords .neg U, C.transversalCoords U)
def edgesInSlab (σ : SlabSide) : Set D.Edge :=
  {b | (b.source : D.Torus) ∈ C.openSlab σ ∧ (b.target : D.Torus) ∈ C.openSlab σ}
abbrev QuadrupleSpace : Type :=
  (C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary) ×
    (C.halfEdges .neg → Matrices.ComplexMatrix2.specialUnitary) ×
    (C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary) ×
    (C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary)
def quadrupleHaar : Measure C.QuadrupleSpace :=
  (C.halfHaar .pos).prod ((C.halfHaar .neg).prod (C.transversalHaar.prod C.transversalHaar))
def liftToQuadruple {E : Type*} (Υ : D.FieldSpace → E) (x : C.QuadrupleSpace) : E :=
  C.evalCoords Υ x.1 x.2.1 (C.transversalQuot x.2.2.1 x.2.2.2)
def pairPoints (x : C.QuadrupleSpace) : C.DoubleSpace × C.DoubleSpace :=
  (C.posPoint x.1 x.2.2.1, C.negPoint x.2.1 x.2.2.2)
end LinkLevel
namespace DoubledTransversal
variable {D : MirrorData} (C : LinkLevel D)
def PositiveEdgesPartition : Prop :=
  {b : D.Edge | b.IsPositivelyOriented} =
      C.halfEdges .pos ∪ C.halfEdges .neg ∪ C.transversalEdges ∧
    Disjoint (C.halfEdges .pos) (C.halfEdges .neg) ∧
    Disjoint (C.halfEdges .pos) C.transversalEdges ∧
    Disjoint (C.halfEdges .neg) C.transversalEdges
def SplitCoordsHomeomorph : Prop :=
  IsHomeomorph C.splitCoords ∧
    Measure.map C.splitCoords D.fieldHaar =
      (C.halfHaar .pos).prod ((C.halfHaar .neg).prod C.transversalHaar)
def HalfAlgebraEqSlabFunctions (σ : SlabSide) : Prop :=
  (∀ F : D.FieldSpace → ℂ,
    D.IsBoundedMeasurableInLinks (C.edgesInSlab σ) F ↔ F ∈ C.halfAlgebra σ) ∧
  ∀ F ∈ C.halfAlgebra σ, TestFunctions.IsBoundedFun (C.halfFunction σ F) ∧
    Measurable[borel (C.halfEdges σ → Matrices.ComplexMatrix2.specialUnitary)] (C.halfFunction σ F)
def HalfAlgebraClosed (σ : SlabSide) : Prop :=
  (∀ F ∈ C.halfAlgebra σ, TestFunctions.IsBoundedFun F ∧ Measurable[borel D.FieldSpace] F) ∧
  (∀ z : ℂ, (fun _ => z) ∈ C.halfAlgebra σ) ∧
  (∀ F ∈ C.halfAlgebra σ, ∀ F' ∈ C.halfAlgebra σ, F + F' ∈ C.halfAlgebra σ) ∧
  (∀ z : ℂ, ∀ F ∈ C.halfAlgebra σ, z • F ∈ C.halfAlgebra σ) ∧
  (∀ F ∈ C.halfAlgebra σ, ∀ F' ∈ C.halfAlgebra σ, F * F' ∈ C.halfAlgebra σ) ∧
  ∀ F ∈ C.halfAlgebra σ, (fun U => starRingEnd ℂ (F U)) ∈ C.halfAlgebra σ
def HalfFunctionLinearIsometric (σ : SlabSide) : Prop :=
  (∀ F ∈ C.halfAlgebra σ, ∀ F' ∈ C.halfAlgebra σ,
    C.halfFunction σ (F + F') = C.halfFunction σ F + C.halfFunction σ F') ∧
  (∀ z : ℂ, ∀ F ∈ C.halfAlgebra σ, C.halfFunction σ (z • F) = z • C.halfFunction σ F) ∧
  ∀ F ∈ C.halfAlgebra σ, ⨆ u, ‖C.halfFunction σ F u‖ = ⨆ U, ‖F U‖
def TransferIsReflection : Prop :=
  IsHomeomorph C.transfer ∧
  Measure.map C.transfer (C.halfHaar .neg) = C.halfHaar .pos ∧
  (∀ U : D.FieldSpace, C.halfCoords .pos (C.reflectField U) =
    C.transfer (C.halfCoords .neg U)) ∧
  ∀ F ∈ C.halfAlgebra .pos, ∀ U : D.FieldSpace, F (C.reflectField U) =
    C.halfFunction .pos F (C.transfer (C.halfCoords .neg U))
def IntegralDoubled (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] : Prop :=
  ∀ Υ : D.FieldSpace → E, TestFunctions.IsBoundedFun Υ → Measurable[borel D.FieldSpace] Υ →
    TestFunctions.IsBoundedFun (C.liftToQuadruple Υ) ∧
    Measurable[borel C.QuadrupleSpace] (C.liftToQuadruple Υ) ∧
    ∫ U, Υ U ∂D.fieldHaar = ∫ x, C.liftToQuadruple Υ x ∂C.quadrupleHaar
def PairPointsIndependent : Prop :=
  Continuous C.pairPoints ∧
  Measure.map C.pairPoints C.quadrupleHaar = C.doubleHaar.prod C.doubleHaar ∧
  ∀ φ ψ : C.DoubleSpace → ℂ, TestFunctions.IsBoundedFun φ → Measurable[borel C.DoubleSpace] φ →
    TestFunctions.IsBoundedFun ψ → Measurable[borel C.DoubleSpace] ψ →
    ∫ x, φ (C.pairPoints x).1 * starRingEnd ℂ (ψ (C.pairPoints x).2) ∂C.quadrupleHaar =
      (∫ ω, φ ω ∂C.doubleHaar) * starRingEnd ℂ (∫ ω, ψ ω ∂C.doubleHaar)
def DoublingProperties : Prop :=
  ∀ (D : MirrorData) (C : LinkLevel D),
    PositiveEdgesPartition C ∧ SplitCoordsHomeomorph C ∧
    (∀ σ : SlabSide, HalfAlgebraEqSlabFunctions C σ ∧ HalfAlgebraClosed C σ ∧
      HalfFunctionLinearIsometric C σ) ∧
    TransferIsReflection C ∧
    IntegralDoubled C ℝ ∧ IntegralDoubled C ℂ ∧
    PairPointsIndependent C
end DoubledTransversal
end YangMills.Construction.ReflectionPositivity.CutoffMirrors
end
