import Reconstruction.MinkowskiSpace.VectorsAtRealPointsDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.WightmanBoundaryValues
section Vectors
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (E : YangMills.Construction.ProjectionMeasures.FourBorelSet →
    YangMills.Construction.OneLoopNotation.BddOp K)
  (Ω : K) (A : ℝ → YangMills.Construction.OneLoopNotation.BddOp K)
structure BoundaryValueProperties (℘ C : ℝ) : Prop where
  wightmanFunctional_zero : ∀ c : ℂ,
    YangMills.Construction.RealPointVectors.wightmanFunctional E Ω A 0 c = c
  integrable_vacuumIntegrand : ∀ (m : ℕ)
    (f : YangMills.Construction.TestSpaces.PointTuple (m + 1) → ℂ),
    f ∈ YangMills.Construction.TestSpaces.schwartzSet (m + 1) →
    ∀ y ∈ YangMills.Construction.RealPointVectors.futureConeTuples m,
      Integrable (YangMills.Construction.RealPointVectors.vacuumIntegrand E Ω A f y)
  exists_continuousOn_extension : ∀ (m : ℕ)
    (f : YangMills.Construction.TestSpaces.PointTuple (m + 1) → ℂ),
    f ∈ YangMills.Construction.TestSpaces.schwartzSet (m + 1) →
    ∃ F : YangMills.Construction.TestSpaces.PointTuple m → ℂ,
      ContinuousOn F (YangMills.Construction.RealPointVectors.closedFutureConeTuples m) ∧
      (∀ y ∈ YangMills.Construction.RealPointVectors.futureConeTuples m,
        F y = ∫ x, YangMills.Construction.RealPointVectors.vacuumIntegrand E Ω A f y x) ∧
      F 0 = YangMills.Construction.RealPointVectors.wightmanFunctional E Ω A (m + 1) f
  norm_wightmanFunctional_le : ∀ (m : ℕ)
    (f : YangMills.Construction.TestSpaces.PointTuple (m + 1) → ℂ),
    f ∈ YangMills.Construction.TestSpaces.schwartzSet (m + 1) →
    ‖YangMills.Construction.RealPointVectors.wightmanFunctional E Ω A (m + 1) f‖ ≤
      4 * ((2 : ℝ) ^ ℘ * C) ^ (m + 1) *
        YangMills.Construction.RealPointVectors.fieldFormNorm ℘ f
end Vectors
def BoundaryValueTheorem : Prop :=
  ∀ {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (E : YangMills.Construction.ProjectionMeasures.FourBorelSet →
      YangMills.Construction.OneLoopNotation.BddOp K)
    (Ω : K) (A : ℝ → YangMills.Construction.OneLoopNotation.BddOp K) (℘ C : ℝ),
    YangMills.Construction.FieldForms.IsBoundedFieldForm E Ω A ℘ C →
    BoundaryValueProperties E Ω A ℘ C
end YangMills.Construction.WightmanBoundaryValues
