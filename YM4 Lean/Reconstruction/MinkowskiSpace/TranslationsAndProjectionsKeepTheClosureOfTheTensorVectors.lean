import Reconstruction.MinkowskiSpace.VectorsAtRealPointsDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.RealPointVectors
def ClosureInvarianceStatement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (vac : H)
    (T : ℝ → OneLoopNotation.BddOp H) (p c : ℝ),
    FieldForms.IsBoundedFieldForm P vac T p c →
    (∀ w : MinkowskiSpace.ComplexVec4,
      MinkowskiSpace.imPart w ∈ MinkowskiSpace.closedFutureCone →
      ∀ v ∈ tensorDomainClosure P vac T,
        FieldForms.spectralTranslation P w v ∈ tensorDomainClosure P vac T) ∧
    ∀ B : ProjectionMeasures.FourBorelSet, ∀ v ∈ tensorDomainClosure P vac T,
      P B v ∈ tensorDomainClosure P vac T
end YangMills.Construction.RealPointVectors
