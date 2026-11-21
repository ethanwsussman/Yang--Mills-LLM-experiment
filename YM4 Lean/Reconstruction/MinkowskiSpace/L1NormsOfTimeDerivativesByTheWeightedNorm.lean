import Reconstruction.MinkowskiSpace.VectorsAtRealPointsDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.TimeDerivativeL1Bound
def Statement : Prop :=
  ∀ (k : ℕ) (h : (Fin 4 → ℝ) → ℂ), h ∈ WightmanTheory.schwartzR4 →
    ENNReal.ofReal (RealPointVectors.maxPartialL1 k h) ≤
      ENNReal.ofReal (Real.pi ^ 2) * WightmanTheory.schwartzNorm (k + 6) h
end YangMills.Construction.TimeDerivativeL1Bound
end
