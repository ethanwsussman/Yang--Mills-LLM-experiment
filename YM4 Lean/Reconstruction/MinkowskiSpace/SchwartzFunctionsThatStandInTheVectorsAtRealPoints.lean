import Reconstruction.MinkowskiSpace.VectorsAtRealPointsDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.RealPointVectors
def SchwartzClosure : Prop :=
  (∀ (n : ℕ) (g : Motions.TensorVal ℂ n), g ∈ WightmanReconstruction.schwartzOfOrder n →
    RealPointVectors.starVal g ∈ WightmanReconstruction.schwartzOfOrder n) ∧
  (∀ (n' n : ℕ) (g : Motions.TensorVal ℂ n') (f : Motions.TensorVal ℂ n),
    g ∈ WightmanReconstruction.schwartzOfOrder n' → f ∈ WightmanReconstruction.schwartzOfOrder n →
      HyperplaneReflection.tensorVal (RealPointVectors.starVal g) f ∈
        WightmanReconstruction.schwartzOfOrder (n' + n)) ∧
  (∀ (n : ℕ) (f : Motions.TensorVal ℂ n) (a : MinkowskiSpace.RealVec4),
    f ∈ WightmanReconstruction.schwartzOfOrder n →
      RealPointVectors.translateVal a f ∈ WightmanReconstruction.schwartzOfOrder n) ∧
  ∀ (n : ℕ) (u : Fin n → (Fin 4 → ℝ) → ℂ),
    (∀ i, u i ∈ WightmanTheory.schwartzR4) →
      RealPointVectors.tensorVal u ∈ WightmanReconstruction.schwartzOfOrder n
end YangMills.Construction.RealPointVectors
