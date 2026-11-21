import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def RealTransposeFaceFunctionPairing : Prop :=
  ∀ L n k a b : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → a ≤ k → b ≤ k →
    ∀ (T₀ : edgeFormSpace L n k a →ₗ[ℝ] faceFunctionSpace L n k b) (g : faceFunctionSpace L n k b)
      (f : edgeFormSpace L n k a),
      edgeFormPairing (PairedFunctionSpace.realTransposeMap (S := edgePairedSpace L n k a)
          (S' := pairedFunctions (Face L n k b)) T₀ g).1
          (f : Edge L n k a → Matrices.ComplexMatrix2) =
        traceFinsumPairing (g : Face L n k b → Matrices.ComplexMatrix2)
          (T₀ f : Face L n k b → Matrices.ComplexMatrix2)
end YangMills.Construction.Tower
end
