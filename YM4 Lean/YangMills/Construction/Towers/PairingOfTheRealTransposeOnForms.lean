import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def RealTransposeEdgeFormPairing : Prop :=
  ∀ L n k a b : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → a ≤ k → b ≤ k →
    ∀ (T₀ : edgeFormSpace L n k a →ₗ[ℝ] edgeFormSpace L n k b) (g : edgeFormSpace L n k b)
      (f : edgeFormSpace L n k a),
      edgeFormPairing (PairedFunctionSpace.realTransposeMap (S := edgePairedSpace L n k a)
          (S' := edgePairedSpace L n k b) T₀ g).1 (f : Edge L n k a → Matrices.ComplexMatrix2) =
        edgeFormPairing (g : Edge L n k b → Matrices.ComplexMatrix2)
          (T₀ f : Edge L n k b → Matrices.ComplexMatrix2)
end YangMills.Construction.Tower
end
