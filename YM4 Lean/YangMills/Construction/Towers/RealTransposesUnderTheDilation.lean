import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ScalingCommutesWithRealTranspose : Prop :=
  ∀ (L n k j : ℕ) (hL : 0 < L) (hj : j ≤ k), Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    ∀ a ≤ j, ∀ b ≤ j,
      ∀ (A : edgeFormSpace L n k a →ₗ[ℝ] edgeFormSpace L n k b)
        (A' : edgeFormSpace L (scaledExponent n k j) j a →ₗ[ℝ] edgeFormSpace L (scaledExponent n k j) j b),
        (∀ (B : edgeFormSpace L n k a) (B' : edgeFormSpace L (scaledExponent n k j) j a),
          (B' : Edge L (scaledExponent n k j) j a → Matrices.ComplexMatrix2) =
              transportTotal (scaleEdge hL hj a) (B : Edge L n k a → Matrices.ComplexMatrix2) →
            (A' B' : Edge L (scaledExponent n k j) j b → Matrices.ComplexMatrix2) =
              transportTotal (scaleEdge hL hj b) (A B : Edge L n k b → Matrices.ComplexMatrix2)) →
        ∀ (g : edgeFormSpace L n k b) (g' : edgeFormSpace L (scaledExponent n k j) j b),
          (g' : Edge L (scaledExponent n k j) j b → Matrices.ComplexMatrix2) =
              transportTotal (scaleEdge hL hj b) (g : Edge L n k b → Matrices.ComplexMatrix2) →
            (PairedFunctionSpace.realTransposeMap (S := edgePairedSpace L (scaledExponent n k j) j a)
                (S' := edgePairedSpace L (scaledExponent n k j) j b) A' g').1 =
              transportTotal (scaleEdge hL hj a)
                (PairedFunctionSpace.realTransposeMap (S := edgePairedSpace L n k a)
                  (S' := edgePairedSpace L n k b) A g).1
end YangMills.Construction.Tower
end
