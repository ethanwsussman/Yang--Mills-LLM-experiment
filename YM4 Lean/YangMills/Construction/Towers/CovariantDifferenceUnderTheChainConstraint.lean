import YangMills.Construction.Towers.ChainOfABlockFieldAndTheTotalNormaliser
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tower Matrices in
def Tower.CovDiffUnderTopConstraint : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L n k k) fun W =>
      ∀ (l : vertexFunctionSpace L n k 0) (B : edgeFormSpace L n k 0),
        (B : Edge L n k 0 → ComplexMatrix2) = covDiff (chainBottom W) l →
        (topConstraintMap L n k W B : Edge L n k k → ComplexMatrix2) =
          covDiff W (restrictVertexFunction k (l : Vertex L n k 0 → ComplexMatrix2))
end YangMills.Construction
end
