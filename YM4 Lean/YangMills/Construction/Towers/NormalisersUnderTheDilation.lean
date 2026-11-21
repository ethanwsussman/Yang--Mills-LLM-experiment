import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def NormalisersScalingCompatible : Prop :=
  ∀ (L n k j : ℕ) (hL : 0 < L) (hj : j ≤ k), Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    1 ≤ j →
    (∀ l < j, EventuallyNearIdentity (fieldSpace L (scaledExponent n k j) j (l + 1)) fun W =>
      transportTotalScalar (scaleEdge (n := n) hL hj (l + 1)) (gaussianNormaliser L n k l) W =
        gaussianNormaliser L (scaledExponent n k j) j l W) ∧
    ∀ l < j, EventuallyNearIdentity (fieldSpace L (scaledExponent n k j) j (l + 1)) fun W =>
      transportTotalScalar (scaleEdge (n := n) hL hj (l + 1)) (logNormaliserRatio L n k l) W =
        logNormaliserRatio L (scaledExponent n k j) j l W
end YangMills.Construction.Tower
end
