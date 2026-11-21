import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.OneStepOfACriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def NextLevelComposite.Statement : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    ∀ (b : CriticalBranchData L n k) (𝒰 : Set (Edge L n k i → Matrices.ComplexMatrix2)) (ε : ℝ)
      (p : (Edge L n k (i + 1) → Matrices.ComplexMatrix2) → Edge L n k i → Matrices.ComplexMatrix2),
      b.IsCriticalUpTo i → IsFibreCriticalSection (b.gaugeFixedEnergy i) 𝒰 ε p →
        EventuallyNearIdentity (fieldSpace L n k (i + 1)) (fun W =>
            smoothingIter L n k (i + 1) ((b.extendLevel i p).prolongComp (i + 1) W) = W ∧
              (b.extendLevel i p).energy (i + 1) W =
                plaquetteAction L n k ((b.extendLevel i p).prolongComp (i + 1) W) ∧
              (b.extendLevel i p).SatisfiesMultiplierIdentity (i + 1) W) ∧
        EventuallyNearIdentity (fieldSpace L n k (i + 1)) (fun W =>
          smoothingIter L n k i ((b.extendLevel i p).prolongComp (i + 1) W) = p W) ∧
        ∃ 𝒱 : Set (Edge L n k 0 → Matrices.ComplexMatrix2), IsOpenNhdOfOne 𝒱 ∧
          EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
            (fieldCurveData L n k 0).IsCriticalOn
              {U | U ∈ 𝒱 ∧ smoothingIter L n k (i + 1) U = W} (plaquetteAction L n k)
              ((b.extendLevel i p).prolongComp (i + 1) W)
end YangMills.Construction.Tower
end
