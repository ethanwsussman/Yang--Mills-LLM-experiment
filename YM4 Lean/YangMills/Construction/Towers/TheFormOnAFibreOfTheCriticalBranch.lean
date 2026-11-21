import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def CriticalFibreHessianPosDef : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → ∀ i : ℕ, i + 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
      (fieldCurveData L n k i).IsCriticalOn (chosenLevelFibre L n k i W)
          (chosenGaugeFixedEnergy L n k i) (chosenProlong L n k i W) ∧
        Function.Surjective (constraintDifferential L n k i W) ∧
        (fieldCurveData L n k i).IsHessianFormAt (S := LinearMap.ker (constraintDifferential L n k i W))
          (fun B => B.1.1) (chosenLevelFibre L n k i W) (chosenGaugeFixedEnergy L n k i)
          (chosenProlong L n k i W) (fibreHessianForm L n k i W) ∧
        (∀ B : LinearMap.ker (constraintDifferential L n k i W),
          ∃ (I : Set ℝ) (γ : ℝ → Edge L n k i → Matrices.ComplexMatrix2),
            (fieldCurveData L n k i).IsTwiceDiffCurve I γ ∧
              Set.MapsTo γ I (chosenLevelFibre L n k i W) ∧ γ 0 = chosenProlong L n k i W ∧
              (fieldCurveData L n k i).tangent γ = B.1.1) ∧
        (fibreHessianForm L n k i W).PosDef
end YangMills.Construction.Tower
end
