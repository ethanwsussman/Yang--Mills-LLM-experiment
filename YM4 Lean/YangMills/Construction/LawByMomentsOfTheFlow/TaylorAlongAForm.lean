import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
def taylorAlongFormStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (G : TorusFields.TorusField n → ℝ)
    (B : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions)
    (D : (Fin 3 → TorusFields.TorusBond n) → ℝ),
    (∀ v : ℝ, 0 ≤ v → v ≤ 1 → TorusFields.ContDiffThreeAt G (expField v B)) →
    (∀ v : ℝ, 0 ≤ v → v ≤ 1 → ∀ (c : Fin 3 → TorusFields.TorusBond n)
      (X : Fin 3 → BlockAverages.imaginaryQuaternions), BlockAverages.AreUnitVectors X →
      |TorusFields.mixedDeriv G (expField v B) c X| ≤ D c) →
    HasQuadraticFormAtIdentity G →
    |G (expField 1 B) - G (TorusFields.trivialField n) -
        1 / 2 * colourEval (hessianAtIdentity G) (toColourForm B) (toColourForm B)| ≤
      ∑ c : Fin 3 → TorusFields.TorusBond n, (∏ l, ‖B (c l)‖) * D c
end YangMills.Construction.MomentLaw
end
