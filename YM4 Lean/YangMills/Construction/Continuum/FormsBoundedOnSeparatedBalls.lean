import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
namespace ConfigSpace
open TestFunctions
variable {n : ℕ}
def SupportInSmallBall (φ : (Fin 4 → ℝ) → ℂ) : Prop :=
  ∃ (B : Set (Fin 4 → ℝ)) (ϱ : ℝ), IsClosedBallRadius B ϱ ∧ ϱ ≤ 1 ∧ tsupport φ ⊆ B
def SeparatedBallBound (c : ℝ) (a : ℕ) (G : ℝ) (T : smoothRealTupleSet n → ℝ) : Prop :=
  2 ≤ n ∧ 0 < c ∧ 0 ≤ G ∧ IsRealMultilinearSmooth T ∧
    ∀ (d : ℝ), 0 < d → ∀ φ : smoothRealTupleSet n,
      (∀ i, SupportInSmallBall (φ.1 i)) → HasSeparatedSupportsR4 φ.1 d →
        |T φ| ≤ G * max 1 (d ^ (-(a : ℤ))) *
          ∏ i, max (uniformNorm (φ.1 i)) (c * gradSupNorm (φ.1 i))
end ConfigSpace
end YangMills.Construction
