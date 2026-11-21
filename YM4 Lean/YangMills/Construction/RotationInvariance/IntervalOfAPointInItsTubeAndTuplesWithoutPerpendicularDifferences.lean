import YangMills.Construction.RotationInvariance.TubesOfTheFramesAndOrderings
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace ForwardTube
def tubeAngleInterval (υ : rightAngleMultiples) {q : ℕ} (σ : Equiv.Perm (Fin (q + 1)))
    (y : Fin (q + 1) → RealPlane) : Set ℝ :=
  {t | t ∈ Set.Ioo (-Real.pi) Real.pi ∧
    embedPlaneTuple (mapPoints (rotate t) y) ∈ orderedTube υ σ}
def genericTuples (n : ℕ) : Set (Fin n → RealPlane) :=
  {y | y ∈ injectivePointTuples n ∧
    ∀ i j k l : Fin n, i ≠ j → k ≠ l → ({i, j} : Finset (Fin n)) ≠ {k, l} →
      inner ℝ (y i - y j) (y k - y l) ≠ 0}
end ForwardTube
end YangMills.Construction
end
