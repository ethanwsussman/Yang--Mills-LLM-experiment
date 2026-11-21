import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TestFunctions
namespace Scales
def lipschitzCompactR4 : AddSubgroup ((Fin 4 → ℝ) → ℝ) where
  carrier := {f | IsLipschitzFor euclidDistR4 f ∧ HasCompactSupport f}
  add_mem' := by
    rintro a b ⟨⟨A, hA, ha⟩, hac⟩ ⟨⟨B, hB, hb⟩, hbc⟩
    refine ⟨⟨A + B, add_nonneg hA hB, fun x y => ?_⟩, hac.add hbc⟩
    have h1 := ha x y
    have h2 := hb x y
    have h3 : ‖(a + b) x - (a + b) y‖ ≤ ‖a x - a y‖ + ‖b x - b y‖ := by
      simp only [Pi.add_apply]
      rw [show a x + b x - (a y + b y) = (a x - a y) + (b x - b y) by ring]
      exact norm_add_le _ _
    nlinarith
  zero_mem' := by
    refine ⟨⟨0, le_refl _, fun x y => ?_⟩, HasCompactSupport.zero⟩
    simp
  neg_mem' := by
    rintro a ⟨⟨A, hA, ha⟩, hac⟩
    refine ⟨⟨A, hA, fun x y => ?_⟩, hac.neg⟩
    have h1 := ha x y
    have h3 : ‖(-a) x - (-a) y‖ = ‖a x - a y‖ := by
      simp only [Pi.neg_apply]
      rw [show -a x - -a y = -(a x - a y) by ring, norm_neg]
    rw [h3]
    exact h1
end Scales
end YangMills.Construction
end
