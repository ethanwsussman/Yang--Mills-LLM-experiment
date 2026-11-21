import YangMills.Construction.PositiveDefinite.KernelRestrictPullbackLimit
import YangMills.Construction.PositiveDefinite.KernelSymmBoundLimit
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ComplexOrder
namespace YangMills.Construction.PositiveDefinite.KernelRestrictPullback
theorem restrictPullbackScaleLimit_holds
    (hSymm : PositiveDefinite.KernelSymmBound.SymmBoundLimitProperties) :
    RestrictPullbackScaleLimit := by
  intro X
  refine ⟨fun K hK => ?_, fun Kseq K₀ hKseq hconv => (hSymm X).2 Kseq K₀ (fun n _ => hKseq n) hconv⟩
  have hprop := (hSymm X).1 K hK
  refine ⟨fun x y => (hprop.1 x y).1, fun x y => (hprop.1 x y).2, hprop.2,
    fun T n x w => hK n (fun i => (x i : X)) w,
    fun Z f n x w => hK n (fun i => f (x i)) w, fun t ht n x w => ?_⟩
  show 0 ≤ ∑ i, ∑ j, conj (w i) * w j * ((t : ℂ) * K (x i) (x j))
  have hfactor : ∑ i, ∑ j, conj (w i) * w j * ((t : ℂ) * K (x i) (x j)) =
      (t : ℂ) * ∑ i, ∑ j, conj (w i) * w j * K (x i) (x j) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hfactor]
  exact mul_nonneg (Complex.zero_le_real.mpr ht.le) (hK n x w)
end YangMills.Construction.PositiveDefinite.KernelRestrictPullback
