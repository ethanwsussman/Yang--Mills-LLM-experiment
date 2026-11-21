import YangMills.Construction.PositiveDefinite.KernelSesquilinearForm
import YangMills.Construction.PositiveDefinite.KernelSymmBoundLimit
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ComplexOrder Topology
open Filter
namespace YangMills.Construction.PositiveDefinite.KernelSymmBound
theorem symmBoundLimitProperties_holds
    (hSesq : PositiveDefinite.KernelSesqForm.SesqFormProperties) :
    SymmBoundLimitProperties := by
  intro X
  refine ⟨fun K hK => ?_, fun Kseq K₀ hKseq hconv => ?_⟩
  · have hprop := (hSesq X K hK).2
    refine ⟨fun x y => ⟨(hprop x y).2.1, (hprop x y).2.2⟩, fun x hx y => ?_⟩
    have hcs := (hprop x y).2.2
    rw [hx, zero_mul] at hcs
    have hsqle : ‖K x y‖ ^ 2 ≤ 0 := by exact_mod_cast hcs
    have hzero : ‖K x y‖ = 0 := by
      have hsq : ‖K x y‖ ^ 2 = 0 := le_antisymm hsqle (sq_nonneg _)
      exact pow_eq_zero_iff (two_ne_zero) |>.mp hsq
    exact norm_eq_zero.mp hzero
  · intro n x w
    have hlimsum : Tendsto (fun m => ∑ i, ∑ j, conj (w i) * w j * Kseq m (x i) (x j)) atTop
        (𝓝 (∑ i, ∑ j, conj (w i) * w j * K₀ (x i) (x j))) :=
      tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
        (hconv (x i) (x j)).const_mul _
    refine ge_of_tendsto hlimsum ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact hKseq m hm n x w
end YangMills.Construction.PositiveDefinite.KernelSymmBound
