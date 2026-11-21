import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate ENNReal
noncomputable section
namespace YangMills.Construction.FourSpace
abbrev Vec : Type := Fin 4 → ℝ
theorem closedSupport_euclidean_eq_tsupport (D : ReflectionPositivity.AxisMirror.MirrorData)
    {𝕜 : Type*} [RCLike 𝕜] (f : Vec → 𝕜) :
    ReflectionPositivity.AxisMirror.Ambient.closedSupport D .euclidean f = tsupport f :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
def C1c : Set (Vec → ℝ) :=
  {f | TestFunctions.IsC1R4 f ∧ IsCompact (tsupport f)}
theorem C1c_eq_compactC1 (D : ReflectionPositivity.AxisMirror.MirrorData) :
    C1c = ReflectionPositivity.AxisMirror.Ambient.compactC1 D ℝ .euclidean := by
  have hcpt : ∀ f : Vec → ℝ, IsCompact (tsupport f) ↔ MetricNotions.IsCompactWrt
      (ReflectionPositivity.AxisMirror.Ambient.metric D .euclidean)
      (ReflectionPositivity.AxisMirror.Ambient.closedSupport D .euclidean f) := fun f => by
    rw [closedSupport_euclidean_eq_tsupport]
    exact (SeparatedTuplesR4.isCompactWrt_euclid_iff (fun _ _ => rfl) _).symm
  ext f
  exact and_congr Iff.rfl (hcpt f)
end YangMills.Construction.FourSpace
