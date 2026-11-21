import YangMills.Construction.HilbertSpace.BoundedSesqFormRepresentation
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
namespace YangMills.Construction.HilbertSpace.BoundedSesqRep
open YangMills.Construction.SpectralCalculus
theorem claim_holds : Claim := by
  intro H _ _ _ c b hc hb hbd
  have ha : ∀ v : H, ∃ w : H, (∀ u, b u v = inner ℂ u w) ∧ ‖w‖ ≤ c * ‖v‖ := by
    intro v
    let f : H →ₗ[ℂ] ℂ :=
      { toFun := fun u => conj (b u v)
        map_add' := fun x y => by simp [hb.add_left]
        map_smul' := fun a x => by simp [hb.smul_left] }
    have hf : ∀ x, ‖f x‖ ≤ c * ‖v‖ * ‖x‖ := fun x => by
      show ‖conj (b x v)‖ ≤ _
      rw [RCLike.norm_conj]
      exact (hbd x v).trans_eq (by ring)
    refine ⟨(InnerProductSpace.toDual ℂ H).symm (f.mkContinuous (c * ‖v‖) hf), fun u => ?_, ?_⟩
    · rw [← inner_conj_symm, InnerProductSpace.toDual_symm_apply]
      show b u v = conj (conj (b u v))
      simp
    · rw [LinearIsometryEquiv.norm_map]
      exact LinearMap.mkContinuous_norm_le f (mul_nonneg hc (norm_nonneg v)) hf
  choose w hw hn using ha
  let L : H →ₗ[ℂ] H :=
    { toFun := w
      map_add' := fun x y => ext_inner_left ℂ fun u => by
        rw [inner_add_right, ← hw, ← hw, ← hw, hb.add_right]
      map_smul' := fun a x => ext_inner_left ℂ fun u => by
        rw [RingHom.id_apply, inner_smul_right, ← hw, ← hw, hb.smul_right] }
  have hB : ∀ u v, inner ℂ u (L.mkContinuous c hn v) = b u v := fun u v => (hw v u).symm
  refine ⟨L.mkContinuous c hn, hB, fun B' h => ?_, LinearMap.mkContinuous_norm_le L hc hn,
    fun hs u v => ?_⟩
  · exact ContinuousLinearMap.ext fun v =>
      ext_inner_left ℂ fun u => (h u v).trans (hB u v).symm
  · rw [← inner_conj_symm (L.mkContinuous c hn u) v, hB, hB, hs u v, Complex.conj_conj]
end YangMills.Construction.HilbertSpace.BoundedSesqRep
