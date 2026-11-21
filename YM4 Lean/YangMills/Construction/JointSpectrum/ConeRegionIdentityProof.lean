import YangMills.Construction.JointSpectrum.ConeRegionIdentity
import Mathlib
set_option autoImplicit false
open YangMills.Construction.DiscGeometry Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ConeIdentity
private theorem re_sq_add_im_sq_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z.re ^ 2 + z.im ^ 2 = 1 := by
  have hn : Complex.normSq z = 1 := by
    rw [← Complex.sq_norm, hz, one_pow]
  rw [Complex.normSq_apply] at hn
  nlinarith [hn]
private theorem norm_one_add_mul_sq_sub (t : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖1 + (t : ℂ) * z‖ ^ 2 - 4 * t = (1 - t) ^ 2 - t * ‖1 - z‖ ^ 2 := by
  have hre := re_sq_add_im_sq_of_norm_eq_one hz
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
  linear_combination (t ^ 2 + t) * hre
private theorem coneDefect_circleConj_eq (t : unitInterval) (z : Circle) :
    coneDefect t (circleConj z) = coneDefect t z := by
  have hz : ‖1 - ((circleConj z : Circle) : ℂ)‖ = ‖1 - (z : ℂ)‖ := by
    rw [coe_circleConj, ← Complex.norm_conj (1 - (z : ℂ))]
    simp
  simp only [coneDefect, hz]
private theorem ofReal_norm_one_sub_sq (z : ℂ) (hz : ‖z‖ = 1) :
    ((‖1 - z‖ ^ 2 : ℝ) : ℂ) = 2 - z - conj z := by
  have hmul : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    simp
  have hsub : (1 - z) * conj (1 - z) = ((‖1 - z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← hsub, map_sub, map_one]
  linear_combination hmul
private theorem coneExterior_eq_setOf : coneExterior = {p | coneDefect p.1 p.2 < 0} := by
  ext p
  simp only [coneExterior, coneDefect, mem_ofPred_eq]
  constructor
  · rintro ⟨-, hp⟩
    linarith
  · intro hp
    refine ⟨?_, by linarith⟩
    rcases eq_or_lt_of_le p.1.2.1 with h0 | h0
    · rw [← h0] at hp
      norm_num at hp
    · exact h0
private theorem mapsTo_polarToDisc_nearRegion : MapsTo polarToDisc coneExterior nearRegion := by
  intro p hp
  have hneg : coneDefect p.1 p.2 < 0 := by
    rw [coneExterior_eq_setOf] at hp
    exact hp
  have hnorm : ‖polarToDisc p‖ = (p.1 : ℝ) := by
    simp [polarToDisc, abs_of_nonneg p.1.2.1, Circle.norm_coe]
  refine ⟨polarToDisc_mem_closedUnitDisc p, ?_⟩
  have hid := norm_one_add_mul_sq_sub (p.1 : ℝ) (p.2 : ℂ) (Circle.norm_coe p.2)
  rw [hnorm]
  have hdef : ‖1 + polarToDisc p‖ ^ 2 - 4 * (p.1 : ℝ) = coneDefect p.1 p.2 := hid
  linarith
private theorem coneRegion_eq_compl : coneRegion = coneExteriorᶜ := by
  rw [coneExterior_eq_setOf]
  ext p
  simp [coneRegion]
private theorem isClosed_coneRegion : IsClosed coneRegion := by
  have hcont : Continuous fun p : unitInterval × Circle => coneDefect p.1 p.2 := by
    unfold coneDefect
    fun_prop
  exact isClosed_le continuous_const hcont
theorem coneIdentityStatement_holds : ConeIdentityStatement :=
  ⟨fun t _ z hz => norm_one_add_mul_sq_sub t z hz, fun _ _ => rfl, coneDefect_circleConj_eq,
    ofReal_norm_one_sub_sq, coneExterior_eq_setOf, mapsTo_polarToDisc_nearRegion,
    coneRegion_eq_compl, isClosed_coneRegion, fun p hp => by
      change 0 ≤ coneDefect p.1 (circleConj p.2)
      rw [coneDefect_circleConj_eq]
      exact hp⟩
end YangMills.Construction.ConeIdentity
