import YangMills.Construction.RotationInvariance.LineSidesAndReflectionByRotations
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LineSidesViaRotations
open RealPlane
private theorem inner_eq_coords (a b : RealPlane) :
    inner ℝ a b = a 0 * b 0 + a 1 * b 1 := by apply _root_.YangMills.Construction.ForwardTube.inner_eq_coord_sum <;> assumption
private theorem rotate_apply_zero (t : ℝ) (y : RealPlane) :
    rotate t y 0 = y 0 * Real.cos t - y 1 * Real.sin t := by
  simp [RealPlane.rotate]
private theorem rotate_apply_one (t : ℝ) (y : RealPlane) :
    rotate t y 1 = y 0 * Real.sin t + y 1 * Real.cos t := by
  simp [RealPlane.rotate]
private theorem rotate_unitX_zero (t : ℝ) : rotate t unitX 0 = Real.cos t := by
  simp [rotate_apply_zero, unitX]
private theorem rotate_unitX_one (t : ℝ) : rotate t unitX 1 = Real.sin t := by
  simp [rotate_apply_one, unitX]
private theorem inner_self_eq_one {v : RealPlane} (h : ‖v‖ = 1) : inner ℝ v v = 1 := by
  rw [real_inner_self_eq_norm_sq, h]
  norm_num
private theorem exists_rotate_unitX_eq {v : RealPlane} (h : ‖v‖ = 1) :
    ∃ θ : ℝ, rotate θ unitX = v := by
  have hsq : v 0 * v 0 + v 1 * v 1 = 1 := by
    rw [← inner_eq_coords]
    exact inner_self_eq_one h
  set z : ℂ := ⟨v 0, v 1⟩ with hzdef
  have hz2 : ‖z‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    exact hsq
  have hz1 : ‖z‖ = 1 := by
    have h0 := norm_nonneg z
    nlinarith
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz1
    exact zero_ne_one hz1
  refine ⟨Complex.arg z, ?_⟩
  ext i
  fin_cases i
  · show rotate _ unitX 0 = v 0
    rw [rotate_unitX_zero, Complex.cos_arg hz0, hz1]
    simp [hzdef]
  · show rotate _ unitX 1 = v 1
    rw [rotate_unitX_one, Complex.sin_arg, hz1]
    simp [hzdef]
private theorem rotate_unitX_eq_of_isNormalAngle {l P : Set RealPlane} {v u : RealPlane} {θ : ℝ}
    (hl : IsLine l) (hv : IsUnitNormal l v) (hu : u ∈ l)
    (hP : P = posSide v u) (h : IsNormalAngle l P θ) :
    rotate θ unitX = v := by
  obtain ⟨hv', u', hu', hP'⟩ := h
  rcases hl.eq_or_eq_neg hv hv' with h | h
  · exact h
  · exfalso
    have hmem : u + v ∈ P := by
      rw [hP]
      show 0 < inner ℝ v (u + v - u)
      rw [add_sub_cancel_left, inner_self_eq_one hv.1]
      norm_num
    rw [hP', h] at hmem
    rw [h] at hv'
    rw [posSide_eq_of_mem hv' hu' hu] at hmem
    have hlt : 0 < inner ℝ (-v) (u + v - u) := hmem
    rw [add_sub_cancel_left, inner_neg_left, inner_self_eq_one hv.1] at hlt
    norm_num at hlt
private theorem rotate_neg_apply_zero {v : RealPlane} {θ : ℝ}
    (h : rotate θ unitX = v) (w : RealPlane) :
    rotate (-θ) w 0 = inner ℝ v w := by
  rw [rotate_apply_zero, inner_eq_coords, ← h, rotate_unitX_zero, rotate_unitX_one,
    Real.cos_neg, Real.sin_neg]
  ring
private theorem inner_reflectAcross_sub {v : RealPlane} (h : ‖v‖ = 1)
    (u y : RealPlane) :
    inner ℝ v (reflectAcross v u y - u) = -inner ℝ v (y - u) := by
  have e : reflectAcross v u y - u = (y - u) - (2 * inner ℝ v (y - u)) • v := by
    simp only [reflectAcross]
    abel
  rw [e, inner_sub_right, inner_smul_right, inner_self_eq_one h]
  ring
private theorem reflectAcross_involutive {v : RealPlane} (h : ‖v‖ = 1)
    (u : RealPlane) : Function.Involutive (reflectAcross v u) := by
  intro y
  have e : reflectAcross v u (reflectAcross v u y) =
      reflectAcross v u y - (2 * inner ℝ v (reflectAcross v u y - u)) • v := rfl
  rw [e, inner_reflectAcross_sub h]
  simp only [reflectAcross]
  rw [mul_neg, neg_smul]
  abel
private theorem posSide_infinite {v : RealPlane} (h : ‖v‖ = 1) (u : RealPlane) :
    (posSide v u).Infinite := by
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h
    exact zero_ne_one h
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => u + ((n : ℝ) + 1) • v) ?_ ?_
  · intro a b hab
    have hs : ((a : ℝ) + 1) • v = ((b : ℝ) + 1) • v := add_left_cancel hab
    have := smul_left_injective ℝ hv0 hs
    have hc : (a : ℝ) = b := by linarith
    exact_mod_cast hc
  · intro n
    show 0 < inner ℝ v (u + ((n : ℝ) + 1) • v - u)
    rw [add_sub_cancel_left, inner_smul_right, inner_self_eq_one h]
    positivity
theorem holds : Holds := by
  intro l P Q u hl hsides hu
  obtain ⟨u₀, hu₀, v, hv, hP, hQ⟩ := hsides
  have hshift : ∀ y : RealPlane, inner ℝ v (y - u₀) = inner ℝ v (y - u) := by
    intro y
    have e : y - u₀ = (y - u) + (u - u₀) := by abel
    rw [e, inner_add_right, hv.2 u₀ hu₀ u hu, add_zero]
  have hP' : P = posSide v u := hP.trans (posSide_eq_of_mem hv hu₀ hu)
  have hQ' : Q = negSide v u := by
    rw [hQ]
    ext y
    show inner ℝ v (y - u₀) < 0 ↔ inner ℝ v (y - u) < 0
    rw [hshift]
  have hR : lineReflection l = reflectAcross v u := lineReflection_eq hl hu hv
  have hinv := reflectAcross_involutive hv.1 u
  have hmemP : ∀ y, y ∈ P ↔ 0 < inner ℝ v (y - u) := by
    intro y
    rw [hP']
    rfl
  have hmemQ : ∀ y, y ∈ Q ↔ inner ℝ v (y - u) < 0 := by
    intro y
    rw [hQ']
    rfl
  have hPQ : ∀ y, reflectAcross v u y ∈ Q ↔ y ∈ P := by
    intro y
    rw [hmemQ, hmemP, inner_reflectAcross_sub hv.1]
    exact neg_lt_zero
  have hQP : ∀ y, reflectAcross v u y ∈ P ↔ y ∈ Q := by
    intro y
    rw [hmemQ, hmemP, inner_reflectAcross_sub hv.1]
    exact neg_pos
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨θ, hθ⟩ := exists_rotate_unitX_eq hv.1
    refine ⟨θ, ?_⟩
    show NormalPointsInto l (rotate θ unitX) P
    rw [hθ]
    exact ⟨hv, u, hu, hP'⟩
  · intro θ θ' h h'
    have e := (rotate_unitX_eq_of_isNormalAngle hl hv hu hP' h).trans
      (rotate_unitX_eq_of_isNormalAngle hl hv hu hP' h').symm
    have hc : Real.cos θ = Real.cos θ' := by
      rw [← rotate_unitX_zero, ← rotate_unitX_zero, e]
    have hs : Real.sin θ = Real.sin θ' := by
      rw [← rotate_unitX_one, ← rotate_unitX_one, e]
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (Real.Angle.cos_sin_inj hc hs)
    exact ⟨k, by rw [hk]; ring⟩
  · intro θ h y
    have e := rotate_unitX_eq_of_isNormalAngle hl hv hu hP' h
    have hfirst := rotate_neg_apply_zero e (y - u)
    refine ⟨?_, ?_, ?_⟩
    · rw [hmemP, ← hfirst]
      rfl
    · rw [hmemQ, ← hfirst]
      rfl
    · have h0 : v 0 = Real.cos θ := by rw [← e, rotate_unitX_zero]
      have h1 : v 1 = Real.sin θ := by rw [← e, rotate_unitX_one]
      have hcs := Real.sin_sq_add_cos_sq θ
      rw [hR]
      ext i
      fin_cases i
      · show reflectAcross v u y 0 = (u + rotate θ (reflectFirst (rotate (-θ) (y - u)))) 0
        simp only [reflectAcross, inner_eq_coords, PiLp.sub_apply, PiLp.add_apply,
          PiLp.smul_apply, smul_eq_mul, rotate_apply_zero, rotate_apply_one, reflectFirst,
          Real.cos_neg, Real.sin_neg, h0, h1]
        simp
        linear_combination (u 0 - y 0) * hcs
      · show reflectAcross v u y 1 = (u + rotate θ (reflectFirst (rotate (-θ) (y - u)))) 1
        simp only [reflectAcross, inner_eq_coords, PiLp.sub_apply, PiLp.add_apply,
          PiLp.smul_apply, smul_eq_mul, rotate_apply_zero, rotate_apply_one, reflectFirst,
          Real.cos_neg, Real.sin_neg, h0, h1]
        simp
        linear_combination (u 1 - y 1) * hcs
  · rw [hR]
    refine ⟨funext hinv, hinv.bijective, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hPQ x).mpr hx
      · intro hy
        exact ⟨reflectAcross v u y, (hPQ _).mp (by rwa [hinv y]), hinv y⟩
    · ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hQP x).mpr hx
      · intro hy
        exact ⟨reflectAcross v u y, (hQP _).mp (by rwa [hinv y]), hinv y⟩
    · rw [hP']
      exact isOpen_lt continuous_const (by fun_prop)
    · rw [hQ']
      exact isOpen_lt (by fun_prop) continuous_const
    · rw [Set.disjoint_left]
      intro y hy hy'
      exact lt_asymm ((hmemP y).mp hy) ((hmemQ y).mp hy')
    · rw [hP']
      exact posSide_infinite hv.1 u
    · rw [hQ', negSide_eq_posSide_neg]
      exact posSide_infinite (by rw [norm_neg]; exact hv.1) u
end YangMills.Construction.LineSidesViaRotations
