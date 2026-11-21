import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftExists
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.Interpolation
theorem hasDerivAt_norm_add_smul (q u : ℍ[ℝ]) (hq : q ≠ 0) :
    HasDerivAt (fun τ : ℝ => ‖q + τ • u‖) (inner ℝ q u / ‖q‖) 0 := by
  have hl : HasDerivAt (fun τ : ℝ => q + τ • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add q
  have h1 := hl.norm_sq
  have h2 : ((‖q + (0 : ℝ) • u‖ ^ 2 : ℝ)) ≠ 0 := by
    simpa using hq
  have h3 := h1.sqrt h2
  have e : (fun τ : ℝ => √(‖q + τ • u‖ ^ 2)) = fun τ : ℝ => ‖q + τ • u‖ := by
    funext τ
    exact Real.sqrt_sq (norm_nonneg _)
  rw [e] at h3
  have e2 : 2 * inner ℝ (q + (0 : ℝ) • u) u / (2 * √(‖q + (0 : ℝ) • u‖ ^ 2)) = inner ℝ q u / ‖q‖ := by
    simp only [zero_smul, add_zero]
    rw [Real.sqrt_sq (norm_nonneg _)]
    have : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 hq
    field_simp
  rw [e2] at h3
  exact h3
theorem hasDerivAt_exp_add_smul (q u : ℍ[ℝ]) (hq : q ≠ 0) (hq0 : q.re = 0) (hu0 : u.re = 0) :
    HasDerivAt (fun τ : ℝ => NormedSpace.exp (q + τ • u))
      (((-Real.sin ‖q‖ * (inner ℝ q u / ‖q‖) : ℝ) : ℍ[ℝ]) +
        ((Real.cos ‖q‖ * (inner ℝ q u / ‖q‖) * ‖q‖ - Real.sin ‖q‖ * (inner ℝ q u / ‖q‖)) / ‖q‖ ^ 2) • q +
        (Real.sin ‖q‖ / ‖q‖) • u) 0 := by
  have hn := hasDerivAt_norm_add_smul q u hq
  have hθ : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 hq
  have e : (fun τ : ℝ => NormedSpace.exp (q + τ • u)) = fun τ : ℝ =>
      ((Real.cos ‖q + τ • u‖ : ℝ) : ℍ[ℝ]) + (Real.sin ‖q + τ • u‖ / ‖q + τ • u‖) • (q + τ • u) := by
    funext τ
    exact Quaternion.exp_of_re_eq_zero _ (by simp [hq0, hu0])
  rw [e]
  have hc : HasDerivAt (fun τ : ℝ => Real.cos ‖q + τ • u‖) (-Real.sin ‖q‖ * (inner ℝ q u / ‖q‖)) 0 := by
    have := hn.cos
    simpa using this
  have hs : HasDerivAt (fun τ : ℝ => Real.sin ‖q + τ • u‖) (Real.cos ‖q‖ * (inner ℝ q u / ‖q‖)) 0 := by
    have := hn.sin
    simpa using this
  have hb := hs.div hn (by simpa using hθ)
  have hl : HasDerivAt (fun τ : ℝ => q + τ • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add q
  have hcoe : HasDerivAt (fun τ : ℝ => ((Real.cos ‖q + τ • u‖ : ℝ) : ℍ[ℝ]))
      (((-Real.sin ‖q‖ * (inner ℝ q u / ‖q‖) : ℝ) : ℍ[ℝ])) 0 := by
    have := hc.smul_const (1 : ℍ[ℝ])
    have e1 : ∀ r : ℝ, r • (1 : ℍ[ℝ]) = (r : ℍ[ℝ]) := fun r => by ext <;> simp
    simp only [e1] at this
    exact this
  have h3 := hcoe.add (hb.smul hl)
  refine h3.congr_deriv ?_
  simp only [Pi.div_apply, zero_smul, add_zero]
  rw [add_assoc, add_comm ((Real.sin ‖q‖ / ‖q‖) • u)]
theorem exists_rightTranslationDeriv_of_ne_zero (w X : BlockAverages.imaginaryQuaternions) (hw : w ≠ 0)
    (hπ : ‖w‖ < Real.pi) : ∃ u : BlockAverages.imaginaryQuaternions, IsRightTranslationDeriv w X u := by
  set q : ℍ[ℝ] := (w : ℍ[ℝ]) with hq
  set x : ℍ[ℝ] := (X : ℍ[ℝ]) with hx
  have hq0 : q.re = 0 := w.2
  have hx0 : x.re = 0 := X.2
  have hqne : q ≠ 0 := fun h => hw (Subtype.ext h)
  set θ := ‖q‖ with hθd
  have hθ : 0 < θ := norm_pos_iff.2 hqne
  have hθπ : θ < Real.pi := hπ
  have hS : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  set a := q.imI with ha
  set b := q.imJ with hb
  set c := q.imK with hc
  set d := x.imI with hd
  set e := x.imJ with he
  set f := x.imK with hf
  have h2 : θ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
    rw [sq, hθd, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def', hq0]
    ring
  set α := θ * Real.cos θ / Real.sin θ with hα
  set γ := (1 - α) / θ ^ 2 with hγ
  set sc := a * d + b * e + c * f with hsc
  set uq : ℍ[ℝ] := ⟨0, α * d + (b * f - c * e) + γ * sc * a, α * e + (c * d - a * f) + γ * sc * b,
    α * f + (a * e - b * d) + γ * sc * c⟩ with huq
  have hu0 : uq.re = 0 := rfl
  have hin : inner ℝ q uq = sc := by
    have e1 : inner ℝ q uq = a * (α * d + (b * f - c * e) + γ * sc * a) +
        b * (α * e + (c * d - a * f) + γ * sc * b) + c * (α * f + (a * e - b * d) + γ * sc * c) := by
      have s1 : (star uq).imI = -(α * d + (b * f - c * e) + γ * sc * a) := rfl
      have s2 : (star uq).imJ = -(α * e + (c * d - a * f) + γ * sc * b) := rfl
      have s3 : (star uq).imK = -(α * f + (a * e - b * d) + γ * sc * c) := rfl
      rw [Quaternion.inner_def, Quaternion.re_mul, s1, s2, s3, hq0]
      ring
    have e2 : γ * θ ^ 2 = 1 - α := by
      rw [hγ]
      field_simp
    rw [e1]
    have e3 : a * (α * d + (b * f - c * e) + γ * sc * a) +
        b * (α * e + (c * d - a * f) + γ * sc * b) + c * (α * f + (a * e - b * d) + γ * sc * c) =
        α * sc + γ * (a ^ 2 + b ^ 2 + c ^ 2) * sc := by
      rw [hsc]
      ring
    rw [e3, ← h2, e2]
    ring
  have hSne := hS.ne'
  have hθne := hθ.ne'
  have goal : HasDerivAt (fun τ : ℝ => NormedSpace.exp (q + τ • uq)) (NormedSpace.exp q * x) 0 := by
    have h1 := hasDerivAt_exp_add_smul q uq hqne hq0 hu0
    rw [← hθd, hin] at h1
    refine h1.congr_deriv ?_
    rw [Quaternion.exp_of_re_eq_zero q hq0, ← hθd]
    have u1 : uq.imI = α * d + (b * f - c * e) + γ * sc * a := rfl
    have u2 : uq.imJ = α * e + (c * d - a * f) + γ * sc * b := rfl
    have u3 : uq.imK = α * f + (a * e - b * d) + γ * sc * c := rfl
    ext <;> simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
      Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe, smul_eq_mul, hq0, hx0, hu0, u1, u2, u3, ← ha, ← hb, ← hc,
      ← hd, ← he, ← hf]
    · rw [hsc]
      field_simp
      ring
    · rw [hγ, hα]
      field_simp
      ring
    · rw [hγ, hα]
      field_simp
      ring
    · rw [hγ, hα]
      field_simp
      ring
  exact ⟨⟨uq, hu0⟩, goal⟩
theorem rightTranslationDerivExists : rightTranslationDerivExistsStatement := by
  have h : ∀ w X : BlockAverages.imaginaryQuaternions, ∃ u : BlockAverages.imaginaryQuaternions,
      ‖w‖ < Real.pi → IsRightTranslationDeriv w X u := by
    intro w X
    by_cases hw : w = 0
    · subst hw
      refine ⟨X, fun _ => ?_⟩
      have := hasDerivAt_exp_smul_const (𝕂 := ℝ) (X : ℍ[ℝ]) (0 : ℝ)
      simpa [IsRightTranslationDeriv] using this
    · by_cases hπ : ‖w‖ < Real.pi
      · obtain ⟨u, hu⟩ := exists_rightTranslationDeriv_of_ne_zero w X hw hπ
        exact ⟨u, fun _ => hu⟩
      · exact ⟨0, fun h => absurd h hπ⟩
  choose Th hTh using h
  exact ⟨Th, hTh⟩
end YangMills.Construction.Interpolation
end
