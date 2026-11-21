import YangMills.Construction.LawInAState.TheExponentsOfTheBox
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.QuadraticConcentration
private lemma rpow_mul_rpow_same {x : ℝ} (hx : 0 < x) (a b : ℝ) : x ^ a * x ^ b = x ^ (a + b) := (Real.rpow_add hx a b).symm
private lemma rpow_npow_same {x : ℝ} (hx : 0 < x) (a : ℝ) (n : ℕ) : (x ^ a) ^ n = x ^ ((n : ℝ) * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, mul_comm]
private lemma rpow_rpow_same {x : ℝ} (hx : 0 < x) (a r : ℝ) : (x ^ a) ^ r = x ^ (a * r) := (Real.rpow_mul hx.le a r).symm
private lemma sqrt_rpow_same {x : ℝ} (hx : 0 < x) (a : ℝ) : Real.sqrt (x ^ a) = x ^ (a / 2) := by
  rw [Real.sqrt_eq_rpow, rpow_rpow_same hx]; ring_nf
private lemma rpow_mono_of_one_le {x : ℝ} (hx : 1 ≤ x) {a b : ℝ} (h : a ≤ b) : x ^ a ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx h
section TermBounds
variable {Cm x lam A φ ε ρ η err D τ : ℝ}
private lemma term_bounds (hx1 : 1 ≤ x) (hs : 2 ≤ x ^ (1 / 10000 : ℝ)) (H : BoxSizes Cm x lam A φ ε ρ η err D τ) :
    productAverageBound lam A φ ε (Real.sqrt ρ + Real.sqrt ε) ≤ 8 * x ^ (-(2 + 1 / 130) : ℝ) ∧
    averageBound lam A φ ε (Real.sqrt ρ + Real.sqrt ε) ≤ 4 * x ^ (-(1 + 1 / 130) : ℝ) ∧
    singleFormBound lam A φ ≤ 3 * x ^ (-(97 / 100) : ℝ) ∧ A * φ ^ 2 ≤ x ^ (-(1 + 1 / 130) : ℝ) := by
  have hx : 0 < x := by linarith
  obtain ⟨l0, l1, A1, A2, f0, f1, e0, e1, r0, r1, n0, n1, d0, d1, D0, D1, t0, t1⟩ := H
  have A0 : 0 ≤ A := by linarith
  have hsr : Real.sqrt ρ ≤ x ^ (1 / 50 - 2 / 27 + 1 / 10000 : ℝ) := by
    have := Real.sqrt_le_sqrt r1
    rw [sqrt_rpow_same hx] at this
    convert this using 2
    ring
  have hse : Real.sqrt ε ≤ x ^ (-10 : ℝ) := by
    have := Real.sqrt_le_sqrt e1
    rw [sqrt_rpow_same hx] at this
    convert this using 2
    norm_num
  set E0 := Real.sqrt ρ + Real.sqrt ε with hE0
  have E01 : E0 ≤ x ^ (1 / 50 - 2 / 27 + 2 / 10000 : ℝ) := by
    have h1 : Real.sqrt ε ≤ x ^ (1 / 50 - 2 / 27 + 1 / 10000 : ℝ) := hse.trans (rpow_mono_of_one_le hx1 (by norm_num))
    have h2 : 0 < x ^ (1 / 50 - 2 / 27 + 1 / 10000 : ℝ) := Real.rpow_pos_of_pos hx _
    calc E0 ≤ 2 * x ^ (1 / 50 - 2 / 27 + 1 / 10000 : ℝ) := by rw [hE0]; linarith
      _ ≤ x ^ (1 / 10000 : ℝ) * x ^ (1 / 50 - 2 / 27 + 1 / 10000 : ℝ) := by gcongr
      _ = x ^ (1 / 50 - 2 / 27 + 2 / 10000 : ℝ) := by rw [rpow_mul_rpow_same hx]; congr 1; ring
  have sA : Real.sqrt A ≤ x ^ (1 / 50 + 1 / 20000 : ℝ) := by
    have := Real.sqrt_le_sqrt A2
    rw [sqrt_rpow_same hx] at this
    convert this using 2
    ring
  have sε : Real.sqrt (ε * A) ≤ x ^ (-(9 : ℝ)) := by
    have h1 : ε * A ≤ x ^ (-20 : ℝ) * x ^ (1 / 25 + 1 / 10000 : ℝ) := mul_le_mul e1 A2 A0 (by positivity)
    have h2 := Real.sqrt_le_sqrt h1
    rw [rpow_mul_rpow_same hx, sqrt_rpow_same hx] at h2
    exact h2.trans (rpow_mono_of_one_le hx1 (by norm_num))
  have T : ∀ {a b : ℝ}, a ≤ b → x ^ a ≤ x ^ b := fun h => rpow_mono_of_one_le hx1 h
  have q1 : lam ^ 2 * A * E0 ≤ x ^ (-(2 + 1 / 130) : ℝ) := by
    calc lam ^ 2 * A * E0 ≤ (x ^ (-1 + 1 / 10000 : ℝ)) ^ 2 * x ^ (1 / 25 + 1 / 10000 : ℝ) * x ^ (1 / 50 - 2 / 27 + 2 / 10000 : ℝ) := by gcongr
      _ ≤ _ := by
        rw [rpow_npow_same hx, rpow_mul_rpow_same hx, rpow_mul_rpow_same hx]; exact T (by norm_num)
  have q2 : lam ^ (3 / 2 : ℝ) * A * φ * E0 ≤ x ^ (-(2 + 1 / 130) : ℝ) := by
    calc lam ^ (3 / 2 : ℝ) * A * φ * E0 ≤ (x ^ (-1 + 1 / 10000 : ℝ)) ^ (3 / 2 : ℝ) * x ^ (1 / 25 + 1 / 10000 : ℝ) *
          x ^ (-(1 / 2) - 2 / 81 + 1 / 10000 : ℝ) * x ^ (1 / 50 - 2 / 27 + 2 / 10000 : ℝ) := by gcongr
      _ ≤ _ := by
        rw [rpow_rpow_same hx, rpow_mul_rpow_same hx, rpow_mul_rpow_same hx, rpow_mul_rpow_same hx]; exact T (by norm_num)
  have q3 : lam * A * φ ^ 2 ≤ x ^ (-(2 + 1 / 130) : ℝ) := by
    calc lam * A * φ ^ 2 ≤ x ^ (-1 + 1 / 10000 : ℝ) * x ^ (1 / 25 + 1 / 10000 : ℝ) * (x ^ (-(1 / 2) - 2 / 81 + 1 / 10000 : ℝ)) ^ 2 := by gcongr
      _ ≤ _ := by
        rw [rpow_npow_same hx, rpow_mul_rpow_same hx, rpow_mul_rpow_same hx]; exact T (by norm_num)
  have q4 : lam * Real.sqrt (ε * A) * φ ≤ x ^ (-(2 + 1 / 130) : ℝ) := by
    calc lam * Real.sqrt (ε * A) * φ ≤ x ^ (-1 + 1 / 10000 : ℝ) * x ^ (-(9 : ℝ)) * x ^ (-(1 / 2) - 2 / 81 + 1 / 10000 : ℝ) := by gcongr
      _ ≤ _ := by
        rw [rpow_mul_rpow_same hx, rpow_mul_rpow_same hx]; exact T (by norm_num)
  have q5 : lam * A ^ (3 / 2 : ℝ) * φ ^ 2 * E0 ≤ x ^ (-(2 + 1 / 130) : ℝ) := by
    calc lam * A ^ (3 / 2 : ℝ) * φ ^ 2 * E0 ≤ x ^ (-1 + 1 / 10000 : ℝ) * (x ^ (1 / 25 + 1 / 10000 : ℝ)) ^ (3 / 2 : ℝ) *
          (x ^ (-(1 / 2) - 2 / 81 + 1 / 10000 : ℝ)) ^ 2 * x ^ (1 / 50 - 2 / 27 + 2 / 10000 : ℝ) := by gcongr
      _ ≤ _ := by
        rw [rpow_rpow_same hx, rpow_npow_same hx, rpow_mul_rpow_same hx, rpow_mul_rpow_same hx, rpow_mul_rpow_same hx]; exact T (by norm_num)
  have q6 : lam ^ (1 / 2 : ℝ) * A ^ (3 / 2 : ℝ) * φ ^ 3 * E0 ≤ x ^ (-(2 + 1 / 130) : ℝ) := by
    calc lam ^ (1 / 2 : ℝ) * A ^ (3 / 2 : ℝ) * φ ^ 3 * E0 ≤ (x ^ (-1 + 1 / 10000 : ℝ)) ^ (1 / 2 : ℝ) * (x ^ (1 / 25 + 1 / 10000 : ℝ)) ^ (3 / 2 : ℝ) *
          (x ^ (-(1 / 2) - 2 / 81 + 1 / 10000 : ℝ)) ^ 3 * x ^ (1 / 50 - 2 / 27 + 2 / 10000 : ℝ) := by gcongr
      _ ≤ _ := by
        rw [rpow_rpow_same hx, rpow_rpow_same hx, rpow_npow_same hx, rpow_mul_rpow_same hx, rpow_mul_rpow_same hx, rpow_mul_rpow_same hx]; exact T (by norm_num)
  have q7 : lam ^ (1 / 2 : ℝ) * A * φ ^ 2 * Real.sqrt ε ≤ x ^ (-(2 + 1 / 130) : ℝ) := by
    calc lam ^ (1 / 2 : ℝ) * A * φ ^ 2 * Real.sqrt ε ≤ (x ^ (-1 + 1 / 10000 : ℝ)) ^ (1 / 2 : ℝ) * x ^ (1 / 25 + 1 / 10000 : ℝ) *
          (x ^ (-(1 / 2) - 2 / 81 + 1 / 10000 : ℝ)) ^ 2 * x ^ (-10 : ℝ) := by gcongr
      _ ≤ _ := by
        rw [rpow_rpow_same hx, rpow_npow_same hx, rpow_mul_rpow_same hx, rpow_mul_rpow_same hx, rpow_mul_rpow_same hx]; exact T (by norm_num)
  have q8 : A ^ 2 * φ ^ 4 ≤ x ^ (-(2 + 1 / 130) : ℝ) := by
    calc A ^ 2 * φ ^ 4 ≤ (x ^ (1 / 25 + 1 / 10000 : ℝ)) ^ 2 * (x ^ (-(1 / 2) - 2 / 81 + 1 / 10000 : ℝ)) ^ 4 := by gcongr
      _ ≤ _ := by
        rw [rpow_npow_same hx, rpow_npow_same hx, rpow_mul_rpow_same hx]; exact T (by norm_num)
  have m1 : lam * Real.sqrt A * E0 ≤ x ^ (-(1 + 1 / 130) : ℝ) := by
    calc lam * Real.sqrt A * E0 ≤ x ^ (-1 + 1 / 10000 : ℝ) * x ^ (1 / 50 + 1 / 20000 : ℝ) * x ^ (1 / 50 - 2 / 27 + 2 / 10000 : ℝ) := by gcongr
      _ ≤ _ := by
        rw [rpow_mul_rpow_same hx, rpow_mul_rpow_same hx]; exact T (by norm_num)
  have m2 : lam ^ (1 / 2 : ℝ) * Real.sqrt A * φ * E0 ≤ x ^ (-(1 + 1 / 130) : ℝ) := by
    calc lam ^ (1 / 2 : ℝ) * Real.sqrt A * φ * E0 ≤ (x ^ (-1 + 1 / 10000 : ℝ)) ^ (1 / 2 : ℝ) * x ^ (1 / 50 + 1 / 20000 : ℝ) *
          x ^ (-(1 / 2) - 2 / 81 + 1 / 10000 : ℝ) * x ^ (1 / 50 - 2 / 27 + 2 / 10000 : ℝ) := by gcongr
      _ ≤ _ := by
        rw [rpow_rpow_same hx, rpow_mul_rpow_same hx, rpow_mul_rpow_same hx, rpow_mul_rpow_same hx]; exact T (by norm_num)
  have m3 : lam ^ (1 / 2 : ℝ) * Real.sqrt ε ≤ x ^ (-(1 + 1 / 130) : ℝ) := by
    calc lam ^ (1 / 2 : ℝ) * Real.sqrt ε ≤ (x ^ (-1 + 1 / 10000 : ℝ)) ^ (1 / 2 : ℝ) * x ^ (-10 : ℝ) := by gcongr
      _ ≤ _ := by
        rw [rpow_rpow_same hx, rpow_mul_rpow_same hx]; exact T (by norm_num)
  have m4 : A * φ ^ 2 ≤ x ^ (-(1 + 1 / 130) : ℝ) := by
    calc A * φ ^ 2 ≤ x ^ (1 / 25 + 1 / 10000 : ℝ) * (x ^ (-(1 / 2) - 2 / 81 + 1 / 10000 : ℝ)) ^ 2 := by gcongr
      _ ≤ _ := by
        rw [rpow_npow_same hx, rpow_mul_rpow_same hx]; exact T (by norm_num)
  have o1 : lam * Real.sqrt A ≤ x ^ (-(97 / 100) : ℝ) := by
    calc lam * Real.sqrt A ≤ x ^ (-1 + 1 / 10000 : ℝ) * x ^ (1 / 50 + 1 / 20000 : ℝ) := by gcongr
      _ ≤ _ := by
        rw [rpow_mul_rpow_same hx]; exact T (by norm_num)
  have o2 : lam ^ (1 / 2 : ℝ) * Real.sqrt A * φ ≤ x ^ (-(97 / 100) : ℝ) := by
    calc lam ^ (1 / 2 : ℝ) * Real.sqrt A * φ ≤ (x ^ (-1 + 1 / 10000 : ℝ)) ^ (1 / 2 : ℝ) * x ^ (1 / 50 + 1 / 20000 : ℝ) *
          x ^ (-(1 / 2) - 2 / 81 + 1 / 10000 : ℝ) := by gcongr
      _ ≤ _ := by
        rw [rpow_rpow_same hx, rpow_mul_rpow_same hx, rpow_mul_rpow_same hx]; exact T (by norm_num)
  have o3 : A * φ ^ 2 ≤ x ^ (-(97 / 100) : ℝ) := m4.trans (T (by norm_num))
  refine ⟨?_, ?_, ?_, m4⟩
  · simp only [productAverageBound]
    linarith [q1, q2, q3, q4, q5, q6, q7, q8]
  · simp only [averageBound]
    linarith [m1, m2, m3, m4]
  · simp only [singleFormBound]
    linarith [o1, o2, o3]
end TermBounds
set_option maxHeartbeats 1600000 in
theorem boxExponents : boxExponentsStatement := by
  intro C₀ Cm hC hCm
  set K₁ : ℝ := 18 * C₀ + 9 with hK₁
  have hC0 : 0 ≤ C₀ := by linarith
  refine ⟨(16 * C₀ + 12 * C₀ + 16 * C₀ * K₁ + (1 + K₁) ^ 2 + 4 + 32 * C₀ + 36 * C₀ ^ 2) + (8 * C₀ + 1 + K₁ + 2), (2 : ℝ) ^ (10000 : ℕ),
    one_le_pow₀ (by norm_num), ?_⟩
  intro x lam A φ ε ρ η err D τ hxx H
  have hx1 : 1 ≤ x := (one_le_pow₀ (by norm_num)).trans hxx
  have hx : 0 < x := lt_of_lt_of_le one_pos hx1
  have hs : 2 ≤ x ^ (1 / 10000 : ℝ) := by
    have h1 : ((2 : ℝ) ^ (10000 : ℕ)) ^ (1 / 10000 : ℝ) ≤ x ^ (1 / 10000 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hxx (by norm_num)
    have h2 : ((2 : ℝ) ^ (10000 : ℕ)) ^ (1 / 10000 : ℝ) = 2 := by
      have := Real.pow_rpow_inv_natCast (x := 2) (by norm_num) (n := 10000) (by norm_num)
      simpa using this
    rwa [h2] at h1
  clear hxx
  obtain ⟨hP, hM, hO, hAφ⟩ := term_bounds hx1 hs H
  obtain ⟨l0, l1, A1, A2, f0, f1, e0, e1, r0, r1, n0, n1, d0, d1, D0, D1, t0, t1⟩ := H
  set T₂ := x ^ (-(2 + 1 / 130) : ℝ) with hT₂
  set T₁ := x ^ (-(1 + 1 / 130) : ℝ) with hT₁
  set O := x ^ (-(97 / 100) : ℝ) with hO'
  have T₂0 : 0 < T₂ := Real.rpow_pos_of_pos hx _
  have T₁0 : 0 < T₁ := Real.rpow_pos_of_pos hx _
  set e₀ := Real.sqrt ρ + Real.sqrt ε with he₀
  have hBp : 0 ≤ productAverageBound lam A φ ε e₀ := by unfold productAverageBound; positivity
  have hBm : 0 ≤ averageBound lam A φ ε e₀ := by unfold averageBound; positivity
  have hBo : 0 ≤ singleFormBound lam A φ := by unfold singleFormBound; positivity
  set bP := C₀ * productAverageBound lam A φ ε e₀ with hbP
  set bM := C₀ * averageBound lam A φ ε e₀ with hbM
  set bO := C₀ * singleFormBound lam A φ with hbO
  have bP0 : 0 ≤ bP := by positivity
  have bM0 : 0 ≤ bM := by positivity
  have bO0 : 0 ≤ bO := by positivity
  have bP1 : bP ≤ 8 * C₀ * T₂ := by
    have := mul_le_mul_of_nonneg_left hP hC0
    linarith only [this]
  have bM1 : bM ≤ 4 * C₀ * T₁ := by
    have := mul_le_mul_of_nonneg_left hM hC0
    linarith only [this]
  have bO1 : bO ≤ 3 * C₀ * O := by
    have := mul_le_mul_of_nonneg_left hO hC0
    linarith only [this]
  have sη : Real.sqrt η ≤ x ^ (-(1 / 14) : ℝ) := by
    have := Real.sqrt_le_sqrt n1
    rw [sqrt_rpow_same hx] at this
    convert this using 2
    ring
  have sη0 : 0 ≤ Real.sqrt η := Real.sqrt_nonneg _
  have sτ : Real.sqrt τ ≤ x ^ (-(16 * (2 * Cm + 4)) : ℝ) := by
    have := Real.sqrt_le_sqrt t1
    rw [sqrt_rpow_same hx] at this
    convert this using 2
    ring
  have sτ1 : Real.sqrt τ ≤ 1 := sτ.trans (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith only [hCm]))
  have wτ : τ ^ (1 / 32 : ℝ) ≤ x ^ (-(2 * Cm + 4) : ℝ) := by
    have h1 : τ ^ (1 / 32 : ℝ) ≤ (x ^ (-(32 * (2 * Cm + 4)) : ℝ)) ^ (1 / 32 : ℝ) := Real.rpow_le_rpow t0 t1 (by norm_num)
    rw [rpow_rpow_same hx] at h1
    convert h1 using 2
    ring
  have wτ1 : τ ^ (1 / 32 : ℝ) ≤ 1 := wτ.trans (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith only [hCm]))
  have eT : err ≤ T₁ := d1.trans (rpow_mono_of_one_le hx1 (by norm_num))
  have z1 : 2 * Real.sqrt η * bO ≤ 6 * C₀ * T₁ := by
    have h1 : Real.sqrt η * O ≤ T₁ := by
      calc Real.sqrt η * O ≤ x ^ (-(1 / 14) : ℝ) * O := by gcongr
        _ ≤ T₁ := by rw [hO', rpow_mul_rpow_same hx]; exact rpow_mono_of_one_le hx1 (by norm_num)
    have h2 : Real.sqrt η * bO ≤ Real.sqrt η * (3 * C₀ * O) := mul_le_mul_of_nonneg_left bO1 sη0
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 3 * C₀)
    linarith only [h2, h3]
  set Zx := 2 * Real.sqrt η * bO + A * φ ^ 2 with hZx
  have Zx0 : 0 ≤ Zx := by positivity
  have Zx1 : Zx ≤ (6 * C₀ + 1) * T₁ := by rw [hZx]; linarith only [z1, hAφ]
  have z2 : D * Real.sqrt τ ≤ T₁ := by
    calc D * Real.sqrt τ ≤ x ^ Cm * x ^ (-(16 * (2 * Cm + 4)) : ℝ) := by gcongr
      _ ≤ T₁ := by rw [hT₁, rpow_mul_rpow_same hx]; exact rpow_mono_of_one_le hx1 (by linarith only [hCm])
  have hZ : centeringBound C₀ lam A φ η err D τ = Zx + err + (3 * D + 2 * Zx + 2 * err) * Real.sqrt τ := rfl
  set Zb := centeringBound C₀ lam A φ η err D τ with hZb
  have Zb0 : 0 ≤ Zb := by rw [hZ]; positivity
  have Zb1 : Zb ≤ K₁ * T₁ := by
    rw [hZ, hK₁]
    have a1 : Zx * Real.sqrt τ ≤ Zx := mul_le_of_le_one_right Zx0 sτ1
    have a2 : err * Real.sqrt τ ≤ err := mul_le_of_le_one_right d0 sτ1
    linarith only [a1, a2, z2, Zx1, eT]
  have hTT : T₁ * T₁ ≤ T₂ := by
    rw [hT₁, hT₂, rpow_mul_rpow_same hx]; exact rpow_mono_of_one_le hx1 (by norm_num)
  have hBE : productBoundOnEvent C₀ lam A φ ε ρ η err D τ = 2 * bP + 4 * bO * err + 4 * Zb * bM + (err + Zb) ^ 2 +
      (4 * D ^ 2 + 4 * bP + 4 * bO ^ 2) * τ ^ (1 / 32 : ℝ) := rfl
  have hBM : meanBoundOnEvent C₀ lam A φ ε ρ η err D τ = 2 * bM + err + Zb + 2 * D * τ ^ (1 / 32 : ℝ) := rfl
  have w1 : D * τ ^ (1 / 32 : ℝ) ≤ T₁ := by
    calc D * τ ^ (1 / 32 : ℝ) ≤ x ^ Cm * x ^ (-(2 * Cm + 4) : ℝ) := by gcongr
      _ ≤ T₁ := by rw [hT₁, rpow_mul_rpow_same hx]; exact rpow_mono_of_one_le hx1 (by linarith only [hCm])
  have w2 : D ^ 2 * τ ^ (1 / 32 : ℝ) ≤ T₂ := by
    calc D ^ 2 * τ ^ (1 / 32 : ℝ) ≤ (x ^ Cm) ^ 2 * x ^ (-(2 * Cm + 4) : ℝ) := by gcongr
      _ ≤ T₂ := by
        rw [hT₂, rpow_npow_same hx, rpow_mul_rpow_same hx]; exact rpow_mono_of_one_le hx1 (by push_cast; linarith only [hCm])
  have oe : O * err ≤ T₂ := by
    calc O * err ≤ O * x ^ (-(11 / 10) : ℝ) := by gcongr
      _ ≤ T₂ := by rw [hO', hT₂, rpow_mul_rpow_same hx]; exact rpow_mono_of_one_le hx1 (by norm_num)
  have oo : O ^ 2 * τ ^ (1 / 32 : ℝ) ≤ T₂ := by
    calc O ^ 2 * τ ^ (1 / 32 : ℝ) ≤ O ^ 2 * x ^ (-(2 * Cm + 4) : ℝ) := by gcongr
      _ ≤ T₂ := by
        rw [hO', hT₂, rpow_npow_same hx, rpow_mul_rpow_same hx]; exact rpow_mono_of_one_le hx1 (by push_cast; linarith only [hCm])
  have b1 : 4 * bO * err ≤ 12 * C₀ * T₂ := by
    have h1 : bO * err ≤ 3 * C₀ * O * err := mul_le_mul_of_nonneg_right bO1 d0
    have h2 := mul_le_mul_of_nonneg_left oe (by positivity : 0 ≤ 3 * C₀)
    linarith only [h1, h2]
  have b2 : 4 * Zb * bM ≤ 16 * C₀ * K₁ * T₂ := by
    have h1 : Zb * bM ≤ (K₁ * T₁) * (4 * C₀ * T₁) := mul_le_mul Zb1 bM1 bM0 (by positivity)
    have h2 := mul_le_mul_of_nonneg_left hTT (by positivity : 0 ≤ 4 * C₀ * K₁)
    linarith only [h1, h2]
  have b3 : (err + Zb) ^ 2 ≤ (1 + K₁) ^ 2 * T₂ := by
    have h1 : err + Zb ≤ (1 + K₁) * T₁ := by linarith only [eT, Zb1]
    have h2 : (err + Zb) ^ 2 ≤ ((1 + K₁) * T₁) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : ((1 + K₁) * T₁) ^ 2 = (1 + K₁) ^ 2 * (T₁ * T₁) := by ring
    rw [h3] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left hTT (by positivity))
  have b4 : (4 * D ^ 2 + 4 * bP + 4 * bO ^ 2) * τ ^ (1 / 32 : ℝ) ≤ (4 + 32 * C₀ + 36 * C₀ ^ 2) * T₂ := by
    have c1 : bP * τ ^ (1 / 32 : ℝ) ≤ 8 * C₀ * T₂ := (mul_le_of_le_one_right bP0 wτ1).trans bP1
    have c2 : bO ^ 2 * τ ^ (1 / 32 : ℝ) ≤ (3 * C₀) ^ 2 * T₂ := by
      have h1 : bO ^ 2 ≤ (3 * C₀ * O) ^ 2 := pow_le_pow_left₀ bO0 bO1 2
      calc bO ^ 2 * τ ^ (1 / 32 : ℝ) ≤ (3 * C₀ * O) ^ 2 * τ ^ (1 / 32 : ℝ) := by gcongr
        _ = (3 * C₀) ^ 2 * (O ^ 2 * τ ^ (1 / 32 : ℝ)) := by ring
        _ ≤ (3 * C₀) ^ 2 * T₂ := by gcongr
    linarith only [w2, c1, c2]
  have hsum0 : 0 ≤ 8 * C₀ + 1 + K₁ + 2 := by positivity
  have hsum1 : 0 ≤ 16 * C₀ + 12 * C₀ + 16 * C₀ * K₁ + (1 + K₁) ^ 2 + 4 + 32 * C₀ + 36 * C₀ ^ 2 := by positivity
  constructor
  · rw [hBE]
    have e1' : 2 * bP ≤ 16 * C₀ * T₂ := by linarith only [bP1]
    have : 2 * bP + 4 * bO * err + 4 * Zb * bM + (err + Zb) ^ 2 + (4 * D ^ 2 + 4 * bP + 4 * bO ^ 2) * τ ^ (1 / 32 : ℝ) ≤
        (16 * C₀ + 12 * C₀ + 16 * C₀ * K₁ + (1 + K₁) ^ 2 + 4 + 32 * C₀ + 36 * C₀ ^ 2) * T₂ := by
      linarith only [e1', b1, b2, b3, b4]
    refine this.trans (mul_le_mul_of_nonneg_right ?_ T₂0.le)
    linarith only [hsum0]
  · rw [hBM]
    have c1 : 2 * bM ≤ 8 * C₀ * T₁ := by linarith only [bM1]
    have : 2 * bM + err + Zb + 2 * D * τ ^ (1 / 32 : ℝ) ≤ (8 * C₀ + 1 + K₁ + 2) * T₁ := by
      linarith only [c1, eT, Zb1, w1]
    refine this.trans (mul_le_mul_of_nonneg_right ?_ T₁0.le)
    linarith only [hsum1]
end YangMills.Construction.QuadraticConcentration
end
