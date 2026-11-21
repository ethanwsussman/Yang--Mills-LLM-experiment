import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.ResponseInTheExpansion.ComparisonFromValues
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfADensityOnTwoTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames DerivativeInterpolation LocalComparison
namespace ResponseInTheExpansion
namespace ValueComparison
variable {F : BlockFrame}
theorem interpolatedSize_le {σ A h E : ℝ} {k : ℕ} (hσ : 0 < σ) (hA : 1 ≤ A) (hh : 0 < h) (hE0 : 0 < E)
    (hE1 : E ≤ 1) (hk1 : 1 ≤ k) (hk2 : k ≤ 2) :
    interpolatedSize σ (A * h * E) (A * h) k ≤ A * (1 + (64 / σ) + (64 / σ) ^ 2 + 1) * h * E ^ (1 / 3 : ℝ) := by
  unfold interpolatedSize
  have hAh : 0 < A * h := by positivity
  have h64 : 0 < 64 / σ := by positivity
  have e1 : A * h * E / (σ / 64) ^ k ≤ A * (1 + (64 / σ) + (64 / σ) ^ 2) * h * E ^ (1 / 3 : ℝ) := by
    have hEp : E ≤ E ^ (1 / 3 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_ge hE0 hE1 (show (1 / 3 : ℝ) ≤ 1 by norm_num)
      simpa using this
    have hinv : 1 / (σ / 64) ^ k ≤ 1 + 64 / σ + (64 / σ) ^ 2 := by
      have e : 1 / (σ / 64) ^ k = (64 / σ) ^ k := by
        rw [one_div, ← inv_pow, inv_div]
      rw [e]
      have hk' : k = 1 ∨ k = 2 := by omega
      rcases hk' with rfl | rfl
      · nlinarith [sq_nonneg (64 / σ)]
      · nlinarith
    calc A * h * E / (σ / 64) ^ k = A * h * E * (1 / (σ / 64) ^ k) := by ring
      _ ≤ A * h * E ^ (1 / 3 : ℝ) * (1 + 64 / σ + (64 / σ) ^ 2) := by
          gcongr
      _ = _ := by ring
  have e2 : (A * h * E) ^ (1 - (k : ℝ) / 3) * (A * h) ^ ((k : ℝ) / 3) ≤ A * h * E ^ (1 / 3 : ℝ) := by
    have hθ : (1 - (k : ℝ) / 3) + (k : ℝ) / 3 = 1 := by ring
    rw [Real.mul_rpow hAh.le hE0.le, mul_comm ((A * h) ^ (1 - (k : ℝ) / 3)), mul_assoc,
      ← Real.rpow_add hAh, hθ, Real.rpow_one, mul_comm]
    have hk3 : (1 / 3 : ℝ) ≤ 1 - (k : ℝ) / 3 := by
      have : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
      linarith
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hE0 hE1 hk3) hAh.le
  calc _ ≤ A * (1 + 64 / σ + (64 / σ) ^ 2) * h * E ^ (1 / 3 : ℝ) + A * h * E ^ (1 / 3 : ℝ) := add_le_add e1 e2
    _ = _ := by ring
theorem bondDeriv_sub_le_interpolatedSize {C₀ : ℝ}
    (hb : ∀ (F F' : BlockFrame) (G : F.GaugeField F.top → ℝ) (G' : F'.GaugeField F'.top → ℝ)
      (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (c' : Fin k → F'.Site F'.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ₀ M₀ M₃ : ℝ),
      1 ≤ k → k ≤ 2 → 0 < τ₀ → 0 < M₀ → 0 ≤ M₃ →
      (∀ ς : Fin k → ℝ, (∀ l, ς l = 1 ∨ ς l = -1) →
        IsControlledAlongLine G V c (fun l => ς l • X l) τ₀ M₃ ∧
        IsControlledAlongLine G' V' c' (fun l => ς l • X l) τ₀ M₃ ∧
        ∀ s : ℝ, |s| ≤ τ₀ → |G (alongLine c (fun l => ς l • X l) s V) -
          G' (alongLine c' (fun l => ς l • X l) s V')| ≤ M₀) →
      |bondDeriv G V c X - bondDeriv G' V' c' X| ≤
        C₀ * (M₀ / τ₀ ^ k + M₀ ^ (1 - (k : ℝ) / 3) * M₃ ^ ((k : ℝ) / 3)))
    (hline : SmallCurvatureAlongLineAndAgreeOn) {σ M₀ M₃ : ℝ} {F F' : BlockFrame}
    {G : F.GaugeField F.top → ℝ} {G' : F'.GaugeField F'.top → ℝ}
    {Y : F.Cell} {Y' : F'.Cell} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {r k : ℕ}
    {h : Fin k → (Fin 4 → ℤ) × Fin 4} {X : Fin k → imaginaryQuaternions} (hσ : 0 < σ) (hM₀ : 0 < M₀)
    (hM₃ : 0 ≤ M₃) (hk1 : 1 ≤ k) (hk2 : k ≤ 2)
    (hs : ∀ W : F.GaugeField F.top, IsSmallCurvature (5 / 4 * σ) W → ContDiffThreeAlongBonds G W)
    (hs' : ∀ W : F'.GaugeField F'.top, IsSmallCurvature (5 / 4 * σ) W → ContDiffThreeAlongBonds G' W)
    (h3 : ∀ (W : F.GaugeField F.top) (c : Fin 3 → F.Site F.top × Fin 4) (X' : Fin 3 → imaginaryQuaternions),
      IsSmallCurvature (5 / 4 * σ) W → AreUnitVectors X' → |bondDeriv G W c X'| ≤ M₃)
    (h3' : ∀ (W : F'.GaugeField F'.top) (c : Fin 3 → F'.Site F'.top × Fin 4) (X' : Fin 3 → imaginaryQuaternions),
      IsSmallCurvature (5 / 4 * σ) W → AreUnitVectors X' → |bondDeriv G' W c X'| ≤ M₃)
    (hclose : ∀ (W : F.GaugeField F.top) (W' : F'.GaugeField F'.top), IsSmallCurvature (5 / 4 * σ) W →
      IsSmallCurvature (5 / 4 * σ) W' → AgreeOnBall (finiteCells F) W (finiteCells F') W' Y Y' r →
      |G W - G' W'| ≤ M₀)
    (hV : IsSmallCurvature (9 / 8 * σ) V) (hV' : IsSmallCurvature (9 / 8 * σ) V')
    (hA : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r) (hbox : ∀ l, BondWithinRadius r (h l))
    (hX : AreUnitVectors X) :
    |bondDeriv G V (bondsAt Y h) X - bondDeriv G' V' (bondsAt Y' h) X| ≤ C₀ * interpolatedSize σ M₀ M₃ k := by
  have hτ : 0 < σ / 64 := by positivity
  have hnorm : ∀ ς : Fin k → ℝ, (∀ l, ς l = 1 ∨ ς l = -1) → ∀ l, ‖ς l • X l‖ = 1 := by
    intro ς hς l
    rw [norm_smul, hX l, mul_one]
    rcases hς l with e | e <;> simp [e]
  have hsmall : ∀ {F'' : BlockFrame} (W : F''.GaugeField F''.top) (c : Fin k → F''.Site F''.top × Fin 4)
      (ς : Fin k → ℝ), (∀ l, ς l = 1 ∨ ς l = -1) → IsSmallCurvature (9 / 8 * σ) W →
      ∀ s : ℝ, |s| ≤ σ / 64 → IsSmallCurvature (5 / 4 * σ) (alongLine c (fun l => ς l • X l) s W) := by
    intro F'' W c ς hς hW s hs
    have h1 := hline.1 F'' W k c (fun l => ς l • X l) s (9 / 8 * σ)
      (fun l => (hnorm ς hς l).le) hW
    intro p hp
    refine (h1 p hp).trans_le ?_
    have hk : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
    have : 4 * (k : ℝ) * |s| ≤ 4 * 2 * (σ / 64) := by
      have h0 : (0 : ℝ) ≤ |s| := abs_nonneg s
      nlinarith
    linarith
  have key := hb F F' G G' V V' k (bondsAt Y h) (bondsAt Y' h) X (σ / 64) M₀ M₃ hk1 hk2
    hτ hM₀ hM₃ ?_
  · exact key
  · intro ς hς
    refine ⟨⟨fun s hs₁ => hs _ (hsmall V _ ς hς hV s hs₁), fun s hs₁ e => ?_⟩,
      ⟨fun s hs₁ => hs' _ (hsmall V' _ ς hς hV' s hs₁), fun s hs₁ e => ?_⟩, fun s hs₁ => ?_⟩
    · exact h3 _ _ _ (hsmall V _ ς hς hV s hs₁) (fun l => hnorm ς hς (e l))
    · exact h3' _ _ _ (hsmall V' _ ς hς hV' s hs₁) (fun l => hnorm ς hς (e l))
    · exact hclose _ _ (hsmall V _ ς hς hV s hs₁) (hsmall V' _ ς hς hV' s hs₁)
        (hline.2 F F' V V' Y Y' r k h _ s hA hbox)
theorem mul_interpolatedSize_le_exp {C₀ σ A h κ CE : ℝ} {k q : ℕ} (hC₀ : 0 < C₀) (hσ : 0 < σ) (hA : 1 ≤ A)
    (hh : 0 < h) (hκ : 0 < κ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2)
    (hCE : C₀ * (A * (1 + 64 / σ + (64 / σ) ^ 2 + 1)) ≤ CE) :
    C₀ * interpolatedSize σ (A * h * Real.exp (-(κ * q / 2 ^ 7))) (A * h) k ≤
      CE * h * Real.exp (-(2 * (κ / 2 ^ 10) * q)) := by
  set E := Real.exp (-(κ * q / 2 ^ 7)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ κ * (q : ℝ) / 2 ^ 7 := by positivity
    linarith)
  have h1 := interpolatedSize_le hσ hA hh hE0 hE1 hk1 hk2
  have h2 : E ^ (1 / 3 : ℝ) ≤ Real.exp (-(2 * (κ / 2 ^ 10) * q)) := by
    rw [hE, ← Real.exp_mul, Real.exp_le_exp]
    have : 0 ≤ κ * (q : ℝ) := by positivity
    nlinarith
  calc C₀ * interpolatedSize σ (A * h * E) (A * h) k
      ≤ C₀ * (A * (1 + 64 / σ + (64 / σ) ^ 2 + 1) * h * E ^ (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 hC₀.le
    _ = C₀ * (A * (1 + 64 / σ + (64 / σ) ^ 2 + 1)) * h * E ^ (1 / 3 : ℝ) := by ring
    _ ≤ CE * h * E ^ (1 / 3 : ℝ) := by gcongr
    _ ≤ _ := by
        have hpos : 0 < C₀ * (A * (1 + 64 / σ + (64 / σ) ^ 2 + 1)) := by positivity
        have : 0 ≤ CE * h := mul_nonneg (hpos.le.trans hCE) hh.le
        exact mul_le_mul_of_nonneg_left h2 this
theorem bondDeriv_sub_le_exp {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hb : ∀ (F F' : BlockFrame) (G : F.GaugeField F.top → ℝ) (G' : F'.GaugeField F'.top → ℝ)
      (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (c' : Fin k → F'.Site F'.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ₀ M₀ M₃ : ℝ),
      1 ≤ k → k ≤ 2 → 0 < τ₀ → 0 < M₀ → 0 ≤ M₃ →
      (∀ ς : Fin k → ℝ, (∀ l, ς l = 1 ∨ ς l = -1) →
        IsControlledAlongLine G V c (fun l => ς l • X l) τ₀ M₃ ∧
        IsControlledAlongLine G' V' c' (fun l => ς l • X l) τ₀ M₃ ∧
        ∀ s : ℝ, |s| ≤ τ₀ → |G (alongLine c (fun l => ς l • X l) s V) -
          G' (alongLine c' (fun l => ς l • X l) s V')| ≤ M₀) →
      |bondDeriv G V c X - bondDeriv G' V' c' X| ≤
        C₀ * (M₀ / τ₀ ^ k + M₀ ^ (1 - (k : ℝ) / 3) * M₃ ^ ((k : ℝ) / 3)))
    (hline : SmallCurvatureAlongLineAndAgreeOn) {σ κ A h CE : ℝ} {F F' : BlockFrame}
    {G : F.GaugeField F.top → ℝ} {G' : F'.GaugeField F'.top → ℝ} {Y : F.Cell} {Y' : F'.Cell}
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {q k : ℕ}
    {b : Fin k → (Fin 4 → ℤ) × Fin 4} {X : Fin k → imaginaryQuaternions} (hσ : 0 < σ) (hκ : 0 < κ)
    (hA : 1 ≤ A) (hh : 0 < h)
    (hk : k ≤ 2) (hCE : C₀ * (A * (1 + 64 / σ + (64 / σ) ^ 2 + 1)) + A ≤ CE)
    (hs : ∀ W : F.GaugeField F.top, IsSmallCurvature (5 / 4 * σ) W → ContDiffThreeAlongBonds G W)
    (hs' : ∀ W : F'.GaugeField F'.top, IsSmallCurvature (5 / 4 * σ) W → ContDiffThreeAlongBonds G' W)
    (h3 : ∀ (W : F.GaugeField F.top) (c : Fin 3 → F.Site F.top × Fin 4) (X' : Fin 3 → imaginaryQuaternions),
      IsSmallCurvature (5 / 4 * σ) W → AreUnitVectors X' → |bondDeriv G W c X'| ≤ A * h)
    (h3' : ∀ (W : F'.GaugeField F'.top) (c : Fin 3 → F'.Site F'.top × Fin 4) (X' : Fin 3 → imaginaryQuaternions),
      IsSmallCurvature (5 / 4 * σ) W → AreUnitVectors X' → |bondDeriv G' W c X'| ≤ A * h)
    (hclose : ∀ (W : F.GaugeField F.top) (W' : F'.GaugeField F'.top), IsSmallCurvature (5 / 4 * σ) W →
      IsSmallCurvature (5 / 4 * σ) W' → AgreeOnBall (finiteCells F) W (finiteCells F') W' Y Y' q →
      |G W - G' W'| ≤ A * h * Real.exp (-(κ * q / 2 ^ 7)))
    (hV : IsSmallCurvature (9 / 8 * σ) V) (hV' : IsSmallCurvature (9 / 8 * σ) V')
    (hAg : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q) (hbox : ∀ l, BondWithinRadius q (b l))
    (hX : AreUnitVectors X) :
    |bondDeriv G V (bondsAt Y b) X - bondDeriv G' V' (bondsAt Y' b) X| ≤
      CE * h * Real.exp (-(2 * (κ / 2 ^ 10) * q)) := by
  have hpos : 0 < A * h * Real.exp (-(κ * q / 2 ^ 7)) := by positivity
  have hP : 0 < C₀ * (A * (1 + 64 / σ + (64 / σ) ^ 2 + 1)) := by positivity
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have c1 : ∀ {F'' : BlockFrame} {W : F''.GaugeField F''.top}, IsSmallCurvature (9 / 8 * σ) W →
        IsSmallCurvature (5 / 4 * σ) W := fun {F'' W} hW p hp => (hW p hp).trans (by linarith)
    have e0 : ∀ {F'' : BlockFrame} (H : F''.GaugeField F''.top → ℝ) (W : F''.GaugeField F''.top)
        (c : Fin 0 → F''.Site F''.top × Fin 4) (X₀ : Fin 0 → imaginaryQuaternions), bondDeriv H W c X₀ = H W := by
      intro F'' H W c X₀
      simp only [bondDeriv, iteratedFDeriv_zero_apply, leftTranslate_bondSpread_zero]
    rw [e0, e0]
    refine (hclose V V' (c1 hV) (c1 hV') hAg).trans ?_
    have h5 : Real.exp (-(κ * q / 2 ^ 7)) ≤ Real.exp (-(2 * (κ / 2 ^ 10) * q)) := by
      rw [Real.exp_le_exp]
      have : 0 ≤ κ * (q : ℝ) := by positivity
      nlinarith
    have hAC : A ≤ CE := by linarith
    calc A * h * Real.exp (-(κ * q / 2 ^ 7)) ≤ CE * h * Real.exp (-(κ * q / 2 ^ 7)) := by gcongr
      _ ≤ _ := by
        have : 0 ≤ CE * h := mul_nonneg (by linarith) hh.le
        exact mul_le_mul_of_nonneg_left h5 this
  · have h1 := bondDeriv_sub_le_interpolatedSize hb hline (k := k) hσ hpos (show 0 ≤ A * h by positivity)
      hk1 hk hs hs' h3 h3' hclose hV hV' hAg hbox hX
    exact h1.trans (mul_interpolatedSize_le_exp hC₀ hσ hA hh hκ hk1 hk (by linarith))
end ValueComparison
open ValueComparison in
theorem derivDiffLeOfValueDiffLe_holds (hT2 : DerivDiffLeOfCloseAlongLines)
    (hLn : SmallCurvatureAlongLineAndAgreeOn) : DerivDiffLeOfValueDiffLe := by
  obtain ⟨C₀, hC₀, hb⟩ := hT2
  exact ⟨C₀, hC₀, fun σ κ A h CE F F' G G' Y Y' V V' q k b X hσ hκ hA hh hk hCE hs hs' h3 h3' hclose hV hV'
    hAg hbox hX =>
    bondDeriv_sub_le_exp hC₀ hb hLn hσ hκ hA hh hk hCE hs hs' h3 h3' hclose hV hV' hAg hbox hX⟩
end ResponseInTheExpansion
end YangMills.Construction
end
