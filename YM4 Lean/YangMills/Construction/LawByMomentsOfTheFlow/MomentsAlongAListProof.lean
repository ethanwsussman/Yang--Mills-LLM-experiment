import YangMills.Construction.LawByMomentsOfTheFlow.MomentsAlongAList
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace MomentMethod
variable {X ι : Type} [MeasurableSpace X] {μ : Measure X}
private theorem measurable_sumAlong (e : ι → X → ℝ) (he : ∀ c, Measurable (e c)) (l : List ι) :
    Measurable (sumAlong e l) := by
  induction l with
  | nil =>
    have : sumAlong e [] = fun _ => 0 := by
      funext x
      simp [sumAlong]
    rw [this]
    exact measurable_const
  | cons c r ih =>
    have : sumAlong e (c :: r) = fun x => e c x + sumAlong e r x := by
      funext x
      simp [sumAlong]
    rw [this]
    exact (he c).add ih
private theorem sumAlong_nonneg (e : ι → X → ℝ) (he : ∀ c x, 0 ≤ e c x) (l : List ι) (x : X) :
    0 ≤ sumAlong e l x := by
  induction l with
  | nil => simp [sumAlong]
  | cons c r ih =>
    have h1 := he c x
    simp only [sumAlong, List.map_cons, List.sum_cons] at ih ⊢
    linarith
private theorem eLpNorm_sumAlong_le (e : ι → X → ℝ) (he : ∀ c, Measurable (e c)) (l : List ι) (p : ENNReal)
    (hp : 1 ≤ p) (b : ℝ) (hb : 0 ≤ b) (hm : ∀ c, eLpNorm (e c) p μ ≤ ENNReal.ofReal b) :
    eLpNorm (sumAlong e l) p μ ≤ ENNReal.ofReal (l.length * b) := by
  induction l with
  | nil =>
    have : sumAlong e [] = fun _ => (0 : ℝ) := by
      funext x
      simp [sumAlong]
    rw [this, eLpNorm_zero']
    exact zero_le
  | cons c r ih =>
    have e1 : sumAlong e (c :: r) = e c + sumAlong e r := by
      funext x
      simp [sumAlong]
    rw [e1]
    refine (eLpNorm_add_le (he c).aestronglyMeasurable (measurable_sumAlong e he r).aestronglyMeasurable hp).trans ?_
    have h2 : ((c :: r).length : ℝ) * b = b + r.length * b := by
      simp only [List.length_cons]
      push_cast
      ring
    rw [h2, ENNReal.ofReal_add hb (by positivity)]
    exact add_le_add (hm c) ih
private theorem eLpNorm_const_le_ofReal [IsProbabilityMeasure μ] (a : ℝ) (ha : 0 ≤ a) (p : ENNReal) :
    eLpNorm (fun _ : X => a) p μ ≤ ENNReal.ofReal a := by
  have := eLpNorm_le_of_ae_bound (μ := μ) (p := p) (f := fun _ : X => a) (C := a) (ae_of_all _ fun _ => by
    rw [Real.norm_eq_abs, abs_of_nonneg ha])
  simpa using this
private theorem eLpNorm_const_mul_le (a : ℝ) (ha : 0 ≤ a) (f : X → ℝ) (p : ENNReal) (B : ℝ) (hB : 0 ≤ B)
    (h : eLpNorm f p μ ≤ ENNReal.ofReal B) : eLpNorm (fun x => a * f x) p μ ≤ ENNReal.ofReal (a * B) := by
  have e : (fun x => a * f x) = a • f := by
    funext x
    simp
  rw [e, eLpNorm_const_smul, ENNReal.ofReal_mul ha]
  have e2 : ‖a‖ₑ = ENNReal.ofReal a := Real.enorm_of_nonneg ha
  rw [e2]
  exact mul_le_mul_right h _
private theorem eLpNorm_pow_le (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (k : ℕ) (hk : 0 < k) (p : ENNReal) (B : ℝ)
    (hB : 0 ≤ B) (h : eLpNorm f (p * k) μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun x => f x ^ k) p μ ≤ ENNReal.ofReal (B ^ k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have e := eLpNorm_norm_rpow (μ := μ) (p := p) f hk'
  have e1 : (fun x => ‖f x‖ ^ (k : ℝ)) = fun x => f x ^ k := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (hf x), Real.rpow_natCast]
  rw [e1, ENNReal.ofReal_natCast] at e
  rw [e]
  calc eLpNorm f (p * k) μ ^ (k : ℝ) ≤ ENNReal.ofReal B ^ (k : ℝ) := ENNReal.rpow_le_rpow h hk'.le
    _ = ENNReal.ofReal (B ^ k) := by
      rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow hB]
theorem momentBound : momentBoundStatement := by
  refine ⟨?_, ?_⟩
  · intro X _ μ _ ι e he he0 l₁ l₂ q b b' ε a₀ a₁ a₂ a₃ c₀ K hq hb hb' hε ha₀ ha₁ ha₂ ha₃ hc₀ hK h2 h20 g hg
    have hq1 : (1 : ENNReal) ≤ (q : ENNReal) := by exact_mod_cast hq
    have hp2 : (1 : ENNReal) ≤ ((2 * q : ℕ) : ENNReal) := by
      have : 1 ≤ 2 * q := by omega
      exact_mod_cast this
    have hq2 : (q : ENNReal) ≤ ((2 * q : ℕ) : ENNReal) := by
      have : q ≤ 2 * q := by omega
      exact_mod_cast this
    have m1 := measurable_sumAlong e he l₁
    have m2 := measurable_sumAlong e he l₂
    have N1 := eLpNorm_sumAlong_le e he l₁ _ hp2 b hb h2
    have N2 := eLpNorm_sumAlong_le e he l₂ _ hp2 b hb h2
    obtain ⟨U, hU⟩ : ∃ U : X → ℝ, U = fun x => a₀ + a₁ * sumAlong e l₁ x + sumAlong e l₂ x := ⟨_, rfl⟩
    have mU : Measurable U := by
      rw [hU]
      exact (measurable_const.add (measurable_const.mul m1)).add m2
    have hU0 : ∀ x, 0 ≤ U x := fun x => by
      rw [hU]
      have h1 := sumAlong_nonneg e he0 l₁ x
      have h2 := sumAlong_nonneg e he0 l₂ x
      positivity
    obtain ⟨Ub, hUb⟩ : ∃ Ub : ℝ, Ub = a₀ + a₁ * (l₁.length * b) + l₂.length * b := ⟨_, rfl⟩
    have hUb0 : 0 ≤ Ub := by rw [hUb]; positivity
    have NU : eLpNorm U ((2 * q : ℕ) : ENNReal) μ ≤ ENNReal.ofReal Ub := by
      have e1 : U = ((fun _ => a₀) + fun x => a₁ * sumAlong e l₁ x) + sumAlong e l₂ := by
        rw [hU]
        rfl
      rw [e1, hUb, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add ha₀ (by positivity)]
      refine (eLpNorm_add_le (measurable_const.add (measurable_const.mul m1)).aestronglyMeasurable m2.aestronglyMeasurable hp2).trans ?_
      refine add_le_add ((eLpNorm_add_le measurable_const.aestronglyMeasurable (measurable_const.mul m1).aestronglyMeasurable hp2).trans ?_) N2
      exact add_le_add (eLpNorm_const_le_ofReal a₀ ha₀ _) (eLpNorm_const_mul_le a₁ ha₁ _ _ _ (by positivity) N1)
    have NU2 : eLpNorm (fun x => U x ^ 2) (q : ENNReal) μ ≤ ENNReal.ofReal (Ub ^ 2) := by
      refine eLpNorm_pow_le U hU0 2 (by norm_num) _ Ub hUb0 ?_
      have e1 : (q : ENNReal) * ((2 : ℕ) : ENNReal) = ((2 * q : ℕ) : ENNReal) := by
        push_cast
        ring
      rw [e1]
      exact NU
    have NUq : eLpNorm U (q : ENNReal) μ ≤ ENNReal.ofReal Ub :=
      (eLpNorm_le_eLpNorm_of_exponent_le hq2 mU.aestronglyMeasurable).trans NU
    have N1q : eLpNorm (sumAlong e l₁) (q : ENNReal) μ ≤ ENNReal.ofReal (l₁.length * b) :=
      (eLpNorm_le_eLpNorm_of_exponent_le hq2 m1.aestronglyMeasurable).trans N1
    have hpow : ∀ c, Measurable fun x => (e c x / ε) ^ 20 := fun c => ((he c).div_const ε).pow_const 20
    have Npow : ∀ c, eLpNorm (fun x => (e c x / ε) ^ 20) (q : ENNReal) μ ≤ ENNReal.ofReal ((b' / ε) ^ 20) := by
      intro c
      refine eLpNorm_pow_le (fun x => e c x / ε) (fun x => div_nonneg (he0 c x) hε.le) 20 (by norm_num) _ (b' / ε) (by positivity) ?_
      have e1 : (fun x => e c x / ε) = fun x => ε⁻¹ * e c x := by
        funext x
        rw [div_eq_inv_mul]
      have e2 : (q : ENNReal) * ((20 : ℕ) : ENNReal) = ((20 * q : ℕ) : ENNReal) := by
        push_cast
        ring
      rw [e1, e2, div_eq_inv_mul]
      exact eLpNorm_const_mul_le _ (by positivity) _ _ _ hb' (h20 c)
    have N3 := eLpNorm_sumAlong_le (fun c x => (e c x / ε) ^ 20) hpow l₂ _ hq1 ((b' / ε) ^ 20) (by positivity) Npow
    have m3 := measurable_sumAlong (fun c x => (e c x / ε) ^ 20) hpow l₂
    have hmain : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖K * U x ^ 2 + c₀ + a₂ * U x + a₃ * sumAlong e l₁ x +
        20 * sumAlong (fun c x => (e c x / ε) ^ 20) l₂ x‖ := by
      filter_upwards [hg] with x hx
      rw [Real.norm_eq_abs]
      refine hx.trans (le_trans ?_ (le_abs_self _))
      rw [hU]
    refine (eLpNorm_mono_ae hmain).trans ?_
    have mA : Measurable fun x => K * U x ^ 2 := measurable_const.mul (mU.pow_const 2)
    have mB : Measurable fun x => a₂ * U x := measurable_const.mul mU
    have mC : Measurable fun x => a₃ * sumAlong e l₁ x := measurable_const.mul m1
    have mD : Measurable fun x => 20 * sumAlong (fun c x => (e c x / ε) ^ 20) l₂ x := measurable_const.mul m3
    have e1 : (fun x => K * U x ^ 2 + c₀ + a₂ * U x + a₃ * sumAlong e l₁ x + 20 * sumAlong (fun c x => (e c x / ε) ^ 20) l₂ x) =
        ((((fun x => K * U x ^ 2) + fun _ => c₀) + fun x => a₂ * U x) + fun x => a₃ * sumAlong e l₁ x) +
          fun x => 20 * sumAlong (fun c x => (e c x / ε) ^ 20) l₂ x := rfl
    rw [e1, ← hUb]
    have p1 : 0 ≤ K * Ub ^ 2 := by positivity
    have p2 : 0 ≤ a₂ * Ub := by positivity
    have p3 : 0 ≤ a₃ * (l₁.length * b) := by positivity
    have p4 : 0 ≤ 20 * (l₂.length * (b' / ε) ^ 20) := by positivity
    rw [ENNReal.ofReal_add (by positivity) p4, ENNReal.ofReal_add (by positivity) p3, ENNReal.ofReal_add (by positivity) p2,
      ENNReal.ofReal_add p1 hc₀]
    refine (eLpNorm_add_le ((mA.add measurable_const).add mB |>.add mC).aestronglyMeasurable mD.aestronglyMeasurable hq1).trans ?_
    refine add_le_add ?_ (eLpNorm_const_mul_le 20 (by norm_num) _ _ _ (by positivity) N3)
    refine (eLpNorm_add_le ((mA.add measurable_const).add mB).aestronglyMeasurable mC.aestronglyMeasurable hq1).trans ?_
    refine add_le_add ?_ (eLpNorm_const_mul_le a₃ ha₃ _ _ _ (by positivity) N1q)
    refine (eLpNorm_add_le (mA.add measurable_const).aestronglyMeasurable mB.aestronglyMeasurable hq1).trans ?_
    refine add_le_add ?_ (eLpNorm_const_mul_le a₂ ha₂ _ _ _ hUb0 NUq)
    refine (eLpNorm_add_le mA.aestronglyMeasurable measurable_const.aestronglyMeasurable hq1).trans ?_
    exact add_le_add (eLpNorm_const_mul_le K hK _ _ _ (by positivity) NU2) (eLpNorm_const_le_ofReal c₀ hc₀ _)
  · intro X _ μ f k C x hk hx hf hm
    have hk2 : 0 < 2 * k := by omega
    have hp0 : ((2 * k : ℕ) : ENNReal) ≠ 0 := by exact_mod_cast hk2.ne'
    have hpt : ((2 * k : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
    have hr : (((2 * k : ℕ) : ENNReal)).toReal = ((2 * k : ℕ) : ℝ) := by simp
    rw [hr]
    have e1 : (fun y => ‖f y‖ₑ ^ ((2 * k : ℕ) : ℝ)) = fun y => ENNReal.ofReal (f y ^ (2 * k)) := by
      funext y
      rw [Real.enorm_of_nonneg (hf y), ENNReal.rpow_natCast, ENNReal.ofReal_pow (hf y)]
    rw [e1]
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (|C| + 1) * x ^ (-(1 / 2) : ℝ) := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by rw [ht]; positivity
    have hC1 : (1 : ℝ) ≤ |C| + 1 := by linarith [abs_nonneg C]
    have hle : C * (x ^ k)⁻¹ ≤ t ^ (2 * k) := by
      have e2 : (x ^ (-(1 / 2) : ℝ)) ^ (2 * k) = (x ^ k)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
        have : -(1 / 2 : ℝ) * ((2 * k : ℕ) : ℝ) = -(k : ℝ) := by
          push_cast
          ring
        rw [this, Real.rpow_neg hx.le, Real.rpow_natCast]
      rw [ht, mul_pow, e2]
      have h3 : C ≤ (|C| + 1) ^ (2 * k) := by
        have h4 : |C| + 1 ≤ (|C| + 1) ^ (2 * k) := le_self_pow₀ hC1 (by omega)
        linarith [le_abs_self C]
      exact mul_le_mul_of_nonneg_right h3 (by positivity)
    have hI := hm.trans (ENNReal.ofReal_le_ofReal hle)
    have hpos : (0 : ℝ) ≤ 1 / ((2 * k : ℕ) : ℝ) := by positivity
    refine (ENNReal.rpow_le_rpow hI hpos).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hpos]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0]
    have : ((2 * k : ℕ) : ℝ) * (1 / ((2 * k : ℕ) : ℝ)) = 1 := by
      have h0 : ((2 * k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hk2.ne'
      field_simp
    rw [this, Real.rpow_one]
    exact ht
end MomentMethod
end YangMills.Construction
end
