import YangMills.Construction.FreeKernel.LatticeGaussianPeriodEstimate
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open MeasureTheory YangMills.Construction.Constants.HeatKernel
namespace GaussianTimesVanishing
lemma eq_of_ordConnected_interior_empty {S : Set ℝ} (hS : S.OrdConnected)
    (hempty : ¬ (interior S).Nonempty) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : x = y := by
  have key : ∀ {a c : ℝ}, a ∈ S → c ∈ S → ¬ a < c := by
    intro a c ha hc hlt
    have hsub : Set.Ioo a c ⊆ S := Set.Ioo_subset_Icc_self.trans (hS.out ha hc)
    exact hempty ⟨(a + c) / 2, isOpen_Ioo.subset_interior_iff.mpr hsub
      ⟨by linarith, by linarith⟩⟩
  exact le_antisymm (not_lt.mp (key hy hx)) (not_lt.mp (key hx hy))
lemma enorm_iteratedDerivWithin_mul_le_sum {n : ℕ} {S : Set ℝ} {f g : ℝ → ℂ}
    (hS : S.OrdConnected) (hf : ContDiffOn ℝ n f S) (hg : ContDiffOn ℝ n g S) {θ : ℝ}
    (hθ : θ ∈ S) :
    ‖iteratedDerivWithin n (fun x => f x * g x) S θ‖ₑ ≤
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ENNReal) * ‖iteratedDerivWithin k f S θ‖ₑ *
        ‖iteratedDerivWithin (n - k) g S θ‖ₑ := by
  by_cases hint : (interior S).Nonempty
  · have hU : UniqueDiffOn ℝ S := uniqueDiffOn_convex hS.convex hint
    have hL : iteratedDerivWithin n (fun x => f x * g x) S θ =
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * iteratedDerivWithin i f S θ *
          iteratedDerivWithin (n - i) g S θ :=
      iteratedDerivWithin_mul hθ hU (hf θ hθ) (hg θ hθ)
    rw [hL]
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [enorm_mul, enorm_mul]
    gcongr
    rw [← ofReal_norm, Complex.norm_natCast, ENNReal.ofReal_natCast]
  · cases n with
    | zero => simp
    | succ m =>
      have hz : iteratedDerivWithin (m + 1) (fun x => f x * g x) S θ = 0 := by
        rw [iteratedDerivWithin_succ]
        apply derivWithin_zero_of_not_accPt
        rw [accPt_iff_nhds]
        intro h
        obtain ⟨y, ⟨_, hy⟩, hne⟩ := h _ Filter.univ_mem
        exact hne (eq_of_ordConnected_interior_empty hS hint hy hθ)
      rw [hz]
      simp
lemma power_times_gaussian_le {n b k : ℕ} {t θ : ℝ} (ht : 1 ≤ t) (hk : k ≤ n) :
    |θ| ^ (b - k) * (t ^ (((n - k : ℕ) : ℝ) / 2) * Real.exp (-(heatDecay * t * θ ^ 2))) ≤
      ((Real.sqrt t * |θ|) ^ (b - k) *
          Real.exp (-(1 / 2 * heatDecay * (Real.sqrt t * |θ|) ^ 2))) *
        (t ^ (((n : ℝ) - b) / 2) * Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2))) := by
  have ht0 : 0 < t := by linarith
  have hsq : (Real.sqrt t * |θ|) ^ 2 = t * θ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ht0.le, sq_abs]
  have hpow : Real.sqrt t ^ (b - k) = t ^ (((b - k : ℕ) : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    congr 1
    ring
  have hexp : Real.exp (-(heatDecay * t * θ ^ 2)) =
      Real.exp (-(1 / 2 * heatDecay * (t * θ ^ 2))) *
        Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hle : t ^ (((n - k : ℕ) : ℝ) / 2) ≤
      t ^ (((b - k : ℕ) : ℝ) / 2) * t ^ (((n : ℝ) - b) / 2) := by
    rw [← Real.rpow_add ht0]
    apply Real.rpow_le_rpow_of_exponent_le ht
    have h1 : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
      rw [Nat.cast_sub hk]
    have h2 : (b : ℝ) ≤ ((b - k : ℕ) : ℝ) + k := by
      exact_mod_cast (by omega : b ≤ (b - k) + k)
    rw [h1]
    linarith
  rw [hsq, mul_pow, hpow, hexp]
  have hnn : 0 ≤ |θ| ^ (b - k) * (Real.exp (-(1 / 2 * heatDecay * (t * θ ^ 2))) *
      Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2))) := by positivity
  calc _ = |θ| ^ (b - k) * (Real.exp (-(1 / 2 * heatDecay * (t * θ ^ 2))) *
          Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2))) * t ^ (((n - k : ℕ) : ℝ) / 2) := by ring
    _ ≤ |θ| ^ (b - k) * (Real.exp (-(1 / 2 * heatDecay * (t * θ ^ 2))) *
          Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2))) *
          (t ^ (((b - k : ℕ) : ℝ) / 2) * t ^ (((n : ℝ) - b) / 2)) :=
        mul_le_mul_of_nonneg_left hle hnn
    _ = _ := by ring
lemma leibniz_term_le {n b k : ℕ} {M t θ : ℝ} (hM : 0 ≤ M) (ht : 1 ≤ t) (hk : k ≤ n) {x y : ℂ}
    (hx : ‖x‖ ≤ M * |θ| ^ (b - k))
    (hy : ‖y‖ₑ ≤ weightedFactorialPower (n - k) * ENNReal.ofReal
      (t ^ (((n - k : ℕ) : ℝ) / 2) * Real.exp (-(heatDecay * t * θ ^ 2)))) :
    (n.choose k : ENNReal) * ‖x‖ₑ * ‖y‖ₑ ≤
      ENNReal.ofReal M * ((n.choose k : ENNReal) * weightedFactorialPower (n - k) *
          gaussianMoment (b - k)) *
        ENNReal.ofReal
          (t ^ (((n : ℝ) - b) / 2) * Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2))) := by
  have hx' : ‖x‖ₑ ≤ ENNReal.ofReal M * ENNReal.ofReal (|θ| ^ (b - k)) := by
    rw [← ENNReal.ofReal_mul hM, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hx
  have hY : ENNReal.ofReal ((Real.sqrt t * |θ|) ^ (b - k) *
      Real.exp (-(1 / 2 * heatDecay * (Real.sqrt t * |θ|) ^ 2))) ≤ gaussianMoment (b - k) := by
    unfold gaussianMoment halfLineSup
    exact le_iSup₂_of_le (Real.sqrt t * |θ|) (by positivity) le_rfl
  have hkey : ENNReal.ofReal (|θ| ^ (b - k)) * ENNReal.ofReal
        (t ^ (((n - k : ℕ) : ℝ) / 2) * Real.exp (-(heatDecay * t * θ ^ 2))) ≤
      gaussianMoment (b - k) * ENNReal.ofReal
        (t ^ (((n : ℝ) - b) / 2) * Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2))) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine (ENNReal.ofReal_le_ofReal (power_times_gaussian_le ht hk)).trans ?_
    rw [ENNReal.ofReal_mul (by positivity)]
    gcongr
  calc (n.choose k : ENNReal) * ‖x‖ₑ * ‖y‖ₑ
      ≤ (n.choose k : ENNReal) * (ENNReal.ofReal M * ENNReal.ofReal (|θ| ^ (b - k))) *
          (weightedFactorialPower (n - k) * ENNReal.ofReal
            (t ^ (((n - k : ℕ) : ℝ) / 2) * Real.exp (-(heatDecay * t * θ ^ 2)))) := by
        gcongr
    _ = ENNReal.ofReal M * ((n.choose k : ENNReal) * weightedFactorialPower (n - k)) *
          (ENNReal.ofReal (|θ| ^ (b - k)) * ENNReal.ofReal
            (t ^ (((n - k : ℕ) : ℝ) / 2) * Real.exp (-(heatDecay * t * θ ^ 2)))) := by ring
    _ ≤ ENNReal.ofReal M * ((n.choose k : ENNReal) * weightedFactorialPower (n - k)) *
          (gaussianMoment (b - k) * ENNReal.ofReal
            (t ^ (((n : ℝ) - b) / 2) * Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2)))) := by
        gcongr
    _ = _ := by ring
lemma lintegral_rpow_mul_gaussian {t : ℝ} (ht : 1 ≤ t) (p : ℝ) :
    ∫⁻ θ : ℝ, ENNReal.ofReal (t ^ p * Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2))) =
      ENNReal.ofReal (Real.pi ^ ((3 : ℝ) / 2) * t ^ (p - 1 / 2)) := by apply _root_.YangMills.Construction.FreeKernel.LatticeGaussianPeriod.lintegral_rpow_mul_gaussian_half <;> assumption
lemma enorm_iteratedDerivWithin_mul_le_gaussian {n b : ℕ} {M t : ℝ} {S : Set ℝ} {f g : ℝ → ℂ}
    (hM : 0 ≤ M) (ht : 1 ≤ t)
    (hS : S.OrdConnected) (hf : ContDiffOn ℝ n f S) (hg : ContDiffOn ℝ n g S)
    (h : ∀ k : ℕ, k ≤ n → ∀ θ ∈ S,
      ‖iteratedDerivWithin k f S θ‖ ≤ M * |θ| ^ (b - k) ∧
      ‖iteratedDerivWithin k g S θ‖ₑ ≤
        weightedFactorialPower k *
          ENNReal.ofReal (t ^ ((k : ℝ) / 2) * Real.exp (-(heatDecay * t * θ ^ 2))))
    {θ : ℝ} (hθ : θ ∈ S) :
    ‖iteratedDerivWithin n (fun x => f x * g x) S θ‖ₑ ≤
      ENNReal.ofReal M * binomialMoment n b *
        ENNReal.ofReal
          (t ^ (((n : ℝ) - b) / 2) * Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2))) := by
  refine (enorm_iteratedDerivWithin_mul_le_sum hS hf hg hθ).trans ?_
  rw [binomialMoment, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact leibniz_term_le hM ht hkn (h k hkn θ hθ).1 (h (n - k) (Nat.sub_le _ _) θ hθ).2
end GaussianTimesVanishing
open GaussianTimesVanishing in
theorem vanishingTimesGaussianBound_holds : VanishingTimesGaussianBound := by
  intro n b M t S f g hM ht hS hf hg h
  have hpt := fun θ (hθ : θ ∈ S) => enorm_iteratedDerivWithin_mul_le_gaussian hM ht hS hf hg h hθ
  refine ⟨hpt, ?_⟩
  have hmeas : Measurable fun θ : ℝ => ENNReal.ofReal
      (t ^ (((n : ℝ) - b) / 2) * Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2))) := by
    fun_prop
  have hexp : ((n : ℝ) - b) / 2 - 1 / 2 = ((n : ℝ) - b - 1) / 2 := by ring
  calc ∫⁻ θ in S, ‖iteratedDerivWithin n (fun x => f x * g x) S θ‖ₑ
      ≤ ∫⁻ θ in S, ENNReal.ofReal M * binomialMoment n b * ENNReal.ofReal
          (t ^ (((n : ℝ) - b) / 2) * Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2))) :=
        setLIntegral_mono' hS.measurableSet hpt
    _ = ENNReal.ofReal M * binomialMoment n b * ∫⁻ θ in S, ENNReal.ofReal
          (t ^ (((n : ℝ) - b) / 2) * Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2))) :=
        lintegral_const_mul _ hmeas
    _ ≤ ENNReal.ofReal M * binomialMoment n b * ∫⁻ θ : ℝ, ENNReal.ofReal
          (t ^ (((n : ℝ) - b) / 2) * Real.exp (-(1 / 2 * heatDecay * t * θ ^ 2))) := mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
    _ = ENNReal.ofReal M * binomialMoment n b * ENNReal.ofReal
          (Real.pi ^ ((3 : ℝ) / 2) * t ^ (((n : ℝ) - b) / 2 - 1 / 2)) := by
        rw [lintegral_rpow_mul_gaussian ht]
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), hexp]
        ring
end YangMills.Construction.FreeKernel
