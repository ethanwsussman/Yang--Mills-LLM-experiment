import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfAWeightedMean
import YangMills.Construction.ColdStepAtMirrorFrames.MeanAlongAParameter
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
namespace GibbsMeanAlongSegment
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ}
structure DerivBounds (μ : Measure Ω) (A H : (Fin k → ℝ) → Ω → ℝ) (τ : Fin k → ℝ) (R : ℝ) : Prop where
  bound_zero : ∀ᵐ ω ∂μ, |H τ ω| ≤ R
  weight_one : ∀ u, ∀ᵐ ω ∂μ, |paramIteratedDeriv A ![u] τ ω| ≤ R * ‖u‖
  energy_one : ∀ u, ∀ᵐ ω ∂μ, |paramIteratedDeriv H ![u] τ ω| ≤ R * ‖u‖
  weight_two : ∀ u w, ∀ᵐ ω ∂μ, |paramIteratedDeriv A ![u, w] τ ω| ≤ R * (‖u‖ * ‖w‖)
  energy_two : ∀ u w, ∀ᵐ ω ∂μ, |paramIteratedDeriv H ![u, w] τ ω| ≤ R * (‖u‖ * ‖w‖)
  weight_three : ∀ u w z, ∀ᵐ ω ∂μ, |paramIteratedDeriv A ![u, w, z] τ ω| ≤ R * (‖u‖ * ‖w‖ * ‖z‖)
  energy_three : ∀ u w z, ∀ᵐ ω ∂μ, |paramIteratedDeriv H ![u, w, z] τ ω| ≤ R * (‖u‖ * ‖w‖ * ‖z‖)
private theorem abs_paramIteratedDeriv_le {G : (Fin k → ℝ) → Ω → ℝ} {B : Set (Fin k → ℝ)} {K R : ℝ}
    {τ : Fin k → ℝ} (hG : IsDominatedSmoothFamily μ 3 B K G) (hτ : τ ∈ B) (hKR : K ≤ R) {j : ℕ}
    (hj : j ≤ 3) (m : Fin j → Fin k → ℝ) : ∀ᵐ ω ∂μ, |paramIteratedDeriv G m τ ω| ≤ R * ∏ i, ‖m i‖ := by
  filter_upwards [hG.norm_iteratedFDeriv_le] with ω hω
  have h1 := (iteratedFDeriv ℝ j (fun τ' => G τ' ω) τ).le_opNorm m
  have hp : 0 ≤ ∏ i, ‖m i‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  calc |paramIteratedDeriv G m τ ω| ≤ ‖iteratedFDeriv ℝ j (fun τ' => G τ' ω) τ‖ * ∏ i, ‖m i‖ := h1
    _ ≤ R * ∏ i, ‖m i‖ := mul_le_mul_of_nonneg_right (le_trans (hω j hj τ hτ) hKR) hp
private theorem derivBounds_of_dominated {A H : (Fin k → ℝ) → Ω → ℝ} {B : Set (Fin k → ℝ)} {K R : ℝ}
    {τ : Fin k → ℝ} (HA : IsDominatedSmoothFamily μ 3 B K A) (HH : IsDominatedSmoothFamily μ 3 B K H)
    (hτ : τ ∈ B) (hKR : K ≤ R) : DerivBounds μ A H τ R := by
  refine ⟨?_, fun u => ?_, fun u => ?_, fun u w => ?_, fun u w => ?_, fun u w z => ?_, fun u w z => ?_⟩
  · filter_upwards [HH.norm_iteratedFDeriv_le] with ω hω
    have h0 := hω 0 (Nat.zero_le _) τ hτ
    rw [norm_iteratedFDeriv_zero] at h0
    exact le_trans h0 hKR
  · simpa using abs_paramIteratedDeriv_le HA hτ hKR (j := 1) (by norm_num) ![u]
  · simpa using abs_paramIteratedDeriv_le HH hτ hKR (j := 1) (by norm_num) ![u]
  · simpa [Fin.prod_univ_two] using abs_paramIteratedDeriv_le HA hτ hKR (j := 2) (by norm_num) ![u, w]
  · simpa [Fin.prod_univ_two] using abs_paramIteratedDeriv_le HH hτ hKR (j := 2) (by norm_num) ![u, w]
  · simpa [Fin.prod_univ_three, mul_assoc] using
      abs_paramIteratedDeriv_le HA hτ hKR (j := 3) (by norm_num) ![u, w, z]
  · simpa [Fin.prod_univ_three, mul_assoc] using
      abs_paramIteratedDeriv_le HH hτ hKR (j := 3) (by norm_num) ![u, w, z]
private theorem abs_sub_le_of_bounds_one {R a t1 t2 : ℝ} (hR : 1 ≤ R) (ha : 0 ≤ a) (b1 : |t1| ≤ R * a)
    (b2 : |t2| ≤ 2 * (R * (R * a))) : |t1 - t2| ≤ 100 * R ^ 4 * a := by
  have e1 : R * a ≤ R ^ 4 * a := by
    apply mul_le_mul_of_nonneg_right _ ha
    calc R = R ^ 1 := (pow_one R).symm
      _ ≤ R ^ 4 := pow_le_pow_right₀ hR (by norm_num)
  have e2 : R ^ 2 * a ≤ R ^ 4 * a :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR (by norm_num)) ha
  have g0 : 0 ≤ R ^ 4 * a := by positivity
  obtain ⟨p1, p2⟩ := abs_le.mp b1
  obtain ⟨q1, q2⟩ := abs_le.mp b2
  rw [abs_le]
  constructor <;> nlinarith
private theorem abs_sub_le_of_bounds_two {R a b t1 t2 t3 t4 t5 : ℝ} (hR : 1 ≤ R) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (b1 : |t1| ≤ R * (a * b)) (b2 : |t2| ≤ 2 * (R * b * (R * a)))
    (b3 : |t3| ≤ 2 * (R * a * (R * b))) (b4 : |t4| ≤ 2 * (R * (R * (a * b))))
    (b5 : |t5| ≤ 6 * (R * (R * b) * (R * a))) :
    |t1 - t2 - t3 - t4 + t5| ≤ 100 * R ^ 4 * (a * b) := by
  have hp : 0 ≤ a * b := by positivity
  have e1 : R * (a * b) ≤ R ^ 4 * (a * b) := by
    apply mul_le_mul_of_nonneg_right _ hp
    calc R = R ^ 1 := (pow_one R).symm
      _ ≤ R ^ 4 := pow_le_pow_right₀ hR (by norm_num)
  have e2 : R ^ 2 * (a * b) ≤ R ^ 4 * (a * b) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR (by norm_num)) hp
  have e3 : R ^ 3 * (a * b) ≤ R ^ 4 * (a * b) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR (by norm_num)) hp
  have g0 : 0 ≤ R ^ 4 * (a * b) := by positivity
  have c2 : R * b * (R * a) = R ^ 2 * (a * b) := by ring
  have c3 : R * a * (R * b) = R ^ 2 * (a * b) := by ring
  have c4 : R * (R * (a * b)) = R ^ 2 * (a * b) := by ring
  have c5 : R * (R * b) * (R * a) = R ^ 3 * (a * b) := by ring
  rw [c2] at b2
  rw [c3] at b3
  rw [c4] at b4
  rw [c5] at b5
  obtain ⟨p1, p2⟩ := abs_le.mp b1
  obtain ⟨q1, q2⟩ := abs_le.mp b2
  obtain ⟨r1, r2⟩ := abs_le.mp b3
  obtain ⟨s1, s2⟩ := abs_le.mp b4
  obtain ⟨u1, u2⟩ := abs_le.mp b5
  rw [abs_le]
  constructor <;> linarith
private theorem abs_sub_le_of_bounds_three {R a b c t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 : ℝ}
    (hR : 1 ≤ R) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (b1 : |t1| ≤ R * (a * b * c))
    (b2 : |t2| ≤ 2 * (R * (b * c) * (R * a))) (b3 : |t3| ≤ 2 * (R * (a * c) * (R * b)))
    (b4 : |t4| ≤ 2 * (R * (a * b) * (R * c))) (b5 : |t5| ≤ 2 * (R * c * (R * (a * b))))
    (b6 : |t6| ≤ 2 * (R * b * (R * (a * c)))) (b7 : |t7| ≤ 2 * (R * a * (R * (b * c))))
    (b8 : |t8| ≤ 6 * (R * c * (R * b) * (R * a))) (b9 : |t9| ≤ 6 * (R * b * (R * c) * (R * a)))
    (b10 : |t10| ≤ 6 * (R * a * (R * c) * (R * b))) (b11 : |t11| ≤ 2 * (R * (R * (a * b * c))))
    (b12 : |t12| ≤ 6 * (R * (R * (b * c)) * (R * a))) (b13 : |t13| ≤ 6 * (R * (R * (a * c)) * (R * b)))
    (b14 : |t14| ≤ 6 * (R * (R * (a * b)) * (R * c)))
    (b15 : |t15| ≤ 26 * (R * (R * c) * (R * b) * (R * a))) :
    |t1 - t2 - t3 - t4 - t5 - t6 - t7 + t8 + t9 + t10 - t11 + t12 + t13 + t14 - t15| ≤
      100 * R ^ 4 * (a * b * c) := by
  set p := a * b * c with hpdef
  have hp : 0 ≤ p := by positivity
  have e1 : R * p ≤ R ^ 4 * p := by
    apply mul_le_mul_of_nonneg_right _ hp
    calc R = R ^ 1 := (pow_one R).symm
      _ ≤ R ^ 4 := pow_le_pow_right₀ hR (by norm_num)
  have e2 : R ^ 2 * p ≤ R ^ 4 * p :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR (by norm_num)) hp
  have e3 : R ^ 3 * p ≤ R ^ 4 * p :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR (by norm_num)) hp
  have g0 : 0 ≤ R ^ 4 * p := by positivity
  have c2 : R * (b * c) * (R * a) = R ^ 2 * p := by rw [hpdef]; ring
  have c3 : R * (a * c) * (R * b) = R ^ 2 * p := by rw [hpdef]; ring
  have c4 : R * (a * b) * (R * c) = R ^ 2 * p := by rw [hpdef]; ring
  have c5 : R * c * (R * (a * b)) = R ^ 2 * p := by rw [hpdef]; ring
  have c6 : R * b * (R * (a * c)) = R ^ 2 * p := by rw [hpdef]; ring
  have c7 : R * a * (R * (b * c)) = R ^ 2 * p := by rw [hpdef]; ring
  have c8 : R * c * (R * b) * (R * a) = R ^ 3 * p := by rw [hpdef]; ring
  have c9 : R * b * (R * c) * (R * a) = R ^ 3 * p := by rw [hpdef]; ring
  have c10 : R * a * (R * c) * (R * b) = R ^ 3 * p := by rw [hpdef]; ring
  have c11 : R * (R * p) = R ^ 2 * p := by ring
  have c12 : R * (R * (b * c)) * (R * a) = R ^ 3 * p := by rw [hpdef]; ring
  have c13 : R * (R * (a * c)) * (R * b) = R ^ 3 * p := by rw [hpdef]; ring
  have c14 : R * (R * (a * b)) * (R * c) = R ^ 3 * p := by rw [hpdef]; ring
  have c15 : R * (R * c) * (R * b) * (R * a) = R ^ 4 * p := by rw [hpdef]; ring
  rw [c2] at b2
  rw [c3] at b3
  rw [c4] at b4
  rw [c5] at b5
  rw [c6] at b6
  rw [c7] at b7
  rw [c8] at b8
  rw [c9] at b9
  rw [c10] at b10
  rw [c11] at b11
  rw [c12] at b12
  rw [c13] at b13
  rw [c14] at b14
  rw [c15] at b15
  obtain ⟨p1, q1⟩ := abs_le.mp b1
  obtain ⟨p2, q2⟩ := abs_le.mp b2
  obtain ⟨p3, q3⟩ := abs_le.mp b3
  obtain ⟨p4, q4⟩ := abs_le.mp b4
  obtain ⟨p5, q5⟩ := abs_le.mp b5
  obtain ⟨p6, q6⟩ := abs_le.mp b6
  obtain ⟨p7, q7⟩ := abs_le.mp b7
  obtain ⟨p8, q8⟩ := abs_le.mp b8
  obtain ⟨p9, q9⟩ := abs_le.mp b9
  obtain ⟨p10, q10⟩ := abs_le.mp b10
  obtain ⟨p11, q11⟩ := abs_le.mp b11
  obtain ⟨p12, q12⟩ := abs_le.mp b12
  obtain ⟨p13, q13⟩ := abs_le.mp b13
  obtain ⟨p14, q14⟩ := abs_le.mp b14
  obtain ⟨p15, q15⟩ := abs_le.mp b15
  rw [abs_le]
  constructor <;> linarith
private theorem abs_gibbsMean_le (hZ : GibbsMeanBounds) {A' f : Ω → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ᵐ ω ∂μ, |f ω| ≤ c) : |gibbsMean μ A' f| ≤ c :=
  (hZ Ω μ A' f (fun _ => 0) (fun _ => 0) (fun _ => 0) c 0 0 0 hc le_rfl le_rfl le_rfl
    hf (by simp) (by simp) (by simp)).1
private theorem abs_gibbsCovariance_le (hZ : GibbsMeanBounds) {A' f g : Ω → ℝ} {c d : ℝ} (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hf : ∀ᵐ ω ∂μ, |f ω| ≤ c) (hg : ∀ᵐ ω ∂μ, |g ω| ≤ d) :
    |gibbsCovariance μ A' f g| ≤ 2 * (c * d) :=
  (hZ Ω μ A' f g (fun _ => 0) (fun _ => 0) c d 0 0 hc hd le_rfl le_rfl hf hg (by simp) (by simp)).2.1
private theorem abs_gibbsCumulantThree_le (hZ : GibbsMeanBounds) {A' f g h : Ω → ℝ} {c d e : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (hf : ∀ᵐ ω ∂μ, |f ω| ≤ c) (hg : ∀ᵐ ω ∂μ, |g ω| ≤ d)
    (hh : ∀ᵐ ω ∂μ, |h ω| ≤ e) : |gibbsCumulantThree μ A' f g h| ≤ 6 * (c * d * e) :=
  (hZ Ω μ A' f g h (fun _ => 0) c d e 0 hc hd he le_rfl hf hg hh (by simp)).2.2.1
private theorem abs_gibbsCumulantFour_le (hZ : GibbsMeanBounds) {A' f g h l : Ω → ℝ} {c d e r : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (hr : 0 ≤ r) (hf : ∀ᵐ ω ∂μ, |f ω| ≤ c)
    (hg : ∀ᵐ ω ∂μ, |g ω| ≤ d) (hh : ∀ᵐ ω ∂μ, |h ω| ≤ e) (hl : ∀ᵐ ω ∂μ, |l ω| ≤ r) :
    |gibbsCumulantFour μ A' f g h l| ≤ 26 * (c * d * e * r) :=
  (hZ Ω μ A' f g h l c d e r hc hd he hr hf hg hh hl).2.2.2
private theorem abs_firstDerivExpansion_le (hZ : GibbsMeanBounds) {A H : (Fin k → ℝ) → Ω → ℝ}
    {τ : Fin k → ℝ} {R : ℝ} (hR : 1 ≤ R) (S : DerivBounds μ A H τ R) (u : Fin k → ℝ) :
    |gibbsMean μ (A τ) (paramIteratedDeriv H ![u] τ) -
      gibbsCovariance μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ)| ≤ 100 * R ^ 4 * ‖u‖ := by
  have hR0 : 0 ≤ R := by linarith
  have hu := norm_nonneg u
  exact abs_sub_le_of_bounds_one hR hu (abs_gibbsMean_le hZ (by positivity) (S.energy_one u))
    (abs_gibbsCovariance_le hZ hR0 (by positivity) S.bound_zero (S.weight_one u))
private theorem abs_secondDerivExpansion_le (hZ : GibbsMeanBounds) {A H : (Fin k → ℝ) → Ω → ℝ}
    {τ : Fin k → ℝ} {R : ℝ} (hR : 1 ≤ R) (S : DerivBounds μ A H τ R) (u v : Fin k → ℝ) :
    |gibbsMean μ (A τ) (paramIteratedDeriv H ![v, u] τ) -
        gibbsCovariance μ (A τ) (paramIteratedDeriv H ![u] τ) (paramIteratedDeriv A ![v] τ) -
        gibbsCovariance μ (A τ) (paramIteratedDeriv H ![v] τ) (paramIteratedDeriv A ![u] τ) -
        gibbsCovariance μ (A τ) (H τ) (paramIteratedDeriv A ![v, u] τ) +
        gibbsCumulantThree μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ) (paramIteratedDeriv A ![v] τ)| ≤
      100 * R ^ 4 * (‖v‖ * ‖u‖) := by
  have hR0 : 0 ≤ R := by linarith
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  exact abs_sub_le_of_bounds_two hR hv hu (abs_gibbsMean_le hZ (by positivity) (S.energy_two v u))
    (abs_gibbsCovariance_le hZ (by positivity) (by positivity) (S.energy_one u) (S.weight_one v))
    (abs_gibbsCovariance_le hZ (by positivity) (by positivity) (S.energy_one v) (S.weight_one u))
    (abs_gibbsCovariance_le hZ hR0 (by positivity) S.bound_zero (S.weight_two v u))
    (abs_gibbsCumulantThree_le hZ hR0 (by positivity) (by positivity) S.bound_zero (S.weight_one u)
      (S.weight_one v))
private theorem abs_thirdDerivExpansion_le (hZ : GibbsMeanBounds) {A H : (Fin k → ℝ) → Ω → ℝ}
    {τ : Fin k → ℝ} {R : ℝ} (hR : 1 ≤ R) (S : DerivBounds μ A H τ R) (u v w : Fin k → ℝ) :
    |gibbsMean μ (A τ) (paramIteratedDeriv H ![w, v, u] τ) -
        gibbsCovariance μ (A τ) (paramIteratedDeriv H ![v, u] τ) (paramIteratedDeriv A ![w] τ) -
        gibbsCovariance μ (A τ) (paramIteratedDeriv H ![w, u] τ) (paramIteratedDeriv A ![v] τ) -
        gibbsCovariance μ (A τ) (paramIteratedDeriv H ![w, v] τ) (paramIteratedDeriv A ![u] τ) -
        gibbsCovariance μ (A τ) (paramIteratedDeriv H ![u] τ) (paramIteratedDeriv A ![w, v] τ) -
        gibbsCovariance μ (A τ) (paramIteratedDeriv H ![v] τ) (paramIteratedDeriv A ![w, u] τ) -
        gibbsCovariance μ (A τ) (paramIteratedDeriv H ![w] τ) (paramIteratedDeriv A ![v, u] τ) +
        gibbsCumulantThree μ (A τ) (paramIteratedDeriv H ![u] τ) (paramIteratedDeriv A ![v] τ)
          (paramIteratedDeriv A ![w] τ) +
        gibbsCumulantThree μ (A τ) (paramIteratedDeriv H ![v] τ) (paramIteratedDeriv A ![u] τ)
          (paramIteratedDeriv A ![w] τ) +
        gibbsCumulantThree μ (A τ) (paramIteratedDeriv H ![w] τ) (paramIteratedDeriv A ![u] τ)
          (paramIteratedDeriv A ![v] τ) -
        gibbsCovariance μ (A τ) (H τ) (paramIteratedDeriv A ![w, v, u] τ) +
        gibbsCumulantThree μ (A τ) (H τ) (paramIteratedDeriv A ![v, u] τ) (paramIteratedDeriv A ![w] τ) +
        gibbsCumulantThree μ (A τ) (H τ) (paramIteratedDeriv A ![w, u] τ) (paramIteratedDeriv A ![v] τ) +
        gibbsCumulantThree μ (A τ) (H τ) (paramIteratedDeriv A ![w, v] τ) (paramIteratedDeriv A ![u] τ) -
        gibbsCumulantFour μ (A τ) (H τ) (paramIteratedDeriv A ![u] τ) (paramIteratedDeriv A ![v] τ)
          (paramIteratedDeriv A ![w] τ)| ≤ 100 * R ^ 4 * (‖w‖ * ‖v‖ * ‖u‖) := by
  have hR0 : 0 ≤ R := by linarith
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  have hw := norm_nonneg w
  exact abs_sub_le_of_bounds_three hR hw hv hu (abs_gibbsMean_le hZ (by positivity) (S.energy_three w v u))
    (abs_gibbsCovariance_le hZ (by positivity) (by positivity) (S.energy_two v u) (S.weight_one w))
    (abs_gibbsCovariance_le hZ (by positivity) (by positivity) (S.energy_two w u) (S.weight_one v))
    (abs_gibbsCovariance_le hZ (by positivity) (by positivity) (S.energy_two w v) (S.weight_one u))
    (abs_gibbsCovariance_le hZ (by positivity) (by positivity) (S.energy_one u) (S.weight_two w v))
    (abs_gibbsCovariance_le hZ (by positivity) (by positivity) (S.energy_one v) (S.weight_two w u))
    (abs_gibbsCovariance_le hZ (by positivity) (by positivity) (S.energy_one w) (S.weight_two v u))
    (abs_gibbsCumulantThree_le hZ (by positivity) (by positivity) (by positivity) (S.energy_one u)
      (S.weight_one v) (S.weight_one w))
    (abs_gibbsCumulantThree_le hZ (by positivity) (by positivity) (by positivity) (S.energy_one v)
      (S.weight_one u) (S.weight_one w))
    (abs_gibbsCumulantThree_le hZ (by positivity) (by positivity) (by positivity) (S.energy_one w)
      (S.weight_one u) (S.weight_one v))
    (abs_gibbsCovariance_le hZ hR0 (by positivity) S.bound_zero (S.weight_three w v u))
    (abs_gibbsCumulantThree_le hZ hR0 (by positivity) (by positivity) S.bound_zero (S.weight_two v u)
      (S.weight_one w))
    (abs_gibbsCumulantThree_le hZ hR0 (by positivity) (by positivity) S.bound_zero (S.weight_two w u)
      (S.weight_one v))
    (abs_gibbsCumulantThree_le hZ hR0 (by positivity) (by positivity) S.bound_zero (S.weight_two w v)
      (S.weight_one u))
    (abs_gibbsCumulantFour_le hZ hR0 (by positivity) (by positivity) (by positivity) S.bound_zero
      (S.weight_one u) (S.weight_one v) (S.weight_one w))
private theorem continuousOn_gibbsMean [IsFiniteMeasure μ] (hμ : μ ≠ 0) {A H : ℝ → Ω → ℝ} {R : ℝ}
    (hAm : ∀ v ∈ Set.Icc (0 : ℝ) 1, AEStronglyMeasurable (A v) μ)
    (hHm : ∀ v ∈ Set.Icc (0 : ℝ) 1, AEStronglyMeasurable (H v) μ)
    (hAb : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ ω ∂μ, |A v ω| ≤ R)
    (hHb : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ ω ∂μ, |H v ω| ≤ R)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun v => A v ω) (Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn (fun v => H v ω) (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun v => gibbsMean μ (A v) (H v)) (Set.Icc (0 : ℝ) 1) := by
  have hexpm : ∀ v ∈ Set.Icc (0 : ℝ) 1, AEStronglyMeasurable (fun ω => Real.exp (- A v ω)) μ :=
    fun v hv => Real.continuous_exp.comp_aestronglyMeasurable (hAm v hv).neg
  have hexpb : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ ω ∂μ, ‖Real.exp (- A v ω)‖ ≤ Real.exp R := fun v hv => by
    filter_upwards [hAb v hv] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hω).1])
  have hD : ContinuousOn (fun v => ∫ ω, Real.exp (- A v ω) ∂μ) (Set.Icc (0 : ℝ) 1) := by
    apply continuousOn_of_dominated hexpm hexpb (integrable_const _)
    filter_upwards [hc] with ω hω
    exact Real.continuous_exp.comp_continuousOn hω.1.neg
  have hN : ContinuousOn (fun v => ∫ ω, H v ω * Real.exp (- A v ω) ∂μ) (Set.Icc (0 : ℝ) 1) := by
    apply continuousOn_of_dominated (bound := fun _ => |R| * Real.exp R)
      (fun v hv => (hHm v hv).mul (hexpm v hv)) _ (integrable_const _)
    · filter_upwards [hc] with ω hω
      exact hω.2.mul (Real.continuous_exp.comp_continuousOn hω.1.neg)
    · intro v hv
      filter_upwards [hHb v hv, hexpb v hv] with ω h1 h2
      change ‖H v ω * Real.exp (- A v ω)‖ ≤ _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (le_trans h1 (le_abs_self R)) h2 (norm_nonneg _) (abs_nonneg _)
  refine hN.div hD fun v hv => ?_
  have hint : Integrable (fun ω => Real.exp (- A v ω)) μ :=
    Integrable.of_bound (hexpm v hv) (Real.exp R) (hexpb v hv)
  have hpos : 0 < ∫ ω, Real.exp (- A v ω) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun ω => (Real.exp_pos _).le) hint]
    have : Function.support (fun ω => Real.exp (- A v ω)) = Set.univ := by
      ext ω
      simp [(Real.exp_pos _).ne']
    rw [this]
    exact Measure.measure_univ_pos.mpr hμ
  exact hpos.ne'
abbrev _root_.YangMills.SharedProofs.p92269 := @continuousOn_gibbsMean
end GibbsMeanAlongSegment
open GibbsMeanAlongSegment in
theorem intervalIntegralGibbsMeanDifferentiation_holds (hZ : GibbsMeanBounds)
    (hD : GibbsMeanDifferentiation) : IntervalIntegralGibbsMeanDifferentiation := by
  obtain ⟨hI, hM⟩ := hD
  intro Ω _ μ _ k B K A H hB hμ hA hH hcont
  set R : ℝ := |K| + 1 with hR
  have hR1 : 1 ≤ R := by
    have := abs_nonneg K
    linarith
  have hR0 : 0 ≤ R := by linarith
  have hKR : K ≤ R := by
    have := le_abs_self K
    linarith
  set μ' : Measure ℝ := volume.restrict (Set.Ioc 0 1) with hμ'
  have hfin : IsFiniteMeasure μ' := ⟨by
    rw [hμ', Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  set G : (Fin k → ℝ) → ℝ → ℝ := fun τ v => gibbsMean μ (A v τ) (H v τ) with hG
  have hmem : ∀ᵐ v ∂μ', v ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact Set.Ioc_subset_Icc_self hv
  have habs : ∀ {F : (Fin k → ℝ) → Ω → ℝ} {τ : Fin k → ℝ}, τ ∈ B → IsDominatedSmoothFamily μ 3 B K F →
      ∀ᵐ ω ∂μ, |F τ ω| ≤ R := fun {F τ} hτ hF => by
    filter_upwards [hF.norm_iteratedFDeriv_le] with ω hω
    have h0 := hω 0 (Nat.zero_le _) τ hτ
    rw [norm_iteratedFDeriv_zero] at h0
    exact le_trans h0 hKR
  have hdom : IsDominatedSmoothFamily μ' 3 B (100 * R ^ 4) G := by
    refine ⟨fun τ hτ => ?_, ?_, ?_⟩
    · have hc := continuousOn_gibbsMean (A := fun v => A v τ) (H := fun v => H v τ) (R := R) hμ
        (fun v hv => (hA v hv).aestronglyMeasurable τ hτ) (fun v hv => (hH v hv).aestronglyMeasurable τ hτ)
        (fun v hv => habs hτ (hA v hv)) (fun v hv => habs hτ (hH v hv)) (hcont τ hτ)
      have h1 : AEStronglyMeasurable (G τ) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
        hc.aestronglyMeasurable measurableSet_Icc
      exact h1.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
    · filter_upwards [hmem] with v hv
      exact (hM Ω μ k B K (A v) (H v) hB hμ (hA v hv) (hH v hv)).1
    · filter_upwards [hmem] with v hv j hj τ hτ
      obtain ⟨-, hform⟩ := hM Ω μ k B K (A v) (H v) hB hμ (hA v hv) (hH v hv)
      have S : DerivBounds μ (A v) (H v) τ R := derivBounds_of_dominated (hA v hv) (hH v hv) hτ hKR
      have hpos4 : 0 ≤ 100 * R ^ 4 := by positivity
      interval_cases j
      · rw [norm_iteratedFDeriv_zero]
        have h1 : |gibbsMean μ (A v τ) (H v τ)| ≤ R :=
          (hZ Ω μ (A v τ) (H v τ) (fun _ => 0) (fun _ => 0) (fun _ => 0) R 0 0 0 hR0 le_rfl le_rfl le_rfl
            S.bound_zero (by simp) (by simp) (by simp)).1
        have h100 : R ≤ 100 * R ^ 4 := by
          have : R ≤ R ^ 4 := by
            calc R = R ^ 1 := (pow_one R).symm
              _ ≤ R ^ 4 := pow_le_pow_right₀ hR1 (by norm_num)
          have h0 : 0 ≤ R ^ 4 := by positivity
          linarith
        exact le_trans h1 h100
      · refine ContinuousMultilinearMap.opNorm_le_bound hpos4 fun m => ?_
        have key := abs_firstDerivExpansion_le hZ hR1 S (m 0)
        rw [← (hform τ hτ (m 0) (m 0) (m 0)).1] at key
        have hm : ![m 0] = m := by
          ext i
          fin_cases i
          rfl
        rw [hm] at key
        simpa using key
      · refine ContinuousMultilinearMap.opNorm_le_bound hpos4 fun m => ?_
        have key := abs_secondDerivExpansion_le hZ hR1 S (m 1) (m 0)
        rw [← (hform τ hτ (m 1) (m 0) (m 0)).2.1] at key
        have hm : ![m 0, m 1] = m := by
          ext i
          fin_cases i <;> rfl
        rw [hm] at key
        simpa [Fin.prod_univ_two] using key
      · refine ContinuousMultilinearMap.opNorm_le_bound hpos4 fun m => ?_
        have key := abs_thirdDerivExpansion_le hZ hR1 S (m 2) (m 1) (m 0)
        rw [← (hform τ hτ (m 2) (m 1) (m 0)).2.2] at key
        have hm : ![m 0, m 1, m 2] = m := by
          ext i
          fin_cases i <;> rfl
        rw [hm] at key
        simpa [Fin.prod_univ_three] using key
  obtain ⟨h1, h2⟩ := hI ℝ μ' k 3 B _ G hB hdom
  have hint : ∀ g : ℝ → ℝ, ∫ v in (0 : ℝ)..1, g v = ∫ v, g v ∂μ' := fun g =>
    intervalIntegral.integral_of_le zero_le_one
  have hfun : (fun τ => ∫ v in (0 : ℝ)..1, gibbsMean μ (A v τ) (H v τ)) = fun τ => ∫ v, G τ v ∂μ' := by
    funext τ
    exact hint _
  refine ⟨by rw [hfun]; exact h1, fun τ hτ j hj w => ?_⟩
  rw [hfun, h2 τ hτ j hj w, hint]
  rfl
end ColdStepAtMirrorFrames
end YangMills.Construction
end
