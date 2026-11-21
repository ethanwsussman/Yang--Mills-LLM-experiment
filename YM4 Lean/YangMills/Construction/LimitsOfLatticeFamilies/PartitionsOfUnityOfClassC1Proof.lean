import YangMills.Construction.LimitsOfLatticeFamilies.FactsOfTheSetting
import YangMills.Construction.LimitsOfLatticeFamilies.PartitionsOfUnityOfClassC1
import YangMills.Construction.PassageToTheLimit.PartitionOfUnityOfClassC1WithSmallPiecesProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits.C1PartitionOfUnity.Existence
open ModelSpace
def cosSqHalfPi (t : ℝ) : ℝ := Real.cos (Real.pi * t / 2) ^ 2
theorem hasDerivAt_cosSqHalfPi (t : ℝ) :
    HasDerivAt cosSqHalfPi (-(Real.pi / 2) * Real.sin (Real.pi * t)) t := by
  have h1 : HasDerivAt (fun u : ℝ => Real.pi * u / 2) (Real.pi / 2) t := by
    simpa using ((hasDerivAt_id t).const_mul Real.pi).div_const 2
  have h2 := (h1.cos).pow 2
  have h3 : Real.sin (Real.pi * t) =
      2 * Real.sin (Real.pi * t / 2) * Real.cos (Real.pi * t / 2) := by
    rw [← Real.sin_two_mul]
    congr 1
    ring
  refine h2.congr_deriv ?_
  rw [h3]
  simp only [Nat.cast_ofNat]
  ring
def cosBump (t : ℝ) : ℝ := if |t| ≤ 1 then cosSqHalfPi t else 0
def cosBumpDeriv (t : ℝ) : ℝ := if |t| ≤ 1 then -(Real.pi / 2) * Real.sin (Real.pi * t) else 0
def cosBumpRight (t : ℝ) : ℝ := if t ≤ 1 then cosSqHalfPi t else 0
def cosBumpRightDeriv (t : ℝ) : ℝ :=
  if t ≤ 1 then -(Real.pi / 2) * Real.sin (Real.pi * t) else 0
theorem cosSqHalfPi_one : cosSqHalfPi 1 = 0 := by
  simp [cosSqHalfPi]
theorem cosSqHalfPi_neg (t : ℝ) : cosSqHalfPi (-t) = cosSqHalfPi t := by
  have : Real.pi * -t / 2 = -(Real.pi * t / 2) := by ring
  simp only [cosSqHalfPi, this, Real.cos_neg]
theorem continuous_cosSqHalfPi : Continuous cosSqHalfPi := by
  unfold cosSqHalfPi
  fun_prop
theorem continuous_cosBumpRight : Continuous cosBumpRight := by
  refine Continuous.if_le continuous_cosSqHalfPi continuous_const continuous_id continuous_const ?_
  intro x hx
  have : x = 1 := hx
  rw [this, cosSqHalfPi_one]
theorem continuous_cosBumpRightDeriv : Continuous cosBumpRightDeriv := by
  refine Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const ?_
  intro x hx
  have : x = 1 := hx
  simp [this]
theorem hasDerivAt_cosBumpRight (t : ℝ) : HasDerivAt cosBumpRight (cosBumpRightDeriv t) t := by
  refine hasDerivAt_of_hasDerivAt_of_ne' (x := 1) (fun y hy => ?_)
    continuous_cosBumpRight.continuousAt continuous_cosBumpRightDeriv.continuousAt t
  rcases lt_or_gt_of_ne hy with h | h
  · have h1 : cosBumpRight =ᶠ[𝓝 y] cosSqHalfPi := by
      filter_upwards [Iio_mem_nhds h] with x hx
      exact if_pos (le_of_lt hx)
    have h2 : cosBumpRightDeriv y = -(Real.pi / 2) * Real.sin (Real.pi * y) := if_pos h.le
    rw [h2]
    exact (hasDerivAt_cosSqHalfPi y).congr_of_eventuallyEq h1
  · have h1 : cosBumpRight =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds h] with x hx
      exact if_neg (not_le.2 hx)
    have h2 : cosBumpRightDeriv y = 0 := if_neg (not_le.2 h)
    rw [h2]
    exact (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq h1
theorem hasDerivAt_cosBump (t : ℝ) : HasDerivAt cosBump (cosBumpDeriv t) t := by
  rcases lt_or_ge (-1) t with h | h
  · have h1 : cosBump =ᶠ[𝓝 t] cosBumpRight := by
      filter_upwards [Ioi_mem_nhds h] with x hx
      have hx' : (-1 : ℝ) < x := hx
      by_cases hx1 : x ≤ 1
      · simp [cosBump, cosBumpRight, abs_le, hx1, hx'.le]
      · have : ¬ |x| ≤ 1 := fun h' => hx1 (abs_le.1 h').2
        simp [cosBump, cosBumpRight, hx1, this]
    have h2 : cosBumpDeriv t = cosBumpRightDeriv t := by
      by_cases ht : t ≤ 1
      · simp [cosBumpDeriv, cosBumpRightDeriv, abs_le, ht, h.le]
      · have : ¬ |t| ≤ 1 := fun h' => ht (abs_le.1 h').2
        simp [cosBumpDeriv, cosBumpRightDeriv, ht, this]
    rw [h2]
    exact (hasDerivAt_cosBumpRight t).congr_of_eventuallyEq h1
  · have hlt : t < 1 := by linarith
    have h1 : cosBump =ᶠ[𝓝 t] fun x => cosBumpRight (-x) := by
      filter_upwards [Iio_mem_nhds hlt] with x hx
      have hx' : x < 1 := hx
      by_cases hx1 : -1 ≤ x
      · have h3 : -x ≤ 1 := by linarith
        have h4 : |x| ≤ 1 := abs_le.2 ⟨hx1, hx'.le⟩
        simp only [cosBump, cosBumpRight, h3, h4, if_true, cosSqHalfPi_neg]
      · have h3 : ¬ -x ≤ 1 := by
          intro h'
          exact hx1 (by linarith)
        have h4 : ¬ |x| ≤ 1 := fun h' => hx1 (abs_le.1 h').1
        simp only [cosBump, cosBumpRight, h3, h4, if_false]
    have h2 : cosBumpDeriv t = cosBumpRightDeriv (-t) * (-1) := by
      by_cases ht : -1 ≤ t
      · have h3 : -t ≤ 1 := by linarith
        have h4 : |t| ≤ 1 := abs_le.2 ⟨ht, hlt.le⟩
        simp only [cosBumpDeriv, cosBumpRightDeriv, h3, h4, if_true]
        have : Real.pi * -t = -(Real.pi * t) := by ring
        rw [this, Real.sin_neg]
        ring
      · have h3 : ¬ -t ≤ 1 := by
          intro h'
          exact ht (by linarith)
        have h4 : ¬ |t| ≤ 1 := fun h' => ht (abs_le.1 h').1
        simp only [cosBumpDeriv, cosBumpRightDeriv, h3, h4, if_false]
        ring
    rw [h2]
    have h5 : HasDerivAt (fun x => cosBumpRight (-x)) (cosBumpRightDeriv (-t) * (-1)) t :=
      (hasDerivAt_cosBumpRight (-t)).comp t (hasDerivAt_neg t)
    exact h5.congr_of_eventuallyEq h1
theorem continuous_cosBumpDeriv : Continuous cosBumpDeriv := by
  refine Continuous.if_le (by fun_prop) continuous_const continuous_abs continuous_const ?_
  intro x hx
  have h : |x| = 1 := hx
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 h with h | h <;> simp [h]
theorem contDiff_cosBump : ContDiff ℝ 1 cosBump := by
  have hd : deriv cosBump = cosBumpDeriv := funext fun t => (hasDerivAt_cosBump t).deriv
  refine contDiff_one_iff_deriv.2 ⟨fun t => (hasDerivAt_cosBump t).differentiableAt, ?_⟩
  rw [hd]
  exact continuous_cosBumpDeriv
theorem cosBump_nonneg (t : ℝ) : 0 ≤ cosBump t := by
  unfold cosBump cosSqHalfPi
  split_ifs
  · positivity
  · exact le_rfl
theorem cosBump_le_one (t : ℝ) : cosBump t ≤ 1 := by
  unfold cosBump cosSqHalfPi
  split_ifs
  · exact Real.cos_sq_le_one _
  · exact zero_le_one
theorem abs_cosBumpDeriv_le (t : ℝ) : |cosBumpDeriv t| ≤ Real.pi / 2 := by
  unfold cosBumpDeriv
  split_ifs
  · rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < Real.pi / 2)]
    have := Real.abs_sin_le_one (Real.pi * t)
    nlinarith [Real.pi_pos]
  · rw [abs_zero]
    positivity
theorem cosBump_eq_zero {t : ℝ} (h : 1 ≤ |t|) : cosBump t = 0 := by
  unfold cosBump
  split_ifs with h1
  · have h2 : |t| = 1 := le_antisymm h1 h
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 h2 with h3 | h3
    · rw [h3, cosSqHalfPi_one]
    · rw [h3, cosSqHalfPi_neg, cosSqHalfPi_one]
  · rfl
theorem abs_lt_one_of_cosBump_ne_zero {t : ℝ} (h : cosBump t ≠ 0) : |t| < 1 := by
  by_contra h1
  exact h (cosBump_eq_zero (not_lt.1 h1))
theorem cosBump_add_cosBump_sub_one {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    cosBump u + cosBump (u - 1) = 1 := by
  have a1 : |u| ≤ 1 := abs_le.2 ⟨by linarith, h1.le⟩
  have a2 : |u - 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  simp only [cosBump, a1, a2, if_true, cosSqHalfPi]
  have h3 : Real.pi * (u - 1) / 2 = Real.pi * u / 2 - Real.pi / 2 := by ring
  rw [h3, Real.cos_sub_pi_div_two]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * u / 2)]
theorem cosBump_sub_eq_zero_of_not_mem (t : ℝ) (k : ℤ)
    (hk : k ∉ ({⌊t⌋, ⌊t⌋ + 1} : Finset ℤ)) : cosBump (t - k) = 0 := by
  apply cosBump_eq_zero
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  rcases lt_or_gt_of_ne hk.1 with h | h
  · have h3 : (k : ℝ) + 1 ≤ ⌊t⌋ := by exact_mod_cast h
    rw [le_abs]
    left
    linarith
  · have h3 : ⌊t⌋ + 1 < k := by
      rcases lt_or_eq_of_le (Int.add_one_le_iff.2 h) with h' | h'
      · exact h'
      · exact absurd h'.symm hk.2
    have h4 : ((⌊t⌋ : ℝ) + 1) + 1 ≤ k := by exact_mod_cast h3
    rw [le_abs]
    right
    linarith
theorem sum_cosBump_floor (t : ℝ) :
    ∑ k ∈ ({⌊t⌋, ⌊t⌋ + 1} : Finset ℤ), cosBump (t - k) = 1 := by
  have hne : ⌊t⌋ ≠ ⌊t⌋ + 1 := by omega
  rw [Finset.sum_pair hne]
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  have h3 := cosBump_add_cosBump_sub_one (u := t - ⌊t⌋) (by linarith) (by linarith)
  have h4 : t - ((⌊t⌋ + 1 : ℤ) : ℝ) = t - ⌊t⌋ - 1 := by
    push_cast
    ring
  rw [h4]
  exact h3
theorem hasSum_cosBump (t : ℝ) : HasSum (fun k : ℤ => cosBump (t - k)) 1 := by
  have h : HasSum (fun k : ℤ => cosBump (t - k))
      (∑ k ∈ ({⌊t⌋, ⌊t⌋ + 1} : Finset ℤ), cosBump (t - k)) :=
    hasSum_sum_of_ne_finset_zero (cosBump_sub_eq_zero_of_not_mem t)
  rwa [sum_cosBump_floor] at h
section Periodised
variable {w : ℕ} [NeZero w]
def residueLift (w : ℕ) (p : ZMod w × ℤ) : ℤ := (p.1.val : ℤ) + w * p.2
theorem cast_residueLift (p : ZMod w × ℤ) : ((residueLift w p : ℤ) : ZMod w) = p.1 := by
  simp [residueLift]
theorem exists_eq_residueLift (n : ℤ) (κ : ZMod w) (h : (n : ZMod w) = κ) :
    ∃ z : ℤ, n = residueLift w (κ, z) := by
  have h1 : (((κ.val : ℤ)) : ZMod w) = (n : ZMod w) := by
    rw [h]
    simp
  obtain ⟨z, hz⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
  exact ⟨z, by simp only [residueLift]; linarith⟩
theorem bijective_residueLift : Function.Bijective (residueLift w) := by
  have hw : (w : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne w
  constructor
  · rintro ⟨κ, z⟩ ⟨κ', z'⟩ h
    have h1 : κ = κ' := by
      have := congrArg (fun n : ℤ => (n : ZMod w)) h
      simpa only [cast_residueLift] using this
    subst h1
    have h2 : (w : ℤ) * z = w * z' := by
      simpa only [residueLift, add_right_inj] using h
    rw [mul_right_inj' hw] at h2
    rw [h2]
  · intro n
    obtain ⟨z, hz⟩ := exists_eq_residueLift (w := w) n (n : ZMod w) rfl
    exact ⟨((n : ZMod w), z), hz.symm⟩
def periodicBump (w : ℕ) (κ : ZMod w) (t : ℝ) : ℝ :=
  ∑' z : ℤ, cosBump (t - (residueLift w (κ, z) : ℤ))
theorem periodicBump_eq_locally (hw : 3 ≤ w) (κ : ZMod w) (t : ℝ) :
    ∃ n : ℤ, (n : ZMod w) = κ ∧ ∀ u, |u - t| < 1 / 2 → periodicBump w κ u = cosBump (u - n) := by
  have hw' : (3 : ℝ) ≤ w := by exact_mod_cast hw
  have hw0 : (0 : ℝ) < w := by linarith
  set z₀ : ℤ := round ((t - κ.val) / w) with hz₀
  refine ⟨residueLift w (κ, z₀), cast_residueLift _, fun u hu => ?_⟩
  unfold periodicBump
  rw [tsum_eq_single z₀]
  intro z hz
  apply cosBump_eq_zero
  have h1 : |(t - κ.val) / w - z₀| ≤ 1 / 2 := abs_sub_round _
  have h2 : |t - κ.val - w * z₀| ≤ w / 2 := by
    have h3 : t - κ.val - w * z₀ = w * ((t - κ.val) / w - z₀) := by
      field_simp
    rw [h3, abs_mul, abs_of_pos hw0]
    nlinarith
  have h3 : (1 : ℝ) ≤ |(z : ℝ) - z₀| := by
    have : (1 : ℤ) ≤ |z - z₀| := Int.one_le_abs (sub_ne_zero.2 hz)
    exact_mod_cast this
  have h4 : u - ((residueLift w (κ, z) : ℤ) : ℝ) =
      (u - t) + (t - κ.val - w * z₀) - w * ((z : ℝ) - z₀) := by
    simp only [residueLift]
    push_cast
    ring
  rw [h4]
  set A := t - κ.val - w * z₀
  set B := (z : ℝ) - z₀
  set C := u - t
  have hA := abs_le.1 h2
  have hC := abs_lt.1 hu
  rcases le_abs.1 h3 with hB | hB
  · have h5 : (w : ℝ) ≤ w * B := by nlinarith
    rw [le_abs]
    right
    linarith [hA.1, hA.2, hC.1, hC.2]
  · have h5 : (w : ℝ) ≤ w * (-B) := by nlinarith
    rw [le_abs]
    left
    linarith [hA.1, hA.2, hC.1, hC.2]
theorem contDiff_periodicBump (hw : 3 ≤ w) (κ : ZMod w) : ContDiff ℝ 1 (periodicBump w κ) := by
  refine contDiff_iff_contDiffAt.2 fun t => ?_
  obtain ⟨n, -, h⟩ := periodicBump_eq_locally hw κ t
  have h1 : periodicBump w κ =ᶠ[𝓝 t] fun u => cosBump (u - n) := by
    filter_upwards [Metric.ball_mem_nhds t (by norm_num : (0 : ℝ) < 1 / 2)] with u hu
    exact h u (by simpa [Real.dist_eq] using hu)
  have h2 : ContDiff ℝ 1 fun u : ℝ => cosBump (u - n) :=
    contDiff_cosBump.comp (contDiff_id.sub contDiff_const)
  exact h2.contDiffAt.congr_of_eventuallyEq h1
theorem exists_hasDerivAt_periodicBump (hw : 3 ≤ w) (κ : ZMod w) (t : ℝ) :
    ∃ D, |D| ≤ Real.pi / 2 ∧ HasDerivAt (periodicBump w κ) D t := by
  obtain ⟨n, -, h⟩ := periodicBump_eq_locally hw κ t
  have h1 : periodicBump w κ =ᶠ[𝓝 t] fun u => cosBump (u - n) := by
    filter_upwards [Metric.ball_mem_nhds t (by norm_num : (0 : ℝ) < 1 / 2)] with u hu
    exact h u (by simpa [Real.dist_eq] using hu)
  refine ⟨cosBumpDeriv (t - n), abs_cosBumpDeriv_le _, ?_⟩
  have h2 : HasDerivAt (fun u : ℝ => cosBump (u - n)) (cosBumpDeriv (t - n)) t :=
    (hasDerivAt_cosBump (t - n)).comp_sub_const t n
  exact h2.congr_of_eventuallyEq h1
theorem exists_periodicBump_eq (hw : 3 ≤ w) (κ : ZMod w) (t : ℝ) :
    ∃ n : ℤ, (n : ZMod w) = κ ∧ periodicBump w κ t = cosBump (t - n) := by
  obtain ⟨n, hn, h⟩ := periodicBump_eq_locally hw κ t
  exact ⟨n, hn, h t (by simp)⟩
theorem exists_near_of_periodicBump_ne_zero (hw : 3 ≤ w) {κ : ZMod w} {t : ℝ}
    (h : periodicBump w κ t ≠ 0) : ∃ n : ℤ, (n : ZMod w) = κ ∧ |t - n| < 1 := by
  obtain ⟨n, hn, h1⟩ := exists_periodicBump_eq hw κ t
  rw [h1] at h
  exact ⟨n, hn, abs_lt_one_of_cosBump_ne_zero h⟩
omit [NeZero w] in
theorem periodicBump_periodic (κ : ZMod w) : Function.Periodic (periodicBump w κ) (w : ℝ) := by
  intro t
  unfold periodicBump
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
  refine tsum_congr fun z => ?_
  congr 1
  simp only [residueLift, Equiv.coe_addRight]
  push_cast
  ring
theorem sum_periodicBump (t : ℝ) : ∑ κ : ZMod w, periodicBump w κ t = 1 := by
  let e := Equiv.ofBijective (residueLift w) bijective_residueLift
  have h0 : HasSum ((fun k : ℤ => cosBump (t - k)) ∘ e) 1 :=
    (Equiv.hasSum_iff e (f := fun k : ℤ => cosBump (t - k))).2 (hasSum_cosBump t)
  have h2 : ∀ κ : ZMod w, HasSum (fun z : ℤ => ((fun k : ℤ => cosBump (t - k)) ∘ e) (κ, z))
      (periodicBump w κ t) := fun κ => (h0.summable.prod_factor κ).hasSum
  have h1 : HasSum (fun κ : ZMod w => periodicBump w κ t) 1 := h0.prod_fiberwise h2
  exact (hasSum_fintype _).unique h1
end Periodised
structure IsUnitProfile (g : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 g
  mem : ∀ t, g t ∈ Icc (0 : ℝ) 1
  deriv : ∀ t, ∃ D, |D| ≤ Real.pi / 2 ∧ HasDerivAt g D t
theorem isUnitProfile_cosBump (k : ℤ) : IsUnitProfile fun t => cosBump (t - k) where
  contDiff := contDiff_cosBump.comp (contDiff_id.sub contDiff_const)
  mem _ := ⟨cosBump_nonneg _, cosBump_le_one _⟩
  deriv t := ⟨cosBumpDeriv (t - k), abs_cosBumpDeriv_le _,
    (hasDerivAt_cosBump (t - k)).comp_sub_const t k⟩
theorem isUnitProfile_periodicBump {w : ℕ} [NeZero w] (hw : 3 ≤ w) (κ : ZMod w) :
    IsUnitProfile (periodicBump w κ) where
  contDiff := contDiff_periodicBump hw κ
  mem t := by
    obtain ⟨n, -, h⟩ := exists_periodicBump_eq hw κ t
    rw [h]
    exact ⟨cosBump_nonneg _, cosBump_le_one _⟩
  deriv := exists_hasDerivAt_periodicBump hw κ
def profileProduct (g : Fin 4 → ℝ → ℝ) (ς : ℝ) (x : Fin 4 → ℝ) : ℝ := ∏ μ, g μ (x μ / ς)
theorem contDiff_profileProduct {g : Fin 4 → ℝ → ℝ} (hg : ∀ μ, IsUnitProfile (g μ)) (ς : ℝ) :
    ContDiff ℝ 1 (profileProduct g ς) := by
  unfold profileProduct
  refine contDiff_prod fun μ _ => (hg μ).contDiff.comp ?_
  exact (contDiff_apply ℝ ℝ μ).div_const ς
theorem profileProduct_mem_Icc {g : Fin 4 → ℝ → ℝ} (hg : ∀ μ, IsUnitProfile (g μ)) (ς : ℝ)
    (x : Fin 4 → ℝ) : profileProduct g ς x ∈ Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg fun μ _ => ((hg μ).mem _).1,
    Finset.prod_le_one (fun μ _ => ((hg μ).mem _).1) fun μ _ => ((hg μ).mem _).2⟩
theorem profile_ne_zero_of_profileProduct_ne_zero {g : Fin 4 → ℝ → ℝ} {ς : ℝ} {x : Fin 4 → ℝ}
    (h : profileProduct g ς x ≠ 0) (μ : Fin 4) : g μ (x μ / ς) ≠ 0 :=
  Finset.prod_ne_zero_iff.1 h μ (Finset.mem_univ μ)
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul {v : Fin 4 → ℝ} {a : ℝ} (ha : 0 ≤ a) (h : ∀ μ, |v μ| ≤ a) :
    TorusMetric.euclidNormVec v ≤ 2 * a := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.euclidNormVec_le <;> assumption
theorem abs_partialDerivR4_profileProduct_le {g : Fin 4 → ℝ → ℝ}
    (hg : ∀ μ, IsUnitProfile (g μ)) {ς : ℝ} (hς : 0 < ς) (μ : Fin 4) (x : Fin 4 → ℝ) :
    |TestFunctions.partialDerivR4 μ (profileProduct g ς) x| ≤ Real.pi / (2 * ς) := by
  set C : ℝ := ∏ ν ∈ Finset.univ.erase μ, g ν (x ν / ς) with hC
  have hC0 : 0 ≤ C := Finset.prod_nonneg fun ν _ => ((hg ν).mem _).1
  have hC1 : C ≤ 1 :=
    Finset.prod_le_one (fun ν _ => ((hg ν).mem _).1) fun ν _ => ((hg ν).mem _).2
  have e : (fun t : ℝ => profileProduct g ς (x + t • Pi.single μ (1 : ℝ))) =
      fun t => g μ ((x μ + t) / ς) * C := by
    funext t
    unfold profileProduct
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ μ), hC]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun ν hν => ?_
      have : ν ≠ μ := Finset.ne_of_mem_erase hν
      simp [Pi.single_eq_of_ne this]
  obtain ⟨D, hD, hder⟩ := (hg μ).deriv (x μ / ς)
  have hin : HasDerivAt (fun t : ℝ => (x μ + t) / ς) (1 / ς) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add (x μ)).div_const ς
  have h2 : HasDerivAt (fun t : ℝ => g μ ((x μ + t) / ς)) (D * (1 / ς)) 0 :=
    HasDerivAt.comp (h₂ := g μ) (0 : ℝ) (by simpa using hder) hin
  have h3 := h2.mul_const C
  unfold TestFunctions.partialDerivR4
  rw [e, h3.deriv, abs_mul, abs_mul, abs_of_nonneg hC0, abs_of_pos (by positivity : 0 < 1 / ς)]
  have h4 : |D| * (1 / ς) ≤ Real.pi / 2 * (1 / ς) :=
    mul_le_mul_of_nonneg_right hD (by positivity)
  have h5 : Real.pi / 2 * (1 / ς) = Real.pi / (2 * ς) := by
    field_simp
  have h6 : |D| * (1 / ς) * C ≤ |D| * (1 / ς) * 1 :=
    mul_le_mul_of_nonneg_left hC1 (by positivity)
  linarith
theorem euclidNormVec_gradR4_profileProduct_le {g : Fin 4 → ℝ → ℝ}
    (hg : ∀ μ, IsUnitProfile (g μ)) {ς : ℝ} (hς : 0 < ς) (x : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (gradR4 (profileProduct g ς) x) ≤ Real.pi / ς := by
  have h := euclidNormVec_le_two_mul (v := gradR4 (profileProduct g ς) x)
    (a := Real.pi / (2 * ς)) (by positivity) fun μ => abs_partialDerivR4_profileProduct_le hg hς μ x
  have h1 : 2 * (Real.pi / (2 * ς)) = Real.pi / ς := by
    field_simp
  rwa [h1] at h
section Family
variable {s : Conventions.StandingParameters} {M : BlockScale s} {Y : ModelSpace}
theorem supportIn_subset_closedBall_of_ne_zero (H : SettingFactsHold s M Y)
    {f : Y.Carrier s → ℝ} {x : Y.Carrier s} {R : ℝ}
    (h : ∀ y, f y ≠ 0 → y ∈ ModelSpace.closedBall s Y x R) :
    supportIn s Y f ⊆ ModelSpace.closedBall s Y x R := by
  intro y hy
  obtain ⟨-, -, -, -, -, htri, -⟩ := H.dist_invariant
  have hy' : ∀ r : ℝ, 0 < r → ∃ y' ∈ {y | f y ≠ 0}, ModelSpace.dist s Y y y' < r := hy
  exact show ModelSpace.dist s Y y x ≤ R from by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨y', hy₁, hd⟩ := hy' ε hε
    have h1 : ModelSpace.dist s Y y' x ≤ R := h y' hy₁
    have h2 := htri y x y'
    linarith
theorem isCompactIn_supportIn (H : SettingFactsHold s M Y)
    {f : Y.Carrier s → ℝ} {K : Set (Y.Carrier s)} (hK : IsCompactIn s Y K)
    (hs : supportIn s Y f ⊆ K) : IsCompactIn s Y (supportIn s Y f) := by
  obtain ⟨-, -, -, -, -, htri, -⟩ := H.dist_invariant
  have hopen : MetricNotions.IsOpenWrt (ModelSpace.dist s Y) (supportIn s Y f)ᶜ := by
    intro x hx
    have hx' : ¬ ∀ r : ℝ, 0 < r → ∃ y ∈ {y | f y ≠ 0}, ModelSpace.dist s Y x y < r := hx
    push Not at hx'
    obtain ⟨r, hr, hr'⟩ := hx'
    refine ⟨r / 2, half_pos hr, fun x' hx₁ hmem => ?_⟩
    have hmem' : ∀ r : ℝ, 0 < r → ∃ y ∈ {y | f y ≠ 0}, ModelSpace.dist s Y x' y < r := hmem
    obtain ⟨y, hy, hd⟩ := hmem' (r / 2) (half_pos hr)
    have h1 := hr' y hy
    have h2 := htri x y x'
    linarith
  intro 𝒰 h𝒰 hcov
  obtain ⟨𝒱, hV, hfin, hVc⟩ := hK (insert (supportIn s Y f)ᶜ 𝒰)
    (by
      intro U hU
      rcases hU with rfl | hU
      · exact hopen
      · exact h𝒰 U hU)
    (by
      intro x _
      by_cases hx : x ∈ supportIn s Y f
      · obtain ⟨U, hU, hxU⟩ := hcov hx
        exact ⟨U, Or.inr hU, hxU⟩
      · exact ⟨_, Or.inl rfl, hx⟩)
  refine ⟨𝒱 \ {(supportIn s Y f)ᶜ}, ?_, hfin.subset sdiff_subset, ?_⟩
  · rintro U ⟨hU, hne⟩
    rcases hV hU with h | h
    · exact absurd h hne
    · exact h
  · intro x hx
    obtain ⟨U, hU, hxU⟩ := hVc (hs hx)
    refine ⟨U, ⟨hU, ?_⟩, hxU⟩
    rintro rfl
    exact hxU hx
theorem exists_partition_of_profileProducts (H : SettingFactsHold s M Y)
    {I : Type*} {ς : ℝ} (hς : 0 < ς) (χ : I → Y.Carrier s → ℝ) (g : I → Fin 4 → ℝ → ℝ)
    (c : I → Y.Carrier s) (hg : ∀ ι μ, IsUnitProfile (g ι μ))
    (hlift : ∀ ι, χ ι ∘ proj s Y = profileProduct (g ι) ς)
    (hball : ∀ ι y, χ ι y ≠ 0 → y ∈ ModelSpace.closedBall s Y (c ι) (2 * ς))
    (hsum : ∀ y, HasSum (fun ι => χ ι y) 1)
    (hfin : ∀ K : Set (Y.Carrier s), IsCompactIn s Y K →
      {ι | (K ∩ ModelSpace.closedBall s Y (c ι) (2 * ς)).Nonempty}.Finite) :
    ∃ χ' : I → c1CompactSupp s Y univ, (∀ ι, (χ' ι).1 = χ ι) ∧
      IsSmoothPartitionAtScale s Y ς χ' := by
  have hsupp : ∀ ι, supportIn s Y (χ ι) ⊆ ModelSpace.closedBall s Y (c ι) (2 * ς) := fun ι =>
    supportIn_subset_closedBall_of_ne_zero H (hball ι)
  have hC1 : ∀ ι, IsC1 s Y (χ ι) := fun ι => (H.isC1_iff.1 (χ ι)).2 (by
    rw [hlift]
    exact contDiff_profileProduct (hg ι) ς)
  have hmem : ∀ ι, χ ι ∈ c1CompactSupp s Y univ := fun ι =>
    ⟨hC1 ι, isCompactIn_supportIn H (H.closedBall_compact _ _ (by positivity)) (hsupp ι),
      subset_univ _⟩
  have hsurj : Function.Surjective (proj s Y) := H.proj_lifts.2.1
  have hgrad : ∀ ι y, TorusMetric.euclidNormVec (grad s Y (χ ι) y) ≤ Real.pi / ς := by
    intro ι y
    obtain ⟨v, rfl⟩ := hsurj y
    have h1 := (H.isC1_iff.2.1 (χ ι) (hC1 ι)).1
    have h2 : grad s Y (χ ι) (proj s Y v) =
        gradR4 (χ ι ∘ proj s Y) v := congrFun h1 v
    rw [h2, hlift]
    exact euclidNormVec_gradR4_profileProduct_le (hg ι) hς v
  obtain ⟨-, -, -, -, hsymm, htri, -⟩ := H.dist_invariant
  have hgs : ∀ ι, gradSup (⟨χ ι, hmem ι⟩ : c1CompactSupp s Y univ) ≤
      ENNReal.ofReal (Real.pi / ς) := fun ι =>
    iSup_le fun y => ENNReal.ofReal_le_ofReal (hgrad ι y)
  refine ⟨fun ι => ⟨χ ι, hmem ι⟩, fun _ => rfl, ?_⟩
  exact
    { mem_Icc := fun ι y => by
        obtain ⟨v, rfl⟩ := hsurj y
        have h1 : χ ι (proj s Y v) = profileProduct (g ι) ς v := congrFun (hlift ι) v
        change χ ι (proj s Y v) ∈ _
        rw [h1]
        exact profileProduct_mem_Icc (hg ι) ς v
      locallyFinite := fun K hK => (hfin K hK).subset fun ι ⟨y, hyK, hy⟩ =>
        ⟨y, hyK, hsupp ι hy⟩
      hasSum_one := hsum
      support_subset_closedBall := fun ι => ⟨c ι, hsupp ι⟩
      dist_le := fun ι y hy y' hy' => by
        have h1 : ModelSpace.dist s Y y (c ι) ≤ 2 * ς := hsupp ι hy
        have h2 : ModelSpace.dist s Y y' (c ι) ≤ 2 * ς := hsupp ι hy'
        have h3 := htri y y' (c ι)
        have h4 := hsymm y' (c ι)
        linarith
      lipNumber_le_gradSup := fun ι => by
        obtain ⟨hlt, -, -, hL⟩ := H.c1_lipschitz.1 ⟨χ ι, hmem ι⟩
        rw [← lipNumber_eq_bestLipschitzConstant]
        calc ENNReal.ofReal (lipNumber s Y (χ ι))
            ≤ ENNReal.ofReal (gradSup (⟨χ ι, hmem ι⟩ : c1CompactSupp s Y univ)).toReal :=
              ENNReal.ofReal_le_ofReal hL
          _ = _ := ENNReal.ofReal_toReal hlt.ne
      gradSup_le := hgs }
theorem hasSum_prod_cosBump (t : Fin 4 → ℝ) :
    HasSum (fun ι : Fin 4 → ℤ => ∏ μ, cosBump (t μ - ι μ)) 1 := by
  let T : Fin 4 → Finset ℤ := fun μ => {⌊t μ⌋, ⌊t μ⌋ + 1}
  have h : HasSum (fun ι : Fin 4 → ℤ => ∏ μ, cosBump (t μ - ι μ))
      (∑ ι ∈ Fintype.piFinset T, ∏ μ, cosBump (t μ - ι μ)) := by
    refine hasSum_sum_of_ne_finset_zero fun ι hι => ?_
    rw [Fintype.mem_piFinset] at hι
    push Not at hι
    obtain ⟨μ, hμ⟩ := hι
    exact Finset.prod_eq_zero (Finset.mem_univ μ) (cosBump_sub_eq_zero_of_not_mem _ _ hμ)
  have h2 : ∑ ι ∈ Fintype.piFinset T, ∏ μ, cosBump (t μ - ι μ) = 1 := by
    rw [← Finset.prod_univ_sum T fun μ k => cosBump (t μ - k)]
    exact Finset.prod_eq_one fun μ _ => sum_cosBump_floor (t μ)
  rwa [h2] at h
theorem abs_sub_mul_le_of_abs_div_sub_lt_one {ς a : ℝ} (hς : 0 < ς) {n : ℝ}
    (h : |a / ς - n| < 1) : |a - ς * n| ≤ ς := by
  have h1 : a - ς * n = ς * (a / ς - n) := by
    field_simp
  rw [h1, abs_mul, abs_of_pos hς]
  nlinarith
theorem finite_lattice_points_near {ς : ℝ} (hς : 0 < ς) (x : Fin 4 → ℝ) (D : ℝ) :
    {ι : Fin 4 → ℤ | TorusMetric.euclidNormVec (x - fun μ => ς * (ι μ : ℝ)) ≤ D}.Finite := by
  refine (Set.Finite.pi' (t := fun μ => Set.Icc ⌊(x μ - D) / ς⌋ ⌈(x μ + D) / ς⌉)
    fun μ => Set.finite_Icc _ _).subset ?_
  intro ι hι μ
  have h1 : |x μ - ς * (ι μ : ℝ)| ≤ D :=
    (abs_apply_le_euclidNormVec (x - fun μ => ς * (ι μ : ℝ)) μ).trans hι
  have h2 := abs_le.1 h1
  constructor
  · have h3 : (x μ - D) / ς ≤ ι μ := by
      rw [div_le_iff₀ hς]
      linarith [h2.2]
    exact Int.cast_le.1 ((Int.floor_le _).trans h3)
  · have h3 : (ι μ : ℝ) ≤ (x μ + D) / ς := by
      rw [le_div_iff₀ hς]
      linarith [h2.1]
    exact Int.cast_le.1 (h3.trans (Int.le_ceil _))
theorem exists_partition_euclidean (H : SettingFactsHold s M euclidean) {ς : ℝ} (hς : 0 < ς) :
    ∃ χ : (Fin 4 → ℤ) → c1CompactSupp s euclidean univ,
      IsSmoothPartitionAtScale s euclidean ς χ := by
  obtain ⟨-, -, -, -, hsymm, htri, -⟩ := H.dist_invariant
  obtain ⟨χ, -, h⟩ := exists_partition_of_profileProducts H hς (I := Fin 4 → ℤ)
    (fun ι => profileProduct (fun μ t => cosBump (t - ι μ)) ς)
    (fun ι μ t => cosBump (t - ι μ)) (fun ι => (fun μ => ς * ι μ : Fin 4 → ℝ))
    (fun ι μ => isUnitProfile_cosBump (ι μ)) (fun _ => rfl)
    (by
      intro ι y hy
      change TorusMetric.euclidNormVec (_ - _) ≤ 2 * ς
      refine euclidNormVec_le_two_mul hς.le fun μ => ?_
      exact abs_sub_mul_le_of_abs_div_sub_lt_one hς
        (abs_lt_one_of_cosBump_ne_zero (profile_ne_zero_of_profileProduct_ne_zero hy μ)))
    (fun y => hasSum_prod_cosBump fun μ => y μ / ς)
    (by
      intro K hK
      obtain ⟨x, R, -, hKR⟩ := (H.compact_bounded K hK).2
      refine (finite_lattice_points_near hς x (R + 2 * ς)).subset ?_
      rintro ι ⟨y, hyK, hy⟩
      have h1 : ModelSpace.dist s euclidean y x ≤ R := hKR hyK
      have h2 : ModelSpace.dist s euclidean y (fun μ => ς * (ι μ : ℝ) : Fin 4 → ℝ) ≤ 2 * ς := hy
      have h3 := htri x (fun μ => ς * (ι μ : ℝ) : Fin 4 → ℝ) y
      have h4 := hsymm x y
      have h5 : ModelSpace.dist s euclidean x (fun μ => ς * (ι μ : ℝ) : Fin 4 → ℝ) ≤
          R + 2 * ς := by
        linarith
      exact h5)
  exact ⟨χ, h⟩
theorem exists_partition_torus (H : SettingFactsHold s M torus) {w : ℕ}
    [NeZero w] (hw : 3 ≤ w) {ς : ℝ} (hς : 0 < ς) (hs : ς = s.side / (w : ℝ)) :
    ∃ χ : (Fin 4 → ZMod w) → c1CompactSupp s torus univ,
      IsSmoothPartitionAtScale s torus ς χ := by
  have hw0 : (w : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne w
  have hℓ : s.side = w * ς := by
    rw [hs]
    field_simp
  have hper : ∀ κ : ZMod w,
      Function.Periodic (fun u : ℝ => periodicBump w κ (u / ς))
        (PeriodicLattice.torusSide s.L s.m) := by
    intro κ u
    have h1 : (u + PeriodicLattice.torusSide s.L s.m) / ς = u / ς + w := by
      change (u + s.side) / ς = _
      rw [hℓ]
      field_simp
    simp only [h1]
    exact periodicBump_periodic κ (u / ς)
  let χ : (Fin 4 → ZMod w) → PeriodicLattice.FourTorus s.L s.m → ℝ :=
    fun κ y => ∏ μ, (hper (κ μ)).lift (y μ)
  have hlift : ∀ κ, χ κ ∘ proj s torus =
      profileProduct (fun μ => periodicBump w (κ μ)) ς := by
    intro κ
    funext x
    refine Finset.prod_congr rfl fun μ _ => ?_
    exact (hper (κ μ)).lift_coe (x μ)
  obtain ⟨hadd, hsurj, -, -, hlen, -⟩ := H.proj_lifts
  have hker : ∀ z : Fin 4 → ℤ,
      proj s torus (fun μ => s.side * (z μ : ℝ)) = 0 := by
    intro z
    exact show (fun μ => s.side * (z μ : ℝ)) ∈ {x | proj s torus x = 0} from by
      rw [H.proj_kernels.2]
      exact ⟨z, rfl⟩
  obtain ⟨χ', -, h⟩ := exists_partition_of_profileProducts H hς (I := Fin 4 → ZMod w) χ
    (fun κ μ => periodicBump w (κ μ))
    (fun κ => proj s torus fun μ => ς * ((κ μ).val : ℝ))
    (fun κ μ => isUnitProfile_periodicBump hw (κ μ)) hlift
    (by
      intro κ y hy
      obtain ⟨v, rfl⟩ := hsurj y
      have h1 : χ κ (proj s torus v) =
          profileProduct (fun μ => periodicBump w (κ μ)) ς v := congrFun (hlift κ) v
      have hy' : profileProduct (fun μ => periodicBump w (κ μ)) ς v ≠ 0 := by
        rw [← h1]
        exact hy
      have hne : ∀ μ, periodicBump w (κ μ) (v μ / ς) ≠ 0 :=
        profile_ne_zero_of_profileProduct_ne_zero hy'
      choose n hn hn' using fun μ => exists_near_of_periodicBump_ne_zero hw (hne μ)
      choose z hz using fun μ => exists_eq_residueLift (n μ) (κ μ) (hn μ)
      have hc : proj s torus (fun μ => ς * (n μ : ℝ)) =
          proj s torus fun μ => ς * ((κ μ).val : ℝ) := by
        have e : (fun μ => ς * (n μ : ℝ)) =
            (fun μ => ς * ((κ μ).val : ℝ)) + fun μ => s.side * (z μ : ℝ) := by
          funext μ
          simp only [hz μ, residueLift, hℓ, Pi.add_apply]
          push_cast
          ring
        rw [e, hadd, hker, add_zero]
      change ModelSpace.norm s torus (proj s torus v - _) ≤ 2 * ς
      rw [← hc]
      exact (hlen v _).trans
        (euclidNormVec_le_two_mul hς.le fun μ => abs_sub_mul_le_of_abs_div_sub_lt_one hς (hn' μ)))
    (by
      intro y
      obtain ⟨v, rfl⟩ := hsurj y
      have h1 : ∀ κ, χ κ (proj s torus v) = ∏ μ, periodicBump w (κ μ) (v μ / ς) :=
        fun κ => congrFun (hlift κ) v
      have h2 : ∑ κ : Fin 4 → ZMod w, ∏ μ, periodicBump w (κ μ) (v μ / ς) = 1 := by
        have h3 := Finset.prod_univ_sum (fun _ : Fin 4 => (Finset.univ : Finset (ZMod w)))
          (fun μ k => periodicBump w k (v μ / ς))
        rw [Fintype.piFinset_univ] at h3
        rw [← h3]
        exact Finset.prod_eq_one fun μ _ => sum_periodicBump _
      have h3 : HasSum (fun κ : Fin 4 → ZMod w => ∏ μ, periodicBump w (κ μ) (v μ / ς)) 1 :=
        h2 ▸ hasSum_fintype _
      have h4 : (fun κ => χ κ (proj s torus v)) =
          fun κ : Fin 4 → ZMod w => ∏ μ, periodicBump w (κ μ) (v μ / ς) := funext h1
      rw [h4]
      exact h3)
    (fun K _ => Set.toFinite _)
  exact ⟨χ', h⟩
theorem two_le_side (s : Conventions.StandingParameters) : 2 ≤ s.side := by
  have hL : (1 : ℝ) ≤ s.L := by
    have h : 13 ≤ s.L := s.isAdmissible.2
    exact_mod_cast (by omega : 1 ≤ s.L)
  have h1 : (1 : ℝ) ≤ (s.L : ℝ) ^ (s.m : ℕ) := one_le_pow₀ hL
  simp only [Conventions.StandingParameters.side, PeriodicLattice.torusSide]
  linarith
theorem yieldsTorusPartitionData {w : ℕ} [NeZero w] {ς : ℝ} (hς : 0 < ς)
    (hs : ς = s.side / (w : ℝ)) {χ : (Fin 4 → ZMod w) → c1CompactSupp s torus univ}
    (hP : IsSmoothPartitionAtScale s torus ς χ) :
    YieldsTorusPartitionData s M w ς χ := by
  have hw0 : (w : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne w
  have hside : 0 < s.side := by linarith [two_le_side s]
  have hlip : ∀ ι, TestFunctions.lipConstTorus (ℓ := s.side) (χ ι).1 ≤ Real.pi / ς := by
    intro ι
    have h := (hP.lipNumber_le_gradSup ι).trans (hP.gradSup_le ι)
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  have hdatum : ∀ r Θ : ℝ, r ∈ admissibleRadii s torus → 2 * ς ≤ r → 1 ≤ Θ →
      (w : ℝ) ^ 4 * (1 + 40 * Real.pi * (M.1 : ℝ) * (w : ℝ) / s.side) ≤ Θ →
      IsTorusPartitionDatum s M.1 r (fun ι => (χ ι).1) Θ := by
    intro r Θ hr h2 h1 hΘ
    refine ⟨M.2, hr, hP.mem_Icc, fun ι => (χ ι).2.1, fun x => ?_, fun ι => ?_, h1, ?_⟩
    · exact (hasSum_fintype _).unique (hP.hasSum_one x)
    · obtain ⟨x, hx⟩ := hP.support_subset_closedBall ι
      exact ⟨x, hx.trans fun y hy => le_trans hy h2⟩
    · have hM : (0 : ℝ) ≤ M.1 := Nat.cast_nonneg _
      have h3 : ∀ ι ∈ (Finset.univ : Finset (Fin 4 → ZMod w)),
          1 + 40 * (M.1 : ℝ) * TestFunctions.lipConstTorus (ℓ := s.side) (χ ι).1 ≤
            1 + 40 * (M.1 : ℝ) * (Real.pi / ς) := by
        intro ι _
        have := mul_le_mul_of_nonneg_left (hlip ι) (by positivity : 0 ≤ 40 * (M.1 : ℝ))
        linarith
      have hcard : Fintype.card (Fin 4 → ZMod w) = w ^ 4 := by
        simp [ZMod.card]
      have h4 : ∑ _ι : Fin 4 → ZMod w, (1 + 40 * (M.1 : ℝ) * (Real.pi / ς)) =
          (w : ℝ) ^ 4 * (1 + 40 * Real.pi * (M.1 : ℝ) * (w : ℝ) / s.side) := by
        rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, hs]
        push_cast
        field_simp
      exact (Finset.sum_le_sum h3).trans (h4.le.trans hΘ)
  refine ⟨hdatum, fun h16 => ?_⟩
  have hw16 : (w : ℝ) = 16 := by exact_mod_cast h16
  have hς8 : 2 * ς = s.side / 8 := by
    rw [hs, hw16]
    ring
  have hπM : 0 ≤ Real.pi * (M.1 : ℝ) := by positivity
  refine hdatum _ _ ?_ ?_ ?_ ?_
  · rw [refRadius_torus_eq_side_div_eight]
    change s.side / 8 ∈ Ioo 0 (maxRadius s)
    rw [maxRadius_eq_side_div_four]
    constructor <;> linarith
  · rw [refRadius_torus_eq_side_div_eight, hς8]
  · unfold ModelSpace.torusFactor
    nlinarith
  · unfold ModelSpace.torusFactor
    rw [hw16]
    have h1 : 40 * Real.pi * (M.1 : ℝ) * 16 / s.side ≤ 320 * Real.pi * (M.1 : ℝ) := by
      rw [div_le_iff₀ hside]
      nlinarith [two_le_side s]
    nlinarith
end Family
theorem claim_of_settingFactsHold (hset : SettingFactsHold.statement) : Claim := by
  intro s M ς hς
  refine ⟨exists_partition_euclidean (hset s M euclidean) hς, ?_⟩
  intro w _ hw hs
  obtain ⟨χ, h⟩ := exists_partition_torus (hset s M torus) hw hς hs
  exact ⟨χ, h, yieldsTorusPartitionData hς hs h⟩
end YangMills.Construction.LatticeLimits.C1PartitionOfUnity.Existence
end
