import YangMills.Construction.ToriAtArbitraryCouplings.NormsCuttingAndNeighbourhoods
import YangMills.Construction.Torus.PartitionOfUnityAroundTheCornersProof
import YangMills.Construction.TorusPowers.FromSmallBallsToAllSeparatedTuples
import Mathlib
set_option autoImplicit false
open Set Filter Topology YangMills.Construction.TorusMetric
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TorusPowers.SmallBallPartition
def cosBump (ς r : ℝ) : ℝ := Real.cos (Real.pi * min r ς / (2 * ς)) ^ 2
def cosBumpDeriv (ς r : ℝ) : ℝ := -(Real.pi / (2 * ς)) * Real.sin (Real.pi * min r ς / ς)
theorem cosBump_nonneg (ς r : ℝ) : 0 ≤ cosBump ς r := sq_nonneg _
theorem cosBump_le_one (ς r : ℝ) : cosBump ς r ≤ 1 := Real.cos_sq_le_one _
theorem cosBump_eq_zero_of_le {ς r : ℝ} (hς : 0 < ς) (h : ς ≤ r) : cosBump ς r = 0 := by
  have : Real.pi * ς / (2 * ς) = Real.pi / 2 := by field_simp
  rw [cosBump, min_eq_right h, this, Real.cos_pi_div_two]
  norm_num
theorem abs_cosBump_sub_le {ς : ℝ} (hς : 0 < ς) (r r' : ℝ) :
    |cosBump ς r - cosBump ς r'| ≤ Real.pi / (2 * ς) * |r - r'| := by
  set x := Real.pi * min r ς / (2 * ς)
  set y := Real.pi * min r' ς / (2 * ς)
  have hxy : x - y = Real.pi / (2 * ς) * (min r ς - min r' ς) := by
    simp only [x, y]
    ring
  have hmin : |min r ς - min r' ς| ≤ |r - r'| := by
    refine (abs_min_sub_min_le_max r ς r' ς).trans ?_
    simp
  have hc : 0 ≤ Real.pi / (2 * ς) := by positivity
  have h₁ : cosBump ς r - cosBump ς r' = (Real.cos (2 * x) - Real.cos (2 * y)) / 2 := by
    simp only [cosBump, Real.cos_sq]
    ring
  rw [h₁, abs_div, abs_two]
  have h₂ := Real.abs_cos_sub_cos_le (2 * x) (2 * y)
  have h₃ : |2 * x - 2 * y| = 2 * |x - y| := by
    rw [← mul_sub, abs_mul, abs_two]
  have h₄ : |x - y| ≤ Real.pi / (2 * ς) * |r - r'| := by
    rw [hxy, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hmin hc
  linarith
theorem hasDerivAt_cosBump {ς : ℝ} (hς : 0 < ς) (y : ℝ) :
    HasDerivAt (cosBump ς) (cosBumpDeriv ς y) y := by
  have hcont : Continuous (cosBump ς) := by
    unfold cosBump
    fun_prop
  have hg : Continuous (cosBumpDeriv ς) := by
    unfold cosBumpDeriv
    fun_prop
  refine hasDerivAt_of_hasDerivAt_of_ne' (x := ς) (fun y hy => ?_) hcont.continuousAt
    hg.continuousAt y
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · have hev : cosBump ς =ᶠ[𝓝 y] fun r => Real.cos (Real.pi * r / (2 * ς)) ^ 2 := by
      filter_upwards [Iio_mem_nhds hlt] with r hr
      rw [cosBump, min_eq_left (le_of_lt hr)]
    have hd : HasDerivAt (fun r => Real.cos (Real.pi * r / (2 * ς)) ^ 2)
        (2 * Real.cos (Real.pi * y / (2 * ς)) ^ 1 *
          (-Real.sin (Real.pi * y / (2 * ς)) * (Real.pi / (2 * ς)))) y := by
      have h₁ : HasDerivAt (fun r => Real.pi * r / (2 * ς)) (Real.pi / (2 * ς)) y := by
        simpa using ((hasDerivAt_id y).const_mul Real.pi).div_const (2 * ς)
      exact_mod_cast (h₁.cos).pow 2
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    have h₂ : Real.pi * y / ς = 2 * (Real.pi * y / (2 * ς)) := by
      field_simp
    rw [cosBumpDeriv, min_eq_left (le_of_lt hlt), h₂, Real.sin_two_mul]
    ring
  · have hev : cosBump ς =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hgt] with r hr
      exact cosBump_eq_zero_of_le hς (le_of_lt hr)
    have h₀ : cosBumpDeriv ς y = 0 := by
      have : Real.pi * ς / ς = Real.pi := by field_simp
      rw [cosBumpDeriv, min_eq_right (le_of_lt hgt), this, Real.sin_pi, mul_zero]
    rw [h₀]
    exact (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev
theorem contDiff_cosBump {ς : ℝ} (hς : 0 < ς) : ContDiff ℝ 1 (cosBump ς) := by
  have hderiv : deriv (cosBump ς) = cosBumpDeriv ς :=
    funext fun y => (hasDerivAt_cosBump hς y).deriv
  refine contDiff_one_iff_deriv.2 ⟨fun y => (hasDerivAt_cosBump hς y).differentiableAt, ?_⟩
  rw [hderiv]
  unfold cosBumpDeriv
  fun_prop
theorem cosBump_abs {ς r : ℝ} (hς : 0 < ς) (hr : -ς ≤ r) : cosBump ς |r| = cosBump ς r := by
  rcases le_or_gt 0 r with h | h
  · rw [abs_of_nonneg h]
  · have h₁ : min r ς = r := min_eq_left (by linarith)
    have h₂ : min (-r) ς = -r := min_eq_left (by linarith)
    rw [abs_of_neg h, cosBump, cosBump, h₁, h₂, mul_neg, neg_div, Real.cos_neg]
theorem contDiff_cosBump_abs {ς : ℝ} (hς : 0 < ς) : ContDiff ℝ 1 fun r => cosBump ς |r| := by
  refine contDiff_iff_contDiffAt.2 fun r₀ => ?_
  rcases lt_or_ge (-ς) r₀ with h | h
  · refine (contDiff_cosBump hς).contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds h] with r hr
    exact cosBump_abs hς (le_of_lt hr)
  · have h' : r₀ < ς := by linarith
    have hc : ContDiff ℝ 1 fun r : ℝ => cosBump ς (-r) := (contDiff_cosBump hς).comp contDiff_neg
    refine hc.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h'] with r hr
    have hr' : r < ς := hr
    have := cosBump_abs hς (r := -r) (by linarith)
    rwa [abs_neg] at this
variable {ℓ : ℝ}
def circleDistBump (ς ℓ t : ℝ) : ℝ := cosBump ς ‖(t : AddCircle ℓ)‖
theorem contDiff_circleDistBump {ς : ℝ} (hς : 0 < ς) (hℓ : 2 * ς < ℓ) :
    ContDiff ℝ 1 (circleDistBump ς ℓ) := by
  have hℓ0 : 0 < ℓ := by linarith
  have : Fact (0 < ℓ) := ⟨hℓ0⟩
  have hcont : Continuous fun t : ℝ => ‖(t : AddCircle ℓ)‖ :=
    continuous_norm.comp (AddCircle.continuous_mk' ℓ)
  refine contDiff_iff_contDiffAt.2 fun t₀ => ?_
  by_cases h : ς < ‖(t₀ : AddCircle ℓ)‖
  · have hev : circleDistBump ς ℓ =ᶠ[𝓝 t₀] fun _ => 0 := by
      filter_upwards [hcont.continuousAt.eventually (Ioi_mem_nhds h)] with t ht
      exact cosBump_eq_zero_of_le hς (le_of_lt ht)
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have h' : ‖(t₀ : AddCircle ℓ)‖ ≤ ς := not_lt.1 h
    set i : ℤ := round (ℓ⁻¹ * t₀)
    have hu : |t₀ - i * ℓ| ≤ ς := by
      rw [← AddCircle.norm_eq]
      exact h'
    have hnear : ∀ᶠ t in 𝓝 t₀, |t - i * ℓ| < ℓ / 2 := by
      have hc : Continuous fun t : ℝ => |t - i * ℓ| := by fun_prop
      exact hc.continuousAt.eventually (Iio_mem_nhds (by linarith))
    have hc : ContDiff ℝ 1 fun t : ℝ => cosBump ς |t - i * ℓ| :=
      (contDiff_cosBump_abs hς).comp (contDiff_id.sub contDiff_const)
    refine hc.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hnear] with t ht
    have hper : ((i * ℓ : ℝ) : AddCircle ℓ) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨i, by simp⟩
    have hcoe : (t : AddCircle ℓ) = ((t - i * ℓ : ℝ) : AddCircle ℓ) := by
      rw [AddCircle.coe_sub, hper, sub_zero]
    have hn : ‖((t - i * ℓ : ℝ) : AddCircle ℓ)‖ = |t - i * ℓ| :=
      (AddCircle.norm_coe_eq_abs_iff ℓ hℓ0.ne').2 (by rw [abs_of_pos hℓ0]; exact le_of_lt ht)
    rw [circleDistBump, hcoe, hn]
def gridBump (ς ℓ : ℝ) (k : ℕ) (x : AddCircle ℓ) : ℝ :=
  cosBump ς ‖x - ((k * ς : ℝ) : AddCircle ℓ)‖
theorem gridBump_coe (ς ℓ : ℝ) (k : ℕ) (t : ℝ) :
    gridBump ς ℓ k (t : AddCircle ℓ) = circleDistBump ς ℓ (t - k * ς) := by
  rw [gridBump, circleDistBump, AddCircle.coe_sub]
theorem abs_gridBump_sub_le {ς : ℝ} (hς : 0 < ς) (k : ℕ) (x y : AddCircle ℓ) :
    |gridBump ς ℓ k x - gridBump ς ℓ k y| ≤ Real.pi / (2 * ς) * ‖x - y‖ := by
  refine (abs_cosBump_sub_le hς _ _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine (abs_norm_sub_norm_le _ _).trans (le_of_eq ?_)
  congr 1
  abel
theorem fin_eq_of_intCast_sub_eq_mul {N : ℕ} {k k' : Fin N} {q : ℤ}
    (h : (k : ℤ) - k' = q * N) : k = k' := by
  have h₁ : (k : ℤ) % N = k := Int.emod_eq_of_lt (by omega) (by omega)
  have h₂ : (k' : ℤ) % N = k' := Int.emod_eq_of_lt (by omega) (by omega)
  have h₃ : (k : ℤ) = k' + q * N := by linarith
  rw [h₃, Int.add_mul_emod_self_right, h₂] at h₁
  exact Fin.ext (by omega)
theorem exists_fin_intCast_eq_add_mul {N : ℕ} (hN : 0 < N) (j : ℤ) :
    ∃ (k : Fin N) (q : ℤ), (k : ℤ) = j + q * N := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have h₁ := Int.emod_nonneg j hN'.ne'
  have h₂ := Int.emod_lt_of_pos j hN'
  refine ⟨⟨(j % N).toNat, by omega⟩, -(j / N), ?_⟩
  have h₃ := Int.emod_add_mul_ediv j N
  simp only [Int.toNat_of_nonneg h₁]
  linarith [mul_comm (N : ℤ) (j / N)]
theorem sum_gridBump {ς : ℝ} (hς : 0 < ς) {N : ℕ} (hN : 2 ≤ N) (hℓ : ℓ = N * ς)
    (x : AddCircle ℓ) : ∑ k : Fin N, gridBump ς ℓ k x = 1 := by
  have hN0 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hℓ0 : 0 < ℓ := by rw [hℓ]; positivity
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  set j : ℤ := ⌊t / ς⌋
  set u : ℝ := t - j * ς
  have hu0 : 0 ≤ u := by
    have := Int.floor_le (t / ς)
    have h' : (j : ℝ) * ς ≤ t := by rwa [le_div_iff₀ hς] at this
    simp only [u]
    linarith
  have hu1 : u < ς := by
    have := Int.lt_floor_add_one (t / ς)
    have h' : t < ((j : ℝ) + 1) * ς := by rwa [div_lt_iff₀ hς] at this
    simp only [u]
    linarith
  have hper : ∀ q : ℤ, ((q * ℓ : ℝ) : AddCircle ℓ) = 0 := fun q => by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨q, by simp⟩
  have hshift : ∀ (k : ℕ) (e q : ℤ), (k : ℤ) = e + q * N →
      (t - k * ς : ℝ) = (t - e * ς) - q * ℓ := fun k e q h => by
    have h' : (k : ℝ) = e + q * N := by exact_mod_cast h
    rw [h', hℓ]
    ring
  have hval : ∀ (k : ℕ) (e q : ℤ), (k : ℤ) = e + q * N → |t - e * ς| ≤ ℓ / 2 →
      gridBump ς ℓ k (t : AddCircle ℓ) = cosBump ς |t - e * ς| := fun k e q h hs => by
    rw [show (QuotientAddGroup.mk t : AddCircle ℓ) = (t : AddCircle ℓ) from rfl, gridBump_coe,
      circleDistBump, hshift k e q h, AddCircle.coe_sub, hper, sub_zero,
      (AddCircle.norm_coe_eq_abs_iff ℓ hℓ0.ne').2 (by rwa [abs_of_pos hℓ0])]
  have hs : ς ≤ ℓ / 2 := by
    rw [hℓ]
    nlinarith
  obtain ⟨k₀, q₀, hk₀⟩ := exists_fin_intCast_eq_add_mul (N := N) (by omega) j
  obtain ⟨k₁, q₁, hk₁⟩ := exists_fin_intCast_eq_add_mul (N := N) (by omega) (j + 1)
  have hne : k₀ ≠ k₁ := by
    intro h
    rw [h] at hk₀
    have hdvd : (N : ℤ) ∣ 1 := ⟨q₀ - q₁, by linarith⟩
    have := Int.le_of_dvd one_pos hdvd
    omega
  have hv₀ : gridBump ς ℓ k₀ (t : AddCircle ℓ) = cosBump ς u := by
    have hu : |t - j * ς| = u := abs_of_nonneg hu0
    rw [hval k₀ j q₀ hk₀ (by rw [hu]; linarith), hu]
  have hv₁ : gridBump ς ℓ k₁ (t : AddCircle ℓ) = cosBump ς (ς - u) := by
    have he : t - ((j + 1 : ℤ) : ℝ) * ς = u - ς := by
      push_cast
      simp only [u]
      ring
    have hu : |t - ((j + 1 : ℤ) : ℝ) * ς| = ς - u := by
      rw [he, abs_of_nonpos (by linarith)]
      ring
    rw [hval k₁ (j + 1) q₁ hk₁ (by rw [hu]; linarith), hu]
  have hv : ∀ c : Fin N, c ≠ k₀ ∧ c ≠ k₁ → gridBump ς ℓ c (t : AddCircle ℓ) = 0 := by
    rintro c ⟨hc₀, hc₁⟩
    rw [gridBump_coe, circleDistBump]
    refine cosBump_eq_zero_of_le hς ?_
    rw [AddCircle.norm_eq]
    set i : ℤ := round (ℓ⁻¹ * (t - c * ς))
    set n : ℤ := j - c - i * N
    have hn : t - c * ς - i * ℓ = u + n * ς := by
      simp only [u, n]
      rw [hℓ]
      push_cast
      ring
    have hn0 : n ≠ 0 := by
      intro h
      refine hc₀ (fin_eq_of_intCast_sub_eq_mul (q := -i - q₀) ?_)
      have h' : j - (c : ℤ) - i * N = 0 := h
      linarith
    have hn1 : n ≠ -1 := by
      intro h
      refine hc₁ (fin_eq_of_intCast_sub_eq_mul (q := -i - q₁) ?_)
      have h' : j - (c : ℤ) - i * N = -1 := h
      linarith
    rw [hn]
    rcases lt_or_gt_of_ne hn0 with h | h
    · have h₂ : n ≤ -2 := by omega
      have h₃ : (n : ℝ) ≤ -2 := by exact_mod_cast h₂
      refine le_trans ?_ (neg_le_abs _)
      nlinarith
    · have h₂ : 1 ≤ n := h
      have h₃ : (1 : ℝ) ≤ n := by exact_mod_cast h₂
      refine le_trans ?_ (le_abs_self _)
      nlinarith
  rw [show (QuotientAddGroup.mk t : AddCircle ℓ) = (t : AddCircle ℓ) from rfl,
    Finset.sum_eq_add k₀ k₁ hne (fun c _ hc => hv c hc) (by simp) (by simp), hv₀, hv₁]
  have h₁ : min u ς = u := min_eq_left (le_of_lt hu1)
  have h₂ : min (ς - u) ς = ς - u := min_eq_left (by linarith)
  have h₃ : Real.pi * (ς - u) / (2 * ς) = Real.pi / 2 - Real.pi * u / (2 * ς) := by
    field_simp
  rw [cosBump, cosBump, h₁, h₂, h₃, Real.cos_pi_div_two_sub]
  exact Real.cos_sq_add_sin_sq _
theorem gridBump_nonneg (ς ℓ : ℝ) (k : ℕ) (x : AddCircle ℓ) : 0 ≤ gridBump ς ℓ k x :=
  cosBump_nonneg _ _
theorem gridBump_le_one (ς ℓ : ℝ) (k : ℕ) (x : AddCircle ℓ) : gridBump ς ℓ k x ≤ 1 :=
  cosBump_le_one _ _
theorem abs_prod_sub_prod_le_sum_abs {ι : Type*} (t : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i, a i ∈ Icc (0 : ℝ) 1) (hb : ∀ i, b i ∈ Icc (0 : ℝ) 1) :
    |∏ i ∈ t, a i - ∏ i ∈ t, b i| ≤ ∑ i ∈ t, |a i - b i| := by apply _root_.YangMills.Construction.Weighted.VertexPartition.abs_prod_sub_prod_le_sum <;> assumption
def cellWeight (ς ℓ : ℝ) {N : ℕ} (a : Fin 4 → Fin N) (x : Torus4 ℓ) : ℝ :=
  ∏ μ, gridBump ς ℓ (a μ) (x μ)
variable {ς : ℝ} {N : ℕ}
theorem cellWeight_mem_Icc (a : Fin 4 → Fin N) (x : Torus4 ℓ) :
    cellWeight ς ℓ a x ∈ Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg fun _ _ => gridBump_nonneg _ _ _ _,
    Finset.prod_le_one (fun _ _ => gridBump_nonneg _ _ _ _) fun _ _ => gridBump_le_one _ _ _ _⟩
theorem sum_cellWeight (hς : 0 < ς) (hN : 2 ≤ N) (hℓ : ℓ = N * ς) (x : Torus4 ℓ) :
    ∑ a : Fin 4 → Fin N, cellWeight ς ℓ a x = 1 := by
  have h := Finset.prod_univ_sum (fun _ : Fin 4 => (Finset.univ : Finset (Fin N)))
    (fun μ k => gridBump ς ℓ k (x μ))
  rw [Fintype.piFinset_univ] at h
  simp only [cellWeight]
  rw [← h]
  simp [sum_gridBump hς hN hℓ]
theorem abs_cellWeight_sub_le (hς : 0 < ς) (a : Fin 4 → Fin N) (x y : Torus4 ℓ) :
    |cellWeight ς ℓ a x - cellWeight ς ℓ a y| ≤ Real.pi / ς * torusEuclidNorm (x - y) := by
  have h₁ := abs_prod_sub_prod_le_sum_abs Finset.univ (fun μ => gridBump ς ℓ (a μ) (x μ))
    (fun μ => gridBump ς ℓ (a μ) (y μ))
    (fun μ => ⟨gridBump_nonneg _ _ _ _, gridBump_le_one _ _ _ _⟩)
    (fun μ => ⟨gridBump_nonneg _ _ _ _, gridBump_le_one _ _ _ _⟩)
  have h₂ : ∑ μ, |gridBump ς ℓ (a μ) (x μ) - gridBump ς ℓ (a μ) (y μ)| ≤
      Real.pi / (2 * ς) * ∑ μ, ‖(x - y) μ‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun μ _ => abs_gridBump_sub_le hς _ _ _
  have h₃ : ∑ μ, ‖(x - y) μ‖ ≤ 2 * torusEuclidNorm (x - y) := by
    rw [AmbientPoints.torusEuclidNorm_eq_sqrt]
    have hcs : (∑ μ, ‖(x - y) μ‖) ^ 2 ≤ (4 : ℝ) * ∑ μ, ‖(x - y) μ‖ ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 4)))
        (f := fun μ => ‖(x - y) μ‖)
    have hle : (∑ μ, ‖(x - y) μ‖) / 2 ≤ Real.sqrt (∑ μ, ‖(x - y) μ‖ ^ 2) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [div_pow]
      linarith
    linarith
  have hc : 0 ≤ Real.pi / (2 * ς) := by positivity
  calc |cellWeight ς ℓ a x - cellWeight ς ℓ a y| ≤ _ := h₁
    _ ≤ _ := h₂
    _ ≤ Real.pi / (2 * ς) * (2 * torusEuclidNorm (x - y)) := mul_le_mul_of_nonneg_left h₃ hc
    _ = Real.pi / ς * torusEuclidNorm (x - y) := by
      field_simp
theorem contDiff_cellWeight_comp (hς : 0 < ς) (hℓ : 2 * ς < ℓ) (a : Fin 4 → Fin N) :
    ContDiff ℝ 1 (cellWeight ς ℓ a ∘ torusProj ℓ) := by
  have h : cellWeight ς ℓ a ∘ torusProj ℓ =
      fun y => ∏ μ, circleDistBump ς ℓ (y μ - (a μ : ℕ) * ς) := by
    funext y
    simp only [Function.comp_apply, cellWeight]
    exact Finset.prod_congr rfl fun μ _ => gridBump_coe _ _ _ _
  rw [h]
  refine contDiff_prod fun μ _ => (contDiff_circleDistBump hς hℓ).comp ?_
  exact (contDiff_apply ℝ ℝ μ).sub contDiff_const
def cellCentre (ς ℓ : ℝ) {N : ℕ} (a : Fin 4 → Fin N) : Torus4 ℓ :=
  fun μ => (((a μ : ℕ) * ς : ℝ) : AddCircle ℓ)
theorem torusEuclidNorm_sub_cellCentre_le (hς : 0 < ς) (a : Fin 4 → Fin N) {x : Torus4 ℓ}
    (h : cellWeight ς ℓ a x ≠ 0) : torusEuclidNorm (x - cellCentre ς ℓ a) ≤ 2 * ς := by
  have hμ : ∀ μ, ‖(x - cellCentre ς ℓ a) μ‖ ≤ ς := by
    intro μ
    by_contra hlt
    refine h (Finset.prod_eq_zero (Finset.mem_univ μ) ?_)
    exact cosBump_eq_zero_of_le hς (le_of_lt (not_le.1 hlt))
  rw [AmbientPoints.torusEuclidNorm_eq_sqrt]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have hsq : ∀ μ, ‖(x - cellCentre ς ℓ a) μ‖ ^ 2 ≤ ς ^ 2 := fun μ =>
    pow_le_pow_left₀ (norm_nonneg _) (hμ μ) 2
  calc ∑ μ, ‖(x - cellCentre ς ℓ a) μ‖ ^ 2 ≤ ∑ _μ : Fin 4, ς ^ 2 :=
        Finset.sum_le_sum fun μ _ => hsq μ
    _ = (2 * ς) ^ 2 := by
      simp
      ring
open YangMills.Construction.ToriAtArbitraryCouplings YangMills.Construction.AmbientPoints
variable {D : Conventions.StandingParameters} {n : ℕ}
theorem closedSupport_eq_tsupport (f : Pt D .torus → ℝ) :
    (TorusSide.ofStandingParameters D).closedSupport .torus f = tsupport f :=
  (closure_eq_closureWrt (Function.support f)).symm
theorem le_torusTupleGap_iff (f : Fin n → Pt D .torus → ℝ) (e : ℝ≥0∞) :
    e ≤ torusTupleGap f ↔ ∀ i k, i ≠ k →
      e ≤ AmbientPoints.setDist D .torus (tsupport (f i)) (tsupport (f k)) := by
  have h₁ : torusTupleGap f = ⨅ (i : Fin n) (k : Fin n) (_ : i ≠ k),
      AmbientPoints.setDist D .torus (tsupport (f i)) (tsupport (f k)) := by
    refine ((TorusSide.ofStandingParameters D).gapAllLengths_eq_supportGap .torus _).trans ?_
    refine ((TorusSide.ofStandingParameters D).supportGap_ofFn .torus f).trans ?_
    refine iInf_congr fun i => iInf_congr fun k => iInf_congr fun _ => ?_
    exact congrArg₂ (AmbientPoints.setDist D .torus) (closedSupport_eq_tsupport (f i))
      (closedSupport_eq_tsupport (f k))
  rw [h₁]
  simp only [le_iInf_iff]
theorem setDist_anti {A A' B B' : Set (Pt D .torus)} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    AmbientPoints.setDist D .torus A B ≤ AmbientPoints.setDist D .torus A' B' :=
  le_iInf₂ fun a ha => le_iInf₂ fun b hb => iInf₂_le_of_le a (hA ha) (iInf₂_le b (hB hb))
theorem sharpNormTorus_nonneg {ℓ M : ℝ} (f : Torus4 ℓ → ℝ) :
    0 ≤ TestFunctions.sharpNormTorus M f :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
theorem abs_apply_le_of_separated (hyp : LipschitzEstimates.Combined) (hL : 8 * 105 ^ 4 ≤ D.L)
    (m' : ℕ) (d c : ℝ) (hd : 0 < d) (hc : 0 ≤ c) (p : ℕ) (hp : 3 ≤ p)
    (Ψ : separatedTuples D .torus n → ℝ) (hΨ : IsTupleMultilinear Ψ)
    (hb : BoundedOnSmallBallTuples ((D.L : ℝ) ^ m') d c p Ψ)
    (h : separatedTuples D .torus n) (hsep : ENNReal.ofReal d ≤ torusTupleGap h.1) :
    |Ψ h| ≤ smallBallConstant ((D.L : ℝ) ^ m') p ^ n * c *
      ∏ i, TestFunctions.sharpNormTorus ((D.L : ℝ) ^ m') (h.1 i) := by
  classical
  set ℓ : ℝ := PeriodicLattice.torusSide D.L D.m with hℓdef
  set M : ℝ := (D.L : ℝ) ^ m' with hMdef
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hL1 : (1 : ℝ) ≤ D.L := by
    have h₁ := D.isAdmissible.2
    exact_mod_cast (by omega : 1 ≤ D.L)
  have hL13 : (13 : ℝ) ≤ D.L := by exact_mod_cast D.isAdmissible.2
  have hℓ26 : 26 ≤ ℓ := by
    have hm : (D.m : ℕ) ≠ 0 := D.m.ne_zero
    have h₁ : (D.L : ℝ) ≤ (D.L : ℝ) ^ (D.m : ℕ) := le_self_pow₀ hL1 hm
    simp only [hℓdef, PeriodicLattice.torusSide]
    linarith
  set ς : ℝ := ℓ / (2 * p) with hςdef
  have hς : 0 < ς := by positivity
  set N : ℕ := 2 * p with hNdef
  have hN2 : 2 ≤ N := by omega
  have hNℓ : ℓ = (N : ℝ) * ς := by
    simp only [hςdef, hNdef]
    push_cast
    field_simp
  have h2ς : 2 * ς < ℓ := by
    have : ς * (2 * p) = ℓ := by
      simp only [hςdef]
      field_simp
    nlinarith
  have hball : 2 * ς = ℓ / p := by
    simp only [hςdef]
    field_simp
  set K : ℝ := 1 + 40 * M * (Real.pi / ς) with hKdef
  have hπς : Real.pi / ς ≤ p / 4 := by
    rw [div_le_iff₀ hς]
    have : (p : ℝ) / 4 * ς = ℓ / 8 := by
      simp only [hςdef]
      field_simp
      ring
    rw [this]
    linarith [Real.pi_lt_d2]
  have hK : K ≤ 1 + 10 * p * M := by
    have : 40 * M * (Real.pi / ς) ≤ 40 * M * (p / 4) :=
      mul_le_mul_of_nonneg_left hπς (by positivity)
    simp only [hKdef]
    linarith
  obtain ⟨⟨hbounds, -, -⟩, hcutting, -, -, -⟩ := hyp (TorusSide.ofStandingParameters D) hL m' .torus
  have hsupp : ∀ i k, i ≠ k → ENNReal.ofReal d ≤
      AmbientPoints.setDist D .torus (tsupport (h.1 i)) (tsupport (h.1 k)) :=
    (le_torusTupleGap_iff h.1 _).1 hsep
  let A : Fin n → Set (Pt D .torus) := fun i => tsupport (h.1 i)
  have hA : Pairwise fun i j => AmbientPoints.PositivelySeparated D .torus (A i) (A j) := by
    intro i j hij h0
    have h₁ : ENNReal.ofReal d ≤ AmbientPoints.setDist D .torus (A i) (A j) := hsupp i j hij
    rw [h0] at h₁
    exact absurd (ENNReal.ofReal_pos.2 hd) (not_lt.2 h₁)
  let χ : (Fin 4 → Fin N) → Pt D .torus → ℝ := fun a => cellWeight ς ℓ a
  let piece : Fin n → (Fin 4 → Fin N) → Pt D .torus → ℝ := fun i a x => χ a x * h.1 i x
  have hmemh : ∀ i, h.1 i ∈ c1Submodule (A i) := fun i =>
    ⟨(h.2.1 i).1, (h.2.1 i).2, subset_rfl⟩
  have hpiece_left : ∀ i a, tsupport (piece i a) ⊆ tsupport (χ a) := fun i a =>
    tsupport_mul_subset_left
  have hpiece_right : ∀ i a, tsupport (piece i a) ⊆ tsupport (h.1 i) := fun i a =>
    tsupport_mul_subset_right
  have hmempiece : ∀ i a, piece i a ∈ c1Submodule (A i) := by
    intro i a
    refine ⟨?_, (h.2.1 i).2.of_isClosed_subset (isClosed_tsupport _) (hpiece_right i a),
      hpiece_right i a⟩
    have h₁ : ContDiff ℝ 1 (cellWeight ς ℓ a ∘ torusProj ℓ) := contDiff_cellWeight_comp hς h2ς a
    have h₂ : ContDiff ℝ 1 (h.1 i ∘ AmbientPoints.proj D .torus) := (h.2.1 i).1
    exact h₁.mul h₂
  let g : (i : Fin n) → c1Submodule (A i) := fun i => ⟨h.1 i, hmemh i⟩
  let g' : (i : Fin n) → (Fin 4 → Fin N) → c1Submodule (A i) :=
    fun i a => ⟨piece i a, hmempiece i a⟩
  have hsum : ∀ i, g i = ∑ a, g' i a := by
    intro i
    apply Subtype.ext
    rw [Submodule.coe_sum]
    funext x
    rw [Finset.sum_apply]
    change h.1 i x = ∑ a, cellWeight ς ℓ a x * h.1 i x
    rw [← Finset.sum_mul, sum_cellWeight hς hN2 hNℓ x, one_mul]
  obtain ⟨Lm, hLm⟩ := hΨ A hA
  have hexpand : Ψ h = ∑ r : Fin n → Fin 4 → Fin N, Lm fun i => g' i (r i) := by
    have h₁ : Ψ h = Lm g := (hLm g).symm
    rw [h₁, ← Lm.map_sum]
    exact congrArg Lm (funext hsum)
  have hsharp : ∀ i a, TestFunctions.sharpNormTorus M (piece i a) ≤
      K * TestFunctions.sharpNormTorus M (h.1 i) := by
    intro i a
    have hmem : h.1 i ∈ (TorusSide.ofStandingParameters D).c1CompactSet .torus := by
      refine ⟨(h.2.1 i).1, ?_⟩
      rw [closedSupport_eq_tsupport]
      exact (isCompact_iff_isCompactWrt _).1 (h.2.1 i).2
    obtain ⟨hbd, hlip, -⟩ := hbounds (h.1 i) hmem
    have hχlip : TestFunctions.IsLipschitzFor
        ((TorusSide.ofStandingParameters D).pointDist .torus) (χ a) :=
      ⟨Real.pi / ς, by positivity, fun x y => abs_cellWeight_sub_le hς a x y⟩
    have hcut := (hcutting ℝ (χ a) (h.1 i) (fun x => cellWeight_mem_Icc a x) hχlip hbd hlip).2.1
    have hlipχ : TestFunctions.lipConstTorus (ℓ := ℓ) (χ a) ≤ Real.pi / ς :=
      csInf_le ⟨0, fun C hC => hC.1⟩ ⟨by positivity, fun x y => abs_cellWeight_sub_le hς a x y⟩
    have hcast : ((cubeEdge (TorusSide.ofStandingParameters D).L m' : ℕ) : ℝ) = M := by
      simp [cubeEdge, hMdef, TorusSide.ofStandingParameters]
    have hconv : ∀ f : Pt D .torus → ℝ,
        (TorusSide.ofStandingParameters D).sharpNormAt m' .torus f =
          TestFunctions.sharpNormTorus M f := by
      intro f
      refine ((TorusSide.ofStandingParameters D).sharpNormAt_eq m' .torus f).trans ?_
      rw [hcast]
      rfl
    refine ((hconv (piece i a)).symm.le.trans hcut).trans ?_
    have h₁ : (TorusSide.ofStandingParameters D).lipConst .torus (χ a) ≤ Real.pi / ς := hlipχ
    have h₂ : 40 * M * (TorusSide.ofStandingParameters D).lipConst .torus (χ a) ≤
        40 * M * (Real.pi / ς) :=
      mul_le_mul_of_nonneg_left h₁ (by positivity)
    rw [hcast]
    refine (le_of_eq (congrArg _ (hconv (h.1 i)))).trans
      (mul_le_mul_of_nonneg_right ?_ (sharpNormTorus_nonneg _))
    simp only [hKdef]
    linarith
  have hterm : ∀ r : Fin n → Fin 4 → Fin N, |Lm fun i => g' i (r i)| ≤
      c * ∏ i, (K * TestFunctions.sharpNormTorus M (h.1 i)) := by
    intro r
    rw [hLm]
    refine (hb _ ?_ ?_).trans (mul_le_mul_of_nonneg_left (Finset.prod_le_prod
      (fun i _ => sharpNormTorus_nonneg _) fun i _ => hsharp i (r i)) hc)
    · refine (le_torusTupleGap_iff _ _).2 fun i k hik => (hsupp i k hik).trans ?_
      exact setDist_anti (hpiece_right i (r i)) (hpiece_right k (r k))
    · intro i
      refine ⟨cellCentre ς ℓ (r i), (hpiece_left i (r i)).trans (closure_minimal ?_ ?_)⟩
      · intro x hx
        have h₁ := torusEuclidNorm_sub_cellCentre_le hς (r i) (x := x) hx
        rw [hball] at h₁
        exact h₁
      · have hcl : IsClosed {y : Pt D .torus |
            dist y (cellCentre ς ℓ (r i) : Pt D .torus) ≤ ℓ / p} :=
          isClosed_le (continuous_id.dist continuous_const) continuous_const
        exact hcl
  have hcard : ((Fintype.card (Fin n → Fin 4 → Fin N) : ℕ) : ℝ) = ((N : ℝ) ^ 4) ^ n := by
    simp
  have hNp : (N : ℝ) = 2 * p := by
    simp [hNdef]
  have hΘ : (N : ℝ) ^ 4 * K ≤ smallBallConstant M p := by
    rw [smallBallConstant, hNp]
    exact mul_le_mul_of_nonneg_left hK (by positivity)
  have hprod : 0 ≤ ∏ i, TestFunctions.sharpNormTorus M (h.1 i) :=
    Finset.prod_nonneg fun i _ => sharpNormTorus_nonneg _
  calc |Ψ h| = |∑ r : Fin n → Fin 4 → Fin N, Lm fun i => g' i (r i)| := by rw [hexpand]
    _ ≤ ∑ r : Fin n → Fin 4 → Fin N, |Lm fun i => g' i (r i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Fin n → Fin 4 → Fin N, c * ∏ i, (K * TestFunctions.sharpNormTorus M (h.1 i)) :=
      Finset.sum_le_sum fun r _ => hterm r
    _ = ((N : ℝ) ^ 4 * K) ^ n * c * ∏ i, TestFunctions.sharpNormTorus M (h.1 i) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
      ring
    _ ≤ smallBallConstant M p ^ n * c * ∏ i, TestFunctions.sharpNormTorus M (h.1 i) := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hc) hprod
      exact pow_le_pow_left₀ (by positivity) hΘ n
theorem smallBallsToSeparatedTuples_holds (hyp : LipschitzEstimates.Combined) :
    SmallBallsToSeparatedTuples := by
  intro D hL M hM n _ d c hd hc p hp Ψ hΨ hb
  obtain ⟨m', rfl⟩ := hM
  refine ⟨fun h hsep => abs_apply_le_of_separated hyp hL m' d c hd hc p hp Ψ hΨ hb h hsep, ?_⟩
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hL1 : (1 : ℝ) ≤ D.L := by
    have h₁ := D.isAdmissible.2
    exact_mod_cast (by omega : 1 ≤ D.L)
  have hM : (1 : ℝ) ≤ (D.L : ℝ) ^ m' := one_le_pow₀ hL1
  have h₁ : (1 : ℝ) ≤ (2 * (p : ℝ)) ^ 4 := one_le_pow₀ (by linarith)
  have h₂ : (1 : ℝ) ≤ 1 + 10 * (p : ℝ) * (D.L : ℝ) ^ m' := by
    have : 0 ≤ 10 * (p : ℝ) * (D.L : ℝ) ^ m' := by positivity
    linarith
  rw [smallBallConstant]
  exact one_le_mul_of_one_le_of_one_le h₁ h₂
end YangMills.Construction.TorusPowers.SmallBallPartition
end
