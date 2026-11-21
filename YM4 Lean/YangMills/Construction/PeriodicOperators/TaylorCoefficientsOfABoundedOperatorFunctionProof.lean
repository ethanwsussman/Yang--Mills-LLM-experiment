import YangMills.Construction.PeriodicOperators.MatricesOfALocalOperatorFunctionOnATorusProof
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfABoundedOperatorFunction
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsReadOnALargerSetOfIndices
import Mathlib
set_option autoImplicit false
open Filter Topology Asymptotics Set Metric
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.CauchyTaylorBounds
open Tower.SmoothingContraction (OpNormLE)
open Quotients (MapsFiniteNorm finiteNormSpace)
open Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
theorem eq_zero_of_norm_le_pow_succ {f : ℂ → ℂ} (hf : ContinuousAt f 0) {K : ℝ} {n : ℕ}
    (h : ∀ᶠ σ in 𝓝[≠] (0 : ℂ), ‖f σ‖ ≤ K * ‖σ‖ ^ (n + 1)) : f 0 = 0 := by
  have t₁ : Tendsto f (𝓝[≠] 0) (𝓝 (f 0)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  have t₂ : Tendsto (fun σ : ℂ => K * ‖σ‖ ^ (n + 1)) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous fun σ : ℂ => K * ‖σ‖ ^ (n + 1) := by fun_prop
    have := hc.tendsto 0
    simp only [norm_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique t₁ (squeeze_zero_norm' h t₂)
theorem quadratic_coeffs_eq_zero_of_isBigO_cube {d₀ d₁ d₂ : ℂ}
    (h : (fun σ : ℂ => d₀ + σ * d₁ + σ ^ 2 * d₂) =O[𝓝 0] fun σ : ℂ => σ ^ 3) :
    d₀ = 0 ∧ d₁ = 0 ∧ d₂ = 0 := by
  obtain ⟨K, hK⟩ := h.bound
  have h₀ : d₀ = 0 := by
    have := hK.self_of_nhds
    simpa using this
  subst h₀
  have hp : ∀ᶠ σ in 𝓝[≠] (0 : ℂ), σ ≠ 0 ∧
      ‖(0 : ℂ) + σ * d₁ + σ ^ 2 * d₂‖ ≤ K * ‖σ ^ 3‖ :=
    (eventually_mem_nhdsWithin).and (hK.filter_mono nhdsWithin_le_nhds)
  have h₁ : d₁ = 0 := by
    have := eq_zero_of_norm_le_pow_succ (f := fun σ => d₁ + σ * d₂) (K := K) (n := 1)
      (by fun_prop) (hp.mono fun σ ⟨h0, hb⟩ => ?_)
    · simpa using this
    · have hσ : 0 < ‖σ‖ := norm_pos_iff.2 h0
      have e : (0 : ℂ) + σ * d₁ + σ ^ 2 * d₂ = σ * (d₁ + σ * d₂) := by ring
      rw [e, norm_mul, norm_pow] at hb
      have : ‖σ‖ * ‖d₁ + σ * d₂‖ ≤ ‖σ‖ * (K * ‖σ‖ ^ (1 + 1)) := by
        calc _ ≤ K * ‖σ‖ ^ 3 := hb
          _ = _ := by ring
      exact le_of_mul_le_mul_left this hσ
  subst h₁
  have h₂ : d₂ = 0 := by
    have := eq_zero_of_norm_le_pow_succ (f := fun _ => d₂) (K := K) (n := 0)
      continuousAt_const (hp.mono fun σ ⟨h0, hb⟩ => ?_)
    · exact this
    · have hσ : 0 < ‖σ‖ ^ 2 := pow_pos (norm_pos_iff.2 h0) 2
      have e : (0 : ℂ) + σ * 0 + σ ^ 2 * d₂ = σ ^ 2 * d₂ := by ring
      rw [e, norm_mul, norm_pow, norm_pow] at hb
      have : ‖σ‖ ^ 2 * ‖d₂‖ ≤ ‖σ‖ ^ 2 * (K * ‖σ‖ ^ (0 + 1)) := by
        calc _ ≤ K * ‖σ‖ ^ 3 := hb
          _ = _ := by ring
      exact le_of_mul_le_mul_left this hσ
  exact ⟨rfl, rfl, h₂⟩
theorem cauchy_estimate_first_second {p : ℂ → ℂ} {a₀ a₁ a₂ : ℂ} {r B : ℝ} (hr : 0 < r)
    (hp : DifferentiableOn ℂ p (closedBall 0 r)) (hB : ∀ σ ∈ closedBall (0 : ℂ) r, ‖p σ‖ ≤ B)
    (hx : (fun σ : ℂ => p σ - (a₀ + σ * a₁ + σ ^ 2 * a₂)) =O[𝓝 0] fun σ : ℂ => σ ^ 3) :
    ‖a₁‖ ≤ B / r ∧ ‖a₂‖ ≤ B / r ^ 2 := by
  have han : AnalyticAt ℂ p 0 := hp.analyticAt (closedBall_mem_nhds 0 hr)
  have hs := han.hasFPowerSeriesAt
  have hO := hs.isBigO_sub_partialSum_pow 3
  have hcl : DiffContOnCl ℂ p (ball 0 r) :=
    (hp.mono closure_ball_subset_closedBall |>.diffContOnCl)
  have hb : ∀ z ∈ sphere (0 : ℂ) r, ‖p z‖ ≤ B := fun z hz => hB z (sphere_subset_closedBall hz)
  have c₁ := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hr hcl hb
  have c₂ := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hr hcl hb
  set b₀ : ℂ := iteratedDeriv 0 p 0 / (Nat.factorial 0 : ℂ) with hb₀
  set b₁ : ℂ := iteratedDeriv 1 p 0 / (Nat.factorial 1 : ℂ) with hb₁
  set b₂ : ℂ := iteratedDeriv 2 p 0 / (Nat.factorial 2 : ℂ) with hb₂
  have hpart : ∀ y : ℂ, (FormalMultilinearSeries.ofScalars ℂ
      (fun n => iteratedDeriv n p 0 / (n.factorial : ℂ))).partialSum 3 y =
      b₀ + y * b₁ + y ^ 2 * b₂ := by
    intro y
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_zero,
      FormalMultilinearSeries.ofScalars_apply_eq, hb₀, hb₁, hb₂]
    simp
    ring
  have hO' : (fun σ : ℂ => p σ - (b₀ + σ * b₁ + σ ^ 2 * b₂)) =O[𝓝 0] fun σ : ℂ => σ ^ 3 := by
    refine (hO.congr_left fun y => ?_).trans (IsBigO.of_bound 1 (Eventually.of_forall fun y => ?_))
    · rw [hpart, zero_add]
    · simp
  have hd := hx.sub hO'
  have hz := quadratic_coeffs_eq_zero_of_isBigO_cube (d₀ := b₀ - a₀) (d₁ := b₁ - a₁) (d₂ := b₂ - a₂)
    (hd.congr_left fun σ => by ring)
  have e₁ : a₁ = b₁ := (sub_eq_zero.1 hz.2.1).symm
  have e₂ : a₂ = b₂ := (sub_eq_zero.1 hz.2.2).symm
  rw [e₁, e₂, hb₁, hb₂]
  constructor
  · simpa using c₁
  · rw [norm_div]
    have : ‖((Nat.factorial 2 : ℕ) : ℂ)‖ = 2 := by simp [Nat.factorial]
    rw [this, div_le_iff₀ (by norm_num)]
    calc _ ≤ _ := c₂
      _ = _ := by simp [Nat.factorial]; ring
section Entries
variable {F I I' : PeriodicData}
theorem fieldValues_smul {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S) (σ : ℂ) (ζ : F.Carrier → ℂ) :
    fieldValues e (σ • ζ) = σ • fieldValues e ζ :=
  rfl
theorem fieldValues_add {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S) (ζ ζ' : F.Carrier → ℂ) :
    fieldValues e (ζ + ζ') = fieldValues e ζ + fieldValues e ζ' :=
  rfl
theorem coe_equiv_injective {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S) :
    Function.Injective fun j => ((e j : S) : F.Carrier) :=
  fun _ _ h => e.injective (Subtype.ext h)
theorem fieldValues_fieldExtend {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S)
    (z : Coordinates.ComplexCoordinates l) : fieldValues e (fieldExtend e z) = z := by apply _root_.YangMills.Construction.PeriodicOperators.LocalTorusMatrices.fieldValues_fieldExtend <;> assumption
theorem norm_fieldExtend_le {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S) {ξ : F.Carrier → ℂ}
    {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ κ, ‖ξ κ‖ ≤ b) (κ : F.Carrier) :
    ‖fieldExtend e (fieldValues e ξ) κ‖ ≤ b := by
  by_cases h : ∃ j, ((e j : S) : F.Carrier) = κ
  · obtain ⟨j, rfl⟩ := h
    have := (coe_equiv_injective e).extend_apply (fieldValues e ξ) 0 j
    simp only [fieldExtend] at *
    rw [this]
    exact hb _
  · simp only [fieldExtend]
    rw [Function.extend_apply' _ _ _ h]
    simpa using hb0
theorem entry_isBigO_expansion (hRead : CoeffsOnSuperset.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ₀ R : ℝ}
    (hM : IsLocalWith F I I' T ρ₀ R) {ζ : F.Carrier → ℂ} {b : ℝ}
    (hb : ∀ κ, ‖ζ κ‖ ≤ b) (ι' : I'.Carrier) (ι : I.Carrier) :
    ∃ a₀ : ℂ, (fun σ : ℂ => T (σ • ζ) ι' ι -
        (a₀ + σ * coeffOne F I I' T ζ ι' ι +
          σ ^ 2 * ((1 / 2 : ℂ) * coeffTwo F I I' T ζ ζ ι' ι)))
      =O[𝓝 0] fun σ : ℂ => σ ^ 3 := by
  obtain ⟨l, e, h, -, hT⟩ := hM.holo_entry ι' ι
  obtain ⟨φ, β, hex, h₁, h₂⟩ :=
    hRead F I I' hF hI hI' T ρ₀ R hM ι' ι _ l e subset_rfl
  have hb0 : 0 ≤ |b| := abs_nonneg b
  have hb' : ∀ κ, ‖ζ κ‖ ≤ |b| := fun κ => (hb κ).trans (le_abs_self b)
  set v := fieldValues e ζ with hv
  have hρ₀ : 0 < ρ₀ := hM.radius_pos
  have hnear : ∀ᶠ σ : ℂ in 𝓝 0, ‖σ‖ * |b| < ρ₀ := by
    have hc : Continuous fun σ : ℂ => ‖σ‖ * |b| := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hρ₀)
  have hbelow : ∀ σ : ℂ, ‖σ‖ * |b| < ρ₀ → ∀ κ, ‖(σ • ζ) κ‖ ≤ ‖σ‖ * |b| := fun σ _ κ => by
    simpa [norm_mul] using mul_le_mul_of_nonneg_left (hb' κ) (norm_nonneg σ)
  have heq : ∀ᶠ σ : ℂ in 𝓝 0, T (σ • ζ) ι' ι = entryFun T ι' ι e (σ • v) := by
    filter_upwards [hnear] with σ hσ
    have B₁ : IsSupBelow F (σ • ζ) ρ₀ := ⟨_, hσ, hbelow σ hσ⟩
    have B₂ : IsSupBelow F (fieldExtend e (σ • v)) ρ₀ :=
      ⟨_, hσ, norm_fieldExtend_le e (mul_nonneg (norm_nonneg σ) hb0) (hbelow σ hσ)⟩
    rw [hT _ B₁, entryFun, hT _ B₂, fieldValues_fieldExtend, fieldValues_smul]
  have ht : Tendsto (fun σ : ℂ => σ • v) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun σ : ℂ => σ • v := by fun_prop
    simpa using hc.tendsto 0
  have hcomp := hex.2.comp_tendsto ht
  refine ⟨entryFun T ι' ι e 0, ?_⟩
  have hO : (fun σ : ℂ => ‖σ • v‖ ^ 3) =O[𝓝 0] fun σ : ℂ => σ ^ 3 := by
    refine IsBigO.of_bound (‖v‖ ^ 3) (Eventually.of_forall fun σ => ?_)
    simp [norm_smul, mul_pow, mul_comm]
  refine (hcomp.trans hO).congr' ?_ EventuallyEq.rfl
  filter_upwards [heq] with σ hσ
  rw [hσ, ← h₁ ζ, ← h₂ ζ ζ]
  simp only [Function.comp_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring
theorem coeffTwo_polarization (hRead : CoeffsOnSuperset.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ₀ R : ℝ}
    (hM : IsLocalWith F I I' T ρ₀ R) (ι' : I'.Carrier) (ι : I.Carrier)
    (ζ₁ ζ₂ : F.Carrier → ℂ) (c c' : ℂ) :
    coeffTwo F I I' T (ζ₁ + ζ₂) (ζ₁ + ζ₂) ι' ι -
        coeffTwo F I I' T (ζ₁ + (-1 : ℂ) • ζ₂) (ζ₁ + (-1 : ℂ) • ζ₂) ι' ι =
      4 * coeffTwo F I I' T ζ₁ ζ₂ ι' ι ∧
    coeffTwo F I I' T (c • ζ₁) (c' • ζ₂) ι' ι =
      c * c' * coeffTwo F I I' T ζ₁ ζ₂ ι' ι := by
  obtain ⟨l, e, -, -, -⟩ := hM.holo_entry ι' ι
  obtain ⟨φ, β, hex, -, h₂⟩ :=
    hRead F I I' hF hI hI' T ρ₀ R hM ι' ι _ l e subset_rfl
  constructor
  · simp only [← h₂, fieldValues_add, fieldValues_smul, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [hex.1 (fieldValues e ζ₂) (fieldValues e ζ₁)]
    ring
  · simp only [← h₂, fieldValues_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
end Entries
section Forms
variable {F I I' : PeriodicData}
def finForm (S : Finset I'.Carrier) (A : Finset I.Carrier) (d K : I'.Carrier → I.Carrier → ℂ) : ℂ :=
  ∑ ι' ∈ S, ∑ ι ∈ A, d ι' ι * K ι' ι
theorem finForm_isBigO_expansion (hRead : CoeffsOnSuperset.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ₀ R : ℝ}
    (hM : IsLocalWith F I I' T ρ₀ R) {ζ : F.Carrier → ℂ} {b : ℝ}
    (hb : ∀ κ, ‖ζ κ‖ ≤ b) (S : Finset I'.Carrier) (A : Finset I.Carrier)
    (d : I'.Carrier → I.Carrier → ℂ) :
    ∃ a₀ : ℂ, (fun σ : ℂ => finForm S A d (T (σ • ζ)) -
        (a₀ + σ * finForm S A d (coeffOne F I I' T ζ) +
          σ ^ 2 * ((1 / 2 : ℂ) * finForm S A d (coeffTwo F I I' T ζ ζ))))
      =O[𝓝 0] fun σ : ℂ => σ ^ 3 := by
  choose a ha using fun ι' ι => entry_isBigO_expansion hRead hF hI hI' hM hb ι' ι
  refine ⟨∑ ι' ∈ S, ∑ ι ∈ A, d ι' ι * a ι' ι, ?_⟩
  have hrow : ∀ ι' ∈ S, (fun σ : ℂ => ∑ ι ∈ A, d ι' ι * (T (σ • ζ) ι' ι -
      (a ι' ι + σ * coeffOne F I I' T ζ ι' ι +
        σ ^ 2 * ((1 / 2 : ℂ) * coeffTwo F I I' T ζ ζ ι' ι))))
      =O[𝓝 0] fun σ : ℂ => σ ^ 3 := fun ι' _ =>
    (IsBigO.sum fun ι _ => (ha ι' ι).const_mul_left (d ι' ι)).congr_left fun σ => by
      rw [Finset.sum_apply]
  refine (IsBigO.sum hrow).congr_left fun σ => ?_
  rw [Finset.sum_apply]
  simp only [finForm, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ι' _ => Finset.sum_congr rfl fun ι _ => ?_
  ring
theorem finForm_coeff_bounds_diag (hRead : CoeffsOnSuperset.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ₀ R : ℝ}
    (hM : IsLocalWith F I I' T ρ₀ R)
    {N : (F.Carrier → ℂ) → ℝ≥0∞} {ρ C B s : ℝ} (hρ : 0 < ρ)
    (hN : IsFieldNorm F N)
    (hT : BoundedOnBall F I I' T N ρ C)
    (S : Finset I'.Carrier) (A : Finset I.Carrier) (d : I'.Carrier → I.Carrier → ℂ)
    (hB : ∀ ξ, N ξ < ENNReal.ofReal ρ → ‖finForm S A d (T ξ)‖ ≤ B)
    {ζ : F.Carrier → ℂ} (hs : 0 < s) (hζ : N ζ < ENNReal.ofReal s) :
    ‖finForm S A d (coeffOne F I I' T ζ)‖ ≤ B * s / ρ ∧
      ‖finForm S A d (coeffTwo F I I' T ζ ζ)‖ ≤ 2 * B * s ^ 2 / ρ ^ 2 := by
  have hfin : N ζ < ∞ := hζ.trans ENNReal.ofReal_lt_top
  obtain ⟨b, hb⟩ := hN.bounded_of_lt_top ζ hfin
  set n : ℝ := (N ζ).toReal with hn
  have hNn : N ζ = ENNReal.ofReal n := (ENNReal.ofReal_toReal hfin.ne).symm
  have hn0 : 0 ≤ n := ENNReal.toReal_nonneg
  have hns : n < s := by
    rw [hNn] at hζ
    exact (ENNReal.ofReal_lt_ofReal_iff hs).1 hζ
  set r : ℝ := ρ / s with hr
  have hr0 : 0 < r := div_pos hρ hs
  have hin : ∀ σ ∈ closedBall (0 : ℂ) r, N (σ • ζ) < ENNReal.ofReal ρ := by
    intro σ hσ
    have hσr : ‖σ‖ ≤ r := by simpa using hσ
    rw [hN.smul_eq, hNn, ← ENNReal.ofReal_mul (norm_nonneg σ),
      ENNReal.ofReal_lt_ofReal_iff hρ]
    calc ‖σ‖ * n ≤ r * n := mul_le_mul_of_nonneg_right hσr hn0
      _ < r * s := mul_lt_mul_of_pos_left hns hr0
      _ = ρ := by rw [hr]; field_simp
  have hdiff : DifferentiableOn ℂ (fun σ : ℂ => finForm S A d (T (σ • ζ)))
      (closedBall 0 r) := by
    refine DifferentiableOn.fun_sum fun ι' _ => DifferentiableOn.fun_sum fun ι _ => ?_
    exact ((hT.differentiableOn_line ζ hfin ι' ι).mono hin).const_mul _
  obtain ⟨a₀, hx⟩ := finForm_isBigO_expansion hRead hF hI hI' hM hb S A d
  obtain ⟨c₁, c₂⟩ := cauchy_estimate_first_second hr0 hdiff (fun σ hσ => hB _ (hin σ hσ)) hx
  constructor
  · calc _ ≤ B / r := c₁
      _ = B * s / ρ := by rw [hr]; field_simp
  · rw [norm_mul] at c₂
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h2] at c₂
    calc _ ≤ 2 * (B / r ^ 2) := by linarith
      _ = 2 * B * s ^ 2 / ρ ^ 2 := by rw [hr]; field_simp
theorem finForm_coeffTwo_bound (hRead : CoeffsOnSuperset.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ₀ R : ℝ}
    (hM : IsLocalWith F I I' T ρ₀ R)
    {N : (F.Carrier → ℂ) → ℝ≥0∞} {ρ C B a b : ℝ} (hρ : 0 < ρ)
    (hN : IsFieldNorm F N)
    (hT : BoundedOnBall F I I' T N ρ C)
    (S : Finset I'.Carrier) (A : Finset I.Carrier) (d : I'.Carrier → I.Carrier → ℂ)
    (hB : ∀ ξ, N ξ < ENNReal.ofReal ρ → ‖finForm S A d (T ξ)‖ ≤ B)
    {ζ ζ' : F.Carrier → ℂ} (ha : 0 < a) (hb : 0 < b)
    (hζ : N ζ < ENNReal.ofReal a) (hζ' : N ζ' < ENNReal.ofReal b) :
    ‖finForm S A d (coeffTwo F I I' T ζ ζ')‖ ≤ 4 * B * a * b / ρ ^ 2 := by
  set ζ₁ : F.Carrier → ℂ := ((a : ℂ)⁻¹) • ζ with hζ₁
  set ζ₂ : F.Carrier → ℂ := ((b : ℂ)⁻¹) • ζ' with hζ₂
  have scaled : ∀ {c : ℝ} {ξ : F.Carrier → ℂ}, 0 < c → N ξ < ENNReal.ofReal c →
      N (((c : ℂ)⁻¹) • ξ) < 1 := by
    intro c ξ hc hξ
    have hfin : N ξ < ∞ := hξ.trans ENNReal.ofReal_lt_top
    have hNn : N ξ = ENNReal.ofReal (N ξ).toReal := (ENNReal.ofReal_toReal hfin.ne).symm
    have hlt : (N ξ).toReal < c := by
      rw [hNn] at hξ
      exact (ENNReal.ofReal_lt_ofReal_iff hc).1 hξ
    rw [hN.smul_eq, hNn, ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_one,
      ENNReal.ofReal_lt_ofReal_iff one_pos]
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le, inv_mul_lt_iff₀ hc]
    simpa using hlt
  have h₁ : N ζ₁ < 1 := scaled ha hζ
  have h₂ : N ζ₂ < 1 := scaled hb hζ'
  have h₂' : N ((-1 : ℂ) • ζ₂) < 1 := by
    rw [hN.smul_eq]
    simpa using h₂
  have two : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have hp : N (ζ₁ + ζ₂) < ENNReal.ofReal 2 := by
    rw [← two]
    calc _ ≤ N ζ₁ + N ζ₂ := hN.add_le _ _
      _ < 1 + 1 := ENNReal.add_lt_add h₁ h₂
      _ = 2 := one_add_one_eq_two
  have hm : N (ζ₁ + (-1 : ℂ) • ζ₂) < ENNReal.ofReal 2 := by
    rw [← two]
    calc _ ≤ N ζ₁ + N ((-1 : ℂ) • ζ₂) := hN.add_le _ _
      _ < 1 + 1 := ENNReal.add_lt_add h₁ h₂'
      _ = 2 := one_add_one_eq_two
  have bp := (finForm_coeff_bounds_diag hRead hF hI hI' hM hρ hN hT S A d hB
    (by norm_num : (0 : ℝ) < 2) hp).2
  have bm := (finForm_coeff_bounds_diag hRead hF hI hI' hM hρ hN hT S A d hB
    (by norm_num : (0 : ℝ) < 2) hm).2
  have hpol : finForm S A d (coeffTwo F I I' T (ζ₁ + ζ₂) (ζ₁ + ζ₂)) -
      finForm S A d (coeffTwo F I I' T (ζ₁ + (-1 : ℂ) • ζ₂) (ζ₁ + (-1 : ℂ) • ζ₂)) =
      4 * ((a : ℂ)⁻¹ * (b : ℂ)⁻¹) * finForm S A d (coeffTwo F I I' T ζ ζ') := by
    simp only [finForm, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ι' _ => Finset.sum_congr rfl fun ι _ => ?_
    obtain ⟨e₁, -⟩ := coeffTwo_polarization hRead hF hI hI' hM ι' ι ζ₁ ζ₂ 1 1
    obtain ⟨-, e₂⟩ := coeffTwo_polarization hRead hF hI hI' hM ι' ι ζ ζ' (a : ℂ)⁻¹ (b : ℂ)⁻¹
    rw [← mul_sub, e₁, e₂]
    ring
  have hnorm : ‖4 * ((a : ℂ)⁻¹ * (b : ℂ)⁻¹)‖ = 4 * (a⁻¹ * b⁻¹) := by
    simp [abs_of_pos ha, abs_of_pos hb]
  have hle : 4 * (a⁻¹ * b⁻¹) * ‖finForm S A d (coeffTwo F I I' T ζ ζ')‖ ≤
      2 * (2 * B * 2 ^ 2 / ρ ^ 2) := by
    rw [← hnorm, ← norm_mul, ← hpol]
    exact (norm_sub_le _ _).trans (by linarith)
  have hab : 0 < a * b := mul_pos ha hb
  have e : 4 * (a⁻¹ * b⁻¹) = 4 / (a * b) := by field_simp
  rw [e, div_mul_eq_mul_div, div_le_iff₀ hab] at hle
  have e' : 2 * (2 * B * 2 ^ 2 / ρ ^ 2) * (a * b) = 4 * (4 * B * a * b / ρ ^ 2) := by ring
  rw [e'] at hle
  linarith
end Forms
section Norms
variable {I I' : PeriodicData}
def weightedMass {J : Type} (w : J → ℝ) (S : Finset J) (f : J → ℂ) : ℝ :=
  ∑ i ∈ S, w i * ‖f i‖ ^ 2
def pairingCoeffs (a : I'.Carrier → ℂ) (b : I.Carrier → ℂ) (ι' : I'.Carrier) (ι : I.Carrier) : ℂ :=
  (I'.weightOf ι' : ℂ) * a ι' * b ι
def PairingsBounded (K : I'.Carrier → I.Carrier → ℂ) (c : ℝ) : Prop :=
  ∀ (S : Finset I'.Carrier) (A : Finset I.Carrier) (a : I'.Carrier → ℂ) (b : I.Carrier → ℂ),
    weightedMass I.weightOf A b ≤ 1 →
      ‖finForm S A (pairingCoeffs a b) K‖ ≤ c * Real.sqrt (weightedMass I'.weightOf S a)
theorem finForm_pairingCoeffs (S : Finset I'.Carrier) (A : Finset I.Carrier) (a : I'.Carrier → ℂ)
    (b : I.Carrier → ℂ) (K : I'.Carrier → I.Carrier → ℂ) :
    finForm S A (pairingCoeffs a b) K =
      ∑ ι' ∈ S, (I'.weightOf ι' : ℂ) * a ι' * ∑ ι ∈ A, K ι' ι * b ι := by
  simp only [finForm, pairingCoeffs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ι' _ => Finset.sum_congr rfl fun ι _ => ?_
  ring
theorem weighted_cauchy_schwarz {J : Type} {w : J → ℝ} (hw : ∀ i, 0 ≤ w i) (S : Finset J)
    (a g : J → ℂ) :
    ‖∑ i ∈ S, (w i : ℂ) * a i * g i‖ ≤
      Real.sqrt (weightedMass w S a) * Real.sqrt (weightedMass w S g) := by
  have hf : ∀ i, 0 ≤ w i * ‖a i‖ ^ 2 := fun i => mul_nonneg (hw i) (by positivity)
  have hg : ∀ i, 0 ≤ w i * ‖g i‖ ^ 2 := fun i => mul_nonneg (hw i) (by positivity)
  refine (norm_sum_le _ _).trans (le_trans (le_of_eq ?_) (Real.sum_sqrt_mul_sqrt_le S hf hg))
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.sqrt_mul (hw i), Real.sqrt_mul (hw i), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw i)]
  have := Real.mul_self_sqrt (hw i)
  calc w i * ‖a i‖ * ‖g i‖ = (Real.sqrt (w i) * Real.sqrt (w i)) * ‖a i‖ * ‖g i‖ := by rw [this]
    _ = _ := by ring
theorem weightedMass_le_wNorm_sq {J : Type} {w : J → ℝ} (hw : ∀ i, 0 ≤ w i) {f : J → ℂ}
    (hf : NormSummable w f) (S : Finset J) : weightedMass w S f ≤ wNorm w f ^ 2 := by
  have hnn : ∀ i, 0 ≤ w i * ‖f i‖ ^ 2 := fun i => mul_nonneg (hw i) (by positivity)
  have hs : Summable fun i => w i * ‖f i‖ ^ 2 :=
    (show (fun i => |w i * ‖f i‖ ^ 2|) = fun i => w i * ‖f i‖ ^ 2 from
      funext fun i => abs_of_nonneg (hnn i)) ▸ hf
  rw [wNorm, Real.sq_sqrt (tsum_nonneg hnn)]
  exact hs.sum_le_tsum S fun i _ => hnn i
theorem pairingsBounded_of_opNormLE (hw' : ∀ ι', 0 ≤ I'.weightOf ι')
    {K : I'.Carrier → I.Carrier → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : OpNormLE I I' K c) : PairingsBounded K c := by
  classical
  intro S A a b hb
  set χ : I.Carrier → ℂ := fun ι => if ι ∈ A then b ι else 0 with hχ
  have hoff : ∀ ι, ι ∉ A → χ ι = 0 := fun ι hι => by simp [hχ, hι]
  have hon : ∀ ι, ι ∈ A → χ ι = b ι := fun ι hι => by simp [hχ, hι]
  have hform : NormSummable I.weightOf χ :=
    summable_of_ne_finset_zero (s := A) fun ι hι => by simp [hoff ι hι]
  have hsum : ∑' ι, I.weightOf ι * ‖χ ι‖ ^ 2 = weightedMass I.weightOf A b := by
    rw [tsum_eq_sum (s := A) fun ι hι => by simp [hoff ι hι]]
    exact Finset.sum_congr rfl fun ι hι => by rw [hon ι hι]
  have hball : χ ∈ wUnitBall I.weightOf (finiteNormSpace I) :=
    ⟨hform, hform, by
      rw [wNorm, hsum]
      exact Real.sqrt_le_one.2 hb⟩
  have hKχ : NormSummable I'.weightOf (applyKernel K χ) := h.2.1 χ hball
  have hnorm : wNorm I'.weightOf (applyKernel K χ) ≤ c := by
    have h₁ : ENNReal.ofReal (wNorm I'.weightOf (applyKernel K χ)) ≤
        wOpNorm I.weightOf I'.weightOf (finiteNormSpace I) (applyKernel K) :=
      le_iSup₂ (f := fun f (_ : f ∈ wUnitBall I.weightOf (finiteNormSpace I)) =>
        ENNReal.ofReal (wNorm I'.weightOf (applyKernel K f))) χ hball
    exact (ENNReal.ofReal_le_ofReal_iff hc).1 (h₁.trans h.2.2)
  have hmass : Real.sqrt (weightedMass I'.weightOf S (applyKernel K χ)) ≤ c := by
    refine Real.sqrt_le_iff.2 ⟨hc, (weightedMass_le_wNorm_sq hw' hKχ S).trans ?_⟩
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hnorm 2
  have hact : ∀ ι', ∑ ι ∈ A, K ι' ι * b ι = applyKernel K χ ι' := fun ι' => by
    rw [applyKernel, tsum_eq_sum (s := A) fun ι hι => by simp [hoff ι hι]]
    exact Finset.sum_congr rfl fun ι hι => by rw [hon ι hι]
  rw [finForm_pairingCoeffs]
  simp only [hact]
  refine (weighted_cauchy_schwarz hw' S a _).trans ?_
  rw [mul_comm c]
  exact mul_le_mul_of_nonneg_left hmass (Real.sqrt_nonneg _)
theorem weightedMass_applyKernel_le (hw : ∀ ι, 0 ≤ I.weightOf ι) (hw' : ∀ ι', 0 ≤ I'.weightOf ι')
    {K : I'.Carrier → I.Carrier → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hrow : ∀ ι', {ι | K ι' ι ≠ 0}.Finite) (h : PairingsBounded K c) {f : I.Carrier → ℂ} {t : ℝ}
    (ht : 0 < t) (hf : NormSummable I.weightOf f) (hft : wNorm I.weightOf f ≤ t)
    (S : Finset I'.Carrier) : weightedMass I'.weightOf S (applyKernel K f) ≤ (c * t) ^ 2 := by
  classical
  set g := applyKernel K f with hg
  set A : Finset I.Carrier := S.biUnion fun ι' => (hrow ι').toFinset with hA
  set a : I'.Carrier → ℂ := fun ι' => (starRingEnd ℂ) (g ι') with ha
  set b : I.Carrier → ℂ := fun ι => (t : ℂ)⁻¹ * f ι with hb
  set X := weightedMass I'.weightOf S g with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ => mul_nonneg (hw' i) (by positivity)
  have hbn : ∀ ι, ‖b ι‖ ^ 2 = (t ^ 2)⁻¹ * ‖f ι‖ ^ 2 := fun ι => by
    simp only [hb, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht.le]
    field_simp
  have hmb : weightedMass I.weightOf A b ≤ 1 := by
    have h₁ : weightedMass I.weightOf A b = (t ^ 2)⁻¹ * weightedMass I.weightOf A f := by
      simp only [weightedMass, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ι _ => ?_
      rw [hbn]
      ring
    have h₂ : weightedMass I.weightOf A f ≤ t ^ 2 :=
      (weightedMass_le_wNorm_sq hw hf A).trans (pow_le_pow_left₀ (Real.sqrt_nonneg _) hft 2)
    rw [h₁, inv_mul_le_iff₀ (by positivity)]
    simpa using h₂
  have hact : ∀ ι' ∈ S, ∑ ι ∈ A, K ι' ι * b ι = (t : ℂ)⁻¹ * g ι' := fun ι' hι' => by
    have hz : ∀ ι, ι ∉ A → K ι' ι * f ι = 0 := fun ι hι => by
      have : K ι' ι = 0 := by
        by_contra hne
        exact hι (Finset.mem_biUnion.2 ⟨ι', hι', (hrow ι').mem_toFinset.2 hne⟩)
      simp [this]
    rw [hg, applyKernel, tsum_eq_sum (s := A) fun ι hι => hz ι hι, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ι _ => ?_
    simp only [hb]
    ring
  have hform : finForm S A (pairingCoeffs a b) K = (t : ℂ)⁻¹ * (X : ℂ) := by
    rw [finForm_pairingCoeffs, hX, weightedMass, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ι' hι' => ?_
    rw [hact ι' hι']
    simp only [ha]
    have : (starRingEnd ℂ) (g ι') * g ι' = ((‖g ι'‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']
      simp
    push_cast at this ⊢
    linear_combination ((I'.weightOf ι' : ℂ) * (t : ℂ)⁻¹) * this
  have hma : weightedMass I'.weightOf S a = X := by
    simp only [hX, weightedMass, ha, RCLike.norm_conj]
  have hb₀ := h S A a b hmb
  rw [hform, hma, norm_mul, norm_inv, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg ht.le, Real.norm_of_nonneg hX0, inv_mul_le_iff₀ ht] at hb₀
  set y := Real.sqrt X with hy
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hyy : y ^ 2 = X := Real.sq_sqrt hX0
  rw [← hyy] at hb₀ ⊢
  have hct : 0 ≤ c * t := mul_nonneg hc ht.le
  have hyc : y ≤ c * t := by
    rcases hy0.eq_or_lt with h0 | h0
    · exact h0.symm.le.trans hct
    · have e : y * y ≤ (c * t) * y := by nlinarith
      exact le_of_mul_le_mul_right e h0
  exact pow_le_pow_left₀ hy0 hyc 2
theorem opNormLE_of_pairingsBounded (hw : ∀ ι, 0 ≤ I.weightOf ι)
    (hw' : ∀ ι', 0 ≤ I'.weightOf ι') {K : I'.Carrier → I.Carrier → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hrow : ∀ ι', {ι | K ι' ι ≠ 0}.Finite) (h : PairingsBounded K c) : OpNormLE I I' K c := by
  have hnn : ∀ (g : I'.Carrier → ℂ) i, 0 ≤ I'.weightOf i * ‖g i‖ ^ 2 := fun g i =>
    mul_nonneg (hw' i) (by positivity)
  have hsummable : ∀ {f : I.Carrier → ℂ} {t : ℝ}, 0 < t → NormSummable I.weightOf f →
      wNorm I.weightOf f ≤ t →
      Summable fun i => I'.weightOf i * ‖applyKernel K f i‖ ^ 2 := fun ht hf hft =>
    summable_of_sum_le (hnn _) (weightedMass_applyKernel_le hw hw' hc hrow h ht hf hft)
  have hformed : ∀ {f : I.Carrier → ℂ} {t : ℝ}, 0 < t → NormSummable I.weightOf f →
      wNorm I.weightOf f ≤ t → NormSummable I'.weightOf (applyKernel K f) :=
    fun ht hf hft => (hsummable ht hf hft).abs
  have hacts : MapsFiniteNorm I I' K := fun f hf => by
    refine ⟨fun ι' => ?_, ?_⟩
    · refine summable_of_ne_finset_zero (s := (hrow ι').toFinset) fun ι hι => ?_
      have h0 : K ι' ι = 0 := by
        by_contra hne
        exact hι ((hrow ι').mem_toFinset.2 hne)
      simp [h0]
    · exact hformed (t := wNorm I.weightOf f + 1)
        (lt_of_le_of_lt (Real.sqrt_nonneg _) (lt_add_one _)) hf (le_add_of_nonneg_right zero_le_one)
  refine ⟨hacts, fun f hf => (hacts f hf.1).2, ?_⟩
  refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
  have hf₁ := hf.2.1
  have hf₂ := hf.2.2
  have hle : ∑' i, I'.weightOf i * ‖applyKernel K f i‖ ^ 2 ≤ (c * 1) ^ 2 :=
    (hsummable one_pos hf₁ hf₂).tsum_le_of_sum_le
      (weightedMass_applyKernel_le hw hw' hc hrow h one_pos hf₁ hf₂)
  rw [wNorm]
  refine Real.sqrt_le_iff.2 ⟨hc, ?_⟩
  simpa using hle
theorem le_apply_zero_of_forall_pos {x : ℝ} {g : ℝ → ℝ} (hg : Continuous g)
    (h : ∀ ε, 0 < ε → x ≤ g ε) : x ≤ g 0 :=
  ge_of_tendsto (hg.continuousWithinAt : Tendsto g (𝓝[>] 0) (𝓝 (g 0)))
    (eventually_mem_nhdsWithin.mono fun ε hε => h ε hε)
end Norms
theorem coeffBounds_of_claims (hFin : CovariantFiniteRange.Claim)
    (hLoc : LocalOpFunTaylor.Claim)
    (hRead : CoeffsOnSuperset.Claim) : CoeffBounds := by
  intro F I I' hF hI hI' T hLocal N ρ C hρ hC hN hT ζ ζ' hζ hζ'
  obtain ⟨ρ₀, R, hM⟩ := hLocal
  have hw : ∀ ι, 0 ≤ I.weightOf ι := fun ι => (hI.weight_pos _).le
  have hw' : ∀ ι', 0 ≤ I'.weightOf ι' := fun ι' => (hI'.weight_pos _).le
  have hfin : ∀ ι' : I'.Carrier, (nearIndices I (I'.pos ι') R).Finite :=
    fun ι' => (hFin.1 I hI).1 _ _
  have standingConstraints : ∀ (Y : I'.Carrier → I.Carrier → ℂ),
      (∀ ι' ι, ¬ TorusMetric.euclidNormVec (I.pos ι - I'.pos ι') ≤ R → Y ι' ι = 0) →
      ∀ ι', {ι | Y ι' ι ≠ 0}.Finite := fun Y hY ι' =>
    (hfin ι').subset fun ι hι => by
      by_contra hn
      exact hι (hY ι' ι hn)
  have van := fun ι' ι => (hLoc F I I' hF hI hI' T ρ₀ R hM ζ ζ' ι' ι 0).2.1.2
  have hn0 : ∀ {ξ : F.Carrier → ℂ}, N ξ < ∞ → ∀ {ε : ℝ}, 0 < ε →
      N ξ < ENNReal.ofReal ((N ξ).toReal + ε) := fun {ξ} hξ {ε} hε => by
    conv_lhs => rw [← ENNReal.ofReal_toReal hξ.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  set n : ℝ := (N ζ).toReal with hn
  set n' : ℝ := (N ζ').toReal with hn'
  have forms : ∀ (S : Finset I'.Carrier) (A : Finset I.Carrier) (a : I'.Carrier → ℂ)
      (b : I.Carrier → ℂ), weightedMass I.weightOf A b ≤ 1 → ∀ ξ, N ξ < ENNReal.ofReal ρ →
      ‖finForm S A (pairingCoeffs a b) (T ξ)‖ ≤ C * Real.sqrt (weightedMass I'.weightOf S a) :=
    fun S A a b hb ξ hξ =>
      pairingsBounded_of_opNormLE hw' hC (hT.opNorm_le ξ hξ) S A a b hb
  constructor
  · refine opNormLE_of_pairingsBounded hw hw' (by positivity)
      (standingConstraints _ fun ι' ι hn => (van ι' ι hn).2.1) ?_
    intro S A a b hb
    have hε := fun ε (hε : 0 < ε) => (finForm_coeff_bounds_diag hRead hF hI hI' hM hρ hN hT S A
      (pairingCoeffs a b) (forms S A a b hb) (s := n + ε) (by positivity) (hn0 hζ hε)).1
    have := le_apply_zero_of_forall_pos
      (g := fun ε => C * Real.sqrt (weightedMass I'.weightOf S a) * (n + ε) / ρ)
      (by fun_prop) hε
    calc _ ≤ _ := this
      _ = _ := by
        simp only [add_zero]
        field_simp
  · refine opNormLE_of_pairingsBounded hw hw' (by positivity)
      (standingConstraints _ fun ι' ι hn => (van ι' ι hn).2.2) ?_
    intro S A a b hb
    have hε := fun ε (hε : 0 < ε) => finForm_coeffTwo_bound hRead hF hI hI' hM hρ hN hT S A
      (pairingCoeffs a b) (forms S A a b hb) (a := n + ε) (b := n' + ε) (by positivity)
      (by positivity) (hn0 hζ hε) (hn0 hζ' hε)
    have := le_apply_zero_of_forall_pos
      (g := fun ε => 4 * (C * Real.sqrt (weightedMass I'.weightOf S a)) * (n + ε) * (n' + ε) / ρ ^ 2)
      (by fun_prop) hε
    calc _ ≤ _ := this
      _ = _ := by
        simp only [add_zero]
        field_simp
end YangMills.Construction.PeriodicOperators.CauchyTaylorBounds
end
