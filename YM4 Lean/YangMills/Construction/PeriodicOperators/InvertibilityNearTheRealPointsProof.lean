import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctions
import YangMills.Construction.PeriodicOperators.InvertibilityNearTheRealPoints
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHomProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.InvertibilityNearReal
open StripSymbols (openStripInterior)
open EntriesDets
section Embedding
variable {J : Type} [Fintype J]
def sqrtWeightEmbed (w : J → ℝ) : (J → ℂ) →ₗ[ℂ] EuclideanSpace ℂ J where
  toFun g := WithLp.toLp 2 fun c => (Real.sqrt (w c) : ℂ) * g c
  map_add' g g' := by
    ext c
    simp [mul_add]
  map_smul' z g := by
    ext c
    simp [mul_left_comm]
omit [Fintype J] in
theorem sqrtWeightEmbed_apply (w : J → ℝ) (g : J → ℂ) (c : J) :
    sqrtWeightEmbed w g c = (Real.sqrt (w c) : ℂ) * g c := rfl
theorem wNorm_eq_norm_sqrtWeightEmbed {w : J → ℝ} (hw : ∀ c, 0 < w c) (g : J → ℂ) :
    wNorm w g = ‖sqrtWeightEmbed w g‖ := by
  rw [EuclideanSpace.norm_eq, wNorm, tsum_fintype]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sqrtWeightEmbed_apply, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (hw c).le]
theorem wInner_eq_inner_sqrtWeightEmbed {w : J → ℝ} (hw : ∀ c, 0 < w c) (g h : J → ℂ) :
    wInner w g h = inner ℂ (sqrtWeightEmbed w g) (sqrtWeightEmbed w h) := by
  rw [wInner, wPairing, tsum_fintype, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hsq : (Real.sqrt (w c) : ℂ) * (Real.sqrt (w c) : ℂ) = (w c : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hw c).le]
  rw [sqrtWeightEmbed_apply, sqrtWeightEmbed_apply, RCLike.inner_apply, map_mul,
    Complex.conj_ofReal, ← hsq]
  ring
omit [Fintype J] in
theorem eq_zero_of_sqrtWeightEmbed_eq_zero {w : J → ℝ} (hw : ∀ c, 0 < w c) {g : J → ℂ}
    (h : sqrtWeightEmbed w g = 0) : g = 0 := by
  funext c
  have hc := congrArg (fun x : EuclideanSpace ℂ J => x c) h
  simp only [sqrtWeightEmbed_apply] at hc
  have hs : (Real.sqrt (w c) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hw c)).ne'
  exact (mul_eq_zero.1 hc).resolve_left hs
open Classical in
theorem linearMap_apply_eq_sum_entry {J' : Type} (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (f : J → ℂ)
    (c' : J') : M f c' = ∑ c, f c * linearMapEntry M c' c := by
  have hf : f = ∑ c, f c • (Pi.single c 1 : J → ℂ) := by
    funext c
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hf]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, linearMapEntry]
end Embedding
section Quotients
variable {I : PeriodicData}
theorem quotWeight_one_pos (hj : Quotients.QuotientTransposeNorm) (hI : IsPeriodic I)
    (c : I.UnitQuot) : 0 < I.quotWeight 1 c := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.quotWeight_pos <;> assumption
variable [Fintype I.UnitQuot]
theorem mul_norm_le_of_loewnerLE (hw : ∀ c, 0 < I.quotWeight 1 c) {M : QuotHom I I} {ς : ℝ}
    (h : LoewnerLE (scalarQuotHom I ς) M) (f : I.UnitQuot → ℂ) :
    ς * ‖sqrtWeightEmbed (I.quotWeight 1) f‖ ≤ ‖sqrtWeightEmbed (I.quotWeight 1) (M f)‖ := by
  set T := sqrtWeightEmbed (I.quotWeight 1) with hT
  have h0 := h.re_nonneg f
  rw [wInner_eq_inner_sqrtWeightEmbed hw, ← hT] at h0
  have hd : (M - scalarQuotHom I ς) f = M f - (ς : ℂ) • f := by
    simp [scalarQuotHom]
  have hs : inner ℂ (T f) (T f) = ((‖T f‖ ^ 2 : ℝ) : ℂ) := by
    simp
  rw [hd, map_sub, map_smul, inner_sub_right, inner_smul_right, hs, ← Complex.ofReal_mul,
    Complex.sub_re, Complex.ofReal_re] at h0
  have h2 : (inner ℂ (T f) (T (M f))).re ≤ ‖T f‖ * ‖T (M f)‖ :=
    re_inner_le_norm (𝕜 := ℂ) (T f) (T (M f))
  rcases eq_or_lt_of_le (norm_nonneg (T f)) with hz | hp
  · rw [← hz]
    simp
  · have h3 : ‖T f‖ * (ς * ‖T f‖) ≤ ‖T f‖ * ‖T (M f)‖ := by nlinarith
    exact le_of_mul_le_mul_left h3 hp
theorem isInvertible_of_lower_bound (hw : ∀ c, 0 < I.quotWeight 1 c) {M : QuotHom I I} {r : ℝ}
    (hr : 0 < r)
    (h : ∀ f, r * ‖sqrtWeightEmbed (I.quotWeight 1) f‖ ≤
      ‖sqrtWeightEmbed (I.quotWeight 1) (M f)‖) :
    IsInvertibleQuotHom M ∧ quotHomNorm (quotHomInverse M) ≤ ENNReal.ofReal (1 / r) := by
  have hinj : Function.Injective M := by
    refine (injective_iff_map_eq_zero M).2 fun f hf => ?_
    have h1 := h f
    rw [hf, map_zero, norm_zero] at h1
    have h2 : ‖sqrtWeightEmbed (I.quotWeight 1) f‖ ≤ 0 := by
      by_contra hc
      have := mul_pos hr (not_le.1 hc)
      linarith
    exact eq_zero_of_sqrtWeightEmbed_eq_zero hw (norm_le_zero_iff.1 h2)
  have hsurj : Function.Surjective M := LinearMap.injective_iff_surjective.1 hinj
  have hinv : IsInvertibleQuotHom M := fun g => by
    obtain ⟨f, hf⟩ := hsurj g
    exact ⟨f, hf, fun f' hf' => hinj (hf'.trans hf.symm)⟩
  refine ⟨hinv, ?_⟩
  refine iSup₂_le fun g hg => ENNReal.ofReal_le_ofReal ?_
  have hg1 : wNorm (I.quotWeight 1) g ≤ 1 := hg.2.2
  have h1 := h (quotHomInverse M g)
  rw [hinv.apply_quotHomInverse g, ← wNorm_eq_norm_sqrtWeightEmbed hw,
    ← wNorm_eq_norm_sqrtWeightEmbed hw] at h1
  rw [le_div_iff₀ hr]
  linarith
theorem holomorphicFnOn_apply_apply {O : Set (Coordinates.ComplexCoordinates 4)}
    (hp : PolynomialHolomorphic 4 O) {F : (Fin 4 → ℂ) → QuotHom I I}
    (hF : QuotHomFamilyHolomorphicOn (n := 4) O F) (f : I.UnitQuot → ℂ) (c : I.UnitQuot) :
    HolomorphicFnOn O fun z => F z f c := by
  let e := Fintype.equivFin I.UnitQuot
  have hu : ∀ i, HolomorphicFnOn O
      fun z => f (e.symm i) * linearMapEntry (F z) c (e.symm i) :=
    fun i => hp.2.2.2 _ _ (hF.2.2 (c, e.symm i))
  have hs := (hp.2.2.1 _ _ hu).1
  have hfun : (fun z => F z f c) =
      fun z => ∑ i, f (e.symm i) * linearMapEntry (F z) c (e.symm i) := by
    funext z
    rw [linearMap_apply_eq_sum_entry, ← Equiv.sum_comp e.symm]
  rw [hfun]
  exact hs
theorem norm_sub_le_of_cauchy_segment {O : Set (Coordinates.ComplexCoordinates 4)}
    (hp : PolynomialHolomorphic 4 O)
    (hc : CauchyEstimate O (normSeminorm ℂ (EuclideanSpace ℂ I.UnitQuot)))
    {F : (Fin 4 → ℂ) → QuotHom I I} (hF : QuotHomFamilyHolomorphicOn (n := 4) O F)
    (f : I.UnitQuot → ℂ) {ρ : Fin 4 → ℝ} (hρ : ∀ j, 0 < ρ j) {c : ℝ} (hc0 : 0 ≤ c)
    {a a' : Coordinates.ComplexCoordinates 4}
    (hs : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → openPolydisc ρ (a + (s : ℂ) • (a' - a)) ⊆ O ∧
      ∀ z ∈ openPolydisc ρ (a + (s : ℂ) • (a' - a)),
        ‖sqrtWeightEmbed (I.quotWeight 1) (F z f)‖ ≤ c) :
    ‖sqrtWeightEmbed (I.quotWeight 1) (F a' f) - sqrtWeightEmbed (I.quotWeight 1) (F a f)‖ ≤
      c * ∑ j, ‖a' j - a j‖ / ρ j := by
  classical
  set T := sqrtWeightEmbed (I.quotWeight 1) with hT
  let e := Fintype.equivFin I.UnitQuot
  let v : Fin (Fintype.card I.UnitQuot) → EuclideanSpace ℂ I.UnitQuot :=
    fun i => T (Pi.single (e.symm i) 1)
  let u : Fin (Fintype.card I.UnitQuot) → Coordinates.ComplexCoordinates 4 → ℂ :=
    fun i z => F z f (e.symm i)
  have hcomb : ∀ z, linComb u v z = T (F z f) := by
    intro z
    have hf : F z f = ∑ c, (F z f) c • (Pi.single c 1 : I.UnitQuot → ℂ) := by
      funext c
      simp [Finset.sum_apply, Pi.single_apply]
    simp only [linComb, u, v]
    rw [Equiv.sum_comp e.symm (fun c => (F z f) c • T (Pi.single c 1))]
    conv_rhs => rw [hf]
    simp only [map_sum, map_smul]
  have hu : ∀ i, HolomorphicFnOn O (u i) := fun i => holomorphicFnOn_apply_apply hp hF f _
  have key := (hc _ v u hu ρ c hρ hc0).2 a a' fun s hs' =>
    ⟨(hs s hs').1, fun z hz => by
      rw [coe_normSeminorm, hcomb]
      exact (hs s hs').2 z hz⟩
  rw [coe_normSeminorm, hcomb, hcomb] at key
  exact key
end Quotients
theorem invertibleNearRealAxis_holds (hq : StripSymbols.Claim) (hn : HomNorm.Claim)
    (hj : Quotients.QuotientTransposeNorm) (hh : EntriesDets.Claim) :
    InvertibleNearRealAxis := by
  intro I hI υ B ς δ F hυ hB hς hδ hδυ hsmall hF hbound hreal κ hκ
  have : Finite I.UnitQuot := hI.finite_quot
  have : Fintype I.UnitQuot := Fintype.ofFinite _
  have hw : ∀ c, 0 < I.quotWeight 1 c := quotWeight_one_pos hj hI
  have hO : IsOpen (openStripInterior υ) := hF.2.1
  have G := hh.2.2.2.2.2.2.1 4 (openStripInterior υ) (by norm_num) hO
  have hp := G.2.2.2.2.2.1
  have hc := (G.2.2.2.2.2.2.2.2.1 (EuclideanSpace ℂ I.UnitQuot) (normSeminorm ℂ _)).2
  have hOeq : openStripInterior υ = openImStrip υ := (hq.1 υ hυ).1
  have hnorm := ((hn I I hI hI).2.2.2.2.2.2.1 I hI).1
  have hlow : ∀ f, ς / 2 * ‖sqrtWeightEmbed (I.quotWeight 1) f‖ ≤
      ‖sqrtWeightEmbed (I.quotWeight 1) (F κ f)‖ := by
    intro f
    set T := sqrtWeightEmbed (I.quotWeight 1) with hT
    let a : Fin 4 → ℂ := fun μ => ((κ μ).re : ℂ)
    have ha : a ∈ realDualPoints := fun j => Complex.ofReal_im _
    have hl := mul_norm_le_of_loewnerLE hw (hreal a ha) f
    rw [← hT] at hl
    have hmove := norm_sub_le_of_cauchy_segment hp hc hF f (ρ := fun _ => υ / 2)
      (fun _ => by positivity) (c := B * ‖T f‖) (by positivity) (a := a) (a' := κ) (by
        intro s hs
        have key : ∀ z ∈ openPolydisc (fun _ => υ / 2) (a + (s : ℂ) • (κ - a)),
            z ∈ openStripInterior υ := by
          intro z hz
          rw [hOeq]
          intro μ
          have h1 : ‖z μ - (a + (s : ℂ) • (κ - a)) μ‖ < υ / 2 := hz μ
          have him : ((a + (s : ℂ) • (κ - a)) μ).im = s * (κ μ).im := by
            simp [a]
          have h2 : |(z μ - (a + (s : ℂ) • (κ - a)) μ).im| ≤ ‖z μ - (a + (s : ℂ) • (κ - a)) μ‖ :=
            Complex.abs_im_le_norm _
          have h3 : |(z μ).im| ≤ |(z μ - (a + (s : ℂ) • (κ - a)) μ).im| +
              |((a + (s : ℂ) • (κ - a)) μ).im| := by
            have := abs_add_le (z μ - (a + (s : ℂ) • (κ - a)) μ).im ((a + (s : ℂ) • (κ - a)) μ).im
            simpa using this
          have h4 : |s * (κ μ).im| ≤ δ := by
            rw [abs_mul, abs_of_nonneg hs.1]
            have := hκ μ
            nlinarith [abs_nonneg (κ μ).im, hs.1, hs.2]
          rw [him] at h3
          linarith
        refine ⟨key, fun z hz => ?_⟩
        rw [hT, ← wNorm_eq_norm_sqrtWeightEmbed hw, ← wNorm_eq_norm_sqrtWeightEmbed hw]
        refine (hnorm (F z) f).trans (mul_le_mul_of_nonneg_right
          (ENNReal.toReal_le_of_le_ofReal hB (hbound z (key z hz))) ?_)
        rw [wNorm_eq_norm_sqrtWeightEmbed hw]
        exact norm_nonneg _)
    rw [← hT] at hmove
    have hsum : ∑ j, ‖κ j - a j‖ / (υ / 2) ≤ 8 * δ / υ := by
      have h1 : ∀ j, ‖κ j - a j‖ / (υ / 2) ≤ δ / (υ / 2) := by
        intro j
        have hj' : κ j - a j = (((κ j).im : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp [a]
        have h2 : ‖κ j - a j‖ ≤ δ := by
          rw [hj', norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
          exact hκ j
        gcongr
      calc ∑ j, ‖κ j - a j‖ / (υ / 2) ≤ ∑ _j : Fin 4, δ / (υ / 2) :=
            Finset.sum_le_sum fun j _ => h1 j
        _ = 8 * δ / υ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          field_simp
          ring
    have hT0 := norm_nonneg (T f)
    have hm2 : ‖T (F κ f) - T (F a f)‖ ≤ ς / 2 * ‖T f‖ := by
      refine hmove.trans ?_
      calc B * ‖T f‖ * ∑ j, ‖κ j - a j‖ / (υ / 2) ≤ B * ‖T f‖ * (8 * δ / υ) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 8 * B * δ / υ * ‖T f‖ := by ring
        _ ≤ ς / 2 * ‖T f‖ := mul_le_mul_of_nonneg_right hsmall hT0
    have h5 : ‖T (F a f)‖ ≤ ‖T (F κ f)‖ + ‖T (F κ f) - T (F a f)‖ := by
      have h6 := norm_le_norm_add_norm_sub' (T (F a f)) (T (F κ f))
      rwa [norm_sub_rev] at h6
    linarith
  have h := isInvertible_of_lower_bound hw (r := ς / 2) (by positivity) hlow
  refine ⟨h.1, ?_⟩
  have htwo : 1 / (ς / 2) = 2 / ς := by
    field_simp
  rw [← htwo]
  exact h.2
end YangMills.Construction.PeriodicOperators.InvertibilityNearReal
end
