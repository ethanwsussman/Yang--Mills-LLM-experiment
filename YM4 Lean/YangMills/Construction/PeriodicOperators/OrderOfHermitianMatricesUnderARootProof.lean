import YangMills.Construction.PeriodicOperators.OrderOfHermitianMatricesUnderARoot
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
namespace RootConjugationOrder
open Quotients (WeightFactorsThroughQuot)
section InnerProduct
variable {P : Type} [Fintype P] (w : P → ℝ)
theorem wInner_eq_sum (v u : P → ℂ) :
    wInner w v u = ∑ i, (w i : ℂ) * (starRingEnd ℂ (v i) * u i) := by
  unfold wInner wPairing
  exact tsum_fintype _
theorem wInner_add_right (f g g' : P → ℂ) :
    wInner w f (g + g') = wInner w f g + wInner w f g' := by
  simp only [wInner_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]
theorem wInner_smul_right (a : ℂ) (f g : P → ℂ) :
    wInner w f (a • g) = a * wInner w f g := by
  simp only [wInner_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
theorem conj_wInner (f g : P → ℂ) :
    starRingEnd ℂ (wInner w f g) = wInner w g f := by
  simp only [wInner_eq_sum, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun i _ => by ring
theorem wInner_add_left (f f' g : P → ℂ) :
    wInner w (f + f') g = wInner w f g + wInner w f' g := by
  rw [← conj_wInner, wInner_add_right, map_add, conj_wInner, conj_wInner]
theorem wInner_ofReal_smul_left (a : ℝ) (f g : P → ℂ) :
    wInner w ((a : ℂ) • f) g = (a : ℂ) * wInner w f g := by
  rw [← conj_wInner, wInner_smul_right, map_mul, conj_wInner, Complex.conj_ofReal]
theorem wInner_self_eq (f : P → ℂ) :
    wInner w f f = ((∑ i, w i * ‖f i‖ ^ 2 : ℝ) : ℂ) := by
  rw [wInner_eq_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul']
  push_cast
  rfl
end InnerProduct
section QuadraticForms
variable {I I' : PeriodicData}
def quadForm (M : QuotHom I I) (f : I.UnitQuot → ℂ) : ℝ :=
  (wInner (I.quotWeight 1) f (M f)).re
def wNormSq (f : I.UnitQuot → ℂ) : ℝ :=
  (wInner (I.quotWeight 1) f f).re
variable [Fintype I.UnitQuot] [Fintype I'.UnitQuot]
theorem isSelfAdjoint_add {M M' : QuotHom I I} (h : IsSelfAdjointQuotHom M)
    (h' : IsSelfAdjointQuotHom M') : IsSelfAdjointQuotHom (M + M') := fun f g => by
  rw [LinearMap.add_apply, LinearMap.add_apply, wInner_add_left, wInner_add_right, h f g, h' f g]
theorem isSelfAdjoint_ofReal_smul (r : ℝ) {M : QuotHom I I} (h : IsSelfAdjointQuotHom M) :
    IsSelfAdjointQuotHom ((r : ℂ) • M) := fun f g => by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, wInner_ofReal_smul_left, wInner_smul_right,
    h f g]
theorem isSelfAdjoint_scalar (I : PeriodicData) [Fintype I.UnitQuot] (r : ℝ) :
    IsSelfAdjointQuotHom (scalarQuotHom I r) :=
  isSelfAdjoint_ofReal_smul r fun _ _ => rfl
omit [Fintype I.UnitQuot] [Fintype I'.UnitQuot] in
theorem isSelfAdjoint_conj {N M : QuotHom I I} (hN : IsSelfAdjointQuotHom N)
    (hM : IsSelfAdjointQuotHom M) : IsSelfAdjointQuotHom (N.comp (M.comp N)) := fun f g => by
  simp only [LinearMap.comp_apply]
  rw [hN (M (N f)) g, hM (N f) (N g), hN f (M (N g))]
theorem wInner_adjoint_left {A : QuotHom I I'} {At : QuotHom I' I} (hA : IsAdjointQuotHom A At)
    (f : I.UnitQuot → ℂ) (g : I'.UnitQuot → ℂ) :
    wInner (I'.quotWeight 1) (A f) g = wInner (I.quotWeight 1) f (At g) := by
  rw [← conj_wInner, hA f g, conj_wInner]
theorem isSelfAdjoint_adjoint_conj {A : QuotHom I I'} {At : QuotHom I' I}
    (hA : IsAdjointQuotHom A At) {T : QuotHom I I} (hT : IsSelfAdjointQuotHom T) :
    IsSelfAdjointQuotHom (A.comp (T.comp At)) := fun f g => by
  simp only [LinearMap.comp_apply]
  rw [wInner_adjoint_left hA, hT (At f) (At g), ← hA (T (At g)) f]
theorem im_wInner_self_apply {M : QuotHom I I} (h : IsSelfAdjointQuotHom M)
    (f : I.UnitQuot → ℂ) : (wInner (I.quotWeight 1) f (M f)).im = 0 := by
  refine Complex.conj_eq_iff_im.1 ?_
  rw [conj_wInner, h f f]
theorem quadForm_add (M M' : QuotHom I I) (f : I.UnitQuot → ℂ) :
    quadForm (M + M') f = quadForm M f + quadForm M' f := by
  simp only [quadForm, LinearMap.add_apply, wInner_add_right, Complex.add_re]
theorem quadForm_ofReal_smul (r : ℝ) (M : QuotHom I I) (f : I.UnitQuot → ℂ) :
    quadForm ((r : ℂ) • M) f = r * quadForm M f := by
  simp only [quadForm, LinearMap.smul_apply, wInner_smul_right, Complex.re_ofReal_mul]
theorem quadForm_scalar (r : ℝ) (f : I.UnitQuot → ℂ) :
    quadForm (scalarQuotHom I r) f = r * wNormSq f := by
  unfold scalarQuotHom
  rw [quadForm_ofReal_smul]
  rfl
omit [Fintype I.UnitQuot] [Fintype I'.UnitQuot] in
theorem quadForm_conj {N : QuotHom I I} (hN : IsSelfAdjointQuotHom N) (M : QuotHom I I)
    (f : I.UnitQuot → ℂ) : quadForm (N.comp (M.comp N)) f = quadForm M (N f) := by
  simp only [quadForm, LinearMap.comp_apply]
  rw [hN f (M (N f))]
omit [Fintype I.UnitQuot] [Fintype I'.UnitQuot] in
theorem quadForm_adjoint_conj {A : QuotHom I I'} {At : QuotHom I' I}
    (hA : IsAdjointQuotHom A At) (T : QuotHom I I) (f : I'.UnitQuot → ℂ) :
    quadForm (A.comp (T.comp At)) f = quadForm T (At f) := by
  simp only [quadForm, LinearMap.comp_apply]
  rw [hA (T (At f)) f]
theorem re_wInner_sub_apply (M M' : QuotHom I I) (f : I.UnitQuot → ℂ) :
    (wInner (I.quotWeight 1) f ((M' - M) f)).re = quadForm M' f - quadForm M f := by
  have e : M' = (M' - M) + M := by abel
  have h := quadForm_add (M' - M) M f
  rw [← e] at h
  unfold quadForm at h ⊢
  linarith
theorem loewnerLE_of_quadForm_le {M M' : QuotHom I I} (h : IsSelfAdjointQuotHom M)
    (h' : IsSelfAdjointQuotHom M') (hle : ∀ f, quadForm M f ≤ quadForm M' f) :
    LoewnerLE M M' where
  isSelfAdjoint_left := h
  isSelfAdjoint_right := h'
  im_eq_zero f := by
    have e : M' f = (M' - M) f + M f := by simp
    have h1 := im_wInner_self_apply h' f
    rw [e, wInner_add_right, Complex.add_im, im_wInner_self_apply h f, add_zero] at h1
    exact h1
  re_nonneg f := by
    rw [re_wInner_sub_apply]
    linarith [hle f]
theorem quadForm_le_of_loewnerLE {M M' : QuotHom I I} (h : LoewnerLE M M')
    (f : I.UnitQuot → ℂ) : quadForm M f ≤ quadForm M' f := by
  have := h.re_nonneg f
  rw [re_wInner_sub_apply] at this
  linarith
theorem wNormSq_nonneg (hw : ∀ c, 0 < I.quotWeight 1 c) (f : I.UnitQuot → ℂ) :
    0 ≤ wNormSq f := by
  unfold wNormSq
  rw [wInner_self_eq, Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (by positivity)
theorem eq_zero_of_wNormSq_eq_zero (hw : ∀ c, 0 < I.quotWeight 1 c) {f : I.UnitQuot → ℂ}
    (h : wNormSq f = 0) : f = 0 := by
  unfold wNormSq at h
  rw [wInner_self_eq, Complex.ofReal_re] at h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (hw i).le (by positivity))).1 h
  funext i
  have hi := hz i (Finset.mem_univ i)
  have : ‖f i‖ ^ 2 = 0 := (mul_eq_zero.1 hi).resolve_left (hw i).ne'
  simpa using this
theorem isInvertible_of_scalar_le (hw : ∀ c, 0 < I.quotWeight 1 c) {H : QuotHom I I} {c : ℝ}
    (hc : 0 < c) (hH : LoewnerLE (scalarQuotHom I c) H) : IsInvertibleQuotHom H := by
  have hinj : Function.Injective H := by
    refine (injective_iff_map_eq_zero H).2 fun f hf => ?_
    have h := quadForm_le_of_loewnerLE hH f
    rw [quadForm_scalar] at h
    have h0 : quadForm H f = 0 := by simp [quadForm, hf, wInner_eq_sum]
    rw [h0] at h
    have hn := wNormSq_nonneg hw f
    refine eq_zero_of_wNormSq_eq_zero hw (le_antisymm ?_ hn)
    nlinarith
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  intro g
  obtain ⟨f, rfl⟩ := hsurj g
  exact ⟨f, rfl, fun f' e => hinj e⟩
omit [Fintype I.UnitQuot] in
theorem isSelfAdjoint_inverse {H : QuotHom I I} (hH : IsSelfAdjointQuotHom H)
    (hi : IsInvertibleQuotHom H) : IsSelfAdjointQuotHom (quotHomInverse H) := fun a b => by
  have h := hH (quotHomInverse H a) (quotHomInverse H b)
  rw [hi.apply_quotHomInverse, hi.apply_quotHomInverse] at h
  exact h.symm
theorem half_wNormSq_le_quadForm_inverse {H : QuotHom I I} (hH : IsSelfAdjointQuotHom H)
    (hi : IsInvertibleQuotHom H) (h0 : ∀ f, 0 ≤ quadForm H f)
    (h2 : ∀ f, quadForm H f ≤ 2 * wNormSq f) (g : I.UnitQuot → ℂ) :
    wNormSq g / 2 ≤ quadForm (quotHomInverse H) g := by
  set u := quotHomInverse H g with hu
  have hHu : H u = g := hi.apply_quotHomInverse g
  have hv := h0 (u + ((-1 / 2 : ℝ) : ℂ) • g)
  have e1 : wInner (I.quotWeight 1) u (H g) = wInner (I.quotWeight 1) g g := by
    rw [← hH u g, hHu]
  have e2 : wInner (I.quotWeight 1) u g = starRingEnd ℂ (wInner (I.quotWeight 1) g u) := by
    rw [conj_wInner]
  have e3 : (wInner (I.quotWeight 1) u g).re = (wInner (I.quotWeight 1) g u).re := by
    rw [e2, Complex.conj_re]
  have hexp : quadForm H (u + ((-1 / 2 : ℝ) : ℂ) • g) =
      (wInner (I.quotWeight 1) g u).re - wNormSq g + quadForm H g / 4 := by
    simp only [quadForm, map_add, map_smul, hHu, wInner_add_left, wInner_add_right,
      wInner_ofReal_smul_left, wInner_smul_right, e1, Complex.add_re, Complex.re_ofReal_mul, e3]
    unfold wNormSq
    ring
  have hg := h2 g
  rw [hexp] at hv
  change wNormSq g / 2 ≤ (wInner (I.quotWeight 1) g u).re
  linarith
end QuadraticForms
theorem quotWeight_one_pos (quotients : Quotients.QuotientTransposeNorm) {I : PeriodicData}
    (hI : IsPeriodic I) (c : I.UnitQuot) : 0 < I.quotWeight 1 c := by
  obtain ⟨ι, rfl⟩ := Quot.exists_rep c
  have hW : WeightFactorsThroughQuot I 1 :=
    ((quotients I I hI hI 1 one_pos).2.1 1 (Or.inl rfl)).1
  have e := hW.2 ι
  change 0 < I.quotWeight 1 (I.mkQuot 1 ι)
  rw [e]
  exact hI.weight_pos _
theorem conjugatedOrderBounds_holds (quotients : Quotients.QuotientTransposeNorm) :
    ConjugatedOrderBounds := by
  intro I J hI hJ N K X A At c cC hc hc1 hcC hN hK hlow hup hroot hA hAN t ht τ hτ
  have := hI.finite_quot
  have := hJ.finite_quot
  let _ : Fintype I.UnitQuot := Fintype.ofFinite _
  let _ : Fintype J.UnitQuot := Fintype.ofFinite _
  have hwI := quotWeight_one_pos quotients hI
  have hKh : IsSelfAdjointQuotHom K := hK.isSelfAdjoint_right
  have hXh : IsSelfAdjointQuotHom X := hup.isSelfAdjoint_left
  have hS := wNormSq_nonneg (I := I) hwI
  have hk : ∀ F, 0 ≤ quadForm K F := fun F => by
    have h := quadForm_le_of_loewnerLE hK F
    rwa [quadForm_scalar, zero_mul] at h
  have hsum : ∀ F, quadForm (K + scalarQuotHom I 1) F = quadForm K F + wNormSq F := fun F => by
    rw [quadForm_add, quadForm_scalar, one_mul]
  have hxlow : ∀ F, c * (quadForm K F + wNormSq F) ≤ quadForm X F := fun F => by
    have h := quadForm_le_of_loewnerLE hlow F
    rwa [quadForm_ofReal_smul, hsum] at h
  have hxup : ∀ F, quadForm X F ≤ quadForm K F + wNormSq F := fun F => by
    have h := quadForm_le_of_loewnerLE hup F
    rwa [hsum] at h
  have hunit : ∀ f, quadForm K (N f) + wNormSq (N f) = wNormSq f := fun f => by
    rw [← hsum, ← quadForm_conj hN, hroot]
    rfl
  have hY : IsSelfAdjointQuotHom ((t : ℂ) • X + ((1 - t : ℝ) : ℂ) • K + scalarQuotHom I 1) :=
    isSelfAdjoint_add (isSelfAdjoint_add (isSelfAdjoint_ofReal_smul _ hXh)
      (isSelfAdjoint_ofReal_smul _ hKh)) (isSelfAdjoint_scalar I 1)
  have hXτ : IsSelfAdjointQuotHom (X + scalarQuotHom I τ) :=
    isSelfAdjoint_add hXh (isSelfAdjoint_scalar I τ)
  have hHh := isSelfAdjoint_conj hN hXτ
  have hformH : ∀ f, quadForm (N.comp ((X + scalarQuotHom I τ).comp N)) f =
      quadForm X (N f) + τ * wNormSq (N f) := fun f => by
    rw [quadForm_conj hN, quadForm_add, quadForm_scalar]
  have hH : LoewnerLE (scalarQuotHom I c) (N.comp ((X + scalarQuotHom I τ).comp N)) := by
    refine loewnerLE_of_quadForm_le (isSelfAdjoint_scalar I c) hHh fun f => ?_
    rw [hformH, quadForm_scalar, ← hunit f]
    have h1 := hxlow (N f)
    have h2 := mul_nonneg hτ.1 (hS (N f))
    linarith
  have hinv := isInvertible_of_scalar_le hwI hc hH
  refine ⟨?_, hH, hinv, ?_⟩
  · refine loewnerLE_of_quadForm_le (isSelfAdjoint_scalar I c) (isSelfAdjoint_conj hN hY)
      fun f => ?_
    rw [quadForm_conj hN, quadForm_add, quadForm_add, quadForm_ofReal_smul, quadForm_ofReal_smul,
      quadForm_scalar, quadForm_scalar, one_mul, ← hunit f]
    have h1 := mul_nonneg ht.1 (sub_nonneg.2 (hxlow (N f)))
    have h2 := mul_nonneg (mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 hc1)) (hk (N f))
    have hct : 0 ≤ 1 - c * (1 - t) := by nlinarith [ht.1, ht.2]
    have h3 := mul_nonneg hct (hS (N f))
    nlinarith
  · set H := N.comp ((X + scalarQuotHom I τ).comp N) with hHdef
    have hH0 : ∀ f, 0 ≤ quadForm H f := fun f => by
      have h := quadForm_le_of_loewnerLE hH f
      rw [quadForm_scalar] at h
      exact (mul_nonneg hc.le (hS f)).trans h
    have hH2 : ∀ f, quadForm H f ≤ 2 * wNormSq f := fun f => by
      rw [hformH, ← hunit f]
      have h1 := hxup (N f)
      have h2 := mul_le_of_le_one_left (hS (N f)) hτ.2
      linarith [hk (N f)]
    have hT : IsSelfAdjointQuotHom (N.comp ((quotHomInverse H).comp N)) :=
      isSelfAdjoint_conj hN (isSelfAdjoint_inverse hHh hinv)
    refine loewnerLE_of_quadForm_le (isSelfAdjoint_scalar J _)
      (isSelfAdjoint_adjoint_conj hA hT) fun f => ?_
    rw [quadForm_scalar, quadForm_adjoint_conj hA, quadForm_conj hN]
    have hhalf := half_wNormSq_le_quadForm_inverse hHh hinv hH0 hH2 (N (At f))
    have hlower := quadForm_le_of_loewnerLE hAN f
    rw [quadForm_scalar, quadForm_adjoint_conj hA] at hlower
    have hNN : quadForm (N.comp N) (At f) = wNormSq (N (At f)) := by
      simp only [quadForm, wNormSq, LinearMap.comp_apply]
      rw [hN (At f) (N (At f))]
    rw [hNN] at hlower
    linarith
end RootConjugationOrder
end YangMills.Construction.PeriodicOperators
end
