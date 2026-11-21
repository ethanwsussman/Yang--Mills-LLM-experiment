import YangMills.Construction.PeriodicOperators.OrbitsOfAPeriodicIndexSetProof
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.PeriodicOperators.SumsOfExponentials
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.PeriodicOperators.Quotients
open YangMills.Construction.TorusMetric (euclidNormVec)
section Classes
variable {I : PeriodicData}
theorem mkQuot_eq_iff (h : IsPeriodic I) (s : ℕ) (x y : I.Carrier) :
    I.mkQuot s x = I.mkQuot s y ↔ ∃ n : Fin 4 → ℤ, y = I.translate (s • n) x := by apply _root_.YangMills.Construction.PeriodicOperators.QuotOrbits.mkQuot_eq_iff <;> assumption
theorem translate_left_injective (h : IsPeriodic I) (x : I.Carrier) {a b : Fin 4 → ℤ}
    (e : I.translate a x = I.translate b x) : a = b := by apply _root_.YangMills.Construction.PeriodicOperators.IdKernelFacts.translate_injective <;> assumption
theorem nonempty_quotMod_equiv (h : IsPeriodic I) (s : ℕ) (hs : 0 < s) :
    Nonempty (I.QuotMod s ≃ I.UnitQuot × (Fin 4 → ZMod s)) := by
  have hrep : ∀ c : I.UnitQuot, ∃ x, I.mkQuot 1 x = c := fun c => Quot.exists_rep c
  choose rep hrep using hrep
  have hcoord : ∀ x, ∃ n : Fin 4 → ℤ, x = I.translate n (rep (I.mkQuot 1 x)) := by
    intro x
    obtain ⟨n, hn⟩ := (mkQuot_eq_iff h 1 _ _).1 (hrep (I.mkQuot 1 x))
    exact ⟨n, by simpa using hn⟩
  choose coord hcoord using hcoord
  have hclass : ∀ (n : Fin 4 → ℤ) x, I.mkQuot 1 (I.translate n x) = I.mkQuot 1 x := fun n x =>
    ((mkQuot_eq_iff h 1 _ _).2 ⟨n, by simp⟩).symm
  have hco : ∀ (n : Fin 4 → ℤ) x, coord (I.translate n x) = coord x + n := by
    intro n x
    apply translate_left_injective h (rep (I.mkQuot 1 x))
    have e1 := hcoord (I.translate n x)
    rw [hclass] at e1
    rw [← e1, h.translate_add, ← hcoord x]
  let F : I.QuotMod s → I.UnitQuot × (Fin 4 → ZMod s) :=
    Quot.lift (fun x => (I.mkQuot 1 x, fun μ => ((coord x μ : ℤ) : ZMod s))) (by
      rintro x _ ⟨n, rfl⟩
      refine Prod.ext (hclass _ _).symm ?_
      funext μ
      simp [hco])
  have hinj : Function.Injective F := by
    intro c c'
    induction c using Quot.ind with
    | mk x =>
      induction c' using Quot.ind with
      | mk y =>
        intro e
        have e1 : I.mkQuot 1 x = I.mkQuot 1 y := congrArg Prod.fst e
        have e2 : ∀ μ, ((coord x μ : ℤ) : ZMod s) = ((coord y μ : ℤ) : ZMod s) :=
          fun μ => congrFun (congrArg Prod.snd e) μ
        have e3 : ∀ μ, ∃ k : ℤ, coord y μ - coord x μ = s * k := by
          intro μ
          obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (coord x μ) (coord y μ) s).1 (e2 μ)
          exact ⟨k, hk⟩
        choose k hk using e3
        have h1 := hcoord y
        rw [← e1] at h1
        have hk' : coord x + s • k = coord y := by
          funext μ
          have := hk μ
          rw [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
          linarith
        apply (mkQuot_eq_iff h s x y).2
        refine ⟨k, ?_⟩
        calc y = I.translate (coord y) (rep (I.mkQuot 1 x)) := h1
          _ = I.translate (s • k) (I.translate (coord x) (rep (I.mkQuot 1 x))) := by
              rw [← h.translate_add, hk']
          _ = I.translate (s • k) x := by rw [← hcoord x]
  have hsurj : Function.Surjective F := by
    rintro ⟨c, z⟩
    have : NeZero s := ⟨hs.ne'⟩
    let n : Fin 4 → ℤ := fun μ => ((z μ).val : ℤ)
    refine ⟨I.mkQuot s (I.translate (n - coord (rep c)) (rep c)), ?_⟩
    refine Prod.ext ((hclass _ _).trans (hrep c)) ?_
    funext μ
    change ((coord (I.translate (n - coord (rep c)) (rep c)) μ : ℤ) : ZMod s) = z μ
    simp [hco, n]
  exact ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩⟩
theorem quotFinite_of_isPeriodic (h : IsPeriodic I) (s : ℕ) (hs : 0 < s) :
    QuotFinite I s := by
  obtain ⟨e⟩ := nonempty_quotMod_equiv h s hs
  have := h.finite_quot
  have : NeZero s := ⟨hs.ne'⟩
  have : Finite (I.QuotMod s) := Finite.of_equiv _ e.symm
  refine ⟨h.finite_quot, inferInstance, ?_⟩
  rw [Nat.card_congr e, Nat.card_prod, mul_comm]
  congr 1
  simp [Nat.card_eq_fintype_card, ZMod.card]
theorem weightOf_translate (h : IsPeriodic I) (n : Fin 4 → ℤ) (x : I.Carrier) :
    I.weightOf (I.translate n x) = I.weightOf x := by
  simp only [PeriodicData.weightOf, h.componentOf_translate]
theorem weightOf_eq_of_mkQuot_eq (h : IsPeriodic I) {t : ℕ} {x y : I.Carrier}
    (e : I.mkQuot t x = I.mkQuot t y) : I.weightOf x = I.weightOf y := by
  obtain ⟨n, rfl⟩ := (mkQuot_eq_iff h t x y).1 e
  exact (weightOf_translate h _ _).symm
theorem quotWeight_mkQuot (h : IsPeriodic I) (t : ℕ) (x : I.Carrier) :
    I.quotWeight t (I.mkQuot t x) = I.weightOf x := by
  have hex : ∃ w, ∀ y, I.mkQuot t y = I.mkQuot t x → I.weightOf y = w :=
    ⟨I.weightOf x, fun y e => weightOf_eq_of_mkQuot_eq h e⟩
  exact (Classical.epsilon_spec hex x rfl).symm
theorem quotWeight_pos (h : IsPeriodic I) (t : ℕ) (c : I.QuotMod t) :
    0 < I.quotWeight t c := by
  obtain ⟨x, rfl⟩ : ∃ x, I.mkQuot t x = c := Quot.exists_rep c
  rw [quotWeight_mkQuot h]
  exact h.weight_pos _
theorem weightFactorsThroughQuot_of_isPeriodic (h : IsPeriodic I) (t : ℕ) :
    WeightFactorsThroughQuot I t :=
  ⟨fun _ _ e => weightOf_eq_of_mkQuot_eq h e, quotWeight_mkQuot h t⟩
theorem exists_weightOf_bounds (h : IsPeriodic I) :
    ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ x, a ≤ I.weightOf x ∧ I.weightOf x ≤ b := by
  have := h.finite_components
  obtain ⟨b, hb⟩ := (Set.finite_range I.weight).bddAbove
  obtain ⟨k, hk⟩ := (Set.finite_range fun p => (I.weight p)⁻¹).bddAbove
  have hpos : 0 < max k 1 := lt_max_of_lt_right one_pos
  refine ⟨(max k 1)⁻¹, max b 0, inv_pos.2 hpos, le_max_right _ _,
    fun x => ⟨?_, (hb ⟨_, rfl⟩).trans (le_max_left _ _)⟩⟩
  have h1 : (I.weightOf x)⁻¹ ≤ max k 1 := (hk ⟨I.componentOf x, rfl⟩).trans (le_max_left _ _)
  exact (inv_le_comm₀ (h.weight_pos _) hpos).1 h1
end Classes
section FiniteSets
variable {J J' : Type}
theorem tsum_weighted_sq_le_one_of_wNorm_le_one {w : J → ℝ} {f : J → ℂ} (h : wNorm w f ≤ 1) :
    ∑' i, w i * ‖f i‖ ^ 2 ≤ 1 := by
  have := (Real.sqrt_le_left zero_le_one).1 h
  simpa using this
variable [Fintype J] [Fintype J']
theorem normSummable_of_fintype (w : J → ℝ) (f : J → ℂ) : NormSummable w f :=
  Summable.of_finite
theorem wNorm_sq (w : J → ℝ) (hw : ∀ i, 0 < w i) (f : J → ℂ) :
    wNorm w f ^ 2 = ∑ i, w i * ‖f i‖ ^ 2 := by
  rw [wNorm, tsum_fintype, Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (sq_nonneg _)
theorem norm_wPairing_le (w : J → ℝ) (hw : ∀ i, 0 < w i) (g h : J → ℂ) :
    ‖wPairing w g h‖ ≤ wNorm w g * wNorm w h := by
  have e : ∀ f : J → ℂ, ∑ i, (√(w i) * ‖f i‖) ^ 2 = ∑ i, w i * ‖f i‖ ^ 2 := fun f =>
    Finset.sum_congr rfl fun i _ => by rw [mul_pow, Real.sq_sqrt (hw i).le]
  calc ‖wPairing w g h‖ = ‖∑ i, (w i : ℂ) * (g i * h i)‖ := by rw [wPairing, tsum_fintype]
    _ ≤ ∑ i, ‖(w i : ℂ) * (g i * h i)‖ := norm_sum_le _ _
    _ = ∑ i, (√(w i) * ‖g i‖) * (√(w i) * ‖h i‖) := Finset.sum_congr rfl fun i _ => by
        have hs := Real.mul_self_sqrt (hw i).le
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw i).le]
        linear_combination (-(‖g i‖ * ‖h i‖)) * hs
    _ ≤ √(∑ i, (√(w i) * ‖g i‖) ^ 2) * √(∑ i, (√(w i) * ‖h i‖) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = wNorm w g * wNorm w h := by
        simp only [e, wNorm, tsum_fintype]
theorem wPairing_wTranspose (w : J → ℝ) (w' : J' → ℝ) (hw : ∀ i, 0 < w i) (M : J' → J → ℂ)
    (f : J → ℂ) (g : J' → ℂ) :
    wPairing w (applyKernel (wTranspose w w' M) g) f = wPairing w' g (applyKernel M f) := by
  simp only [wPairing, applyKernel, wTranspose, tsum_fintype, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_comm.trans
    (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_)
  have hne : (w i : ℂ) ≠ 0 := by exact_mod_cast (hw i).ne'
  rw [Complex.ofReal_div]
  field_simp
theorem conjFun_applyKernel_wTranspose (w : J → ℝ) (w' : J' → ℝ) (M : J' → J → ℂ) (g : J' → ℂ) :
    conjFun (applyKernel (wTranspose w w' (conjKernel M)) g) =
      applyKernel (wTranspose w w' M) (conjFun g) := by
  funext i
  simp only [conjFun, applyKernel, wTranspose, conjKernel, tsum_fintype, map_sum,
    map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
theorem wOpNorm_linearMap_lt_top (w : J → ℝ) (w' : J' → ℝ) (hw : ∀ i, 0 < w i)
    (hw' : ∀ i, 0 < w' i) (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) :
    wOpNorm w w' univ M < ∞ := by
  let Mc : (J → ℂ) →L[ℂ] (J' → ℂ) := LinearMap.toContinuousLinearMap M
  set R : ℝ := 1 + ∑ c, (w c)⁻¹ with hR
  have hS : 0 ≤ ∑ c, (w c)⁻¹ := Finset.sum_nonneg fun c _ => (inv_pos.2 (hw c)).le
  have hR0 : 0 ≤ R := by linarith
  set B : ℝ := ‖Mc‖ * R with hB
  refine lt_of_le_of_lt (iSup₂_le fun f hf => ?_)
    (ENNReal.ofReal_lt_top (r := √(∑ j, w' j * B ^ 2)))
  refine ENNReal.ofReal_le_ofReal ?_
  have hsum : ∑ c, w c * ‖f c‖ ^ 2 ≤ 1 := by
    have := tsum_weighted_sq_le_one_of_wNorm_le_one hf.2.2
    rwa [tsum_fintype] at this
  have hfc : ∀ c, ‖f c‖ ≤ R := by
    intro c
    have h1 : w c * ‖f c‖ ^ 2 ≤ 1 :=
      (Finset.single_le_sum (f := fun c => w c * ‖f c‖ ^ 2)
        (fun i _ => mul_nonneg (hw i).le (sq_nonneg _)) (Finset.mem_univ c)).trans hsum
    have hne := (hw c).ne'
    have h2 : ‖f c‖ ^ 2 ≤ (w c)⁻¹ := by
      calc ‖f c‖ ^ 2 = (w c)⁻¹ * (w c * ‖f c‖ ^ 2) := by field_simp
        _ ≤ (w c)⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (inv_pos.2 (hw c)).le
        _ = (w c)⁻¹ := mul_one _
    have h3 : (w c)⁻¹ ≤ R :=
      (Finset.single_le_sum (f := fun c => (w c)⁻¹) (fun i _ => (inv_pos.2 (hw i)).le)
        (Finset.mem_univ c)).trans (le_add_of_nonneg_left zero_le_one)
    have h4 : R ≤ R ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR0 two_ne_zero).1 (h2.trans (h3.trans h4))
  have hpi : ‖f‖ ≤ R := (pi_norm_le_iff_of_nonneg hR0).2 hfc
  have hMf : ‖M f‖ ≤ ‖Mc‖ * ‖f‖ := Mc.le_opNorm f
  have hM : ∀ j, ‖M f j‖ ≤ B := fun j =>
    (norm_le_pi_norm (M f) j).trans
      (hMf.trans (mul_le_mul_of_nonneg_left hpi (norm_nonneg _)))
  simp only [wNorm, tsum_fintype]
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hM j) 2) (hw' j).le)
theorem wOpNorm_wTranspose_le (w : J → ℝ) (w' : J' → ℝ) (hw : ∀ i, 0 < w i)
    (hw' : ∀ i, 0 < w' i) (M : J' → J → ℂ) :
    wOpNorm w' w univ (applyKernel (wTranspose w w' M)) ≤
      wOpNorm w w' univ (applyKernel M) := by
  refine iSup₂_le fun g hg => ?_
  set u := applyKernel (wTranspose w w' M) g with hu
  set a := wNorm w u with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  rcases ha0.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp
  have hne : a ≠ 0 := hpos.ne'
  have hneC : (a : ℂ) ≠ 0 := by exact_mod_cast hne
  have hsq : ∑ i, w i * ‖u i‖ ^ 2 = a ^ 2 := (wNorm_sq w hw u).symm
  let f : J → ℂ := fun i => conj (u i) / a
  have hfn : wNorm w f ^ 2 = 1 := by
    rw [wNorm_sq w hw]
    have e : ∀ i, w i * ‖f i‖ ^ 2 = (w i * ‖u i‖ ^ 2) / a ^ 2 := fun i => by
      simp only [f, norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg ha0]
      ring
    simp only [e]
    rw [← Finset.sum_div, hsq]
    field_simp
  have hf1 : wNorm w f ≤ 1 := by
    have h0 : 0 ≤ wNorm w f := Real.sqrt_nonneg _
    nlinarith
  have hpair : wPairing w u f = a := by
    rw [wPairing, tsum_fintype]
    have e : ∀ i, (w i : ℂ) * (u i * f i) = ((w i * ‖u i‖ ^ 2 : ℝ) : ℂ) / a := fun i => by
      simp only [f]
      push_cast
      rw [← Complex.mul_conj']
      ring
    simp only [e]
    rw [← Finset.sum_div, ← Complex.ofReal_sum, hsq]
    push_cast
    field_simp
  have hmem : f ∈ wUnitBall w univ := ⟨mem_univ _, normSummable_of_fintype _ _, hf1⟩
  have h1 : a ≤ wNorm w' (applyKernel M f) := by
    have e := wPairing_wTranspose w w' hw M f g
    have hcs := norm_wPairing_le w' hw' g (applyKernel M f)
    rw [← e, hpair, Complex.norm_real, Real.norm_of_nonneg ha0] at hcs
    have hg1 : wNorm w' g ≤ 1 := hg.2.2
    have hn : 0 ≤ wNorm w' (applyKernel M f) := Real.sqrt_nonneg _
    nlinarith
  exact (ENNReal.ofReal_le_ofReal h1).trans
    (le_iSup₂ (f := fun f (_ : f ∈ wUnitBall w univ) =>
      ENNReal.ofReal (wNorm w' (applyKernel M f))) f hmem)
theorem wTranspose_wTranspose (w : J → ℝ) (w' : J' → ℝ) (hw : ∀ i, 0 < w i)
    (hw' : ∀ i, 0 < w' i) (M : J' → J → ℂ) : wTranspose w' w (wTranspose w w' M) = M := by
  funext j i
  have h1 : (w i : ℂ) ≠ 0 := by exact_mod_cast (hw i).ne'
  have h2 : (w' j : ℂ) ≠ 0 := by exact_mod_cast (hw' j).ne'
  simp only [wTranspose, Complex.ofReal_div]
  field_simp
theorem wOpNorm_wTranspose (w : J → ℝ) (w' : J' → ℝ) (hw : ∀ i, 0 < w i)
    (hw' : ∀ i, 0 < w' i) (M : J' → J → ℂ) :
    wOpNorm w' w univ (applyKernel (wTranspose w w' M)) =
      wOpNorm w w' univ (applyKernel M) := by
  refine le_antisymm (wOpNorm_wTranspose_le w w' hw hw' M) ?_
  have := wOpNorm_wTranspose_le w' w hw' hw (wTranspose w w' M)
  rwa [wTranspose_wTranspose w w' hw hw'] at this
end FiniteSets
section Schur
variable {J J' : Type}
theorem sq_tsum_mul_le_tsum_mul_tsum {t u : J → ℝ} (ht : ∀ i, 0 ≤ t i) (h0 : Summable t)
    (h1 : Summable fun i => t i * u i) (h2 : Summable fun i => t i * u i ^ 2) :
    (∑' i, t i * u i) ^ 2 ≤ (∑' i, t i) * ∑' i, t i * u i ^ 2 := by
  have hq : ∀ x : ℝ, 0 ≤ (∑' i, t i) * (x * x) + (-2 * ∑' i, t i * u i) * x +
      ∑' i, t i * u i ^ 2 := by
    intro x
    have hs := ((h0.hasSum.mul_right (x * x)).add (h1.hasSum.mul_right (-2 * x))).add h2.hasSum
    have hn := hs.nonneg fun i => by
      have e : t i * (x * x) + t i * u i * (-2 * x) + t i * u i ^ 2 = t i * (u i - x) ^ 2 := by
        ring
      rw [e]
      exact mul_nonneg (ht i) (sq_nonneg _)
    linarith
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith
theorem summable_tsum_comm_of_nonneg {a : J' → J → ℝ} (ha : ∀ j i, 0 ≤ a j i)
    (hcol : ∀ i, Summable fun j => a j i) (hs : Summable fun i => ∑' j, a j i) :
    (Summable fun j => ∑' i, a j i) ∧ ∑' j, ∑' i, a j i = ∑' i, ∑' j, a j i := by
  have hF : Summable (Function.uncurry fun i j => a j i) :=
    (summable_prod_of_nonneg fun p => ha _ _).2 ⟨hcol, hs⟩
  have hFs : Summable (Function.uncurry a) := hF.prod_symm
  exact ⟨((summable_prod_of_nonneg fun p => ha _ _).1 hFs).2, hF.tsum_comm⟩
theorem schur_test {t : J' → J → ℝ} {u : J → ℝ} {P Q C : ℝ}
    (ht : ∀ j i, 0 ≤ t j i) (hC : ∀ j i, t j i ≤ C)
    (hrow : ∀ j, Summable (t j)) (hrowb : ∀ j, ∑' i, t j i ≤ P)
    (hcol : ∀ i, Summable fun j => t j i) (hcolb : ∀ i, ∑' j, t j i ≤ Q)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hu0 : ∀ i, 0 ≤ u i) (hu : Summable fun i => u i ^ 2) :
    (∀ j, Summable fun i => t j i * u i) ∧
      Summable (fun j => (∑' i, t j i * u i) ^ 2) ∧
      ∑' j, (∑' i, t j i * u i) ^ 2 ≤ P * Q * ∑' i, u i ^ 2 := by
  have h2 : ∀ j, Summable fun i => t j i * u i ^ 2 := fun j =>
    Summable.of_nonneg_of_le (fun i => mul_nonneg (ht j i) (sq_nonneg _))
      (fun i => mul_le_mul_of_nonneg_right (hC j i) (sq_nonneg _)) (hu.mul_left C)
  have h1 : ∀ j, Summable fun i => t j i * u i := fun j => by
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (ht j i) (hu0 i)) (fun i => ?_)
      ((hrow j).add (h2 j))
    have := mul_nonneg (ht j i) (by nlinarith [sq_nonneg (u i - 1)] : 0 ≤ 1 + u i ^ 2 - u i)
    linarith
  have hin : ∀ i, ∑' j, t j i * u i ^ 2 ≤ Q * u i ^ 2 := fun i => by
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (hcolb i) (sq_nonneg _)
  have hcs : ∀ i, Summable fun j => t j i * u i ^ 2 := fun i => (hcol i).mul_right _
  have hcsum : Summable fun i => ∑' j, t j i * u i ^ 2 :=
    Summable.of_nonneg_of_le
      (fun i => tsum_nonneg fun j => mul_nonneg (ht j i) (sq_nonneg _)) hin (hu.mul_left Q)
  obtain ⟨hg, hcomm⟩ :=
    summable_tsum_comm_of_nonneg (fun j i => mul_nonneg (ht j i) (sq_nonneg (u i))) hcs hcsum
  have hv : ∀ j, (∑' i, t j i * u i) ^ 2 ≤ P * ∑' i, t j i * u i ^ 2 := fun j =>
    (sq_tsum_mul_le_tsum_mul_tsum (ht j) (hrow j) (h1 j) (h2 j)).trans
      (mul_le_mul_of_nonneg_right (hrowb j) (tsum_nonneg fun i => mul_nonneg (ht j i) (sq_nonneg _)))
  have hs : Summable fun j => (∑' i, t j i * u i) ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hv (hg.mul_left P)
  refine ⟨h1, hs, ?_⟩
  calc ∑' j, (∑' i, t j i * u i) ^ 2 ≤ ∑' j, P * ∑' i, t j i * u i ^ 2 :=
        Summable.tsum_le_tsum hv hs (hg.mul_left P)
    _ = P * ∑' i, ∑' j, t j i * u i ^ 2 := by rw [tsum_mul_left, hcomm]
    _ ≤ P * ∑' i, Q * u i ^ 2 := mul_le_mul_of_nonneg_left
        (Summable.tsum_le_tsum hin hcsum (hu.mul_left Q)) hP
    _ = P * Q * ∑' i, u i ^ 2 := by rw [tsum_mul_left, mul_assoc]
theorem summable_and_tsum_le_of_le_mul {t e : J → ℝ} {C A : ℝ} (hC : 0 < C) (ht : ∀ i, 0 ≤ t i)
    (hle : ∀ i, t i ≤ C * e i) (he : Summable e) (hA : ∑' i, e i ≤ A) :
    Summable t ∧ ∑' i, t i ≤ C * A := by
  have hs := he.mul_left C
  have h1 : Summable t := Summable.of_nonneg_of_le ht hle hs
  refine ⟨h1, ?_⟩
  calc ∑' i, t i ≤ ∑' i, C * e i := Summable.tsum_le_tsum hle h1 hs
    _ = C * ∑' i, e i := tsum_mul_left
    _ ≤ C * A := mul_le_mul_of_nonneg_left hA hC.le
end Schur
section PeriodicKernel
theorem euclidNormVec_sub_comm (a b : Fin 4 → ℝ) :
    euclidNormVec (a - b) = euclidNormVec (b - a) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
variable {I I' : PeriodicData}
theorem periodicKernel_exists_bound (H : ExponentialSums.Bounds) (h : IsPeriodic I)
    (h' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ} (hT : IsPeriodicKernel I I' T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f ∈ finiteNormSpace I,
      (∀ y, ApplySummableAt T f y) ∧ NormSummable I'.weightOf (applyKernel T f) ∧
        ∑' y, I'.weightOf y * ‖applyKernel T f y‖ ^ 2 ≤
          K * ∑' x, I.weightOf x * ‖f x‖ ^ 2 := by
  obtain ⟨-, C, δ, hC, hδ, hb⟩ := hT
  obtain ⟨a, _, ha, _, hab⟩ := exists_weightOf_bounds h
  obtain ⟨_, b', _, hb0, hab'⟩ := exists_weightOf_bounds h'
  obtain ⟨-, -, hsum⟩ := H δ hδ
  set A : ℝ := (Nat.card I.UnitQuot : ℝ) * (Real.exp (2 * δ) * expHalfSum δ ^ 4) with hAdef
  set A' : ℝ := (Nat.card I'.UnitQuot : ℝ) * (Real.exp (2 * δ) * expHalfSum δ ^ 4) with hA'def
  have hA : 0 ≤ A := by positivity
  have hA' : 0 ≤ A' := by positivity
  have hbound : ∀ y x, ‖T y x‖ ≤
      C * Real.exp (-δ * euclidNormVec (I'.pos y - I.pos x)) := hb
  have hrow : ∀ y, Summable (fun x => ‖T y x‖) ∧ ∑' x, ‖T y x‖ ≤ C * A := fun y => by
    obtain ⟨s1, s2⟩ := hsum I h (I'.pos y)
    exact summable_and_tsum_le_of_le_mul hC (fun _ => norm_nonneg _) (fun x => by
      have := hbound y x
      rwa [euclidNormVec_sub_comm] at this) s1 s2
  have hcol : ∀ x, Summable (fun y => ‖T y x‖) ∧ ∑' y, ‖T y x‖ ≤ C * A' := fun x => by
    obtain ⟨s1, s2⟩ := hsum I' h' (I.pos x)
    exact summable_and_tsum_le_of_le_mul hC (fun _ => norm_nonneg _) (fun y => hbound y x) s1 s2
  have hCb : ∀ y x, ‖T y x‖ ≤ C := fun y x => by
    have h0 : 0 ≤ euclidNormVec (I'.pos y - I.pos x) := Real.sqrt_nonneg _
    have h1 : Real.exp (-δ * euclidNormVec (I'.pos y - I.pos x)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith)
    have := hbound y x
    nlinarith
  have hP : 0 ≤ C * A := mul_nonneg hC.le hA
  have hQ : 0 ≤ C * A' := mul_nonneg hC.le hA'
  refine ⟨b' * (C * A * (C * A')) * a⁻¹,
    mul_nonneg (mul_nonneg hb0 (mul_nonneg hP hQ)) (inv_pos.2 ha).le, fun f hf => ?_⟩
  have hwn : ∀ x, 0 ≤ I.weightOf x * ‖f x‖ ^ 2 := fun x =>
    mul_nonneg (ha.le.trans (hab x).1) (sq_nonneg _)
  have hf' : Summable fun x => I.weightOf x * ‖f x‖ ^ 2 :=
    (summable_congr fun x => abs_of_nonneg (hwn x)).1 hf
  have hpt : ∀ x, ‖f x‖ ^ 2 ≤ a⁻¹ * (I.weightOf x * ‖f x‖ ^ 2) := fun x => by
    have hne := ha.ne'
    calc ‖f x‖ ^ 2 = a⁻¹ * (a * ‖f x‖ ^ 2) := by field_simp
      _ ≤ a⁻¹ * (I.weightOf x * ‖f x‖ ^ 2) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hab x).1 (sq_nonneg _)) (inv_pos.2 ha).le
  have hu : Summable fun x => ‖f x‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hpt (hf'.mul_left a⁻¹)
  obtain ⟨s1, s2, s3⟩ := schur_test (t := fun y x => ‖T y x‖) (u := fun x => ‖f x‖)
    (fun _ _ => norm_nonneg _) hCb (fun j => (hrow j).1) (fun j => (hrow j).2)
    (fun i => (hcol i).1) (fun i => (hcol i).2) hP hQ (fun _ => norm_nonneg _) hu
  have hform : ∀ y, ApplySummableAt T f y := fun y =>
    (summable_congr fun x => norm_mul _ _).2 (s1 y)
  have hle : ∀ y, ‖applyKernel T f y‖ ≤ ∑' x, ‖T y x‖ * ‖f x‖ := fun y => by
    have := norm_tsum_le_tsum_norm (hform y)
    simpa only [applyKernel, norm_mul] using this
  have hterm : ∀ y, I'.weightOf y * ‖applyKernel T f y‖ ^ 2 ≤
      b' * (∑' x, ‖T y x‖ * ‖f x‖) ^ 2 := fun y =>
    mul_le_mul (hab' y).2 (pow_le_pow_left₀ (norm_nonneg _) (hle y) 2) (sq_nonneg _) hb0
  have hnn : ∀ y, 0 ≤ I'.weightOf y * ‖applyKernel T f y‖ ^ 2 := fun y =>
    mul_nonneg (h'.weight_pos _).le (sq_nonneg _)
  have hs' : Summable fun y => I'.weightOf y * ‖applyKernel T f y‖ ^ 2 :=
    Summable.of_nonneg_of_le hnn hterm (s2.mul_left b')
  have hU : ∑' x, ‖f x‖ ^ 2 ≤ a⁻¹ * ∑' x, I.weightOf x * ‖f x‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hpt hu (hf'.mul_left _)
  refine ⟨hform, (summable_congr fun y => abs_of_nonneg (hnn y)).2 hs', ?_⟩
  calc ∑' y, I'.weightOf y * ‖applyKernel T f y‖ ^ 2
      ≤ ∑' y, b' * (∑' x, ‖T y x‖ * ‖f x‖) ^ 2 :=
        Summable.tsum_le_tsum hterm hs' (s2.mul_left b')
    _ = b' * ∑' y, (∑' x, ‖T y x‖ * ‖f x‖) ^ 2 := tsum_mul_left
    _ ≤ b' * (C * A * (C * A') * ∑' x, ‖f x‖ ^ 2) := mul_le_mul_of_nonneg_left s3 hb0
    _ ≤ b' * (C * A * (C * A') * (a⁻¹ * ∑' x, I.weightOf x * ‖f x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU (mul_nonneg hP hQ)) hb0
    _ = b' * (C * A * (C * A')) * a⁻¹ * ∑' x, I.weightOf x * ‖f x‖ ^ 2 := by ring
theorem periodicKernel_mapsFiniteNorm_opNormFinite (H : ExponentialSums.Bounds)
    (h : IsPeriodic I) (h' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) :
    MapsFiniteNorm I I' T ∧ OpNormFinite I I' T := by
  obtain ⟨K, hK0, hK⟩ := periodicKernel_exists_bound H h h' hT
  refine ⟨fun f hf => ⟨(hK f hf).1, (hK f hf).2.1⟩, fun f hf => (hK f hf.1).2.1, ?_⟩
  refine lt_of_le_of_lt (iSup₂_le fun f hf => ?_) (ENNReal.ofReal_lt_top (r := √K))
  refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
  have h3 := (hK f hf.1).2.2
  have hU := tsum_weighted_sq_le_one_of_wNorm_le_one hf.2.2
  calc ∑' y, I'.weightOf y * ‖applyKernel T f y‖ ^ 2
      ≤ K * ∑' x, I.weightOf x * ‖f x‖ ^ 2 := h3
    _ ≤ K * 1 := mul_le_mul_of_nonneg_left hU hK0
    _ = K := mul_one _
end PeriodicKernel
theorem pairingNormFiniteSum_of_isPeriodic {I : PeriodicData} (h : IsPeriodic I) (t : ℕ)
    (ht : 0 < t) : PairingNormFiniteSum I t := by
  have : Finite (I.QuotMod t) := (quotFinite_of_isPeriodic h t ht).2.1
  intro f f'
  refine ⟨Summable.of_finite, Summable.of_finite, tsum_eq_finsum (Set.toFinite _), ?_⟩
  rw [wNorm, tsum_eq_finsum (Set.toFinite _)]
theorem quotientTransposeNorm_of_bounds (H : ExponentialSums.Bounds) : QuotientTransposeNorm := by
  intro I I' h h' s hs
  have hpos : ∀ t : ℕ, t = 1 ∨ t = s → 0 < t := by
    rintro t (rfl | rfl)
    exacts [one_pos, hs]
  refine ⟨quotFinite_of_isPeriodic h s hs, fun t ht => ⟨weightFactorsThroughQuot_of_isPeriodic h t,
    pairingNormFiniteSum_of_isPeriodic h t (hpos t ht)⟩, fun t t' ht ht' => ?_,
    fun T hT => periodicKernel_mapsFiniteNorm_opNormFinite H h h' hT⟩
  have : Finite (I.QuotMod t) := (quotFinite_of_isPeriodic h t (hpos t ht)).2.1
  have : Finite (I'.QuotMod t') := (quotFinite_of_isPeriodic h' t' (hpos t' ht')).2.1
  letI := Fintype.ofFinite (I.QuotMod t)
  letI := Fintype.ofFinite (I'.QuotMod t')
  have hw := quotWeight_pos h t
  have hw' := quotWeight_pos h' t'
  refine ⟨fun M => ⟨fun f _ => normSummable_of_fintype _ _,
    wOpNorm_linearMap_lt_top _ _ hw hw' M⟩, fun M f g => wPairing_wTranspose _ _ hw M f g,
    fun M f g => ?_, fun M => wOpNorm_wTranspose _ _ hw hw' M⟩
  rw [conjFun_applyKernel_wTranspose]
  exact wPairing_wTranspose _ _ hw M f _
end YangMills.Construction.PeriodicOperators.Quotients
end
