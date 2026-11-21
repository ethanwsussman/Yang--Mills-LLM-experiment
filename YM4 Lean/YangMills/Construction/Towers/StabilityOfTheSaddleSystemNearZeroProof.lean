import YangMills.Construction.PeriodicOperators.CyclicityAndTransposeOfTheTraceNumberProof
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHomProof
import YangMills.Construction.PeriodicOperators.OrderOfHermitianMatricesUnderARootProof
import YangMills.Construction.Towers.FreeOperatorsAtTheRealPoints
import YangMills.Construction.Towers.SandwichesOfTheFreeOperatorsInCoefficients
import YangMills.Construction.Towers.StabilityOfTheSaddleSystemNearZero
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.SaddleStability
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.StripSymbols (openStripInterior)
open YangMills.Construction.Tower.FreeCoercivity (edgeResolventConjugate)
open YangMills.Construction.Tower.FreeResolvents (edgeResolvent trivialRescaledOperators)
section FiniteSets
variable {J : Type} [Fintype J] (w : J → ℝ)
theorem wInner_eq_sum (h h' : J → ℂ) :
    wInner w h h' = ∑ i, (w i : ℂ) * (starRingEnd ℂ (h i) * h' i) := by apply _root_.YangMills.Construction.PeriodicOperators.RootConjugationOrder.wInner_eq_sum <;> assumption
theorem wInner_add (h f g : J → ℂ) :
    wInner w h (f + g) = wInner w h f + wInner w h g := by
  simp only [wInner_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]
theorem wInner_smul (c : ℂ) (h f : J → ℂ) :
    wInner w h (c • f) = c * wInner w h f := by apply _root_.YangMills.Construction.PeriodicOperators.RootConjugationOrder.wInner_smul_right <;> assumption
theorem wInner_zero (h : J → ℂ) : wInner w h 0 = 0 := by
  simp only [wInner_eq_sum, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
theorem conj_wInner (h h' : J → ℂ) :
    starRingEnd ℂ (wInner w h h') = wInner w h' h := by apply _root_.YangMills.Construction.PeriodicOperators.RootConjugationOrder.conj_wInner <;> assumption
theorem re_wInner_self (h : J → ℂ) :
    (wInner w h h).re = ∑ i, w i * ‖h i‖ ^ 2 := by
  rw [wInner_eq_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
theorem eq_zero_of_re_wInner_self_nonpos {w : J → ℝ} (hw : ∀ i, 0 < w i) {h : J → ℂ}
    (h0 : (wInner w h h).re ≤ 0) : h = 0 := by
  rw [re_wInner_self] at h0
  have hn : ∀ i ∈ Finset.univ, 0 ≤ w i * ‖h i‖ ^ 2 := fun i _ => by
    have := hw i
    positivity
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).1 (le_antisymm h0 (Finset.sum_nonneg hn))
  funext i
  have hi := hz i (Finset.mem_univ i)
  have hwi := (hw i).ne'
  simpa [hwi] using hi
theorem wNorm_eq_sqrt (f : J → ℂ) :
    wNorm w f = Real.sqrt (∑ i, w i * ‖f i‖ ^ 2) := by
  rw [wNorm, tsum_fintype]
omit [Fintype J] in
theorem wNorm_nonneg (f : J → ℂ) : 0 ≤ wNorm w f := Real.sqrt_nonneg _
theorem exists_wNorm_le_mul_norm {w : J → ℝ} (hw : ∀ i, 0 < w i) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ f : J → ℂ, wNorm w f ≤ a * ‖f‖ := by
  have hs : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => (hw i).le
  refine ⟨Real.sqrt (∑ i, w i), Real.sqrt_nonneg _, fun f => ?_⟩
  rw [wNorm_eq_sqrt]
  have hle : ∑ i, w i * ‖f i‖ ^ 2 ≤ (∑ i, w i) * ‖f‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hw i).le
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm f i) 2
  calc Real.sqrt (∑ i, w i * ‖f i‖ ^ 2) ≤ Real.sqrt ((∑ i, w i) * ‖f‖ ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt (∑ i, w i) * ‖f‖ := by
      rw [Real.sqrt_mul hs, Real.sqrt_sq (norm_nonneg _)]
theorem exists_norm_le_mul_wNorm {w : J → ℝ} (hw : ∀ i, 0 < w i) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ f : J → ℂ, ‖f‖ ≤ a * wNorm w f := by
  have hnn : ∀ i, 0 ≤ (Real.sqrt (w i))⁻¹ := fun i => inv_nonneg.2 (Real.sqrt_nonneg _)
  have ha : 0 ≤ ∑ i, (Real.sqrt (w i))⁻¹ := Finset.sum_nonneg fun i _ => hnn i
  refine ⟨∑ i, (Real.sqrt (w i))⁻¹, ha, fun f => ?_⟩
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg ha (wNorm_nonneg w f))).2 fun i => ?_
  have hsq : 0 < Real.sqrt (w i) := Real.sqrt_pos.2 (hw i)
  have hterm : w i * ‖f i‖ ^ 2 ≤ ∑ j, w j * ‖f j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => w j * ‖f j‖ ^ 2)
      (fun j _ => mul_nonneg (hw j).le (by positivity)) (Finset.mem_univ i)
  have h₁ : Real.sqrt (w i) * ‖f i‖ ≤ wNorm w f := by
    rw [wNorm_eq_sqrt]
    refine Real.le_sqrt_of_sq_le ?_
    rwa [mul_pow, Real.sq_sqrt (hw i).le]
  have h₂ : ‖f i‖ ≤ (Real.sqrt (w i))⁻¹ * wNorm w f := by
    rw [inv_mul_eq_div, le_div_iff₀ hsq, mul_comm]
    exact h₁
  refine h₂.trans (mul_le_mul_of_nonneg_right ?_ (wNorm_nonneg w f))
  exact Finset.single_le_sum (f := fun j => (Real.sqrt (w j))⁻¹) (fun j _ => hnn j)
    (Finset.mem_univ i)
end FiniteSets
section Entries
variable {J J' : Type} [Fintype J] [Fintype J']
omit [Fintype J'] in
theorem apply_eq_sum_linearMapEntry (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (b : J → ℂ) (c' : J') :
    M b c' = ∑ c, linearMapEntry M c' c * b c := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.apply_eq_sum_linearMapEntry <;> assumption
def entryNormSum (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) : ℝ := ∑ c', ∑ c, ‖linearMapEntry M c' c‖
theorem entryNormSum_nonneg (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) : 0 ≤ entryNormSum M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
theorem norm_apply_le_entryNormSum (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (f : J → ℂ) :
    ‖M f‖ ≤ entryNormSum M * ‖f‖ := by
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg (entryNormSum_nonneg M) (norm_nonneg _))).2 fun c' => ?_
  rw [apply_eq_sum_linearMapEntry]
  calc ‖∑ c, linearMapEntry M c' c * f c‖ ≤ ∑ c, ‖linearMapEntry M c' c * f c‖ := norm_sum_le _ _
    _ ≤ ∑ c, ‖linearMapEntry M c' c‖ * ‖f‖ := Finset.sum_le_sum fun c _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm f c) (norm_nonneg _)
    _ = (∑ c, ‖linearMapEntry M c' c‖) * ‖f‖ := by rw [Finset.sum_mul]
    _ ≤ entryNormSum M * ‖f‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact Finset.single_le_sum (f := fun d => ∑ c, ‖linearMapEntry M d c‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ c')
theorem tendsto_entryNormSum_sub {P : Type} [TopologicalSpace P]
    (M : P → (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (p₀ : P)
    (h : ∀ c' c, ContinuousAt (fun p => linearMapEntry (M p) c' c) p₀) :
    Tendsto (fun p => entryNormSum (M p - M p₀)) (𝓝 p₀) (𝓝 0) := by
  have hterm : ∀ c' c, Tendsto (fun p => ‖linearMapEntry (M p - M p₀) c' c‖) (𝓝 p₀) (𝓝 0) := by
    intro c' c
    have h₁ : Tendsto (fun p => linearMapEntry (M p) c' c - linearMapEntry (M p₀) c' c) (𝓝 p₀)
        (𝓝 (linearMapEntry (M p₀) c' c - linearMapEntry (M p₀) c' c)) :=
      (h c' c).tendsto.sub_const _
    rw [sub_self] at h₁
    exact tendsto_zero_iff_norm_tendsto_zero.1 h₁
  have hs : Tendsto (fun p => ∑ c', ∑ c, ‖linearMapEntry (M p - M p₀) c' c‖) (𝓝 p₀)
      (𝓝 (∑ _c' : J', ∑ _c : J, (0 : ℝ))) :=
    tendsto_finsetSum _ fun c' _ => tendsto_finsetSum _ fun c _ => hterm c' c
  simpa [entryNormSum] using hs
end Entries
theorem saddle_bounded_below_near {P : Type} [TopologicalSpace P] {J₁ J₂ : Type} [Fintype J₁]
    [Fintype J₂] {w₁ : J₁ → ℝ} {w₂ : J₂ → ℝ} (hw₁ : ∀ i, 0 < w₁ i) (hw₂ : ∀ i, 0 < w₂ i)
    (A : P → (J₁ → ℂ) →ₗ[ℂ] (J₁ → ℂ)) (B : P → (J₂ → ℂ) →ₗ[ℂ] (J₁ → ℂ))
    (D : P → (J₁ → ℂ) →ₗ[ℂ] (J₂ → ℂ)) (p₀ : P)
    (hA : ∀ c' c, ContinuousAt (fun p => linearMapEntry (A p) c' c) p₀)
    (hB : ∀ c' c, ContinuousAt (fun p => linearMapEntry (B p) c' c) p₀)
    (hD : ∀ c' c, ContinuousAt (fun p => linearMapEntry (D p) c' c) p₀)
    (hinj : ∀ u v, A p₀ u - B p₀ v = 0 → D p₀ u = 0 → u = 0 ∧ v = 0) :
    ∃ C : ℝ, ∃ N ∈ 𝓝 p₀, ∀ p ∈ N, ∀ (u : J₁ → ℂ) (v : J₂ → ℂ),
      wNorm w₁ u + wNorm w₂ v ≤
        C * (wNorm w₁ (A p u - B p v) + wNorm w₂ (D p u)) := by
  let F₀ : ((J₁ → ℂ) × (J₂ → ℂ)) →ₗ[ℂ] ((J₁ → ℂ) × (J₂ → ℂ)) :=
    ((A p₀).comp (LinearMap.fst ℂ _ _) - (B p₀).comp (LinearMap.snd ℂ _ _)).prod
      ((D p₀).comp (LinearMap.fst ℂ _ _))
  have hF₀ : ∀ u v, F₀ (u, v) = (A p₀ u - B p₀ v, D p₀ u) := fun _ _ => rfl
  have hker : LinearMap.ker F₀ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨u, v⟩ h
    rw [hF₀] at h
    obtain ⟨hu, hv⟩ := hinj u v (congrArg Prod.fst h) (congrArg Prod.snd h)
    rw [hu, hv]
    rfl
  obtain ⟨K, hKpos, hanti⟩ := LinearMap.exists_antilipschitzWith F₀ hker
  have hK : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hlow : ∀ x, ‖x‖ ≤ (K : ℝ) * ‖F₀ x‖ := fun x => by
    have h := hanti.le_mul_dist x 0
    simpa [dist_zero_right] using h
  obtain ⟨a₁, ha₁, hα₁⟩ := exists_wNorm_le_mul_norm hw₁
  obtain ⟨a₂, ha₂, hα₂⟩ := exists_wNorm_le_mul_norm hw₂
  obtain ⟨e₁, he₁, hε₁⟩ := exists_norm_le_mul_wNorm hw₁
  obtain ⟨e₂, he₂, hε₂⟩ := exists_norm_le_mul_wNorm hw₂
  have hsum : Tendsto (fun p => entryNormSum (A p - A p₀) + entryNormSum (B p - B p₀) +
      entryNormSum (D p - D p₀)) (𝓝 p₀) (𝓝 (0 + 0 + 0)) :=
    ((tendsto_entryNormSum_sub A p₀ hA).add (tendsto_entryNormSum_sub B p₀ hB)).add
      (tendsto_entryNormSum_sub D p₀ hD)
  have hsmall : ∀ᶠ p in 𝓝 p₀, entryNormSum (A p - A p₀) + entryNormSum (B p - B p₀) +
      entryNormSum (D p - D p₀) < 1 / (2 * (K : ℝ)) := by
    refine hsum.eventually (gt_mem_nhds ?_)
    have : (0 : ℝ) < 1 / (2 * (K : ℝ)) := by positivity
    simpa using this
  refine ⟨(a₁ + a₂) * (2 * K) * (e₁ + e₂), _, hsmall, fun p hp u v => ?_⟩
  have hp' : entryNormSum (A p - A p₀) + entryNormSum (B p - B p₀) + entryNormSum (D p - D p₀) <
      1 / (2 * (K : ℝ)) := hp
  set s := entryNormSum (A p - A p₀) + entryNormSum (B p - B p₀) + entryNormSum (D p - D p₀)
    with hs
  have hA₀ := entryNormSum_nonneg (A p - A p₀)
  have hB₀ := entryNormSum_nonneg (B p - B p₀)
  have hD₀ := entryNormSum_nonneg (D p - D p₀)
  set x : (J₁ → ℂ) × (J₂ → ℂ) := (u, v) with hx
  set y₁ := A p u - B p v with hy₁
  set y₂ := D p u with hy₂
  have hux : ‖u‖ ≤ ‖x‖ := norm_fst_le x
  have hvx : ‖v‖ ≤ ‖x‖ := norm_snd_le x
  have hx₀ : 0 ≤ ‖x‖ := norm_nonneg x
  have hdiff₁ : ‖(A p₀ u - B p₀ v) - y₁‖ ≤ s * ‖x‖ := by
    have e : (A p₀ u - B p₀ v) - y₁ = (B p - B p₀) v - (A p - A p₀) u := by
      simp only [hy₁, LinearMap.sub_apply]
      abel
    rw [e]
    calc ‖(B p - B p₀) v - (A p - A p₀) u‖ ≤ ‖(B p - B p₀) v‖ + ‖(A p - A p₀) u‖ :=
          norm_sub_le _ _
      _ ≤ entryNormSum (B p - B p₀) * ‖v‖ + entryNormSum (A p - A p₀) * ‖u‖ :=
        add_le_add (norm_apply_le_entryNormSum _ _) (norm_apply_le_entryNormSum _ _)
      _ ≤ entryNormSum (B p - B p₀) * ‖x‖ + entryNormSum (A p - A p₀) * ‖x‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hvx hB₀) (mul_le_mul_of_nonneg_left hux hA₀)
      _ ≤ s * ‖x‖ := by
        rw [hs]
        nlinarith [mul_nonneg hD₀ hx₀]
  have hdiff₂ : ‖D p₀ u - y₂‖ ≤ s * ‖x‖ := by
    have e : D p₀ u - y₂ = -((D p - D p₀) u) := by
      simp only [hy₂, LinearMap.sub_apply]
      abel
    rw [e, norm_neg]
    calc ‖(D p - D p₀) u‖ ≤ entryNormSum (D p - D p₀) * ‖u‖ := norm_apply_le_entryNormSum _ _
      _ ≤ entryNormSum (D p - D p₀) * ‖x‖ := mul_le_mul_of_nonneg_left hux hD₀
      _ ≤ s * ‖x‖ := by
        rw [hs]
        nlinarith [mul_nonneg hA₀ hx₀, mul_nonneg hB₀ hx₀]
  have hy₁₀ : 0 ≤ ‖y₁‖ := norm_nonneg _
  have hy₂₀ : 0 ≤ ‖y₂‖ := norm_nonneg _
  have hs₀ : 0 ≤ s * ‖x‖ := mul_nonneg (by rw [hs]; positivity) hx₀
  have hF : ‖F₀ x‖ ≤ ‖y₁‖ + ‖y₂‖ + s * ‖x‖ := by
    rw [hx, hF₀, Prod.norm_def]
    refine max_le ?_ ?_
    · have h₁ : ‖A p₀ u - B p₀ v‖ ≤ ‖y₁‖ + ‖(A p₀ u - B p₀ v) - y₁‖ := by
        have := norm_add_le y₁ ((A p₀ u - B p₀ v) - y₁)
        rwa [add_sub_cancel] at this
      show ‖A p₀ u - B p₀ v‖ ≤ _
      linarith
    · have h₂ : ‖D p₀ u‖ ≤ ‖y₂‖ + ‖D p₀ u - y₂‖ := by
        have := norm_add_le y₂ (D p₀ u - y₂)
        rwa [add_sub_cancel] at this
      show ‖D p₀ u‖ ≤ _
      linarith
  have hKs : (K : ℝ) * s ≤ 1 / 2 := by
    have h₁ : (K : ℝ) * s < K * (1 / (2 * (K : ℝ))) := mul_lt_mul_of_pos_left hp' hK
    have h₂ : (K : ℝ) * (1 / (2 * (K : ℝ))) = 1 / 2 := by
      field_simp
    linarith
  have hmain : ‖x‖ ≤ 2 * K * (‖y₁‖ + ‖y₂‖) := by
    have h₁ := hlow x
    have h₂ : (K : ℝ) * ‖F₀ x‖ ≤ K * (‖y₁‖ + ‖y₂‖ + s * ‖x‖) :=
      mul_le_mul_of_nonneg_left hF hK.le
    have h₃ : (K : ℝ) * (s * ‖x‖) ≤ 1 / 2 * ‖x‖ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hKs hx₀
    nlinarith
  have hN₁ := wNorm_nonneg w₁ y₁
  have hN₂ := wNorm_nonneg w₂ y₂
  have hy : ‖y₁‖ + ‖y₂‖ ≤ (e₁ + e₂) * (wNorm w₁ y₁ + wNorm w₂ y₂) := by
    have h₁ := hε₁ y₁
    have h₂ := hε₂ y₂
    nlinarith [mul_nonneg he₁ hN₂, mul_nonneg he₂ hN₁]
  have hleft : wNorm w₁ u + wNorm w₂ v ≤ (a₁ + a₂) * ‖x‖ := by
    have h₁ := (hα₁ u).trans (mul_le_mul_of_nonneg_left hux ha₁)
    have h₂ := (hα₂ v).trans (mul_le_mul_of_nonneg_left hvx ha₂)
    linarith
  calc wNorm w₁ u + wNorm w₂ v ≤ (a₁ + a₂) * ‖x‖ := hleft
    _ ≤ (a₁ + a₂) * (2 * K * ((e₁ + e₂) * (wNorm w₁ y₁ + wNorm w₂ y₂))) := by
      refine mul_le_mul_of_nonneg_left (hmain.trans ?_) (add_nonneg ha₁ ha₂)
      exact mul_le_mul_of_nonneg_left hy (by positivity)
    _ = (a₁ + a₂) * (2 * K) * (e₁ + e₂) * (wNorm w₁ y₁ + wNorm w₂ y₂) := by ring
theorem quotWeight_one_pos {I : PeriodicData} (hI : IsPeriodic I) (c : I.UnitQuot) :
    0 < I.quotWeight 1 c := by apply _root_.YangMills.SharedProofs.p9241 <;> assumption
theorem saddle_kernel_trivial {A B : PeriodicData} [Finite A.UnitQuot] [Finite B.UnitQuot]
    (hA : ∀ c, 0 < A.quotWeight 1 c) (hB : ∀ c, 0 < B.quotWeight 1 c)
    {P Ξ K G : QuotHom A A} {Q : QuotHom A B} {Qt : QuotHom B A} {c c' : ℝ}
    (hc : 0 < c) (hc' : 0 < c')
    (hΞ : LoewnerLE ((c : ℂ) • (K + scalarQuotHom A 1)) Ξ)
    (hK : LoewnerLE (scalarQuotHom A 0) K)
    (hadj : IsAdjointQuotHom Q Qt)
    (hS : LoewnerLE (scalarQuotHom B c') (Q.comp (G.comp Qt)))
    (hP : ∀ u, Q u = 0 → P u = Ξ u) {t : ℂ} (ht : t ≠ 0) {u : A.UnitQuot → ℂ}
    {v : B.UnitQuot → ℂ} (h₁ : P u + t • Qt v = 0) (h₂ : Q u = 0) : u = 0 ∧ v = 0 := by
  let := Fintype.ofFinite A.UnitQuot
  let := Fintype.ofFinite B.UnitQuot
  have hPu : Ξ u = -(t • Qt v) := by
    rw [← hP u h₂]
    exact eq_neg_of_add_eq_zero_left h₁
  have huv : wInner (A.quotWeight 1) u (Qt v) = 0 := by
    rw [← conj_wInner, ← hadj u v, h₂, wInner_zero, map_zero]
  have huΞ : wInner (A.quotWeight 1) u (Ξ u) = 0 := by
    have e : Ξ u = (-t) • Qt v := by rw [hPu, neg_smul]
    rw [e, wInner_smul, huv, mul_zero]
  have hlow := hΞ.re_nonneg u
  have hKu := hK.re_nonneg u
  have e₁ : (Ξ - (c : ℂ) • (K + scalarQuotHom A 1)) u =
      Ξ u + (-(c : ℂ)) • (K u + u) := by
    simp [scalarQuotHom, sub_eq_add_neg]
    abel
  have e₂ : (K - scalarQuotHom A 0) u = K u := by
    simp [scalarQuotHom]
  rw [e₁, wInner_add, wInner_smul, wInner_add, huΞ, zero_add] at hlow
  rw [e₂] at hKu
  have hre : (wInner (A.quotWeight 1) u u).re ≤ 0 := by
    have e₃ : (-(c : ℂ) * (wInner (A.quotWeight 1) u (K u) +
        wInner (A.quotWeight 1) u u)).re =
        -c * ((wInner (A.quotWeight 1) u (K u)).re +
          (wInner (A.quotWeight 1) u u).re) := by
      rw [← Complex.ofReal_neg, Complex.re_ofReal_mul, Complex.add_re]
    rw [e₃] at hlow
    nlinarith
  have hu : u = 0 := eq_zero_of_re_wInner_self_nonpos hA hre
  refine ⟨hu, ?_⟩
  have hQt : Qt v = 0 := by
    have hP0 : P u = 0 := by rw [hu, map_zero]
    rw [hP0, zero_add] at h₁
    exact (smul_eq_zero.1 h₁).resolve_left ht
  have hup := hS.re_nonneg v
  have e₄ : (Q.comp (G.comp Qt) - scalarQuotHom B c') v = (-(c' : ℂ)) • v := by
    simp [scalarQuotHom, hQt]
  rw [e₄, wInner_smul, ← Complex.ofReal_neg, Complex.re_ofReal_mul] at hup
  refine eq_zero_of_re_wInner_self_nonpos hB ?_
  nlinarith
theorem l1NormVec_le_four_mul (v : Fin 4 → ℝ) :
    TorusMetric.l1NormVec v ≤ 4 * TorusMetric.euclidNormVec v := by
  have h : ∀ μ, |v μ| ≤ TorusMetric.euclidNormVec v := fun μ => by
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun ν => v ν ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
  simp only [TorusMetric.l1NormVec, Fin.sum_univ_four]
  linarith [h 0, h 1, h 2, h 3]
theorem symbolHom_entry_continuousAt (hSymbols : StripSymbols.Claim) {I I' : PeriodicData}
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ}
    (hT : IsPeriodicKernel I I' T) (hrate : IsDecayRate I I' T 4) (c' : I'.UnitQuot)
    (c : I.UnitQuot) :
    ContinuousAt (fun κ => linearMapEntry (symbolHom I I' T κ) c' c) 0 := by
  obtain ⟨-, C, hC₀, hC⟩ := hrate
  have hbound : ∀ ι' ι, ‖T ι' ι‖ ≤
      C * Real.exp (-1 * TorusMetric.l1NormVec (I'.pos ι' - I.pos ι)) := fun ι' ι => by
    refine (hC ι' ι).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₀.le)
    have := l1NormVec_le_four_mul (I'.pos ι' - I.pos ι)
    linarith
  obtain ⟨-, hO, he⟩ := ((hSymbols.2.1 I I' hI hI').1.decay 1 one_pos C T hT hbound).2
  have h0 : (0 : Fin 4 → ℂ) ∈ openStripInterior 1 := by
    rw [(hSymbols.1 1 one_pos).1]
    simp [openImStrip]
  have h₁ := (he (c', c)).2.1.continuousAt (hO.mem_nhds h0)
  exact ((continuous_apply (0 : Fin 1)).continuousAt).comp h₁
theorem wNorm_coarse_eq_pauliFamilyNorm (hSandwich : FreeSandwiches.SandwichFacts)
    {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (h0 : (0 : Fin 4 → ℂ) ∈ realDualPoints)
    [Fintype (colourEdges L k k).UnitQuot] (z : (colourEdges L k k).UnitQuot → ℂ) :
    wNorm ((colourEdges L k k).quotWeight 1) z =
      pauliFamilyNorm (PlaneWaveCalculus.topEdgeComponent L k z) := by
  have h := (hSandwich L hL k hk 0 h0).edge_norm z
  have hre := congrArg Complex.re h
  rw [Complex.ofReal_re] at hre
  have hre' : ∑ i, (colourEdges L k k).quotWeight 1 i * ‖z i‖ ^ 2 =
      ∑ a, ∑ μ, ‖FreeSandwiches.topEdgeCoeff L k z a μ‖ ^ 2 := by
    rw [← re_wInner_self]
    exact hre
  rw [wNorm_eq_sqrt, pauliFamilyNorm, hre', Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [pauliNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  rfl
theorem uniformBoundNearZero_proof (hCoercive : FreeCoercivity.FreeOperatorsCoercive)
    (hReal : FreeSymbolsAtRealPoints)
    (hFree : FreeOperators.FreeOperatorsArePeriodic)
    (hSandwich : FreeSandwiches.SandwichFacts)
    (hIndex : TowerIndexSets.Claim)
    (hSymbols : StripSymbols.Claim) : UniformBoundNearZero := by
  intro L hL k hk
  obtain ⟨cXi, hcXi, cY, hcY, cC, hcC, hc⟩ := hCoercive
  obtain ⟨hops, -, -, hreal⟩ := hc L hL k hk
  obtain ⟨-, hE0, -⟩ := hIndex L hL k 0 (Nat.zero_le k)
  obtain ⟨-, hEk, -⟩ := hIndex L hL k k le_rfl
  have : Finite (colourEdges L k 0).UnitQuot := hE0.finite_quot
  have : Finite (colourEdges L k k).UnitQuot := hEk.finite_quot
  let := Fintype.ofFinite (colourEdges L k 0).UnitQuot
  let := Fintype.ofFinite (colourEdges L k k).UnitQuot
  have h0 : (0 : Fin 4 → ℂ) ∈ realDualPoints := fun μ => by simp
  obtain ⟨hmaps, hranges⟩ := hFree.2 L hL k hk
  have hQop : FreeOperators.HasFiniteRangeEveryRate (colourEdges L k 0) (colourEdges L k k)
      (trivialRescaledOperators L k).Q := hmaps.edgeAverage.finite_range
  have hQtop : FreeOperators.HasFiniteRangeEveryRate (colourEdges L k k) (colourEdges L k 0)
      (trivialRescaledOperators L k).Qt := hranges.edgeAverage_transpose
  have hXop : FreeOperators.HasFiniteRangeEveryRate (colourEdges L k 0) (colourEdges L k 0)
      (trivialRescaledOperators L k).X := hranges.X
  have hinj : ∀ (u : (colourEdges L k 0).UnitQuot → ℂ) (v : (colourEdges L k k).UnitQuot → ℂ),
      symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X 0 u -
          symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt 0 v
            = 0 →
      symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q 0 u = 0 →
      u = 0 ∧ v = 0 := by
    intro u v h₁ h₂
    obtain ⟨-, hr⟩ := hreal 0 h0
    obtain ⟨hK, -, hadj, -, hQt, -⟩ := hReal L hL k hk 0 h0
    have fQ := hops.Q.2.2 0 (Set.mem_univ _)
    have fQt := hops.Qt.2.2 0 (Set.mem_univ _)
    have fXi := hops.Xi.2.2 0 (Set.mem_univ _)
    have facts : ∀ {I I' : PeriodicData}, IsPeriodic I → IsPeriodic I' →
        ∀ (T : I'.Carrier → I.Carrier → ℂ) (κ : Fin 4 → ℂ), IsPeriodicKernel I I' T →
          SymbolSummableAt I I' T κ → StripSymbols.PointwiseCalculus I I' T κ :=
      fun hI hI' T κ hT hf => (hSymbols.2.1 _ _ hI hI').2.1 T κ hT hf
    have FQt := facts hEk hE0 _ 0 hops.Qt.1 fQt
    have FXi := facts hE0 hE0 _ 0 hops.Xi.1 fXi
    obtain ⟨-, hper, hform, hcomp⟩ := FQt.comp (colourEdges L k 0) hE0 _ hops.Q.1 fQ
    obtain ⟨-, -, hmapX⟩ := FXi.linComb _ hper hform 1 (-1)
    have eX : StripSymbols.linCombKernel 1 (-1) (trivialRescaledOperators L k).Xi
        (compKernel (trivialRescaledOperators L k).Qt (trivialRescaledOperators L k).Q) =
          (trivialRescaledOperators L k).X := by
      funext a b
      simp [StripSymbols.linCombKernel, RescaledOperators.X, sub_eq_add_neg]
    have hmapX' := (congrArg
      (fun T => symbolHom (colourEdges L k 0) (colourEdges L k 0) T 0) eX).symm.trans hmapX
    have hP : ∀ u, symbolHom (colourEdges L k 0) (colourEdges L k k)
        (trivialRescaledOperators L k).Q 0 u = 0 →
        symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X 0 u =
          symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).Xi 0 u := by
      intro u hu
      rw [hmapX', hcomp]
      simp [hu]
    have hav := hr.edge_lower
    unfold edgeResolventConjugate at hav
    rw [hQt] at hav
    refine saddle_kernel_trivial (quotWeight_one_pos hE0) (quotWeight_one_pos hEk) hcXi.1 hcC.1
      hr.Xi_lower hK hadj hav hP (t := -1) (by norm_num) ?_ h₂
    rw [neg_one_smul, ← sub_eq_add_neg]
    exact h₁
  obtain ⟨C, N, hN, hC⟩ := saddle_bounded_below_near (quotWeight_one_pos hE0)
    (quotWeight_one_pos hEk)
    (fun p => symbolHom (colourEdges L k 0) (colourEdges L k 0) (trivialRescaledOperators L k).X p)
    (fun p => symbolHom (colourEdges L k k) (colourEdges L k 0) (trivialRescaledOperators L k).Qt p)
    (fun p => symbolHom (colourEdges L k 0) (colourEdges L k k) (trivialRescaledOperators L k).Q p) 0
    (symbolHom_entry_continuousAt hSymbols hE0 hE0 hXop.1 (hXop.2.2 4 (by norm_num)))
    (symbolHom_entry_continuousAt hSymbols hEk hE0 hQtop.1 (hQtop.2.2 4 (by norm_num)))
    (symbolHom_entry_continuousAt hSymbols hE0 hEk hQop.1 (hQop.2.2 4 (by norm_num))) hinj
  refine ⟨C, N, hN, fun p hp u v => ?_⟩
  have h := hC p hp u v
  rw [wNorm_coarse_eq_pauliFamilyNorm hSandwich hL hk h0,
    wNorm_coarse_eq_pauliFamilyNorm hSandwich hL hk h0] at h
  exact h
end YangMills.Construction.Tower.SaddleStability
end
