import YangMills.Construction.ColdChainAtEveryLevel.MixedDerivativesOfAComposite
import YangMills.Construction.ColdStepAtMirrorFrames.CompositesAtAPoint
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology
namespace YangMills.Construction.Calculus
theorem iteratedFDeriv_comp_continuousLinearMap_apply (j : ℕ) {A B E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [CompleteSpace B] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (L : A →L[ℝ] B)
    (f : B → E) (x : A) (hf : AnalyticAt ℝ f (L x)) (v : Fin j → A) :
    iteratedFDeriv ℝ j (f ∘ L) x v = iteratedFDeriv ℝ j f (L x) fun m => L (v m) := by
  have hc : ContDiffAt ℝ ω f (L x) := hf.contDiffAt
  obtain ⟨u, hu, hon⟩ := hc.contDiffOn (m := (j : WithTop ℕ∞)) le_top (by simp)
  obtain ⟨t, htu, hto, hxt⟩ := mem_nhds_iff.mp hu
  have hon' : ContDiffOn ℝ j f t := hon.mono htu
  have hpre : IsOpen (L ⁻¹' t) := hto.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hon' hto.uniqueDiffOn hpre.uniqueDiffOn
    (show x ∈ L ⁻¹' t from hxt) (i := j) le_rfl
  rw [iteratedFDerivWithin_of_isOpen j hpre (show x ∈ L ⁻¹' t from hxt),
    iteratedFDerivWithin_of_isOpen j hto hxt] at h
  rw [h]
  rfl
def zeroCoordCLM {k : ℕ} (l : Fin k) : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun m => if m = l then 0 else ContinuousLinearMap.proj m
theorem zeroCoordCLM_apply {k : ℕ} (l : Fin k) (σ : Fin k → ℝ) : zeroCoordCLM l σ = Function.update σ l 0 := by
  funext m
  by_cases h : m = l
  · subst h
    simp [zeroCoordCLM]
  · simp [zeroCoordCLM, h]
theorem iteratedFDeriv_eq_zero_of_update_invariant {k j : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : (Fin k → ℝ) → E) (l : Fin k) (v : Fin j → Fin k → ℝ) (m : Fin j) (hf : AnalyticAt ℝ f 0)
    (hinv : ∀ (σ : Fin k → ℝ) (s : ℝ), f (Function.update σ l s) = f σ) (hv : v m = Pi.single l 1) :
    iteratedFDeriv ℝ j f 0 v = 0 := by
  have e : f ∘ zeroCoordCLM l = f := funext fun σ => by
    simp only [Function.comp, zeroCoordCLM_apply, hinv]
  have h0 : zeroCoordCLM l (0 : Fin k → ℝ) = 0 := map_zero _
  have h := iteratedFDeriv_comp_continuousLinearMap_apply j (zeroCoordCLM l) f 0 (by rw [h0]; exact hf) v
  rw [e, h0] at h
  rw [h]
  refine ContinuousMultilinearMap.map_coord_zero _ m ?_
  rw [hv, zeroCoordCLM_apply]
  funext x
  by_cases hx : x = l
  · subst hx
    simp
  · simp [hx, Pi.single_eq_of_ne hx]
theorem norm_iteratedFDeriv_comp_apply_le (hFaa : Analytic.FaaDiBrunoAnalyticProperty) (j : ℕ) {A B W : Type} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [CompleteSpace A] [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] (G : B → W) (T : A → B) (x : A) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hT : AnalyticAt ℝ T x) (hG : AnalyticAt ℝ G (T x))
    (bG : ∀ p, p ≤ j → ‖iteratedFDeriv ℝ p G (T x)‖ ≤ C)
    (bT : ∀ s, 1 ≤ s → s ≤ j → ‖iteratedFDeriv ℝ s T x‖ ≤ D) (v : Fin j → A) (hv : ∀ l, ‖v l‖ ≤ 1) :
    ‖iteratedFDeriv ℝ j (G ∘ T) x v‖ ≤ (Fintype.card (OrderedFinpartition j) : ℝ) * C * (D + 1) ^ j := by
  rw [hFaa j A B W G T x hT hG v]
  refine (norm_sum_le _ _).trans ?_
  have term : ∀ c : OrderedFinpartition j,
      ‖iteratedFDeriv ℝ c.length G (T x) fun i => iteratedFDeriv ℝ (c.partSize i) T x (v ∘ c.emb i)‖ ≤
        C * (D + 1) ^ j := by
    intro c
    refine ((iteratedFDeriv ℝ c.length G (T x)).le_opNorm _).trans ?_
    have h1 : ∀ i, ‖iteratedFDeriv ℝ (c.partSize i) T x (v ∘ c.emb i)‖ ≤ D + 1 := by
      intro i
      refine ((iteratedFDeriv ℝ (c.partSize i) T x).le_opNorm _).trans ?_
      have h2 : ∏ s, ‖(v ∘ c.emb i) s‖ ≤ 1 :=
        Finset.prod_le_one (fun _ _ => norm_nonneg _) fun s _ => hv _
      have h3 := bT (c.partSize i) (c.partSize_pos i) (c.partSize_le i)
      have h4 := norm_nonneg (iteratedFDeriv ℝ (c.partSize i) T x)
      nlinarith [norm_nonneg (iteratedFDeriv ℝ (c.partSize i) T x), h2,
        Finset.prod_nonneg (s := Finset.univ) fun (s : Fin (c.partSize i)) _ => norm_nonneg ((v ∘ c.emb i) s)]
    have h5 : ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) T x (v ∘ c.emb i)‖ ≤ (D + 1) ^ j := by
      calc ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) T x (v ∘ c.emb i)‖
          ≤ ∏ _i : Fin c.length, (D + 1) :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => h1 i
        _ = (D + 1) ^ c.length := by simp
        _ ≤ (D + 1) ^ j := pow_le_pow_right₀ (by linarith) c.length_le
    exact mul_le_mul (bG _ c.length_le) h5 (Finset.prod_nonneg fun _ _ => norm_nonneg _) hC
  calc ∑ c : OrderedFinpartition j, _ ≤ ∑ _c : OrderedFinpartition j, C * (D + 1) ^ j :=
        Finset.sum_le_sum fun c _ => term c
    _ = (Fintype.card (OrderedFinpartition j) : ℝ) * C * (D + 1) ^ j := by
        simp [Finset.card_univ, mul_assoc]
theorem abs_iteratedFDeriv_comp_single_le (hFaa : Analytic.FaaDiBrunoAnalyticProperty) (k n : ℕ) (G : (Fin n → ℝ) → ℝ)
    (T : (Fin k → ℝ) → Fin n → ℝ) (R : Fin k → Fin n → Prop) (D N : ℝ) (hk : 1 ≤ k) (hD : 0 ≤ D) (hN : 0 ≤ N)
    (hT : AnalyticAt ℝ T 0) (hT0 : T 0 = 0) (hG : AnalyticAt ℝ G 0)
    (bT : ∀ (j : ℕ) (v : Fin j → Fin k) (r : Fin n), 1 ≤ j → j ≤ k →
      |iteratedFDeriv ℝ j T 0 (fun m => Pi.single (v m) 1) r| ≤ D)
    (zT : ∀ (j : ℕ) (v : Fin j → Fin k) (r : Fin n) (m : Fin j), ¬ R (v m) r →
      iteratedFDeriv ℝ j T 0 (fun m => Pi.single (v m) 1) r = 0)
    (bG : ∀ (p : ℕ) (r : Fin p → Fin n), 1 ≤ p → p ≤ k → (∀ l, ∃ m, R l (r m)) →
      |iteratedFDeriv ℝ p G 0 (fun m => Pi.single (r m) 1)| ≤ N) :
    |iteratedFDeriv ℝ k (G ∘ T) 0 (fun l => Pi.single l 1)| ≤ compositeCoordBound k n D N := by
  classical
  have hG' : AnalyticAt ℝ G (T 0) := by rw [hT0]; exact hG
  rw [hFaa k (Fin k → ℝ) (Fin n → ℝ) ℝ G T 0 hT hG' _, hT0]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hD1 : (1 : ℝ) ≤ D + 1 := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have term : ∀ c : OrderedFinpartition k,
      |iteratedFDeriv ℝ c.length G 0 fun i =>
        iteratedFDeriv ℝ (c.partSize i) T 0 ((fun l => Pi.single l (1 : ℝ)) ∘ c.emb i)| ≤
        ((n : ℝ) + 1) ^ k * (D + 1) ^ k * N := by
    intro c
    set t : Fin c.length → Fin n → ℝ := fun i =>
      iteratedFDeriv ℝ (c.partSize i) T 0 ((fun l => Pi.single l (1 : ℝ)) ∘ c.emb i) with ht
    have hsum : ∀ i, t i = ∑ r, t i r • (Pi.single r (1 : ℝ) : Fin n → ℝ) := by
      intro i
      funext x
      simp [Finset.sum_apply, Pi.single_apply]
    have e1 : (iteratedFDeriv ℝ c.length G 0) t =
        ∑ r : Fin c.length → Fin n, (∏ i, t i (r i)) •
          (iteratedFDeriv ℝ c.length G 0) fun i => (Pi.single (r i) (1 : ℝ) : Fin n → ℝ) := by
      conv_lhs => rw [show t = fun i => ∑ r, t i r • (Pi.single r (1 : ℝ) : Fin n → ℝ) from funext hsum]
      rw [ContinuousMultilinearMap.map_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      exact ContinuousMultilinearMap.map_smul_univ _ _ _
    rw [e1]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have each : ∀ r : Fin c.length → Fin n,
        |(∏ i, t i (r i)) • (iteratedFDeriv ℝ c.length G 0) fun i => (Pi.single (r i) (1 : ℝ) : Fin n → ℝ)| ≤
          (D + 1) ^ k * N := by
      intro r
      rw [smul_eq_mul, abs_mul]
      by_cases hall : ∀ (i : Fin c.length) (s : Fin (c.partSize i)), R (c.emb i s) (r i)
      · have hcomp : ∀ l, ∃ m, R l (r m) := by
          intro l
          obtain ⟨m, s, hs⟩ := c.cover l
          exact ⟨m, hs ▸ hall m s⟩
        have b1 := bG c.length r (c.length_pos (by omega)) c.length_le hcomp
        have b2 : |∏ i, t i (r i)| ≤ (D + 1) ^ k := by
          rw [Finset.abs_prod]
          calc ∏ i, |t i (r i)| ≤ ∏ _i : Fin c.length, (D + 1) := by
                refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => ?_
                have := bT (c.partSize i) (c.emb i) (r i) (c.partSize_pos i) (c.partSize_le i)
                exact this.trans (by linarith)
            _ = (D + 1) ^ c.length := by simp
            _ ≤ (D + 1) ^ k := pow_le_pow_right₀ hD1 c.length_le
        exact mul_le_mul b2 b1 (abs_nonneg _) (by positivity)
      · push_neg at hall
        obtain ⟨i, s, hs⟩ := hall
        have z : t i (r i) = 0 := zT (c.partSize i) (c.emb i) (r i) s hs
        have : ∏ i, t i (r i) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) z
        rw [this]
        simp only [abs_zero, zero_mul]
        positivity
    calc ∑ r : Fin c.length → Fin n, _ ≤ ∑ _r : Fin c.length → Fin n, (D + 1) ^ k * N :=
          Finset.sum_le_sum fun r _ => each r
      _ = (n : ℝ) ^ c.length * ((D + 1) ^ k * N) := by
          simp [Finset.card_univ]
      _ ≤ ((n : ℝ) + 1) ^ k * ((D + 1) ^ k * N) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc (n : ℝ) ^ c.length ≤ ((n : ℝ) + 1) ^ c.length :=
                pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) _
            _ ≤ ((n : ℝ) + 1) ^ k := pow_le_pow_right₀ hn1 c.length_le
      _ = ((n : ℝ) + 1) ^ k * (D + 1) ^ k * N := by ring
  calc ∑ c : OrderedFinpartition k, _ ≤ ∑ _c : OrderedFinpartition k, ((n : ℝ) + 1) ^ k * (D + 1) ^ k * N :=
        Finset.sum_le_sum fun c _ => term c
    _ = compositeCoordBound k n D N := by
        simp [compositeCoordBound, Finset.card_univ]
        ring
theorem compositeDerivativesAtPoint_holds (hFaa : Analytic.FaaDiBrunoAnalyticProperty) : CompositeDerivativesAtPoint :=
  ⟨fun j A B E _ _ _ _ _ _ _ _ L f x hf v => iteratedFDeriv_comp_continuousLinearMap_apply j L f x hf v,
   fun k j E _ _ _ f l v m hf hinv hv => iteratedFDeriv_eq_zero_of_update_invariant f l v m hf hinv hv,
   fun j A B W _ _ _ _ _ _ _ _ _ G T x C D hC hD hT hG bG bT v hv =>
    norm_iteratedFDeriv_comp_apply_le hFaa j G T x C D hC hD hT hG bG bT v hv,
   fun k n G T R D N hk hD hN hT hT0 hG bT zT bG =>
    abs_iteratedFDeriv_comp_single_le hFaa k n G T R D N hk hD hN hT hT0 hG bT zT bG⟩
end YangMills.Construction.Calculus
end
