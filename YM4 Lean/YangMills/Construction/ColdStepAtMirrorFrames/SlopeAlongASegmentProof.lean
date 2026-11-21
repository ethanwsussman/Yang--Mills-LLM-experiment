import YangMills.Construction.ColdStepAtMirrorFrames.ChangeAlongASegment
import YangMills.Construction.ColdStepAtMirrorFrames.FaaDiBrunoAtAPoint
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeAlongASegment
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Calculus
theorem weightedNorm_nonneg {N : ℕ} {w : Fin N → ℝ} (hw : ∀ n, 0 ≤ w n) (x : Fin N → ℝ) : 0 ≤ weightedNorm w x :=
  Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (hw n)
theorem weightedNorm_add_le {N : ℕ} {w : Fin N → ℝ} (hw : ∀ n, 0 ≤ w n) (x y : Fin N → ℝ) :
    weightedNorm w (x + y) ≤ weightedNorm w x + weightedNorm w y := by
  unfold weightedNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (hw n)
theorem weightedNorm_smul {N : ℕ} (w : Fin N → ℝ) (c : ℝ) (x : Fin N → ℝ) :
    weightedNorm w (c • x) = |c| * weightedNorm w x := by
  unfold weightedNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  ring
theorem abs_multilinear_le_prod_weightedNorm {N j : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin N → ℝ) ℝ) (K : ℝ)
    (w : Fin N → ℝ) (hw : ∀ n, 0 ≤ w n) (hK : 0 ≤ K)
    (hT : ∀ r : Fin j → Fin N, |T (fun i => Pi.single (r i) 1)| ≤ K * ∏ i, w (r i))
    (ξ : Fin j → Fin N → ℝ) : |T ξ| ≤ K * ∏ i, weightedNorm w (ξ i) := by
  classical
  have hx : ξ = fun i => ∑ n, (ξ i n) • (Pi.single n (1 : ℝ) : Fin N → ℝ) := by
    funext i l
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [T.map_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold weightedNorm
  rw [Finset.prod_univ_sum, Finset.mul_sum]
  simp only [Fintype.piFinset_univ]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [T.map_smul_univ, smul_eq_mul, abs_mul, Finset.abs_prod, Finset.prod_mul_distrib]
  have h1 := hT r
  have h2 : 0 ≤ ∏ i, |ξ i (r i)| := Finset.prod_nonneg fun i _ => abs_nonneg _
  calc (∏ i, |ξ i (r i)|) * |T (fun i => Pi.single (r i) 1)| ≤ (∏ i, |ξ i (r i)|) * (K * ∏ i, w (r i)) :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = _ := by ring
theorem iteratedDerivCompSegmentDiffBound_of_faaDiBrunoAt (hFaa : FaaDiBrunoAt) :
    IteratedDerivCompSegmentDiffBound := by
  classical
  intro N k g P D wt K C₁ ω s Gt B hw hP0 hPa hDa hga hK hNP hND hD0 hB hG hK0 hC₁ hω0 hω1 hs
  have hPc : ∀ n : ℕ, ContDiffAt ℝ n P 0 := fun n => hPa.contDiffAt
  have hDc : ∀ n : ℕ, ContDiffAt ℝ n D 0 := fun n => hDa.contDiffAt
  have hform : ∀ θ ∈ Set.Icc (0 : ℝ) 1, iteratedFDeriv ℝ k (g ∘ fun τ => P τ + θ • D τ) 0 (fun l => Pi.single l 1) =
      ∑ c : OrderedFinpartition k, iteratedFDeriv ℝ c.length g (θ • D 0) (fun i =>
        iteratedFDeriv ℝ (c.partSize i) P 0 (fun l => Pi.single (c.emb i l) 1) +
          θ • iteratedFDeriv ℝ (c.partSize i) D 0 (fun l => Pi.single (c.emb i l) 1)) := by
    intro θ hθ
    have e0 : P 0 + θ • D 0 = θ • D 0 := by simp [hP0]
    have h := hFaa _ _ _ g (fun τ => P τ + θ • D τ) k 0 (by
        change ContDiffAt ℝ k g (P 0 + θ • D 0)
        rw [e0]
        exact (hga θ hθ).contDiffAt)
      ((hPc k).add ((hDc k).const_smul θ)) (fun l => Pi.single l 1)
    rw [h]
    refine Finset.sum_congr rfl fun c _ => ?_
    change iteratedFDeriv ℝ c.length g (P 0 + θ • D 0) _ = _
    rw [e0]
    congr 1
    funext i
    have e1 : iteratedFDeriv ℝ (c.partSize i) (fun τ => P τ + θ • D τ) 0 =
        iteratedFDeriv ℝ (c.partSize i) P 0 + θ • iteratedFDeriv ℝ (c.partSize i) D 0 := by
      have h1 : ContDiffAt ℝ (c.partSize i) (fun τ => θ • D τ) 0 := (hDc _).const_smul θ
      have e2 : (fun τ => P τ + θ • D τ) = P + fun τ => θ • D τ := rfl
      rw [e2, iteratedFDeriv_add_apply (hPc _) h1]
      have e3 : (fun τ => θ • D τ) = θ • D := rfl
      rw [e3, iteratedFDeriv_const_smul_apply (hDc _)]
    rw [e1]
    rfl
  have hper : ∀ c : OrderedFinpartition k,
      |iteratedFDeriv ℝ c.length g (s • D 0) (fun i =>
          iteratedFDeriv ℝ (c.partSize i) P 0 (fun l => Pi.single (c.emb i l) 1) +
            s • iteratedFDeriv ℝ (c.partSize i) D 0 (fun l => Pi.single (c.emb i l) 1)) -
        iteratedFDeriv ℝ c.length g ((0 : ℝ) • D 0) (fun i =>
          iteratedFDeriv ℝ (c.partSize i) P 0 (fun l => Pi.single (c.emb i l) 1) +
            (0 : ℝ) • iteratedFDeriv ℝ (c.partSize i) D 0 (fun l => Pi.single (c.emb i l) 1))| ≤
        2 ^ (k + 2) * K * (2 * C₁) ^ (k + 1) * ω * Gt := by
    intro c
    obtain ⟨x, hx⟩ : ∃ x : Fin c.length → Fin N → ℝ, x = fun i =>
        iteratedFDeriv ℝ (c.partSize i) P 0 (fun l => Pi.single (c.emb i l) 1) := ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : Fin c.length → Fin N → ℝ, y = fun i =>
        iteratedFDeriv ℝ (c.partSize i) D 0 (fun l => Pi.single (c.emb i l) 1) := ⟨_, rfl⟩
    have hxs : ∀ i, weightedNorm wt (x i) ≤ C₁ * B (Finset.univ.image (c.emb i)) := fun i => by
      rw [hx]
      exact hNP _ _ (c.partSize_pos i) (c.emb_strictMono i).injective
    have hys : ∀ i, weightedNorm wt (y i) ≤ C₁ * ω * B (Finset.univ.image (c.emb i)) := fun i => by
      rw [hy]
      exact hND _ _ (c.partSize_pos i) (c.emb_strictMono i).injective
    obtain ⟨b, hb⟩ : ∃ b : Fin c.length → ℝ, b = fun i => 2 * C₁ * B (Finset.univ.image (c.emb i)) := ⟨_, rfl⟩
    have hb0 : ∀ i, 0 ≤ b i := fun i => by
      rw [hb]
      have := (hB (Finset.univ.image (c.emb i))).1
      positivity
    have hs0 := hs.1
    have hs1 := hs.2
    have hBi : ∀ i, 0 ≤ C₁ * B (Finset.univ.image (c.emb i)) := fun i => by
      have := (hB (Finset.univ.image (c.emb i))).1
      positivity
    have hXs : ∀ i, weightedNorm wt (x i + s • y i) ≤ b i := by
      intro i
      refine (weightedNorm_add_le hw _ _).trans ?_
      rw [weightedNorm_smul, abs_of_nonneg hs0, hb]
      have h1 := hxs i
      have h2 := hys i
      have h3 : 0 ≤ weightedNorm wt (y i) := weightedNorm_nonneg hw _
      have h4 : s * weightedNorm wt (y i) ≤ weightedNorm wt (y i) := by nlinarith
      have h5 : C₁ * ω * B (Finset.univ.image (c.emb i)) ≤ C₁ * B (Finset.univ.image (c.emb i)) := by
        have := hBi i
        nlinarith
      simp only
      linarith
    have hxb : ∀ i, weightedNorm wt (x i) ≤ b i := by
      intro i
      have h1 := hxs i
      have h2 := hBi i
      rw [hb]
      simp only
      linarith
    have hyb : ∀ i, weightedNorm wt (s • y i) ≤ ω * b i := by
      intro i
      rw [weightedNorm_smul, abs_of_nonneg hs0, hb]
      have h2 := hys i
      have h3 : 0 ≤ weightedNorm wt (y i) := weightedNorm_nonneg hw _
      have h4 : s * weightedNorm wt (y i) ≤ weightedNorm wt (y i) := by nlinarith
      have h5 := hBi i
      simp only
      have h6 : 0 ≤ ω * (C₁ * B (Finset.univ.image (c.emb i))) := mul_nonneg hω0 h5
      nlinarith
    have hbprod : 0 ≤ ∏ i, b i := Finset.prod_nonneg fun i _ => hb0 i
    have hA : |iteratedFDeriv ℝ c.length g (s • D 0) (fun i => x i + s • y i) -
        iteratedFDeriv ℝ c.length g ((0 : ℝ) • D 0) (fun i => x i + s • y i)| ≤ K * (C₁ * ω) * ∏ i, b i := by
      obtain ⟨X, hXd⟩ : ∃ X : Fin c.length → Fin N → ℝ, X = fun i => x i + s • y i := ⟨_, rfl⟩
      rw [← hXd]
      have hder : ∀ θ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun θ : ℝ => iteratedFDeriv ℝ c.length g (θ • D 0) X)
          (iteratedFDeriv ℝ (c.length + 1) g (θ • D 0) (Fin.cons (D 0) X)) (Set.Icc 0 1) θ := by
        intro θ hθ
        have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ c.length g) (θ • D 0) :=
          ((hga θ hθ).contDiffAt (n := ((c.length + 1 : ℕ) : WithTop ℕ∞))).differentiableAt_iteratedFDeriv
            (by exact_mod_cast Nat.lt_succ_self _)
        have h1 : HasDerivAt (fun u : ℝ => u • D 0) (D 0) θ := by
          simpa using (hasDerivAt_id θ).smul_const (D 0)
        have h2 := hd.hasFDerivAt.comp_hasDerivAt θ h1
        have h3 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin c.length => Fin N → ℝ) ℝ X).hasFDerivAt.comp_hasDerivAt θ h2
        refine (h3.congr_deriv ?_).hasDerivWithinAt
        rw [iteratedFDeriv_succ_apply_left]
        simp [Fin.tail_def]
      have hbound : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (c.length + 1) g (θ • D 0) (Fin.cons (D 0) X)‖ ≤
          K * (C₁ * ω) * ∏ i, b i := by
        intro θ hθ
        have h1 := abs_multilinear_le_prod_weightedNorm (iteratedFDeriv ℝ (c.length + 1) g (θ • D 0)) K wt hw hK0
          (hK θ hθ _ (by omega) (by have := c.length_le; omega)) (Fin.cons (D 0) X)
        rw [Real.norm_eq_abs]
        refine h1.trans ?_
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [← mul_assoc]
        have h2 : ∏ i, weightedNorm wt (X i) ≤ ∏ i, b i :=
          Finset.prod_le_prod (fun i _ => weightedNorm_nonneg hw _) fun i _ => by
            rw [hXd]
            exact hXs i
        have h3 : 0 ≤ ∏ i, weightedNorm wt (X i) := Finset.prod_nonneg fun i _ => weightedNorm_nonneg hw _
        have h4 : K * weightedNorm wt (D 0) ≤ K * (C₁ * ω) := mul_le_mul_of_nonneg_left hD0 hK0
        exact mul_le_mul h4 h2 h3 (by positivity)
      have hmv := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
        (Set.left_mem_Icc.mpr zero_le_one) hs
      rw [Real.norm_eq_abs] at hmv
      refine hmv.trans ?_
      have h5 : ‖s - 0‖ ≤ 1 := by
        rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hs0]
        exact hs1
      have h6 : 0 ≤ K * (C₁ * ω) * ∏ i, b i := by positivity
      exact mul_le_of_le_one_right h6 h5
    have hBt : |iteratedFDeriv ℝ c.length g ((0 : ℝ) • D 0) (fun i => x i + s • y i) -
        iteratedFDeriv ℝ c.length g ((0 : ℝ) • D 0) x| ≤ 2 ^ c.length * (K * ω * ∏ i, b i) := by
      obtain ⟨T, hT⟩ : ∃ T, T = iteratedFDeriv ℝ c.length g ((0 : ℝ) • D 0) := ⟨_, rfl⟩
      rw [← hT]
      have e1 : (fun i => x i + s • y i) = x + fun i => s • y i := rfl
      rw [e1, T.map_add_univ, ← Finset.add_sum_erase _ _ (Finset.mem_univ (Finset.univ : Finset (Fin c.length)))]
      have e2 : (Finset.univ : Finset (Fin c.length)).piecewise x (fun i => s • y i) = x := by
        funext i
        simp
      rw [e2, add_sub_cancel_left]
      have hterm : ∀ S ∈ (Finset.univ : Finset (Finset (Fin c.length))).erase Finset.univ,
          |T (S.piecewise x fun i => s • y i)| ≤ K * ω * ∏ i, b i := by
        intro S hS
        obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∉ S := by
          by_contra hcon
          push Not at hcon
          apply (Finset.mem_erase.mp hS).1
          exact Finset.eq_univ_iff_forall.mpr hcon
        have hl1 : 1 ≤ c.length := by
          have := i₀.2
          omega
        have h1 := abs_multilinear_le_prod_weightedNorm T K wt hw hK0 (fun r => by
          rw [hT]
          exact hK 0 (Set.left_mem_Icc.mpr zero_le_one) _ hl1 (by have := c.length_le; omega) r)
          (S.piecewise x fun i => s • y i)
        refine h1.trans ?_
        rw [mul_assoc K]
        refine mul_le_mul_of_nonneg_left ?_ hK0
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀), ← Finset.mul_prod_erase _ b (Finset.mem_univ i₀), ← mul_assoc]
        have h2 : weightedNorm wt (S.piecewise x (fun i => s • y i) i₀) ≤ ω * b i₀ := by
          rw [Finset.piecewise_eq_of_notMem _ _ _ hi₀]
          exact hyb i₀
        have h3 : ∏ i ∈ Finset.univ.erase i₀, weightedNorm wt (S.piecewise x (fun i => s • y i) i) ≤
            ∏ i ∈ Finset.univ.erase i₀, b i := by
          refine Finset.prod_le_prod (fun i _ => weightedNorm_nonneg hw _) fun i _ => ?_
          by_cases hi : i ∈ S
          · rw [Finset.piecewise_eq_of_mem _ _ _ hi]
            exact hxb i
          · rw [Finset.piecewise_eq_of_notMem _ _ _ hi]
            refine (hyb i).trans ?_
            have := hb0 i
            nlinarith
        exact mul_le_mul h2 h3 (Finset.prod_nonneg fun i _ => weightedNorm_nonneg hw _)
          (mul_nonneg hω0 (hb0 i₀))
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (((Finset.univ : Finset (Finset (Fin c.length))).erase Finset.univ).card : ℝ) ≤ 2 ^ c.length := by
        have h1 : ((Finset.univ : Finset (Finset (Fin c.length))).erase Finset.univ).card ≤ 2 ^ c.length := by
          refine (Finset.card_le_card (Finset.erase_subset _ _)).trans ?_
          simp
        exact_mod_cast h1
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    have e0 : (fun i => iteratedFDeriv ℝ (c.partSize i) P 0 (fun l => Pi.single (c.emb i l) 1) +
        (0 : ℝ) • iteratedFDeriv ℝ (c.partSize i) D 0 (fun l => Pi.single (c.emb i l) 1)) = x := by
      funext i
      rw [hx]
      simp
    rw [e0]
    have e1 : (fun i => iteratedFDeriv ℝ (c.partSize i) P 0 (fun l => Pi.single (c.emb i l) 1) +
        s • iteratedFDeriv ℝ (c.partSize i) D 0 (fun l => Pi.single (c.emb i l) 1)) = fun i => x i + s • y i := by
      rw [hx, hy]
    rw [e1]
    have htri : ∀ p q r : ℝ, |p - r| ≤ |p - q| + |q - r| := fun p q r => abs_sub_le p q r
    refine (htri _ _ _).trans ((add_le_add hA hBt).trans ?_)
    have hprod : ∏ i, b i = (2 * C₁) ^ c.length * ∏ i, B (Finset.univ.image (c.emb i)) := by
      rw [hb, Finset.prod_mul_distrib]
      simp
    have hBp0 : 0 ≤ ∏ i, B (Finset.univ.image (c.emb i)) := Finset.prod_nonneg fun i _ => (hB _).1
    have hBp := hG c
    have hl := c.length_le
    have hC2 : (1 : ℝ) ≤ 2 * C₁ := by linarith
    have hp1 : (2 * C₁) ^ c.length * (2 * C₁) ≤ (2 * C₁) ^ (k + 1) := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hC2 (by omega)
    have hp2 : (2 : ℝ) ^ c.length ≤ 2 ^ (k + 2) / 2 := by
      have : (2 : ℝ) ^ (k + 2) / 2 = 2 ^ (k + 1) := by
        rw [pow_succ 2 (k + 1)]
        ring
      rw [this]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hpow0 : (0 : ℝ) < (2 * C₁) ^ c.length := by positivity
    have h2l : (1 : ℝ) ≤ 2 ^ c.length := one_le_pow₀ (by norm_num)
    rw [hprod]
    have hq : K * (C₁ * ω) * ((2 * C₁) ^ c.length * ∏ i, B (Finset.univ.image (c.emb i))) +
        2 ^ c.length * (K * ω * ((2 * C₁) ^ c.length * ∏ i, B (Finset.univ.image (c.emb i)))) =
        K * ω * ((2 * C₁) ^ c.length * (C₁ + 2 ^ c.length)) * ∏ i, B (Finset.univ.image (c.emb i)) := by ring
    rw [hq]
    have hr : (2 * C₁) ^ c.length * (C₁ + 2 ^ c.length) ≤ 2 ^ (k + 2) * (2 * C₁) ^ (k + 1) := by
      have h1 : C₁ + 2 ^ c.length ≤ (2 * C₁) * 2 ^ c.length := by nlinarith
      calc (2 * C₁) ^ c.length * (C₁ + 2 ^ c.length)
          ≤ (2 * C₁) ^ c.length * ((2 * C₁) * 2 ^ c.length) := mul_le_mul_of_nonneg_left h1 hpow0.le
        _ = ((2 * C₁) ^ c.length * (2 * C₁)) * 2 ^ c.length := by ring
        _ ≤ (2 * C₁) ^ (k + 1) * (2 ^ (k + 2) / 2) := mul_le_mul hp1 hp2 (by positivity) (by positivity)
        _ ≤ 2 ^ (k + 2) * (2 * C₁) ^ (k + 1) := by
            have h3 : (0 : ℝ) < 2 ^ (k + 2) * (2 * C₁) ^ (k + 1) := by positivity
            nlinarith
    have hKω : 0 ≤ K * ω := mul_nonneg hK0 hω0
    calc K * ω * ((2 * C₁) ^ c.length * (C₁ + 2 ^ c.length)) * ∏ i, B (Finset.univ.image (c.emb i))
        ≤ K * ω * (2 ^ (k + 2) * (2 * C₁) ^ (k + 1)) * Gt := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hr hKω) hBp hBp0 (by positivity)
      _ = _ := by ring
  have h0 := hform 0 (Set.left_mem_Icc.mpr zero_le_one)
  have e0 : (fun τ => P τ + (0 : ℝ) • D τ) = P := by
    funext τ
    simp
  rw [e0] at h0
  rw [hform s hs, h0, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun c _ => hper c).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  apply le_of_eq
  unfold segmentConstant
  ring
theorem iteratedDerivAlongSegmentBound_of_faaDiBrunoAt (hFaa : FaaDiBrunoAt) : IteratedDerivAlongSegmentBound := by
  classical
  intro N k A v P D wt K C₁ ω s Gt B hw hP0 hPa hDa hAa hK hH0 hNP hND hD0 hB hG hK0 hC₁ hω0 hω1 hs
  obtain ⟨g, hg⟩ : ∃ g : (Fin N → ℝ) → ℝ, g = fun σ => fderiv ℝ A σ v := ⟨_, rfl⟩
  rw [← hg] at hK hH0 ⊢
  have hga : ∀ θ ∈ Set.Icc (0 : ℝ) 1, AnalyticAt ℝ g (θ • D 0) := by
    intro θ hθ
    rw [hg]
    have h1 := (hAa θ hθ).fderiv
    have h2 : AnalyticAt ℝ (fun M : (Fin N → ℝ) →L[ℝ] ℝ => M v) (fderiv ℝ A (θ • D 0)) :=
      (ContinuousLinearMap.apply ℝ ℝ v).analyticAt _
    exact h2.comp h1
  have h := iteratedDerivCompSegmentDiffBound_of_faaDiBrunoAt hFaa
    N k g P D wt K C₁ ω s Gt B hw hP0 hPa hDa hga hK hNP hND hD0 hB hG hK0 hC₁ hω0 hω1 hs
  rw [hH0, sub_zero] at h
  exact h

end YangMills.Construction.Calculus
end
