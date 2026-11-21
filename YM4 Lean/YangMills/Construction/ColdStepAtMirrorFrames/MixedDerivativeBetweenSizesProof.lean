import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeBetweenSizes
import YangMills.Construction.ColdStepAtMirrorFrames.MixedDerivativeBetweenSizes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace MultilinearLine
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem sum_signed_diagonal_eq_factorial_mul {j : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ)
    (hA : ∀ (σ : Equiv.Perm (Fin j)) (v : Fin j → E), A (v ∘ σ) = A v) (v : Fin j → E) :
    ∑ S : Finset (Fin j), (-1 : ℝ) ^ (j - S.card) * A (fun _ => ∑ l ∈ S, v l) =
      (j.factorial : ℝ) * A v := by
  classical
  have hexp : ∀ S : Finset (Fin j), A (fun _ => ∑ l ∈ S, v l) =
      ∑ f : Fin j → Fin j, (if ∀ i, f i ∈ S then A (v ∘ f) else 0) := by
    intro S
    have h := A.map_sum_finset (fun _ l => v l) (fun _ => S)
    rw [h]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext f
      simp [Fintype.mem_piFinset]
    · intro f _
      rfl
  simp only [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hf : ∀ f : Fin j → Fin j,
      ∑ S : Finset (Fin j), (-1 : ℝ) ^ (j - S.card) * (if ∀ i, f i ∈ S then A (v ∘ f) else 0) =
        if Function.Bijective f then A (v ∘ f) else 0 := by
    intro f
    set T := Finset.univ.image f with hT
    have e1 : ∀ S : Finset (Fin j), (∀ i, f i ∈ S) ↔ T ⊆ S := by
      intro S
      simp [hT, Finset.subset_iff]
    by_cases hb : Function.Bijective f
    · rw [if_pos hb]
      have hTu : T = Finset.univ := by
        ext x
        simp [hT, hb.2 x]
      rw [Finset.sum_eq_single Finset.univ]
      · simp
      · intro S _ hS
        rw [if_neg]
        · simp
        · intro hall
          apply hS
          have : T ⊆ S := (e1 S).mp hall
          rw [hTu] at this
          exact Finset.univ_subset_iff.mp this
      · simp
    · rw [if_neg hb]
      have hne : T ≠ Finset.univ := by
        intro h
        apply hb
        have hs : Function.Surjective f := by
          intro x
          have : x ∈ T := by rw [h]; exact Finset.mem_univ x
          simpa [hT] using this
        exact (Finite.injective_iff_surjective.mpr hs |>.bijective_of_finite)
      have hsum : ∑ S : Finset (Fin j), (if T ⊆ S then (-1 : ℝ) ^ (j - S.card) else 0) = 0 := by
        obtain ⟨x, hx⟩ : ∃ x, x ∉ T := by
          by_contra hc
          push Not at hc
          exact hne (Finset.eq_univ_iff_forall.mpr hc)
        apply Finset.sum_involution (fun S _ => if x ∈ S then S.erase x else insert x S)
        · intro S _
          by_cases hxS : x ∈ S
          · simp only [hxS, if_true]
            by_cases hTS : T ⊆ S
            · have h2 : T ⊆ S.erase x := fun y hy =>
                Finset.mem_erase.mpr ⟨fun e => hx (e ▸ hy), hTS hy⟩
              rw [if_pos hTS, if_pos h2, Finset.card_erase_of_mem hxS]
              have hc : S.card ≤ j := by simpa using Finset.card_le_univ S
              have hc0 : 0 < S.card := Finset.card_pos.mpr ⟨x, hxS⟩
              have e : j - (S.card - 1) = (j - S.card) + 1 := by omega
              rw [e, pow_succ]
              ring
            · have h2 : ¬ T ⊆ S.erase x := fun h => hTS (h.trans (Finset.erase_subset _ _))
              rw [if_neg hTS, if_neg h2, add_zero]
          · simp only [hxS, if_false]
            by_cases hTS : T ⊆ S
            · have h2 : T ⊆ insert x S := hTS.trans (Finset.subset_insert _ _)
              rw [if_pos hTS, if_pos h2, Finset.card_insert_of_notMem hxS]
              have hc : (insert x S).card ≤ j := by simpa using Finset.card_le_univ (insert x S)
              rw [Finset.card_insert_of_notMem hxS] at hc
              have e : j - S.card = (j - (S.card + 1)) + 1 := by omega
              rw [e, pow_succ]
              ring
            · have h2 : ¬ T ⊆ insert x S := by
                intro h
                apply hTS
                intro y hy
                have := h hy
                rcases Finset.mem_insert.mp this with e | e
                · exact absurd (e ▸ hy) hx
                · exact e
              rw [if_neg hTS, if_neg h2, add_zero]
        · intro S _ hne0 hfix
          by_cases hxS : x ∈ S
          · simp only [hxS, if_true] at hfix
            exact absurd (hfix ▸ Finset.mem_erase.mp (hfix.symm ▸ hxS)).1 (by simp)
          · simp only [hxS, if_false] at hfix
            exact hxS (hfix ▸ Finset.mem_insert_self x S)
        · intro S _
          by_cases hxS : x ∈ S
          · simp [hxS, Finset.insert_erase]
          · simp [hxS]
        · intro S _
          exact Finset.mem_univ _
      have : ∀ S : Finset (Fin j), (-1 : ℝ) ^ (j - S.card) * (if ∀ i, f i ∈ S then A (v ∘ f) else 0) =
          (if T ⊆ S then (-1 : ℝ) ^ (j - S.card) else 0) * A (v ∘ f) := by
        intro S
        by_cases h : T ⊆ S
        · rw [if_pos ((e1 S).mpr h), if_pos h]
        · rw [if_neg fun h2 => h ((e1 S).mp h2), if_neg h]
          simp
      simp only [this]
      rw [← Finset.sum_mul, hsum, zero_mul]
  simp only [hf]
  rw [← Finset.sum_filter]
  have hperm : ∑ f ∈ Finset.univ.filter (fun f : Fin j → Fin j => Function.Bijective f), A (v ∘ f) =
      ∑ σ : Equiv.Perm (Fin j), A (v ∘ σ) := by
    symm
    apply Finset.sum_bij (fun (σ : Equiv.Perm (Fin j)) _ => (⇑σ : Fin j → Fin j))
    · intro σ _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.bijective⟩
    · intro σ _ τ _ h
      exact Equiv.coe_fn_injective h
    · intro f hf
      have hb := (Finset.mem_filter.mp hf).2
      exact ⟨Equiv.ofBijective f hb, Finset.mem_univ _, rfl⟩
    · intro σ _
      rfl
  rw [hperm]
  simp only [hA]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
theorem hasDerivAt_iteratedFDeriv_along_line {u : E → ℝ} {p i : ℕ} (hu : ContDiff ℝ p u)
    (hi : i < p) (w : E) (s : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ i u (s • w) fun _ => w)
      (iteratedFDeriv ℝ (i + 1) u (s • w) fun _ => w) s := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ i u) :=
    hu.differentiable_iteratedFDeriv (by exact_mod_cast hi)
  have h1 : HasDerivAt (fun s : ℝ => s • w) w s := by
    simpa using (hasDerivAt_id s).smul_const w
  have h2 := ((hd (s • w)).hasFDerivAt).comp_hasDerivAt s h1
  have h3 := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => E) ℝ fun _ => w).hasFDerivAt).comp_hasDerivAt
    s h2
  refine HasDerivAt.congr_deriv h3 ?_
  rw [iteratedFDeriv_succ_apply_left]
  rfl
end MultilinearLine
open MultilinearLine in
theorem landauKolmogorovMultivariateAtZero_of_landauKolmogorovAtZero
    (hOne : LandauKolmogorovAtZero) :
    LandauKolmogorovMultivariateAtZero := by
  intro k p j hj
  obtain ⟨C₁, hC₁, hb⟩ := hOne p j hj
  refine ⟨2 ^ j * ((j : ℝ) + 1) ^ j * C₁, by positivity, ?_⟩
  intro u τ₀ M₀ Mp hτ hM hMp hu hsize hhigh hsym v hv
  set A := iteratedFDeriv ℝ j u 0 with hA
  set R : ℝ := M₀ / τ₀ ^ j + M₀ ^ (1 - (j : ℝ) / p) * Mp ^ ((j : ℝ) / p) with hR
  have hR0 : 0 ≤ R := by positivity
  have hline : ∀ w : Fin k → ℝ, ‖w‖ ≤ 1 → |A fun _ => w| ≤ C₁ * R := by
    intro w hw
    have hs : ∀ s : ℝ, |s| ≤ τ₀ → ‖s • w‖ ≤ τ₀ := by
      intro s h
      rw [norm_smul, Real.norm_eq_abs]
      calc |s| * ‖w‖ ≤ |s| * 1 := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
        _ ≤ τ₀ := by linarith
    have := hb (fun i s => iteratedFDeriv ℝ i u (s • w) fun _ => w) τ₀ M₀ Mp hτ hM hMp
      (fun i hi s _ => hasDerivAt_iteratedFDeriv_along_line hu hi w s)
      (fun s h => by
        simp only [iteratedFDeriv_zero_apply]
        exact hsize _ (hs s h))
      (fun s h => by
        have h2 := (iteratedFDeriv ℝ p u (s • w)).le_opNorm fun _ => w
        rw [Real.norm_eq_abs] at h2
        refine h2.trans ?_
        have h3 : ∏ _i : Fin p, ‖w‖ ≤ 1 := by
          apply Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => hw
        have h4 := hhigh _ (hs s h)
        calc ‖iteratedFDeriv ℝ p u (s • w)‖ * ∏ _i : Fin p, ‖w‖
            ≤ ‖iteratedFDeriv ℝ p u (s • w)‖ * 1 :=
              mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
          _ ≤ Mp := by linarith)
    simpa only [zero_smul] using this
  have hpol := sum_signed_diagonal_eq_factorial_mul A hsym v
  have hjf : (1 : ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hS : ∀ S : Finset (Fin j), |A fun _ => ∑ l ∈ S, v l| ≤ ((j : ℝ) + 1) ^ j * (C₁ * R) := by
    intro S
    set c : ℝ := ((j : ℝ) + 1) with hc
    have hc0 : 0 < c := by positivity
    set w : Fin k → ℝ := c⁻¹ • ∑ l ∈ S, v l with hw
    have hwn : ‖w‖ ≤ 1 := by
      rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc0), inv_mul_le_iff₀ hc0]
      calc ‖∑ l ∈ S, v l‖ ≤ ∑ l ∈ S, ‖v l‖ := norm_sum_le _ _
        _ ≤ ∑ _l ∈ S, (1 : ℝ) := Finset.sum_le_sum fun l _ => hv l
        _ = S.card := by simp
        _ ≤ c := by
          have : (S.card : ℝ) ≤ j := by
            have := Finset.card_le_univ S
            simp only [Fintype.card_fin] at this
            exact_mod_cast this
          simp only [hc]
          linarith
        _ = c * 1 := by ring
    have e : (fun _ : Fin j => ∑ l ∈ S, v l) = fun i => (fun _ : Fin j => c) i • (fun _ : Fin j => w) i := by
      funext i
      simp only [hw, smul_smul]
      rw [mul_inv_cancel₀ hc0.ne', one_smul]
    rw [e, ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, abs_mul]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (hline w hwn) (by positivity)
  have hsum : (j.factorial : ℝ) * |A v| ≤ 2 ^ j * (((j : ℝ) + 1) ^ j * (C₁ * R)) := by
    rw [← abs_of_pos (by positivity : (0 : ℝ) < j.factorial), ← abs_mul, ← hpol]
    calc |∑ S : Finset (Fin j), (-1 : ℝ) ^ (j - S.card) * A fun _ => ∑ l ∈ S, v l|
        ≤ ∑ S : Finset (Fin j), |(-1 : ℝ) ^ (j - S.card) * A fun _ => ∑ l ∈ S, v l| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _S : Finset (Fin j), ((j : ℝ) + 1) ^ j * (C₁ * R) := by
          apply Finset.sum_le_sum
          intro S _
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
          exact hS S
      _ = 2 ^ j * (((j : ℝ) + 1) ^ j * (C₁ * R)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
  have habs := abs_nonneg (A v)
  calc |A v| ≤ (j.factorial : ℝ) * |A v| := by nlinarith
    _ ≤ 2 ^ j * (((j : ℝ) + 1) ^ j * (C₁ * R)) := hsum
    _ = 2 ^ j * ((j : ℝ) + 1) ^ j * C₁ * R := by ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
