import YangMills.Construction.PeriodicOperators.SchurTestOnWeightedFunctions
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SchurTest
theorem sq_tsum_mul_le_weighted {J : Type} (t g : J → ℝ) (ht0 : ∀ i, 0 ≤ t i) (hg0 : ∀ i, 0 ≤ g i)
    (ht : Summable t) (hq : Summable fun i => t i * g i ^ 2) :
    Summable (fun i => t i * g i) ∧
      (∑' i, t i * g i) ^ 2 ≤ (∑' i, t i) * ∑' i, t i * g i ^ 2 := by
  have hq0 : ∀ i, 0 ≤ t i * g i ^ 2 := fun i => mul_nonneg (ht0 i) (sq_nonneg _)
  have hX : 0 ≤ (∑' i, t i) * ∑' i, t i * g i ^ 2 :=
    mul_nonneg (tsum_nonneg ht0) (tsum_nonneg hq0)
  have hbound : ∀ s : Finset J, ∑ i ∈ s, t i * g i ≤
      Real.sqrt ((∑' i, t i) * ∑' i, t i * g i ^ 2) := by
    intro s
    apply Real.le_sqrt_of_sq_le
    have h1 := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (r := fun i => t i * g i) (f := t)
      (g := fun i => t i * g i ^ 2) (fun i _ => ht0 i) (fun i _ => hq0 i)
      (fun i _ => le_of_eq (by ring))
    exact h1.trans (mul_le_mul (ht.sum_le_tsum s fun i _ => ht0 i)
      (hq.sum_le_tsum s fun i _ => hq0 i) (Finset.sum_nonneg fun i _ => hq0 i)
      (tsum_nonneg ht0))
  have hp0 : ∀ i, 0 ≤ t i * g i := fun i => mul_nonneg (ht0 i) (hg0 i)
  have hs : Summable fun i => t i * g i := summable_of_sum_le hp0 hbound
  refine ⟨hs, ?_⟩
  have h2 := hs.tsum_le_of_sum_le hbound
  calc (∑' i, t i * g i) ^ 2
      ≤ Real.sqrt ((∑' i, t i) * ∑' i, t i * g i ^ 2) ^ 2 :=
        pow_le_pow_left₀ (tsum_nonneg hp0) h2 2
    _ = (∑' i, t i) * ∑' i, t i * g i ^ 2 := Real.sq_sqrt hX
theorem applyKernel_sq_bound {J J' : Type} (T : J' → J → ℂ) (f : J → ℂ) (A B : ℝ) (hA : 0 ≤ A)
    (hrow : ∀ j, Summable (fun i => ‖T j i‖) ∧ ∑' i, ‖T j i‖ ≤ A)
    (hcol : ∀ i, Summable (fun j => ‖T j i‖) ∧ ∑' j, ‖T j i‖ ≤ B)
    (hf : Summable fun i => ‖f i‖ ^ 2) :
    (∀ j, ApplySummableAt T f j) ∧ Summable (fun j => ‖applyKernel T f j‖ ^ 2) ∧
      ∑' j, ‖applyKernel T f j‖ ^ 2 ≤ A * (B * ∑' i, ‖f i‖ ^ 2) := by
  have hq0 : ∀ j i, 0 ≤ ‖T j i‖ * ‖f i‖ ^ 2 := fun j i =>
    mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hq : ∀ j, Summable fun i => ‖T j i‖ * ‖f i‖ ^ 2 := fun j =>
    Summable.of_nonneg_of_le (hq0 j)
      (fun i => mul_le_mul_of_nonneg_left (hf.le_tsum i fun _ _ => sq_nonneg _) (norm_nonneg _))
      ((hrow j).1.mul_right _)
  have hcs := fun j => sq_tsum_mul_le_weighted (fun i => ‖T j i‖) (fun i => ‖f i‖)
    (fun i => norm_nonneg _) (fun i => norm_nonneg _) (hrow j).1 (hq j)
  have hnorm : ∀ j i, ‖T j i * f i‖ = ‖T j i‖ * ‖f i‖ := fun j i => norm_mul _ _
  have hformed : ∀ j, ApplySummableAt T f j := fun j => by
    unfold ApplySummableAt
    simp only [hnorm]
    exact (hcs j).1
  have hpt : ∀ j, ‖applyKernel T f j‖ ^ 2 ≤ A * ∑' i, ‖T j i‖ * ‖f i‖ ^ 2 := fun j => by
    have h1 : ‖applyKernel T f j‖ ≤ ∑' i, ‖T j i‖ * ‖f i‖ := by
      have := norm_tsum_le_tsum_norm (hformed j)
      simpa only [hnorm, applyKernel] using this
    calc ‖applyKernel T f j‖ ^ 2 ≤ (∑' i, ‖T j i‖ * ‖f i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑' i, ‖T j i‖) * ∑' i, ‖T j i‖ * ‖f i‖ ^ 2 := (hcs j).2
      _ ≤ A * ∑' i, ‖T j i‖ * ‖f i‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hrow j).2 (tsum_nonneg (hq0 j))
  have hfin : ∀ s : Finset J', ∑ j ∈ s, ∑' i, ‖T j i‖ * ‖f i‖ ^ 2 ≤ B * ∑' i, ‖f i‖ ^ 2 := by
    intro s
    rw [← Summable.tsum_finsetSum fun j _ => hq j, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun i => ?_) (summable_sum fun j _ => hq j) (hf.mul_left B)
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right
      (((hcol i).1.sum_le_tsum s fun _ _ => norm_nonneg _).trans (hcol i).2) (sq_nonneg _)
  have hsq : ∀ s : Finset J', ∑ j ∈ s, ‖applyKernel T f j‖ ^ 2 ≤
      A * (B * ∑' i, ‖f i‖ ^ 2) := fun s =>
    calc ∑ j ∈ s, ‖applyKernel T f j‖ ^ 2
        ≤ ∑ j ∈ s, A * ∑' i, ‖T j i‖ * ‖f i‖ ^ 2 := Finset.sum_le_sum fun j _ => hpt j
      _ = A * ∑ j ∈ s, ∑' i, ‖T j i‖ * ‖f i‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ A * (B * ∑' i, ‖f i‖ ^ 2) := mul_le_mul_of_nonneg_left (hfin s) hA
  have hsum : Summable fun j => ‖applyKernel T f j‖ ^ 2 :=
    summable_of_sum_le (fun _ => sq_nonneg _) hsq
  exact ⟨hformed, hsum, hsum.tsum_le_of_sum_le hsq⟩
theorem normSummable_const_iff {J : Type} {w : J → ℝ} {a : ℝ} (ha : 0 < a) (hw : ∀ i, w i = a)
    (f : J → ℂ) : NormSummable w f ↔ Summable fun i => ‖f i‖ ^ 2 := by
  unfold NormSummable
  have h : ∀ i, |w i * ‖f i‖ ^ 2| = a * ‖f i‖ ^ 2 := fun i => by
    rw [hw, abs_of_nonneg (mul_nonneg ha.le (sq_nonneg _))]
  simp only [h]
  exact summable_mul_left_iff ha.ne'
theorem wNorm_const {J : Type} {w : J → ℝ} {a : ℝ} (hw : ∀ i, w i = a) (f : J → ℂ) :
    wNorm w f = Real.sqrt (a * ∑' i, ‖f i‖ ^ 2) := by
  unfold wNorm
  simp only [hw, tsum_mul_left]
theorem bound_of_const_weights {J J' : Type} (T : J' → J → ℂ) (w : J → ℝ) (w' : J' → ℝ)
    (a a' A B c : ℝ)
    (ha : 0 < a) (ha' : 0 < a') (hc : 0 ≤ c) (hw : ∀ i, w i = a) (hw' : ∀ j, w' j = a')
    (hrow : ∀ j, Summable (fun i => ‖T j i‖) ∧ ∑' i, ‖T j i‖ ≤ A)
    (hcol : ∀ i, Summable (fun j => ‖T j i‖) ∧ ∑' j, ‖T j i‖ ≤ B)
    (habc : a' * (A * B) ≤ c ^ 2 * a) (f : J → ℂ) (hf : NormSummable w f) :
    (∀ j, ApplySummableAt T f j) ∧ NormSummable w' (applyKernel T f) ∧
      (wNorm w f ≤ 1 → wNorm w' (applyKernel T f) ≤ c) := by
  rcases isEmpty_or_nonempty J' with hJ' | ⟨⟨j₀⟩⟩
  · refine ⟨fun j => isEmptyElim j, ?_, fun _ => ?_⟩
    · rw [normSummable_const_iff ha' hw']
      exact summable_empty
    · rw [wNorm_const hw', tsum_empty, mul_zero, Real.sqrt_zero]
      exact hc
  have hA : 0 ≤ A := (tsum_nonneg fun _ => norm_nonneg _).trans (hrow j₀).2
  have hf' := (normSummable_const_iff ha hw f).1 hf
  obtain ⟨hformed, hsum, hle⟩ := applyKernel_sq_bound T f A B hA hrow hcol hf'
  refine ⟨hformed, (normSummable_const_iff ha' hw' _).2 hsum, fun h1 => ?_⟩
  rw [wNorm_const hw] at h1
  rw [wNorm_const hw']
  have hS : 0 ≤ ∑' i, ‖f i‖ ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have haS : 0 ≤ a * ∑' i, ‖f i‖ ^ 2 := mul_nonneg ha.le hS
  have haS1 : a * ∑' i, ‖f i‖ ^ 2 ≤ 1 := by
    rw [← Real.sq_sqrt haS]
    exact pow_le_one₀ (Real.sqrt_nonneg _) h1
  refine Real.sqrt_le_iff.2 ⟨hc, ?_⟩
  calc a' * ∑' j, ‖applyKernel T f j‖ ^ 2
      ≤ a' * (A * (B * ∑' i, ‖f i‖ ^ 2)) := mul_le_mul_of_nonneg_left hle ha'.le
    _ = (a' * (A * B)) * ∑' i, ‖f i‖ ^ 2 := by ring
    _ ≤ (c ^ 2 * a) * ∑' i, ‖f i‖ ^ 2 := mul_le_mul_of_nonneg_right habc hS
    _ = c ^ 2 * (a * ∑' i, ‖f i‖ ^ 2) := by ring
    _ ≤ c ^ 2 * 1 := mul_le_mul_of_nonneg_left haS1 (sq_nonneg _)
    _ = c ^ 2 := mul_one _
theorem constantWeights_holds : ConstantWeights := by
  intro J J' T w w' a a' A B c ha ha' hc hw hw' hrow hcol habc
  have key := bound_of_const_weights T w w' a a' A B c ha ha' hc hw hw' hrow hcol habc
  refine ⟨fun f hf => ⟨(key f hf).1, (key f hf).2.1⟩, fun E => ⟨fun f hf => (key f hf.2.1).2.1, ?_⟩⟩
  refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ((key f hf.2.1).2.2 hf.2.2)
theorem summable_of_single_colour {σ : Type} (F : Fin 3 × σ → ℝ) (b : Fin 3) (n : σ → ℝ) (A : ℝ)
    (hF0 : ∀ p, 0 ≤ F p) (hother : ∀ b' x, b' ≠ b → F (b', x) = 0) (hle : ∀ x, F (b, x) ≤ n x)
    (hn : Summable n) (hA : ∑' x, n x ≤ A) : Summable F ∧ ∑' p, F p ≤ A := by
  have hi : Function.Injective fun x : σ => (b, x) := fun x y h => (Prod.ext_iff.1 h).2
  have hzero : ∀ p ∉ Set.range fun x : σ => (b, x), F p = 0 := by
    rintro ⟨b', x⟩ h
    exact hother b' x fun e => h ⟨x, by rw [e]⟩
  have hs : Summable fun x => F (b, x) := Summable.of_nonneg_of_le (fun x => hF0 _) hle hn
  refine ⟨(hi.summable_iff hzero).1 hs, ?_⟩
  have hsupp : Function.support F ⊆ Set.range fun x : σ => (b, x) := fun p h => by
    by_contra hp
    exact h (hzero p hp)
  rw [← hi.tsum_eq hsupp]
  exact (hs.tsum_le_tsum hle hn).trans hA
theorem diagonalInColour_holds : DiagonalInColour := by
  intro σ σ' T N w w' a a' A B c ha ha' hc hw hw' hdiag hN hrow hcol habc
  refine constantWeights_holds _ _ T w w' a a' A B c ha ha' hc hw hw' ?_ ?_ habc
  · rintro ⟨b', y⟩
    exact summable_of_single_colour (fun p => ‖T (b', y) p‖) b' (N y) A (fun _ => norm_nonneg _)
      (fun b x h => by simp [hdiag b b' y x h.symm]) (fun x => hN b' y x) (hrow y).1 (hrow y).2
  · rintro ⟨b, x⟩
    exact summable_of_single_colour (fun p => ‖T p (b, x)‖) b (fun y => N y x) B
      (fun _ => norm_nonneg _) (fun b' y h => by simp [hdiag b b' y x h]) (fun y => hN b y x)
      (hcol x).1 (hcol x).2
theorem schurTest_holds : Holds := ⟨constantWeights_holds, diagonalInColour_holds⟩
end YangMills.Construction.PeriodicOperators.SchurTest
end
