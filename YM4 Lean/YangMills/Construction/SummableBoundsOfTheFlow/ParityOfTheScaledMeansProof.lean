import YangMills.Construction.SummableBoundsOfTheFlow.BoundedDerivativesOnASetProof
import YangMills.Construction.SummableBoundsOfTheFlow.ParityOfTheScaledMeans
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansHaveTheirDerivatives
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames Set Filter
open YangMills.Construction.StepDensities
open scoped Topology
namespace ScaledVariables
private theorem abs_sub_limit_le_of_deriv_bound {g g' : ℝ → ℝ} {v l₁ B : ℝ} {n : ℕ} (hB : 0 ≤ B)
    (hd : ∀ l, 0 < l → l ≤ l₁ → HasDerivAt g (g' l) l) (hb : ∀ l, 0 < l → l ≤ l₁ → |g' l| ≤ B * l ^ n)
    (hl : Tendsto g (𝓝[>] 0) (𝓝 v)) : ∀ l, 0 < l → l ≤ l₁ → |g l - v| ≤ B * l ^ (n + 1) := by
  intro l h0 h1
  have key : ∀ s, 0 < s → s ≤ l → |g l - g s| ≤ B * l ^ n * (l - s) := by
    intro s hs hsl
    have hsub := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (f' := g') (C := B * l ^ n)
      (s := Icc s l) (x := s) (y := l)
      (fun x hx => (hd x (lt_of_lt_of_le hs hx.1) (hx.2.trans h1)).hasDerivWithinAt)
      (fun x hx => by
        have hx0 : 0 < x := lt_of_lt_of_le hs hx.1
        rw [Real.norm_eq_abs]
        refine (hb x hx0 (hx.2.trans h1)).trans ?_
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0.le hx.2 n) hB)
      (convex_Icc s l) (left_mem_Icc.2 hsl) (right_mem_Icc.2 hsl)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hsl)] at hsub
    exact hsub
  have ht : Tendsto (fun s => |g l - g s|) (𝓝[>] 0) (𝓝 |g l - v|) := (tendsto_const_nhds.sub hl).abs
  have hu : Tendsto (fun s : ℝ => B * l ^ n * (l - s)) (𝓝[>] 0) (𝓝 (B * l ^ n * (l - 0))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((continuous_const.mul (continuous_const.sub continuous_id)).tendsto 0)
  have hle := le_of_tendsto_of_tendsto ht hu (by
    filter_upwards [Ioc_mem_nhdsGT h0] with s hs using key s hs.1 hs.2)
  refine hle.trans (le_of_eq ?_)
  ring
abbrev _root_.YangMills.SharedProofs.p112515 := @abs_sub_limit_le_of_deriv_bound
private theorem hasDerivAt_iteratedDeriv_of_contDiffAt {g : ℝ → ℝ} {n : ℕ} {l : ℝ}
    (h : ContDiffAt ℝ (n + 1 : ℕ) g l) :
    HasDerivAt (iteratedDeriv n g) (iteratedDeriv (n + 1) g l) l := by apply _root_.YangMills.Construction.UniformDerivativeBounds.hasDerivAt_iteratedDeriv_of_contDiffAt <;> assumption
theorem scaledMeanParity_of_derivBounds (hD : scaledMeanDerivStatement) :
    scaledMeanParity := by
  refine EventuallyOrdered.mono hD ?_
  intro T hT hn cD e
  obtain ⟨l₀, C, hl₀, hC, g⟩ := cD e
  refine ⟨l₀, C, hl₀, hC, ?_⟩
  intro l₁ hl₁ hle t f F V Y law K Ob k c X hfam hF hV hlaw hK hob hX
  have D := g l₁ hl₁ hle t f F V Y law K Ob k c X hfam hF hV hlaw hK hob hX
  set B : ℝ := C * K * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c)) with hB
  have hB0 : 0 ≤ B := by positivity
  set G : ℝ → ℝ := fun l' =>
    bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l') V c X with hG
  have cont2 : k ≤ 3 → ∀ l, 0 < l → l ≤ l₁ → ContDiffAt ℝ (2 : ℕ) G l := by
    intro hk l h0 h1
    have h2 := D.contDiffAt hk l h0 h1
    split_ifs at h2 with h3
    · exact h2
    · exact h2.of_le (by norm_num)
  have cont3 : k ≤ 2 → ∀ l, 0 < l → l ≤ l₁ → ContDiffAt ℝ (3 : ℕ) G l := by
    intro hk l h0 h1
    have h2 := D.contDiffAt (by omega) l h0 h1
    rw [if_neg (by omega)] at h2
    exact h2
  have dG : k ≤ 3 → ∀ l, 0 < l → l ≤ l₁ → HasDerivAt G (deriv G l) l := by
    intro hk l h0 h1
    exact ((cont2 hk l h0 h1).differentiableAt (by norm_num)).hasDerivAt
  have d2 : k ≤ 3 → ∀ l, 0 < l → l ≤ l₁ → HasDerivAt (deriv G) (iteratedDeriv 2 G l) l := by
    intro hk l h0 h1
    have h2 := hasDerivAt_iteratedDeriv_of_contDiffAt (n := 1) (cont2 hk l h0 h1)
    rwa [iteratedDeriv_one] at h2
  have near : k ≤ 3 → ∀ l : ℝ, 0 < l → l ≤ l₁ →
      |G l - bondDeriv (observableGaussianMean T.a T.ρA T.lam f law Ob) V c X| ≤ B * l ^ 2 := by
    intro hk
    have b2 : ∀ l, 0 < l → l ≤ l₁ → |iteratedDeriv 2 G l| ≤ B * l ^ 0 := by
      intro l h0 h1
      simpa using D.iteratedDeriv_le 2 l (Or.inl ⟨hk, le_rfl⟩) h0 h1
    have b1 := abs_sub_limit_le_of_deriv_bound hB0 (d2 hk) b2 (D.tendsto_deriv_zero hk)
    have b1' : ∀ l, 0 < l → l ≤ l₁ → |deriv G l| ≤ B * l ^ 1 := by
      intro l h0 h1
      simpa using b1 l h0 h1
    exact abs_sub_limit_le_of_deriv_bound hB0 (dG hk) b1' (D.tendsto_gaussianMean hk)
  refine ⟨D.iteratedDeriv_le, D.tendsto_gaussianMean, D.tendsto_deriv_zero, ?_, ?_, ?_⟩
  · intro hk l h0 h1
    have := near hk l h0 h1
    calc _ ≤ B * l ^ 2 := this
      _ = _ := by rw [hB]; ring
  · intro hk
    have h1 : Tendsto (fun _ : ℝ => B) (𝓝[>] 0) (𝓝 B) := tendsto_const_nhds
    have h2 : |2 * bondDeriv (observableSecondOrderCoeff T.a T.ρA T.lam f law Ob) V c X| ≤ B := by
      refine le_of_tendsto_of_tendsto (D.tendsto_secondDeriv hk).abs h1 ?_
      filter_upwards [Ioc_mem_nhdsGT hl₁] with l hl
      exact D.iteratedDeriv_le 2 l (Or.inr ⟨hk, by norm_num⟩) hl.1 hl.2
    rw [abs_mul, abs_two] at h2
    have := abs_nonneg (bondDeriv (observableSecondOrderCoeff T.a T.ρA T.lam f law Ob) V c X)
    show _ ≤ B
    linarith
  · intro hk
    set q : ℝ := bondDeriv (observableSecondOrderCoeff T.a T.ρA T.lam f law Ob) V c X with hq
    have hk3 : k ≤ 3 := by omega
    have d3 : ∀ l, 0 < l → l ≤ l₁ → HasDerivAt (iteratedDeriv 2 G) (iteratedDeriv 3 G l) l :=
      fun l h0 h1 => hasDerivAt_iteratedDeriv_of_contDiffAt (n := 2) (cont3 hk l h0 h1)
    have b3 : ∀ l, 0 < l → l ≤ l₁ → |iteratedDeriv 3 G l| ≤ B * l ^ 0 := by
      intro l h0 h1
      simpa using D.iteratedDeriv_le 3 l (Or.inr ⟨hk, le_rfl⟩) h0 h1
    have s2 := abs_sub_limit_le_of_deriv_bound hB0 d3 b3 (D.tendsto_secondDeriv hk)
    have d1 : ∀ l, 0 < l → l ≤ l₁ → HasDerivAt (fun l => deriv G l - 2 * q * l)
        (iteratedDeriv 2 G l - 2 * q) l := by
      intro l h0 h1
      have h2 := (d2 hk3 l h0 h1).sub ((hasDerivAt_id l).const_mul (2 * q))
      exact h2.congr_deriv (by simp)
    have b2 : ∀ l, 0 < l → l ≤ l₁ → |iteratedDeriv 2 G l - 2 * q| ≤ B * l ^ 1 := by
      intro l h0 h1
      simpa using s2 l h0 h1
    have l1 : Tendsto (fun l => deriv G l - 2 * q * l) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun l : ℝ => 2 * q * l) (𝓝[>] 0) (𝓝 0) := by
        apply Tendsto.mono_left _ nhdsWithin_le_nhds
        have h2 : Tendsto (fun l : ℝ => 2 * q * l) (𝓝 0) (𝓝 (2 * q * 0)) :=
          (continuous_const.mul continuous_id : Continuous fun l : ℝ => 2 * q * l).tendsto 0
        rwa [mul_zero] at h2
      simpa using (D.tendsto_deriv_zero hk3).sub h1
    have s1 := abs_sub_limit_le_of_deriv_bound hB0 d1 b2 l1
    have d0 : ∀ l, 0 < l → l ≤ l₁ → HasDerivAt (fun l => G l - q * l ^ 2) (deriv G l - 2 * q * l) l := by
      intro l h0 h1
      have h2 := (dG hk3 l h0 h1).sub ((hasDerivAt_pow 2 l).const_mul q)
      refine h2.congr_deriv ?_
      simp
      ring
    have b1 : ∀ l, 0 < l → l ≤ l₁ → |deriv G l - 2 * q * l| ≤ B * l ^ 2 := by
      intro l h0 h1
      simpa using s1 l h0 h1
    have l0 : Tendsto (fun l => G l - q * l ^ 2) (𝓝[>] 0)
        (𝓝 (bondDeriv (observableGaussianMean T.a T.ρA T.lam f law Ob) V c X)) := by
      have h1 : Tendsto (fun l : ℝ => q * l ^ 2) (𝓝[>] 0) (𝓝 0) := by
        apply Tendsto.mono_left _ nhdsWithin_le_nhds
        have := (by fun_prop : Continuous fun l : ℝ => q * l ^ 2).tendsto 0
        simpa using this
      simpa using (D.tendsto_gaussianMean hk3).sub h1
    have s0 := abs_sub_limit_le_of_deriv_bound hB0 d0 b1 l0
    intro l h0 h1
    have := s0 l h0 h1
    calc _ = |G l - q * l ^ 2 - bondDeriv (observableGaussianMean T.a T.ρA T.lam f law Ob) V c X| := by
          congr 1
          simp only [hG]
          ring
      _ ≤ B * l ^ 3 := this
      _ = _ := by rw [hB]; ring
end ScaledVariables
end YangMills.Construction
end
