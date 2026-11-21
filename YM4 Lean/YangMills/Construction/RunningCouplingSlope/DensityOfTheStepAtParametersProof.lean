import YangMills.Construction.ClusterExpansionOfAStep.NumbersOfTheStepAreFinite
import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfAnExpansionProof
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepAtParameters
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsAnalyticAtParameters
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsInvariantAtParameters
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepOnTwoToriAtParameters
import YangMills.Construction.RunningCouplingSlope.DerivativesOfTheDensityOfTheStepDecayAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps RenormalizationStepParameters ReferenceDensity StepDensity
namespace RunningCouplingSlope
private theorem isCold_mono {n : ℕ} {s s' : ℝ} {V : TorusField n} (hs : s ≤ s') (hV : IsCold s V) :
    IsCold s' V := fun x μ ν h => lt_of_lt_of_le (hV x μ ν h) hs
private theorem trivialField_isCold {s : ℝ} (hs : 0 < s) (n : ℕ) : IsCold s (trivialField n) := by
  intro x μ ν _
  simpa [curvature, holonomy, trivialField] using hs
abbrev _root_.YangMills.SharedProofs.p4747 := @trivialField_isCold
private theorem mixedDeriv_zero_order {n : ℕ} (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 0 → TorusBond n)
    (X : Fin 0 → imaginaryQuaternions) :
    mixedDeriv G W c X = G W := by apply _root_.YangMills.Construction.TorusLumps.mixedDeriv_of_fin_zero <;> assumption
private theorem mixedDeriv_sub_const {n k : ℕ} (hk : 1 ≤ k) (G : TorusField n → ℝ) (κ : ℝ) (W : TorusField n)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (h : ContDiffAt ℝ k (fun σ : Fin k → ℝ => G (perturb c X σ W)) 0) :
    mixedDeriv (fun V => G V - κ) W c X = mixedDeriv G W c X := by
  unfold mixedDeriv
  have e1 : (fun σ : Fin k → ℝ => G (perturb c X σ W) - κ) =
      (fun σ : Fin k → ℝ => G (perturb c X σ W)) + (fun _ => -κ) := by
    funext σ
    simp [sub_eq_add_neg]
  have hc : iteratedFDeriv ℝ k (fun _ : Fin k → ℝ => -κ) = 0 := iteratedFDeriv_const_of_ne (by omega) (-κ)
  rw [e1, iteratedFDeriv_add_apply h contDiffAt_const, hc]
  simp
abbrev _root_.YangMills.DeltaSharedProofs.p1303 := @mixedDeriv_sub_const
abbrev _root_.YangMills.SharedProofs.p1322 := @mixedDeriv_sub_const
private theorem exp_bound_weaken {c c' C C' m : ℝ} (hc : c' ≤ c) (hC : C ≤ C') (hC' : 0 ≤ C') (hm : 0 ≤ m) :
    C * Real.exp (-(c * m)) ≤ C' * Real.exp (-(c' * m)) := by
  have h1 : Real.exp (-(c * m)) ≤ Real.exp (-(c' * m)) :=
    Real.exp_le_exp.2 (by nlinarith)
  exact mul_le_mul hC h1 (Real.exp_pos _).le hC'
private theorem exp_le_weightGrowthSup_div (hN : PotentialSumsFinite) {T : ParameterAssignment} (hT : T.Admissible) {c : ℝ}
    (hc : 2 * (T.rt / 2 ^ 10) ≤ c) (y₁ : ℝ) (m : ℕ) :
    Real.exp (-(c * m)) ≤ weightGrowthSup T.rt T.n₁ / (T.stepParameters y₁).weight m := by
  have hL : (0 : ℝ) < T.side := by
    have h := T.side_ne.out
    exact_mod_cast Nat.pos_of_ne_zero h
  have hn₁ : 0 < T.n₁ := Real.rpow_pos_of_pos hL _
  have h := (hN T.rt T.n₁ hT.rt_pos hn₁).2.2.2.1 m
  have e : (T.stepParameters y₁).weight m = expansionWeight T.rt T.n₁ m := rfl
  have hw : 0 < expansionWeight T.rt T.n₁ m := by
    unfold expansionWeight
    have : (0 : ℝ) < max 1 (((m : ℝ) / T.n₁) ^ 16000) := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  rw [e, le_div_iff₀ hw]
  have h1 : Real.exp (-(c * m)) ≤ Real.exp (-(2 * (T.rt / 2 ^ 10) * m)) :=
    Real.exp_le_exp.2 (by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith)
  calc _ ≤ Real.exp (-(2 * (T.rt / 2 ^ 10) * m)) * expansionWeight T.rt T.n₁ m :=
        mul_le_mul_of_nonneg_right h1 hw.le
    _ = expansionWeight T.rt T.n₁ m * Real.exp (-(2 * (T.rt / 2 ^ 10) * m)) := mul_comm _ _
    _ ≤ _ := h
theorem stepDensityBoundsAtParameters_holds (hA : AnalyticAtAdmissibleParameters)
    (hI : InvariantAtAdmissibleParameters)
    (hD : DensityDerivativesDecay)
    (hT₂ : StepDensityLocality) (hN : PotentialSumsFinite) :
    StepDensityBoundsAtFixedParameters := by
  obtain ⟨c₁, C₁, hc₁, hC₁, hd⟩ := hD
  obtain ⟨c₂, hc₂, ht⟩ := hT₂
  have hcpos : ∀ l, 0 < min (c₁ l) (c₂ l) := fun l => lt_min (hc₁ l) (hc₂ l)
  refine ⟨fun l => 2 ^ 8 * min (c₁ l) (c₂ l), fun l => min (c₁ l) (c₂ l),
    fun l => mul_pos (by norm_num) (hcpos l), hcpos, fun T hT => ?_⟩
  obtain ⟨C₂, hC₂, ht⟩ := ht T hT
  have hCpos : 0 < max (C₁ T.toChainParameters) C₂ := lt_max_of_lt_left (hC₁ _)
  refine ⟨max (C₁ T.toChainParameters) C₂, hCpos, ?_⟩
  have hσ : 0 < T.threshold := hT.σ_pos
  have hσ98 : T.threshold ≤ 9 / 8 * T.threshold := by linarith
  have hb : ∀ (y₁ : ℝ) (t : ℕ), HasStepDensityBounds T.threshold (T.stepParameters y₁)
      (min (c₁ T.toChainParameters) (c₂ T.toChainParameters))
      (max (C₁ T.toChainParameters) C₂) (paramStepDensity T t) := fun y₁ t =>
    { admissible :=
        { smooth := fun n _ hn y W hW k b X => (hA T hT t n hn y W (isCold_mono hσ98 hW) k b X).contDiffAt
          gauge := fun n _ hn y g W hW => (hI T hT t n hn W hW).1 y g
          translation := fun n _ hn y u W hW => (hI T hT t n hn W hW).2 y u }
      analyticAt := fun n _ hn y W hW k b X => hA T hT t n hn y W (isCold_mono hσ98 hW) k b X
      decay := fun n _ hn y W hW k b X k1 k3 hX =>
        (hd T hT t n hn y W (isCold_mono hσ98 hW) k b X k1 k3 hX).trans
          (exp_bound_weaken (min_le_left _ _) (le_max_left _ _) hCpos.le (Nat.cast_nonneg _))
      decay_wider := fun n _ hn y W hW k b X k1 k3 hX =>
        (hd T hT t n hn y W hW k b X k1 k3 hX).trans
          (exp_bound_weaken (min_le_left _ _) (le_max_left _ _) hCpos.le (Nat.cast_nonneg _))
      local_comparison := fun n n' _ _ hn hn' y y' W W' m h1 h2 hW hW' hA' k b X hk hb' hX =>
        (ht t n n' hn hn' y y' W W' m h1 h2 hW hW' hA' k b X hk hb' hX).trans
          (exp_bound_weaken (min_le_right _ _) (le_max_right _ _) hCpos.le (Nat.cast_nonneg _)) }
  refine ⟨fun y₁ t _ => hb y₁ t, fun hrt => ?_⟩
  set c := min (c₁ T.toChainParameters) (c₂ T.toChainParameters) with hcdef
  set C := max (C₁ T.toChainParameters) C₂ with hCdef
  have hC0 : 0 < C := hCpos
  have h4 : 4 * (T.rt / 2 ^ 10) ≤ c := by
    have h : T.rt ≤ 2 ^ 8 * c := hrt
    norm_num at h ⊢
    linarith
  have h2 : 2 * (T.rt / 2 ^ 10) ≤ c := by
    have := hT.rt_pos
    have h : (0 : ℝ) ≤ T.rt / 2 ^ 10 := by positivity
    linarith
  have hL : (0 : ℝ) < T.side := by
    have h := T.side_ne.out
    exact_mod_cast Nat.pos_of_ne_zero h
  have hn₁ : 0 < T.n₁ := Real.rpow_pos_of_pos hL _
  have hcap : 1 ≤ weightGrowthSup T.rt T.n₁ := (hN T.rt T.n₁ hT.rt_pos hn₁).2.2.2.2.2.2
  have hn64 : 64 ≤ T.n₀ := le_trans (by norm_num) hT.n₀_ge
  refine ⟨h4, 2 * C * weightGrowthSup T.rt T.n₁, by positivity, fun y₁ t _ => ?_⟩
  have hB := hb y₁ t
  have hw : ∀ m : ℕ, C * Real.exp (-(c * m)) ≤ C * weightGrowthSup T.rt T.n₁ / (T.stepParameters y₁).weight m :=
    fun m => by
      have := mul_le_mul_of_nonneg_left (exp_le_weightGrowthSup_div hN hT h2 y₁ m) hC0.le
      rwa [mul_div_assoc]
  have hwpos : ∀ m : ℕ, 0 < (T.stepParameters y₁).weight m := fun m => by
    unfold StepParameters.weight
    have : (0 : ℝ) < max 1 (((m : ℝ) / (T.stepParameters y₁).n₁) ^ 16000) :=
      lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  have hdouble : ∀ m : ℕ, C * weightGrowthSup T.rt T.n₁ / (T.stepParameters y₁).weight m ≤
      2 * C * weightGrowthSup T.rt T.n₁ / (T.stepParameters y₁).weight m := fun m => by
    refine div_le_div_of_nonneg_right ?_ (hwpos m).le
    have : 0 < C * weightGrowthSup T.rt T.n₁ := by positivity
    linarith
  refine
    { smooth := fun n _ hn y W hW => hB.admissible.smooth n (hn64.trans hn) y W hW
      gauge := fun n _ hn y g W hW => hB.admissible.gauge n (hn64.trans hn) y g W hW
      translation := fun n _ hn y u W hW => hB.admissible.translation n (hn64.trans hn) y u W hW
      decay := fun n _ hn y W hW k b X k1 k3 hX =>
        ((hB.decay n (hn64.trans hn) y W hW k b X k1 k3 hX).trans (hw _)).trans (hdouble _)
      local_density := ?_ }
  intro n n' _ _ hn hn' y y' W W' m h1 h2' hW hW' hAg k b X hk hbox hX
  have hn64' : 64 ≤ n := hn64.trans hn
  have hn64'' : 64 ≤ n' := hn64.trans hn'
  have hcmp := hB.local_comparison n n' hn64' hn64'' y y' W W' m h1 h2' hW hW' hAg k b X hk hbox hX
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have a2 := hB.local_comparison n n' hn64' hn64'' y y' (trivialField n) (trivialField n') m h1 h2'
      (trivialField_isCold hσ n) (trivialField_isCold hσ n') (fun _ _ => rfl) 0 b X hk hbox hX
    simp only [mixedDeriv_zero_order] at hcmp a2 ⊢
    have e : centered (paramStepDensity T t) n y W - centered (paramStepDensity T t) n' y' W' =
        (paramStepDensity T t n y W - paramStepDensity T t n' y' W') -
          (paramStepDensity T t n y (trivialField n) - paramStepDensity T t n' y' (trivialField n')) := by
      unfold centered
      ring
    rw [e]
    have hbound : C * Real.exp (-(c * m)) ≤ C * weightGrowthSup T.rt T.n₁ / (T.stepParameters y₁).weight m := hw m
    have hsplit : 2 * C * weightGrowthSup T.rt T.n₁ / (T.stepParameters y₁).weight m =
        C * weightGrowthSup T.rt T.n₁ / (T.stepParameters y₁).weight m +
          C * weightGrowthSup T.rt T.n₁ / (T.stepParameters y₁).weight m := by
      ring
    rw [hsplit]
    exact (abs_sub _ _).trans (add_le_add (hcmp.trans hbound) (a2.trans hbound))
  · have hk' : ∀ (r : ℕ) [NeZero r] (z : TorusSite r) (V : TorusField r) (e : Fin k → TorusBond r), 64 ≤ r →
        IsCold T.threshold V →
        mixedDeriv (centered (paramStepDensity T t) r z) V e X = mixedDeriv (paramStepDensity T t r z) V e X := by
      intro r _ z V e hr hV
      exact mixedDeriv_sub_const hk1 (paramStepDensity T t r z) _ V e X
        (hA T hT t r hr z V (isCold_mono hσ98 hV) k e X).contDiffAt
    rw [hk' n y W _ hn64' hW, hk' n' y' W' _ hn64'' hW']
    exact (hcmp.trans (hw m)).trans (hdouble m)
end RunningCouplingSlope
end YangMills.Construction
end
