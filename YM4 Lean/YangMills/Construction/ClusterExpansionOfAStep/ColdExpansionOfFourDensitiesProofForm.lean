import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfFourDensities
import YangMills.Construction.ClusterExpansionOfAStep.NumbersOfTheStepAreFiniteProof
import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfAnExpansionProof
import YangMills.Construction.ClusterExpansionOfAStep.WilsonWeightHasTheExpansionProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.TorusLumps.DensityExpansion
open YangMills.Construction.BlockAverages
open YangMills.Construction.TorusFields
open YangMills.Construction.TorusLumps
section Calculus
variable {n k : ℕ}
theorem mixedDeriv_add (G₁ G₂ : TorusField n → ℝ) (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3)
    (h₁ : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => G₁ (perturb c X σ W)) 0)
    (h₂ : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => G₂ (perturb c X σ W)) 0) :
    mixedDeriv (fun V => G₁ V + G₂ V) W c X = mixedDeriv G₁ W c X + mixedDeriv G₂ W c X := by
  have hk' : ((k : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have e := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := k) (h₁.of_le hk') (h₂.of_le hk')
  unfold mixedDeriv
  have : (fun σ : Fin k → ℝ => G₁ (perturb c X σ W) + G₂ (perturb c X σ W)) =
      (fun σ : Fin k → ℝ => G₁ (perturb c X σ W)) + (fun σ : Fin k → ℝ => G₂ (perturb c X σ W)) := rfl
  rw [this, e]
  rfl
theorem mixedDeriv_const_mul (b : ℝ) (G : TorusField n → ℝ) (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3)
    (h : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => G (perturb c X σ W)) 0) :
    mixedDeriv (fun V => b * G V) W c X = b * mixedDeriv G W c X := by
  have hk' : ((k : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have e := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := k) (a := b) (h.of_le hk')
  unfold mixedDeriv
  have : (fun σ : Fin k → ℝ => b * G (perturb c X σ W)) = b • (fun σ : Fin k → ℝ => G (perturb c X σ W)) := rfl
  rw [this, e]
  rfl
theorem mixedDeriv_sub_const (G : TorusField n → ℝ) (e : ℝ) (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (hk : 1 ≤ k)
    (hk3 : k ≤ 3) (h : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => G (perturb c X σ W)) 0) :
    mixedDeriv (fun V => G V - e) W c X = mixedDeriv G W c X := by
  have hk' : ((k : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk3
  have e1 := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := k) (h.of_le hk')
    (contDiffAt_const (c := e) (x := (0 : Fin k → ℝ)))
  unfold mixedDeriv
  have : (fun σ : Fin k → ℝ => G (perturb c X σ W) - e) =
      (fun σ : Fin k → ℝ => G (perturb c X σ W)) - (fun _ => e) := rfl
  rw [this, e1, iteratedFDeriv_const_of_ne (by omega)]
  simp
theorem mixedDeriv_of_no_bonds (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 0 → TorusBond n)
    (X : Fin 0 → imaginaryQuaternions) :
    mixedDeriv G W c X = G W := by apply _root_.YangMills.Construction.TorusLumps.mixedDeriv_of_fin_zero <;> assumption
theorem mixedDeriv_four_sub_mul (G₁ G₂ G₃ G₄ G₅ : TorusField n → ℝ) (b : ℝ) (W : TorusField n)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (hk : k ≤ 3)
    (h₁ : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => G₁ (perturb c X σ W)) 0)
    (h₂ : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => G₂ (perturb c X σ W)) 0)
    (h₃ : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => G₃ (perturb c X σ W)) 0)
    (h₄ : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => G₄ (perturb c X σ W)) 0)
    (h₅ : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => G₅ (perturb c X σ W)) 0) :
    mixedDeriv (fun V => G₁ V + G₂ V + G₃ V + G₄ V - b * G₅ V) W c X =
      mixedDeriv G₁ W c X + mixedDeriv G₂ W c X + mixedDeriv G₃ W c X + mixedDeriv G₄ W c X -
        b * mixedDeriv G₅ W c X := by
  have e₀ : (fun V => G₁ V + G₂ V + G₃ V + G₄ V - b * G₅ V) =
      fun V => (G₁ V + G₂ V + G₃ V + G₄ V) + (-b) * G₅ V := by
    funext V
    ring
  have s₂ : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => G₁ (perturb c X σ W) + G₂ (perturb c X σ W)) 0 :=
    h₁.add h₂
  have s₃ : ContDiffAt ℝ 3
      (fun σ : Fin k → ℝ => G₁ (perturb c X σ W) + G₂ (perturb c X σ W) + G₃ (perturb c X σ W)) 0 :=
    s₂.add h₃
  have s₄ : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ =>
      G₁ (perturb c X σ W) + G₂ (perturb c X σ W) + G₃ (perturb c X σ W) + G₄ (perturb c X σ W)) 0 :=
    s₃.add h₄
  have s₅ : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => (-b) * G₅ (perturb c X σ W)) 0 := contDiffAt_const.mul h₅
  rw [e₀, mixedDeriv_add (fun V => G₁ V + G₂ V + G₃ V + G₄ V) (fun V => (-b) * G₅ V) W c X hk s₄ s₅,
    mixedDeriv_add (fun V => G₁ V + G₂ V + G₃ V) G₄ W c X hk s₃ h₄,
    mixedDeriv_add (fun V => G₁ V + G₂ V) G₃ W c X hk s₂ h₃, mixedDeriv_add G₁ G₂ W c X hk h₁ h₂,
    mixedDeriv_const_mul (-b) G₅ W c X hk h₅]
  ring
end Calculus
section Weight
theorem weight_eq_expansionWeight (ℓ : StepParameters) (m : ℕ) : ℓ.weight m = expansionWeight ℓ.rt ℓ.n₁ m := by
  simp only [StepParameters.weight, StepParameters.weightRate, expansionWeight]
theorem weight_pos (ℓ : StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
theorem bddAbove_expansionWeight_mul_exp (rt n₁ : ℝ) (hrt : 0 < rt) (hn : 0 < n₁) :
    BddAbove (Set.range fun m : ℕ => expansionWeight rt n₁ m * Real.exp (-(2 * (rt / 2 ^ 10) * m))) := by apply _root_.YangMills.Construction.TorusLumps.PotentialSums.bddAbove_expansionWeight_mul_exp <;> assumption
theorem exp_le_weightGrowthSup_div (ℓ : StepParameters) (hrt : 0 < ℓ.rt) (hn : 0 < ℓ.n₁) (m : ℕ) (κ : ℝ)
    (hκ : 2 * (ℓ.rt / 2 ^ 10) ≤ κ) :
    Real.exp (-(κ * m)) ≤ weightGrowthSup ℓ.rt ℓ.n₁ / ℓ.weight m := by
  have hw := weight_pos ℓ m
  rw [le_div_iff₀ hw, weight_eq_expansionWeight]
  have h₁ : expansionWeight ℓ.rt ℓ.n₁ m * Real.exp (-(2 * (ℓ.rt / 2 ^ 10) * m)) ≤
      weightGrowthSup ℓ.rt ℓ.n₁ :=
    le_ciSup (bddAbove_expansionWeight_mul_exp ℓ.rt ℓ.n₁ hrt hn) m
  have h₂ : Real.exp (-(κ * m)) ≤ Real.exp (-(2 * (ℓ.rt / 2 ^ 10) * m)) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hw' : 0 < expansionWeight ℓ.rt ℓ.n₁ m := by rw [← weight_eq_expansionWeight]; exact hw
  calc Real.exp (-(κ * m)) * expansionWeight ℓ.rt ℓ.n₁ m
      ≤ Real.exp (-(2 * (ℓ.rt / 2 ^ 10) * m)) * expansionWeight ℓ.rt ℓ.n₁ m :=
        mul_le_mul_of_nonneg_right h₂ hw'.le
    _ = expansionWeight ℓ.rt ℓ.n₁ m * Real.exp (-(2 * (ℓ.rt / 2 ^ 10) * m)) := mul_comm _ _
    _ ≤ weightGrowthSup ℓ.rt ℓ.n₁ := h₁
theorem weightGrowthSup_nonneg (ℓ : StepParameters) (hrt : 0 < ℓ.rt) (hn : 0 < ℓ.n₁) :
    0 ≤ weightGrowthSup ℓ.rt ℓ.n₁ := by
  have h := exp_le_weightGrowthSup_div ℓ hrt hn 0 (2 * (ℓ.rt / 2 ^ 10)) le_rfl
  have hw := weight_pos ℓ 0
  have h1 : 0 < Real.exp (-(2 * (ℓ.rt / 2 ^ 10) * ((0 : ℕ) : ℝ))) := Real.exp_pos _
  have h2 : 0 < weightGrowthSup ℓ.rt ℓ.n₁ / ℓ.weight 0 := lt_of_lt_of_le h1 h
  exact ((div_pos_iff_of_pos_right hw).mp h2).le
end Weight
section Requirements
variable {ℓ : StepParameters}
theorem trivialField_isCold (hσ : 0 < ℓ.threshold) (n : ℕ) : IsCold ℓ.threshold (trivialField n) := by
  intro x μ ν _
  simpa [curvature, holonomy, trivialField] using hσ
theorem trivialField_agree {n n' : ℕ} (y : TorusSite n) (y' : TorusSite n') (m : ℕ) :
    FieldsAgreeNear (trivialField n) (trivialField n') y y' m := fun _ _ => rfl
theorem localComparison_centered {h : LocalDensity} {e : ℕ → ℝ} (hσ : 0 < ℓ.threshold)
    (hp : IsAdmissibleDensity ℓ h) (hc : LocalComparison ℓ h e) (he : ∀ m, 0 ≤ e m) :
    LocalComparison ℓ (centeredFamily h) fun m => 2 * e m := by
  intro n n' _ _ hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have A := hc n n' hn hn' y y' W W' m h2 h2' cW cW' ag 0 bb X hk hbox hu
    have B := hc n n' hn hn' y y' (trivialField n) (trivialField n') m h2 h2' (trivialField_isCold hσ n)
      (trivialField_isCold hσ n') (trivialField_agree y y' m) 0 bb X hk hbox hu
    rw [mixedDeriv_of_no_bonds, mixedDeriv_of_no_bonds] at A B
    rw [mixedDeriv_of_no_bonds, mixedDeriv_of_no_bonds]
    simp only [centeredFamily, centered]
    rw [abs_le] at A B ⊢
    constructor <;> linarith [A.1, A.2, B.1, B.2]
  · have A := hc n n' hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu
    have e₁ : mixedDeriv (centeredFamily h n y) W (fun l => bondFrom y (bb l)) X =
        mixedDeriv (h n y) W (fun l => bondFrom y (bb l)) X :=
      mixedDeriv_sub_const (h n y) _ W _ X hk1 (by omega) (hp.smooth n hn y W cW k _ X)
    have e₂ : mixedDeriv (centeredFamily h n' y') W' (fun l => bondFrom y' (bb l)) X =
        mixedDeriv (h n' y') W' (fun l => bondFrom y' (bb l)) X :=
      mixedDeriv_sub_const (h n' y') _ W' _ X hk1 (by omega) (hp.smooth n' hn' y' W' cW' k _ X)
    rw [e₁, e₂]
    linarith [he m]
theorem abs_four_sub_mul_le (d₁ d₂ d₃ d₄ d₅ b : ℝ) :
    |d₁ + d₂ + d₃ + d₄ - b * d₅| ≤ |d₁| + |d₂| + |d₃| + |d₄| + |b| * |d₅| := by
  calc |d₁ + d₂ + d₃ + d₄ - b * d₅| ≤ |d₁ + d₂ + d₃ + d₄| + |b * d₅| := abs_sub _ _
    _ ≤ |d₁ + d₂ + d₃| + |d₄| + |b * d₅| := by gcongr; exact abs_add_le _ _
    _ ≤ |d₁ + d₂| + |d₃| + |d₄| + |b * d₅| := by gcongr; exact abs_add_le _ _
    _ ≤ |d₁| + |d₂| + |d₃| + |d₄| + |b * d₅| := by gcongr; exact abs_add_le _ _
    _ = |d₁| + |d₂| + |d₃| + |d₄| + |b| * |d₅| := by rw [abs_mul]
end Requirements
section Main
variable {ℓ : StepParameters} {t : ℕ} {x b Cs CE ε e Na : ℝ} {Dp : TorusFunctional}
  {u s τ g a : LocalDensity}
theorem centered_densitiesLessMultiple (n : ℕ) (y : TorusSite n) :
    centered (densitiesLessMultiple u s τ g a b) n y =
      fun V => centered u n y V + centered s n y V + centered τ n y V + centered g n y V -
        b * centered a n y V := by
  funext V
  simp only [centered, densitiesLessMultiple, sumOfFour]
  ring
theorem weightGrowthSup_terms_le (H : ColdExpansionHypotheses ℓ t x b Cs CE ε e Na Dp u s τ g a) :
    2 * Cs * weightGrowthSup ℓ.rt ℓ.n₁ + baseConstant Cs ℓ.rt * (weightGrowthSup ℓ.rt ℓ.n₁ * Na) ≤
      ℓ.E / 4 := by
  have hB := H.abs_b_le
  have hf0 : 0 ≤ baseConstant Cs ℓ.rt := le_trans (abs_nonneg _) hB
  have hE := H.E_eq
  unfold expansionConstant at hE
  nlinarith [hf0]
theorem contDiffAt_sumOfFour (H : ColdExpansionHypotheses ℓ t x b Cs CE ε e Na Dp u s τ g a) (n : ℕ)
    [NeZero n] (hn : ℓ.n₀ ≤ n) (y : TorusSite n) (W : TorusField n) (hc : IsCold ℓ.threshold W) (k : ℕ)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => sumOfFour u s τ g n y (perturb c X σ W)) 0 :=
  (((H.densityBounds.admissible_u.smooth n hn y W hc k c X).add
    (H.densityBounds.admissible_s.smooth n hn y W hc k c X)).add
    (H.densityBounds.admissible_τ.smooth n hn y W hc k c X)).add
    (H.densityBounds.admissible_g.smooth n hn y W hc k c X)
theorem secondDerivLimit_densitiesLessMultiple (H : ColdExpansionHypotheses ℓ t x b Cs CE ε e Na Dp u s τ g a)
    (c c' : LatticeBond) (X X' : imaginaryQuaternions) :
    secondDerivLimit (densitiesLessMultiple u s τ g a b) c c' X X' =
      secondDerivLimit (sumOfFour u s τ g) c c' X X' - b * secondDerivLimit a c c' X X' := by
  obtain ⟨v₁, t₁⟩ := H.form_sum.1 c c' X X'
  obtain ⟨v₂, t₂⟩ := H.form_family.1 c c' X X'
  have e₁ : secondDerivLimit (sumOfFour u s τ g) c c' X X' = v₁ := t₁.limUnder_eq
  have e₂ : secondDerivLimit a c c' X X' = v₂ := t₂.limUnder_eq
  rw [e₁, e₂]
  have t₃ := t₁.sub (t₂.const_mul b)
  refine Filter.Tendsto.limUnder_eq (t₃.congr' ?_)
  have hσ := H.admissible.σ_pos
  have hn₀ := H.admissible.n₀_ge
  filter_upwards [Filter.eventually_ge_atTop ℓ.n₀] with n hn
  have : NeZero n := ⟨by omega⟩
  have hc := trivialField_isCold hσ n
  have h₁ := contDiffAt_sumOfFour H n hn 0 (trivialField n) hc 2 ![bondFrom 0 c, bondFrom 0 c'] ![X, X']
  have h₂ := H.family.smooth n hn 0 (trivialField n) hc 2 ![bondFrom 0 c, bondFrom 0 c'] ![X, X']
  have e₃ : densitiesLessMultiple u s τ g a b n 0 =
      fun V => sumOfFour u s τ g n 0 V + (-b) * a n 0 V := by
    funext V
    simp only [densitiesLessMultiple]
    ring
  have h₃ : ContDiffAt ℝ 3 (fun σ : Fin 2 → ℝ =>
      (-b) * a n 0 (perturb ![bondFrom 0 c, bondFrom 0 c'] ![X, X'] σ (trivialField n))) 0 :=
    contDiffAt_const.mul h₂
  rw [e₃, mixedDeriv_add _ _ _ _ _ (by omega) h₁ h₃, mixedDeriv_const_mul (-b) _ _ _ _ (by omega) h₂]
  ring
theorem limitForm_densitiesLessMultiple_hasSum_zero
    (H : ColdExpansionHypotheses ℓ t x b Cs CE ε e Na Dp u s τ g a)
    (A A' : Fin 4 → Fin 4 → imaginaryQuaternions) (hA : ∀ μ ν, A μ ν = - A ν μ)
    (hA' : ∀ μ ν, A' μ ν = - A' ν μ) :
    HasSum (fun cc : LatticeBond × LatticeBond =>
      secondDerivLimit (densitiesLessMultiple u s τ g a b) cc.1 cc.2 (linearPotential A cc.1)
        (linearPotential A' cc.2)) 0 := by
  have h₁ := H.form_sum.2 A A' hA hA'
  have h₂ := (H.form_family.2 A A' hA hA').mul_left b
  have h₃ := h₁.sub h₂
  have e₀ : b * curvaturePairing A A' - b * (1 * curvaturePairing A A') = 0 := by ring
  rw [e₀] at h₃
  have e₁ : (fun cc : LatticeBond × LatticeBond =>
      secondDerivLimit (densitiesLessMultiple u s τ g a b) cc.1 cc.2 (linearPotential A cc.1)
        (linearPotential A' cc.2)) =
      fun cc => limitFormTerm (sumOfFour u s τ g) A A' cc - b * (limitFormTerm a A A' cc) := by
    funext cc
    exact secondDerivLimit_densitiesLessMultiple H cc.1 cc.2 _ _
  rw [e₁]
  exact h₃
theorem decay_densitiesLessMultiple (H : ColdExpansionHypotheses ℓ t x b Cs CE ε e Na Dp u s τ g a) (n : ℕ)
    [NeZero n] (hn : ℓ.n₀ ≤ n) (y : TorusSite n) (W : TorusField n) (hc : IsCold ℓ.threshold W) (k : ℕ)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (hk1 : 1 ≤ k) (hk3 : k ≤ 3)
    (hu : AreUnitVectors X) :
    |mixedDeriv (densitiesLessMultiple u s τ g a b n y) W c X| ≤
      (if k = 3 then ℓ.E₃ else ℓ.E) / ℓ.weight (supportDiam y c) := by
  have hrt := H.admissible.rt_pos
  have hn₁ := H.admissible.n₁_pos
  have F := H.densityBounds
  have e₅ := mixedDeriv_four_sub_mul (u n y) (s n y) (τ n y) (g n y) (a n y) b W c X hk3
    (F.admissible_u.smooth n hn y W hc k c X) (F.admissible_s.smooth n hn y W hc k c X)
    (F.admissible_τ.smooth n hn y W hc k c X) (F.admissible_g.smooth n hn y W hc k c X)
    (H.family.smooth n hn y W hc k c X)
  have e₀ : mixedDeriv (densitiesLessMultiple u s τ g a b n y) W c X =
      mixedDeriv (fun V => u n y V + s n y V + τ n y V + g n y V - b * a n y V) W c X := rfl
  rw [e₀, e₅]
  set m := supportDiam y c with hm
  set w := ℓ.weight m with hw
  have hw0 : 0 < w := weight_pos ℓ m
  set C := weightGrowthSup ℓ.rt ℓ.n₁ with hC
  set Ek : ℝ := if k = 3 then ℓ.E₃ else ℓ.E with hEk
  have hEk0 : ℓ.E ≤ Ek := by
    rw [hEk]
    split_ifs
    · exact H.E_le
    · exact le_rfl
  have hC0 : 0 ≤ C := weightGrowthSup_nonneg ℓ hrt hn₁
  have hexp : Real.exp (-(ℓ.rt / 2 ^ 6 * m)) * w ≤ C := by
    have := exp_le_weightGrowthSup_div ℓ hrt hn₁ m (ℓ.rt / 2 ^ 6) (by
      have : (0 : ℝ) < ℓ.rt := hrt
      norm_num
      linarith)
    rwa [le_div_iff₀ hw0] at this
  have du := F.decay_u n hn y W hc k c X hk1 hk3 hu
  have ds := F.decay_s n hn y W hc k c X hk1 hk3 hu
  have dτ := F.decay_τ n hn y W hc k c X hk1 hk3 hu
  have dg := F.decay_g n hn y W hc k c X hk1 hk3 hu
  have da := H.family.decay n hn y W hc k c X hk1 hk3 hu
  simp only at du ds dτ dg
  rw [← hm] at du ds dτ dg da
  set Px : ℝ := CE * x ^ (-(1 / 2 : ℝ)) with hPx
  have hPx0 : 0 ≤ Px := mul_nonneg H.CE_nonneg (Real.rpow_nonneg H.x_nonneg _)
  have hU : |mixedDeriv (u n y) W c X| * w ≤ Cs * C := by
    calc |mixedDeriv (u n y) W c X| * w ≤ Cs * Real.exp (-(ℓ.rt / 2 ^ 6 * m)) * w :=
          mul_le_mul_of_nonneg_right du hw0.le
      _ = Cs * (Real.exp (-(ℓ.rt / 2 ^ 6 * m)) * w) := by ring
      _ ≤ Cs * C := mul_le_mul_of_nonneg_left hexp H.Cs_nonneg
  have hS : |mixedDeriv (s n y) W c X| * w ≤ 2⁻¹ ^ 6 * Ek + Px * C := by
    calc |mixedDeriv (s n y) W c X| * w ≤
          (2⁻¹ ^ 6 * Ek / w + Px * Real.exp (-(ℓ.rt / 2 ^ 6 * m))) * w :=
          mul_le_mul_of_nonneg_right ds hw0.le
      _ = 2⁻¹ ^ 6 * Ek + Px * (Real.exp (-(ℓ.rt / 2 ^ 6 * m)) * w) := by
          field_simp
      _ ≤ 2⁻¹ ^ 6 * Ek + Px * C := by
          gcongr
  have hT : |mixedDeriv (τ n y) W c X| * w ≤ ε := by
    rwa [le_div_iff₀ hw0] at dτ
  have hG : |mixedDeriv (g n y) W c X| * w ≤ e := by
    rwa [le_div_iff₀ hw0] at dg
  have hA : |mixedDeriv (a n y) W c X| * w ≤ C * Na := by
    rwa [le_div_iff₀ hw0] at da
  have hbA : |b| * |mixedDeriv (a n y) W c X| * w ≤ baseConstant Cs ℓ.rt * (C * Na) := by
    calc |b| * |mixedDeriv (a n y) W c X| * w = |b| * (|mixedDeriv (a n y) W c X| * w) := by ring
      _ ≤ baseConstant Cs ℓ.rt * (C * Na) :=
        mul_le_mul H.abs_b_le hA (mul_nonneg (abs_nonneg _) hw0.le) (le_trans (abs_nonneg _) H.abs_b_le)
  have hnum := weightGrowthSup_terms_le H
  have hsmall := H.small
  have hE0 : 0 < ℓ.E := H.admissible.E_pos
  have hCs : 0 ≤ Cs * C := mul_nonneg H.Cs_nonneg hC0
  rw [le_div_iff₀ hw0]
  have hab := abs_four_sub_mul_le (mixedDeriv (u n y) W c X) (mixedDeriv (s n y) W c X)
    (mixedDeriv (τ n y) W c X) (mixedDeriv (g n y) W c X) (mixedDeriv (a n y) W c X) b
  have hab' := mul_le_mul_of_nonneg_right hab hw0.le
  have hε := H.ε_nonneg
  have he := H.e_nonneg
  have h2 : (2⁻¹ : ℝ) ^ 6 = 1 / 64 := by norm_num
  rw [h2] at hS
  nlinarith [hab', hU, hS, hT, hG, hbA, hnum, hsmall, hEk0, hE0, hCs]
theorem localComparison_densitiesLessMultiple (H : ColdExpansionHypotheses ℓ t x b Cs CE ε e Na Dp u s τ g a)
    (n n' : ℕ) [NeZero n] [NeZero n']
    (hn : ℓ.n₀ ≤ n) (hn' : ℓ.n₀ ≤ n') (y : TorusSite n) (y' : TorusSite n') (W : TorusField n)
    (W' : TorusField n') (m : ℕ)
    (h2 : 2 * m + 2 < n) (h2' : 2 * m + 2 < n') (hc : IsCold ℓ.threshold W) (hc' : IsCold ℓ.threshold W')
    (ag : FieldsAgreeNear W W' y y' m) (k : ℕ) (bb : Fin k → (Fin 4 → ℤ) × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (hk : k ≤ 2) (hbox : ∀ l, BondOffsetInBox m (bb l)) (hu : AreUnitVectors X) :
    |mixedDeriv (centered (densitiesLessMultiple u s τ g a b) n y) W (fun l => bondFrom y (bb l)) X -
        mixedDeriv (centered (densitiesLessMultiple u s τ g a b) n' y') W' (fun l => bondFrom y' (bb l)) X| ≤
      ℓ.E / ℓ.weight m := by
  have hrt := H.admissible.rt_pos
  have hn₁ := H.admissible.n₁_pos
  have hσ := H.admissible.σ_pos
  have F := H.densityBounds
  have hk3 : k ≤ 3 := by omega
  have centered_smooth : ∀ (h : LocalDensity) (p : ℕ) [NeZero p] (z : TorusSite p) (V : TorusField p)
      (c : Fin k → TorusBond p),
      IsAdmissibleDensity ℓ h → ℓ.n₀ ≤ p → IsCold ℓ.threshold V →
      ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => centered h p z (perturb c X σ V)) 0 :=
    fun h p _ z V c hp hpn hV => (hp.smooth p hpn z V hV k c X).sub contDiffAt_const
  have centered_smooth_a : ∀ (p : ℕ) [NeZero p] (z : TorusSite p) (V : TorusField p)
      (c : Fin k → TorusBond p),
      ℓ.n₀ ≤ p → IsCold ℓ.threshold V →
      ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => centered a p z (perturb c X σ V)) 0 :=
    fun p _ z V c hpn hV => (H.family.smooth p hpn z V hV k c X).sub contDiffAt_const
  set c₁ : Fin k → TorusBond n := fun l => bondFrom y (bb l) with hc₁
  set c₂ : Fin k → TorusBond n' := fun l => bondFrom y' (bb l) with hc₂
  have e₁ := mixedDeriv_four_sub_mul (centered u n y) (centered s n y) (centered τ n y) (centered g n y)
    (centered a n y) b W c₁ X hk3
    (centered_smooth u n y W c₁ F.admissible_u hn hc) (centered_smooth s n y W c₁ F.admissible_s hn hc)
    (centered_smooth τ n y W c₁ F.admissible_τ hn hc) (centered_smooth g n y W c₁ F.admissible_g hn hc)
    (centered_smooth_a n y W c₁ hn hc)
  have e₂ := mixedDeriv_four_sub_mul (centered u n' y') (centered s n' y') (centered τ n' y')
    (centered g n' y') (centered a n' y') b W' c₂ X hk3
    (centered_smooth u n' y' W' c₂ F.admissible_u hn' hc') (centered_smooth s n' y' W' c₂ F.admissible_s hn' hc')
    (centered_smooth τ n' y' W' c₂ F.admissible_τ hn' hc') (centered_smooth g n' y' W' c₂ F.admissible_g hn' hc')
    (centered_smooth_a n' y' W' c₂ hn' hc')
  rw [centered_densitiesLessMultiple, centered_densitiesLessMultiple, e₁, e₂]
  set w := ℓ.weight m with hw
  have hw0 : 0 < w := weight_pos ℓ m
  set C := weightGrowthSup ℓ.rt ℓ.n₁ with hC
  have hC0 : 0 ≤ C := weightGrowthSup_nonneg ℓ hrt hn₁
  have hexp : Real.exp (-(ℓ.rt / 2 ^ 9 * m)) * w ≤ C := by
    have := exp_le_weightGrowthSup_div ℓ hrt hn₁ m (ℓ.rt / 2 ^ 9) (le_of_eq (by ring))
    rwa [le_div_iff₀ hw0] at this
  have cu := localComparison_centered hσ F.admissible_u F.local_u
    (fun m => mul_nonneg H.Cs_nonneg (Real.exp_pos _).le)
  have cτ := localComparison_centered hσ F.admissible_τ F.local_τ
    (fun m => div_nonneg H.ε_nonneg (weight_pos ℓ m).le)
  have du := cu n n' hn hn' y y' W W' m h2 h2' hc hc' ag k bb X hk hbox hu
  have ds := F.local_s n n' hn hn' y y' W W' m h2 h2' hc hc' ag k bb X hk hbox hu
  have dτ := cτ n n' hn hn' y y' W W' m h2 h2' hc hc' ag k bb X hk hbox hu
  have dg := F.local_g n n' hn hn' y y' W W' m h2 h2' hc hc' ag k bb X hk hbox hu
  have da := H.family.local_density n n' hn hn' y y' W W' m h2 h2' hc hc' ag k bb X hk hbox hu
  simp only at du ds dτ dg
  set U := mixedDeriv (centered u n y) W c₁ X - mixedDeriv (centered u n' y') W' c₂ X with hU'
  set S := mixedDeriv (centered s n y) W c₁ X - mixedDeriv (centered s n' y') W' c₂ X with hS'
  set T := mixedDeriv (centered τ n y) W c₁ X - mixedDeriv (centered τ n' y') W' c₂ X with hT'
  set G := mixedDeriv (centered g n y) W c₁ X - mixedDeriv (centered g n' y') W' c₂ X with hG'
  set A := mixedDeriv (centered a n y) W c₁ X - mixedDeriv (centered a n' y') W' c₂ X with hA'
  have hU : |U| * w ≤ 2 * Cs * C := by
    have du' : |U| ≤ 2 * (Cs * Real.exp (-(ℓ.rt / 2 ^ 9 * m))) := du
    calc |U| * w ≤ 2 * (Cs * Real.exp (-(ℓ.rt / 2 ^ 9 * m))) * w :=
          mul_le_mul_of_nonneg_right du' hw0.le
      _ = 2 * Cs * (Real.exp (-(ℓ.rt / 2 ^ 9 * m)) * w) := by ring
      _ ≤ 2 * Cs * C := mul_le_mul_of_nonneg_left hexp (by linarith [H.Cs_nonneg])
  have hS : |S| * w ≤ 1 / 16 * ℓ.E := by
    have ds' : |S| ≤ 2⁻¹ ^ 4 * ℓ.E / w := ds
    have h2 : (2⁻¹ : ℝ) ^ 4 = 1 / 16 := by norm_num
    rw [h2, le_div_iff₀ hw0] at ds'
    exact ds'
  have hT : |T| * w ≤ 2 * ε := by
    have dτ' : |T| ≤ 2 * (ε / w) := dτ
    calc |T| * w ≤ 2 * (ε / w) * w := mul_le_mul_of_nonneg_right dτ' hw0.le
      _ = 2 * ε := by field_simp
  have hG : |G| * w ≤ e := by
    have dg' : |G| ≤ e / w := dg
    rwa [le_div_iff₀ hw0] at dg'
  have hA : |A| * w ≤ C * Na := by
    have da' : |A| ≤ C * Na / w := da
    rwa [le_div_iff₀ hw0] at da'
  have hbA : |b| * |A| * w ≤ baseConstant Cs ℓ.rt * (C * Na) := by
    calc |b| * |A| * w = |b| * (|A| * w) := by ring
      _ ≤ baseConstant Cs ℓ.rt * (C * Na) :=
        mul_le_mul H.abs_b_le hA (mul_nonneg (abs_nonneg _) hw0.le) (le_trans (abs_nonneg _) H.abs_b_le)
  have hnum := weightGrowthSup_terms_le H
  have hsmall := H.small
  have hE0 : 0 < ℓ.E := H.admissible.E_pos
  have hPx0 : 0 ≤ CE * x ^ (-(1 / 2 : ℝ)) * C :=
    mul_nonneg (mul_nonneg H.CE_nonneg (Real.rpow_nonneg H.x_nonneg _)) hC0
  have he := H.e_nonneg
  have e₃ : mixedDeriv (centered u n y) W c₁ X + mixedDeriv (centered s n y) W c₁ X +
        mixedDeriv (centered τ n y) W c₁ X + mixedDeriv (centered g n y) W c₁ X -
        b * mixedDeriv (centered a n y) W c₁ X -
      (mixedDeriv (centered u n' y') W' c₂ X + mixedDeriv (centered s n' y') W' c₂ X +
        mixedDeriv (centered τ n' y') W' c₂ X + mixedDeriv (centered g n' y') W' c₂ X -
        b * mixedDeriv (centered a n' y') W' c₂ X) =
      U + S + T + G - b * A := by
    rw [hU', hS', hT', hG', hA']
    ring
  rw [e₃, le_div_iff₀ hw0]
  have hab := abs_four_sub_mul_le U S T G A b
  have hab' := mul_le_mul_of_nonneg_right hab hw0.le
  nlinarith [hab', hU, hS, hT, hG, hbA, hnum, hsmall, hE0, hPx0]
end Main
theorem coldExpansionOfDensities_holds : ColdExpansionOfDensities := by
  intro ℓ t x b Cs CE ε e Na Dp u s τ g a H
  have F := H.densityBounds
  have sum_centered : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ V : TorusField n, IsCold ℓ.threshold V →
      ∑ y, centered (densitiesLessMultiple u s τ g a b) n y V =
        ∑ y, centered (sumOfFour u s τ g) n y V - b * ∑ y, centered a n y V := by
    intro n _ _ V _
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [centered, densitiesLessMultiple]
    ring
  exact
    { positive := H.positive
      smooth := fun n _ hn y W hc k c X =>
        (contDiffAt_sumOfFour H n hn y W hc k c X).sub
          (contDiffAt_const.mul (H.family.smooth n hn y W hc k c X))
      gauge := fun n _ hn y γ W hc => by
        simp only [densitiesLessMultiple, sumOfFour]
        rw [F.admissible_u.gauge n hn y γ W hc, F.admissible_s.gauge n hn y γ W hc,
          F.admissible_τ.gauge n hn y γ W hc, F.admissible_g.gauge n hn y γ W hc,
          H.family.gauge n hn y γ W hc]
      translation := fun n _ hn y v W hc => by
        simp only [densitiesLessMultiple, sumOfFour]
        rw [F.admissible_u.translation n hn y v W hc, F.admissible_s.translation n hn y v W hc,
          F.admissible_τ.translation n hn y v W hc, F.admissible_g.translation n hn y v W hc,
          H.family.translation n hn y v W hc]
      form := fun n _ hn W hc => by
        rw [sum_centered n hn W hc, H.log_eq n hn W hc, H.sum_eq_action n hn W hc]
        ring
      decay := fun n _ hn y W hc k c X hk1 hk3 hu =>
        decay_densitiesLessMultiple H n hn y W hc k c X hk1 hk3 hu
      local_density := fun n n' _ _ hn hn' y y' W W' m h2 h2' hc hc' ag k bb X hk hbox hu =>
        localComparison_densitiesLessMultiple H n n' hn hn' y y' W W' m h2 h2' hc hc' ag k bb X hk hbox hu
      no_curvature_term := fun A A' hA hA' =>
        limitForm_densitiesLessMultiple_hasSum_zero H A A' hA hA' }
end YangMills.Construction.TorusLumps.DensityExpansion
end
