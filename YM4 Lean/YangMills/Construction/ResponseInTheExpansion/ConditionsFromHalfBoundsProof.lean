import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfFourDensitiesProofForm
import YangMills.Construction.ResponseInTheExpansion.ConditionsFromHalfBounds
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepCosts ShareFamilies BlockAverages
section Calculus
variable {n k : ℕ}
theorem mixedDeriv_sub_const_mul (G H : TorusField n → ℝ) (b : ℝ) (W : TorusField n) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3)
    (hG : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => G (perturb c X σ W)) 0)
    (hH : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => H (perturb c X σ W)) 0) :
    mixedDeriv (fun V => G V - b * H V) W c X = mixedDeriv G W c X - b * mixedDeriv H W c X := by
  have hk' : ((k : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have hbH : ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => b • H (perturb c X σ W)) 0 := hH.const_smul b
  have e := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := k) (hG.of_le hk') (hbH.of_le hk')
  have e' := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := k) (a := b) (hH.of_le hk')
  unfold mixedDeriv
  have h1 : (fun σ : Fin k → ℝ => G (perturb c X σ W) - b * H (perturb c X σ W)) =
      (fun σ : Fin k → ℝ => G (perturb c X σ W)) - (fun σ : Fin k → ℝ => b • H (perturb c X σ W)) := rfl
  have h2 : (fun σ : Fin k → ℝ => b • H (perturb c X σ W)) = b • (fun σ : Fin k → ℝ => H (perturb c X σ W)) := rfl
  rw [h1, e, h2, e']
  rfl
end Calculus
section Bounds
variable {ℓ : StepParameters}
theorem weight_pos_of_params (ℓ : StepParameters) (m : ℕ) : 0 < ℓ.weight m := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
theorem isCold_trivialField (hσ : 0 < ℓ.threshold) (n : ℕ) : IsCold ℓ.threshold (trivialField n) := by apply _root_.YangMills.Construction.TorusLumps.DensityExpansion.trivialField_isCold <;> assumption
theorem hasCurvatureForm_sub_const_mul {F a : LocalDensity} {b c e : ℝ} (hfit : ℓ.Admissible)
    (hF : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
      ContDiffThreeAt (F n y) W)
    (ha : ∀ n [NeZero n], ℓ.n₀ ≤ n → ∀ (y : TorusSite n) (W : TorusField n), IsCold ℓ.threshold W →
      ContDiffThreeAt (a n y) W)
    (hFb : HasCurvatureForm F b) (hac : HasCurvatureForm a c) :
    HasCurvatureForm (fun n y W => F n y W - e * a n y W) (b - e * c) := by
  have hlim : ∀ (cc c' : (Fin 4 → ℤ) × Fin 4) (X X' : imaginaryQuaternions),
      Filter.Tendsto (fun n : ℕ => mixedDeriv ((fun n y W => F n y W - e * a n y W) n 0) (trivialField n)
        ![bondFrom 0 cc, bondFrom 0 c'] ![X, X']) Filter.atTop
        (𝓝 (secondDerivLimit F cc c' X X' - e * secondDerivLimit a cc c' X X')) := by
    intro cc c' X X'
    obtain ⟨v, hv⟩ := hFb.1 cc c' X X'
    obtain ⟨w, hw⟩ := hac.1 cc c' X X'
    have hv' : secondDerivLimit F cc c' X X' = v := hv.limUnder_eq
    have hw' : secondDerivLimit a cc c' X X' = w := hw.limUnder_eq
    rw [hv', hw']
    refine (hv.sub (hw.const_mul e)).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ℓ.n₀] with n hn
    have hn0 : n ≠ 0 := by
      have := hfit.n₀_ge
      omega
    haveI : NeZero n := ⟨hn0⟩
    exact (mixedDeriv_sub_const_mul (F n 0) (a n 0) e (trivialField n) _ _ (by norm_num)
      (hF n hn 0 (trivialField n) (isCold_trivialField hfit.σ_pos n) 2 _ _)
      (ha n hn 0 (trivialField n) (isCold_trivialField hfit.σ_pos n) 2 _ _)).symm
  refine ⟨fun cc c' X X' => ⟨_, hlim cc c' X X'⟩, fun A A' hA hA' => ?_⟩
  have hs := (hFb.2 A A' hA hA').sub ((hac.2 A A' hA hA').mul_left e)
  have hterm : limitFormTerm (fun n y W => F n y W - e * a n y W) A A' =
      fun cc => limitFormTerm F A A' cc - e * limitFormTerm a A A' cc := by
    funext cc
    exact (hlim cc.1 cc.2 _ _).limUnder_eq
  rw [hterm]
  have he : (b - e * c) * curvaturePairing A A' =
      b * curvaturePairing A A' - e * (c * curvaturePairing A A') := by
    ring
  rw [he]
  exact hs
theorem coldDensityBounds_sub_of_half {E η₃ b Ca : ℝ} {F a : LocalDensity} (hfit : ℓ.Admissible) (hE : 0 ≤ E)
    (hη : 0 < η₃) (hη1 : η₃ ≤ 1)
    (hF : HalfDensityBounds ℓ E η₃ F) (ha : IsCurvatureFamily ℓ Ca a) (hb : |b| * Ca ≤ E / 2)
    (hfF : HasCurvatureForm F b) (hfa : HasCurvatureForm a 1) :
    ColdDensityBounds ℓ E (E / η₃) fun n y W => F n y W - b * a n y W := by
  have hEη : E ≤ E / η₃ := by
    rw [le_div_iff₀ hη]
    nlinarith
  refine ⟨fun n _ hn y W hW k c X => ?_, fun n _ hn y g W hW => ?_, fun n _ hn y u W hW => ?_,
    fun n _ hn y W hW k c X hk1 hk3 hX => ?_,
    fun n n' _ _ hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu => ?_, fun A A' hA hA' => ?_⟩
  · exact (hF.admissible.smooth n hn y W hW k c X).sub (contDiffAt_const.mul (ha.smooth n hn y W hW k c X))
  · simp only [hF.admissible.gauge n hn y g W hW, ha.gauge n hn y g W hW]
  · simp only [hF.admissible.translation n hn y u W hW, ha.translation n hn y u W hW]
  · have e := mixedDeriv_sub_const_mul (F n y) (a n y) b W c X hk3 (hF.admissible.smooth n hn y W hW k c X)
      (ha.smooth n hn y W hW k c X)
    have h1 := hF.decay n hn y W hW k c X hk1 hk3 hX
    have h2 := ha.decay n hn y W hW k c X hk1 hk3 hX
    have hw := weight_pos_of_params ℓ (supportDiam y c)
    set w := ℓ.weight (supportDiam y c) with hwdef
    set e₀ : ℝ := if k = 3 then E / η₃ else E with he₀
    have hEe : E ≤ e₀ := by
      simp only [he₀]
      split_ifs
      · exact hEη
      · exact le_rfl
    have h3 : |b * mixedDeriv (a n y) W c X| ≤ |b| * Ca / w := by
      rw [abs_mul, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    have h4 : |mixedDeriv (fun V => F n y V - b * a n y V) W c X| ≤ 1 / 2 * e₀ / w + |b| * Ca / w := by
      rw [e]
      exact (abs_sub _ _).trans (add_le_add h1 h3)
    refine h4.trans ?_
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hw.le
    linarith
  · have centered_eq : ∀ {p : ℕ} (z : TorusSite p), centered (fun n y W => F n y W - b * a n y W) p z =
        fun V => centeredFamily F p z V - b * centered a p z V := by
      intro p z
      funext V
      simp only [centered, centeredFamily]
      ring
    rw [centered_eq y, centered_eq y']
    have smoothF : ∀ {p : ℕ} [NeZero p] (hp : ℓ.n₀ ≤ p) (z : TorusSite p) (U : TorusField p)
        (hU : IsCold ℓ.threshold U) (c : Fin k → TorusBond p),
        ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => centeredFamily F p z (perturb c X σ U)) 0 := by
      intro p _ hp z U hU c
      exact (hF.admissible.smooth p hp z U hU k c X).sub contDiffAt_const
    have smoothA : ∀ {p : ℕ} [NeZero p] (hp : ℓ.n₀ ≤ p) (z : TorusSite p) (U : TorusField p)
        (hU : IsCold ℓ.threshold U) (c : Fin k → TorusBond p),
        ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => centered a p z (perturb c X σ U)) 0 := by
      intro p _ hp z U hU c
      exact (ha.smooth p hp z U hU k c X).sub contDiffAt_const
    have hk3 : k ≤ 3 := by omega
    rw [mixedDeriv_sub_const_mul _ _ b W _ X hk3 (smoothF hn y W cW _) (smoothA hn y W cW _),
      mixedDeriv_sub_const_mul _ _ b W' _ X hk3 (smoothF hn' y' W' cW' _) (smoothA hn' y' W' cW' _)]
    have h1 := hF.compare n n' hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu
    have h3 := ha.local_density n n' hn hn' y y' W W' m h2 h2' cW cW' ag k bb X hk hbox hu
    have hw := weight_pos_of_params ℓ m
    set A₁ := mixedDeriv (centeredFamily F n y) W (fun l => bondFrom y (bb l)) X
    set A₂ := mixedDeriv (centeredFamily F n' y') W' (fun l => bondFrom y' (bb l)) X
    set B₁ := mixedDeriv (centered a n y) W (fun l => bondFrom y (bb l)) X
    set B₂ := mixedDeriv (centered a n' y') W' (fun l => bondFrom y' (bb l)) X
    have h4 : |b * (B₁ - B₂)| ≤ |b| * Ca / ℓ.weight m := by
      rw [abs_mul, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    have h5 : A₁ - b * B₁ - (A₂ - b * B₂) = (A₁ - A₂) - b * (B₁ - B₂) := by ring
    rw [h5]
    refine (abs_sub _ _).trans ((add_le_add h1 h4).trans ?_)
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hw.le
    linarith
  · have hform := hasCurvatureForm_sub_const_mul (e := b) hfit hF.admissible.smooth ha.smooth hfF hfa
    have h0 := (hform.2 A A' hA hA').tsum_eq
    have : (b - b * 1) * curvaturePairing A A' = 0 := by ring
    rw [this] at h0
    exact h0
end Bounds
theorem coldBoundsFromHalfBounds_holds : ColdBoundsFromHalfBounds := by
  intro ℓ K t x al b Ca P G hfit hη hη1 hKa hKb hx hS hF hG hT hR hfF hfG hb₁ hb₂
  set a := levelShareFamily ℓ.coupling ℓ.side (t + 1) with ha
  have hEa : 0 ≤ K.Ka * x ^ (-(1 / 2) : ℝ) := mul_nonneg hKa (Real.rpow_nonneg hx.le _)
  have hEb : 0 ≤ K.Kb * x⁻¹ := mul_nonneg hKb (inv_nonneg.mpr hx.le)
  refine ⟨fun n y W => responseSubShare ℓ.coupling P al n y W - b * a n y W,
    fun n y W => G n y W - b * a n y W, ?_, ?_,
    coldDensityBounds_sub_of_half hfit hEa hη hη1 hF hS.isCurvatureFamily hb₁ hfF hS.hasForm,
    coldDensityBounds_sub_of_half hfit hEb hη hη1 hG hS.isCurvatureFamily hb₂ hfG hS.hasForm, hR⟩
  · intro n _ hn y W hW
    have hne : n ≠ 0 := NeZero.ne n
    have h1 : responseAtOne P n y W = P n y W (constOneWeight _) := dif_neg hne
    have h2 : responseAtOne P n y (trivialField n) = P n y (trivialField n) (constOneWeight _) := dif_neg hne
    have h3 : a n y W = levelShare ℓ.coupling ℓ.side (t + 1) Finset.univ y W := dif_neg hne
    have h4 : a n y (trivialField n) = 0 := by
      have : a n y (trivialField n) = levelShare ℓ.coupling ℓ.side (t + 1) Finset.univ y (trivialField n) :=
        dif_neg hne
      rw [this, hS.share_trivial n hn y]
    simp only [centeredResponse, centered, responseSubShare, h1, h2, ← ha]
    rw [h3, h4]
    ring
  · intro n _ hn W hW
    have h1 := hT.sum_eq n hn W hW
    have h2 := hS.sum_centered_eq n hn W hW
    have h3 : ∀ y, centered (fun n y W => G n y W - b * a n y W) n y W = centered G n y W - b * centered a n y W := by
      intro y
      simp only [centered]
      ring
    simp only [h3, Finset.sum_sub_distrib, ← Finset.mul_sum, h1]
    rw [← ha] at h2
    rw [h2]
    ring
end YangMills.Construction.WeightedResponses
end
