import YangMills.Construction.CellOfTheFlow.LongClassesAreRareProof
import YangMills.Construction.ClusterExpansionOfAStep.ConditionalLawsOfAWeight
import YangMills.Construction.LawByMomentsOfTheFlow.NearCaseFunctionsSplitOverTheGasProof
import YangMills.Construction.TransfersOffTheWalk.CovarianceOfFarSpins
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction.Dobrushin
namespace LocalDecoupling
private def clip (T x : ℝ) : ℝ := max (-T) (min x T)
private theorem abs_clip_le_level {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : |clip T x| ≤ T := by
  unfold clip
  refine abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
private theorem abs_clip_le_abs {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : |clip T x| ≤ |x| := by
  unfold clip
  refine abs_le.mpr ⟨le_max_of_le_right (le_min (neg_abs_le x) ?_), max_le ?_ ((min_le_left _ _).trans (le_abs_self x))⟩
  · linarith [abs_nonneg x]
  · linarith [abs_nonneg x]
private theorem clip_eq_self {T x : ℝ} (h : |x| ≤ T) : clip T x = x := by
  unfold clip
  obtain ⟨h1, h2⟩ := abs_le.mp h
  rw [min_eq_left h2, max_eq_right h1]
private theorem abs_sub_clip_le {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : |x - clip T x| ≤ |x| := by
  by_cases h : |x| ≤ T
  · rw [clip_eq_self h]
    simp
  · rcases le_total 0 x with h0 | h0
    · have hx : T ≤ x := by
        rw [abs_of_nonneg h0] at h
        linarith
      have e : clip T x = T := by
        unfold clip
        rw [min_eq_right hx, max_eq_right (by linarith)]
      rw [e, abs_of_nonneg h0, abs_of_nonneg (by linarith)]
      linarith
    · have hx : x ≤ -T := by
        rw [abs_of_nonpos h0] at h
        linarith
      have e : clip T x = -T := by
        unfold clip
        rw [min_eq_left (by linarith), max_eq_left hx]
      rw [e, abs_of_nonpos h0, abs_of_nonpos (by linarith)]
      linarith
private theorem one_add_pow_le_exp_half (K : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (1 + s) ^ K ≤ polyMomentConstant K * Real.exp (s / 2) := by
  have h1 := Real.pow_div_factorial_le_exp ((1 + s) / 2) (by positivity) K
  have hf : (0 : ℝ) < K.factorial := by exact_mod_cast K.factorial_pos
  rw [div_le_iff₀ hf] at h1
  have hh : Real.exp (1 / 2) ≤ 2 := by
    have e : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have h3 := Real.exp_one_lt_d9
    have h4 := Real.exp_pos (1 / 2)
    nlinarith
  have e2 : Real.exp ((1 + s) / 2) = Real.exp (1 / 2) * Real.exp (s / 2) := by
    rw [← Real.exp_add]
    ring_nf
  have h2 : (1 + s) ^ K = 2 ^ K * ((1 + s) / 2) ^ K := by
    rw [← mul_pow]
    congr 1
    ring
  rw [h2]
  unfold polyMomentConstant
  have hp : (0 : ℝ) < 2 ^ K := by positivity
  have h5 : ((1 + s) / 2) ^ K ≤ 2 * Real.exp (s / 2) * (K.factorial : ℝ) := by
    refine h1.trans ?_
    rw [e2]
    have := Real.exp_pos (s / 2)
    gcongr
  calc 2 ^ K * ((1 + s) / 2) ^ K ≤ 2 ^ K * (2 * Real.exp (s / 2) * (K.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left h5 hp.le
    _ = _ := by ring
private theorem polyMomentConstant_mono {a b : ℕ} (h : a ≤ b) : polyMomentConstant a ≤ polyMomentConstant b := by
  unfold polyMomentConstant
  have h1 : (a.factorial : ℝ) ≤ b.factorial := by exact_mod_cast Nat.factorial_le h
  have h2 : (2 : ℝ) ^ a ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) h
  gcongr
private theorem polyMomentConstant_nonneg (K : ℕ) : 0 ≤ polyMomentConstant K := by
  unfold polyMomentConstant
  positivity
private theorem abs_prod_sub_prod_le {ι : Type} (s : Finset ι) (a b B : ι → ℝ) {e : ℝ} (he : 0 ≤ e)
    (ha : ∀ g ∈ s, |a g| ≤ B g) (hb : ∀ g ∈ s, |b g| ≤ B g) (hd : ∀ g ∈ s, |a g - b g| ≤ e * B g) :
    |∏ g ∈ s, a g - ∏ g ∈ s, b g| ≤ (s.card : ℝ) * e * ∏ g ∈ s, B g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hB : ∀ g ∈ insert j s, 0 ≤ B g := fun g hg => (abs_nonneg _).trans (ha g hg)
    have ih' := ih (fun g hg => ha g (Finset.mem_insert_of_mem hg)) (fun g hg => hb g (Finset.mem_insert_of_mem hg))
      (fun g hg => hd g (Finset.mem_insert_of_mem hg))
    have hP : |∏ g ∈ s, a g| ≤ ∏ g ∈ s, B g := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun g _ => abs_nonneg _) fun g hg => ha g (Finset.mem_insert_of_mem hg)
    have hjm : j ∈ insert j s := Finset.mem_insert_self j s
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    have e1 : a j * ∏ g ∈ s, a g - b j * ∏ g ∈ s, b g =
        (a j - b j) * ∏ g ∈ s, a g + b j * (∏ g ∈ s, a g - ∏ g ∈ s, b g) := by ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have t1 : |a j - b j| * |∏ g ∈ s, a g| ≤ (e * B j) * ∏ g ∈ s, B g :=
      mul_le_mul (hd j hjm) hP (abs_nonneg _) (mul_nonneg he (hB j hjm))
    have t2 : |b j| * |∏ g ∈ s, a g - ∏ g ∈ s, b g| ≤ B j * ((s.card : ℝ) * e * ∏ g ∈ s, B g) :=
      mul_le_mul (hb j hjm) ih' (abs_nonneg _) (hB j hjm)
    push_cast
    nlinarith [t1, t2]
private theorem sum_biUnion_le_sum_sum {ι κ : Type} [DecidableEq κ] (s : Finset ι) (t : ι → Finset κ) (f : κ → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by apply _root_.YangMills.SharedProofs.p62010 <;> assumption
variable {I : Type} [DecidableEq I] {S : I → Type}
private theorem isAdmissible_vacateOutside (A : PairConstraint S) (M : Finset I) {σ : ∀ i, S i}
    (h : A.IsAdmissible σ) : A.IsAdmissible (vacateOutside A M σ) := by apply _root_.YangMills.SharedProofs.p71124 <;> assumption
private theorem measurable_vacateOutside [∀ i, MeasurableSpace (S i)] (A : PairConstraint S) (M : Finset I) :
    Measurable (vacateOutside A M) := by
  refine measurable_pi_lambda _ fun i => ?_
  unfold vacateOutside
  by_cases hi : i ∈ M
  · simp only [if_pos hi]
    exact measurable_pi_apply i
  · simp only [if_neg hi]
    exact measurable_const
end LocalDecoupling
open LocalDecoupling in
theorem localFunctionsDecouple (hCov : CovarianceDecayStatement) (hC : ActivityConditionalLawsStatement) :
    LocalFunctionsDecoupleStatement := by
  classical
  intro I _ _ S _ A m _ G z h c Q k M w p U Sc ε δ t hcol hw1 hfar hpm hSm hS0 hU hε hδ ht hkeep hsize hforget hmom
  obtain ⟨hprob, hgibbs, -, -⟩ := hC I S A m G z h
  set μ := A.gibbsLaw m G with hμ
  have hae : ∀ᵐ σ ∂μ, A.IsAdmissible σ := hgibbs.ae_admissible
  set W : (∀ i, S i) → ℝ := fun σ => Real.exp (Sc σ) with hWd
  have hWm : Measurable W := Real.measurable_exp.comp hSm
  have hW0 : ∀ σ, 0 ≤ W σ := fun σ => (Real.exp_pos _).le
  have hWi : Integrable W μ := by
    refine ⟨hWm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hW0)]
    exact lt_of_le_of_lt hmom (by simp)
  have hW2 : ∫ σ, W σ ∂μ ≤ 2 := by
    have e := ofReal_integral_eq_lintegral_ofReal hWi (Filter.Eventually.of_forall hW0)
    have e2 : ENNReal.ofReal (∫ σ, W σ ∂μ) ≤ ENNReal.ofReal 2 := by
      rw [e]
      simpa using hmom
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp e2
  have mean_le : ∀ (f : (∀ i, S i) → ℝ) (C : ℝ), AEStronglyMeasurable f μ → 0 ≤ C → (∀ᵐ σ ∂μ, |f σ| ≤ C * W σ) →
      Integrable f μ ∧ |∫ σ, f σ ∂μ| ≤ 2 * C := by
    intro f C hf hC0 hb
    have hi : Integrable f μ := (hWi.const_mul C).mono' hf (by simpa using hb)
    refine ⟨hi, (abs_integral_le_integral_abs).trans ?_⟩
    calc ∫ σ, |f σ| ∂μ ≤ ∫ σ, C * W σ ∂μ := integral_mono_ae hi.abs (hWi.const_mul C) hb
      _ = C * ∫ σ, W σ ∂μ := integral_const_mul _ _
      _ ≤ C * 2 := mul_le_mul_of_nonneg_left hW2 hC0
      _ = _ := by ring
  set T : Fin Q → ℝ := fun g => U g * (1 + t) ^ k g with hT
  have hT0 : ∀ g, 0 ≤ T g := fun g => mul_nonneg (hU g) (by positivity)
  set P : Fin Q → (∀ i, S i) → ℝ := fun g σ => p g (vacateOutside A (M g) σ) with hP
  set F : Fin Q → (∀ i, S i) → ℝ := fun g σ => clip (T g) (P g σ) with hF
  have hPm : ∀ g, Measurable (P g) := fun g => (hpm g).comp (measurable_vacateOutside A (M g))
  have hFm : ∀ g, Measurable (F g) := fun g => by
    simp only [hF, clip]
    exact measurable_const.max ((hPm g).min measurable_const)
  have hFT : ∀ g σ, |F g σ| ≤ T g := fun g σ => abs_clip_le_level (hT0 g) _
  set V : Fin Q → (∀ i, S i) → ℝ := fun g σ => U g * (1 + Sc σ) ^ k g with hV
  have hV0 : ∀ g σ, 0 ≤ V g σ := fun g σ => mul_nonneg (hU g) (pow_nonneg (by linarith [hS0 σ]) _)
  set io : (∀ i, S i) → ℝ := fun σ => Real.exp ((Sc σ - t) / 2) with hio
  have hptw : ∀ g σ, A.IsAdmissible σ →
      |p g σ| ≤ V g σ ∧ |F g σ| ≤ V g σ ∧ |p g σ - F g σ| ≤ (ε + io σ) * V g σ := by
    intro g σ hσ
    have hk := isAdmissible_vacateOutside A (M g) hσ
    have h1 : |P g σ| ≤ V g σ := by
      refine (hsize g _ hk).trans ?_
      simp only [hV]
      refine mul_le_mul_of_nonneg_left ?_ (hU g)
      exact pow_le_pow_left₀ (by linarith [hS0 (vacateOutside A (M g) σ)]) (by linarith [hkeep g σ]) _
    have h2 : |F g σ| ≤ |P g σ| := abs_clip_le_abs (hT0 g) _
    have h3 : |P g σ - F g σ| ≤ io σ * V g σ := by
      by_cases hs : Sc σ ≤ t
      · have hle : |P g σ| ≤ T g := by
          refine h1.trans ?_
          simp only [hV, hT]
          refine mul_le_mul_of_nonneg_left ?_ (hU g)
          exact pow_le_pow_left₀ (by linarith [hS0 σ]) (by linarith) _
        have e : F g σ = P g σ := clip_eq_self hle
        rw [e, sub_self, abs_zero]
        exact mul_nonneg (Real.exp_pos _).le (hV0 g σ)
      · have hi : 1 ≤ io σ := Real.one_le_exp (by
          have : t < Sc σ := not_le.mp hs
          linarith)
        calc |P g σ - F g σ| ≤ |P g σ| := abs_sub_clip_le (hT0 g) _
          _ ≤ V g σ := h1
          _ ≤ io σ * V g σ := le_mul_of_one_le_left (hV0 g σ) hi
    refine ⟨hsize g σ hσ, h2.trans h1, ?_⟩
    have h4 := hforget g σ hσ
    have e : p g σ - F g σ = (p g σ - P g σ) + (P g σ - F g σ) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    calc _ ≤ ε * V g σ + io σ * V g σ := add_le_add h4 h3
      _ = _ := by ring
  set K := ∑ g, k g with hK
  set cK := polyMomentConstant K with hcK
  have hcK0 : 0 ≤ cK := polyMomentConstant_nonneg K
  set X := ∏ g, U g with hX
  have hX0 : 0 ≤ X := Finset.prod_nonneg fun g _ => hU g
  set E₁ := ε + Real.exp (-(t / 2)) with hE₁
  have hE₁0 : 0 ≤ E₁ := add_nonneg hε (Real.exp_pos _).le
  have hio0 : ∀ σ, 0 ≤ io σ := fun σ => (Real.exp_pos _).le
  have hsW : ∀ σ, Real.exp (Sc σ / 2) ≤ W σ := fun σ => Real.exp_le_exp.mpr (by linarith [hS0 σ])
  have hs_one : ∀ σ k', (1 + Sc σ) ^ k' ≤ polyMomentConstant k' * W σ := fun σ k' =>
    (one_add_pow_le_exp_half k' (hS0 σ)).trans (mul_le_mul_of_nonneg_left (hsW σ) (polyMomentConstant_nonneg _))
  have hs_exp : ∀ σ k', (1 + Sc σ) ^ k' * (ε + io σ) ≤ polyMomentConstant k' * (W σ * E₁) := by
    intro σ k'
    have h1 := one_add_pow_le_exp_half k' (hS0 σ)
    have e1 : Real.exp (Sc σ / 2) * (ε + io σ) ≤ W σ * E₁ := by
      have b : Real.exp (Sc σ / 2) * io σ = W σ * Real.exp (-(t / 2)) := by
        simp only [hio, hWd]
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
      calc Real.exp (Sc σ / 2) * (ε + io σ) = Real.exp (Sc σ / 2) * ε + Real.exp (Sc σ / 2) * io σ := by ring
        _ ≤ W σ * ε + W σ * Real.exp (-(t / 2)) := by
            rw [b]
            exact add_le_add (mul_le_mul_of_nonneg_right (hsW σ) hε) le_rfl
        _ = _ := by
            simp only [hE₁]
            ring
    calc (1 + Sc σ) ^ k' * (ε + io σ) ≤ (polyMomentConstant k' * Real.exp (Sc σ / 2)) * (ε + io σ) :=
          mul_le_mul_of_nonneg_right h1 (add_nonneg hε (hio0 σ))
      _ = polyMomentConstant k' * (Real.exp (Sc σ / 2) * (ε + io σ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left e1 (polyMomentConstant_nonneg _)
  have hprodV : ∀ σ, ∏ g, V g σ = X * (1 + Sc σ) ^ K := by
    intro σ
    simp only [hV]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hpM : Measurable fun σ => ∏ g, p g σ := Finset.measurable_prod _ fun g _ => hpm g
  have hFM : Measurable fun σ => ∏ g, F g σ := Finset.measurable_prod _ fun g _ => hFm g
  have hVW : ∀ σ, ∏ g, V g σ ≤ X * cK * W σ := by
    intro σ
    rw [hprodV, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hs_one σ K) hX0
  have hIp := mean_le (fun σ => ∏ g, p g σ) (X * cK) hpM.aestronglyMeasurable (mul_nonneg hX0 hcK0) (by
    filter_upwards [hae] with σ hσ
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod (fun g _ => abs_nonneg _) fun g _ => (hptw g σ hσ).1).trans (hVW σ))
  have hIF := mean_le (fun σ => ∏ g, F g σ) (X * cK) hFM.aestronglyMeasurable (mul_nonneg hX0 hcK0) (by
    filter_upwards [hae] with σ hσ
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod (fun g _ => abs_nonneg _) fun g _ => (hptw g σ hσ).2.1).trans (hVW σ))
  have t1 : |∫ σ, ∏ g, p g σ ∂μ - ∫ σ, ∏ g, F g σ ∂μ| ≤ 2 * ((Q : ℝ) * X * cK * E₁) := by
    have h := mean_le (fun σ => ∏ g, p g σ - ∏ g, F g σ) ((Q : ℝ) * X * cK * E₁)
      (hpM.sub hFM).aestronglyMeasurable (by positivity) (by
      filter_upwards [hae] with σ hσ
      have h1 := abs_prod_sub_prod_le Finset.univ (fun g => p g σ) (fun g => F g σ) (fun g => V g σ)
        (add_nonneg hε (hio0 σ)) (fun g _ => (hptw g σ hσ).1) (fun g _ => (hptw g σ hσ).2.1)
        (fun g _ => (hptw g σ hσ).2.2)
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      refine h1.trans ?_
      rw [hprodV]
      have h2 := hs_exp σ K
      calc (Q : ℝ) * (ε + io σ) * (X * (1 + Sc σ) ^ K) = (Q : ℝ) * X * ((1 + Sc σ) ^ K * (ε + io σ)) := by ring
        _ ≤ (Q : ℝ) * X * (cK * (W σ * E₁)) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring)
    rw [integral_sub hIp.1 hIF.1] at h
    exact h.2
  have hone : ∀ g, Integrable (p g) μ ∧ Integrable (F g) μ ∧ |∫ σ, p g σ ∂μ| ≤ 2 * (polyMomentConstant (k g) * U g) ∧
      |∫ σ, F g σ ∂μ| ≤ 2 * (polyMomentConstant (k g) * U g) ∧
      |∫ σ, p g σ ∂μ - ∫ σ, F g σ ∂μ| ≤ E₁ * (2 * (polyMomentConstant (k g) * U g)) := by
    intro g
    have hc0 := polyMomentConstant_nonneg (k g)
    have hVb : ∀ σ, V g σ ≤ polyMomentConstant (k g) * U g * W σ := fun σ => by
      simp only [hV]
      calc U g * (1 + Sc σ) ^ k g ≤ U g * (polyMomentConstant (k g) * W σ) :=
            mul_le_mul_of_nonneg_left (hs_one σ _) (hU g)
        _ = _ := by ring
    have a1 := mean_le (p g) (polyMomentConstant (k g) * U g) (hpm g).aestronglyMeasurable (mul_nonneg hc0 (hU g)) (by
      filter_upwards [hae] with σ hσ
      exact (hptw g σ hσ).1.trans (hVb σ))
    have a2 := mean_le (F g) (polyMomentConstant (k g) * U g) (hFm g).aestronglyMeasurable (mul_nonneg hc0 (hU g)) (by
      filter_upwards [hae] with σ hσ
      exact (hptw g σ hσ).2.1.trans (hVb σ))
    have a3 := mean_le (fun σ => p g σ - F g σ) (polyMomentConstant (k g) * U g * E₁)
      ((hpm g).sub (hFm g)).aestronglyMeasurable (mul_nonneg (mul_nonneg hc0 (hU g)) hE₁0) (by
      filter_upwards [hae] with σ hσ
      refine (hptw g σ hσ).2.2.trans ?_
      simp only [hV]
      have h2 := hs_exp σ (k g)
      calc (ε + io σ) * (U g * (1 + Sc σ) ^ k g) = U g * ((1 + Sc σ) ^ k g * (ε + io σ)) := by ring
        _ ≤ U g * (polyMomentConstant (k g) * (W σ * E₁)) := mul_le_mul_of_nonneg_left h2 (hU g)
        _ = _ := by ring)
    rw [integral_sub a1.1 a2.1] at a3
    refine ⟨a1.1, a2.1, a1.2, a2.2, a3.2.trans (le_of_eq (by ring))⟩
  have hBprod : ∏ g, (2 * (polyMomentConstant (k g) * U g)) ≤ (2 * cK) ^ Q * X := by
    have e : ∏ g, (2 * (polyMomentConstant (k g) * U g)) = (∏ g, (2 * polyMomentConstant (k g))) * X := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun g _ => by ring
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ hX0
    calc ∏ g, (2 * polyMomentConstant (k g)) ≤ ∏ _g : Fin Q, (2 * cK) :=
          Finset.prod_le_prod (fun g _ => mul_nonneg (by norm_num) (polyMomentConstant_nonneg _)) fun g _ =>
            mul_le_mul_of_nonneg_left (polyMomentConstant_mono (Finset.single_le_sum (f := k)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ g))) (by norm_num)
      _ = _ := by simp
  have t3 : |∏ g, ∫ σ, p g σ ∂μ - ∏ g, ∫ σ, F g σ ∂μ| ≤ (Q : ℝ) * E₁ * ((2 * cK) ^ Q * X) := by
    have h1 := abs_prod_sub_prod_le Finset.univ (fun g => ∫ σ, p g σ ∂μ) (fun g => ∫ σ, F g σ ∂μ)
      (fun g => 2 * (polyMomentConstant (k g) * U g)) hE₁0 (fun g _ => (hone g).2.2.1) (fun g _ => (hone g).2.2.2.1)
      (fun g _ => (hone g).2.2.2.2)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hBprod (by positivity))
  have hFr : ∀ g, DependsOnlyOn (M g) (F g) := by
    intro g σ σ' hag
    have e : vacateOutside A (M g) σ = vacateOutside A (M g) σ' := by
      funext i
      unfold vacateOutside
      by_cases hi : i ∈ M g
      · simp only [if_pos hi]
        exact hag i hi
      · simp only [if_neg hi]
    simp only [hF, hP, e]
  have hz0 := h.activity_nonneg
  have key : ∀ s : Finset (Fin Q), |∫ σ, ∏ g ∈ s, F g σ ∂μ - ∏ g ∈ s, ∫ σ, F g σ ∂μ| ≤
      96 * (s.card : ℝ) * (∏ g ∈ s, T g) * ((Q : ℝ) * δ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      have hB₂ : 0 ≤ ∏ g ∈ s, T g := Finset.prod_nonneg fun g _ => hT0 g
      have hF₂m : Measurable fun σ => ∏ g ∈ s, F g σ := Finset.measurable_prod _ fun g _ => hFm g
      have hF₂b : ∀ σ, |∏ g ∈ s, F g σ| ≤ ∏ g ∈ s, T g := fun σ => by
        rw [Finset.abs_prod]
        exact Finset.prod_le_prod (fun g _ => abs_nonneg _) fun g _ => hFT g σ
      have hF₂r : DependsOnlyOn (s.biUnion M) fun σ => ∏ g ∈ s, F g σ := by
        intro σ σ' hag
        refine Finset.prod_congr rfl fun g hg => hFr g σ σ' fun i hi => hag i ?_
        exact Finset.mem_biUnion.mpr ⟨g, hg, hi⟩
      have hcov := hCov I S A m G z h c (w j) (M j) (s.biUnion M) (F j) (fun σ => ∏ g ∈ s, F g σ) (T j)
        (∏ g ∈ s, T g) (hcol j) (hw1 j) (hFm j) hF₂m (hFT j) hF₂b (hFr j) hF₂r
      have hsum : ∑ i ∈ s.biUnion M, w j i * z i ≤ (Q : ℝ) * δ := by
        have hnn : ∀ i, 0 ≤ w j i * z i := fun i => mul_nonneg ((hcol j).weight_pos i).le (hz0 i)
        have h1 := sum_biUnion_le_sum_sum s M (fun i => w j i * z i) hnn
        have h2 : ∑ g ∈ s, ∑ i ∈ M g, w j i * z i ≤ ∑ _g ∈ s, δ :=
          Finset.sum_le_sum fun g hg => hfar j g fun e => hj (e ▸ hg)
        have h3 : (s.card : ℝ) ≤ Q := by
          have := Finset.card_le_univ s
          simp only [Fintype.card_fin] at this
          exact_mod_cast this
        have h4 : ∑ _g ∈ s, δ = (s.card : ℝ) * δ := by simp
        have h5 := mul_le_mul_of_nonneg_right h3 hδ
        linarith
      have hFj : |∫ σ, F j σ ∂μ| ≤ T j := by
        have := norm_integral_le_of_norm_le_const (μ := μ) (f := F j) (C := T j)
          (Filter.Eventually.of_forall fun σ => by
            rw [Real.norm_eq_abs]
            exact hFT j σ)
        simpa using this
      simp only [Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
      have e : ∫ σ, F j σ * ∏ g ∈ s, F g σ ∂μ - (∫ σ, F j σ ∂μ) * ∏ g ∈ s, ∫ σ, F g σ ∂μ =
          (∫ σ, F j σ * ∏ g ∈ s, F g σ ∂μ - (∫ σ, F j σ ∂μ) * ∫ σ, ∏ g ∈ s, F g σ ∂μ) +
            (∫ σ, F j σ ∂μ) * (∫ σ, ∏ g ∈ s, F g σ ∂μ - ∏ g ∈ s, ∫ σ, F g σ ∂μ) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      have a1 : |∫ σ, F j σ * ∏ g ∈ s, F g σ ∂μ - (∫ σ, F j σ ∂μ) * ∫ σ, ∏ g ∈ s, F g σ ∂μ| ≤
          96 * T j * (∏ g ∈ s, T g) * ((Q : ℝ) * δ) :=
        hcov.trans (mul_le_mul_of_nonneg_left hsum (mul_nonneg (mul_nonneg (by norm_num) (hT0 j)) hB₂))
      have a2 : |∫ σ, F j σ ∂μ| * |∫ σ, ∏ g ∈ s, F g σ ∂μ - ∏ g ∈ s, ∫ σ, F g σ ∂μ| ≤
          T j * (96 * (s.card : ℝ) * (∏ g ∈ s, T g) * ((Q : ℝ) * δ)) :=
        mul_le_mul hFj ih (abs_nonneg _) (hT0 j)
      push_cast
      nlinarith [a1, a2]
  have t2 := key Finset.univ
  have hTprod : ∏ g, T g = X * (1 + t) ^ K := by
    simp only [hT]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hTprod] at t2
  simp only [Finset.card_univ, Fintype.card_fin] at t2
  set E₂ := (1 + t) ^ K * δ with hE₂
  have hE₂0 : 0 ≤ E₂ := by positivity
  have tri : |∫ σ, ∏ g, p g σ ∂μ - ∏ g, ∫ σ, p g σ ∂μ| ≤
      |∫ σ, ∏ g, p g σ ∂μ - ∫ σ, ∏ g, F g σ ∂μ| + |∫ σ, ∏ g, F g σ ∂μ - ∏ g, ∫ σ, F g σ ∂μ| +
        |∏ g, ∫ σ, p g σ ∂μ - ∏ g, ∫ σ, F g σ ∂μ| := by
    rw [abs_sub_comm (∏ g, ∫ σ, p g σ ∂μ)]
    have e3 : ∀ a b c d : ℝ, a - d = (a - b) + (b - c) + (c - d) := fun a b c d => by ring
    rw [e3 (∫ σ, ∏ g, p g σ ∂μ) (∫ σ, ∏ g, F g σ ∂μ) (∏ g, ∫ σ, F g σ ∂μ) (∏ g, ∫ σ, p g σ ∂μ)]
    exact abs_add_three _ _ _
  unfold decouplingConstant
  have q0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have b1 : 0 ≤ (2 * (Q : ℝ) * cK) * X * E₂ := by positivity
  have b2 : 0 ≤ (96 * (Q : ℝ) ^ 2) * X * E₁ := by positivity
  have b3 : 0 ≤ ((Q : ℝ) * (2 * cK) ^ Q) * X * E₂ := by positivity
  have e2 : 96 * (Q : ℝ) * (X * (1 + t) ^ K) * ((Q : ℝ) * δ) = (96 * (Q : ℝ) ^ 2) * X * E₂ := by
    simp only [hE₂]
    ring
  rw [e2] at t2
  nlinarith [tri, t1, t2, t3, b1, b2, b3]
end YangMills.Construction.Dobrushin
end
