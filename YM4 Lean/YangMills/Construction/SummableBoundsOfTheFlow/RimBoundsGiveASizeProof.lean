import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionHasTheConditionsOfThirdOrderProof
import YangMills.Construction.SummableBoundsOfTheFlow.RimBoundsGiveASize
import YangMills.Construction.SummableBoundsOfTheFlow.SizeFromSquareBoundsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation
namespace YangMills.Construction.Estimates
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {p : ℝ → ℝ}
private theorem cutoffFactor_nonneg' (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
private theorem ballDensity_nonneg' (Φ : BondField ι → ℝ) (η : BondField ι) :
    0 ≤ ballDensity (cutoffFactor ρ p) Φ η :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => cutoffFactor_nonneg' _) (Real.exp_pos _).le
private theorem ballDensity_eq_zero_of_not_mem {Φ : BondField ι → ℝ} {η : BondField ι}
    (hη : ¬ (∀ b, ‖η b‖ < ρ)) :
    ballDensity (cutoffFactor ρ p) Φ η = 0 := by apply _root_.YangMills.SharedProofs.p11780 <;> assumption
private theorem isOpen_bondBalls : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by apply _root_.YangMills.SharedProofs.p5886 <;> assumption
private theorem ballExpectation_le_mul_sum {α : Type} {Φ f : BondField ι → ℝ} {I : Finset α}
    {g : α → BondField ι → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hint : ∀ i ∈ I, Integrable (fun η => g i η * ballDensity (cutoffFactor ρ p) Φ η))
    (hfi : Integrable (fun η => f η * ballDensity (cutoffFactor ρ p) Φ η))
    (hf : ∀ η, f η * ballDensity (cutoffFactor ρ p) Φ η ≤
      C * ∑ i ∈ I, g i η * ballDensity (cutoffFactor ρ p) Φ η) :
    ballExpectation (cutoffFactor ρ p) Φ f ≤ C * ∑ i ∈ I, ballExpectation (cutoffFactor ρ p) Φ (g i) := by
  unfold ballExpectation
  have hZ : 0 ≤ ∫ η, ballDensity (cutoffFactor ρ p) Φ η :=
    integral_nonneg fun η => ballDensity_nonneg' Φ η
  have h1 : ∫ η, f η * ballDensity (cutoffFactor ρ p) Φ η ≤
      C * ∑ i ∈ I, ∫ η, g i η * ballDensity (cutoffFactor ρ p) Φ η := by
    rw [← integral_finset_sum I hint, ← integral_const_mul]
    exact integral_mono hfi ((integrable_finsetSum I hint).const_mul C) hf
  calc _ ≤ (C * ∑ i ∈ I, ∫ η, g i η * ballDensity (cutoffFactor ρ p) Φ η) /
        ∫ η, ballDensity (cutoffFactor ρ p) Φ η := div_le_div_of_nonneg_right h1 hZ
    _ = _ := by rw [mul_div_assoc, Finset.sum_div]
private def momentConstant (Cr : ℕ → ℕ → ℕ → ℝ) (N q : ℕ) : ℝ :=
  1 + |Cr 1 q (q * N)| + |Cr 2 q (q * N)| + |Cr 3 q (q * N)|
private theorem one_le_momentConstant (Cr : ℕ → ℕ → ℕ → ℝ) (N q : ℕ) : 1 ≤ momentConstant Cr N q := by
  unfold momentConstant
  linarith [abs_nonneg (Cr 1 q (q * N)), abs_nonneg (Cr 2 q (q * N)), abs_nonneg (Cr 3 q (q * N))]
private theorem le_momentConstant (Cr : ℕ → ℕ → ℕ → ℝ) (N q : ℕ) (j : Fin 3) :
    Cr (j + 1) q (q * N) ≤ momentConstant Cr N q := by
  unfold momentConstant
  have a1 := abs_nonneg (Cr 1 q (q * N))
  have a2 := abs_nonneg (Cr 2 q (q * N))
  have a3 := abs_nonneg (Cr 3 q (q * N))
  have b1 := le_abs_self (Cr 1 q (q * N))
  have b2 := le_abs_self (Cr 2 q (q * N))
  have b3 := le_abs_self (Cr 3 q (q * N))
  fin_cases j
  · simp only [Fin.zero_eta, Fin.val_zero, zero_add]
    linarith
  · simp only [Fin.mk_one, Fin.val_one]
    linarith
  · simp only [Fin.reduceFinMk, Fin.val_two]
    linarith
theorem momentBound_of_cutoffDerivSum_bound {Cr : ℕ → ℕ → ℕ → ℝ} {n N q : ℕ} {x A : ℝ}
    {Φ F : BondField ι → ℝ}
    {S : Finset ι} (hx : 1 ≤ x) (hq : 1 ≤ q) (hA : 0 ≤ A) (hS : S.card ≤ n)
    (hderiv : ∀ (j q N' : ℕ) (b : ι), 1 ≤ j → 1 ≤ q →
      Integrable (fun η => |iteratedDeriv j p ‖η b‖| ^ q * ballDensity (cutoffFactor ρ p) Φ η) ∧
      ballExpectation (cutoffFactor ρ p) Φ (fun η => |iteratedDeriv j p ‖η b‖| ^ q) ≤ Cr j q N' * (x ^ N')⁻¹)
    (hm : AEStronglyMeasurable (fun η => |F η| ^ q * ballDensity (cutoffFactor ρ p) Φ η) volume)
    (hb : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |F η| ≤ A * ∑ b ∈ S, cutoffDerivSum p ‖η b‖) :
    MomentBound (cutoffFactor ρ p) Φ F q (A * (3 * (n : ℝ) + 1) * momentConstant Cr N q * (x ^ N)⁻¹) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  obtain ⟨Nn, hNn⟩ : ∃ Nn : ℝ, Nn = 3 * (n : ℝ) + 1 := ⟨_, rfl⟩
  have hNn1 : 1 ≤ Nn := by
    rw [hNn]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  rw [← hNn]
  obtain ⟨I, hI⟩ : ∃ I : Finset (ι × Fin 3), I = S ×ˢ Finset.univ := ⟨_, rfl⟩
  have hcard : (I.card : ℝ) ≤ Nn := by
    have h1 : I.card = S.card * 3 := by simp [hI]
    have h2 : (S.card : ℝ) ≤ n := by exact_mod_cast hS
    rw [h1, hNn]
    push_cast
    linarith
  obtain ⟨a, ha⟩ : ∃ a : ι × Fin 3 → BondField ι → ℝ,
    a = fun i η => |iteratedDeriv (i.2 + 1) p ‖η i.1‖| := ⟨_, rfl⟩
  have ha0 : ∀ i η, 0 ≤ a i η := fun i η => by rw [ha]; exact abs_nonneg _
  have hsum : ∀ η : BondField ι, ∑ b ∈ S, cutoffDerivSum p ‖η b‖ = ∑ i ∈ I, a i η := by
    intro η
    rw [hI, Finset.sum_product]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [ha, cutoffDerivSum, Fin.sum_univ_three]
  have hpow : ∀ η : BondField ι,
      (∑ i ∈ I, a i η) ^ (k + 1) ≤ Nn ^ k * ∑ i ∈ I, a i η ^ (k + 1) := by
    intro η
    rcases I.eq_empty_or_nonempty with h0 | h0
    · simp [h0]
    · have hc : (0 : ℝ) < I.card := by exact_mod_cast h0.card_pos
      have h1 := pow_sum_div_card_le_sum_pow (s := I) (f := fun i => a i η) (fun i _ => ha0 i η) k
      rw [div_le_iff₀ (pow_pos hc k)] at h1
      refine h1.trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc.le hcard k)
        (Finset.sum_nonneg fun i _ => pow_nonneg (ha0 i η) _)
  obtain ⟨C, hC⟩ : ∃ C, C = A ^ (k + 1) * Nn ^ k := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hpt : ∀ η, |F η| ^ (k + 1) * ballDensity (cutoffFactor ρ p) Φ η ≤
      C * ∑ i ∈ I, a i η ^ (k + 1) * ballDensity (cutoffFactor ρ p) Φ η := by
    intro η
    by_cases hη : ∀ b, ‖η b‖ < ρ
    · rw [← Finset.sum_mul, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (ballDensity_nonneg' Φ η)
      have h1 := hb η hη
      rw [hsum η] at h1
      calc |F η| ^ (k + 1) ≤ (A * ∑ i ∈ I, a i η) ^ (k + 1) :=
            pow_le_pow_left₀ (abs_nonneg _) h1 _
        _ = A ^ (k + 1) * (∑ i ∈ I, a i η) ^ (k + 1) := mul_pow _ _ _
        _ ≤ A ^ (k + 1) * (Nn ^ k * ∑ i ∈ I, a i η ^ (k + 1)) :=
            mul_le_mul_of_nonneg_left (hpow η) (by positivity)
        _ = _ := by rw [hC]; ring
    · simp [ballDensity_eq_zero_of_not_mem hη]
  have hint : ∀ i ∈ I, Integrable (fun η => a i η ^ (k + 1) * ballDensity (cutoffFactor ρ p) Φ η) := by
    intro i _
    have := (hderiv (i.2 + 1) (k + 1) 0 i.1 (by omega) (by omega)).1
    rw [ha]
    exact this
  have hfi : Integrable (fun η => |F η| ^ (k + 1) * ballDensity (cutoffFactor ρ p) Φ η) := by
    refine Integrable.mono' ((integrable_finsetSum I hint).const_mul C) hm
      (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (ballDensity_nonneg' Φ η))]
    exact hpt η
  refine ⟨hfi, ?_⟩
  have hmean := ballExpectation_le_mul_sum (f := fun η => |F η| ^ (k + 1))
    (g := fun i η => a i η ^ (k + 1)) hC0 hint hfi hpt
  refine hmean.trans ?_
  obtain ⟨X, hX⟩ : ∃ X, X = (x ^ N)⁻¹ := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hCm := one_le_momentConstant Cr N (k + 1)
  obtain ⟨M, hM⟩ : ∃ M, M = momentConstant Cr N (k + 1) := ⟨_, rfl⟩
  rw [← hM] at hCm ⊢
  have each : ∀ i ∈ I,
      ballExpectation (cutoffFactor ρ p) Φ (fun η => a i η ^ (k + 1)) ≤ M * X ^ (k + 1) := by
    intro i _
    have h1 := (hderiv (i.2 + 1) (k + 1) ((k + 1) * N) i.1 (by omega) (by omega)).2
    have h2 : (x ^ ((k + 1) * N))⁻¹ = X ^ (k + 1) := by
      rw [hX, mul_comm, pow_mul, inv_pow]
    have h3 := le_momentConstant Cr N (k + 1) i.2
    rw [← hM] at h3
    rw [h2] at h1
    rw [ha]
    exact h1.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
  have hs : ∑ i ∈ I, ballExpectation (cutoffFactor ρ p) Φ (fun η => a i η ^ (k + 1)) ≤
      I.card * (M * X ^ (k + 1)) := by
    have := Finset.sum_le_card_nsmul I _ _ each
    simpa using this
  have hMk : M ≤ M ^ (k + 1) := le_self_pow₀ hCm (by omega)
  rw [← hX]
  calc C * ∑ i ∈ I, ballExpectation (cutoffFactor ρ p) Φ (fun η => a i η ^ (k + 1))
      ≤ C * (I.card * (M * X ^ (k + 1))) := mul_le_mul_of_nonneg_left hs hC0
    _ ≤ C * (Nn * (M ^ (k + 1) * X ^ (k + 1))) := by
        gcongr
    _ = (A * Nn * M * X) ^ (k + 1) := by
        rw [hC]
        simp only [mul_pow, pow_succ]
        ring
private theorem MomentBound.of_le {Φ F : BondField ι → ℝ} {q : ℕ} {B B' : ℝ} (hB : 0 ≤ B) (h : B ≤ B')
    (hm : MomentBound (cutoffFactor ρ p) Φ F q B) : MomentBound (cutoffFactor ρ p) Φ F q B' :=
  ⟨hm.1, hm.2.trans (pow_le_pow_left₀ hB h q)⟩
theorem localSizeOfCutoffDerivBound : localSizeOfCutoffDerivBoundStatement := by
  intro ρ p Cr n N K hρ hK
  refine ⟨fun q => K * (3 * (n : ℝ) + 1) * momentConstant Cr N q, fun q => ?_, ?_⟩
  · have := one_le_momentConstant Cr N q
    positivity
  intro ι _ _ x κ h Φ S dZ H hx hh hS hd hderiv hZ hdiff hH hG
  have hU := isOpen_bondBalls (ι := ι) (ρ := ρ)
  refine ⟨fun η hη => (hdiff η hη).differentiableAt (hU.mem_nhds hη), 0, fun q hq => ⟨?_, fun b => ?_⟩⟩
  · have hAE : AEStronglyMeasurable ({η : BondField ι | ∀ b, ‖η b‖ < ρ}.indicator H) volume :=
      (aestronglyMeasurable_indicator_iff hU.measurableSet).2
        (hdiff.continuousOn.aestronglyMeasurable hU.measurableSet)
    have e : (fun η => |H η - 0| ^ q * ballDensity (cutoffFactor ρ p) Φ η) =
        fun η => |{η : BondField ι | ∀ b, ‖η b‖ < ρ}.indicator H η| ^ q *
          ballDensity (cutoffFactor ρ p) Φ η := by
      funext η
      by_cases hη : ∀ b, ‖η b‖ < ρ
      · rw [Set.indicator_of_mem (show η ∈ {η : BondField ι | ∀ b, ‖η b‖ < ρ} from hη), sub_zero]
      · rw [ballDensity_eq_zero_of_not_mem hη]
        simp
    have hm : AEStronglyMeasurable
        (fun η => |H η - 0| ^ q * ballDensity (cutoffFactor ρ p) Φ η) volume := by
      rw [e]
      exact (hAE.aemeasurable.abs.pow_const q |>.aestronglyMeasurable).mul hd
    have := momentBound_of_cutoffDerivSum_bound (Cr := Cr) (n := n) (N := N) (F := fun η => H η - 0) hx hq
      (mul_nonneg hK hh) hS hderiv hm (fun η hη => by simpa using hH η hη)
    refine MomentBound.of_le (by have := one_le_momentConstant Cr N q; positivity) (le_of_eq ?_) this
    ring
  · have hmeas : Measurable (bondGradNorm H b) := by
      unfold bondGradNorm
      have h1 : Measurable (fderiv ℝ H) := measurable_fderiv ℝ H
      have h2 : Continuous fun L : BondField ι →L[ℝ] ℝ =>
          ‖L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)‖ :=
        (continuous_id.clm_comp continuous_const).norm
      exact h2.measurable.comp h1
    have hm : AEStronglyMeasurable
        (fun η => |bondGradNorm H b η| ^ q * ballDensity (cutoffFactor ρ p) Φ η) volume :=
      ((hmeas.abs.pow_const q).aestronglyMeasurable).mul hd
    by_cases hb : b ∈ S
    · have := momentBound_of_cutoffDerivSum_bound (Cr := Cr) (n := n) (N := N) (F := bondGradNorm H b) hx hq
        (mul_nonneg hK hh) hS hderiv hm (fun η hη => by
          have h1 := hG η hη b
          rw [if_pos hb] at h1
          rw [abs_of_nonneg (show 0 ≤ bondGradNorm H b η from norm_nonneg _)]
          exact h1)
      refine MomentBound.of_le (by have := one_le_momentConstant Cr N q; positivity) ?_ this
      rw [hZ b hb]
      have hsq : 1 ≤ Real.sqrt x := Real.one_le_sqrt.2 hx
      have hCm := one_le_momentConstant Cr N q
      have hB : 0 ≤ K * (3 * (n : ℝ) + 1) * momentConstant Cr N q * (h * (x ^ N)⁻¹) := by positivity
      simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
      calc K * h * (3 * (n : ℝ) + 1) * momentConstant Cr N q * (x ^ N)⁻¹ =
            K * (3 * (n : ℝ) + 1) * momentConstant Cr N q * (h * (x ^ N)⁻¹) := by ring
        _ ≤ K * (3 * (n : ℝ) + 1) * momentConstant Cr N q * (h * (x ^ N)⁻¹) * Real.sqrt x :=
            le_mul_of_one_le_right hB hsq
        _ = _ := by ring
    · have := momentBound_of_cutoffDerivSum_bound (Cr := Cr) (n := 0) (N := N) (S := ∅)
        (F := bondGradNorm H b) hx hq
        le_rfl (by simp) hderiv hm (fun η hη => by
          have h1 := hG η hη b
          rw [if_neg hb] at h1
          rw [abs_of_nonneg (show 0 ≤ bondGradNorm H b η from norm_nonneg _)]
          simpa using h1)
      refine MomentBound.of_le (by simp) ?_ this
      have hCm := one_le_momentConstant Cr N q
      simp only [zero_mul]
      positivity
end YangMills.Construction.Estimates
end
