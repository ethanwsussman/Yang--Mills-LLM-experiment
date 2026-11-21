import YangMills.Construction.ClusterExpansionOfAStep.TheHotHalfProof
import YangMills.Construction.FreeEnergiesOfTheFlow.MeanOfTheVariableOfAStepProof
import YangMills.Construction.ResponseInTheExpansion.DerivativesOfTheGasOfAResponse
import YangMills.Construction.ResponseInTheExpansion.GasOfAResponseAtColdFields
import YangMills.Construction.ResponseInTheExpansion.GasResponseReadsItsSite
import YangMills.Construction.ResponseInTheExpansion.ResponseOfTheGas
import YangMills.Construction.ResponseInTheExpansion.ResponseOfTheGasAtEveryRadius
import YangMills.Construction.ResponseInTheExpansion.WeightsThatAgreeAtABlock
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.WeightedResponses.AtColdFields
open TorusFields TorusLumps StepSettings RenormalizationStepParameters StepGas StepFloors BlockAverages BlockOffsets
  ColdStepAtMirrorFrames AgreeingWeights
section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem iteratedFDeriv_perm_of_le_three {u : E → ℝ} (hu : ContDiff ℝ 3 u) (z : E) (j : ℕ) (hj : j ≤ 3)
    (σ : Equiv.Perm (Fin j))
    (m : Fin j → E) : iteratedFDeriv ℝ j u z (m ∘ σ) = iteratedFDeriv ℝ j u z m := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockDensities.iteratedFDeriv_perm_of_le_three <;> assumption
end Calculus
section Moves
variable {n : ℕ}
private theorem isCold_perturb {k : ℕ} (hk : k ≤ 3) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X)
    (τ : Fin k → ℝ) (V : TorusField n) (s : ℝ) (hs : 0 < s) (hV : IsCold s V) (hτ : ‖τ‖ ≤ s / 2 ^ 10) :
    IsCold (9 / 8 * s) (perturb c X τ V) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockDensities.isCold_perturb <;> assumption
private theorem two_mul_supDist_le [NeZero n] (x y : TorusSite n) : 2 * supDist x y ≤ n := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.two_mul_supDist_le <;> assumption
end Moves
section Sizes
private theorem weight_le_of_le (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (hn1 : 0 < ℓ.n₁) (hrt : 0 < ℓ.rt) (m N : ℕ)
    (hN : N ≤ 2 * m + 4) (p : ℕ)
    (hw : ℓ.weight N = max 1 (((N : ℝ) / ℓ.n₁) ^ p) * Real.exp (ℓ.weightRate * N)) :
    ℓ.weight N ≤ (2 + 4 / ℓ.n₁) ^ p * (1 + m / ℓ.n₁) ^ p *
      (Real.exp (ℓ.rt / 2 ^ 8) * Real.exp (ℓ.rt * m / 2 ^ 9)) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockDensities.weight_le_of_le <;> assumption
private theorem weight_pos' (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (N : ℕ) : 0 < ℓ.weight N := by apply _root_.YangMills.Construction.WilsonExpansion.weight_pos <;> assumption
private theorem interpolation_le_aux (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (hrt : 0 < ℓ.rt) (ch x C Ck τ₀ P Q : ℝ) (hch : 0 < ch)
    (hx1 : 1 ≤ x) (hC : 0 ≤ C) (hCk : 0 < Ck) (hτ0 : 0 < τ₀) (hτ1 : τ₀ ≤ 1) (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q)
    (hK : Ck * (2 / τ₀ ^ 3 + 8) * Q * Real.exp (ℓ.rt / 2 ^ 8) ≤ x) (m N k : ℕ)
    (hy : x ^ (C + 1) * P * Real.exp (-(1 / 4) * (ch * x + ℓ.rt * m / 2 ^ 8)) ≤ 1)
    (hWle : ℓ.weight N ≤ Q * P * (Real.exp (ℓ.rt / 2 ^ 8) * Real.exp (ℓ.rt * m / 2 ^ 9))) (hk : k ≤ 3) :
    Ck * ((2 * Real.exp (-(ch * x) - ℓ.rt * m / 2 ^ 8)) / τ₀ ^ k +
        (2 * Real.exp (-(ch * x) - ℓ.rt * m / 2 ^ 8)) ^ (1 - (k : ℝ) / (40 : ℕ)) *
          (4 * x ^ C) ^ ((k : ℝ) / (40 : ℕ))) ≤
      Real.exp (-(5 * (ch * x) / 8)) / ℓ.weight N := by
  have hx0 : 0 < x := by linarith
  set u : ℝ := ch * x + ℓ.rt * m / 2 ^ 8 with hu_def
  have hu : 0 ≤ u := by positivity
  have he : -(ch * x) - ℓ.rt * m / 2 ^ 8 = -u := by rw [hu_def]; ring
  rw [he]
  set E : ℝ := Real.exp (-(37 / 40) * u) with hE_def
  have hE0 : 0 < E := Real.exp_pos _
  have hxC : 1 ≤ x ^ C := Real.one_le_rpow hx1 hC
  have hkr : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have t1 : 2 * Real.exp (-u) / τ₀ ^ k ≤ 2 * E / τ₀ ^ 3 := by
    have h1 : Real.exp (-u) ≤ E := Real.exp_le_exp.mpr (by nlinarith)
    have h2 : τ₀ ^ 3 ≤ τ₀ ^ k := pow_le_pow_of_le_one hτ0.le hτ1 hk
    have h3 : 0 < τ₀ ^ 3 := by positivity
    exact div_le_div₀ (by positivity) (by linarith) h3 h2
  have ha2 : 1 - (k : ℝ) / (40 : ℕ) ≤ 1 := by
    push_cast
    have : 0 ≤ (k : ℝ) / 40 := by positivity
    linarith
  have t2 : (2 * Real.exp (-u)) ^ (1 - (k : ℝ) / (40 : ℕ)) ≤ 2 * E := by
    rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
    have h1 : (2 : ℝ) ^ (1 - (k : ℝ) / (40 : ℕ)) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - (k : ℝ) / (40 : ℕ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) ha2
        _ = 2 := Real.rpow_one 2
    have h2 : Real.exp (-u * (1 - (k : ℝ) / (40 : ℕ))) ≤ E := Real.exp_le_exp.mpr (by nlinarith)
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)
  have hb4 : 1 ≤ 4 * x ^ C := by linarith
  have t3 : (4 * x ^ C) ^ ((k : ℝ) / (40 : ℕ)) ≤ 4 * x ^ C := by
    have hb : (k : ℝ) / (40 : ℕ) ≤ 1 := by
      push_cast
      linarith
    calc (4 * x ^ C) ^ ((k : ℝ) / (40 : ℕ)) ≤ (4 * x ^ C) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb4 hb
      _ = 4 * x ^ C := Real.rpow_one _
  have step1 : Ck * ((2 * Real.exp (-u)) / τ₀ ^ k + (2 * Real.exp (-u)) ^ (1 - (k : ℝ) / (40 : ℕ)) *
      (4 * x ^ C) ^ ((k : ℝ) / (40 : ℕ))) ≤ Ck * (2 / τ₀ ^ 3 + 8) * x ^ C * E := by
    have h1 : (2 * Real.exp (-u)) ^ (1 - (k : ℝ) / (40 : ℕ)) * (4 * x ^ C) ^ ((k : ℝ) / (40 : ℕ)) ≤
        2 * E * (4 * x ^ C) :=
      mul_le_mul t2 t3 (Real.rpow_nonneg (by positivity) _) (by positivity)
    have h2 : 2 * E / τ₀ ^ 3 ≤ 2 / τ₀ ^ 3 * x ^ C * E := by
      have : 2 * E / τ₀ ^ 3 = 2 / τ₀ ^ 3 * 1 * E := by ring
      rw [this]
      have h20 : 0 ≤ 2 / τ₀ ^ 3 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxC h20) hE0.le
    have h3 : Ck * (2 / τ₀ ^ 3 + 8) * x ^ C * E = Ck * (2 / τ₀ ^ 3 * x ^ C * E + 2 * E * (4 * x ^ C)) := by
      ring
    rw [h3]
    exact mul_le_mul_of_nonneg_left (by linarith) hCk.le
  have hW0 : 0 < ℓ.weight N := weight_pos' ℓ N
  refine step1.trans ?_
  rw [le_div_iff₀ hW0]
  have hpow : x ^ (C + 1) = x ^ C * x := Real.rpow_add_one hx0.ne' C
  have hyy := hy
  rw [hpow] at hyy
  set S := Real.exp (ℓ.rt / 2 ^ 8) with hS
  set T := Real.exp (ℓ.rt * m / 2 ^ 9) with hT
  calc Ck * (2 / τ₀ ^ 3 + 8) * x ^ C * E * ℓ.weight N
      ≤ Ck * (2 / τ₀ ^ 3 + 8) * x ^ C * E * (Q * P * (S * T)) :=
        mul_le_mul_of_nonneg_left hWle (by positivity)
    _ = (Ck * (2 / τ₀ ^ 3 + 8) * Q * S) * (x ^ C * P * E * T) := by ring
    _ ≤ x * (x ^ C * P * E * T) := mul_le_mul_of_nonneg_right hK (by positivity)
    _ = (x ^ C * x * P * Real.exp (-(1 / 4) * u)) * (Real.exp (-(27 / 40) * u) * T) := by
        have : E = Real.exp (-(1 / 4) * u) * Real.exp (-(27 / 40) * u) := by
          rw [← Real.exp_add, hE_def]
          congr 1
          ring
        rw [this]
        ring
    _ ≤ 1 * (Real.exp (-(27 / 40) * u) * T) :=
        mul_le_mul_of_nonneg_right hyy (by positivity)
    _ = Real.exp (-(27 / 40) * u + ℓ.rt * m / 2 ^ 9) := by rw [one_mul, hT, ← Real.exp_add]
    _ ≤ Real.exp (-(5 * (ch * x) / 8)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : 0 ≤ ch * x := by positivity
        have h2 : 0 ≤ ℓ.rt * m / 2 ^ 8 := by positivity
        have e : ℓ.rt * (m : ℝ) / 2 ^ 9 = (ℓ.rt * m / 2 ^ 8) / 2 := by ring
        rw [hu_def, e]
        linarith
private theorem interpolation_le (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (hrt : 0 < ℓ.rt) (hn1 : 0 < ℓ.n₁) (ch x C Ck τ₀ : ℝ)
    (hch : 0 < ch)
    (hx1 : 1 ≤ x) (hC : 0 ≤ C) (hCk : 0 < Ck) (hτ0 : 0 < τ₀) (hτ1 : τ₀ ≤ 1)
    (hK : Ck * (2 / τ₀ ^ 3 + 8) * (2 + 4 / ℓ.n₁) ^ 16000 * Real.exp (ℓ.rt / 2 ^ 8) ≤ x)
    (hy : ∀ m : ℕ, x ^ (C + 1) * (1 + m / ℓ.n₁) ^ 16000 *
      Real.exp (-(1 / 4) * (ch * x + ℓ.rt * m / 2 ^ 8)) ≤ 1)
    (m N k : ℕ) (hN : N ≤ 2 * m + 4) (hk : k ≤ 3) :
    Ck * ((2 * Real.exp (-(ch * x) - ℓ.rt * m / 2 ^ 8)) / τ₀ ^ k +
        (2 * Real.exp (-(ch * x) - ℓ.rt * m / 2 ^ 8)) ^ (1 - (k : ℝ) / (40 : ℕ)) *
          (4 * x ^ C) ^ ((k : ℝ) / (40 : ℕ))) ≤
      Real.exp (-(5 * (ch * x) / 8)) / ℓ.weight N :=
  interpolation_le_aux ℓ hrt ch x C Ck τ₀ _ _ hch hx1 hC hCk hτ0 hτ1 (pow_nonneg (by positivity) _)
    (pow_nonneg (by positivity) _) hK m N k (hy m)
    (weight_le_of_le ℓ hn1 hrt m N hN 16000 rfl) hk
end Sizes
section Between
private def InterpolationBound (Cm : ℝ) : Prop :=
  ∀ k ≤ 3, ∀ (u : (Fin k → ℝ) → ℝ) (τ₀ M₀ Mp : ℝ), 0 < τ₀ → 0 < M₀ → 0 ≤ Mp → ContDiff ℝ 40 u →
    (∀ τ, ‖τ‖ ≤ τ₀ → |u τ| ≤ M₀) → (∀ τ, ‖τ‖ ≤ τ₀ → ‖iteratedFDeriv ℝ 40 u τ‖ ≤ Mp) →
    ∀ v : Fin k → (Fin k → ℝ), (∀ l, ‖v l‖ ≤ 1) →
      |iteratedFDeriv ℝ k u 0 v| ≤
        Cm * (M₀ / τ₀ ^ k + M₀ ^ (1 - (k : ℝ) / (40 : ℕ)) * Mp ^ ((k : ℝ) / (40 : ℕ)))
private theorem exists_interpolationBound (hI : LandauKolmogorovMultivariateAtZero) :
    ∃ Cm : ℝ, 0 < Cm ∧ InterpolationBound Cm := by
  choose! C hC hmain using fun k : ℕ => fun _ : k < 4 => hI k 40 k (by omega)
  refine ⟨C 0 + C 1 + C 2 + C 3, ?_, ?_⟩
  · have := hC 0 (by norm_num); have := hC 1 (by norm_num); have := hC 2 (by norm_num)
    have := hC 3 (by norm_num)
    linarith
  · intro k hk u τ₀ M₀ Mp hτ hM hMp hu h1 h2 v hv
    have hk4 : k < 4 := by omega
    have h3 := hmain k hk4 u τ₀ M₀ Mp hτ hM hMp hu h1 h2
      (fun σ m => iteratedFDeriv_perm_of_le_three (hu.of_le (by norm_num)) 0 k hk σ m) v hv
    refine h3.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have h0 := (hC 0 (by norm_num)).le
    have h1' := (hC 1 (by norm_num)).le
    have h2' := (hC 2 (by norm_num)).le
    have h3' := (hC 3 (by norm_num)).le
    interval_cases k <;> linarith
private theorem exists_contDiff_eventuallyEq {k : ℕ} (G : (Fin k → ℝ) → ℝ) (τ₀ : ℝ) (hτ : 0 < τ₀)
    (hG : ∀ τ, ‖τ‖ < 2 * τ₀ → ContDiffAt ℝ 40 G τ) :
    ∃ Gb : (Fin k → ℝ) → ℝ, ContDiff ℝ 40 Gb ∧ ∀ τ, ‖τ‖ < 3 / 2 * τ₀ → Gb =ᶠ[nhds τ] G := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockDensities.exists_contDiff_eventuallyEq <;> assumption
private theorem le_mul_of_forall_add {a S B : ℝ} (hB : 0 ≤ B) (h : ∀ ε, 0 < ε → a ≤ (S + ε) * B) :
    a ≤ S * B := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have h1 := h (δ / (B + 1)) (by positivity)
  have h2 : δ / (B + 1) * B ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith
private def blockCount (R : StepSetup) : ℝ := 2 * (R.params.side : ℝ) ^ 4 + 16 * R.params.coupling
private structure Constants (R : StepSetup) (ch C Cm : ℝ) : Prop where
  threshold_pos : 0 < R.params.threshold
  threshold_le : R.params.threshold ≤ 1
  rt_pos : 0 < R.params.rt
  n₁_pos : 0 < R.params.n₁
  ch_pos : 0 < ch
  one_le_coupling : 1 ≤ R.coupling
  C_nonneg : 0 ≤ C
  Cm_pos : 0 < Cm
  coupling_pos : 0 < R.params.coupling
  large : Cm * (2 / (R.params.threshold / 2 ^ 11) ^ 3 + 8) * (2 + 4 / R.params.n₁) ^ 16000 *
    Real.exp (R.params.rt / 2 ^ 8) ≤ R.coupling
  power_le : ∀ m : ℕ, R.coupling ^ (C + 1) * (1 + m / R.params.n₁) ^ 16000 *
    Real.exp (-(1 / 4) * (ch * R.coupling + R.params.rt * m / 2 ^ 8)) ≤ 1
  one_le_rate : 1 ≤ ch * R.coupling
  rt_le_rate : R.params.rt ≤ ch * R.coupling
  count_le : blockCount R * Real.exp (-(ch * R.coupling / 8)) ≤ 1
variable {R : StepSetup} {ch C Cm : ℝ}
private theorem Constants.one_le_count (N : Constants R ch C Cm) : 1 ≤ blockCount R := by
  have h1 : (1 : ℝ) ≤ R.params.side := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne R.params.side)
  have h2 : (1 : ℝ) ≤ (R.params.side : ℝ) ^ 4 := one_le_pow₀ h1
  have h3 := N.coupling_pos
  unfold blockCount
  linarith
private theorem Constants.deriv_bound (N : Constants R ch C Cm) (hI : InterpolationBound Cm) {k : ℕ}
    (hk : k ≤ 3)
    (u : (Fin k → ℝ) → ℝ) (hu : ContDiff ℝ 40 u) (m M : ℕ) (hM : M ≤ 2 * m + 4) (Q : ℝ) (hQ : 0 < Q)
    (hs : ∀ τ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 →
      |u τ| ≤ Q * (2 * Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8)))
    (hd : ∀ τ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 → ‖iteratedFDeriv ℝ 40 u τ‖ ≤ Q * (4 * R.coupling ^ C)) :
    |iteratedFDeriv ℝ k u 0 (fun l => Pi.single l 1)| ≤
      Q * (Real.exp (-(5 * (ch * R.coupling) / 8)) / R.params.weight M) := by
  have hτ : 0 < R.params.threshold / 2 ^ 11 := by have := N.threshold_pos; positivity
  have hτ1 : R.params.threshold / 2 ^ 11 ≤ 1 := by
    have := N.threshold_le
    have := N.threshold_pos
    linarith
  have hxC : 0 < R.coupling ^ C := Real.rpow_pos_of_pos (by linarith [N.one_le_coupling]) _
  set A := 2 * Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8) with hA
  have hA0 : 0 < A := by positivity
  have hB0 : 0 < 4 * R.coupling ^ C := by positivity
  have h1 := hI k hk u (R.params.threshold / 2 ^ 11) (Q * A) (Q * (4 * R.coupling ^ C)) hτ (by positivity)
    (by positivity) hu hs hd
    (fun l => Pi.single l 1) (fun l => by simp [Pi.norm_single])
  have e : (Q * A) ^ (1 - (k : ℝ) / (40 : ℕ)) * (Q * (4 * R.coupling ^ C)) ^ ((k : ℝ) / (40 : ℕ)) =
      Q * (A ^ (1 - (k : ℝ) / (40 : ℕ)) * (4 * R.coupling ^ C) ^ ((k : ℝ) / (40 : ℕ))) := by
    rw [Real.mul_rpow hQ.le hA0.le, Real.mul_rpow hQ.le hB0.le]
    have h2 : Q ^ (1 - (k : ℝ) / (40 : ℕ)) * Q ^ ((k : ℝ) / (40 : ℕ)) = Q := by
      rw [← Real.rpow_add hQ]
      simp
    calc _ = (Q ^ (1 - (k : ℝ) / (40 : ℕ)) * Q ^ ((k : ℝ) / (40 : ℕ))) *
          (A ^ (1 - (k : ℝ) / (40 : ℕ)) * (4 * R.coupling ^ C) ^ ((k : ℝ) / (40 : ℕ))) := by ring
      _ = _ := by rw [h2]
  rw [e] at h1
  have h3 := interpolation_le R.params N.rt_pos N.n₁_pos ch R.coupling C Cm _ N.ch_pos N.one_le_coupling
    N.C_nonneg N.Cm_pos hτ hτ1 N.large N.power_le m M k hM hk
  have h4 : Cm * (Q * A / (R.params.threshold / 2 ^ 11) ^ k + Q * (A ^ (1 - (k : ℝ) / (40 : ℕ)) *
      (4 * R.coupling ^ C) ^ ((k : ℝ) / (40 : ℕ)))) =
      Q * (Cm * (A / (R.params.threshold / 2 ^ 11) ^ k + A ^ (1 - (k : ℝ) / (40 : ℕ)) *
        (4 * R.coupling ^ C) ^ ((k : ℝ) / (40 : ℕ)))) := by ring
  rw [h4] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left h3 hQ.le)
private theorem Constants.deriv_le (N : Constants R ch C Cm) (hI : InterpolationBound Cm) {k : ℕ} (hk : k ≤ 3)
    (u : (Fin k → ℝ) → ℝ) (hu : ContDiff ℝ 40 u) (m M : ℕ) (hM : M ≤ 2 * m + 4) (S : ℝ) (hS : 0 ≤ S)
    (hs : ∀ τ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 →
      |u τ| ≤ blockCount R * (2 * Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8)) * S)
    (hd : ∀ τ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 →
      ‖iteratedFDeriv ℝ 40 u τ‖ ≤ blockCount R * (4 * R.coupling ^ C) * S) :
    |iteratedFDeriv ℝ k u 0 (fun l => Pi.single l 1)| ≤
      Real.exp (-(ch * R.coupling / 2)) * S / R.params.weight M := by
  have hK := N.one_le_count
  have hW := weight_pos' R.params M
  have hxC : 0 < R.coupling ^ C := Real.rpow_pos_of_pos (by linarith [N.one_le_coupling]) _
  have hB : 0 ≤ Real.exp (-(ch * R.coupling / 2)) / R.params.weight M := by positivity
  have e : Real.exp (-(ch * R.coupling / 2)) * S / R.params.weight M =
      S * (Real.exp (-(ch * R.coupling / 2)) / R.params.weight M) := by
    ring
  rw [e]
  refine le_mul_of_forall_add hB fun ε hε => ?_
  have hQ : 0 < blockCount R * (S + ε) := by positivity
  have h1 := N.deriv_bound hI hk u hu m M hM (blockCount R * (S + ε)) hQ
    (fun τ ht => (hs τ ht).trans (by
      have hp : 0 ≤ blockCount R * (2 * Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8)) := by
        positivity
      nlinarith))
    (fun τ ht => (hd τ ht).trans (by
      have hp : 0 ≤ blockCount R * (4 * R.coupling ^ C) := by positivity
      nlinarith))
  refine h1.trans ?_
  have h2 : blockCount R * Real.exp (-(5 * (ch * R.coupling) / 8)) ≤ Real.exp (-(ch * R.coupling / 2)) := by
    have e2 : Real.exp (-(5 * (ch * R.coupling) / 8)) =
        Real.exp (-(ch * R.coupling / 2)) * Real.exp (-(ch * R.coupling / 8)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e2]
    have h3 := N.count_le
    have h4 := Real.exp_pos (-(ch * R.coupling / 2))
    nlinarith
  calc blockCount R * (S + ε) * (Real.exp (-(5 * (ch * R.coupling) / 8)) / R.params.weight M)
      = (S + ε) * ((blockCount R * Real.exp (-(5 * (ch * R.coupling) / 8))) / R.params.weight M) := by ring
    _ ≤ (S + ε) * (Real.exp (-(ch * R.coupling / 2)) / R.params.weight M) := by gcongr
private structure SmoothAlongMoves (R : StepSetup) (ch C S : ℝ) {k : ℕ} (F : (Fin k → ℝ) → ℝ) : Prop where
  smooth : ∀ τ, ‖τ‖ < 2 * (R.params.threshold / 2 ^ 11) → ContDiffAt ℝ 40 F τ
  deriv : ∀ τ, ‖τ‖ < 2 * (R.params.threshold / 2 ^ 11) →
    ‖iteratedFDeriv ℝ 40 F τ‖ ≤ blockCount R * R.coupling ^ C * S
  size : ∀ τ, ‖τ‖ < 2 * (R.params.threshold / 2 ^ 11) → |F τ| ≤ Real.exp (-(5 * ch * R.coupling)) * S
private theorem exists_smooth_extension (N : Constants R ch C Cm) {S : ℝ} {k : ℕ} {F : (Fin k → ℝ) → ℝ}
    (G : SmoothAlongMoves R ch C S F) :
    ∃ Gb : (Fin k → ℝ) → ℝ, ContDiff ℝ 40 Gb ∧
      (∀ τ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 → Gb τ = F τ) ∧
      (∀ τ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 →
        ‖iteratedFDeriv ℝ 40 Gb τ‖ ≤ blockCount R * R.coupling ^ C * S) ∧
      (∀ j : ℕ, iteratedFDeriv ℝ j Gb 0 = iteratedFDeriv ℝ j F 0) := by
  have hσ := N.threshold_pos
  have hτ0 : 0 < R.params.threshold / 2 ^ 11 := by positivity
  obtain ⟨Gb, hGb, hGe⟩ := exists_contDiff_eventuallyEq F (R.params.threshold / 2 ^ 11) hτ0 G.smooth
  have hin : ∀ τ : Fin k → ℝ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 →
      ‖τ‖ < 3 / 2 * (R.params.threshold / 2 ^ 11) := fun τ ht => by
    linarith
  refine ⟨Gb, hGb, fun τ ht => (hGe τ (hin τ ht)).self_of_nhds, fun τ ht => ?_, fun j => ?_⟩
  · rw [((hGe τ (hin τ ht)).iteratedFDeriv (𝕜 := ℝ) 40).self_of_nhds]
    exact G.deriv τ (by linarith)
  · exact ((hGe 0 (by simpa using hτ0)).iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds
private def zeroCoord {k : ℕ} (l₀ : Fin k) : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun l => if l = l₀ then 0 else ContinuousLinearMap.proj l
private theorem zeroCoord_apply {k : ℕ} (l₀ l : Fin k) (τ : Fin k → ℝ) :
    zeroCoord l₀ τ l = if l = l₀ then 0 else τ l := by
  unfold zeroCoord
  by_cases h : l = l₀ <;> simp [h]
private theorem norm_zeroCoord_apply_le {k : ℕ} (l₀ : Fin k) (τ : Fin k → ℝ) : ‖zeroCoord l₀ τ‖ ≤ ‖τ‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun l => ?_
  rw [zeroCoord_apply]
  split_ifs
  · simpa using norm_nonneg τ
  · exact norm_le_pi_norm τ l
private theorem norm_zeroCoord_le {k : ℕ} (l₀ : Fin k) : ‖zeroCoord l₀‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun τ => by
    simpa using norm_zeroCoord_apply_le l₀ τ
private theorem norm_iteratedFDeriv_comp_zeroCoord_le {k j : ℕ} (Gb : (Fin k → ℝ) → ℝ) (hGb : ContDiff ℝ 40 Gb)
    (hj : j ≤ 40) (l₀ : Fin k)
    (τ : Fin k → ℝ) :
    ‖iteratedFDeriv ℝ j (fun z => Gb (zeroCoord l₀ z)) τ‖ ≤ ‖iteratedFDeriv ℝ j Gb (zeroCoord l₀ τ)‖ := by
  have h := (zeroCoord l₀).iteratedFDeriv_comp_right hGb τ (i := j) (by exact_mod_cast hj)
  have e : (fun z => Gb (zeroCoord l₀ z)) = Gb ∘ (zeroCoord l₀) := rfl
  rw [e, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _i : Fin j, ‖zeroCoord l₀‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_zeroCoord_le l₀
  exact mul_le_of_le_one_right (norm_nonneg _) this
private theorem iteratedFDeriv_comp_zeroCoord_eq_zero {k : ℕ} (Gb : (Fin k → ℝ) → ℝ) (hGb : ContDiff ℝ 40 Gb)
    (hk : k ≤ 40) (l₀ : Fin k) :
    iteratedFDeriv ℝ k (fun z => Gb (zeroCoord l₀ z)) 0 (fun l => Pi.single l 1) = 0 := by
  have h := (zeroCoord l₀).iteratedFDeriv_comp_right hGb 0 (i := k) (by exact_mod_cast hk)
  have e : (fun z => Gb (zeroCoord l₀ z)) = Gb ∘ (zeroCoord l₀) := rfl
  rw [e, h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine ContinuousMultilinearMap.map_coord_zero _ l₀ ?_
  funext l
  simp [zeroCoord_apply, Pi.single_apply]
private theorem Constants.small_le (N : Constants R ch C Cm) (m : ℕ) (hm : m ≤ 1) :
    2 * Real.exp (-(5 * ch * R.coupling)) ≤
      blockCount R * (2 * Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8)) := by
  have hK := N.one_le_count
  have h1 := N.rt_le_rate
  have h0 := N.rt_pos
  have hm' : (m : ℝ) ≤ 1 := by exact_mod_cast hm
  have h2 : R.params.rt * m / 2 ^ 8 ≤ R.params.rt := by nlinarith
  have h4 : Real.exp (-(5 * ch * R.coupling)) ≤ Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h5 := Real.exp_pos (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8)
  nlinarith
private theorem Constants.deriv_le_four (N : Constants R ch C Cm) (S : ℝ) (hS : 0 ≤ S) :
    blockCount R * R.coupling ^ C * S ≤ blockCount R * (4 * R.coupling ^ C) * S := by
  have hK := N.one_le_count
  have hxC : 0 < R.coupling ^ C := Real.rpow_pos_of_pos (by linarith [N.one_le_coupling]) _
  have : blockCount R * R.coupling ^ C ≤ blockCount R * (4 * R.coupling ^ C) := by nlinarith
  exact mul_le_mul_of_nonneg_right this hS
private theorem deriv_le_of_far (N : Constants R ch C Cm) (hI : InterpolationBound Cm) {k : ℕ} (hk : k ≤ 3)
    {S : ℝ} (hS : 0 ≤ S)
    {F : (Fin k → ℝ) → ℝ} (G : SmoothAlongMoves R ch C S F) (l₀ : Fin k) (m M : ℕ) (hM : M ≤ 2 * m + 4)
    (hd : ∀ τ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 → |F τ - F (zeroCoord l₀ τ)| ≤
      blockCount R * Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8) * S) :
    |iteratedFDeriv ℝ k F 0 (fun l => Pi.single l 1)| ≤
      Real.exp (-(ch * R.coupling / 2)) * S / R.params.weight M := by
  obtain ⟨Gb, hGb, hval, hder, hzero⟩ := exists_smooth_extension N G
  have hK := N.one_le_count
  have hP : ContDiff ℝ 40 (fun τ => Gb (zeroCoord l₀ τ)) := hGb.comp (zeroCoord l₀).contDiff
  have hu : ContDiff ℝ 40 (fun τ => Gb τ - Gb (zeroCoord l₀ τ)) := hGb.sub hP
  have hb := N.deriv_le hI hk _ hu m M hM S hS ?_ ?_
  · have e0 : iteratedFDeriv ℝ k (fun τ => Gb τ - Gb (zeroCoord l₀ τ)) 0 (fun l => Pi.single l 1) =
        iteratedFDeriv ℝ k F 0 (fun l => Pi.single l 1) := by
      rw [fun_iteratedFDeriv_sub_apply (hGb.of_le (by exact_mod_cast (by omega : k ≤ 40))).contDiffAt
        (hP.of_le (by exact_mod_cast (by omega : k ≤ 40))).contDiffAt, ContinuousMultilinearMap.sub_apply,
        iteratedFDeriv_comp_zeroCoord_eq_zero Gb hGb (by omega) l₀, hzero k, sub_zero]
    rw [← e0]
    exact hb
  · intro τ ht
    have hPτ : ‖zeroCoord l₀ τ‖ ≤ R.params.threshold / 2 ^ 11 := (norm_zeroCoord_apply_le l₀ τ).trans ht
    rw [hval τ ht, hval _ hPτ]
    refine (hd τ ht).trans ?_
    have hp := Real.exp_pos (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8)
    have : blockCount R * Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8) ≤
        blockCount R * (2 * Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8)) := by nlinarith
    exact mul_le_mul_of_nonneg_right this hS
  · intro τ ht
    have hPτ : ‖zeroCoord l₀ τ‖ ≤ R.params.threshold / 2 ^ 11 := (norm_zeroCoord_apply_le l₀ τ).trans ht
    rw [fun_iteratedFDeriv_sub_apply hGb.contDiffAt hP.contDiffAt]
    refine (norm_sub_le _ _).trans ?_
    have h5 := hder τ ht
    have h6 := (norm_iteratedFDeriv_comp_zeroCoord_le Gb hGb (le_refl 40) l₀ τ).trans (hder _ hPτ)
    have h7 : blockCount R * (4 * R.coupling ^ C) * S =
        2 * (blockCount R * R.coupling ^ C * S) + 2 * (blockCount R * R.coupling ^ C * S) := by
      ring
    have h8 : 0 ≤ blockCount R * R.coupling ^ C * S := by
      have hxC : 0 < R.coupling ^ C := Real.rpow_pos_of_pos (by linarith [N.one_le_coupling]) _
      positivity
    linarith
private theorem deriv_le_of_small (N : Constants R ch C Cm) (hI : InterpolationBound Cm) {k : ℕ} (hk : k ≤ 3)
    {S : ℝ} (hS : 0 ≤ S)
    {F : (Fin k → ℝ) → ℝ} (G : SmoothAlongMoves R ch C S F) (m M : ℕ) (hm : m ≤ 1) (hM : M ≤ 2 * m + 4) :
    |iteratedFDeriv ℝ k F 0 (fun l => Pi.single l 1)| ≤
      Real.exp (-(ch * R.coupling / 2)) * S / R.params.weight M := by
  obtain ⟨Gb, hGb, hval, hder, hzero⟩ := exists_smooth_extension N G
  have hσ := N.threshold_pos
  have hb := N.deriv_le hI hk Gb hGb m M hM S hS
    (fun τ ht => by
      rw [hval τ ht]
      have h1 := G.size τ (by linarith)
      have h2 := N.small_le m hm
      have h3 := Real.exp_pos (-(5 * ch * R.coupling))
      have h4 : Real.exp (-(5 * ch * R.coupling)) * S ≤
          blockCount R * (2 * Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8)) * S :=
        mul_le_mul_of_nonneg_right (by linarith) hS
      linarith)
    (fun τ ht => (hder τ ht).trans (N.deriv_le_four S hS))
  rw [← hzero k]
  exact hb
private theorem deriv_sub_le_of_near (N : Constants R ch C Cm) (hI : InterpolationBound Cm) {k : ℕ} (hk : k ≤ 3)
    {S : ℝ} (hS : 0 ≤ S)
    {F F' : (Fin k → ℝ) → ℝ} (G : SmoothAlongMoves R ch C S F) (G' : SmoothAlongMoves R ch C S F') (m M : ℕ)
    (hM : M ≤ 2 * m + 4)
    (hd : ∀ τ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 → |F τ - F' τ| ≤
      blockCount R * (2 * Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8)) * S) :
    |iteratedFDeriv ℝ k F 0 (fun l => Pi.single l 1) - iteratedFDeriv ℝ k F' 0 (fun l => Pi.single l 1)| ≤
      Real.exp (-(ch * R.coupling / 2)) * S / R.params.weight M := by
  obtain ⟨Gb, hGb, hval, hder, hzero⟩ := exists_smooth_extension N G
  obtain ⟨Gb', hGb', hval', hder', hzero'⟩ := exists_smooth_extension N G'
  have hu : ContDiff ℝ 40 (fun τ => Gb τ - Gb' τ) := hGb.sub hGb'
  have hb := N.deriv_le hI hk _ hu m M hM S hS
    (fun τ ht => by
      rw [hval τ ht, hval' τ ht]
      exact hd τ ht)
    (fun τ ht => by
      rw [fun_iteratedFDeriv_sub_apply hGb.contDiffAt hGb'.contDiffAt]
      refine (norm_sub_le _ _).trans ?_
      have h5 := hder τ ht
      have h6 := hder' τ ht
      have h7 : blockCount R * (4 * R.coupling ^ C) * S =
          2 * (blockCount R * R.coupling ^ C * S) + 2 * (blockCount R * R.coupling ^ C * S) := by ring
      have h8 : 0 ≤ blockCount R * R.coupling ^ C * S := by
        have hK := N.one_le_count
        have hxC : 0 < R.coupling ^ C := Real.rpow_pos_of_pos (by linarith [N.one_le_coupling]) _
        positivity
      linarith)
  have e0 : iteratedFDeriv ℝ k (fun τ => Gb τ - Gb' τ) 0 (fun l => Pi.single l 1) =
      iteratedFDeriv ℝ k F 0 (fun l => Pi.single l 1) - iteratedFDeriv ℝ k F' 0 (fun l => Pi.single l 1) := by
    rw [fun_iteratedFDeriv_sub_apply (hGb.of_le (by exact_mod_cast (by omega : k ≤ 40))).contDiffAt
      (hGb'.of_le (by exact_mod_cast (by omega : k ≤ 40))).contDiffAt, ContinuousMultilinearMap.sub_apply,
      hzero k, hzero' k]
  rw [← e0]
  exact hb
end Between
section Block
variable {L : ℕ} [NeZero L]
private theorem mem_sitesInBlocks_iff' {n : ℕ} [NeZero n] (S : Finset (TorusSite n)) (x : TorusSite (n * L)) :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.SharedProofs.p74636 <;> assumption
private theorem fineSite_mem (hodd : Odd L) {n : ℕ} [NeZero n] (Y : TorusSite n) {o : Fin 4 → ℤ}
    (ho : o ∈ centredCube L) :
    fineSite L Y 0 o ∈ sitesInBlocks L {Y} := by
  rw [mem_sitesInBlocks_iff', parentBlock_fineSite hodd Y 0 o ho, siteOfInt_zero_offset, add_zero]
  exact Finset.mem_singleton_self _
private theorem isPlaquetteAt_of_fineSite (hodd : Odd L) (t : ℕ) {n : ℕ} [NeZero n] (Y : TorusSite n)
    {o : Fin 4 → ℤ} (ho : o ∈ centredCube L)
    (p : TorusPlaquette (fineSide L t (n * L))) (hp : IsPlaquetteAt L t (fineSite L Y 0 o) p) :
    IsPlaquetteAt L (t + 1) Y p := by
  obtain ⟨h1, c, hc, hb⟩ := hp
  exact ⟨h1, c, hc, Finset.mem_biUnion.mpr ⟨_, fineSite_mem hodd Y ho, hb⟩⟩
private theorem sum_sitesInBlocks_singleton (hodd : Odd L) {n : ℕ} [NeZero n] (Y : TorusSite n)
    (f : TorusSite (n * L) → ℝ) :
    ∑ y ∈ sitesInBlocks L {Y}, f y = ∑ o ∈ centredCube L, f (fineSite L Y 0 o) := by
  classical
  have e : sitesInBlocks L {Y} = (centredCube L).image fun o => fineSite L Y 0 o := by
    ext y
    constructor
    · intro hy
      have hb : parentBlock L y = Y := Finset.mem_singleton.mp ((mem_sitesInBlocks_iff' _ _).mp hy)
      obtain ⟨o, ho, rfl⟩ := exists_fineSite_of_parentBlock hodd Y y hb
      exact Finset.mem_image.mpr ⟨o, ho, rfl⟩
    · intro hy
      obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hy
      exact fineSite_mem hodd Y ho
  rw [e, Finset.sum_image]
  intro o ho o' ho' h
  exact fineSite_injective Y 0 hodd ho ho' h
abbrev _root_.YangMills.SharedProofs.p123070 := @sum_sitesInBlocks_singleton
private theorem weightNorm_nonneg {m : ℕ} (L t : ℕ) (h : PlaquetteWeight m) : 0 ≤ weightNorm L t h :=
  le_max_of_le_left (Real.iSup_nonneg fun _ => abs_nonneg _)
end Block
section Gas
variable {R : StepSetup} {ch C Cm : ℝ}
private theorem recordedSiteScore_cold {n : ℕ} [NeZero n] (A : ResponseSetup R) (V : TorusField n)
    (y : TorusSite (n * R.params.side)) :
    recordedSiteScore A (coldCaseGround R V) y = 0 := by
  have h : y ∉ (coldCaseGround R V).recordedSites := by
    simp [GasGround.recordedSites, coldCaseGround, emptyCoarseState, CoarseState.labelAt, CoarseState.markAt]
  simp [recordedSiteScore, siteScore, h]
private theorem coldCaseGround_admissible {n : ℕ} [NeZero n] (hn : R.params.n₀ ≤ n) (V : TorusField n)
    (hV : IsCold (9 / 8 * R.params.threshold) V) :
    (coldCaseGround R V).IsAdmissibleGround :=
  Or.inl ⟨hn, hV, rfl, rfl, rfl⟩
private theorem coldCaseGround_agree {n n' : ℕ} [NeZero n] [NeZero n'] (V : TorusField n) (V' : TorusField n')
    (Y : TorusSite n) (Y' : TorusSite n')
    (m : ℕ) (hs : 2 * m + 2 < n) (hs' : 2 * m + 2 < n') (hag : FieldsAgreeNear V V' Y Y' m) :
    GroundsAgreeNear (coldCaseGround R V) (coldCaseGround R V') Y Y' m :=
  ⟨hs, hs', hag, fun _ _ => by simp [coldCaseGround],
    fun _ _ => by simp [coldCaseGround, emptyCoarseState, CoarseState.markAt]⟩
private def scoreSum {n : ℕ} [NeZero n] (G : GasGround R n) (Y : TorusSite n) : ℝ :=
  ∑ i : Fin 4, (gasBondScoreShift G (bondFrom Y ((0 : Fin 4 → ℤ), i)) +
    gasBondScoreShift G (bondFrom Y (-(Pi.single i 1 : Fin 4 → ℤ), i)))
private theorem bondFrom_zero {n : ℕ} [NeZero n] (Y : TorusSite n) (i : Fin 4) :
    bondFrom Y ((0 : Fin 4 → ℤ), i) = (Y, i) := by
  simp [bondFrom, siteOfInt_zero_offset]
private theorem bondFrom_neg_single {n : ℕ} [NeZero n] (Y : TorusSite n) (i : Fin 4) :
    bondFrom Y (-(Pi.single i 1 : Fin 4 → ℤ), i) = (Y - TorusFields.unitStep n i, i) := by
  have e : (siteOfInt (-(Pi.single i 1 : Fin 4 → ℤ)) : TorusSite n) = - TorusFields.unitStep n i := by
    funext j
    by_cases hj : j = i <;> simp [siteOfInt, TorusFields.unitStep, hj]
  simp only [bondFrom]
  rw [e, sub_eq_add_neg]
private theorem gasTermAtBlock_eq (hodd : Odd R.params.side) {n : ℕ} [NeZero n] (A : ResponseSetup R)
    (G : GasGround R n) (Y : TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    gasTermAtBlock A G Y h = ∑ o ∈ centredCube R.params.side, gasResponseShift A G (fineSite R.params.side Y 0 o) h +
      R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h * scoreSum G Y := by
  unfold gasTermAtBlock scoreSum
  rw [sum_sitesInBlocks_singleton hodd Y]
  simp only [bondFrom_zero, bondFrom_neg_single]
private theorem card_centredCube_real (hodd : Odd R.params.side) :
    ((centredCube R.params.side).card : ℝ) = (R.params.side : ℝ) ^ 4 := by
  obtain ⟨H, hH⟩ := hodd
  have hL : ((R.params.side : ℤ) - 1) / 2 = (H : ℤ) := by rw [hH]; push_cast; omega
  have hc : (Finset.Icc (-(H : ℤ)) (H : ℤ)).card = R.params.side := by
    rw [Int.card_Icc, hH]
    omega
  unfold centredCube
  rw [hL, Fintype.card_piFinset]
  simp [hc]
private structure Inputs (A : ResponseSetup R) (ch C Cm : ℝ) : Prop where
  consts : Constants R ch C Cm
  interp : InterpolationBound Cm
  odd : Odd R.params.side
  three_le : 3 ≤ R.params.n₀
  abs_coeff : |A.coeff| ≤ 2
  abs_mean : ∀ (n : ℕ) [NeZero n] (Y : TorusSite n) (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)),
    |blockMean R.params.side (R.depth + 1) n Y h| ≤ weightNorm R.params.side R.depth h
  agree_fine : ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (Y : TorusSite n) (Y' : TorusSite n')
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n')),
    WeightsAgreeAt R.params.side (R.depth + 1) Y Y' h h' → ∀ o ∈ centredCube R.params.side,
    WeightsAgreeAt R.params.side R.depth (fineSite R.params.side Y 0 o) (fineSite R.params.side Y' 0 o) h h'
  mean_agree : ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (y : TorusSite n) (y' : TorusSite n')
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n')),
    WeightsAgreeAt R.params.side (R.depth + 1) y y' h h' →
    blockMean R.params.side (R.depth + 1) n y h = blockMean R.params.side (R.depth + 1) n' y' h'
  exists_trim : ∀ (n n' : ℕ) [NeZero n] [NeZero n'], 3 ≤ n → 3 ≤ n' → ∀ (Y : TorusSite n) (Y' : TorusSite n')
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n')),
    WeightsAgreeAt R.params.side (R.depth + 1) Y Y' h h' →
    ∃ g : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n'),
      (∀ p, IsPlaquetteAt R.params.side (R.depth + 1) Y' p → g p = h' p) ∧
      weightNorm R.params.side R.depth g ≤ weightNorm R.params.side R.depth h ∧
      WeightsAgreeAt R.params.side (R.depth + 1) Y Y' h g
  mean_reads : ∀ (n : ℕ) [NeZero n] (Y : TorusSite n)
    (h h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)),
    (∀ p, IsPlaquetteAt R.params.side (R.depth + 1) Y p → h p = h' p) →
    blockMean R.params.side (R.depth + 1) n Y h = blockMean R.params.side (R.depth + 1) n Y h'
  bounds : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n,
    IsCold (9 / 8 * R.params.threshold) V →
    (∀ (y : TorusSite (n * R.params.side))
      (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))),
      |gasResponseShift A (coldCaseGround R V) y h| ≤
        Real.exp (-(6 * ch * R.coupling)) * weightNorm R.params.side R.depth h) ∧
    ∀ c : TorusBond n, |gasBondScoreShift (coldCaseGround R V) c| ≤ Real.exp (-(6 * ch * R.coupling))
  far : ∀ (n n' : ℕ) [NeZero n] [NeZero n'], R.params.n₀ ≤ n → R.params.n₀ ≤ n' →
    ∀ (V : TorusField n) (V' : TorusField n') (Y : TorusSite n)
    (Y' : TorusSite n') (m : ℕ), 1 ≤ m → 2 * m + 2 < n → 2 * m + 2 < n' →
    IsCold (9 / 8 * R.params.threshold) V →
    IsCold (9 / 8 * R.params.threshold) V' → FieldsAgreeNear V V' Y Y' m →
    (∀ o ∈ centredCube R.params.side,
      ∀ (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side)))
      (h' : PlaquetteWeight (fineSide R.params.side R.depth (n' * R.params.side))),
      WeightsAgreeAt R.params.side R.depth (fineSite R.params.side Y 0 o) (fineSite R.params.side Y' 0 o) h h' →
      |gasResponseShift A (coldCaseGround R V) (fineSite R.params.side Y 0 o) h -
          gasResponseShift A (coldCaseGround R V') (fineSite R.params.side Y' 0 o) h'| ≤
        2 * Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8) *
          max (weightNorm R.params.side R.depth h) (weightNorm R.params.side R.depth h')) ∧
    ∀ c : (Fin 4 → ℤ) × Fin 4, IsBondAtOrigin c →
      |gasBondScoreShift (coldCaseGround R V) (bondFrom Y c) -
          gasBondScoreShift (coldCaseGround R V') (bondFrom Y' c)| ≤
        2 * Real.exp (-(ch * R.coupling) - R.params.rt * m / 2 ^ 8)
  smooth : A.GasTermsSmooth C
  reads : ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ V : TorusField n, IsCold (9 / 8 * R.params.threshold) V →
    ∀ (y : TorusSite (n * R.params.side))
      (h h' : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))),
      (∀ p, IsPlaquetteAt R.params.side R.depth y p → h p = h' p) →
      gasResponseShift A (coldCaseGround R V) y h = gasResponseShift A (coldCaseGround R V) y h'
variable {A : ResponseSetup R}
private theorem Inputs.coeffTerm_le (Gv : Inputs A ch C Cm) {n : ℕ} [NeZero n] (Y : TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    |R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h| ≤
      R.params.coupling * weightNorm R.params.side R.depth h := by
  have ha := Gv.consts.coupling_pos
  have h1 := Gv.abs_coeff
  have h2 := Gv.abs_mean n Y h
  rw [abs_mul, abs_mul, abs_of_pos (half_pos ha)]
  calc R.params.coupling / 2 * |A.coeff| * |blockMean R.params.side (R.depth + 1) n Y h|
      ≤ R.params.coupling / 2 * 2 * weightNorm R.params.side R.depth h := by gcongr
    _ = _ := by ring
private theorem Inputs.scoreSum_le (Gv : Inputs A ch C Cm) {n : ℕ} [NeZero n] (hn : R.params.n₀ ≤ n)
    (V : TorusField n)
    (hV : IsCold (9 / 8 * R.params.threshold) V) (Y : TorusSite n) :
    |scoreSum (coldCaseGround R V) Y| ≤ 8 * Real.exp (-(6 * ch * R.coupling)) := by
  unfold scoreSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      |gasBondScoreShift (coldCaseGround R V) (bondFrom Y ((0 : Fin 4 → ℤ), i)) +
        gasBondScoreShift (coldCaseGround R V) (bondFrom Y (-(Pi.single i 1 : Fin 4 → ℤ), i))| ≤
      2 * Real.exp (-(6 * ch * R.coupling)) := by
    intro i _
    refine (abs_add_le _ _).trans ?_
    have a1 := (Gv.bounds n hn V hV).2 (bondFrom Y ((0 : Fin 4 → ℤ), i))
    have a2 := (Gv.bounds n hn V hV).2 (bondFrom Y (-(Pi.single i 1 : Fin 4 → ℤ), i))
    linarith
  refine (Finset.sum_le_sum h1).trans ?_
  simp
  linarith
private theorem Inputs.blockTerm_le (Gv : Inputs A ch C Cm) {n : ℕ} [NeZero n] (hn : R.params.n₀ ≤ n)
    (V : TorusField n)
    (hV : IsCold (9 / 8 * R.params.threshold) V) (Y : TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    |gasTermAtBlock A (coldCaseGround R V) Y h| ≤
      Real.exp (-(5 * ch * R.coupling)) * weightNorm R.params.side R.depth h := by
  have N := Gv.consts
  have hS : 0 ≤ weightNorm R.params.side R.depth h := weightNorm_nonneg R.params.side R.depth h
  rw [gasTermAtBlock_eq Gv.odd]
  set e := Real.exp (-(6 * ch * R.coupling)) with he
  have h1 : |∑ o ∈ centredCube R.params.side,
      gasResponseShift A (coldCaseGround R V) (fineSite R.params.side Y 0 o) h| ≤
      (R.params.side : ℝ) ^ 4 * (e * weightNorm R.params.side R.depth h) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun o _ => (Gv.bounds n hn V hV).1 _ h).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, card_centredCube_real Gv.odd]
    exact le_rfl
  have h2 : |R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h *
      scoreSum (coldCaseGround R V) Y| ≤
      R.params.coupling * weightNorm R.params.side R.depth h * (8 * e) := by
    rw [abs_mul]
    exact mul_le_mul (Gv.coeffTerm_le Y h) (Gv.scoreSum_le hn V hV Y) (abs_nonneg _)
      (by have := N.coupling_pos; positivity)
  refine (abs_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
  have hb := N.count_le
  have hx : 0 ≤ ch * R.coupling := by linarith [N.one_le_rate]
  have e5 : Real.exp (-(5 * ch * R.coupling)) = e * Real.exp (ch * R.coupling) := by
    rw [he, ← Real.exp_add]
    congr 1
    ring
  have hK : blockCount R ≤ Real.exp (ch * R.coupling) := by
    have e8 : blockCount R * Real.exp (-(ch * R.coupling / 8)) * Real.exp (ch * R.coupling / 8) =
        blockCount R := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    have h3 : blockCount R ≤ Real.exp (ch * R.coupling / 8) := by
      rw [← e8]
      have := Real.exp_pos (ch * R.coupling / 8)
      nlinarith
    exact h3.trans (Real.exp_le_exp.mpr (by linarith))
  rw [e5]
  have h4 : (R.params.side : ℝ) ^ 4 + 8 * R.params.coupling ≤ blockCount R := by
    unfold blockCount
    have := N.coupling_pos
    have : (0 : ℝ) ≤ (R.params.side : ℝ) ^ 4 := by positivity
    linarith
  have h5 : ((R.params.side : ℝ) ^ 4 + 8 * R.params.coupling) * (e * weightNorm R.params.side R.depth h) ≤
      Real.exp (ch * R.coupling) * (e * weightNorm R.params.side R.depth h) :=
    mul_le_mul_of_nonneg_right (h4.trans hK) (by positivity)
  nlinarith
private theorem Inputs.blockTerm_sub_le (Gv : Inputs A ch C Cm) {n n' : ℕ} [NeZero n] [NeZero n']
    (G : GasGround R n)
    (G' : GasGround R n') (Y : TorusSite n) (Y' : TorusSite n')
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n')) (e S : ℝ) (he : 0 ≤ e)
    (hS : weightNorm R.params.side R.depth h ≤ S)
    (hh : blockMean R.params.side (R.depth + 1) n Y h = blockMean R.params.side (R.depth + 1) n' Y' h')
    (hr : ∀ o ∈ centredCube R.params.side, |gasResponseShift A G (fineSite R.params.side Y 0 o) h -
      gasResponseShift A G' (fineSite R.params.side Y' 0 o) h'| ≤ 2 * e * S)
    (hc : ∀ c : (Fin 4 → ℤ) × Fin 4, IsBondAtOrigin c →
      |gasBondScoreShift G (bondFrom Y c) - gasBondScoreShift G' (bondFrom Y' c)| ≤ 2 * e) :
    |gasTermAtBlock A G Y h - gasTermAtBlock A G' Y' h'| ≤ blockCount R * e * S := by
  have N := Gv.consts
  have hS0 : 0 ≤ S := (weightNorm_nonneg R.params.side R.depth h).trans hS
  rw [gasTermAtBlock_eq Gv.odd, gasTermAtBlock_eq Gv.odd, ← hh]
  have e1 : ∑ o ∈ centredCube R.params.side, gasResponseShift A G (fineSite R.params.side Y 0 o) h +
      R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h * scoreSum G Y -
      (∑ o ∈ centredCube R.params.side, gasResponseShift A G' (fineSite R.params.side Y' 0 o) h' +
      R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h * scoreSum G' Y') =
      ∑ o ∈ centredCube R.params.side, (gasResponseShift A G (fineSite R.params.side Y 0 o) h -
        gasResponseShift A G' (fineSite R.params.side Y' 0 o) h') +
      R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h *
        (scoreSum G Y - scoreSum G' Y') := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [e1]
  have h1 : |∑ o ∈ centredCube R.params.side, (gasResponseShift A G (fineSite R.params.side Y 0 o) h -
      gasResponseShift A G' (fineSite R.params.side Y' 0 o) h')| ≤ (R.params.side : ℝ) ^ 4 * (2 * e * S) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hr).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, card_centredCube_real Gv.odd]
  have h2 : |scoreSum G Y - scoreSum G' Y'| ≤ 16 * e := by
    unfold scoreSum
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h3 : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
        |gasBondScoreShift G (bondFrom Y ((0 : Fin 4 → ℤ), i)) +
            gasBondScoreShift G (bondFrom Y (-(Pi.single i 1 : Fin 4 → ℤ), i)) -
          (gasBondScoreShift G' (bondFrom Y' ((0 : Fin 4 → ℤ), i)) +
            gasBondScoreShift G' (bondFrom Y' (-(Pi.single i 1 : Fin 4 → ℤ), i)))| ≤ 4 * e := by
      intro i _
      have a1 := hc ((0 : Fin 4 → ℤ), i) (Or.inl rfl)
      have a2 := hc (-(Pi.single i 1 : Fin 4 → ℤ), i) (Or.inr rfl)
      have e2 : gasBondScoreShift G (bondFrom Y ((0 : Fin 4 → ℤ), i)) +
            gasBondScoreShift G (bondFrom Y (-(Pi.single i 1 : Fin 4 → ℤ), i)) -
          (gasBondScoreShift G' (bondFrom Y' ((0 : Fin 4 → ℤ), i)) +
            gasBondScoreShift G' (bondFrom Y' (-(Pi.single i 1 : Fin 4 → ℤ), i))) =
          (gasBondScoreShift G (bondFrom Y ((0 : Fin 4 → ℤ), i)) -
            gasBondScoreShift G' (bondFrom Y' ((0 : Fin 4 → ℤ), i))) +
          (gasBondScoreShift G (bondFrom Y (-(Pi.single i 1 : Fin 4 → ℤ), i)) -
            gasBondScoreShift G' (bondFrom Y' (-(Pi.single i 1 : Fin 4 → ℤ), i))) := by ring
      rw [e2]
      refine (abs_add_le _ _).trans ?_
      linarith
    refine (Finset.sum_le_sum h3).trans ?_
    simp
    linarith
  have h4 : |R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h *
      (scoreSum G Y - scoreSum G' Y')| ≤
      R.params.coupling * S * (16 * e) := by
    rw [abs_mul]
    have a0 := N.coupling_pos
    exact mul_le_mul ((Gv.coeffTerm_le Y h).trans (mul_le_mul_of_nonneg_left hS a0.le)) h2 (abs_nonneg _)
      (by positivity)
  refine (abs_add_le _ _).trans ((add_le_add h1 h4).trans (le_of_eq ?_))
  unfold blockCount
  ring
private theorem norm_iteratedFDeriv_sum_le {k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → (Fin k → ℝ) → ℝ)
    (τ : Fin k → ℝ)
    (B : ι → ℝ) (hf : ∀ i ∈ s, ContDiffAt ℝ 40 (f i) τ) (hb : ∀ i ∈ s, ‖iteratedFDeriv ℝ 40 (f i) τ‖ ≤ B i) :
    ‖iteratedFDeriv ℝ 40 (fun z => ∑ i ∈ s, f i z) τ‖ ≤ ∑ i ∈ s, B i := by
  rw [iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := 40) hf]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum hb)
private theorem Inputs.blockTerm_perturb_eq (Gv : Inputs A ch C Cm) {n k : ℕ} [NeZero n] (Y : TorusSite n)
    (V : TorusField n)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    (fun τ => gasTermAtBlock A (coldCaseGround R (perturb c X τ V)) Y h) = fun τ =>
      ∑ o ∈ centredCube R.params.side,
          gasResponseShift A (coldCaseGround R (perturb c X τ V)) (fineSite R.params.side Y 0 o) h +
        (R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h) •
          scoreSum (coldCaseGround R (perturb c X τ V)) Y :=
  funext fun τ => by rw [gasTermAtBlock_eq Gv.odd, smul_eq_mul]
private theorem Inputs.scoreSum_contDiffAt (Gv : Inputs A ch C Cm) {n k : ℕ} [NeZero n] (hn : R.params.n₀ ≤ n)
    (Y : TorusSite n)
    (V : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (hc : IsCold (9 / 8 * R.params.threshold) (perturb c X τ V)) :
    ContDiffAt ℝ 40 (fun τ' => scoreSum (coldCaseGround R (perturb c X τ' V)) Y) τ := by
  unfold scoreSum
  refine ContDiffAt.sum fun i _ => ?_
  exact ((Gv.smooth n hn V k c X τ hc).2 _).1.add ((Gv.smooth n hn V k c X τ hc).2 _).1
private theorem Inputs.blockTerm_contDiffAt (Gv : Inputs A ch C Cm) {n k : ℕ} [NeZero n] (hn : R.params.n₀ ≤ n)
    (Y : TorusSite n)
    (V : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (hc : IsCold (9 / 8 * R.params.threshold) (perturb c X τ V))
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    ContDiffAt ℝ 40 (fun τ' => gasTermAtBlock A (coldCaseGround R (perturb c X τ' V)) Y h) τ := by
  rw [Gv.blockTerm_perturb_eq]
  exact (ContDiffAt.sum fun o _ => ((Gv.smooth n hn V k c X τ hc).1 _ h).1).add
    ((Gv.scoreSum_contDiffAt hn Y V c X τ hc).const_smul _)
private theorem Inputs.scoreSum_deriv_le (Gv : Inputs A ch C Cm) {n k : ℕ} [NeZero n] (hn : R.params.n₀ ≤ n)
    (Y : TorusSite n)
    (V : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (hc : IsCold (9 / 8 * R.params.threshold) (perturb c X τ V)) (hk : k ≤ 3) (hX : AreUnitVectors X) :
    ‖iteratedFDeriv ℝ 40 (fun τ' => scoreSum (coldCaseGround R (perturb c X τ' V)) Y) τ‖ ≤
      8 * R.coupling ^ C := by
  have hS := Gv.smooth n hn V k c X τ hc
  unfold scoreSum
  refine (norm_iteratedFDeriv_sum_le Finset.univ _ τ (fun _ => 2 * R.coupling ^ C)
    (fun i _ => (hS.2 _).1.add (hS.2 _).1) fun i _ => ?_).trans ?_
  · rw [fun_iteratedFDeriv_add_apply (hS.2 _).1 (hS.2 _).1]
    refine (norm_add_le _ _).trans ?_
    have a1 := (hS.2 (bondFrom Y ((0 : Fin 4 → ℤ), i))).2 hk hX
    have a2 := (hS.2 (bondFrom Y (-(Pi.single i 1 : Fin 4 → ℤ), i))).2 hk hX
    linarith
  · simp
    linarith
private theorem Inputs.blockTerm_deriv_le (Gv : Inputs A ch C Cm) {n k : ℕ} [NeZero n] (hn : R.params.n₀ ≤ n)
    (Y : TorusSite n)
    (V : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (hc : IsCold (9 / 8 * R.params.threshold) (perturb c X τ V)) (hk : k ≤ 3) (hX : AreUnitVectors X)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    ‖iteratedFDeriv ℝ 40 (fun τ' => gasTermAtBlock A (coldCaseGround R (perturb c X τ' V)) Y h) τ‖ ≤
      blockCount R * R.coupling ^ C * weightNorm R.params.side R.depth h := by
  have N := Gv.consts
  have hS := Gv.smooth n hn V k c X τ hc
  have hS0 : 0 ≤ weightNorm R.params.side R.depth h := weightNorm_nonneg R.params.side R.depth h
  have hxC : 0 < R.coupling ^ C := Real.rpow_pos_of_pos (by linarith [N.one_le_coupling]) _
  rw [Gv.blockTerm_perturb_eq]
  have f1 : ContDiffAt ℝ 40 (fun τ' => ∑ o ∈ centredCube R.params.side,
      gasResponseShift A (coldCaseGround R (perturb c X τ' V)) (fineSite R.params.side Y 0 o) h) τ :=
    ContDiffAt.sum fun o _ => (hS.1 _ h).1
  have f2 := Gv.scoreSum_contDiffAt hn Y V c X τ hc
  rw [fun_iteratedFDeriv_add_apply f1 (f2.const_smul _)]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖iteratedFDeriv ℝ 40 (fun τ' => ∑ o ∈ centredCube R.params.side,
      gasResponseShift A (coldCaseGround R (perturb c X τ' V)) (fineSite R.params.side Y 0 o) h) τ‖ ≤
      (R.params.side : ℝ) ^ 4 * (R.coupling ^ C * weightNorm R.params.side R.depth h) := by
    refine (norm_iteratedFDeriv_sum_le _ _ τ (fun _ => R.coupling ^ C * weightNorm R.params.side R.depth h)
      (fun o _ => (hS.1 _ h).1)
      fun o _ => (hS.1 _ h).2 hk hX).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, card_centredCube_real Gv.odd]
  have h2 : ‖iteratedFDeriv ℝ 40 (fun τ' =>
      (R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y h) •
      scoreSum (coldCaseGround R (perturb c X τ' V)) Y) τ‖ ≤
      R.params.coupling * weightNorm R.params.side R.depth h * (8 * R.coupling ^ C) := by
    rw [iteratedFDeriv_const_smul_apply' f2, norm_smul, Real.norm_eq_abs]
    have a0 := N.coupling_pos
    exact mul_le_mul (Gv.coeffTerm_le Y h) (Gv.scoreSum_deriv_le hn Y V c X τ hc hk hX) (norm_nonneg _)
      (by positivity)
  refine (add_le_add h1 h2).trans ?_
  have h4 : (R.params.side : ℝ) ^ 4 + 8 * R.params.coupling ≤ blockCount R := by
    unfold blockCount
    have := N.coupling_pos
    have : (0 : ℝ) ≤ (R.params.side : ℝ) ^ 4 := by positivity
    linarith
  have h5 : ((R.params.side : ℝ) ^ 4 + 8 * R.params.coupling) *
      (R.coupling ^ C * weightNorm R.params.side R.depth h) ≤
      blockCount R * (R.coupling ^ C * weightNorm R.params.side R.depth h) :=
    mul_le_mul_of_nonneg_right h4 (by positivity)
  nlinarith
private theorem Inputs.isCold_perturb_ball (Gv : Inputs A ch C Cm) {n k : ℕ} (V : TorusField n)
    (hV : IsCold R.params.threshold V) (hk : k ≤ 3)
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) (τ : Fin k → ℝ)
    (ht : ‖τ‖ < 2 * (R.params.threshold / 2 ^ 11)) :
    IsCold (9 / 8 * R.params.threshold) (perturb c X τ V) :=
  isCold_perturb hk c X hX τ V R.params.threshold Gv.consts.threshold_pos hV (by linarith)
private theorem Inputs.smoothAlongMoves (Gv : Inputs A ch C Cm) {n k : ℕ} [NeZero n] (hn : R.params.n₀ ≤ n)
    (Y : TorusSite n) (V : TorusField n)
    (hV : IsCold R.params.threshold V) (hk : k ≤ 3) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) (S : ℝ)
    (hS : weightNorm R.params.side R.depth h ≤ S) :
    SmoothAlongMoves R ch C S (fun τ => gasTermAtBlock A (coldCaseGround R (perturb c X τ V)) Y h) := by
  have N := Gv.consts
  have hK := N.one_le_count
  have hxC : 0 < R.coupling ^ C := Real.rpow_pos_of_pos (by linarith [N.one_le_coupling]) _
  refine ⟨fun τ ht => Gv.blockTerm_contDiffAt hn Y V c X τ (Gv.isCold_perturb_ball V hV hk c X hX τ ht) h,
    fun τ ht => ?_, fun τ ht => ?_⟩
  · exact (Gv.blockTerm_deriv_le hn Y V c X τ (Gv.isCold_perturb_ball V hV hk c X hX τ ht) hk hX h).trans
      (mul_le_mul_of_nonneg_left hS (by positivity))
  · exact (Gv.blockTerm_le hn _ (Gv.isCold_perturb_ball V hV hk c X hX τ ht) Y h).trans
      (mul_le_mul_of_nonneg_left hS (Real.exp_pos _).le)
section Agree
variable {n : ℕ}
private theorem fieldsAgreeNear_perturb_zeroCoord {k : ℕ} (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (τ τ' : Fin k → ℝ) (V : TorusField n)
    (y : TorusSite n) (m : ℕ) (l₀ : Fin k) (hτ : ∀ l, l ≠ l₀ → τ' l = τ l)
    (hfar : ∀ b, TorusFields.BondOffsetInBox m b → c l₀ ≠ bondFrom y b) :
    FieldsAgreeNear (perturb c X τ V) (perturb c X τ' V) y y m := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockDensities.fieldsAgreeNear_perturb_drop <;> assumption
private theorem fieldsAgreeNear_perturb_two {n' : ℕ} [NeZero n] [NeZero n'] {k : ℕ}
    (h : Fin k → (Fin 4 → ℤ) × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) (V : TorusField n) (V' : TorusField n')
    (y : TorusSite n) (y' : TorusSite n') (m : ℕ)
    (hn : 2 * m + 2 < n) (hn' : 2 * m + 2 < n') (hh : ∀ l, TorusFields.BondOffsetInBox m (h l))
    (hag : FieldsAgreeNear V V' y y' m) :
    FieldsAgreeNear (perturb (fun l => bondFrom y (h l)) X τ V) (perturb (fun l => bondFrom y' (h l)) X τ V')
      y y' m := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockDensities.fieldsAgreeNear_perturb <;> assumption
private theorem ne_bondFrom_of_lt_supDist [NeZero n] (y : TorusSite n) (z : TorusBond n) (m : ℕ)
    (hz : m < supDist y z.1) (b : (Fin 4 → ℤ) × Fin 4)
    (hb : TorusFields.BondOffsetInBox m b) : z ≠ bondFrom y b := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockDensities.ne_bondFrom_of_lt <;> assumption
end Agree
private theorem Inputs.blockTerm_decay (Gv : Inputs A ch C Cm) {n k : ℕ} [NeZero n] (hn : R.params.n₀ ≤ n)
    (Y : TorusSite n) (V : TorusField n)
    (hV : IsCold R.params.threshold V) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (h1 : 1 ≤ k) (hk : k ≤ 3) (hX : AreUnitVectors X)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)) :
    |mixedDeriv (fun U : TorusField n => gasTermAtBlock A (coldCaseGround R U) Y h) V c X| ≤
      Real.exp (-(ch * R.coupling / 2)) * weightNorm R.params.side R.depth h /
        R.params.weight (supportDiam Y c) := by
  have N := Gv.consts
  have hσ := N.threshold_pos
  have hS : 0 ≤ weightNorm R.params.side R.depth h := weightNorm_nonneg R.params.side R.depth h
  have G := Gv.smoothAlongMoves hn Y V hV hk c X hX h _ le_rfl
  have hcold : ∀ τ : Fin k → ℝ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 →
      IsCold (9 / 8 * R.params.threshold) (perturb c X τ V) :=
    fun τ ht => Gv.isCold_perturb_ball V hV hk c X hX τ (by linarith)
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨l₀, -, hl₀⟩ := Finset.exists_mem_eq_sup Finset.univ hne fun l : Fin k => supDist Y (c l).1
  set D : ℕ := Finset.univ.sup fun l : Fin k => supDist Y (c l).1 with hD
  have hle : ∀ l, supDist Y (c l).1 ≤ D := fun l => Finset.le_sup (f := fun l : Fin k => supDist Y (c l).1)
    (Finset.mem_univ l)
  have hspan : supportDiam Y c ≤ 2 * (D - 2) + 4 := by
    have h2 : supportDiam Y c ≤ 2 * D := by
      unfold supportDiam
      refine max_le (by omega) (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
      have := supDist_triangle (c l).1 Y (c l').1
      have h3 := hle l
      have h4 := hle l'
      rw [supDist_comm (c l).1 Y] at this
      omega
    omega
  show |iteratedFDeriv ℝ k (fun τ => gasTermAtBlock A (coldCaseGround R (perturb c X τ V)) Y h) 0
    (fun l => Pi.single l 1)| ≤ _
  by_cases h4 : 4 ≤ D
  · refine deriv_le_of_far N Gv.interp hk hS G l₀ (D - 2) _ hspan fun τ ht => ?_
    have hPτ : ‖zeroCoord l₀ τ‖ ≤ R.params.threshold / 2 ^ 11 := (norm_zeroCoord_apply_le l₀ τ).trans ht
    have hm1 : 1 ≤ D - 2 := by omega
    have hside : 2 * (D - 2) + 2 < n := by
      have := two_mul_supDist_le Y (c l₀).1
      rw [← hl₀] at this
      omega
    have hag : FieldsAgreeNear (perturb c X τ V) (perturb c X (zeroCoord l₀ τ) V) Y Y (D - 2) :=
      fieldsAgreeNear_perturb_zeroCoord c X τ _ V Y (D - 2) l₀
        (fun l hl => by rw [zeroCoord_apply, if_neg hl])
        (fun b hb => ne_bondFrom_of_lt_supDist Y (c l₀) (D - 2) (by rw [← hl₀]; omega) b hb)
    obtain ⟨fr, fc⟩ := Gv.far n n hn hn _ _ Y Y (D - 2) hm1 hside hside (hcold τ ht) (hcold _ hPτ) hag
    have hb := Gv.blockTerm_sub_le (coldCaseGround R (perturb c X τ V))
      (coldCaseGround R (perturb c X (zeroCoord l₀ τ) V)) Y Y h h
      (Real.exp (-(ch * R.coupling) - R.params.rt * ((D - 2 : ℕ) : ℝ) / 2 ^ 8))
      (weightNorm R.params.side R.depth h) (Real.exp_pos _).le le_rfl rfl
      (fun o ho => by
        have := fr o ho h h (fun _ _ _ _ _ => rfl)
        rwa [max_self] at this)
      fc
    exact hb
  · exact deriv_le_of_small N Gv.interp hk hS G (D - 2) _ (by omega) hspan
private theorem Inputs.blockTerm_reads (Gv : Inputs A ch C Cm) {n : ℕ} [NeZero n] (hn : R.params.n₀ ≤ n)
    (V : TorusField n)
    (hV : IsCold (9 / 8 * R.params.threshold) V) (Y : TorusSite n)
    (h h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (hp : ∀ p, IsPlaquetteAt R.params.side (R.depth + 1) Y p → h p = h' p) :
    gasTermAtBlock A (coldCaseGround R V) Y h = gasTermAtBlock A (coldCaseGround R V) Y h' := by
  rw [gasTermAtBlock_eq Gv.odd, gasTermAtBlock_eq Gv.odd, Gv.mean_reads n Y h h' hp]
  congr 1
  refine Finset.sum_congr rfl fun o ho => ?_
  exact Gv.reads n hn V hV _ h h' fun p hq => hp p (isPlaquetteAt_of_fineSite Gv.odd R.depth Y ho p hq)
private theorem Inputs.blockTerm_two_tori (Gv : Inputs A ch C Cm) {n n' k : ℕ} [NeZero n] [NeZero n']
    (hn : R.params.n₀ ≤ n)
    (hn' : R.params.n₀ ≤ n') (Y : TorusSite n) (Y' : TorusSite n') (V : TorusField n) (V' : TorusField n')
    (m : ℕ) (hs : 2 * m + 2 < n)
    (hs' : 2 * m + 2 < n') (hV : IsCold R.params.threshold V) (hV' : IsCold R.params.threshold V')
    (hag : FieldsAgreeNear V V' Y Y' m)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n'))
    (hw : WeightsAgreeAt R.params.side (R.depth + 1) Y Y' h h') (b : Fin k → (Fin 4 → ℤ) × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hk : k ≤ 2)
    (hb : ∀ l, TorusFields.BondOffsetInBox m (b l)) (hX : AreUnitVectors X) :
    |mixedDeriv (fun U : TorusField n => gasTermAtBlock A (coldCaseGround R U) Y h) V (fun l => bondFrom Y (b l)) X -
        mixedDeriv (fun U : TorusField n' => gasTermAtBlock A (coldCaseGround R U) Y' h') V'
          (fun l => bondFrom Y' (b l)) X| ≤
      Real.exp (-(ch * R.coupling / 2)) * weightNorm R.params.side R.depth h / R.params.weight m := by
  have N := Gv.consts
  have hσ := N.threshold_pos
  have hτ0 : 0 < R.params.threshold / 2 ^ 11 := by positivity
  have hk3 : k ≤ 3 := by omega
  have h3 : 3 ≤ n := Gv.three_le.trans hn
  have h3' : 3 ≤ n' := Gv.three_le.trans hn'
  have hS : 0 ≤ weightNorm R.params.side R.depth h := weightNorm_nonneg R.params.side R.depth h
  obtain ⟨g, g1, g2, hwg⟩ := Gv.exists_trim n n' h3 h3' Y Y' h h' hw
  have G := Gv.smoothAlongMoves hn Y V hV hk3 (fun l => bondFrom Y (b l)) X hX h _ le_rfl
  have G' := Gv.smoothAlongMoves hn' Y' V' hV' hk3 (fun l => bondFrom Y' (b l)) X hX g _ g2
  have hcold : ∀ τ : Fin k → ℝ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 →
      IsCold (9 / 8 * R.params.threshold) (perturb (fun l => bondFrom Y (b l)) X τ V) :=
    fun τ ht => Gv.isCold_perturb_ball V hV hk3 _ X hX τ (by linarith)
  have hcold' : ∀ τ : Fin k → ℝ, ‖τ‖ ≤ R.params.threshold / 2 ^ 11 →
      IsCold (9 / 8 * R.params.threshold) (perturb (fun l => bondFrom Y' (b l)) X τ V') :=
    fun τ ht => Gv.isCold_perturb_ball V' hV' hk3 _ X hX τ (by linarith)
  have hp := deriv_sub_le_of_near N Gv.interp hk3 hS G G' m m (by omega) fun τ ht => by
    by_cases hm : 1 ≤ m
    · obtain ⟨fr, fc⟩ := Gv.far n n' hn hn' _ _ Y Y' m hm hs hs' (hcold τ ht) (hcold' τ ht)
        (fieldsAgreeNear_perturb_two b X τ V V' Y Y' m hs hs' hb hag)
      have hd := Gv.blockTerm_sub_le (coldCaseGround R (perturb (fun l => bondFrom Y (b l)) X τ V))
        (coldCaseGround R (perturb (fun l => bondFrom Y' (b l)) X τ V')) Y Y' h g
        (Real.exp (-(ch * R.coupling) - R.params.rt * (m : ℝ) / 2 ^ 8)) (weightNorm R.params.side R.depth h)
        (Real.exp_pos _).le le_rfl
        (Gv.mean_agree n n' Y Y' h g hwg)
        (fun o ho => by
          exact (fr o ho h g (Gv.agree_fine n n' Y Y' h g hwg o ho)).trans
            (mul_le_mul_of_nonneg_left (max_le le_rfl g2) (by positivity)))
        fc
      refine hd.trans ?_
      have hK := N.one_le_count
      have hp := Real.exp_pos (-(ch * R.coupling) - R.params.rt * (m : ℝ) / 2 ^ 8)
      have : blockCount R * Real.exp (-(ch * R.coupling) - R.params.rt * (m : ℝ) / 2 ^ 8) ≤
          blockCount R * (2 * Real.exp (-(ch * R.coupling) - R.params.rt * (m : ℝ) / 2 ^ 8)) := by nlinarith
      exact mul_le_mul_of_nonneg_right this hS
    · have hm0 : m = 0 := by omega
      subst hm0
      have a1 := G.size τ (by linarith)
      have a2 := G'.size τ (by linarith)
      have a3 := abs_sub (gasTermAtBlock A (coldCaseGround R (perturb (fun l => bondFrom Y (b l)) X τ V)) Y h)
        (gasTermAtBlock A (coldCaseGround R (perturb (fun l => bondFrom Y' (b l)) X τ V')) Y' g)
      have a4 := mul_le_mul_of_nonneg_right (N.small_le 0 (by omega)) hS
      linarith
  have hbase : ∀ᶠ τ in nhds (0 : Fin k → ℝ),
      gasTermAtBlock A (coldCaseGround R (perturb (fun l => bondFrom Y' (b l)) X τ V')) Y' g =
      gasTermAtBlock A (coldCaseGround R (perturb (fun l => bondFrom Y' (b l)) X τ V')) Y' h' := by
    have hmem : Metric.ball (0 : Fin k → ℝ) (R.params.threshold / 2 ^ 11) ∈ nhds (0 : Fin k → ℝ) :=
      Metric.ball_mem_nhds _ hτ0
    filter_upwards [hmem] with τ ht
    have ht' : ‖τ‖ ≤ R.params.threshold / 2 ^ 11 := by
      have : ‖τ‖ < R.params.threshold / 2 ^ 11 := by simpa using ht
      exact this.le
    exact Gv.blockTerm_reads hn' _ (hcold' τ ht') Y' g h' g1
  have e1 : iteratedFDeriv ℝ k
        (fun τ => gasTermAtBlock A (coldCaseGround R (perturb (fun l => bondFrom Y' (b l)) X τ V')) Y' g) 0 =
      iteratedFDeriv ℝ k
        (fun τ => gasTermAtBlock A (coldCaseGround R (perturb (fun l => bondFrom Y' (b l)) X τ V')) Y' h') 0 :=
    (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hbase k).self_of_nhds
  rw [e1] at hp
  exact hp
private theorem isCold_nine_eighths {n : ℕ} (hσ : 0 < R.params.threshold) (V : TorusField n)
    (hV : IsCold R.params.threshold V) :
    IsCold (9 / 8 * R.params.threshold) V := fun x μ ν h => by
  have := hV x μ ν h
  linarith
private theorem Inputs.clauses (Gv : Inputs A ch C Cm) :
    (∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (Y : TorusSite n) (V : TorusField n), IsCold R.params.threshold V →
      ∀ h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n),
        |gasTermAtBlock A (coldCaseGround R V) Y h| ≤
          Real.exp (-(5 * ch * R.coupling)) * weightNorm R.params.side R.depth h ∧
        ContDiffThreeAt (fun V' : TorusField n => gasTermAtBlock A (coldCaseGround R V') Y h) V ∧
        ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
          AreUnitVectors X →
          |mixedDeriv (fun V' : TorusField n => gasTermAtBlock A (coldCaseGround R V') Y h) V c X| ≤
            Real.exp (-(ch * R.coupling / 2)) * weightNorm R.params.side R.depth h /
              R.params.weight (supportDiam Y c)) ∧
    ∀ (n n' : ℕ) [NeZero n] [NeZero n'], R.params.n₀ ≤ n → R.params.n₀ ≤ n' →
      ∀ (Y : TorusSite n) (Y' : TorusSite n') (V : TorusField n) (V' : TorusField n') (m : ℕ),
        2 * m + 2 < n → 2 * m + 2 < n' →
        IsCold R.params.threshold V → IsCold R.params.threshold V' → FieldsAgreeNear V V' Y Y' m →
        ∀ (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
          (h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n')),
          WeightsAgreeAt R.params.side (R.depth + 1) Y Y' h h' →
          ∀ (k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
            (∀ l, TorusFields.BondOffsetInBox m (b l)) →
            AreUnitVectors X →
            |mixedDeriv (fun U : TorusField n => gasTermAtBlock A (coldCaseGround R U) Y h) V
                (fun l => bondFrom Y (b l)) X -
                mixedDeriv (fun U : TorusField n' => gasTermAtBlock A (coldCaseGround R U) Y' h') V'
                  (fun l => bondFrom Y' (b l)) X| ≤
              Real.exp (-(ch * R.coupling / 2)) * weightNorm R.params.side R.depth h / R.params.weight m := by
  have hσ := Gv.consts.threshold_pos
  refine ⟨fun n _ hn Y V hV h => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Gv.blockTerm_le hn V (isCold_nine_eighths hσ V hV) Y h
  · intro k c X
    have h0 : IsCold (9 / 8 * R.params.threshold) (perturb c X (0 : Fin k → ℝ) V) := by
      rw [perturb_zero]
      exact isCold_nine_eighths hσ V hV
    exact (Gv.blockTerm_contDiffAt hn Y V c X 0 h0 h).of_le (by norm_num)
  · intro k c X h1 hk hX
    exact Gv.blockTerm_decay hn Y V hV c X h1 hk hX h
  · intro n n' _ _ hn hn' Y Y' V V' m hs hs' hV hV' hag h h' hw k b X hk hb hX
    exact Gv.blockTerm_two_tori hn hn' Y Y' V V' m hs hs' hV hV' hag h h' hw b X hk hb hX
end Gas
private theorem gasRate_pos (T : ParameterAssignment) (hT : T.Admissible) : 0 < T.gasRate := by apply _root_.YangMills.Construction.StepFloors.gasRate_pos <;> assumption
private theorem params_n₁_pos (T : ParameterAssignment) (hT : T.Admissible) : 0 < T.n₁ := by apply _root_.YangMills.Construction.StepFloors.n₁_pos <;> assumption
private theorem constants_of_schedule (T : ParameterAssignment) (hT : T.Admissible) (R : StepSetup) (y : ℝ)
    (hℓ : R.params = T.stepParameters y)
    (C Cm : ℝ) (hC : 0 ≤ C) (hCm : 0 < Cm) (hx1 : 1 ≤ R.coupling)
    (hbig : Cm * (2 / (T.threshold / 2 ^ 11) ^ 3 + 8) * (2 + 4 / T.n₁) ^ 16000 * Real.exp (T.rt / 2 ^ 8) ≤
      R.coupling)
    (hK : 8 * (2 * (T.side : ℝ) ^ 4 + 16 * T.coupling) / T.gasRate ≤ R.coupling)
    (hF : T.FloorConditions (C + 1) 1 R.coupling) : Constants R T.gasRate C Cm := by
  have eσ : R.params.threshold = T.threshold := by rw [hℓ]; rfl
  have ert : R.params.rt = T.rt := by rw [hℓ]; rfl
  have en : R.params.n₁ = T.n₁ := by rw [hℓ]; rfl
  have ea : R.params.coupling = T.coupling := by rw [hℓ]; rfl
  have eL : R.params.side = T.side := by rw [hℓ]; rfl
  have hch := gasRate_pos T hT
  obtain ⟨y1, y2, y3⟩ := hF.gas_powers
  have hrt0 := hT.rt_pos
  have hp : 1 ≤ R.coupling ^ (1 / 90 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hm : (0 : ℝ) ≤ 16 * T.rt * boxRadius R.coupling := by positivity
  refine ⟨?_, ?_, ?_, ?_, hch, hx1, hC, hCm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eσ]; exact hT.σ_pos
  · rw [eσ]; exact hT.σ_one
  · rw [ert]; exact hrt0
  · rw [en]; exact params_n₁_pos T hT
  · clear hbig
    rw [ea]
    linarith [hT.a_ge]
  · rw [eσ, ert, en]; exact hbig
  · intro m
    rw [ert, en]
    have := y3 m
    have e : -(1 / 4) * (T.gasRate * R.coupling + T.rt * m / 2 ^ 8) =
        -(1 / 4 * (T.gasRate * R.coupling + T.rt * m / 2 ^ 8)) := by
      ring
    rw [e]
    exact this
  · clear hbig
    linarith
  · clear hbig
    rw [ert]
    linarith
  · clear hbig
    have hKx : blockCount R ≤ T.gasRate * R.coupling / 8 := by
      unfold blockCount
      rw [ea, eL]
      rw [div_le_iff₀ hch] at hK
      linarith
    have h1 := Real.add_one_le_exp (T.gasRate * R.coupling / 8)
    have h2 : blockCount R ≤ Real.exp (T.gasRate * R.coupling / 8) := by linarith
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    exact h2
theorem gasTermAtColdFields_holds (hG : GasResponseBounds)
    (hE : GasResponseComparisonAllRadii) (hD : GasTermsOfResponseSmooth)
    (hR : gasResponseShift_local) (hM : BlockMeanIsLinearAndLocal)
    (hW : WeightsCloseToBlockMeans) (hA : WeightsAgreeingOnBlock)
    (hI : LandauKolmogorovMultivariateAtZero) (hFl : EventuallyFloorConditions) :
    GasTermAtColdFields := by
  obtain ⟨r1, p1, h1⟩ := hG
  obtain ⟨r2, p2, h2⟩ := hE
  obtain ⟨r3, p3, h3⟩ := hD
  obtain ⟨r4, p4, h4⟩ := hR
  obtain ⟨Cm, hCm, hInt⟩ := exists_interpolationBound hI
  refine ⟨fun c => min (r1 c) (min (r2 c) (min (r3 c) (r4 c))),
    fun c => lt_min (p1 c) (lt_min (p2 c) (lt_min (p3 c) (p4 c))), ?_⟩
  intro T hT hrt K
  obtain ⟨ya, ha⟩ := h1 T hT (hrt.trans (min_le_left _ _)) K
  obtain ⟨yb, hb⟩ := h2 T hT (hrt.trans ((min_le_right _ _).trans (min_le_left _ _))) K
  obtain ⟨C, yc, hC, hc⟩ :=
    h3 T hT (hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) K
  obtain ⟨yd, hd⟩ :=
    h4 T hT (hrt.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) K
  obtain ⟨yf, hf⟩ := hFl T hT (C + 1) 1 (by linarith) one_pos
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = Cm * (2 / (T.threshold / 2 ^ 11) ^ 3 + 8) * (2 + 4 / T.n₁) ^ 16000 *
      Real.exp (T.rt / 2 ^ 8) := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = 8 * (2 * (T.side : ℝ) ^ 4 + 16 * T.coupling) / T.gasRate := ⟨_, rfl⟩
  refine ⟨max (max (max ya yb) (max yc yd)) (max yf (max K₁ (max K₂ 1))), ?_⟩
  intro y hy R A hAK hAt hArr
  have hy1 := (le_max_left _ _).trans hy
  have hy2 := (le_max_right _ _).trans hy
  have hya : ya ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy1
  have hyb : yb ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy1
  have hyc : yc ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy1
  have hyd : yd ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy1
  have hyf : yf ≤ y := (le_max_left _ _).trans hy2
  have hyK : K₁ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy2
  have hyK₂ : K₂ ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy2
  have hy1' : (1 : ℝ) ≤ y := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hy2
  have hOn := hAt.onFamily
  have hx := hOn.le_coupling
  have N : Constants R T.gasRate C Cm :=
    constants_of_schedule T hT R y hOn.params_eq C Cm hC hCm (hy1'.trans hx) (hK₁ ▸ hyK.trans hx)
      (hK₂ ▸ hyK₂.trans hx) (hf R.coupling (hyf.trans hx))
  have hodd : Odd R.params.side := by
    have eL : R.params.side = T.side := by rw [hOn.params_eq]; rfl
    rw [eL]
    exact hT.L_odd
  have hside : 3 ≤ R.params.n₀ := by
    have en : R.params.n₀ = T.n₀ := by rw [hOn.params_eq]; rfl
    rw [en]
    have := hT.n₀_ge
    omega
  have Pa := ha y hya R A hAK hAt
  have Pb := hb y hyb R A hAK hAt
  have Pc := hc y hyc R A hAK hAt hArr
  have Pd := hd y hyd R A hAK hAt
  have Gv : Inputs A T.gasRate C Cm :=
    { consts := N
      interp := hInt
      odd := hodd
      three_le := hside
      abs_coeff := hAt.admissible.abs_coeff_le
      abs_mean := fun n _ Y h => ((hW R.params.side hodd (R.depth + 1) n Y).1 h).trans (le_max_left _ _)
      agree_fine := fun n n' _ _ Y Y' h h' hw o ho => (hA R.params.side hodd).1 R.depth n n' Y Y' h h' hw o ho
      mean_agree := fun n n' _ _ y y' h h' hw => (hA R.params.side hodd).2.1 (R.depth + 1) n n' y y' h h' hw
      exists_trim := fun n n' _ _ hn hn' Y Y' h h' hw =>
        (hA R.params.side hodd).2.2 (R.depth + 1) R.depth n n' hn hn' Y Y' h h' hw
      mean_reads := fun n _ Y h h' hp => (hM R.params.side hodd (R.depth + 1) n Y).2.2 h h' hp
      bounds := fun n _ hn V hV => by
        have Q := Pa.1 n (coldCaseGround R V) (coldCaseGround_admissible hn V hV)
        refine ⟨fun y' h => ?_, fun c => (Q.2 c).1⟩
        have := (Q.1 y' h).1
        rwa [recordedSiteScore_cold, add_zero, one_mul] at this
      far := fun n n' _ _ hn hn' V V' Y Y' m hm hs hs' hV hV' hag => by
        have Q := Pb n n' (coldCaseGround R V) (coldCaseGround R V') Y Y' m (coldCaseGround_admissible hn V hV)
          (coldCaseGround_admissible hn' V' hV') (coldCaseGround_agree V V' Y Y' m hs hs' hag) hm
        refine ⟨fun o ho h h' hw => ?_, Q.2⟩
        have := Q.1 o ho h h' hw
        rwa [recordedSiteScore_cold, add_zero, mul_one] at this
      smooth := Pc
      reads := fun n _ hn V hV y' h h' hp => Pd n hn V hV y' h h' hp }
  exact Gv.clauses
end YangMills.Construction.WeightedResponses.AtColdFields
end
