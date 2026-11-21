import YangMills.Construction.OneLoopLaw.OneLoopLawForTheNormalisers
import YangMills.Construction.OneLoopLaw.TheSumOfTheOneLoopIncrements
import YangMills.Construction.Towers.TheMassiveFunctionalAndTheFunctionOfTheMassiveJets
import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperatorsAreAdmitted
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.OneLoopLaw.NormaliserLaw
open ParameterChoice ComplexVariables
open Tower Tower.FullSpace.BackgroundJets
open Tower.Massive (uvDeviation)
open Tower.FullSpace.BackgroundJets.MassiveFunctionalAndJets
  (ofRealMomentum realPartialDeriv)
theorem hasDerivAt_realLine_of_tendsto_diffQuot (F : Coordinates.ComplexCoordinates 4 → ℂ)
    (p : Fin 4 → ℝ) (j : Fin 4) (l : ℂ)
    (h : Tendsto (diffQuot F (ofRealMomentum p) j) (𝓝[≠] 0) (𝓝 l)) :
    HasDerivAt (fun t : ℝ => F (ofRealMomentum (Function.update p j t))) l (p j) := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hc : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  refine (h.comp hc).congr (fun t => ?_)
  have hu : ofRealMomentum (Function.update p j (p j + t)) =
      ofRealMomentum p + (t : ℂ) • Coordinates.ComplexCoordinates.stdBasisVector j := by
    funext μ
    by_cases hμ : μ = j
    · subst hμ
      simp [ofRealMomentum, Coordinates.ComplexCoordinates.stdBasisVector]
    · simp [ofRealMomentum, Coordinates.ComplexCoordinates.stdBasisVector,
        Function.update_of_ne hμ, Pi.single_eq_of_ne hμ]
  have hp : ofRealMomentum (Function.update p j (p j)) = ofRealMomentum p := by simp
  simp only [Function.comp, diffQuot, hu, hp]
  rw [Complex.real_smul]
  push_cast
  rfl
theorem realMixedPartial_eq_mixedPartial {U : Set (Coordinates.ComplexCoordinates 4)}
    (F : Coordinates.ComplexCoordinates 4 → ℂ)
    (h0 : (0 : Coordinates.ComplexCoordinates 4) ∈ U) (hF : HasIteratedPartials U [0, 1] F) :
    MassiveFunctionalAndJets.mixedPartialAtZero
        (fun p => F (ofRealMomentum p)) =
      partialDeriv 0 (partialDeriv 1 F) 0 := by
  have hF1 : HasPartialDeriv U F 1 := hF.1.2
  have hF0 : HasPartialDeriv U (partialDeriv 1 F) 0 := hF.2
  have main1 : ∀ w ∈ U,
      Tendsto (diffQuot F w 1) (𝓝[≠] 0) (𝓝 (partialDeriv 1 F w)) := by
    intro w hw
    obtain ⟨l, hl⟩ := hF1.2 w hw
    have he : partialDeriv 1 F w = l := hl.limUnder_eq
    rw [he]
    exact hl
  have main0 : ∀ w ∈ U, Tendsto (diffQuot (partialDeriv 1 F) w 0) (𝓝[≠] 0)
      (𝓝 (partialDeriv 0 (partialDeriv 1 F) w)) := by
    intro w hw
    obtain ⟨l, hl⟩ := hF0.2 w hw
    have he : partialDeriv 0 (partialDeriv 1 F) w = l := hl.limUnder_eq
    rw [he]
    exact hl
  have stepA : ∀ p : Fin 4 → ℝ, ofRealMomentum p ∈ U →
      realPartialDeriv 1 (fun p => F (ofRealMomentum p)) p = partialDeriv 1 F (ofRealMomentum p) :=
    fun p hp => (hasDerivAt_realLine_of_tendsto_diffQuot F p 1 _ (main1 _ hp)).deriv
  have hz0 : ofRealMomentum (0 : Fin 4 → ℝ) = 0 := by
    funext μ
    simp [ofRealMomentum]
  have hcont : Continuous
      (fun t : ℝ => ofRealMomentum (Function.update (0 : Fin 4 → ℝ) 0 t)) := by
    have hu : Continuous (fun t : ℝ => Function.update (0 : Fin 4 → ℝ) 0 t) :=
      continuous_const.update 0 continuous_id
    refine continuous_pi fun μ => ?_
    exact Complex.continuous_ofReal.comp ((continuous_apply μ).comp hu)
  have hat : ofRealMomentum (Function.update (0 : Fin 4 → ℝ) 0 ((0 : Fin 4 → ℝ) 0)) ∈ U := by
    rw [Function.update_eq_self, hz0]
    exact h0
  have hev : ∀ᶠ t : ℝ in 𝓝 ((0 : Fin 4 → ℝ) 0),
      ofRealMomentum (Function.update (0 : Fin 4 → ℝ) 0 t) ∈ U :=
    hcont.continuousAt.eventually_mem (hF1.1.mem_nhds hat)
  have hev2 : (fun t : ℝ => realPartialDeriv 1 (fun p => F (ofRealMomentum p))
        (Function.update (0 : Fin 4 → ℝ) 0 t)) =ᶠ[𝓝 ((0 : Fin 4 → ℝ) 0)]
      fun t => partialDeriv 1 F (ofRealMomentum (Function.update (0 : Fin 4 → ℝ) 0 t)) := by
    filter_upwards [hev] with t ht
    exact stepA _ ht
  have hlast := (hasDerivAt_realLine_of_tendsto_diffQuot (partialDeriv 1 F) 0 0 _
    (main0 (ofRealMomentum 0) (by rw [hz0]; exact h0))).deriv
  rw [hz0] at hlast
  change deriv (fun t : ℝ => realPartialDeriv 1 (fun p => F (ofRealMomentum p))
    (Function.update (0 : Fin 4 → ℝ) 0 t)) ((0 : Fin 4 → ℝ) 0) = _
  rw [hev2.deriv_eq]
  exact hlast
theorem stripHalfWidth_pos
    (hRem : FreePolarizationRemainder.FreePolarizationRemainderBound)
    (hConsts : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) : 0 < stripHalfWidth := by
  obtain ⟨_, _, δ, hδ, C, _, hI, _, _⟩ := hConsts
  have he : stripHalfWidth = δ := Part.mem_unique hRem.1 hδ
  rw [he]
  exact hI.1
theorem multiIndexSteps_mixedIndex :
    multiIndexSteps FreePolarizationRemainder.mixedIndex = [0, 1] := by
  decide
theorem finestMesh_sq (L k : ℕ) :
    finestMesh L k ^ 2 = ((L : ℝ) ^ (2 * k))⁻¹ := by
  have h : finestMesh L k = ((L : ℝ) ^ k)⁻¹ := by
    simp [finestMesh, meshAt, zpow_neg]
  rw [h, inv_pow, ← pow_mul, Nat.mul_comm]
theorem log_inv_finestMesh_sq {L : ℕ} (k : ℕ) :
    11 / (6 * Real.pi ^ 2) * Real.log (1 / finestMesh L k ^ 2) =
      (k : ℝ) * oneLoopCoefficient L := by
  rw [finestMesh_sq, one_div, inv_inv, Real.log_pow]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [oneLoopCoefficient, colorNumber]
  push_cast
  field_simp
  ring
theorem deviationBound_nonneg {L : ℕ} (hL : 0 < L) (hB : Conventions.IsAdmissibleBlockingFactor L)
    (hRem : FreePolarizationRemainder.FreePolarizationRemainderBound)
    (hUv : MassiveStiffnessAsymptotics) : 0 ≤ deviationBound L := by
  have h1 := ((hRem.2.1 L hL hB).1 1 le_rfl).stiffness_bound
  have h2 := hUv.2.2.2 L hB hL 1 one_pos le_rfl
  have h3 : 0 ≤ uvDeviation hL 1 := by
    unfold uvDeviation
    positivity
  exact add_nonneg ((norm_nonneg _).trans h1) (h3.trans h2)
theorem stiffness_sum_deviation_of_pos {L : ℕ} (hL : 0 < L)
    (hB : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) (hk : 1 ≤ k)
    (hSum : IncrementSum.IncrementsSumToTotal)
    (hRem : FreePolarizationRemainder.FreePolarizationRemainderBound)
    (hMassive : MassiveFunctionalAndJets.Claim)
    (hUv : MassiveStiffnessAsymptotics)
    (hConsts : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) :
    |∑ j ∈ Finset.range k, normaliserStiffness hL j - (k : ℝ) * oneLoopCoefficient L|
      ≤ deviationBound L := by
  have hδ := stripHalfWidth_pos hRem hConsts
  have hH := (hRem.2.1 L hL hB).1 k hk
  have hS := ((hMassive L hL hB).2.2.2 k hk).2
  have hsum : ∑ j ∈ Finset.range k, normaliserStiffness hL j =
      FunctionalStiffness.stiffnessConstant hL (logNormaliserFamily L k) :=
    hSum.2.2 L hL hB k
  have hform : HasIteratedPartials FreePolarizationRemainder.openPolydisc [0, 1]
      (FreePolarizationRemainder.massiveAtFirstPair L k) := by
    have h := hH.has_mixed_partial
    rw [HasPartialOfIndex, multiIndexSteps_mixedIndex] at h
    exact h
  have h0 : (0 : Coordinates.ComplexCoordinates 4) ∈ FreePolarizationRemainder.openPolydisc := by
    intro μ
    simpa using hδ
  have hbridge : MassiveFunctionalAndJets.mixedPartialAtZero
        (fun p => massiveLogFnSharp L k (ofRealMomentum p) 0 1) =
      partialDeriv 0 (partialDeriv 1
        (FreePolarizationRemainder.massiveAtFirstPair L k)) 0 :=
    realMixedPartial_eq_mixedPartial _ h0 hform
  have hD : FreePolarizationRemainder.mixedPartialAtZero L k =
      partialDeriv 0 (partialDeriv 1
        (FreePolarizationRemainder.massiveAtFirstPair L k)) 0 := by
    simp only [FreePolarizationRemainder.mixedPartialAtZero, partialOfIndex,
      multiIndexSteps_mixedIndex]
    rfl
  have hbound := hH.stiffness_bound
  rw [hD, ← hbridge] at hbound
  have hpos : 0 < finestMesh L k ^ 2 := by
    rw [finestMesh_sq]
    have : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  have hle : finestMesh L k ^ 2 ≤ 1 := by
    rw [finestMesh_sq]
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    exact inv_le_one_of_one_le₀ (one_le_pow₀ this)
  have hU := hUv.2.2.2 L hB hL _ hpos hle
  set w := finestMesh L k ^ 2 with hw
  have hlog : 11 / (6 * Real.pi ^ 2) * Real.log (1 / w) = (k : ℝ) * oneLoopCoefficient L :=
    log_inv_finestMesh_sq k
  have hfour : finestMesh L k ^ 4 = w ^ 2 := by
    rw [hw]
    ring
  unfold uvDeviation at hU
  rw [hlog] at hU
  set b0 := massiveStiffness hL w
  set b1 := massiveStiffnessDeriv hL w
  set b2 := massiveStiffnessDeriv2 hL w
  set B := FunctionalStiffness.stiffnessConstant hL (logNormaliserFamily L k)
  have hnorm : |B - (b0 - w * b1 + 1 / 2 * w ^ 2 * b2)| ≤
      FreePolarizationRemainder.remainderBound L * stripHalfWidth ^ (-2 : ℤ) := by
    have hneg := neg_eq_iff_eq_neg.1 hS
    rw [hneg, hfour] at hbound
    have hc : ((B : ℝ) : ℂ) + -((b0 - w * b1 + 1 / 2 * w ^ 2 * b2 : ℝ) : ℂ) =
        ((B - (b0 - w * b1 + 1 / 2 * w ^ 2 * b2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hc, Complex.norm_real, Real.norm_eq_abs] at hbound
    exact hbound
  rw [hsum]
  unfold deviationBound
  have a1 := le_abs_self (b0 - (k : ℝ) * oneLoopCoefficient L)
  have a2 := neg_abs_le (b0 - (k : ℝ) * oneLoopCoefficient L)
  have a3 := le_abs_self (w * b1)
  have a4 := neg_abs_le (w * b1)
  have a5 := le_abs_self (w ^ 2 * b2)
  have a6 := neg_abs_le (w ^ 2 * b2)
  have a7 := (abs_le.1 hnorm).1
  have a8 := (abs_le.1 hnorm).2
  rw [abs_le]
  constructor <;> linarith
theorem stiffness_sum_deviation {L : ℕ} (hL : 0 < L)
    (hB : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ)
    (hSum : IncrementSum.IncrementsSumToTotal)
    (hRem : FreePolarizationRemainder.FreePolarizationRemainderBound)
    (hMassive : MassiveFunctionalAndJets.Claim)
    (hUv : MassiveStiffnessAsymptotics)
    (hConsts : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) :
    |∑ j ∈ Finset.range k, normaliserStiffness hL j - (k : ℝ) * oneLoopCoefficient L|
      ≤ deviationBound L := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using deviationBound_nonneg hL hB hRem hUv
  · exact stiffness_sum_deviation_of_pos hL hB k hk hSum hRem hMassive hUv hConsts
theorem stiffness_sum_Ico_deviation {L : ℕ} (hL : 0 < L) (i n : ℕ) (hin : i ≤ n)
    (hi : |∑ j ∈ Finset.range i, normaliserStiffness hL j - (i : ℝ) * oneLoopCoefficient L|
      ≤ deviationBound L)
    (hn : |∑ j ∈ Finset.range n, normaliserStiffness hL j - (n : ℝ) * oneLoopCoefficient L|
      ≤ deviationBound L) :
    |∑ j ∈ Finset.Ico i n, normaliserStiffness hL j - ((n : ℝ) - i) * oneLoopCoefficient L| ≤
      2 * deviationBound L := by
  rw [Finset.sum_Ico_eq_sub _ hin]
  have h1 := abs_le.1 hi
  have h2 := abs_le.1 hn
  rw [abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
theorem normaliserStiffnessLaw_holds (hSum : IncrementSum.IncrementsSumToTotal)
    (hRem : FreePolarizationRemainder.FreePolarizationRemainderBound)
    (hMassive : MassiveFunctionalAndJets.Claim)
    (hUv : MassiveStiffnessAsymptotics)
    (hConsts : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) :
    NormaliserStiffnessLaw := by
  intro L hL hB
  have hall := fun k => stiffness_sum_deviation hL hB k hSum hRem hMassive hUv hConsts
  have hbetween := fun i n (hin : i ≤ n) => stiffness_sum_Ico_deviation hL i n hin (hall i) (hall n)
  refine ⟨hall, hbetween, fun i n hin => ?_⟩
  have h := (abs_le.1 (hbetween i n hin)).1
  linarith
end YangMills.Construction.OneLoopLaw.NormaliserLaw
end
