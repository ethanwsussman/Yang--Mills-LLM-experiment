import YangMills.Construction.SummableBoundsOfTheFlow.LawsBetweenAreConvexProof
import YangMills.Construction.ColdStepAtMirrorFrames.MeansFrozenInValueProofForm
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.ResponseInTheExpansion.MajorisedObservablesAreAdmitted
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionHasTheConditionsOfThirdOrderProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation TorusComparison FamilyNorms WeightedResponses MeasureTheory
namespace ResponseInTheExpansion
variable {F : BlockFrame} {ι : Type} [Fintype ι] [DecidableEq ι]
private def extendMap (j : ι → ↥(chordBonds (finiteCells F))) (Λ : Finset ι) :
    BondField ι →L[ℝ] StepVariable (finiteCells F) :=
  ∑ i ∈ Λ, (ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) (j i)).comp
    (ContinuousLinearMap.proj i)
private theorem extendMap_apply (j : ι → ↥(chordBonds (finiteCells F))) (Λ : Finset ι) (ζ : BondField ι) :
    extendMap j Λ ζ = _root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ := by
  funext b
  simp [extendMap, _root_.YangMills.Construction.Interpolation.extendByZero, Pi.single_apply, Finset.sum_apply, eq_comm]
private theorem extendByZero_apply_self {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j)
    {Λ : Finset ι} {i : ι} (hi : i ∈ Λ) (ζ : BondField ι) : _root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ (j i) = ζ i := by apply _root_.YangMills.SharedProofs.p25945 <;> assumption
private theorem norm_extendByZero_lt {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) (Λ : Finset ι)
    {r : ℝ} (hr : 0 < r) {ζ : BondField ι} (hζ : ∀ i, ‖ζ i‖ < r) (b : ↥(chordBonds (finiteCells F))) :
    ‖_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b‖ < r := by apply _root_.YangMills.DeltaSharedProofs.p501821 <;> assumption
abbrev _root_.YangMills.SharedProofs.p46738 := @norm_extendByZero_lt
private theorem extendByZero_single (j : ι → ↥(chordBonds (finiteCells F))) (Λ : Finset ι) (i : ι) (v : BondVector) :
    _root_.YangMills.Construction.Interpolation.extendByZero j Λ (Pi.single i v) = if i ∈ Λ then Pi.single (j i) v else 0 := by
  funext b
  unfold _root_.YangMills.Construction.Interpolation.extendByZero
  by_cases hi : i ∈ Λ
  · rw [Finset.sum_eq_single i]
    · simp [hi, Pi.single_apply, eq_comm]
    · intro i' _ hne
      simp [hne]
    · exact fun h => absurd hi h
  · rw [Finset.sum_eq_zero]
    · simp [hi]
    · intro i' hi'
      have hne : i' ≠ i := fun e => hi (e ▸ hi')
      simp [hne]
private theorem bondGradNorm_extendByZero_le {A : StepVariable (finiteCells F) → ℝ}
    {j : ι → ↥(chordBonds (finiteCells F))} {Λ : Finset ι} {ζ : BondField ι}
    (hA : DifferentiableAt ℝ A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)) (i : ι) {B : ℝ} (hB : 0 ≤ B)
    (h : i ∈ Λ → bondGradNorm A (j i) (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) ≤ B) :
    bondGradNorm (fun ζ' => A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ')) i ζ ≤ B := by
  have e : (fun ζ' => A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ')) = A ∘ (extendMap j Λ) := by
    funext ζ'
    simp [extendMap_apply]
  have hA' : DifferentiableAt ℝ A (extendMap j Λ ζ) := by rwa [extendMap_apply]
  unfold bondGradNorm at h ⊢
  rw [e, fderiv_comp ζ hA' (extendMap j Λ).differentiableAt, ContinuousLinearMap.fderiv, extendMap_apply]
  by_cases hi : i ∈ Λ
  · have : (extendMap j Λ).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) i) =
        ContinuousLinearMap.single ℝ (fun _ : ↥(chordBonds (finiteCells F)) => BondVector) (j i) := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp [extendMap_apply, extendByZero_single, hi]
    rw [ContinuousLinearMap.comp_assoc, this]
    exact h hi
  · have : (extendMap j Λ).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) i) = 0 := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp [extendMap_apply, extendByZero_single, hi]
    rw [ContinuousLinearMap.comp_assoc, this]
    simpa using hB
private structure BallLawFacts (r : ℝ) (p : ℝ → ℝ) (Φ : BondField ι → ℝ) : Prop where
  measurable : Measurable (ballDensity (cutoffFactor r p) Φ)
  nonneg : ∀ η, 0 ≤ ballDensity (cutoffFactor r p) Φ η
  integrable : Integrable (ballDensity (cutoffFactor r p) Φ)
  mass : 0 < ∫ η, ballDensity (cutoffFactor r p) Φ η
  off : ∀ η, ¬ (∀ b, ‖η b‖ < r) → ballDensity (cutoffFactor r p) Φ η = 0
  weight_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ η, radialWeightProd (cutoffFactor r p) η ≤ C * ballDensity (cutoffFactor r p) Φ η
  weight_measurable : Measurable (radialWeightProd (cutoffFactor r p) (ι := ι))
  weight_nonneg : ∀ η : BondField ι, 0 ≤ radialWeightProd (cutoffFactor r p) η
  weight_off : ∀ η : BondField ι, ¬ (∀ b, ‖η b‖ < r) → radialWeightProd (cutoffFactor r p) η = 0
private theorem ballLawFacts_of_eqOn {r : ℝ} {p : ℝ → ℝ} (hr : 0 < r) (hp : IsCutoff r p)
    (hLaw : ConvexObservables.normalizedBallLawIsProbabilityStatement)
    {Φ Φ' : BondField ι → ℝ} (hE : ∀ η, (∀ b, ‖η b‖ < r) → Φ' η = Φ η) (hc : Continuous Φ') :
    BallLawFacts r p Φ := by
  obtain ⟨-, -, -, -, hme, hnn, hint, hmass, -, hnz, -⟩ := hLaw _ r p Φ' hr hp hc
  have hz : ∀ η : BondField ι, ¬ (∀ b, ‖η b‖ < r) → radialWeightProd (cutoffFactor r p) η = 0 := fun η hη => by
    have h0 : ballDensity (cutoffFactor r p) Φ' η = 0 := by
      by_contra hne
      exact hη ((hnz η).1 hne)
    unfold ballDensity at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact h
    · exact absurd h (Real.exp_pos _).ne'
  have hd : ballDensity (cutoffFactor r p) Φ = ballDensity (cutoffFactor r p) Φ' := by
    funext η
    by_cases hη : ∀ b, ‖η b‖ < r
    · unfold ballDensity
      rw [hE η hη]
    · unfold ballDensity
      rw [hz η hη, zero_mul, zero_mul]
  have hrn : ∀ η : BondField ι, 0 ≤ radialWeightProd (cutoffFactor r p) η := fun η => by
    have := hnn η
    unfold ballDensity at this
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have hrm : Measurable (radialWeightProd (cutoffFactor r p) (ι := ι)) := by
    have e : radialWeightProd (cutoffFactor r p) (ι := ι) =
        fun η => ballDensity (cutoffFactor r p) Φ' η * Real.exp (Φ' η) := by
      funext η
      unfold ballDensity
      rw [mul_assoc, ← Real.exp_add]
      simp
    rw [e]
    exact hme.mul (Real.continuous_exp.comp hc).measurable
  refine ⟨hd ▸ hme, hd ▸ hnn, hd ▸ hint, hd ▸ hmass, fun η hη => ?_, ?_, hrm, hrn, hz⟩
  · unfold ballDensity
    rw [hz η hη, zero_mul]
  · obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : BondField ι) r).exists_bound_of_continuousOn
      (f := fun η => Real.exp (Φ' η)) (Real.continuous_exp.comp hc).continuousOn
    refine ⟨max B 0, le_max_right _ _, fun η => ?_⟩
    by_cases hη : ∀ b, ‖η b‖ < r
    · have hmem : η ∈ Metric.closedBall (0 : BondField ι) r := by
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hr.le]
        exact fun b => (hη b).le
      have h1 := hB η hmem
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
      rw [hd]
      unfold ballDensity
      have hw : 0 ≤ radialWeightProd (cutoffFactor r p) η := hrn η
      have he : Real.exp (Φ' η) * Real.exp (- Φ' η) = 1 := by rw [← Real.exp_add]; simp
      calc radialWeightProd (cutoffFactor r p) η
            = radialWeightProd (cutoffFactor r p) η * (Real.exp (Φ' η) * Real.exp (- Φ' η)) := by
            rw [he, mul_one]
        _ ≤ radialWeightProd (cutoffFactor r p) η * (max B 0 * Real.exp (- Φ' η)) := by
            refine mul_le_mul_of_nonneg_left ?_ hw
            exact mul_le_mul_of_nonneg_right (h1.trans (le_max_left _ _)) (Real.exp_pos _).le
        _ = max B 0 * (radialWeightProd (cutoffFactor r p) η * Real.exp (- Φ' η)) := by ring
    · rw [hz η hη]
      exact mul_nonneg (le_max_right _ _) (by rw [hd]; exact hnn η)
private theorem abs_ballExpectation_le {r : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ} (hg : BallLawFacts r p Φ)
    {u : BondField ι → ℝ} {B : ℝ} (h : ∀ η, (∀ b, ‖η b‖ < r) → |u η| ≤ B) (hB : 0 ≤ B) :
    |ballExpectation (cutoffFactor r p) Φ u| ≤ B := by
  unfold ballExpectation
  rw [abs_div, abs_of_pos hg.mass, div_le_iff₀ hg.mass]
  have hpt : ∀ η, ‖u η * ballDensity (cutoffFactor r p) Φ η‖ ≤ B * ballDensity (cutoffFactor r p) Φ η := fun η => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hg.nonneg η)]
    by_cases hη : ∀ b, ‖η b‖ < r
    · exact mul_le_mul_of_nonneg_right (h η hη) (hg.nonneg η)
    · rw [hg.off η hη]
      simp
  calc |∫ η, u η * ballDensity (cutoffFactor r p) Φ η| ≤ ∫ η, ‖u η * ballDensity (cutoffFactor r p) Φ η‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ η, B * ballDensity (cutoffFactor r p) Φ η :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (hg.integrable.const_mul B) (Filter.Eventually.of_forall hpt)
    _ = B * ∫ η, ballDensity (cutoffFactor r p) Φ η := integral_const_mul _ _
private theorem abs_ballExpectation_le_abs {r : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ} (hg : BallLawFacts r p Φ)
    (u : BondField ι → ℝ) :
    |ballExpectation (cutoffFactor r p) Φ u| ≤ ballExpectation (cutoffFactor r p) Φ (fun η => |u η|) := by
  unfold ballExpectation
  rw [abs_div, abs_of_pos hg.mass]
  refine div_le_div_of_nonneg_right ?_ hg.mass.le
  have e : (fun η => |u η| * ballDensity (cutoffFactor r p) Φ η) =
      fun η => ‖u η * ballDensity (cutoffFactor r p) Φ η‖ := by
    funext η
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hg.nonneg η)]
  rw [e, ← Real.norm_eq_abs]
  exact norm_integral_le_integral_norm _
private theorem ballExpectation_mono {r : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ} (hg : BallLawFacts r p Φ)
    {u w : BondField ι → ℝ} (hu : ∀ η, (∀ b, ‖η b‖ < r) → 0 ≤ u η)
    (hw : Integrable fun η => w η * ballDensity (cutoffFactor r p) Φ η) (h : ∀ η, (∀ b, ‖η b‖ < r) → u η ≤ w η) :
    ballExpectation (cutoffFactor r p) Φ u ≤ ballExpectation (cutoffFactor r p) Φ w := by
  unfold ballExpectation
  refine div_le_div_of_nonneg_right ?_ hg.mass.le
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun η => ?_) hw (Filter.Eventually.of_forall fun η => ?_)
  · by_cases hη : ∀ b, ‖η b‖ < r
    · exact mul_nonneg (hu η hη) (hg.nonneg η)
    · show (0 : ℝ) ≤ u η * ballDensity (cutoffFactor r p) Φ η
      rw [hg.off η hη, mul_zero]
  · by_cases hη : ∀ b, ‖η b‖ < r
    · exact mul_le_mul_of_nonneg_right (h η hη) (hg.nonneg η)
    · show u η * ballDensity (cutoffFactor r p) Φ η ≤ w η * ballDensity (cutoffFactor r p) Φ η
      rw [hg.off η hη, mul_zero, mul_zero]
private def HasAllMoments (w : ℝ → ℝ) (Φ h : BondField ι → ℝ) : Prop :=
  Measurable h ∧ (∀ η, 0 ≤ h η) ∧ ∀ q : ℕ, 1 ≤ q → Integrable fun η => h η ^ q * ballDensity w Φ η
private theorem HasAllMoments.add {w : ℝ → ℝ} {Φ h h' : BondField ι → ℝ} (hm : Measurable (ballDensity w Φ))
    (hn : ∀ η, 0 ≤ ballDensity w Φ η) (a : HasAllMoments w Φ h) (b : HasAllMoments w Φ h') :
    HasAllMoments w Φ (fun η => h η + h' η) := by
  refine ⟨a.1.add b.1, fun η => add_nonneg (a.2.1 η) (b.2.1 η), fun q hq => ?_⟩
  refine Integrable.mono' (((a.2.2 q hq).add (b.2.2 q hq)).const_mul (2 ^ (q - 1)))
    ((((a.1.add b.1).pow_const q).mul hm).aestronglyMeasurable) (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (add_nonneg (a.2.1 η) (b.2.1 η)) _) (hn η))]
  have := add_pow_le (a.2.1 η) (b.2.1 η) q
  calc (h η + h' η) ^ q * ballDensity w Φ η ≤ 2 ^ (q - 1) * (h η ^ q + h' η ^ q) * ballDensity w Φ η :=
        mul_le_mul_of_nonneg_right this (hn η)
    _ = _ := by simp only [Pi.add_apply]; ring
private theorem HasAllMoments.sum {κ' : Type} {w : ℝ → ℝ} {Φ : BondField ι → ℝ} (S : Finset κ')
    {h : κ' → BondField ι → ℝ} (hm : Measurable (ballDensity w Φ)) (hn : ∀ η, 0 ≤ ballDensity w Φ η)
    (a : ∀ b ∈ S, HasAllMoments w Φ (h b)) : HasAllMoments w Φ (fun η => ∑ b ∈ S, h b η) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simp, by simp, fun q hq => ?_⟩
    have : q ≠ 0 := by omega
    simp [this]
  | insert b S hb ih =>
    have e : (fun η => ∑ c ∈ insert b S, h c η) = fun η => h b η + ∑ c ∈ S, h c η := by
      funext η
      rw [Finset.sum_insert hb]
    rw [e]
    exact (a b (Finset.mem_insert_self _ _)).add hm hn (ih fun c hc => a c (Finset.mem_insert_of_mem hc))
private theorem ballExpectation_const_mul (w : ℝ → ℝ) (Φ u : BondField ι → ℝ) (c : ℝ) :
    ballExpectation w Φ (fun η => c * u η) = c * ballExpectation w Φ u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ValueFreezing.expectation_const_mul <;> assumption
private theorem ballExpectation_two_add_sum {κ' : Type} {r : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ}
    (hg : BallLawFacts r p Φ) (S : Finset κ') (h h' : κ' → BondField ι → ℝ) (c : ℝ)
    (hi : ∀ b ∈ S, Integrable fun η => h b η * ballDensity (cutoffFactor r p) Φ η)
    (hi' : ∀ b ∈ S, Integrable fun η => h' b η * ballDensity (cutoffFactor r p) Φ η) :
    ballExpectation (cutoffFactor r p) Φ (fun η => 2 + c * ∑ b ∈ S, (h b η + h' b η)) =
      2 + c * ∑ b ∈ S, (ballExpectation (cutoffFactor r p) Φ (h b) + ballExpectation (cutoffFactor r p) Φ (h' b)) := by
  have hZ := hg.mass.ne'
  unfold ballExpectation
  have e : (fun η => (2 + c * ∑ b ∈ S, (h b η + h' b η)) * ballDensity (cutoffFactor r p) Φ η) =
      fun η => 2 * ballDensity (cutoffFactor r p) Φ η + c * ∑ b ∈ S, (h b η * ballDensity (cutoffFactor r p) Φ η +
        h' b η * ballDensity (cutoffFactor r p) Φ η) := by
    funext η
    simp only [add_mul, mul_assoc, Finset.sum_mul, Finset.mul_sum]
  have hs : Integrable fun η => ∑ b ∈ S, (h b η * ballDensity (cutoffFactor r p) Φ η +
      h' b η * ballDensity (cutoffFactor r p) Φ η) :=
    integrable_finsetSum _ fun b hb => (hi b hb).add (hi' b hb)
  have e3 : ∫ η, ∑ b ∈ S, (h b η * ballDensity (cutoffFactor r p) Φ η + h' b η * ballDensity (cutoffFactor r p) Φ η) =
      ∑ b ∈ S, ∫ η, (h b η * ballDensity (cutoffFactor r p) Φ η + h' b η * ballDensity (cutoffFactor r p) Φ η) :=
    integral_finsetSum _ fun b hb => (hi b hb).add (hi' b hb)
  rw [e, integral_add (hg.integrable.const_mul 2) (hs.const_mul c), integral_const_mul, integral_const_mul, e3]
  have : ∀ b ∈ S, ∫ η, (h b η * ballDensity (cutoffFactor r p) Φ η + h' b η * ballDensity (cutoffFactor r p) Φ η) =
      (∫ η, h b η * ballDensity (cutoffFactor r p) Φ η) + ∫ η, h' b η * ballDensity (cutoffFactor r p) Φ η :=
    fun b hb => integral_add (hi b hb) (hi' b hb)
  rw [Finset.sum_congr rfl this, add_div, mul_div_assoc, mul_div_assoc, div_self hZ, mul_one, Finset.sum_div]
  simp only [add_div]
private theorem iteratedDeriv_two_eq (p : ℝ → ℝ) : iteratedDeriv 2 p = deriv (deriv p) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
private theorem cutoffMajorant_moments {r x κ C : ℝ} {p : ℝ → ℝ} {Cq : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ} {d : ι → ι → ℝ}
    {Φ : BondField ι → ℝ} (hg : BallLawFacts r p Φ) (hm : LawMomentBounds r x κ C p Cq Cr d Φ) {Y : F.Cell}
    {j : ι → ↥(chordBonds (finiteCells F))} {Λ : Finset ι} (hj : Function.Injective j)
    (hcov : ∀ b : ↥(chordBonds (finiteCells F)), enclosingCell b.1.1 = Y → ∃ i ∈ Λ, j i = b) {N : ℕ}
    (hN : (open Classical in
      (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y).card) ≤ N) :
    HasAllMoments (cutoffFactor r p) Φ (fun ζ => cutoffMajorant p Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)) ∧
      ballExpectation (cutoffFactor r p) Φ (fun ζ => cutoffMajorant p Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) ^ 2) ≤
        2 + 4 * N * (N * (|Cr 1 2 0| + |Cr 2 2 0|)) := by
  classical
  set S := Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y with hS
  have hNS : S.card ≤ N := by
    convert hN
  have hpt : ∀ b ∈ S, ∃ i, ∀ ζ : BondField ι, _root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b = ζ i := fun b hb => by
    obtain ⟨i, hi, rfl⟩ := hcov b (by simpa [hS] using hb)
    exact ⟨i, fun ζ => extendByZero_apply_self hj hi ζ⟩
  set a : ↥(chordBonds (finiteCells F)) → BondField ι → ℝ :=
    fun b ζ => |deriv p ‖_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b‖| with ha
  set c : ↥(chordBonds (finiteCells F)) → BondField ι → ℝ :=
    fun b ζ => |deriv (deriv p) ‖_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b‖| with hc
  have hcont : ∀ l : ι, Continuous fun ζ : BondField ι => ‖ζ l‖ := fun l => (continuous_apply l).norm
  have ea : ∀ b ∈ S, ∃ i, a b = fun ζ => |deriv p ‖ζ i‖| := fun b hb => by
    obtain ⟨i, hi⟩ := hpt b hb
    exact ⟨i, funext fun ζ => by simp only [ha, hi]⟩
  have ec : ∀ b ∈ S, ∃ i, c b = fun ζ => |deriv (deriv p) ‖ζ i‖| := fun b hb => by
    obtain ⟨i, hi⟩ := hpt b hb
    exact ⟨i, funext fun ζ => by simp only [hc, hi]⟩
  have ga : ∀ b ∈ S, HasAllMoments (cutoffFactor r p) Φ (a b) := fun b hb => by
    obtain ⟨i, e⟩ := ea b hb
    rw [e]
    refine ⟨continuous_abs.measurable.comp ((measurable_deriv p).comp (hcont _).measurable), fun _ => abs_nonneg _,
      fun q hq => ?_⟩
    have := (hm.cutoff_deriv_moments 1 q 0 i le_rfl hq).1
    rwa [iteratedDeriv_one] at this
  have gc : ∀ b ∈ S, HasAllMoments (cutoffFactor r p) Φ (c b) := fun b hb => by
    obtain ⟨i, e⟩ := ec b hb
    rw [e]
    refine ⟨continuous_abs.measurable.comp ((measurable_deriv _).comp (hcont _).measurable), fun _ => abs_nonneg _,
      fun q hq => ?_⟩
    have := (hm.cutoff_deriv_moments 2 q 0 i (by norm_num) hq).1
    rwa [iteratedDeriv_two_eq] at this
  have e : ∀ ζ : BondField ι, cutoffMajorant p Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) = 1 + ∑ b ∈ S, (a b ζ + c b ζ) := fun ζ => by
    unfold cutoffMajorant ColdHalfLaw.sumOverBlock
    rw [← Finset.sum_filter]
  have e' : (fun ζ => cutoffMajorant p Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)) = fun ζ => 1 + ∑ b ∈ S, (a b ζ + c b ζ) := funext e
  have hone : HasAllMoments (cutoffFactor r p) Φ (fun _ => (1 : ℝ)) :=
    ⟨measurable_const, fun _ => zero_le_one, fun q _ => by simpa using hg.integrable⟩
  constructor
  · rw [e']
    exact hone.add hg.measurable hg.nonneg
      (HasAllMoments.sum S hg.measurable hg.nonneg fun b hb => (ga b hb).add hg.measurable hg.nonneg (gc b hb))
  · have hbound : ∀ ζ, cutoffMajorant p Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) ^ 2 ≤
        2 + (4 * N) * ∑ b ∈ S, (a b ζ ^ 2 + c b ζ ^ 2) := fun ζ => by
      rw [e ζ]
      set w := ∑ b ∈ S, (a b ζ + c b ζ) with hw
      have h1 : w ^ 2 ≤ S.card * ∑ b ∈ S, (a b ζ + c b ζ) ^ 2 := sq_sum_le_card_mul_sum_sq
      have h2 : ∑ b ∈ S, (a b ζ + c b ζ) ^ 2 ≤ 2 * ∑ b ∈ S, (a b ζ ^ 2 + c b ζ ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun b _ => by nlinarith [sq_nonneg (a b ζ - c b ζ)]
      have h3 : 0 ≤ ∑ b ∈ S, (a b ζ ^ 2 + c b ζ ^ 2) := Finset.sum_nonneg fun b _ => by positivity
      have h4 : (S.card : ℝ) ≤ N := by exact_mod_cast hNS
      have h5 : (S.card : ℝ) * ∑ b ∈ S, (a b ζ + c b ζ) ^ 2 ≤ N * (2 * ∑ b ∈ S, (a b ζ ^ 2 + c b ζ ^ 2)) :=
        mul_le_mul h4 h2 (Finset.sum_nonneg fun b _ => by positivity) (by positivity)
      nlinarith [sq_nonneg (w - 1)]
    have ia : ∀ b ∈ S, Integrable fun η => a b η ^ 2 * ballDensity (cutoffFactor r p) Φ η :=
      fun b hb => (ga b hb).2.2 2 (by norm_num)
    have ic : ∀ b ∈ S, Integrable fun η => c b η ^ 2 * ballDensity (cutoffFactor r p) Φ η :=
      fun b hb => (gc b hb).2.2 2 (by norm_num)
    have hw : Integrable fun η =>
        (2 + (4 * N) * ∑ b ∈ S, (a b η ^ 2 + c b η ^ 2)) * ballDensity (cutoffFactor r p) Φ η := by
      have e2 : (fun η => (2 + (4 * N) * ∑ b ∈ S, (a b η ^ 2 + c b η ^ 2)) * ballDensity (cutoffFactor r p) Φ η) =
          fun η => 2 * ballDensity (cutoffFactor r p) Φ η + (4 * N) * ∑ b ∈ S,
            (a b η ^ 2 * ballDensity (cutoffFactor r p) Φ η + c b η ^ 2 * ballDensity (cutoffFactor r p) Φ η) := by
        funext η
        simp only [add_mul, mul_assoc, Finset.sum_mul, Finset.mul_sum]
      rw [e2]
      exact (hg.integrable.const_mul 2).add ((integrable_finsetSum _ fun b hb => (ia b hb).add (ic b hb)).const_mul _)
    refine (ballExpectation_mono hg (fun _ _ => by positivity) hw fun ζ _ => hbound ζ).trans ?_
    rw [ballExpectation_two_add_sum hg S (fun b η => a b η ^ 2) (fun b η => c b η ^ 2) (4 * N) ia ic]
    have hA : ∀ b ∈ S, ballExpectation (cutoffFactor r p) Φ (fun η => a b η ^ 2) ≤ |Cr 1 2 0| := fun b hb => by
      obtain ⟨i, e⟩ := ea b hb
      have := (hm.cutoff_deriv_moments 1 2 0 i le_rfl (by norm_num)).2
      rw [iteratedDeriv_one] at this
      simp only [e]
      simpa using this.trans (by simpa using le_abs_self _)
    have hC : ∀ b ∈ S, ballExpectation (cutoffFactor r p) Φ (fun η => c b η ^ 2) ≤ |Cr 2 2 0| := fun b hb => by
      obtain ⟨i, e⟩ := ec b hb
      have := (hm.cutoff_deriv_moments 2 2 0 i (by norm_num) (by norm_num)).2
      rw [iteratedDeriv_two_eq] at this
      simp only [e]
      simpa using this.trans (by simpa using le_abs_self _)
    have hsum : ∑ b ∈ S, (ballExpectation (cutoffFactor r p) Φ (fun η => a b η ^ 2) +
        ballExpectation (cutoffFactor r p) Φ (fun η => c b η ^ 2)) ≤ N * (|Cr 1 2 0| + |Cr 2 2 0|) := by
      calc _ ≤ ∑ b ∈ S, (|Cr 1 2 0| + |Cr 2 2 0|) := Finset.sum_le_sum fun b hb => add_le_add (hA b hb) (hC b hb)
        _ = S.card * (|Cr 1 2 0| + |Cr 2 2 0|) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hNS) (by positivity)
    have : (0 : ℝ) ≤ 4 * N := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsum this]
private theorem isOpen_ballSet (r : ℝ) : IsOpen {ζ : BondField ι | ∀ i, ‖ζ i‖ < r} := by apply _root_.YangMills.SharedProofs.p5886 <;> assumption
private theorem integrable_pow_of_le {r c : ℝ} {p : ℝ → ℝ} {Φ g u : BondField ι → ℝ} (hg : BallLawFacts r p Φ)
    (good : HasAllMoments (cutoffFactor r p) Φ g) (hc : 0 ≤ c)
    (hu : AEStronglyMeasurable (Set.indicator {ζ : BondField ι | ∀ i, ‖ζ i‖ < r} u) volume)
    (hb : ∀ ζ, (∀ i, ‖ζ i‖ < r) → |u ζ| ≤ c * g ζ) (q : ℕ) (hq : 1 ≤ q) :
    Integrable fun ζ => |u ζ| ^ q * ballDensity (cutoffFactor r p) Φ ζ := by
  have hm : AEStronglyMeasurable (fun ζ => |u ζ| ^ q * ballDensity (cutoffFactor r p) Φ ζ) volume := by
    have e : (fun ζ => |u ζ| ^ q * ballDensity (cutoffFactor r p) Φ ζ) =
        fun ζ => ‖Set.indicator {ζ : BondField ι | ∀ i, ‖ζ i‖ < r} u ζ‖ ^ q * ballDensity (cutoffFactor r p) Φ ζ := by
      funext ζ
      by_cases hζ : ∀ i, ‖ζ i‖ < r
      · rw [Set.indicator_of_mem (show ζ ∈ {ζ : BondField ι | ∀ i, ‖ζ i‖ < r} from hζ), Real.norm_eq_abs]
      · rw [hg.off ζ hζ, mul_zero, mul_zero]
    rw [e]
    exact (hu.norm.pow q).mul hg.measurable.aestronglyMeasurable
  refine Integrable.mono' ((good.2.2 q hq).const_mul (c ^ q)) hm (Filter.Eventually.of_forall fun ζ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hg.nonneg ζ))]
  by_cases hζ : ∀ i, ‖ζ i‖ < r
  · calc |u ζ| ^ q * ballDensity (cutoffFactor r p) Φ ζ ≤ (c * g ζ) ^ q * ballDensity (cutoffFactor r p) Φ ζ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hb ζ hζ) q) (hg.nonneg ζ)
      _ = _ := by rw [mul_pow]; ring
  · rw [hg.off ζ hζ, mul_zero, mul_zero, mul_zero]
private theorem hasGradientBound_extendByZero {r x κ M D : ℝ} {p : ℝ → ℝ} {q : ℕ} {Y : F.Cell}
    {A : StepVariable (finiteCells F) → ℝ} {Φ : BondField ι → ℝ} {j : ι → ↥(chordBonds (finiteCells F))}
    {Λ : Finset ι} (hr : 0 < r) (hx : 1 ≤ x) (hκ : 0 ≤ κ)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hg : BallLawFacts r p Φ) (hj : Function.Injective j)
    (good : HasAllMoments (cutoffFactor r p) Φ (fun ζ => cutoffMajorant p Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)))
    (hmean : ballExpectation (cutoffFactor r p) Φ (fun ζ => cutoffMajorant p Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) ^ 2) ≤ D)
    (hA : IsCutoffDominated r κ M p q Y A) :
    HasGradientBound r (cutoffFactor r p) Φ x κ (M * (1 + D)) (fun i => bondDistToCell Y (j i))
      (fun ζ => A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ)) := by
  set H : BondField ι → ℝ := fun ζ => A (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) with hH
  set g : BondField ι → ℝ := fun ζ => cutoffMajorant p Y (_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ) with hgd
  have hballs : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < r) → ∀ b, ‖_root_.YangMills.Construction.Interpolation.extendByZero j Λ ζ b‖ < r :=
    fun ζ hζ b => norm_extendByZero_lt hj Λ hr hζ b
  have hAd : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < r) → DifferentiableAt ℝ A η := fun η hη =>
    (hA.smooth.contDiffAt ((isOpen_ballSet r).mem_nhds hη)).differentiableAt (by norm_num)
  have hcomp : H = A ∘ extendMap j Λ := by
    funext ζ
    simp [hH, extendMap_apply]
  have hdiff : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < r) → DifferentiableAt ℝ H ζ := fun ζ hζ => by
    rw [hcomp]
    refine DifferentiableAt.comp ζ ?_ (extendMap j Λ).differentiableAt
    rw [extendMap_apply]
    exact hAd _ (hballs ζ hζ)
  have hgn : ∀ ζ, 0 ≤ g ζ := good.2.1
  have hexp : ∀ i, Real.exp (-(2 * κ * bondDistToCell Y (j i))) ≤ 1 := fun i => by
    have : 0 ≤ bondDistToCell Y (j i) := by unfold bondDistToCell; positivity
    exact Real.exp_le_one_iff.2 (by nlinarith)
  have hpn : ∀ ζ : BondField ι, (∀ i, ‖ζ i‖ < r) → ∀ i,
      bondGradNorm H i ζ ≤ M * Real.exp (-(2 * κ * bondDistToCell Y (j i))) * g ζ := fun ζ hζ i =>
    bondGradNorm_extendByZero_le (hAd _ (hballs ζ hζ)) i (mul_nonneg (mul_nonneg hM (Real.exp_pos _).le) (hgn ζ))
      fun _ => hA.gradient_le _ (hballs ζ hζ) _
  have hpn0 : ∀ ζ i, 0 ≤ bondGradNorm H i ζ := fun ζ i => norm_nonneg _
  have hHm : AEStronglyMeasurable (Set.indicator {ζ : BondField ι | ∀ i, ‖ζ i‖ < r} H) volume := by
    have hco : ContinuousOn H {ζ : BondField ι | ∀ i, ‖ζ i‖ < r} :=
      fun ζ hζ => (hdiff ζ hζ).continuousAt.continuousWithinAt
    exact (aestronglyMeasurable_indicator_iff (isOpen_ballSet r).measurableSet).2
      (hco.aestronglyMeasurable (isOpen_ballSet r).measurableSet)
  have hPm : ∀ i, AEStronglyMeasurable
      (Set.indicator {ζ : BondField ι | ∀ i, ‖ζ i‖ < r} (bondGradNorm H i)) volume := fun i => by
    have : Measurable (bondGradNorm H i) := by
      unfold bondGradNorm
      have hc : Continuous fun L : BondField ι →L[ℝ] ℝ =>
          ‖L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) i)‖ :=
        (continuous_id.clm_comp continuous_const).norm
      exact hc.measurable.comp (measurable_fderiv ℝ H)
    exact (this.indicator (isOpen_ballSet r).measurableSet).aestronglyMeasurable
  have hHi : ∀ q' : ℕ, 1 ≤ q' → Integrable fun ζ => |H ζ| ^ q' * ballDensity (cutoffFactor r p) Φ ζ :=
    integrable_pow_of_le hg good hM hHm fun ζ hζ => hA.abs_le _ (hballs ζ hζ)
  have hPi : ∀ (i : ι) (q' : ℕ), 1 ≤ q' →
      Integrable fun ζ => |bondGradNorm H i ζ| ^ q' * ballDensity (cutoffFactor r p) Φ ζ :=
    fun i => integrable_pow_of_le hg good (mul_nonneg hM (Real.exp_pos _).le) (hPm i) fun ζ hζ => by
      rw [abs_of_nonneg (hpn0 ζ i)]
      exact hpn ζ hζ i
  refine ⟨hdiff, fun q' hq' => ⟨hHi q' hq', fun i => hPi i q' hq'⟩, fun i => ⟨hPi i 2 (by norm_num), ?_⟩⟩
  set e := Real.exp (-(2 * κ * bondDistToCell Y (j i))) with he
  have hw : Integrable fun ζ => ((M * e) ^ 2 * g ζ ^ 2) * ballDensity (cutoffFactor r p) Φ ζ := by
    simp_rw [mul_assoc]
    exact (good.2.2 2 (by norm_num)).const_mul _
  have h1 := ballExpectation_mono hg (u := fun ζ => |bondGradNorm H i ζ| ^ 2) (fun _ _ => by positivity) hw
    fun ζ hζ => by
      rw [abs_of_nonneg (hpn0 ζ i), ← mul_pow]
      exact pow_le_pow_left₀ (hpn0 ζ i) (hpn ζ hζ i) 2
  rw [ballExpectation_const_mul] at h1
  refine h1.trans ?_
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have h2 : (M * e) ^ 2 * ballExpectation (cutoffFactor r p) Φ (fun ζ => g ζ ^ 2) ≤ (M * e) ^ 2 * D :=
    mul_le_mul_of_nonneg_left hmean (by positivity)
  refine h2.trans ?_
  have h3 : D ≤ x * (1 + D) ^ 2 := by nlinarith [sq_nonneg D]
  calc (M * e) ^ 2 * D ≤ (M * e) ^ 2 * (x * (1 + D) ^ 2) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (Real.sqrt x * (M * (1 + D)) * e) ^ 2 := by rw [mul_pow, mul_pow, mul_pow, hsx]; ring
private theorem integrable_mul_radialWeightProd {r x κ h : ℝ} {p : ℝ → ℝ} {Φ H : BondField ι → ℝ} {dZ : ι → ℝ}
    (hg : BallLawFacts r p Φ) (hs : HasGradientBound r (cutoffFactor r p) Φ x κ h dZ H) :
    Integrable fun η => H η * radialWeightProd (cutoffFactor r p) η := by
  obtain ⟨C, hC, hle⟩ := hg.weight_le
  have hco : ContinuousOn H {ζ : BondField ι | ∀ i, ‖ζ i‖ < r} :=
    fun ζ hζ => (hs.1 ζ hζ).continuousAt.continuousWithinAt
  have hind : AEStronglyMeasurable (Set.indicator {ζ : BondField ι | ∀ i, ‖ζ i‖ < r} H) volume :=
    (aestronglyMeasurable_indicator_iff (isOpen_ballSet r).measurableSet).2
      (hco.aestronglyMeasurable (isOpen_ballSet r).measurableSet)
  have hm : AEStronglyMeasurable (fun η => H η * radialWeightProd (cutoffFactor r p) η) volume := by
    have e : (fun η => H η * radialWeightProd (cutoffFactor r p) η) =
        fun η => Set.indicator {ζ : BondField ι | ∀ i, ‖ζ i‖ < r} H η * radialWeightProd (cutoffFactor r p) η := by
      funext ζ
      by_cases hζ : ∀ i, ‖ζ i‖ < r
      · rw [Set.indicator_of_mem (show ζ ∈ {ζ : BondField ι | ∀ i, ‖ζ i‖ < r} from hζ)]
      · rw [hg.weight_off ζ hζ, mul_zero, mul_zero]
    rw [e]
    exact hind.mul hg.weight_measurable.aestronglyMeasurable
  refine Integrable.mono' (((hs.2.1 1 le_rfl).1).const_mul C) hm (Filter.Eventually.of_forall fun η => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hg.weight_nonneg η), pow_one]
  calc |H η| * radialWeightProd (cutoffFactor r p) η ≤ |H η| * (C * ballDensity (cutoffFactor r p) Φ η) :=
        mul_le_mul_of_nonneg_left (hle η) (abs_nonneg _)
    _ = _ := by ring
private theorem one_le_cutoffMajorant (p : ℝ → ℝ) (Y : F.Cell) (η : StepVariable (finiteCells F)) :
    1 ≤ cutoffMajorant p Y η := by
  unfold cutoffMajorant ColdHalfLaw.sumOverBlock
  have : 0 ≤ ∑ b : ↥(chordBonds (finiteCells F)), (open Classical in if enclosingCell b.1.1 = Y then
      |deriv p ‖η b‖| + |deriv (deriv p) ‖η b‖| else 0) :=
    Finset.sum_nonneg fun b _ => by split_ifs <;> positivity
  linarith
abbrev _root_.YangMills.SharedProofs.p29597 := @one_le_cutoffMajorant
private theorem ballLaw_of_convexCombination_two {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ} {t : ℕ}
    {x : ℝ} (hP : InterpolatedFrameBoundsAt T Cq Cz Cr t x) (hr : 0 < T.ballRadius) (hp : IsCutoff T.ballRadius T.p)
    (hLaw : ConvexObservables.normalizedBallLawIsProbabilityStatement)
    (d : ι → ι → ℝ) (M₀ M₁ : LawOnBondVariables ι) {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1)
    (a₀ : M₀.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀
      (frameRadius x) d)
    (a₁ : M₁.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀
      (frameRadius x) d)
    {Φ : BondField ι → ℝ}
    (hΦ : ∀ ζ, Φ ζ = w * M₀.exponent T.chainParams.lam x ζ + (1 - w) * M₁.exponent T.chainParams.lam x ζ) :
    BallLawFacts T.ballRadius T.p Φ ∧ LawMomentBounds T.ballRadius x T.κ T.Cs T.p Cq Cr d Φ := by
  have e : convexCombinationExponent T.chainParams.lam x ![w, 1 - w] ![M₀, M₁] = Φ := by
    funext ζ
    rw [hΦ]
    simp [convexCombinationExponent, Fin.sum_univ_two]
  obtain ⟨hconv, hm, -⟩ := hP.laws ι d 2 ![w, 1 - w] ![M₀, M₁]
    ⟨fun l => by fin_cases l <;> simp [h0, h1], by simp [Fin.sum_univ_two]⟩
    (fun l => by fin_cases l <;> simpa)
  rw [e] at hconv hm
  obtain ⟨Ψ', K', hΨ', hconvex, -, -⟩ := hconv
  exact ⟨ballLawFacts_of_eqOn hr hp hLaw hΨ' hconvex.smooth.continuous, hm⟩
theorem dominatedObservablesComparable_of_statements (hJ : EventuallyInParametersCombines)
    (hFB : interpolatedFramesStatement) (hLaw : ConvexObservables.normalizedBallLawIsProbabilityStatement)
    (hFew : Estimates.cellBondsCardStatement) :
    DominatedObservablesComparable := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cq, Cz, Cr, hP⟩ := hFB
  have h2 : EventuallyInParameters fun T => 2 ≤ T.n₀ ∧ 1 ≤ T.coupling := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨2, fun _ h => ⟨0, fun _ _ => ⟨1, fun _ hy => ⟨h, hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine weaken _ _ ?_ (join _ _ hP h2)
  rintro T hDr ⟨hPT, hn2, hy1⟩
  set Cr' := Cr (momentParameters T) with hCr'
  set N : ℕ := 4 * T.L ^ 4 with hNdef
  set D : ℝ := 2 + 4 * N * (N * (|Cr' 1 2 0| + |Cr' 2 2 0|)) with hDdef
  have hD : 0 ≤ D := by positivity
  refine ⟨2 * (1 + D), by positivity, ?_⟩
  intro t x f F V V' Y q ι _ _ j K M hfl hrow htop hV hV' hpair hM hK hK' hsh
  have hx1 : 1 ≤ x := hy1.trans hfl
  have hfam : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f :=
    ⟨hrow.smooth, hrow.gauge_invariant, hrow.translation_invariant, hrow.decay, hrow.locality⟩
  have hr : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  have hκ : 0 ≤ T.κ := hDr.κ_pos.le
  have hPx := hPT t x hfl
  obtain ⟨hLF, htt, n, hside, hn⟩ := id htop
  have hoddF : Odd F.blockSide := by rw [hLF]; exact hDr.odd_L
  have hN : (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y).card ≤ N := by
    have := hFew F hoddF (fun i => by rw [hside]; omega) Y
    rw [hLF] at this
    convert this
  set Q := coldHalfLawAt T x f with hQ
  have hα : 2 * (1 + D) * M = M * (1 + (2 * D + 1)) := by ring
  have hdom : D ≤ 2 * D + 1 := by linarith
  have hnear : ∀ b : ↥(chordBonds (finiteCells F)), enclosingCell b.1.1 = Y → b ∈ bondsNearCell Y q := fun b hb => by
    unfold bondsNearCell
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hz : cellSupDist Y Y = 0 := Nat.le_zero.1 (Finset.sup_le fun i _ => by simp)
    rw [hb, hz]
    simp
  have hjinj := hpair.isBoxPairing.injective_left
  have hid : ∀ Λ : Finset ↥(chordBonds (finiteCells F)),
      (∀ b : ↥(chordBonds (finiteCells F)), enclosingCell b.1.1 = Y → b ∈ Λ) →
      ∀ b : ↥(chordBonds (finiteCells F)), enclosingCell b.1.1 = Y → ∃ i ∈ Λ, id i = b :=
    fun Λ h b hb => ⟨b, h b hb, rfl⟩
  have admW : ∀ W : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) W → ∀ Λ : Finset ↥(chordBonds (finiteCells F)),
      (⟨F, W, id, Λ, Q.exponent W⟩ : LawOnBondVariables ↥(chordBonds (finiteCells F))).IsAdmissible T.a
        T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀ (frameRadius x)
        (chordBondDist F) := fun W hW Λ =>
    ⟨htop, hW, IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hfam, Function.injective_id, fun _ _ => rfl⟩
  have segLaw : ∀ W : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) W → ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
      BallLawFacts T.ballRadius T.p (freezingHomotopy T.chainParams.lam x (bondsNearCell Y q) (Q.exponent W) v) ∧
      LawMomentBounds T.ballRadius x T.κ T.Cs T.p (Cq (momentParameters T)) Cr' (chordBondDist F)
        (freezingHomotopy T.chainParams.lam x (bondsNearCell Y q) (Q.exponent W) v) := fun W hW v h0 h1 =>
    ballLaw_of_convexCombination_two hPx hr hDr.cutoff hLaw (chordBondDist F) _ _ h0 h1 (admW W hW Finset.univ)
      (admW W hW (bondsNearCell Y q))
      fun ζ => by
        simp only [LawOnBondVariables.exponent, frozenExponent, freezingHomotopy, extendByZero_id, Finset.sdiff_self,
          Finset.sum_empty, add_zero]
  have sideGrad : ∀ W : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) W →
      IsCutoffDominated T.ballRadius T.κ M T.p q Y (fun η => K η W) → ∀ Λ : Finset ↥(chordBonds (finiteCells F)),
      (∀ b : ↥(chordBonds (finiteCells F)), enclosingCell b.1.1 = Y → b ∈ Λ) → ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
      HasGradientBound T.ballRadius (cutoffFactor T.ballRadius T.p)
        (freezingHomotopy T.chainParams.lam x (bondsNearCell Y q) (Q.exponent W) v) x T.κ
        (2 * (1 + D) * M) (bondDistToCell Y) (fun η => K (_root_.YangMills.Construction.Interpolation.extendByZero id Λ η) W) := fun W hW hKW Λ hΛ v h0 h1 => by
    obtain ⟨hg, hm⟩ := segLaw W hW v h0 h1
    obtain ⟨good, hmean⟩ := cutoffMajorant_moments hg hm (j := id) (Λ := Λ) Function.injective_id (hid Λ hΛ) hN
    rw [hα]
    exact hasGradientBound_extendByZero hr hx1 hκ hM (by positivity) hg Function.injective_id good
      (hmean.trans hdom) hKW
  have hpid : ∀ (W : F.GaugeField F.top), (fun η => K (_root_.YangMills.Construction.Interpolation.extendByZero id Finset.univ η) W) = fun η => K η W := fun W => by
    funext η
    rw [extendByZero_id]
  have hseg1 : ∀ W : F.GaugeField F.top,
      freezingHomotopy T.chainParams.lam x (bondsNearCell Y q) (Q.exponent W) 1 = Q.exponent W := fun W => by
    funext η
    simp [freezingHomotopy]
  have side : ∀ W : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) W →
      IsCutoffDominated T.ballRadius T.κ M T.p q Y (fun η => K η W) →
      ComparisonHypothesesOnTorus T.ballRadius T.chainParams.lam x T.κ (2 * (1 + D) * M) T.p q Y (Q.exponent W)
        (fun η => K η W) :=
    fun W hW hKW => by
    have g1 := sideGrad W hW hKW Finset.univ (fun _ _ => Finset.mem_univ _)
    have g2 := sideGrad W hW hKW (bondsNearCell Y q) hnear
    rw [hpid] at g1
    refine ⟨?_, ?_, g1, g2, fun v h0 h1 => ?_⟩
    · have := g1 1 zero_le_one le_rfl
      rw [hseg1] at this
      have hg := (segLaw W hW 1 zero_le_one le_rfl).1
      rw [hseg1] at hg
      exact integrable_mul_radialWeightProd hg this
    · have := g2 1 zero_le_one le_rfl
      rw [hseg1] at this
      have hg := (segLaw W hW 1 zero_le_one le_rfl).1
      rw [hseg1] at hg
      exact integrable_mul_radialWeightProd hg this
    · have hg := (segLaw W hW v h0 h1).1
      have hC : M ≤ 2 * (1 + D) * M := by nlinarith
      refine abs_ballExpectation_le hg (fun η hη => (hKW.freeze_le η hη).trans ?_) (by positivity)
      exact mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
  have bound : ∀ W : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) W →
      IsCutoffDominated T.ballRadius T.κ M T.p q Y (fun η => K η W) →
      |Q.expectation W fun η => K η W| ≤ (1 + D) * M := fun W hW hKW => by
    have hl := segLaw W hW 1 zero_le_one le_rfl
    rw [hseg1] at hl
    obtain ⟨hg, hm⟩ := hl
    obtain ⟨good, hmean⟩ := cutoffMajorant_moments hg hm (j := id) (Λ := Finset.univ) Function.injective_id
      (hid _ fun _ _ => Finset.mem_univ _) hN
    simp only [extendByZero_id] at good hmean
    have hw : Integrable fun η =>
        (M * cutoffMajorant T.p Y η ^ 2) * ballDensity (cutoffFactor T.ballRadius T.p) (Q.exponent W) η := by
      simp_rw [mul_assoc]
      exact (good.2.2 2 (by norm_num)).const_mul _
    have h1 := ballExpectation_mono hg (u := fun η => |K η W|) (fun _ _ => abs_nonneg _) hw fun η hη => by
      have h1 := hKW.abs_le η hη
      have h2 := one_le_cutoffMajorant T.p Y η
      exact h1.trans (mul_le_mul_of_nonneg_left (by nlinarith) hM)
    rw [ballExpectation_const_mul] at h1
    have h2 := abs_ballExpectation_le_abs hg (fun η => K η W)
    have h3 : M * ballExpectation (cutoffFactor T.ballRadius T.p) (Q.exponent W)
        (fun η => cutoffMajorant T.p Y η ^ 2) ≤ M * D :=
      mul_le_mul_of_nonneg_left hmean hM
    show |ballExpectation (cutoffFactor T.ballRadius T.p) (Q.exponent W) fun η => K η W| ≤ _
    nlinarith
  have pLaw : ∀ th : ℝ, 0 ≤ th → th ≤ 1 →
      BallLawFacts T.ballRadius T.p (pairingHomotopy j j (Q.exponent V) (Q.exponent V') th) ∧
      LawMomentBounds T.ballRadius x T.κ T.Cs T.p (Cq (momentParameters T)) Cr'
        (fun i i' => chordBondDist F (j i) (j i'))
        (pairingHomotopy j j (Q.exponent V) (Q.exponent V') th) := fun th h0 h1 =>
    ballLaw_of_convexCombination_two hPx hr hDr.cutoff hLaw (fun i i' => chordBondDist F (j i) (j i'))
      ⟨F, V, j, Finset.univ, Q.exponent V⟩ ⟨F, V', j, Finset.univ, Q.exponent V'⟩ h0 h1
      ⟨htop, hV, IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hfam, hjinj, fun _ _ => rfl⟩
      ⟨htop, hV', IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hfam, hjinj, fun _ _ => rfl⟩
      fun ζ => by
        simp only [LawOnBondVariables.exponent, frozenExponent, pairingHomotopy, toTorus, Finset.sdiff_self,
          Finset.sum_empty, add_zero]
  have hcovj : ∀ b : ↥(chordBonds (finiteCells F)), enclosingCell b.1.1 = Y → ∃ i ∈ Finset.univ, j i = b :=
    fun b hb => by
    obtain ⟨i, hi⟩ := (hpair.isBoxPairing.mem_left_iff b).1 (hnear b hb)
    exact ⟨i, Finset.mem_univ _, hi⟩
  have pGrad : ∀ W : F.GaugeField F.top, IsCutoffDominated T.ballRadius T.κ M T.p q Y (fun η => K η W) →
      ∀ th : ℝ, 0 ≤ th → th ≤ 1 →
      HasGradientBound T.ballRadius (cutoffFactor T.ballRadius T.p)
        (pairingHomotopy j j (Q.exponent V) (Q.exponent V') th) x T.κ
        (2 * (1 + D) * M) (fun i => bondDistToCell Y (j i)) (fun ζ => K (toTorus j ζ) W) := fun W hKW th h0 h1 => by
    obtain ⟨hg, hm⟩ := pLaw th h0 h1
    obtain ⟨good, hmean⟩ := cutoffMajorant_moments hg hm hjinj hcovj hN
    rw [hα]
    exact hasGradientBound_extendByZero hr hx1 hκ hM (by positivity) hg hjinj good (hmean.trans hdom) hKW
  refine ⟨hK.smooth, hK'.smooth, side V hV hK, side V' hV' hK', ?_,
    fun th h0 h1 => ⟨pGrad V hK th h0 h1, pGrad V' hK' th h0 h1⟩, fun hq th h0 h1 => ?_⟩
  · have b1 := bound V hV hK
    have b2 := bound V' hV' hK'
    obtain ⟨l1, u1⟩ := abs_le.1 b1
    obtain ⟨l2, u2⟩ := abs_le.1 b2
    have e1 : Q.expectation V (fun η => K η V) =
        ballExpectation (cutoffFactor T.ballRadius T.p) (Q.exponent V) (fun η => K η V) := rfl
    have e2 : Q.expectation V' (fun η => K η V') =
        ballExpectation (cutoffFactor T.ballRadius T.p) (Q.exponent V') (fun η => K η V') := rfl
    rw [e1] at l1 u1
    rw [e2] at l2 u2
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · have hg := (pLaw th h0 h1).1
    have hC : M ≤ 2 * (1 + D) * M := by nlinarith
    refine abs_ballExpectation_le hg (fun ζ hζ => (hsh hq ζ hζ).trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
end ResponseInTheExpansion
end YangMills.Construction
end
