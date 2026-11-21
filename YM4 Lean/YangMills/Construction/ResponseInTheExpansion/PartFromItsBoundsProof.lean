import YangMills.Construction.ColdStepAtMirrorFrames.MomentOfASquareBoundProof
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.ResponseInTheExpansion.PartFromItsBounds
import YangMills.Construction.SummableBoundsOfTheFlow.SlicesOfASmoothFunction
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation ConvexObservables WeightedResponses
namespace ResponseInTheExpansion
namespace RemainderMoments
variable {ι : Type} [Fintype ι]
private theorem pow_weighted_sum_le (w z : ι → ℝ) (hw : ∀ b, 0 ≤ w b) (hz : ∀ b, 0 ≤ z b) {q : ℕ} (hq : 1 ≤ q) :
    (∑ b, w b * z b) ^ q ≤ (∑ b, w b) ^ (q - 1) * ∑ b, w b * z b ^ q := by apply _root_.YangMills.SharedProofs.p74209 <;> assumption
private theorem linear_add_cubic_pow_le {y : ℝ} (hy : 0 ≤ y) (q : ℕ) :
    (y + y ^ 3) ^ q ≤ 2 ^ q * (2 + y ^ (6 * q)) := by
  have h0 : 0 ≤ y + y ^ 3 := by positivity
  rcases le_total y 1 with h | h
  · have h1 : y + y ^ 3 ≤ 2 := by
      have : y ^ 3 ≤ 1 := pow_le_one₀ hy h
      linarith
    calc (y + y ^ 3) ^ q ≤ 2 ^ q := pow_le_pow_left₀ h0 h1 q
      _ = 2 ^ q * 1 := by ring
      _ ≤ 2 ^ q * (2 + y ^ (6 * q)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : 0 ≤ y ^ (6 * q) := by positivity
          linarith
  · have h1 : y + y ^ 3 ≤ 2 * y ^ (3 : ℕ) := by
      have : y ≤ y ^ 3 := le_self_pow₀ h (by norm_num)
      linarith
    have h2 : (y ^ 3) ^ q ≤ y ^ (6 * q) := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ h (by omega)
    calc (y + y ^ 3) ^ q ≤ (2 * y ^ 3) ^ q := pow_le_pow_left₀ h0 h1 q
      _ = 2 ^ q * (y ^ 3) ^ q := by rw [mul_pow]
      _ ≤ 2 ^ q * (2 + y ^ (6 * q)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
variable [DecidableEq ι]
theorem momentBound_of_linear_cubic_bound (hLaw : normalizedBallLawIsProbabilityStatement) {ρ x : ℝ} {p : ℝ → ℝ}
    {Ψ : BondField ι → ℝ}
    {Cm : ℕ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hΨ : Continuous Ψ) (hx : 1 ≤ x)
    (hm : ∀ (q : ℕ) (b : ι), ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ (2 * q)) ≤ Cm q * (x ^ q)⁻¹)
    (H : BondField ι → ℝ) (B S : ℝ) (w : ι → ℝ) (q : ℕ) (hq : 1 ≤ q) (hB : 0 ≤ B) (hw : ∀ b, 0 ≤ w b)
    (hS : ∑ b, w b ≤ S) (hc : ContinuousOn H {η | ∀ b, ‖η b‖ < ρ})
    (hb : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |H η| ≤ B * ∑ b, w b * (‖η b‖ + x * ‖η b‖ ^ 3)) :
    MomentBound (cutoffFactor ρ p) Ψ H q (2 * S * B * (2 + |Cm (3 * q)|) * x ^ (-(1 / 2) : ℝ)) := by
  set r := cutoffFactor ρ p with hr
  obtain ⟨hprob, hmean, hint, hball, -, hdens0, hdensI, hZ, -, -, -⟩ := hLaw ι ρ p Ψ hρ hp hΨ
  set P := normalizedBallLaw r Ψ with hP
  have hx0 : 0 < x := by linarith
  set U : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ} with hU
  have hUo : IsOpen U := by
    have : U = ⋂ b, {η : BondField ι | ‖η b‖ < ρ} := by
      ext η
      simp [hU]
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt ((continuous_apply b).norm) continuous_const
  have hPU : ∀ᵐ η ∂P, η ∈ U := hball
  have hrestr : P.restrict U = P := Measure.restrict_eq_self_of_ae_mem hPU
  have hHm : AEStronglyMeasurable H P := by
    rw [← hrestr]
    exact hc.aestronglyMeasurable hUo.measurableSet
  set s := Real.sqrt x with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hx0
  have hss : s * s = x := Real.mul_self_sqrt hx0.le
  have hxs : x ^ (-(1 / 2) : ℝ) = s⁻¹ := by
    rw [hs, Real.sqrt_eq_rpow, Real.rpow_neg hx0.le]
  set S₁ := ∑ b, w b with hS₁
  have hS₁0 : 0 ≤ S₁ := Finset.sum_nonneg fun b _ => hw b
  set D := 2 + |Cm (3 * q)| with hD
  have hD1 : 1 ≤ D := by
    have := abs_nonneg (Cm (3 * q))
    linarith
  let φ : ι → BondField ι → ℝ := fun b η => 2 + x ^ (3 * q) * ‖η b‖ ^ (2 * (3 * q))
  have hqb : ∀ b : ι, Integrable (fun η : BondField ι => ‖η b‖ ^ (2 * (3 * q))) P := by
    intro b
    refine Integrable.of_bound (C := ρ ^ (2 * (3 * q))) ?_ ?_
    · exact ((continuous_apply b).norm.pow _).aestronglyMeasurable
    · filter_upwards [hPU] with η hη
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hη b).le _
  have hφI : ∀ b, Integrable (φ b) P := fun b => (integrable_const _).add ((hqb b).const_mul _)
  have hφ : ∀ b, ∫ η, φ b η ∂P ≤ D := by
    intro b
    have e : ∫ η, φ b η ∂P = 2 + x ^ (3 * q) * ∫ η, ‖η b‖ ^ (2 * (3 * q)) ∂P := by
      simp only [φ]
      rw [integral_add (integrable_const _) ((hqb b).const_mul _), integral_const_mul]
      simp
    rw [e, hmean]
    have h1 := hm (3 * q) b
    have hp0 : 0 < x ^ (3 * q) := pow_pos hx0 _
    have h2 : x ^ (3 * q) * ballExpectation r Ψ (fun η => ‖η b‖ ^ (2 * (3 * q))) ≤ Cm (3 * q) := by
      calc x ^ (3 * q) * ballExpectation r Ψ (fun η => ‖η b‖ ^ (2 * (3 * q))) ≤
            x ^ (3 * q) * (Cm (3 * q) * (x ^ (3 * q))⁻¹) := mul_le_mul_of_nonneg_left h1 hp0.le
        _ = Cm (3 * q) := by field_simp
    have := le_abs_self (Cm (3 * q))
    rw [hD]
    linarith
  set c₀ := (B * s⁻¹) ^ q * (S₁ ^ (q - 1) * 2 ^ q) with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set g : BondField ι → ℝ := fun η => c₀ * ∑ b, w b * φ b η with hg
  have hle : ∀ η ∈ U, |H η| ^ q ≤ g η := by
    intro η hη
    have hyb : ∀ b, ‖η b‖ + x * ‖η b‖ ^ 3 = s⁻¹ * (s * ‖η b‖ + (s * ‖η b‖) ^ 3) := fun b => by
      rw [← hss]
      field_simp
    have h1 : |H η| ≤ B * s⁻¹ * ∑ b, w b * (s * ‖η b‖ + (s * ‖η b‖) ^ 3) := by
      refine (hb η hη).trans (le_of_eq ?_)
      have e : ∑ b, w b * (‖η b‖ + x * ‖η b‖ ^ 3) = s⁻¹ * ∑ b, w b * (s * ‖η b‖ + (s * ‖η b‖) ^ 3) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by
          rw [hyb b]
          ring
      rw [e]
      ring
    have hz0 : ∀ b, 0 ≤ s * ‖η b‖ + (s * ‖η b‖) ^ 3 := fun b => by positivity
    have h2 := pow_weighted_sum_le w (fun b => s * ‖η b‖ + (s * ‖η b‖) ^ 3) hw hz0 hq
    have h3 : ∑ b, w b * (s * ‖η b‖ + (s * ‖η b‖) ^ 3) ^ q ≤ 2 ^ q * ∑ b, w b * φ b η := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b _ => ?_
      have h4 := linear_add_cubic_pow_le (y := s * ‖η b‖) (by positivity) q
      have h5 : (s * ‖η b‖) ^ (6 * q) = x ^ (3 * q) * ‖η b‖ ^ (2 * (3 * q)) := by
        rw [mul_pow, ← hss, ← mul_pow, ← pow_two, ← pow_mul]
        ring
      rw [h5] at h4
      calc w b * (s * ‖η b‖ + (s * ‖η b‖) ^ 3) ^ q ≤ w b * (2 ^ q * φ b η) :=
            mul_le_mul_of_nonneg_left h4 (hw b)
        _ = 2 ^ q * (w b * φ b η) := by ring
    calc |H η| ^ q ≤ (B * s⁻¹ * ∑ b, w b * (s * ‖η b‖ + (s * ‖η b‖) ^ 3)) ^ q :=
          pow_le_pow_left₀ (abs_nonneg _) h1 q
      _ = (B * s⁻¹) ^ q * (∑ b, w b * (s * ‖η b‖ + (s * ‖η b‖) ^ 3)) ^ q := by rw [mul_pow]
      _ ≤ (B * s⁻¹) ^ q * (S₁ ^ (q - 1) * (2 ^ q * ∑ b, w b * φ b η)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
      _ = g η := by
          simp only [hg, hc₀]
          ring
  have hsumI : Integrable (fun η => ∑ b, w b * φ b η) P :=
    integrable_finsetSum _ fun b _ => (hφI b).const_mul _
  have hgI : Integrable g P := hsumI.const_mul _
  have hHq : Integrable (fun η => |H η| ^ q) P := by
    refine Integrable.mono' hgI ((hHm.norm.pow q).congr ?_) ?_
    · exact Filter.Eventually.of_forall fun η => by simp
    · filter_upwards [hPU] with η hη
      rw [Real.norm_of_nonneg (by positivity)]
      exact hle η hη
  refine ⟨(hint _).mp hHq, ?_⟩
  rw [← hmean]
  have hmain : ∫ η, |H η| ^ q ∂P ≤ ∫ η, g η ∂P :=
    integral_mono_ae hHq hgI (by filter_upwards [hPU] with η hη using hle η hη)
  refine hmain.trans ?_
  have hgval : ∫ η, g η ∂P = c₀ * ∑ b, w b * ∫ η, φ b η ∂P := by
    simp only [hg]
    rw [integral_const_mul, integral_finsetSum _ fun b _ => (hφI b).const_mul _]
    congr 1
    exact Finset.sum_congr rfl fun b _ => integral_const_mul _ _
  rw [hgval, hxs]
  have hsum : ∑ b, w b * ∫ η, φ b η ∂P ≤ S₁ * D := by
    rw [hS₁, Finset.sum_mul]
    exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hφ b) (hw b)
  have hSS : S₁ ≤ S := hS
  have hS0 : 0 ≤ S := hS₁0.trans hS
  have hDq : D ≤ D ^ q := le_self_pow₀ hD1 (by omega)
  have hq' : S₁ ^ (q - 1) * S₁ = S₁ ^ q := by
    rw [← pow_succ]
    congr 1
    omega
  calc c₀ * ∑ b, w b * ∫ η, φ b η ∂P ≤ c₀ * (S₁ * D) := mul_le_mul_of_nonneg_left hsum hc₀0
    _ = (B * s⁻¹) ^ q * 2 ^ q * (S₁ ^ q * D) := by
        rw [hc₀, ← hq']
        ring
    _ ≤ (B * s⁻¹) ^ q * 2 ^ q * (S ^ q * D ^ q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (pow_le_pow_left₀ hS₁0 hSS q) hDq (by linarith) (by positivity)
    _ = (2 * S * B * D * s⁻¹) ^ q := by
        rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow]
        ring
theorem abs_ballExpectation_le_of_momentBound (hLaw : normalizedBallLawIsProbabilityStatement) {ρ : ℝ} {p : ℝ → ℝ}
    {Ψ H : BondField ι → ℝ} {Bd : ℝ}
    (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hΨ : Continuous Ψ) (hm : MomentBound (cutoffFactor ρ p) Ψ H 1 Bd) :
    |ballExpectation (cutoffFactor ρ p) Ψ H| ≤ Bd := by
  obtain ⟨-, hmean, -⟩ := hLaw ι ρ p Ψ hρ hp hΨ
  have h1 := hm.2
  rw [pow_one] at h1
  rw [← hmean] at h1 ⊢
  refine (norm_integral_le_integral_norm H).trans ?_
  simpa using h1
theorem integrable_mul_ballDensity_of_momentBound (hLaw : normalizedBallLawIsProbabilityStatement) {ρ : ℝ}
    {p : ℝ → ℝ} {Ψ H : BondField ι → ℝ}
    {Bd : ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hΨ : Continuous Ψ) (hc : ContinuousOn H {η | ∀ b, ‖η b‖ < ρ})
    (hm : MomentBound (cutoffFactor ρ p) Ψ H 1 Bd) :
    Integrable fun η => H η * ballDensity (cutoffFactor ρ p) Ψ η := by
  obtain ⟨-, -, hint, hball, -⟩ := hLaw ι ρ p Ψ hρ hp hΨ
  have hUo : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by
    have : {η : BondField ι | ∀ b, ‖η b‖ < ρ} = ⋂ b, {η : BondField ι | ‖η b‖ < ρ} := by
      ext η
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt ((continuous_apply b).norm) continuous_const
  have hrestr := Measure.restrict_eq_self_of_ae_mem hball
  have hHm : AEStronglyMeasurable H (normalizedBallLaw (cutoffFactor ρ p) Ψ) := by
    rw [← hrestr]
    exact hc.aestronglyMeasurable hUo.measurableSet
  have h1 := (hint _).2 hm.1
  refine (hint H).1 ?_
  exact (integrable_norm_iff hHm).1 (h1.congr (Filter.Eventually.of_forall fun η => by simp))
private theorem momentBound_mono {r : ℝ → ℝ} {Ψ H : BondField ι → ℝ} {q : ℕ} {B B' : ℝ} (h0 : 0 ≤ B)
    (h : B ≤ B') (hm : MomentBound r Ψ H q B) : MomentBound r Ψ H q B' :=
  ⟨hm.1, hm.2.trans (pow_le_pow_left₀ h0 h q)⟩
private theorem momentBound_of_ballDensity_eq {r : ℝ → ℝ} {Ψ Ψ' H : BondField ι → ℝ} {q : ℕ} {B : ℝ}
    (hd : ballDensity r Ψ = ballDensity r Ψ') (hm : MomentBound r Ψ' H q B) : MomentBound r Ψ H q B := by
  unfold MomentBound ballExpectation at *
  rw [hd]
  exact hm
private theorem value_constant_le {a Cq CF y E : ℝ} (ha : a ≤ Cq) (ha0 : 0 ≤ a) (hCF : 1 ≤ CF) (hy : 0 ≤ y)
    (hE : 0 ≤ E) : a * y * E ≤ Cq * (CF * y * E) := by
  have hC : 0 ≤ Cq := ha0.trans ha
  have h1 : a * (y * E) ≤ Cq * (y * E) := mul_le_mul_of_nonneg_right ha (by positivity)
  have h2 : Cq * (y * E) ≤ Cq * (CF * (y * E)) := by
    apply mul_le_mul_of_nonneg_left _ hC
    nlinarith [mul_nonneg hy hE]
  calc a * y * E = a * (y * E) := by ring
    _ ≤ Cq * (CF * (y * E)) := h1.trans h2
    _ = Cq * (CF * y * E) := by ring
private theorem gradient_constant_le {a Cq CF s y E e : ℝ} (ha : a ≤ Cq) (ha0 : 0 ≤ a) (hCF : 1 ≤ CF)
    (hsy : s * y = 1) (hE : 0 ≤ E) (he : 0 ≤ e) : a * (E * e) ≤ Cq * s * (CF * y * E) * e := by
  have e1 : Cq * s * (CF * y * E) * e = Cq * CF * (E * e) := by
    calc Cq * s * (CF * y * E) * e = Cq * CF * (E * e) * (s * y) := by ring
      _ = Cq * CF * (E * e) := by rw [hsy, mul_one]
  rw [e1]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  nlinarith
end RemainderMoments
open RemainderMoments in
theorem remainderOfBounds_holds (hFB : interpolatedFramesStatement)
    (hLaw : normalizedBallLawIsProbabilityStatement)
    (hFew : Estimates.cellBondsCardStatement) (hSum : CellCounting.ExpDecaySumBounded)
    (hSl : SmoothSlices.IteratedFDerivSlices) (hM : momentBoundOfQuadraticBound)
    (hG : CubicTorusCellGeometry) (hJ : EventuallyInParametersCombines) : remainderOfBoundsStatement := by
  classical
  intro A hA
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cm, Cz, Cr, hP⟩ := hFB
  obtain ⟨hg1, -⟩ := hG
  choose! Wf hWf0 hWf using hSum
  let S₀ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U => Wf (4 * U.L ^ 4) U.κ
  let W₂ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U => Wf (4 * U.L ^ 4) (2 * U.κ)
  let Cmo : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ := fun U => Cm (momentParameters U)
  let CqF : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ := fun U q => |2 * S₀ U * A U * (2 + |Cmo U (3 * q)|)| +
    |lpMomentConstant U.chainParams.lam (S₀ U) (W₂ U) q * A U|
  let CF : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U => 1 + |2 * S₀ U * A U * (2 + |Cmo U (3 * 1)|)|
  refine ⟨CqF, CF, fun T q => by positivity, fun T => by positivity, ?_⟩
  have hlarge : EventuallyInParameters fun T => 64 ≤ T.n₀ ∧ 1 ≤ T.coupling := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨64, fun _ h => ⟨0, fun _ _ => ⟨1, fun _ hy => ⟨h, hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine weaken _ _ ?_ (join _ _ hP hlarge)
  rintro T hDr ⟨hPT, hlarge', hy1⟩
  intro t x f F V Y K hst hb
  have hfl : T.coupling ≤ x := hst.coupling_le
  have hx1 : 1 ≤ x := hy1.trans hfl
  have hx : 0 < x := by linarith
  have hPT' := hPT t x hfl
  set Q := coldHalfLawAt T x f with hQ
  set U := parametersBeforeSide T with hU
  let M : LawOnBondVariables ↥(chordBonds (finiteCells F)) := lawAtTop V (Q.exponent V)
  have hadm : M.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀
      (frameRadius x) (chordBondDist F) :=
    ⟨hst.torus, hst.small_curvature, IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hst.family_bounded,
      Function.injective_id, fun _ _ => rfl⟩
  obtain ⟨hconv, hmoms, -⟩ := hPT'.laws _ (chordBondDist F) 1 (fun _ => 1) (fun _ => M)
    ⟨fun _ => zero_le_one, by simp⟩ (fun _ => hadm)
  rw [convexCombinationExponent_lawAtTop] at hconv hmoms
  obtain ⟨Ψ', K', hΨ', hconvex, hslope, -⟩ := hconv
  have hΨc : Continuous Ψ' := hconvex.smooth.continuous
  have hρ : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  have hκ : 0 < T.κ := hDr.κ_pos
  have hlam : 0 < T.chainParams.lam := hDr.chain_admissible.positivity.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hnz, -⟩ := hLaw _ T.ballRadius T.p Ψ' hρ hDr.cutoff hΨc
  have hz : ∀ η : BondField ↥(chordBonds (finiteCells F)), ¬ (∀ b, ‖η b‖ < T.ballRadius) →
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ' η = 0 := fun η hη => by
    by_contra hne
    exact hη ((hnz η).1 hne)
  have hd : ballDensity (cutoffFactor T.ballRadius T.p) (Q.exponent V) =
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ' := by
    funext η
    by_cases hη' : ∀ b, ‖η b‖ < T.ballRadius
    · unfold ballDensity
      rw [hΨ' η hη']
    · have h0 := hz η hη'
      have h1 : radialWeightProd (cutoffFactor T.ballRadius T.p) η = 0 := by
        unfold ballDensity at h0
        rcases mul_eq_zero.1 h0 with h | h
        · exact h
        · exact absurd h (Real.exp_pos _).ne'
      rw [h0]
      unfold ballDensity
      rw [h1, zero_mul]
  obtain ⟨hLF, htt, n, hside, hn⟩ := hst.torus
  have hnpos : 64 ≤ n := hlarge'.trans hn
  have hoddF : Odd F.blockSide := by rw [hLF]; exact hDr.odd_L
  have hcub : IsLargeCubicTorus F := ⟨n, hnpos, hside⟩
  obtain ⟨-, -, hsym, htri, -⟩ := hg1 F hoddF hcub
  have hN : ∀ z : F.Cell,
      (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤
      4 * U.L ^ 4 := fun z => by
    have := hFew F hoddF (fun i => by rw [hside]; omega) z
    rwa [hLF] at this
  set y : ↥(chordBonds (finiteCells F)) → F.Cell := fun b => enclosingCell b.1.1 with hy
  have hS₀ : 0 ≤ S₀ U := hWf0 _ _ hκ
  have hW₂ : 0 ≤ W₂ U := hWf0 _ _ (by show 0 < 2 * T.κ; positivity)
  have hWκ : ∀ z : F.Cell, ∑ b, Real.exp (-(T.κ * (cellSupDist (y b) z : ℝ))) ≤ S₀ U := fun z =>
    hWf _ _ hκ F _ y hN z
  have hW2 : ∀ b₀, ∑ b, Real.exp (-(2 * T.κ * chordBondDist F b b₀)) ≤ W₂ U := fun b₀ =>
    hWf _ (2 * T.κ) (by positivity) F _ y hN (y b₀)
  have hself : ∀ a : F.Cell, cellSupDist a a = 0 := fun a => by
    simp [cellSupDist]
  have hbd : IsPseudoMetricOnBonds (chordBondDist F) := by
    refine ⟨fun b => ?_, fun b b' => ?_, fun b b' b'' => ?_⟩
    · simp [chordBondDist, hself]
    · simp only [chordBondDist]
      rw [hsym]
    · simp only [chordBondDist]
      exact_mod_cast htri _ _ _
  set r := cutoffFactor T.ballRadius T.p with hr
  have hmean_eq : ∀ g : StepVariable (finiteCells F) → ℝ,
      ballExpectation r (Q.exponent V) g = ballExpectation r Ψ' g := fun g => by
    unfold ballExpectation
    rw [hd]
  have hmom' : ∀ (q : ℕ) (b : ↥(chordBonds (finiteCells F))),
      ballExpectation r Ψ' (fun η => ‖η b‖ ^ (2 * q)) ≤ Cmo U q * (x ^ q)⁻¹ := fun q b => by
    rw [← hmean_eq]
    exact hmoms.moments q b
  set w : ↥(chordBonds (finiteCells F)) → ℝ :=
    fun b => Real.exp (-(T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) with hw
  have hw0 : ∀ b, 0 ≤ w b := fun b => (Real.exp_pos _).le
  have hAU : 0 ≤ A U := hA U
  let Ec : ∀ {k : ℕ}, (Fin k → F.Site F.top × Fin 4) → ℝ :=
    fun c => Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c))
  have hEc : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4), 0 ≤ Ec c := fun c => (Real.exp_pos _).le
  have hUo : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} := by
    have : {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} =
        ⋂ b, {η : StepVariable (finiteCells F) | ‖η b‖ < T.ballRadius} := by
      ext η; simp
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
  have smoothH : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (m : ℕ), m + k ≤ 2 →
      ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
      ContDiffAt ℝ m (fun ζ => bondDeriv (K ζ) V c X) η := by
    intro k c X m hmk η hη
    exact hSl.2.1 (Fin k → ℝ) (StepVariable (finiteCells F))
      (fun q => K q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) k m
      (fun l => Pi.single l 1) η ((hb.smooth η k c X fun b => (hη b).le).of_le (by exact_mod_cast hmk))
  have contH : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
      ContinuousOn (fun ζ => bondDeriv (K ζ) V c X) {η | ∀ b, ‖η b‖ < T.ballRadius} := fun c X hk η hη =>
    (smoothH c X 0 (by omega) η hη).continuousAt.continuousWithinAt
  have val : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
      AreUnitVectors X → ∀ q : ℕ, 1 ≤ q →
      MomentBound r Ψ' (fun ζ => bondDeriv (K ζ) V c X) q
        (2 * S₀ U * (A U * Ec c) * (2 + |Cmo U (3 * q)|) * x ^ (-(1 / 2) : ℝ)) := fun c X hk hX q hq =>
    momentBound_of_linear_cubic_bound hLaw hρ hDr.cutoff hΨc hx1 hmom' _ (A U * Ec c) (S₀ U) w q hq
      (mul_nonneg hAU (hEc c)) hw0 (hWκ Y) (contH c X hk) (hb.deriv_le _ c X hk hX)
  have grad : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 1 →
      AreUnitVectors X → ∀ q : ℕ, 1 ≤ q →
      ∀ b : ↥(chordBonds (finiteCells F)),
      MomentBound r Ψ' (bondGradNorm (fun ζ => bondDeriv (K ζ) V c X) b) q
        (lpMomentConstant T.chainParams.lam (S₀ U) (W₂ U) q *
          (A U * Ec c * Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) * 1)) := by
    intro k c X hk hX q hq b
    have hC1 : ContDiffOn ℝ 1 (fun ζ => bondDeriv (K ζ) V c X) {η | ∀ b, ‖η b‖ < T.ballRadius} := fun η hη =>
      (smoothH c X 1 (by omega) η hη).contDiffWithinAt
    have hgc : ContinuousOn (bondGradNorm (fun ζ => bondDeriv (K ζ) V c X) b)
        {η | ∀ b, ‖η b‖ < T.ballRadius} := by
      have h1 := hC1.continuousOn_fderiv_of_isOpen hUo le_rfl
      unfold bondGradNorm
      exact (h1.clm_comp continuousOn_const).norm
    refine hM _ T.ballRadius x T.chainParams.lam T.κ (W₂ U) (S₀ U) (chordBondDist F) Ψ' K' T.p hρ hx hlam hκ.le hW₂ hS₀
      hDr.cutoff hbd hconvex hW2 hslope _ _ 1 w q hq (by have := hEc c; positivity) zero_le_one hw0
      (by simpa using hWκ Y) hgc ?_
    intro η hη
    have h0 : 0 ≤ bondGradNorm (fun ζ => bondDeriv (K ζ) V c X) b η := norm_nonneg _
    rw [abs_of_nonneg h0]
    exact hb.gradNorm_le k c X hk hX η b hη
  have hCF1 : 1 ≤ CF U := by
    have := abs_nonneg (2 * S₀ U * A U * (2 + |Cmo U (3 * 1)|))
    simp only [CF]
    linarith
  set h := CF U * x ^ (-(1 / 2) : ℝ) with hh
  have hy0 : 0 < x ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hx _
  have hsx : Real.sqrt x * x ^ (-(1 / 2) : ℝ) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    norm_num
  have hm0 : ∀ q, 0 ≤ lpMomentConstant T.chainParams.lam (S₀ U) (W₂ U) q := fun q => by
    have : 0 ≤ ∏ k ∈ Finset.range q, (4 * (k : ℝ) + 8 * W₂ U) := Finset.prod_nonneg fun k _ => by positivity
    unfold lpMomentConstant
    positivity
  refine ⟨⟨fun η k c X hη => hb.smooth η k c X hη, fun k c X hk hX => ?_⟩, ?_, fun c X hX => ?_⟩
  · have hk1 : k ≤ 1 := by omega
    unfold ColdHalfLaw.HasSize HasLocalSize
    refine ⟨fun η hη => (smoothH c X 1 (by omega) η hη).differentiableAt (by norm_num), 0,
      fun q hq => ⟨?_, fun b => ?_⟩⟩
    · have hv : MomentBound r Ψ' (fun η => bondDeriv (K η) V c X - 0) q
          (2 * S₀ U * (A U * Ec c) * (2 + |Cmo U (3 * q)|) * x ^ (-(1 / 2) : ℝ)) := by
        simpa using val c X (by omega) hX q hq
      have ha0 : 0 ≤ 2 * S₀ U * A U * (2 + |Cmo U (3 * q)|) := by positivity
      have ha : 2 * S₀ U * A U * (2 + |Cmo U (3 * q)|) ≤ CqF U q := by
        simp only [CqF]
        have h1 := le_abs_self (2 * S₀ U * A U * (2 + |Cmo U (3 * q)|))
        have h2 := abs_nonneg (lpMomentConstant U.chainParams.lam (S₀ U) (W₂ U) q * A U)
        linarith
      refine momentBound_of_ballDensity_eq hd (momentBound_mono ?_ ?_ hv)
      · have := hEc c
        positivity
      · have := value_constant_le ha ha0 hCF1 hy0.le (hEc c)
        calc 2 * S₀ U * (A U * Ec c) * (2 + |Cmo U (3 * q)|) * x ^ (-(1 / 2) : ℝ) =
              2 * S₀ U * A U * (2 + |Cmo U (3 * q)|) * x ^ (-(1 / 2) : ℝ) * Ec c := by ring
          _ ≤ _ := this
    · have hv := grad c X hk1 hX q hq b
      have ha0 : 0 ≤ lpMomentConstant T.chainParams.lam (S₀ U) (W₂ U) q * A U := mul_nonneg (hm0 q) hAU
      have ha : lpMomentConstant T.chainParams.lam (S₀ U) (W₂ U) q * A U ≤ CqF U q := by
        have h1 := le_abs_self (lpMomentConstant T.chainParams.lam (S₀ U) (W₂ U) q * A U)
        have h2 := abs_nonneg (2 * S₀ U * A U * (2 + |Cmo U (3 * q)|))
        show _ ≤ |2 * S₀ U * A U * (2 + |Cmo U (3 * q)|)| + |lpMomentConstant T.chainParams.lam (S₀ U) (W₂ U) q * A U|
        linarith
      have he := (Real.exp_pos (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ)))).le
      refine momentBound_of_ballDensity_eq hd (momentBound_mono ?_ ?_ hv)
      · have := hEc c
        have := hm0 q
        positivity
      · have := gradient_constant_le ha ha0 hCF1 hsx (hEc c) he
        calc lpMomentConstant T.chainParams.lam (S₀ U) (W₂ U) q *
              (A U * Ec c * Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) * 1) =
              lpMomentConstant T.chainParams.lam (S₀ U) (W₂ U) q * A U *
                (Ec c * Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ)))) := by ring
          _ ≤ _ := this
  · have e0 : ∀ ζ, bondDeriv (K ζ) V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions) = K ζ V := fun ζ => by
      unfold bondDeriv
      rw [iteratedFDeriv_zero_apply, leftTranslate_bondSpread_zero]
    have hv := val (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)
      (by omega) (fun l => l.elim0) 1 le_rfl
    have i1 := integrable_mul_ballDensity_of_momentBound hLaw hρ hDr.cutoff hΨc (contH _ _ (by omega)) hv
    simp only [e0] at i1
    show Integrable fun η => K η V * ballDensity r (Q.exponent V) η
    rw [hd]
    exact i1
  · have hv := abs_ballExpectation_le_of_momentBound hLaw hρ hDr.cutoff hΨc (val c X le_rfl hX 1 le_rfl)
    show |ballExpectation r (Q.exponent V) _| ≤ _
    rw [hmean_eq]
    refine hv.trans ?_
    have ha0 : 0 ≤ 2 * S₀ U * A U * (2 + |Cmo U (3 * 1)|) := by positivity
    have ha : 2 * S₀ U * A U * (2 + |Cmo U (3 * 1)|) ≤ CF U := by
      simp only [CF]
      have h1 := le_abs_self (2 * S₀ U * A U * (2 + |Cmo U (3 * 1)|))
      linarith
    have := value_constant_le ha ha0 hCF1 hy0.le (hEc c)
    calc 2 * S₀ U * (A U * Ec c) * (2 + |Cmo U (3 * 1)|) * x ^ (-(1 / 2) : ℝ) =
          2 * S₀ U * A U * (2 + |Cmo U (3 * 1)|) * x ^ (-(1 / 2) : ℝ) * Ec c := by ring
      _ ≤ CF U * (CF U * x ^ (-(1 / 2) : ℝ) * Ec c) := this
      _ = CF U * h * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) := by
          rw [hh]
          simp only [Ec]
          ring
end ResponseInTheExpansion
end YangMills.Construction
end
