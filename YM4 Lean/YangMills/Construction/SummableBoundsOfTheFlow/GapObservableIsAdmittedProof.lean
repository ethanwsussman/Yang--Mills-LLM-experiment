import YangMills.Construction.ResponseInTheExpansion.CalculusOfTwoMoves
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionHasTheConditionsOfThirdOrderProof
import YangMills.Construction.SummableBoundsOfTheFlow.FromTheMirrorFramesToTheLeastFieldProof
import YangMills.Construction.SummableBoundsOfTheFlow.GapObservableIsAdmitted
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeOfACutHasItsSize
import YangMills.Construction.SummableBoundsOfTheFlow.WeightPartIsAdmittedProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation TorusComparison Estimates ConvexObservables
namespace TorusFreezing
namespace BlockGap
open LocalCalculus
section Laws
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {p : ℝ → ℝ}
private theorem radialWeightProd_eq_zero_of_not_mem {η : BondField ι} (hη : η ∉ openPolyball ι ρ) :
    radialWeightProd (cutoffFactor ρ p) η = 0 := by apply _root_.YangMills.SharedProofs.p17620 <;> assumption
private theorem ballDensity_congr {Φ₁ Φ₂ : BondField ι → ℝ} (h : ∀ η ∈ openPolyball ι ρ, Φ₁ η = Φ₂ η) :
    ballDensity (cutoffFactor ρ p) Φ₁ = ballDensity (cutoffFactor ρ p) Φ₂ := by apply _root_.YangMills.SharedProofs.p18172 <;> assumption
private theorem ballExpectation_congr_density {Φ₁ Φ₂ : BondField ι → ℝ}
    (h : ballDensity (cutoffFactor ρ p) Φ₁ = ballDensity (cutoffFactor ρ p) Φ₂) (f : BondField ι → ℝ) :
    ballExpectation (cutoffFactor ρ p) Φ₁ f = ballExpectation (cutoffFactor ρ p) Φ₂ f := by apply _root_.YangMills.SharedProofs.p53358 <;> assumption
private theorem integrable_mul_radialWeightProd (hρ : 0 < ρ) {Ψ H : BondField ι → ℝ} (hΨ : Continuous Ψ)
    (hi : Integrable fun η => H η * ballDensity (cutoffFactor ρ p) Ψ η) :
    Integrable fun η => H η * radialWeightProd (cutoffFactor ρ p) η := by
  obtain ⟨M, hM₀⟩ := (isCompact_closedBall (0 : BondField ι) ρ).exists_bound_of_continuousOn
    hΨ.continuousOn
  have hM : ∀ η ∈ openPolyball ι ρ, |Ψ η| ≤ M := fun η hη => by
    have : η ∈ Metric.closedBall (0 : BondField ι) ρ := by
      rw [openPolyball_eq_ball hρ] at hη
      exact Metric.ball_subset_closedBall hη
    simpa using hM₀ η this
  set g : BondField ι → ℝ := fun η => Real.exp (max (-M) (min M (Ψ η))) with hg
  have hgc : Continuous g := by
    simp only [hg]
    exact Real.continuous_exp.comp (continuous_const.max (continuous_const.min hΨ))
  have hb : ∀ η, ‖g η‖ ≤ Real.exp |M| := by
    intro η
    simp only [hg, Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    refine max_le ?_ ((min_le_left _ _).trans (le_abs_self M))
    have := neg_abs_le M
    have h2 := neg_le_abs M
    linarith
  have h1 : Integrable fun η => (H η * ballDensity (cutoffFactor ρ p) Ψ η) * g η :=
    hi.mul_bdd (c := Real.exp |M|) hgc.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine h1.congr (Filter.Eventually.of_forall fun η => ?_)
  by_cases hη : η ∈ openPolyball ι ρ
  · have h3 := abs_le.1 (hM η hη)
    have e1 : max (-M) (min M (Ψ η)) = Ψ η := by
      rw [min_eq_right h3.2, max_eq_right h3.1]
    simp only [hg, e1, ballDensity]
    rw [mul_assoc, mul_assoc, ← Real.exp_add]
    simp
  · simp [ballDensity, radialWeightProd_eq_zero_of_not_mem hη]
private structure ContinuousMomentLaw (ρ x κ C : ℝ) (p : ℝ → ℝ) (Cq : ℕ → ℝ) (Cr : ℕ → ℕ → ℕ → ℝ)
    (d : ι → ι → ℝ) (Φ : BondField ι → ℝ) : Prop where
  moments : LawMomentBounds ρ x κ C p Cq Cr d Φ
  exponent : ∃ Ψ : BondField ι → ℝ, Continuous Ψ ∧ ∀ η ∈ openPolyball ι ρ, Φ η = Ψ η
private theorem abs_add_pow_le (a b : ℝ) (q : ℕ) : |a + b| ^ q ≤ 2 ^ q * |a| ^ q + 2 ^ q * |b| ^ q := by
  have h1 : |a + b| ≤ 2 * max |a| |b| :=
    (abs_add_le a b).trans (by linarith [le_max_left |a| |b|, le_max_right |a| |b|])
  have h2 : |a + b| ^ q ≤ (2 * max |a| |b|) ^ q := pow_le_pow_left₀ (abs_nonneg _) h1 q
  rw [mul_pow] at h2
  have h3 : (max |a| |b|) ^ q ≤ |a| ^ q + |b| ^ q := by
    rcases le_total |a| |b| with h | h
    · rw [max_eq_right h]
      have := pow_nonneg (abs_nonneg a) q
      linarith
    · rw [max_eq_left h]
      have := pow_nonneg (abs_nonneg b) q
      linarith
  have h4 : (2 : ℝ) ^ q * (max |a| |b|) ^ q ≤ 2 ^ q * (|a| ^ q + |b| ^ q) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith [mul_add ((2 : ℝ) ^ q) (|a| ^ q) (|b| ^ q)]
private theorem aestronglyMeasurable_normalizedBallLaw (hlaw : normalizedBallLawIsProbabilityStatement)
    (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    {Ψ H : BondField ι → ℝ} (hΨ : Continuous Ψ) (hc : ContinuousOn H (openPolyball ι ρ)) :
    AEStronglyMeasurable H (normalizedBallLaw (cutoffFactor ρ p) Ψ) := by
  obtain ⟨-, -, -, l4, -⟩ := hlaw ι ρ p Ψ hρ hp hΨ
  have h := Measure.restrict_eq_self_of_ae_mem (μ := normalizedBallLaw (cutoffFactor ρ p) Ψ)
    (s := openPolyball ι ρ) l4
  rw [← h]
  exact hc.aestronglyMeasurable (isOpen_openPolyball hρ).measurableSet
private theorem hasGradientBound_of_hasLocalSize (hlaw : normalizedBallLawIsProbabilityStatement)
    (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    {x κ h α : ℝ} {Cq : ℕ → ℝ} {dZ : ι → ℝ} {Φ Ψ H : BondField ι → ℝ} (hΨ : Continuous Ψ)
    (hd : ballDensity (cutoffFactor ρ p) Φ = ballDensity (cutoffFactor ρ p) Ψ)
    (hc : ContinuousOn H (openPolyball ι ρ)) (hs : HasLocalSize ρ (cutoffFactor ρ p) Φ Cq x κ h dZ H)
    (hh : 0 ≤ h) (hC : 0 ≤ Cq 2) (hα : Cq 2 * h ≤ α) :
    HasGradientBound ρ (cutoffFactor ρ p) Φ x κ α dZ H := by
  obtain ⟨hdiff, H₀, hm⟩ := hs
  obtain ⟨l1, -, l3, -⟩ := hlaw ι ρ p Ψ hρ hp hΨ
  haveI := l1
  have hmeas := aestronglyMeasurable_normalizedBallLaw hlaw hρ hp hΨ hc
  refine ⟨hdiff, fun q hq => ⟨?_, fun b => ((hm q hq).2 b).1⟩, fun b => ?_⟩
  · rw [hd]
    refine (l3 _).1 ?_
    have h1 : Integrable (fun η => |H η - H₀| ^ q) (normalizedBallLaw (cutoffFactor ρ p) Ψ) :=
      (l3 _).2 (by rw [← hd]; exact (hm q hq).1.1)
    refine ((h1.const_mul (2 ^ q)).add (integrable_const ((2 : ℝ) ^ q * |H₀| ^ q))).mono'
      ((continuous_pow q).comp_aestronglyMeasurable (continuous_abs.comp_aestronglyMeasurable hmeas))
      (Filter.Eventually.of_forall fun η => ?_)
    have := abs_add_pow_le (H η - H₀) H₀ q
    rw [sub_add_cancel] at this
    simpa [abs_of_nonneg (pow_nonneg (abs_nonneg (H η)) q)] using this
  · have h2 := (hm 2 (by norm_num)).2 b
    refine ⟨h2.1, h2.2.trans ?_⟩
    have he := Real.exp_pos (-(2 * κ * dZ b))
    have hsx := Real.sqrt_nonneg x
    have e1 : Cq 2 * Real.sqrt x * h * Real.exp (-(2 * κ * dZ b)) =
        Real.sqrt x * (Cq 2 * h) * Real.exp (-(2 * κ * dZ b)) := by ring
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    rw [e1]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα hsx) he.le
private theorem abs_slope_term_le (e v : BondVector) :
    |deriv p ‖v‖ * ‖v‖⁻¹ * ⟪v, e⟫| ≤ |deriv p ‖v‖| * ‖e‖ := by
  rw [abs_mul, abs_mul, abs_inv, abs_norm]
  have h1 : |⟪v, e⟫| ≤ ‖v‖ * ‖e‖ := abs_real_inner_le_norm v e
  by_cases hv : ‖v‖ = 0
  · simp only [hv, inv_zero, mul_zero, zero_mul]
    positivity
  · have h0 : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    calc |deriv p ‖v‖| * ‖v‖⁻¹ * |⟪v, e⟫| ≤ |deriv p ‖v‖| * ‖v‖⁻¹ * (‖v‖ * ‖e‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = |deriv p ‖v‖| * ‖e‖ := by field_simp
private theorem abs_ballExpectation_cutoffSlope_le (hlaw : normalizedBallLawIsProbabilityStatement)
    (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    {x κ C E₀ : ℝ} {Cq : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ} {d : ι → ι → ℝ} {Φ : BondField ι → ℝ}
    (hR : ContinuousMomentLaw ρ x κ C p Cq Cr d Φ) {S : Finset ι} {e : BondField ι} (N : ℕ)
    (hE : 0 ≤ E₀) (hsup : ∀ b, b ∉ S → e b = 0) (hn : ∀ b, ‖e b‖ ≤ E₀) :
    |ballExpectation (cutoffFactor ρ p) Φ (cutoffSlope p e)| ≤ S.card * (E₀ * (Cr 1 1 N * (x ^ N)⁻¹)) := by
  obtain ⟨Ψ, hc, hag⟩ := hR.exponent
  have hd := ballDensity_congr (p := p) hag
  obtain ⟨l1, l2, l3, -⟩ := hlaw ι ρ p Ψ hρ hp hc
  haveI := l1
  have hi : ∀ b, Integrable (fun η : BondField ι => |iteratedDeriv 1 p ‖η b‖| ^ 1)
      (normalizedBallLaw (cutoffFactor ρ p) Ψ) := fun b => (l3 _).2 (by
    have := (hR.moments.cutoff_deriv_moments 1 1 N b le_rfl le_rfl).1
    rwa [hd] at this)
  have hb : ∀ b, ∫ η, |iteratedDeriv 1 p ‖η b‖| ^ 1 ∂normalizedBallLaw (cutoffFactor ρ p) Ψ ≤
      Cr 1 1 N * (x ^ N)⁻¹ :=
    fun b => by
      rw [l2, ← ballExpectation_congr_density hd]
      exact (hR.moments.cutoff_deriv_moments 1 1 N b le_rfl le_rfl).2
  have hG : Integrable (fun η : BondField ι => ∑ b ∈ S, E₀ * |iteratedDeriv 1 p ‖η b‖| ^ 1)
      (normalizedBallLaw (cutoffFactor ρ p) Ψ) := integrable_finset_sum _ fun b _ => (hi b).const_mul _
  have hle : ∀ η : BondField ι, ‖cutoffSlope p e η‖ ≤ ∑ b ∈ S, E₀ * |iteratedDeriv 1 p ‖η b‖| ^ 1 := by
    intro η
    have e1 : cutoffSlope p e η = ∑ b ∈ S, deriv p ‖η b‖ * ‖η b‖⁻¹ * ⟪η b, e b⟫ := by
      unfold cutoffSlope
      refine (Finset.sum_subset (Finset.subset_univ S) fun b _ hb => ?_).symm
      simp [hsup b hb]
    rw [e1, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    refine (abs_slope_term_le _ _).trans ?_
    rw [iteratedDeriv_one, pow_one, mul_comm]
    exact mul_le_mul_of_nonneg_right (hn b) (abs_nonneg _)
  have h1 := norm_integral_le_of_norm_le hG (Filter.Eventually.of_forall hle)
  rw [ballExpectation_congr_density hd, ← l2, ← Real.norm_eq_abs]
  refine h1.trans ?_
  rw [integral_finset_sum _ fun b _ => (hi b).const_mul _]
  calc ∑ b ∈ S, ∫ η, E₀ * |iteratedDeriv 1 p ‖η b‖| ^ 1 ∂normalizedBallLaw (cutoffFactor ρ p) Ψ
      ≤ ∑ _b ∈ S, E₀ * (Cr 1 1 N * (x ^ N)⁻¹) := Finset.sum_le_sum fun b _ => by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hb b) hE
    _ = S.card * (E₀ * (Cr 1 1 N * (x ^ N)⁻¹)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
private theorem cutoffSlope_regular (hlaw : normalizedBallLawIsProbabilityStatement)
    (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    {x κ C α h : ℝ} {Cq CqS : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ} {d : ι → ι → ℝ} {Φ : BondField ι → ℝ}
    {e : BondField ι} {dZ : ι → ℝ} (hR : ContinuousMomentLaw ρ x κ C p Cq Cr d Φ)
    (hsz : Integrable (ballDensity (cutoffFactor ρ p) Φ) →
      ContDiffOn ℝ 1 (cutoffSlope p e) {η | ∀ b, ‖η b‖ < ρ} ∧
        HasLocalSize ρ (cutoffFactor ρ p) Φ CqS x κ h dZ (cutoffSlope p e))
    (hh : 0 ≤ h) (hC : 0 ≤ CqS 2) (hα : CqS 2 * h ≤ α) :
    ContDiffOn ℝ 1 (cutoffSlope p e) {η | ∀ b, ‖η b‖ < ρ} ∧
      HasGradientBound ρ (cutoffFactor ρ p) Φ x κ α dZ (cutoffSlope p e) ∧
      Integrable fun η => cutoffSlope p e η * radialWeightProd (cutoffFactor ρ p) η := by
  obtain ⟨Ψ, hc, hag⟩ := hR.exponent
  have hd := ballDensity_congr (p := p) hag
  obtain ⟨l1, -, l3, -, -, -, l7, -⟩ := hlaw ι ρ p Ψ hρ hp hc
  haveI := l1
  obtain ⟨hs, hsize⟩ := hsz (by rw [hd]; exact l7)
  have hcon : ContinuousOn (cutoffSlope p e) (openPolyball ι ρ) := hs.continuousOn
  have hg := hasGradientBound_of_hasLocalSize hlaw hρ hp hc hd hcon hsize hh hC hα
  refine ⟨hs, hg, ?_⟩
  refine integrable_mul_radialWeightProd hρ hc ((l3 _).1 ?_)
  have hmeas := aestronglyMeasurable_normalizedBallLaw hlaw hρ hp hc hcon
  have h1 := (hg.2.1 1 le_rfl).1
  rw [hd] at h1
  have h2 := (l3 _).2 h1
  refine (integrable_norm_iff hmeas).1 ?_
  simpa [Real.norm_eq_abs] using h2
end Laws
section Cells
variable {F : BlockFrame}
private def gapDirection (a ρA : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top) {ι : Type}
    (j : ι → ↥(chordBonds (finiteCells F))) : BondField ι :=
  fun i => if enclosingCell (j i).1.1 = Y then _root_.YangMills.Construction.Interpolation.imaginaryCoords (frameGap a ρA m (j i).1 V) else 0
private theorem inner_imaginaryCoords (v : BondVector) (w : imaginaryQuaternions) :
    ⟪((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]), (w : ℍ[ℝ])⟫ = ⟪v, _root_.YangMills.Construction.Interpolation.imaginaryCoords w⟫ := by apply _root_.YangMills.Construction.FrameInterpolationProof.inner_toImaginary <;> assumption
private theorem norm_imaginaryCoords (w : imaginaryQuaternions) : ‖_root_.YangMills.Construction.Interpolation.imaginaryCoords w‖ = ‖w‖ := by apply _root_.YangMills.SharedProofs.p6124 <;> assumption
private theorem imaginaryCoords_sub (w w' : imaginaryQuaternions) :
    _root_.YangMills.Construction.Interpolation.imaginaryCoords w - _root_.YangMills.Construction.Interpolation.imaginaryCoords w' = _root_.YangMills.Construction.Interpolation.imaginaryCoords (w - w') := by
  ext i
  fin_cases i <;> simp [_root_.YangMills.Construction.Interpolation.imaginaryCoords]
private theorem extendByZero_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    {j : ι → ↥(chordBonds (finiteCells F))}
    (hj : Function.Injective j) (ζ : BondField ι) (i : ι) :
    _root_.YangMills.Construction.Interpolation.extendByZero j Finset.univ ζ (j i) = ζ i := by apply _root_.YangMills.Construction.SecondOrderMoves.toTorus_apply_self <;> assumption
private theorem blockGapObservable_extendByZero {ι : Type} [Fintype ι] [DecidableEq ι] (a ρA : ℝ) (m : ℕ)
    (p : ℝ → ℝ) (Y : F.Cell)
    (V : F.GaugeField F.top) {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j)
    (hr : ∀ b : ↥(chordBonds (finiteCells F)), enclosingCell b.1.1 = Y → ∃ i, j i = b) (ζ : BondField ι) :
    blockGapObservable a ρA m p Y V (_root_.YangMills.Construction.Interpolation.extendByZero j Finset.univ ζ) =
      cutoffSlope p (gapDirection a ρA m Y V j) ζ := by
  classical
  unfold blockGapObservable cutoffSlope
  set f : ↥(chordBonds (finiteCells F)) → ℝ := fun b => if enclosingCell b.1.1 = Y then
    deriv p ‖_root_.YangMills.Construction.Interpolation.extendByZero j Finset.univ ζ b‖ * ‖_root_.YangMills.Construction.Interpolation.extendByZero j Finset.univ ζ b‖⁻¹ *
      ⟪((toImaginary (_root_.YangMills.Construction.Interpolation.extendByZero j Finset.univ ζ b) : imaginaryQuaternions) : ℍ[ℝ]),
        ((frameGap a ρA m b.1 V : imaginaryQuaternions) : ℍ[ℝ])⟫
    else 0 with hf
  have h1 : ∑ b, f b = ∑ i, f (j i) := by
    rw [← Finset.sum_image (s := Finset.univ) (g := j) (fun a _ b _ h => hj h)]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro b _ hb
    simp only [hf]
    rw [if_neg]
    intro hc
    obtain ⟨i, rfl⟩ := hr b hc
    exact hb (Finset.mem_image_of_mem j (Finset.mem_univ i))
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hf, gapDirection, extendByZero_apply hj]
  by_cases hc : enclosingCell (j i).1.1 = Y
  · rw [if_pos hc, if_pos hc, inner_imaginaryCoords]
  · rw [if_neg hc, if_neg hc]
    simp
private theorem extendByZero_id (η : StepVariable (finiteCells F)) :
    _root_.YangMills.Construction.Interpolation.extendByZero (id : ↥(chordBonds (finiteCells F)) → _) Finset.univ η = η := by apply _root_.YangMills.Construction.InterpolatedBirths.extendByZero_id <;> assumption
private theorem blockGapObservable_eq_cutoffSlope (a ρA : ℝ) (m : ℕ) (p : ℝ → ℝ) (Y : F.Cell)
    (V : F.GaugeField F.top) :
    blockGapObservable a ρA m p Y V = cutoffSlope p (gapDirection a ρA m Y V id) := by
  funext η
  have h := blockGapObservable_extendByZero a ρA m p Y V (j := id) Function.injective_id
    (fun b _ => ⟨b, rfl⟩) η
  rwa [extendByZero_id] at h
private theorem cutoffSlope_sub {ι : Type} [Fintype ι] (p : ℝ → ℝ) (e e' ζ : BondField ι) :
    cutoffSlope p e ζ - cutoffSlope p e' ζ = cutoffSlope p (e - e') ζ := by
  unfold cutoffSlope
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.sub_apply, inner_sub_right]
  ring
private theorem cutoffSlope_freezeOutside (p : ℝ → ℝ) (Λ : Finset ↥(chordBonds (finiteCells F)))
    {e : BondField ↥(chordBonds (finiteCells F))} (hs : ∀ b, b ∉ Λ → e b = 0)
    (η : StepVariable (finiteCells F)) : cutoffSlope p e (freezeOutside Λ η) = cutoffSlope p e η := by
  unfold cutoffSlope
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : b ∈ Λ
  · have : freezeOutside Λ η b = η b := by
      simp only [freezeOutside, _root_.YangMills.Construction.Interpolation.extendByZero, id]
      rw [Finset.sum_ite_eq' Λ b, if_pos hb]
    rw [this]
  · simp [hs b hb]
private def singleLaw {ι : Type} [Fintype ι] [DecidableEq ι] (V : F.GaugeField F.top)
    (j : ι → ↥(chordBonds (finiteCells F))) (Λ : Finset ι) (Ψ : StepVariable (finiteCells F) → ℝ) :
    LawOnBondVariables ι := ⟨F, V, j, Λ, Ψ⟩
private theorem freezingHomotopy_eq_convexCombination (lam x v : ℝ) (V : F.GaugeField F.top)
    (Λ : Finset ↥(chordBonds (finiteCells F)))
    (Ψ : StepVariable (finiteCells F) → ℝ) :
    freezingHomotopy lam x Λ Ψ v = convexCombinationExponent lam x ![v, 1 - v]
      ![singleLaw V id Finset.univ Ψ, singleLaw V id Λ Ψ] := by
  funext η
  simp [-Finset.univ_eq_attach, freezingHomotopy, convexCombinationExponent, Fin.sum_univ_two,
    LawOnBondVariables.exponent, singleLaw, frozenExponent, extendByZero_id]
private theorem pairingHomotopy_eq_convexCombination {F' : BlockFrame} {ι : Type} [Fintype ι] [DecidableEq ι]
    (lam x th : ℝ)
    (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (j : ι → ↥(chordBonds (finiteCells F)))
    (j' : ι → ↥(chordBonds (finiteCells F'))) (Ψ : StepVariable (finiteCells F) → ℝ)
    (Ψ' : StepVariable (finiteCells F') → ℝ) :
    pairingHomotopy j j' Ψ Ψ' th = convexCombinationExponent lam x ![th, 1 - th]
      ![singleLaw V j Finset.univ Ψ, singleLaw V' j' Finset.univ Ψ'] := by
  funext ζ
  simp [pairingHomotopy, convexCombinationExponent, Fin.sum_univ_two, LawOnBondVariables.exponent,
    singleLaw, frozenExponent, toTorus]
private theorem isConvexWeights_two {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : IsConvexWeights ![v, 1 - v] := by apply _root_.YangMills.SharedProofs.p68332 <;> assumption
private theorem cellSupDist_self_eq_zero (Y : F.Cell) : cellSupDist Y Y = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
private theorem comparisonBoundsOnTorus_cutoffSlope {ρ lam x κ α : ℝ} {p : ℝ → ℝ} {q : ℕ} {Y : F.Cell}
    {Ψ : StepVariable (finiteCells F) → ℝ} {e : BondField ↥(chordBonds (finiteCells F))} (hα : 0 ≤ α)
    (hs : ∀ b, b ∉ bondsNearCell Y q → e b = 0)
    (hg : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → HasGradientBound ρ (cutoffFactor ρ p)
      (freezingHomotopy lam x (bondsNearCell Y q) Ψ v) x κ α (bondDistToCell Y) (cutoffSlope p e))
    (hi : Integrable fun η => cutoffSlope p e η * radialWeightProd (cutoffFactor ρ p) η) :
    ComparisonHypothesesOnTorus ρ lam x κ α p q Y Ψ (cutoffSlope p e) := by
  have e1 : (fun η => cutoffSlope p e (freezeOutside (bondsNearCell Y q) η)) = cutoffSlope p e :=
    funext (cutoffSlope_freezeOutside p _ hs)
  refine ⟨hi, ?_, hg, ?_, fun v _ _ => ?_⟩
  · simp only [cutoffSlope_freezeOutside p _ hs]
    exact hi
  · intro v h0 h1
    rw [e1]
    exact hg v h0 h1
  · simp only [cutoffSlope_freezeOutside p _ hs, sub_self]
    simp only [ballExpectation, zero_mul, integral_zero, zero_div, abs_zero]
    positivity
end Cells
section Pairs
variable {F F' : BlockFrame}
private theorem offset_eq_zero (hDist : cellOffsetStatement) (hL : Odd F.blockSide) {q : ℕ}
    (hq : ∀ i, 2 * q + 2 < F.extent i) {Y : F.Cell} {h : Fin 4 → ℤ} (hh : ∀ l, 2 * |h l| ≤ q)
    (he : Y + siteOfCoords F.top h = Y) : h = 0 := by
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by have := hq i; omega
  obtain ⟨-, -, -, d4⟩ := hDist F hL hs
  have h1 := (d4 q hq Y h 0 hh (fun l => by simp)).1
  rw [he] at h1
  rw [← h1]
  funext i
  simp [Estimates.cellOffset]
private theorem add_siteOfCoords_zero (Y : F.Cell) : (Y + siteOfCoords F.top (0 : Fin 4 → ℤ) : F.Cell) = Y := by apply _root_.YangMills.SharedProofs.p55653 <;> assumption
private theorem isShortPairing_offsets (hDist : cellOffsetStatement) (hL : Odd F.blockSide)
    (hL' : Odd F'.blockSide)
    (hLL : F'.blockSide = F.blockSide) {q : ℕ} (hq : ∀ i, 2 * q + 2 < F.extent i)
    (hq' : ∀ i, 2 * q + 2 < F'.extent i)
    {Y : F.Cell} {Y' : F'.Cell} {ι : Type} {j : ι → ↥(chordBonds (finiteCells F))}
    {j' : ι → ↥(chordBonds (finiteCells F'))} (hpair : IsShortPairing Y Y' q j j') (k : ι) :
    ∃ (h o : Fin 4 → ℤ) (k₀ : Fin 4), (∀ l, 2 * |h l| ≤ q) ∧ o ∈ centredCube F.blockSide ∧
      (j k).1 = fineBondAt Y h o k₀ ∧
      (j' k).1 = fineBondAt Y' h o k₀ ∧ enclosingCell (j k).1.1 = Y + siteOfCoords F.top h ∧
      enclosingCell (j' k).1.1 = Y' + siteOfCoords F'.top h := by
  have two : ∀ {G : BlockFrame}, (∀ i, 2 * q + 2 < G.extent i) → ∀ i, 2 ≤ G.extent i := fun h i => by
    have := h i
    omega
  obtain ⟨d1, -, -, -⟩ := hDist F hL (two hq)
  obtain ⟨f1, -, -, -⟩ := hDist F' hL' (two hq')
  obtain ⟨h, o, k₀, hs₀, ho, e1, e2⟩ := hpair.short_offsets k
  refine ⟨h, o, k₀, hs₀, ho, e1, e2, ?_, ?_⟩
  · rw [e1]
    exact d1 Y h o k₀ ho
  · rw [e2]
    exact f1 Y' h o k₀ (by rw [hLL]; exact ho)
private theorem isShortPairing_same_cell (hDist : cellOffsetStatement) (hL : Odd F.blockSide)
    (hL' : Odd F'.blockSide)
    (hLL : F'.blockSide = F.blockSide) {q : ℕ} (hq : ∀ i, 2 * q + 2 < F.extent i)
    (hq' : ∀ i, 2 * q + 2 < F'.extent i)
    {Y : F.Cell} {Y' : F'.Cell} {ι : Type} {j : ι → ↥(chordBonds (finiteCells F))}
    {j' : ι → ↥(chordBonds (finiteCells F'))} (hpair : IsShortPairing Y Y' q j j') (k : ι) :
    enclosingCell (j k).1.1 = Y ↔ enclosingCell (j' k).1.1 = Y' := by
  obtain ⟨h, o, k₀, hs₀, ho, e1, e2, c1, c2⟩ := isShortPairing_offsets hDist hL hL' hLL hq hq' hpair k
  constructor
  · intro hc
    have h0 := offset_eq_zero hDist hL hq hs₀ (c1.symm.trans hc)
    rw [c2, h0]
    exact add_siteOfCoords_zero Y'
  · intro hc
    have h0 := offset_eq_zero hDist hL' hq' hs₀ (c2.symm.trans hc)
    rw [c1, h0]
    exact add_siteOfCoords_zero Y
private theorem isShortPairing_preservesCellDist (hDist : cellOffsetStatement) (hL : Odd F.blockSide)
    (hL' : Odd F'.blockSide)
    (hLL : F'.blockSide = F.blockSide) {q : ℕ} (hq : ∀ i, 2 * q + 2 < F.extent i)
    (hq' : ∀ i, 2 * q + 2 < F'.extent i)
    {Y : F.Cell} {Y' : F'.Cell} {ι : Type} [Fintype ι] [DecidableEq ι]
    {j : ι → ↥(chordBonds (finiteCells F))}
    {j' : ι → ↥(chordBonds (finiteCells F'))} (hpair : IsShortPairing Y Y' q j j') :
    PreservesCellDist j'
      (fun k k' => (cellSupDist (enclosingCell (j k).1.1) (enclosingCell (j k').1.1) : ℝ)) := by
  have two : ∀ {G : BlockFrame}, (∀ i, 2 * q + 2 < G.extent i) → ∀ i, 2 ≤ G.extent i := fun h i => by
    have := h i
    omega
  obtain ⟨-, -, -, d4⟩ := hDist F hL (two hq)
  obtain ⟨-, -, -, f4⟩ := hDist F' hL' (two hq')
  intro k k'
  obtain ⟨a, -, -, ha, -, -, -, e1, e2⟩ := isShortPairing_offsets hDist hL hL' hLL hq hq' hpair k
  obtain ⟨b, -, -, hb, -, -, -, e3, e4⟩ := isShortPairing_offsets hDist hL hL' hLL hq hq' hpair k'
  simp only
  rw [e1, e2, e3, e4, (d4 q hq Y a b ha hb).2, (f4 q hq' Y' a b ha hb).2]
end Pairs
private theorem eventually_lower_bounds :
    EventuallyInParameters fun T => 2 ≤ T.blockIndex ∧ 4 * T.κ ≤ T.chainParams.δ₂ ∧ 1 ≤ T.n₀ ∧ 1 ≤ T.coupling := by
  intro a _
  refine ⟨0, fun L _ _ c hc => ?_⟩
  obtain ⟨⟨-, -, -, hδ₂, -⟩, -⟩ := hc.classical
  refine ⟨0, fun Ct _ => ⟨c.δ₂ / 4, by positivity, fun κ _ hκ => ⟨1, one_pos, fun η₃ _ _ _ =>
    ⟨2, fun nss hn => ⟨1, one_pos, fun σ _ _ p _ => ⟨0, fun Cs _ E _ => ⟨1, fun n₀ hn₀ =>
      ⟨0, fun CE _ => ⟨1, fun y₁ hy => ?_⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine ⟨hn, ?_, hn₀, hy⟩
  show 4 * κ ≤ c.δ₂
  linarith
private theorem card_mul_le {c n E Cr R xN : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ n) (hE : 0 ≤ E) (hR0 : 0 ≤ R)
    (hR : Cr ≤ R) (hx : 0 ≤ xN) : c * (E * (Cr * xN)) ≤ n * (E * (R * xN)) := by
  have h1 : E * (Cr * xN) ≤ E * (R * xN) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR hx) hE
  exact (mul_le_mul_of_nonneg_left h1 hc0).trans
    (mul_le_mul_of_nonneg_right hc (by positivity))
end BlockGap
set_option maxHeartbeats 1000000 in
open BlockGap LocalCalculus in
theorem gapObservableIsAdmissible_of_estimates (hJ : EventuallyInParametersCombines)
    (hF : interpolatedFramesStatement)
    (hS : cutoffSlopeSize) (hCnt : cellBondsCardStatement)
    (hDist : cellOffsetStatement) (hlaw : normalizedBallLawIsProbabilityStatement) :
    gapObservableIsAdmissible := by
  obtain ⟨Cq, Cz, Cr, hT⟩ := hF
  refine hJ.2 _ GapObservableIsAdmissible ?_ (hJ.1 _ _ hT eventually_lower_bounds)
  rintro T hD ⟨hFr, hnss, hκδ, hn₀, hy₁⟩ N
  have hσ : 0 < T.σ := hD.σ_pos
  have hρ : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  have hcut : IsCutoff T.ballRadius T.p := hD.cutoff
  obtain ⟨⟨-, -, -, hδ₂, -, hK, -⟩, -⟩ := hD.chain_admissible.classical
  obtain ⟨Cqn, hCqn⟩ : ∃ c, c = Cq (momentParameters T) := ⟨_, rfl⟩
  obtain ⟨Crn, hCrn⟩ : ∃ c, c = Cr (momentParameters T) := ⟨_, rfl⟩
  rw [← hCqn, ← hCrn] at hFr
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = 4 * T.L ^ 4 := ⟨_, rfl⟩
  obtain ⟨CqS, hC0, hsz⟩ := hS T.ballRadius T.p Crn n N hρ hcut
  obtain ⟨E₀, hE₀⟩ : ∃ E : ℝ, E = |T.Ct| * T.σ := ⟨_, rfl⟩
  have hE0 : 0 ≤ E₀ := by
    rw [hE₀]
    positivity
  obtain ⟨R, hRd⟩ : ∃ R : ℝ, R = |Crn 1 1 N| := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by
    rw [hRd]
    exact abs_nonneg _
  have hRle : Crn 1 1 N ≤ R := by
    rw [hRd]
    exact le_abs_self _
  obtain ⟨CN, hCN⟩ : ∃ c : ℝ, c = CqS 2 * E₀ + 2 * (n * (E₀ * R)) + n * (2 * T.chainParams.K * T.σ * R) :=
    ⟨_, rfl⟩
  have hCS := hC0 2
  have hCNa : CqS 2 * E₀ ≤ CN := by
    rw [hCN]
    have h1 : 0 ≤ (n : ℝ) * (E₀ * R) := by positivity
    have h2 : 0 ≤ (n : ℝ) * (2 * T.chainParams.K * T.σ * R) := by positivity
    linarith
  have hCNb : 2 * (n * (E₀ * R)) ≤ CN := by
    rw [hCN]
    have h1 : 0 ≤ CqS 2 * E₀ := by positivity
    have h2 : 0 ≤ (n : ℝ) * (2 * T.chainParams.K * T.σ * R) := by positivity
    linarith
  have hCNc : n * (2 * T.chainParams.K * T.σ * R) ≤ CN := by
    rw [hCN]
    have h1 : 0 ≤ CqS 2 * E₀ := by positivity
    have h2 : 0 ≤ (n : ℝ) * (E₀ * R) := by positivity
    linarith
  have hCN0 : 0 ≤ CN := le_trans (by positivity) hCNa
  refine ⟨CN, ?_⟩
  intro t x s φ F F' V V' Y Y' q ι _ _ j j' hx hs hs1 hφ hTF hTF' hV hV' hAg hpair hq
  have hx1 : 1 ≤ x := hy₁.trans hx
  obtain ⟨xN, hxN⟩ : ∃ c : ℝ, c = (x ^ N)⁻¹ := ⟨_, rfl⟩
  have hxN0 : 0 ≤ xN := by
    rw [hxN]
    positivity
  rw [← hxN]
  have hα : 0 ≤ CN * xN := by positivity
  have hFx := hFr t x hx
  have reads : ∀ (κ₀ : Type) [Fintype κ₀] [DecidableEq κ₀] (d : κ₀ → κ₀ → ℝ) (k : ℕ) (w : Fin k → ℝ)
      (M : Fin k → LawOnBondVariables κ₀), IsConvexWeights w →
      (∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀
        (frameRadius x) d) →
      ContinuousMomentLaw T.ballRadius x T.κ T.Cs T.p Cqn Crn d
        (convexCombinationExponent T.chainParams.lam x w M) := by
    intro κ₀ _ _ d k w M hw hM
    obtain ⟨hc, hm, -⟩ := hFx.laws κ₀ d k w M hw hM
    obtain ⟨Ψ, K, hag, hconv, -⟩ := hc
    exact ⟨hm, Ψ, hconv.smooth.continuous, fun η hη => (hag η hη).symm⟩
  have sides : ∀ {G : BlockFrame}, IsCubicTopTorus T.L t T.n₀ G →
      (∀ i, G.extent i = 0 ∨ 2 * q + 2 < G.extent i) →
      ∀ i, 2 * q + 2 < G.extent i := by
    intro G hG hA i
    obtain ⟨-, -, m, hm, hnm⟩ := hG
    rcases hA i with h | h
    · have := hm i
      omega
    · exact h
  have hq₁ := sides hTF hAg.1
  have hq₂ := sides hTF' hAg.2.1
  have hL : Odd F.blockSide := by
    rw [hTF.1]
    exact hD.odd_L
  have hL' : Odd F'.blockSide := by
    rw [hTF'.1]
    exact hD.odd_L
  have hLL : F'.blockSide = F.blockSide := hTF'.1.trans hTF.1.symm
  have two : ∀ {G : BlockFrame}, (∀ i, 2 * q + 2 < G.extent i) → ∀ i, 2 ≤ G.extent i := fun h i => by
    have := h i
    omega
  have gapLe : ∀ (G : BlockFrame) (W : G.GaugeField G.top) (Z : G.Cell) (κ₀ : Type)
      (j₀ : κ₀ → ↥(chordBonds (finiteCells G))), IsCubicTopTorus T.L t T.n₀ G →
      IsSmallCurvature (5 / 4 * T.σ) W → ∀ i,
      ‖gapDirection T.a T.chainParams.ρA (frameRadius x) Z W j₀ i‖ ≤ E₀ := by
    intro G W Z κ₀ j₀ hG hW i
    unfold gapDirection
    split_ifs with hc
    · rw [norm_imaginaryCoords]
      refine (((hFx.one_torus G W s hG hW hs hs1).near_minimizer.norm_eq_and_le (j₀ i).1 (j₀ i).2).2).trans ?_
      have he : Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x)) ≤ 1 := by
        apply Real.exp_le_one_iff.2
        have : 0 ≤ T.chainParams.δ₂ / 4 * frameRadius x := by positivity
        linarith
      have he0 := Real.exp_pos (-(T.chainParams.δ₂ / 4 * frameRadius x))
      have h1 : T.Ct * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x)) ≤ |T.Ct| :=
        calc T.Ct * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x))
            ≤ |T.Ct| * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x)) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) he0.le
          _ ≤ |T.Ct| * 1 := mul_le_mul_of_nonneg_left he (abs_nonneg _)
          _ = |T.Ct| := mul_one _
      rw [hE₀]
      exact mul_le_mul_of_nonneg_right h1 hσ.le
    · simpa using hE0
  have torus : ∀ (G : BlockFrame) (W : G.GaugeField G.top) (Z : G.Cell), IsCubicTopTorus T.L t T.n₀ G →
      IsSmallCurvature (5 / 4 * T.σ) W → (∀ i, 2 * q + 2 < G.extent i) →
      ComparisonHypothesesOnTorus T.ballRadius T.chainParams.lam x T.κ (CN * xN) T.p q Z
        (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ W)
        (blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Z W) ∧
      ContDiffOn ℝ 1 (blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Z W)
        {η | ∀ b, ‖η b‖ < T.ballRadius} ∧
      |ballExpectation (cutoffFactor T.ballRadius T.p) (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ W)
        (blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Z W)| ≤ n * (E₀ * (R * xN)) := by
    intro G W Z hG hW hsd
    rw [blockGapObservable_eq_cutoffSlope]
    obtain ⟨e, he⟩ : ∃ e, e = gapDirection T.a T.chainParams.ρA (frameRadius x) Z W
      (id : ↥(chordBonds (finiteCells G)) → _) := ⟨_, rfl⟩
    rw [← he]
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, Ψ = familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ W := ⟨_, rfl⟩
    rw [← hΨ]
    obtain ⟨S, hSd⟩ : ∃ S : Finset ↥(chordBonds (finiteCells G)),
        S = Finset.univ.filter fun b => enclosingCell b.1.1 = Z :=
      ⟨_, rfl⟩
    have hGo : Odd G.blockSide := by
      rw [hG.1]
      exact hD.odd_L
    have hcard : S.card ≤ n := by
      rw [hSd, hn, ← hG.1]
      exact hCnt G hGo (two hsd) Z
    have hsup : ∀ b, b ∉ S → e b = 0 := by
      intro b hb
      have : ¬ enclosingCell b.1.1 = Z := fun h =>
        hb (by rw [hSd]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      rw [he]
      simp [gapDirection, this]
    have hdZ : ∀ b ∈ S, bondDistToCell Z b = 0 := by
      intro b hb
      rw [hSd] at hb
      have := (Finset.mem_filter.1 hb).2
      simp [bondDistToCell, this, cellSupDist_self_eq_zero]
    have hnorm : ∀ b, ‖e b‖ ≤ E₀ := fun b => by
      rw [he]
      exact gapLe G W Z _ id hG hW b
    have hread : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → ContinuousMomentLaw T.ballRadius x T.κ T.Cs T.p Cqn Crn
        (fun b b' : ↥(chordBonds (finiteCells G)) =>
          (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℝ))
        (freezingHomotopy T.chainParams.lam x (bondsNearCell Z q) Ψ v) := by
      intro v h0 h1
      rw [freezingHomotopy_eq_convexCombination T.chainParams.lam x v W]
      refine reads _ _ 2 _ _ (isConvexWeights_two h0 h1) (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
      · exact ⟨hG, hW, hΨ ▸ IsIntermediateLaw.ofFamily s φ hs hs1 hφ, Function.injective_id, fun _ _ => rfl⟩
      · exact ⟨hG, hW, hΨ ▸ IsIntermediateLaw.ofFamily s φ hs hs1 hφ, Function.injective_id, fun _ _ => rfl⟩
    have hamp : CqS 2 * (E₀ * xN) ≤ CN * xN := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hCNa hxN0
    have pack : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → _ := fun v h0 h1 =>
      cutoffSlope_regular (e := e) (dZ := bondDistToCell Z) (α := CN * xN) hlaw hρ hcut (hread v h0 h1)
        (fun hi => by
          have h := hsz _ x T.κ T.Cs Cqn _ _ S (bondDistToCell Z) e E₀ hx1 hE0 hcard (hread v h0 h1).moments hi
            hsup hdZ hnorm
          rw [← hxN] at h
          exact h)
        (by positivity) hCS hamp
    have hone : freezingHomotopy T.chainParams.lam x (bondsNearCell Z q) Ψ 1 = Ψ := by
      funext η
      simp [freezingHomotopy]
    have hnear : ∀ b, b ∉ bondsNearCell Z q → e b = 0 := by
      intro b hb
      refine hsup b fun hbS => hb ?_
      rw [hSd] at hbS
      have := (Finset.mem_filter.1 hbS).2
      simp [bondsNearCell, this, cellSupDist_self_eq_zero]
    refine ⟨comparisonBoundsOnTorus_cutoffSlope hα hnear (fun v h0 h1 => (pack v h0 h1).2.1)
      (pack 1 zero_le_one le_rfl).2.2,
      (pack 1 zero_le_one le_rfl).1, ?_⟩
    have h1 := abs_ballExpectation_cutoffSlope_le hlaw hρ hcut (hread 1 zero_le_one le_rfl) N hE0 hsup hnorm
    rw [hone, ← hxN] at h1
    exact h1.trans (card_mul_le (Nat.cast_nonneg _) (by exact_mod_cast hcard) hE0 hR0 hRle hxN0)
  obtain ⟨t₁, c₁, m₁⟩ := torus F V Y hTF hV hq₁
  obtain ⟨t₂, c₂, m₂⟩ := torus F' V' Y' hTF' hV' hq₂
  have hpr := hpair.isBoxPairing
  have hmemNear : ∀ {G : BlockFrame} (Z : G.Cell) (b : ↥(chordBonds (finiteCells G))),
      enclosingCell b.1.1 = Z → b ∈ bondsNearCell Z q := by
    intro G Z b hb
    simp [bondsNearCell, hb, cellSupDist_self_eq_zero]
  have hrj : ∀ b : ↥(chordBonds (finiteCells F)), enclosingCell b.1.1 = Y → ∃ i, j i = b := fun b hb =>
    (hpr.mem_left_iff b).1 (hmemNear Y b hb)
  have hrj' : ∀ b : ↥(chordBonds (finiteCells F')), enclosingCell b.1.1 = Y' → ∃ i, j' i = b := fun b hb =>
    (hpr.mem_right_iff b).1 (hmemNear Y' b hb)
  have hcell := isShortPairing_same_cell hDist hL hL' hLL hq₁ hq₂ hpair
  obtain ⟨d, hd⟩ : ∃ d : ι → ι → ℝ,
      d = fun k k' => (cellSupDist (enclosingCell (j k).1.1) (enclosingCell (j k').1.1) : ℝ) :=
    ⟨_, rfl⟩
  have hk₁ : PreservesCellDist j d := by
    rw [hd]
    exact fun _ _ => rfl
  have hk₂ : PreservesCellDist j' d := by
    rw [hd]
    exact isShortPairing_preservesCellDist hDist hL hL' hLL hq₁ hq₂ hpair
  obtain ⟨Ψ₁, hΨ₁⟩ : ∃ Ψ, Ψ = familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V := ⟨_, rfl⟩
  obtain ⟨Ψ₂, hΨ₂⟩ : ∃ Ψ, Ψ = familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ V' := ⟨_, rfl⟩
  have readsP : ∀ th : ℝ, 0 ≤ th → th ≤ 1 → ContinuousMomentLaw T.ballRadius x T.κ T.Cs T.p Cqn Crn d
      (pairingHomotopy j j' Ψ₁ Ψ₂ th) := by
    intro th h0 h1
    rw [pairingHomotopy_eq_convexCombination T.chainParams.lam x th V V']
    refine reads _ _ 2 _ _ (isConvexWeights_two h0 h1) (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · exact ⟨hTF, hV, hΨ₁ ▸ IsIntermediateLaw.ofFamily s φ hs hs1 hφ, hpr.injective_left, hk₁⟩
    · exact ⟨hTF', hV', hΨ₂ ▸ IsIntermediateLaw.ofFamily s φ hs hs1 hφ, hpr.injective_right, hk₂⟩
  obtain ⟨S, hSd⟩ : ∃ S : Finset ι, S = Finset.univ.filter fun i => enclosingCell (j i).1.1 = Y := ⟨_, rfl⟩
  have hcard : S.card ≤ n := by
    have h1 : S.card ≤
        (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y).card := by
      refine Finset.card_le_card_of_injOn j (fun i hi => ?_) hpr.injective_left.injOn
      rw [hSd] at hi
      have := (Finset.mem_filter.1 hi).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩
    refine h1.trans ?_
    rw [hn, ← hTF.1]
    exact hCnt F hL (two hq₁) Y
  obtain ⟨e₁, he₁⟩ : ∃ e, e = gapDirection T.a T.chainParams.ρA (frameRadius x) Y V j := ⟨_, rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e, e = gapDirection T.a T.chainParams.ρA (frameRadius x) Y' V' j' := ⟨_, rfl⟩
  have hsup₁ : ∀ i, i ∉ S → e₁ i = 0 := by
    intro i hi
    have : ¬ enclosingCell (j i).1.1 = Y := fun h =>
      hi (by rw [hSd]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [he₁]
    simp [gapDirection, this]
  have hsup₂ : ∀ i, i ∉ S → e₂ i = 0 := by
    intro i hi
    have : ¬ enclosingCell (j' i).1.1 = Y' := fun h =>
      hi (by rw [hSd]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hcell i).2 h⟩)
    rw [he₂]
    simp [gapDirection, this]
  have hdZ : ∀ i ∈ S, (fun i => bondDistToCell Y (j i)) i = 0 := by
    intro i hi
    rw [hSd] at hi
    have := (Finset.mem_filter.1 hi).2
    simp [bondDistToCell, this, cellSupDist_self_eq_zero]
  have hnorm₁ : ∀ i, ‖e₁ i‖ ≤ E₀ := fun i => by
    rw [he₁]
    exact gapLe F V Y _ j hTF hV i
  have hnorm₂ : ∀ i, ‖e₂ i‖ ≤ E₀ := fun i => by
    rw [he₂]
    exact gapLe F' V' Y' _ j' hTF' hV' i
  have hread₁ : (fun ζ => blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Y V (toTorus j ζ)) =
      cutoffSlope T.p e₁ := by
    funext ζ
    rw [he₁]
    exact blockGapObservable_extendByZero _ _ _ _ _ _ hpr.injective_left hrj ζ
  have hread₂ : (fun ζ => blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Y' V' (toTorus j' ζ)) =
      cutoffSlope T.p e₂ := by
    funext ζ
    rw [he₂]
    exact blockGapObservable_extendByZero _ _ _ _ _ _ hpr.injective_right hrj' ζ
  have hamp : CqS 2 * (E₀ * xN) ≤ CN * xN := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hCNa hxN0
  refine ⟨⟨t₁, t₂, ?_, ?_, ?_⟩, c₁, c₂⟩
  · refine (abs_sub _ _).trans ?_
    have h1 : n * (E₀ * (R * xN)) + n * (E₀ * (R * xN)) ≤ CN * xN := by
      have := mul_le_mul_of_nonneg_right hCNb hxN0
      nlinarith
    linarith
  · intro th h0 h1
    rw [hread₁, hread₂, ← hΨ₁, ← hΨ₂]
    refine ⟨(cutoffSlope_regular (e := e₁) (dZ := fun i => bondDistToCell Y (j i)) (α := CN * xN) hlaw hρ hcut
      (readsP th h0 h1) (fun hi => ?_) (by positivity) hCS hamp).2.1,
      (cutoffSlope_regular (e := e₂) (dZ := fun i => bondDistToCell Y (j i)) (α := CN * xN) hlaw hρ hcut
      (readsP th h0 h1) (fun hi => ?_) (by positivity) hCS hamp).2.1⟩
    · have h := hsz _ x T.κ T.Cs Cqn _ _ S _ e₁ E₀ hx1 hE0 hcard (readsP th h0 h1).moments hi hsup₁ hdZ hnorm₁
      rw [← hxN] at h
      exact h
    · have h := hsz _ x T.κ T.Cs Cqn _ _ S _ e₂ E₀ hx1 hE0 hcard (readsP th h0 h1).moments hi hsup₂ hdZ hnorm₂
      rw [← hxN] at h
      exact h
  · intro hnq th h0 h1
    have hq2 : 2 ≤ q := hnss.trans hnq
    have hloc := ((hFx.two_tori F F' V V' Y Y' q s hTF hTF' hV hV' hAg hs hs1).1)
    have hside₁ : ∀ i, 4 * frameRadius x + 5 < F.extent i := fun i => by
      have := hq₁ i
      omega
    have hside₂ : ∀ i, 4 * frameRadius x + 5 < F'.extent i := fun i => by
      have := hq₂ i
      omega
    obtain ⟨E₂, hE₂⟩ : ∃ E : ℝ, E = 2 * T.chainParams.K * T.σ * Real.exp (-(4 * T.κ * q)) := ⟨_, rfl⟩
    have hE₂0 : 0 ≤ E₂ := by
      rw [hE₂]
      positivity
    have hdiff : ∀ i, ‖(e₁ - e₂) i‖ ≤ E₂ := by
      intro i
      by_cases hc : enclosingCell (j i).1.1 = Y
      · have hc' := (hcell i).1 hc
        obtain ⟨h, o, k₀, hs₀, ho, a1, a2, -, -⟩ := isShortPairing_offsets hDist hL hL' hLL hq₁ hq₂ hpair i
        have hcl : enclosingCell (fineBondAt Y h o k₀).1 = Y := by
          rw [← a1]
          exact hc
        have hbox : IsFineBondWithinRadius Y q h o k₀ := by
          refine ⟨ho, a1 ▸ (j i).2, fun l => ?_, ?_, ?_⟩
          · have := hs₀ l
            have h0 := abs_nonneg (h l)
            linarith
          · rw [hcl, cellSupDist_self_eq_zero]
            exact Nat.zero_le _
          · have := TopLevelSites.cellSupDist_enclosingCell_step_le hL (two hq₁) (fineBondAt Y h o k₀).1 k₀
            rw [hcl] at this
            omega
        have hm : (frameRadius x : ℝ) < (q : ℝ) - cellSupDist Y (enclosingCell (fineBondAt Y h o k₀).1) := by
          rw [hcl, cellSupDist_self_eq_zero]
          have h3 : 4 * (frameRadius x : ℝ) < q := by exact_mod_cast hq
          simp only [Nat.cast_zero, sub_zero]
          linarith
        obtain ⟨-, f2, f3⟩ := hloc.eq_far_inside hside₁ hside₂ h o k₀ hbox hm
        rw [he₁, he₂]
        simp only [Pi.sub_apply, gapDirection, if_pos hc, if_pos hc']
        rw [imaginaryCoords_sub, norm_imaginaryCoords, a1, a2, f2, norm_neg]
        refine f3.trans ?_
        rw [hcl, cellSupDist_self_eq_zero, hE₂]
        have hexp : Real.exp (-(T.chainParams.δ₂ * ((q : ℝ) - (0 : ℕ)))) ≤ Real.exp (-(4 * T.κ * q)) := by
          apply Real.exp_le_exp.mpr
          simp only [Nat.cast_zero, sub_zero]
          nlinarith
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
      · have hc' : ¬ enclosingCell (j' i).1.1 = Y' := fun h => hc ((hcell i).2 h)
        rw [he₁, he₂]
        simpa [gapDirection, hc, hc'] using hE₂0
    have hsupD : ∀ i, i ∉ S → (e₁ - e₂) i = 0 := fun i hi => by
      simp [hsup₁ i hi, hsup₂ i hi]
    have hfun : (fun ζ => blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Y V (toTorus j ζ) -
        blockGapObservable T.a T.chainParams.ρA (frameRadius x) T.p Y' V' (toTorus j' ζ)) =
          cutoffSlope T.p (e₁ - e₂) := by
      funext ζ
      rw [← cutoffSlope_sub, ← congrFun hread₁ ζ, ← congrFun hread₂ ζ]
    rw [hfun, ← hΨ₁, ← hΨ₂]
    have h2 := abs_ballExpectation_cutoffSlope_le hlaw hρ hcut (readsP th h0 h1) N hE₂0 hsupD hdiff
    rw [← hxN] at h2
    refine h2.trans ((card_mul_le (n := (n : ℝ)) (Nat.cast_nonneg _) (by exact_mod_cast hcard) hE₂0 hR0 hRle
      hxN0).trans ?_)
    rw [hE₂]
    have hee := Real.exp_pos (-(4 * T.κ * q))
    have e3 : (n : ℝ) * (2 * T.chainParams.K * T.σ * Real.exp (-(4 * T.κ * q)) * (R * xN)) =
        (n * (2 * T.chainParams.K * T.σ * R)) * xN * Real.exp (-(4 * T.κ * q)) := by ring
    rw [e3]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCNc hxN0) hee.le
end TorusFreezing
end YangMills.Construction
end
