import YangMills.Construction.ClusterExpansionOfAStep.LawsOnProductsOfBalls
import YangMills.Construction.ColdStepAtMirrorFrames.CalculusOfLocalTerms
import YangMills.Construction.ColdStepAtMirrorFrames.GapsBetweenCompare
import YangMills.Construction.ColdStepAtMirrorFrames.HaarsBetweenCompare
import YangMills.Construction.ColdStepAtMirrorFrames.SlopesBetweenCompare
import YangMills.Construction.RunningCouplingSlope.ValueOfTheDensityOfTheStepOnTwoToriAtParametersProof
import YangMills.Construction.SummableBoundsOfTheFlow.LawsBetweenAreConvex
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetween
import YangMills.Construction.SummableBoundsOfTheFlow.PartsOfALawOfTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.TheBirthsBetweenProof
import YangMills.Construction.SummableBoundsOfTheFlow.WeightPartIsAdmitted
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation TorusComparison ConvexObservables FamilyNorms
  CellCounting Estimates SummableBounds
namespace TorusFreezing
namespace RemainderProof
open LocalCalculus
section Expectations
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {p : ℝ → ℝ}
private theorem radialWeightProd_eq_zero_of_not_mem {η : BondField ι} (hη : η ∉ openPolyball ι ρ) :
    radialWeightProd (cutoffFactor ρ p) η = 0 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BallLaws.radialWeightProd_eq_zero <;> assumption
abbrev _root_.YangMills.SharedProofs.p17620 := @radialWeightProd_eq_zero_of_not_mem
private theorem ballDensity_congr {Φ₁ Φ₂ : BondField ι → ℝ} (h : ∀ η ∈ openPolyball ι ρ, Φ₁ η = Φ₂ η) :
    ballDensity (cutoffFactor ρ p) Φ₁ = ballDensity (cutoffFactor ρ p) Φ₂ := by
  funext η
  by_cases hη : η ∈ openPolyball ι ρ
  · unfold ballDensity
    rw [h η hη]
  · simp [ballDensity, radialWeightProd_eq_zero_of_not_mem hη]
abbrev _root_.YangMills.SharedProofs.p18172 := @ballDensity_congr
private theorem ballExpectation_congr_of_density {Φ₁ Φ₂ : BondField ι → ℝ}
    (h : ballDensity (cutoffFactor ρ p) Φ₁ = ballDensity (cutoffFactor ρ p) Φ₂) (f : BondField ι → ℝ) :
    ballExpectation (cutoffFactor ρ p) Φ₁ f = ballExpectation (cutoffFactor ρ p) Φ₂ f := by
  unfold ballExpectation
  rw [h]
abbrev _root_.YangMills.SharedProofs.p53358 := @ballExpectation_congr_of_density
private theorem positiveForm_of_eqOn {Ψ Φ : BondField ι → ℝ} (F : IsPositiveUnitalForm ρ p Ψ)
    (h : ∀ η ∈ openPolyball ι ρ, Ψ η = Φ η) : IsPositiveUnitalForm ρ p Φ := by
  have hm : ∀ f, ballExpectation (cutoffFactor ρ p) Φ f = ballExpectation (cutoffFactor ρ p) Ψ f :=
    ballExpectation_congr_of_density (ballDensity_congr fun η hη => (h η hη).symm)
  refine ⟨?_, fun f g hfg => ?_, fun Ψ' f h' => ?_, fun f g hf hg hfg => ?_, fun f g hf hg => ?_,
    fun c f => ?_⟩
  · rw [hm]
    exact F.map_one
  · rw [hm, hm]
    exact F.congr_on f g hfg
  · rw [hm]
    exact F.congr_potential Ψ' f fun η hη => (h η hη).trans (h' η hη)
  · rw [hm, hm]
    exact F.mono f g hf hg hfg
  · rw [hm, hm, hm]
    exact F.map_add f g hf hg
  · rw [hm, hm]
    exact F.map_smul c f
private theorem integrable_mul_ballDensity (hlaw : normalizedBallLawIsProbabilityStatement) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) {Ψ f : BondField ι → ℝ} (hΨ : Continuous Ψ) (hf : IsBoundedContinuousOn ι ρ f) :
    Integrable fun η => f η * ballDensity (cutoffFactor ρ p) Ψ η := by
  obtain ⟨l1, -, l3, l4, -⟩ := hlaw ι ρ p Ψ hρ hp hΨ
  obtain ⟨hc, M, hM⟩ := hf
  have := l1
  refine (l3 _).1 ?_
  have hm : AEStronglyMeasurable f (normalizedBallLaw (cutoffFactor ρ p) Ψ) := by
    have h := Measure.restrict_eq_self_of_ae_mem (μ := normalizedBallLaw (cutoffFactor ρ p) Ψ)
      (s := openPolyball ι ρ) l4
    rw [← h]
    exact hc.aestronglyMeasurable (isOpen_openPolyball hρ).measurableSet
  exact Integrable.of_bound hm M (l4.mono fun η hη => by simpa [Real.norm_eq_abs] using hM η hη)
private theorem integrable_mul_radialWeightProd (hlaw : normalizedBallLawIsProbabilityStatement)
    (hρ : 0 < ρ) (hp : IsCutoff ρ p) {f : BondField ι → ℝ} (hf : IsBoundedContinuousOn ι ρ f) :
    Integrable fun η => f η * radialWeightProd (cutoffFactor ρ p) η := by
  have h := integrable_mul_ballDensity hlaw hρ hp (Ψ := fun _ => 0) continuous_const hf
  refine h.congr (Filter.Eventually.of_forall fun η => ?_)
  simp [ballDensity]
private theorem hasGradientBound_of_hasLocalSize (hlaw : normalizedBallLawIsProbabilityStatement)
    (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    {Φ Ψ H : BondField ι → ℝ} (hΨ : Continuous Ψ) (hag : ∀ η ∈ openPolyball ι ρ, Ψ η = Φ η)
    (hH : IsBoundedContinuousOn ι ρ H) {Cq : ℕ → ℝ} {x κ c α : ℝ} {dZ : ι → ℝ} (hc : 0 ≤ c)
    (hα : |Cq 2| * c ≤ α) (hs : HasLocalSize ρ (cutoffFactor ρ p) Φ Cq x κ c dZ H) :
    HasGradientBound ρ (cutoffFactor ρ p) Φ x κ α dZ H := by
  obtain ⟨hd, H₀, hm⟩ := hs
  have hdens := ballDensity_congr (p := p) hag
  refine ⟨hd, fun q hq => ⟨?_, fun b => ((hm q hq).2 b).1⟩,
    fun b => ⟨((hm 2 (by norm_num)).2 b).1, ?_⟩⟩
  · rw [← hdens]
    have hn : IsBoundedContinuousOn ι ρ (fun η => |H η| ^ q) := by
      obtain ⟨hc', M, hM⟩ := hH
      refine ⟨hc'.abs.pow q, M ^ q, fun η hη => ?_⟩
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM η hη) q
    exact integrable_mul_ballDensity hlaw hρ hp hΨ hn
  · refine ((hm 2 (by norm_num)).2 b).2.trans ?_
    have he : 0 < Real.exp (-(2 * κ * dZ b)) := Real.exp_pos _
    have hs0 := Real.sqrt_nonneg x
    have hα0 : 0 ≤ α := (mul_nonneg (abs_nonneg _) hc).trans hα
    apply sq_le_sq.2
    rw [abs_of_nonneg (a := Real.sqrt x * α * Real.exp (-(2 * κ * dZ b))) (by positivity),
      abs_mul, abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hs0, abs_of_pos he]
    have : |Cq 2| * Real.sqrt x * c = Real.sqrt x * (|Cq 2| * c) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα hs0) he.le
private theorem expectation_weightedSq_le {Φ : BondField ι → ℝ} (hρ : 0 < ρ)
    (F : IsPositiveUnitalForm ρ p Φ) {m : ℝ}
    (hm : ∀ b, ballExpectation (cutoffFactor ρ p) Φ (fun η => ‖η b‖ ^ 2) ≤ m) (w : ι → ℝ)
    (hw : ∀ b, 0 ≤ w b) :
    ballExpectation (cutoffFactor ρ p) Φ (fun η => ∑ b, w b * ‖η b‖ ^ 2) ≤ (∑ b, w b) * m := by
  rw [F.map_sum Finset.univ (fun b η => w b * ‖η b‖ ^ 2)
    (fun b _ => (IsBoundedContinuousOn.const _).mul (IsBoundedContinuousOn.norm_sq_apply hρ b)),
    Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [F.map_smul]
  exact mul_le_mul_of_nonneg_left (hm b) (hw b)
private theorem boundedContinuous_weightedSq (hρ : 0 < ρ) (w : ι → ℝ) :
    IsBoundedContinuousOn ι ρ (fun η => ∑ b, w b * ‖η b‖ ^ 2) :=
  IsBoundedContinuousOn.sum _ _ fun b _ =>
    (IsBoundedContinuousOn.const _).mul (IsBoundedContinuousOn.norm_sq_apply hρ b)
private theorem abs_expectation_le_of_quadratic {Φ f : BondField ι → ℝ} (hρ : 0 < ρ)
    (F : IsPositiveUnitalForm ρ p Φ)
    {m x B Ww : ℝ} (hx : 0 < x) (hm0 : 0 ≤ m)
    (hm : ∀ b, ballExpectation (cutoffFactor ρ p) Φ (fun η => ‖η b‖ ^ 2) ≤ m / x) (w : ι → ℝ)
    (hw : ∀ b, 0 ≤ w b) (hWw : ∑ b, w b ≤ Ww) (hf : IsBoundedContinuousOn ι ρ f) (hB : 0 ≤ B)
    (h : ∀ η ∈ openPolyball ι ρ, |f η| ≤ B * (x * (∑ b, w b * ‖η b‖ ^ 2) + 1)) :
    |ballExpectation (cutoffFactor ρ p) Φ f| ≤ B * (Ww * m + 1) := by
  have hq := boundedContinuous_weightedSq (ρ := ρ) hρ w
  have hg : IsBoundedContinuousOn ι ρ (fun η => (B * x) * (∑ b, w b * ‖η b‖ ^ 2) + B) :=
    ((IsBoundedContinuousOn.const _).mul hq).add (IsBoundedContinuousOn.const _)
  have h1 := abs_ballExpectation_le F hf hg fun η hη => by
    refine (h η hη).trans (le_of_eq ?_)
    ring
  have hconst : ballExpectation (cutoffFactor ρ p) Φ (fun _ => B) = B := by
    have := F.map_smul B (fun _ => 1)
    rw [F.map_one] at this
    simpa using this
  rw [F.map_add _ _ ((IsBoundedContinuousOn.const _).mul hq) (IsBoundedContinuousOn.const _), F.map_smul,
    hconst] at h1
  have h2 := expectation_weightedSq_le hρ F hm w hw
  have h3 : (∑ b, w b) * (m / x) ≤ Ww * (m / x) :=
    mul_le_mul_of_nonneg_right hWw (by positivity)
  have h4 : (B * x) * ballExpectation (cutoffFactor ρ p) Φ (fun η => ∑ b, w b * ‖η b‖ ^ 2) ≤
      (B * x) * (Ww * (m / x)) := mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
  have h5 : (B * x) * (Ww * (m / x)) = B * (Ww * m) := by
    field_simp
  linarith
private theorem abs_expectation_le_of_slopes {Φ f : BondField ι → ℝ} (hρ : 0 < ρ)
    (F : IsPositiveUnitalForm ρ p Φ)
    {m x B Ww Wu : ℝ} (hx : 1 ≤ x) (hm0 : 0 ≤ m)
    (hm : ∀ b, ballExpectation (cutoffFactor ρ p) Φ (fun η => ‖η b‖ ^ 2) ≤ m / x) (w u : ι → ℝ)
    (hw : ∀ b, 0 ≤ w b) (hu : ∀ b, 0 ≤ u b) (hWw : ∑ b, w b ≤ Ww) (hWu : ∑ b, u b ≤ Wu)
    (hf : IsBoundedContinuousOn ι ρ f) (hB : 0 ≤ B)
    (h : ∀ η ∈ openPolyball ι ρ, |f η| ≤
      B * ∑ b, u b * ‖η b‖ * (x * Real.sqrt (∑ b', w b' * ‖η b'‖ ^ 2) + 1)) :
    |ballExpectation (cutoffFactor ρ p) Φ f| ≤ B * Wu * (m * (1 + Ww) / 2 + (1 + m) / 2) := by
  have hx0 : 0 < x := by linarith
  set U := ∑ b, u b with hU
  have hU0 : 0 ≤ U := Finset.sum_nonneg fun b _ => hu b
  have hW0 : 0 ≤ Ww := (Finset.sum_nonneg fun b _ => hw b).trans hWw
  set a : ι → ℝ := fun b => B * u b * (x + 1) / 2 with ha
  have ha0 : ∀ b, 0 ≤ a b := fun b => by
    have := hu b
    simp only [ha]
    positivity
  have hq := boundedContinuous_weightedSq (ρ := ρ) hρ w
  have hqa := boundedContinuous_weightedSq (ρ := ρ) hρ a
  set c₁ := B * U * x / 2 with hc₁
  set c₀ := B * U / 2 with hc₀
  have hg1 : IsBoundedContinuousOn ι ρ (fun η => c₁ * ∑ b, w b * ‖η b‖ ^ 2) :=
    (IsBoundedContinuousOn.const _).mul hq
  have hg2 : IsBoundedContinuousOn ι ρ
      (fun η => (∑ b, a b * ‖η b‖ ^ 2) + c₁ * ∑ b, w b * ‖η b‖ ^ 2) := hqa.add hg1
  have hg : IsBoundedContinuousOn ι ρ
      (fun η => ((∑ b, a b * ‖η b‖ ^ 2) + c₁ * ∑ b, w b * ‖η b‖ ^ 2) + c₀) :=
    hg2.add (IsBoundedContinuousOn.const _)
  have hpt : ∀ η ∈ openPolyball ι ρ,
      |f η| ≤ ((∑ b, a b * ‖η b‖ ^ 2) + c₁ * ∑ b, w b * ‖η b‖ ^ 2) + c₀ := by
    intro η hη
    refine (h η hη).trans ?_
    set S := ∑ b', w b' * ‖η b'‖ ^ 2 with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun b _ => mul_nonneg (hw b) (by positivity)
    have hrt := Real.sq_sqrt hS0
    have hterm : ∀ b, u b * ‖η b‖ * (x * Real.sqrt S + 1) ≤
        u b * (x + 1) / 2 * ‖η b‖ ^ 2 + u b * x / 2 * S + u b / 2 := by
      intro b
      have h1 : ‖η b‖ * Real.sqrt S ≤ (‖η b‖ ^ 2 + S) / 2 := by
        nlinarith [sq_nonneg (‖η b‖ - Real.sqrt S)]
      have h2 : ‖η b‖ ≤ (‖η b‖ ^ 2 + 1) / 2 := by
        nlinarith [sq_nonneg (‖η b‖ - 1)]
      have h3 : u b * x * (‖η b‖ * Real.sqrt S) ≤ u b * x * ((‖η b‖ ^ 2 + S) / 2) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg (hu b) hx0.le)
      have h4 : u b * ‖η b‖ ≤ u b * ((‖η b‖ ^ 2 + 1) / 2) := mul_le_mul_of_nonneg_left h2 (hu b)
      nlinarith
    have hsum : ∑ b, u b * ‖η b‖ * (x * Real.sqrt S + 1) ≤
        ∑ b, (u b * (x + 1) / 2 * ‖η b‖ ^ 2 + u b * x / 2 * S + u b / 2) :=
      Finset.sum_le_sum fun b _ => hterm b
    have e : B * ∑ b, (u b * (x + 1) / 2 * ‖η b‖ ^ 2 + u b * x / 2 * S + u b / 2) =
        ((∑ b, a b * ‖η b‖ ^ 2) + c₁ * S) + c₀ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div,
        ← Finset.sum_div, ← Finset.sum_mul, mul_add, mul_add, Finset.mul_sum]
      simp only [hc₁, hc₀, ha, hU]
      congr 1
      · congr 1
        · exact Finset.sum_congr rfl fun b _ => by ring
        · ring
      · ring
    calc _ ≤ B * ∑ b, (u b * (x + 1) / 2 * ‖η b‖ ^ 2 + u b * x / 2 * S + u b / 2) :=
          mul_le_mul_of_nonneg_left hsum hB
      _ = _ := e
  have h1 := abs_ballExpectation_le F hf hg hpt
  have hconst : ballExpectation (cutoffFactor ρ p) Φ (fun _ => c₀) = c₀ := by
    have := F.map_smul c₀ (fun _ => 1)
    rw [F.map_one] at this
    simpa using this
  rw [F.map_add _ _ hg2 (IsBoundedContinuousOn.const _), F.map_add _ _ hqa hg1, F.map_smul, hconst] at h1
  have h2 := expectation_weightedSq_le hρ F hm w hw
  have h3 := expectation_weightedSq_le hρ F hm a ha0
  have hmx : m / x ≤ m := div_le_self hm0 hx
  have hsa : ∑ b, a b = B * U * (x + 1) / 2 := by
    simp only [ha, hU]
    rw [← Finset.sum_div, ← Finset.sum_mul, ← Finset.mul_sum]
  have hmx0 : 0 ≤ m / x := by positivity
  have hBU : 0 ≤ B * U := mul_nonneg hB hU0
  have h4 : c₁ * ballExpectation (cutoffFactor ρ p) Φ (fun η => ∑ b, w b * ‖η b‖ ^ 2) ≤
      c₁ * (Ww * (m / x)) := by
    refine mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_right hWw hmx0
  have e1 : c₁ * (Ww * (m / x)) = B * U * (Ww * m) / 2 := by
    simp only [hc₁]
    field_simp
  have e2 : (∑ b, a b) * (m / x) ≤ B * U * m := by
    rw [hsa]
    have : B * U * (x + 1) / 2 * (m / x) = B * U * (m + m / x) / 2 := by
      field_simp
    rw [this]
    have : B * U * (m + m / x) / 2 ≤ B * U * (m + m) / 2 := by
      have := mul_le_mul_of_nonneg_left (add_le_add_right hmx m) hBU
      linarith
    linarith
  have hfin : B * U * (m * (1 + Ww) / 2 + (1 + m) / 2) ≤ B * Wu * (m * (1 + Ww) / 2 + (1 + m) / 2) := by
    have h6 : B * U ≤ B * Wu := mul_le_mul_of_nonneg_left hWu hB
    exact mul_le_mul_of_nonneg_right h6 (by positivity)
  linarith
end Expectations
section Parameters
private def ObservableSizesAt (Cq : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ)
    (n : ℕ) (w : Fin n → ℝ) (M : Fin n → LawOnBondVariables ι), IsConvexWeights w →
    (∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio
      T.L t T.n₀ (frameRadius x) d) →
    ∀ M₀ : LawOnBondVariables ι,
      M₀.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t
        T.n₀ (frameRadius x) d →
      ObservableSizes T.a T.chainParams.ρA T.ballRadius T.chainParams.lam x T.κ T.Cs T.decayRate T.η₃ T.L t
        T.n₀ (frameRadius x) T.σ T.p (Cq (momentParameters T))
        (convexCombinationExponent T.chainParams.lam x w M) M₀
private def MomentBoundsAt (Cq : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ) (Cr : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℕ → ℕ → ℝ)
    (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ)
    (n : ℕ) (w : Fin n → ℝ) (M : Fin n → LawOnBondVariables ι), IsConvexWeights w →
    (∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio
      T.L t T.n₀ (frameRadius x) d) →
    LawMomentBounds T.ballRadius x T.κ T.Cs T.p (Cq (momentParameters T)) (Cr (momentParameters T)) d
      (convexCombinationExponent T.chainParams.lam x w M)
private def ConvexityAt (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ)
    (n : ℕ) (w : Fin n → ℝ) (M : Fin n → LawOnBondVariables ι), IsConvexWeights w →
    (∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio
      T.L t T.n₀ (frameRadius x) d) →
    HasUniformlyConvexLaw T.ballRadius T.chainParams.lam x T.κ T.Ct d
      (convexCombinationExponent T.chainParams.lam x w M)
private def ExponentBoundsAt (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → ∀ (F : BlockFrame) (V : F.GaugeField F.top) (s : ℝ),
    IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 ≤ s → s ≤ 1 →
    InterpolatedExponentBounds s T.a T.chainParams.ρA T.ballRadius x T.κ T.Cs (frameRadius x) V
private theorem eventuallyInParameters_and {P R : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → Prop} (hP : EventuallyInParameters P)
    (hR : EventuallyInParameters R) :
    EventuallyInParameters fun T => P T ∧ R T := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.EventuallyInParameters.and <;> assumption
private structure ChosenParams (U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (x : ℝ) : Prop where
  κ_pos : 0 < U.κ
  σ_pos : 0 < U.σ
  isCutoff : IsCutoff (U.σ / 64) U.p
  lam_pos : 0 < U.chainParams.lam
  one_le_x : 1 ≤ x
  coupling_le_x : U.coupling ≤ x
  one_le_Cs : 1 ≤ U.Cs
private theorem ChosenParams.ballRadius_pos {U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} (D : ChosenParams U x) :
    0 < U.ballRadius := by
  have := D.σ_pos
  show 0 < U.σ / 64
  positivity
private structure MixtureFacts (U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (x m : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : BondField ι → ℝ) : Prop where
  extension : ∃ Ψ : BondField ι → ℝ, Continuous Ψ ∧ ∀ η ∈ openPolyball ι U.ballRadius, Ψ η = Φ η
  form : IsPositiveUnitalForm U.ballRadius U.p Φ
  secondMoment : ∀ b, ballExpectation (cutoffFactor U.ballRadius U.p) Φ (fun η => ‖η b‖ ^ 2) ≤ m / x
private theorem mixtureFacts_of (hMeans : CutoffExpectationIsPositiveForm) {Cq : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ}
    {Cr : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℕ → ℕ → ℝ} {U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} (D : ChosenParams U x)
    (hC : ConvexityAt U) (hM : MomentBoundsAt Cq Cr U) (t : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (d : ι → ι → ℝ) (n : ℕ)
    (w : Fin n → ℝ) (M : Fin n → LawOnBondVariables ι) (hw : IsConvexWeights w)
    (hadm : ∀ l, (M l).IsAdmissible U.a U.chainParams.ρA U.chainParams.lam x U.σ U.decayRate U.E
      U.energyRatio U.L t U.n₀ (frameRadius x) d) :
    MixtureFacts U x |Cq (momentParameters U) 1| (convexCombinationExponent U.chainParams.lam x w M) := by
  obtain ⟨Ψ, K, ag, cv, -, -⟩ := hC t x D.coupling_le_x ι d n w M hw hadm
  have hcont : Continuous Ψ := cv.smooth.continuous
  have cut : IsCutoff U.ballRadius U.p := D.isCutoff
  have F₀ := hMeans ι U.ballRadius U.p Ψ D.ballRadius_pos cut hcont
  refine ⟨⟨Ψ, hcont, ag⟩, positiveForm_of_eqOn F₀ ag, fun b => ?_⟩
  have h := (hM t x D.coupling_le_x ι d n w M hw hadm).moments 1 b
  simp only [mul_one, pow_one] at h
  refine h.trans ?_
  rw [div_eq_mul_inv]
  have hx0 : 0 ≤ x := by
    have := D.one_le_x
    linarith
  exact mul_le_mul_of_nonneg_right (le_abs_self _) (inv_nonneg.2 hx0)
private theorem isConvexWeights_pair {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : IsConvexWeights ![v, 1 - v] := by
  refine ⟨fun l => ?_, by simp [Fin.sum_univ_two]⟩
  fin_cases l
  · simpa using h0
  · simpa using h1
abbrev _root_.YangMills.SharedProofs.p68332 := @isConvexWeights_pair
private abbrev torusLaw {ι : Type} [Fintype ι] [DecidableEq ι] {F : BlockFrame} (V : F.GaugeField F.top)
    (j : ι → ↥(chordBonds (finiteCells F))) (Λ : Finset ι) (Ψ : StepVariable (finiteCells F) → ℝ) :
    LawOnBondVariables ι := ⟨F, V, j, Λ, Ψ⟩
section SingleTorus
variable {F : BlockFrame}
private theorem extendByZero_univ (η : StepVariable (finiteCells F)) : _root_.YangMills.Construction.Interpolation.extendByZero id Finset.univ η = η := by apply _root_.YangMills.Construction.InterpolatedBirths.extendByZero_id <;> assumption
private theorem freezingHomotopy_eq_mixture (V : F.GaugeField F.top) (lam x v : ℝ)
    (Λ : Finset ↥(chordBonds (finiteCells F))) (Ψ : StepVariable (finiteCells F) → ℝ) :
    freezingHomotopy lam x Λ Ψ v = convexCombinationExponent lam x ![v, 1 - v]
      ![torusLaw V id Finset.univ Ψ, torusLaw V id Λ Ψ] := by
  funext ζ
  simp [-Finset.univ_eq_attach, convexCombinationExponent, LawOnBondVariables.exponent, Fin.sum_univ_two,
    freezingHomotopy, frozenExponent, extendByZero_univ]
private theorem freezeOutside_eq_restrict (Λ : Finset ↥(chordBonds (finiteCells F)))
    (η : StepVariable (finiteCells F)) :
    freezeOutside Λ η = restrictToBonds Λ η := by
  funext b
  simp only [freezeOutside, _root_.YangMills.Construction.Interpolation.extendByZero, restrictToBonds, id]
  rw [Finset.sum_ite_eq' Λ b]
private theorem cellSupDist_self (Y : F.Cell) : cellSupDist Y Y = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
private theorem cellQuadratic_eq_sum (lam x : ℝ) (Y : F.Cell) (η : StepVariable (finiteCells F)) :
    cellQuadratic lam x Y η =
      ∑ b : ↥(chordBonds (finiteCells F)),
        (if enclosingCell b.1.1 = Y then x * lam / 2 else 0) * ‖η b‖ ^ 2 := by
  unfold cellQuadratic
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : enclosingCell b.1.1 = Y <;> simp [h]
private theorem boundedContinuous_cellQuadratic {ρ : ℝ} (hρ : 0 < ρ) (lam x : ℝ) (Y : F.Cell) :
    IsBoundedContinuousOn _ ρ (cellQuadratic lam x Y) := by
  have e : cellQuadratic lam x Y = fun η => ∑ b : ↥(chordBonds (finiteCells F)),
      (if enclosingCell b.1.1 = Y then x * lam / 2 else 0) * ‖η b‖ ^ 2 :=
    funext (cellQuadratic_eq_sum lam x Y)
  rw [e]
  exact boundedContinuous_weightedSq hρ _
private theorem contDiff_cellQuadratic (lam x : ℝ) (Y : F.Cell) : ContDiff ℝ 1 (cellQuadratic lam x Y) := by
  have e : cellQuadratic lam x Y = fun η => ∑ b : ↥(chordBonds (finiteCells F)),
      (if enclosingCell b.1.1 = Y then x * lam / 2 else 0) * ‖η b‖ ^ 2 :=
    funext (cellQuadratic_eq_sum lam x Y)
  rw [e]
  refine ContDiff.sum fun b _ => contDiff_const.mul ?_
  exact (contDiff_norm_sq_apply b).of_le (by norm_num)
private theorem cellQuadratic_freezeOutside (lam x : ℝ) (Y : F.Cell) (q : ℕ)
    (η : StepVariable (finiteCells F)) :
    cellQuadratic lam x Y (freezeOutside (bondsNearCell Y q) η) = cellQuadratic lam x Y η := by
  rw [freezeOutside_eq_restrict]
  unfold cellQuadratic
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : enclosingCell b.1.1 = Y
  · have hb : b ∈ bondsNearCell Y q := by
      simp [bondsNearCell, h, cellSupDist_self]
    simp [h, restrictToBonds, hb]
  · simp [h]
end SingleTorus
section Freezing
variable {ι P : Type} [Fintype ι] [DecidableEq ι] [Fintype P]
private theorem abs_sub_restrict_le {ρ r c x q : ℝ} {pos : ι → P} {D : P → P → ℝ} {z : P}
    {θ : BondField ι → ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hθ : IsLocalTermAt ρ r c x pos D z θ) (Λ : Finset ι) (hq0 : 0 ≤ q)
    (hoff : ∀ b, b ∉ Λ → q ≤ 2 * D (pos b) z)
    {η : BondField ι} (hη : η ∈ openPolyball ι ρ) :
    |θ η - θ (restrictToBonds Λ η)| ≤ (c * Real.exp (-(4 * r * q))) *
      ∑ b, Real.exp (-(2 ^ 4 * r * D (pos b) z)) * ‖η b‖ *
        (x * Real.sqrt (∑ b', Real.exp (-(2 ^ 5 * r * D (pos b') z)) * ‖η b'‖ ^ 2) + 1) := by
  have hζ := restrictToBonds_mem_openPolyball hρ Λ hη
  set R := Real.sqrt (∑ b', Real.exp (-(2 ^ 5 * r * D (pos b') z)) * ‖η b'‖ ^ 2) with hR
  have h1 := abs_sub_le_sum_bondGradNorm hρ (contDiffOn_one_of_two hθ.smooth) hη hζ
    (fun b => c * (x * R + 1) * Real.exp (-(2 ^ 5 * r * D (pos b) z))) (fun s hs b => by
      have hpt := (convex_openPolyball (ι := ι) hρ).add_smul_sub_mem hζ hη hs
      refine (hθ.slope _ hpt b).trans ?_
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hc) (Real.exp_pos _).le
      have hmono : weightedSqNormNear r pos D z (restrictToBonds Λ η + s • (η - restrictToBonds Λ η)) ≤
          weightedSqNormNear r pos D z η := by
        refine weightedSqNormNear_mono z fun b' => ?_
        by_cases hb : b' ∈ Λ
        · simp [restrictToBonds, hb]
        · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, restrictToBonds, hb, if_false, zero_add,
            sub_zero, norm_smul, Real.norm_eq_abs]
          rw [abs_of_nonneg hs.1]
          exact mul_le_of_le_one_left (norm_nonneg _) hs.2
      have := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) hx
      simpa [hR, weightedSqNormNear] using this)
  refine h1.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases hb : b ∈ Λ
  · have : η b - restrictToBonds Λ η b = 0 := by
      simp [restrictToBonds, hb]
    rw [this, norm_zero, mul_zero]
    have : 0 ≤ x * R + 1 := by positivity
    positivity
  · have e1 : η b - restrictToBonds Λ η b = η b := by
      simp [restrictToBonds, hb]
    rw [e1]
    have hq := hoff b hb
    have hexp : Real.exp (-(2 ^ 5 * r * D (pos b) z)) ≤
        Real.exp (-(4 * r * q)) * Real.exp (-(2 ^ 4 * r * D (pos b) z)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h2 := mul_le_mul_of_nonneg_left hq hr
      have h3 : 0 ≤ r * D (pos b) z := mul_nonneg hr (by linarith)
      nlinarith
    calc c * (x * R + 1) * Real.exp (-(2 ^ 5 * r * D (pos b) z)) * ‖η b‖
        ≤ c * (x * R + 1) * (Real.exp (-(4 * r * q)) * Real.exp (-(2 ^ 4 * r * D (pos b) z))) * ‖η b‖ := by
          gcongr
      _ = _ := by ring
end Freezing
section CellParts
variable {F : BlockFrame}
private theorem interpolatedBlockExponent_facts {U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x s : ℝ} (D : ChosenParams U x)
    (hP : StepLawLocalDecomposition U) (hB : ExponentBoundsAt U) {t : ℕ} [Fintype F.Cell]
    {V : F.GaugeField F.top} (Y : F.Cell) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hF : IsCubicTopTorus U.L t U.n₀ F) (hV : IsSmallCurvature (5 / 4 * U.σ) V) :
    IsLocalTermAt U.ballRadius U.κ U.Cs x bondCell realCellDist Y
        (interpolatedBlockExponent s U.a U.chainParams.ρA x (frameRadius x) Y V) ∧
      ∀ η ∈ openPolyball _ U.ballRadius,
        |interpolatedBlockExponent s U.a U.chainParams.ρA x (frameRadius x) Y V η| ≤
        U.Cs * (x * localSqNorm U.κ Y η + 1) := by
  constructor
  · obtain ⟨Ψ, -, -, -, terms⟩ := hP t x s (StepLaw.ofWeight 1) F V D.coupling_le_x hs hs1
      ⟨zero_le_one, le_rfl⟩ hF hV
    have ht := terms Y
    have e : stepLawCellPart (StepLaw.ofWeight 1) s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) V Y =
        interpolatedBlockExponent s U.a U.chainParams.ρA x (frameRadius x) Y V := by
      funext η
      simp [stepLawCellPart]
    rw [e] at ht
    have e2 : U.Cs * StepLaw.amplitude (StepLaw.ofWeight 1) U.energyRatio = U.Cs := by
      simp [StepLaw.amplitude]
    rwa [e2] at ht
  · intro η hη
    have h := (hB t x D.coupling_le_x F V s hF hV hs hs1).deriv_top Y η 0 Fin.elim0 Fin.elim0 hη
      (by norm_num) (fun l => l.elim0)
    have e : ∀ (G : F.GaugeField F.top → ℝ) (c : Fin 0 → F.Site F.top × Fin 4)
        (X : Fin 0 → imaginaryQuaternions), bondDeriv G V c X = G V := by
      intro G c X
      have hV' : leftTranslate (ColdStepAtMirrorFrames.bondSpread c X 0) V = V := by
        funext y i
        have h0 : expUnit (0 : imaginaryQuaternions) = 1 := by
          apply Subtype.ext
          simp [expUnit]
        simp [leftTranslate, ColdStepAtMirrorFrames.bondSpread, h0]
      unfold bondDeriv
      rw [iteratedFDeriv_zero_apply]
      exact congrArg G hV'
    rw [e] at h
    refine h.trans (le_of_eq ?_)
    simp [bondSpan]
end CellParts
section OneTorus
variable {F : BlockFrame}
private theorem boundedContinuous_localSqNorm {ρ κ : ℝ} (hρ : 0 < ρ) (Y : F.Cell) :
    IsBoundedContinuousOn _ ρ (localSqNorm κ Y) := by
  have e : localSqNorm κ Y = fun η => ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(2 ^ 6 * κ * cellSupDist (enclosingCell b.1.1) Y)) * ‖η b‖ ^ 2 := rfl
  rw [e]
  exact boundedContinuous_weightedSq hρ _
private theorem remainder_regular {U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x s : ℝ} (D : ChosenParams U x)
    (hP : StepLawLocalDecomposition U) (hB : ExponentBoundsAt U) {t : ℕ} [Fintype F.Cell]
    {V : F.GaugeField F.top} (Y : F.Cell) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hF : IsCubicTopTorus U.L t U.n₀ F) (hV : IsSmallCurvature (5 / 4 * U.σ) V) :
    ContDiffOn ℝ 1 (cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V)
        (openPolyball _ U.ballRadius) ∧
      IsBoundedContinuousOn _ U.ballRadius
        (cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V) := by
  obtain ⟨ht, hv⟩ := interpolatedBlockExponent_facts D hP hB Y hs hs1 hF hV
  have hcd : ContDiffOn ℝ 1
      (cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V)
      (openPolyball _ U.ballRadius) :=
    (contDiffOn_one_of_two ht.smooth).sub (contDiff_cellQuadratic U.chainParams.lam x Y).contDiffOn
  refine ⟨hcd, ?_⟩
  have hψ : IsBoundedContinuousOn _ U.ballRadius
      (interpolatedBlockExponent s U.a U.chainParams.ρA x (frameRadius x) Y V) := by
    obtain ⟨-, M, hM⟩ := boundedContinuous_localSqNorm (κ := U.κ) D.ballRadius_pos Y
    have hc0 : 0 ≤ U.Cs := by
      have := D.one_le_Cs
      linarith
    have hx0 : 0 ≤ x := by
      have := D.one_le_x
      linarith
    refine ⟨(contDiffOn_one_of_two ht.smooth).continuousOn, U.Cs * (x * M + 1), fun η hη => ?_⟩
    refine (hv η hη).trans (mul_le_mul_of_nonneg_left ?_ hc0)
    have := mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hM η hη)) hx0
    linarith
  exact hψ.sub (boundedContinuous_cellQuadratic D.ballRadius_pos U.chainParams.lam x Y)
private theorem boundedContinuous_freezeOutside {ρ : ℝ} (hρ : 0 < ρ)
    (Λ : Finset ↥(chordBonds (finiteCells F)))
    {A : StepVariable (finiteCells F) → ℝ} (hA : IsBoundedContinuousOn _ ρ A) :
    IsBoundedContinuousOn _ ρ (fun η => A (freezeOutside Λ η)) := by
  obtain ⟨hc, M, hM⟩ := hA
  have e : (fun η => A (freezeOutside Λ η)) = fun ζ => A (restrictToBondsCLM Λ ζ) := by
    funext ζ
    rw [freezeOutside_eq_restrict, restrictToBondsCLM_apply]
  rw [e]
  refine ⟨hc.comp (restrictToBondsCLM Λ).continuous.continuousOn fun η hη => ?_, M,
    fun η hη => hM _ ?_⟩
  · show restrictToBondsCLM Λ η ∈ openPolyball _ ρ
    rw [restrictToBondsCLM_apply]
    exact restrictToBonds_mem_openPolyball hρ Λ hη
  · rw [restrictToBondsCLM_apply]
    exact restrictToBonds_mem_openPolyball hρ Λ hη
private theorem along_freezingHomotopy (hMeans : CutoffExpectationIsPositiveForm)
    {Co Cm : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ}
    {Cr : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℕ → ℕ → ℝ} {U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} (D : ChosenParams U x)
    (hS : ObservableSizesAt Co U)
    (hM : MomentBoundsAt Cm Cr U) (hC : ConvexityAt U) {t : ℕ} {s τ : ℝ} {V : F.GaugeField F.top}
    (Y : F.Cell)
    (Λ : Finset ↥(chordBonds (finiteCells F))) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hF : IsCubicTopTorus U.L t U.n₀ F) (hV : IsSmallCurvature (5 / 4 * U.σ) V) {v : ℝ} (h0 : 0 ≤ v)
    (h1 : v ≤ 1) :
    MixtureFacts U x |Cm (momentParameters U) 1|
        (freezingHomotopy U.chainParams.lam x Λ
          (weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V) v) ∧
      HasLocalSize U.ballRadius (cutoffFactor U.ballRadius U.p)
        (freezingHomotopy U.chainParams.lam x Λ
          (weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V) v)
        (Co (momentParameters U)) x U.κ U.Cs (bondDistToCell Y)
        (cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V) ∧
      HasLocalSize U.ballRadius (cutoffFactor U.ballRadius U.p)
        (freezingHomotopy U.chainParams.lam x Λ
          (weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V) v)
        (Co (momentParameters U)) x U.κ U.Cs (bondDistToCell Y)
        (fun η => cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V
          (freezeOutside Λ η)) := by
  set Ψ := weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V with hΨ
  set d : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ :=
    fun b b' => (cellSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℝ) with hd
  have adm : ∀ N : Finset ↥(chordBonds (finiteCells F)),
      (torusLaw V id N Ψ).IsAdmissible U.a U.chainParams.ρA U.chainParams.lam x U.σ U.decayRate U.E
        U.energyRatio U.L t U.n₀ (frameRadius x) d := fun N =>
    ⟨hF, hV, IsIntermediateLaw.ofWeight s τ hs hs1 hτ hτ1, Function.injective_id, fun _ _ => rfl⟩
  have hadm : ∀ l, (![torusLaw V id Finset.univ Ψ, torusLaw V id Λ Ψ] l).IsAdmissible U.a
      U.chainParams.ρA U.chainParams.lam x U.σ U.decayRate U.E U.energyRatio U.L t U.n₀ (frameRadius x) d :=
    Fin.forall_fin_two.2 ⟨adm _, adm _⟩
  rw [freezingHomotopy_eq_mixture V]
  refine ⟨mixtureFacts_of hMeans D hC hM t d 2 _ _ (isConvexWeights_pair h0 h1) hadm, ?_, ?_⟩
  · have h := (hS t x D.coupling_le_x _ d 2 _ _ (isConvexWeights_pair h0 h1) hadm
      (torusLaw V id Finset.univ Ψ) (adm _)).exponent_sub_quadratic s Y hs hs1
    have e : (fun ζ => interpolatedBlockExponent s U.a U.chainParams.ρA x (frameRadius x) Y V
        (_root_.YangMills.Construction.Interpolation.extendByZero id Finset.univ ζ) -
          cellQuadratic U.chainParams.lam x Y (_root_.YangMills.Construction.Interpolation.extendByZero id Finset.univ ζ)) =
        cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V := by
      funext ζ
      rw [extendByZero_univ]
      rfl
    exact e ▸ h
  · exact (hS t x D.coupling_le_x _ d 2 _ _ (isConvexWeights_pair h0 h1) hadm (torusLaw V id Λ Ψ)
      (adm _)).exponent_sub_quadratic s Y hs hs1
private theorem comparisonBoundsOnTorus_of (hlaw : normalizedBallLawIsProbabilityStatement)
    (hMeans : CutoffExpectationIsPositiveForm)
    {Co Cm : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ} {Cr : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℕ → ℕ → ℝ} {U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ}
    (D : ChosenParams U x) (hS : ObservableSizesAt Co U) (hM : MomentBoundsAt Cm Cr U) (hC : ConvexityAt U)
    (hP : StepLawLocalDecomposition U) (hB : ExponentBoundsAt U) {t : ℕ} {s τ : ℝ} [Fintype F.Cell]
    {V : F.GaugeField F.top} (Y : F.Cell) (q : ℕ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hF : IsCubicTopTorus U.L t U.n₀ F) (hV : IsSmallCurvature (5 / 4 * U.σ) V) {W : ℝ}
    (hWs : ∀ z : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(U.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ W) {α : ℝ}
    (hα1 : |Co (momentParameters U) 2| * U.Cs ≤ α)
    (hα2 : U.Cs * W * (|Cm (momentParameters U) 1| * (1 + W) / 2 + (1 + |Cm (momentParameters U) 1|) / 2)
      ≤ α) :
    ComparisonHypothesesOnTorus U.ballRadius U.chainParams.lam x U.κ α U.p q Y
      (weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V)
      (cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V) := by
  have hρ := D.ballRadius_pos
  have hcut : IsCutoff U.ballRadius U.p := D.isCutoff
  have hc0 : 0 ≤ U.Cs := by
    have := D.one_le_Cs
    linarith
  have hx0 : 0 ≤ x := by
    have := D.one_le_x
    linarith
  obtain ⟨hcd, hnice⟩ := remainder_regular D hP hB Y hs hs1 hF hV
  obtain ⟨hterm, -⟩ := interpolatedBlockExponent_facts D hP hB Y hs hs1 hF hV
  have hfn := boundedContinuous_freezeOutside hρ (bondsNearCell Y q) hnice
  have seg := fun v (h0 : 0 ≤ v) (h1 : v ≤ 1) =>
    along_freezingHomotopy hMeans D hS hM hC (t := t) (V := V) Y (bondsNearCell Y q) hs hs1 hτ hτ1 hF hV
      h0 h1
  refine ⟨integrable_mul_radialWeightProd hlaw hρ hcut hnice,
    integrable_mul_radialWeightProd hlaw hρ hcut hfn,
    fun v h0 h1 => ?_, fun v h0 h1 => ?_, fun v h0 h1 => ?_⟩
  · obtain ⟨fa, h2, -⟩ := seg v h0 h1
    obtain ⟨Ψ', c', a'⟩ := fa.extension
    exact hasGradientBound_of_hasLocalSize hlaw hρ hcut c' a' hnice hc0 hα1 h2
  · obtain ⟨fa, -, h3⟩ := seg v h0 h1
    obtain ⟨Ψ', c', a'⟩ := fa.extension
    exact hasGradientBound_of_hasLocalSize hlaw hρ hcut c' a' hfn hc0 hα1 h3
  · obtain ⟨fa, -, -⟩ := seg v h0 h1
    set A := cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V with hA
    set E := Real.exp (-(4 * U.κ * q)) with hE
    have hκ := D.κ_pos
    have hdist : ∀ b : ↥(chordBonds (finiteCells F)), 0 ≤ realCellDist (bondCell b) Y := fun b => by
      simp only [realCellDist]
      positivity
    have hw : ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(2 ^ 5 * U.κ * realCellDist (bondCell b) Y)) ≤ W := by
      refine le_trans (Finset.sum_le_sum fun b _ => ?_) (hWs Y)
      apply Real.exp_le_exp.mpr
      have := mul_nonneg hκ.le (hdist b)
      simp only [realCellDist, bondCell] at this ⊢
      linarith
    have hu : ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(2 ^ 4 * U.κ * realCellDist (bondCell b) Y)) ≤ W := by
      refine le_trans (Finset.sum_le_sum fun b _ => ?_) (hWs Y)
      apply Real.exp_le_exp.mpr
      have := mul_nonneg hκ.le (hdist b)
      simp only [realCellDist, bondCell] at this ⊢
      linarith
    have hpt : ∀ η ∈ openPolyball _ U.ballRadius, |A η - A (freezeOutside (bondsNearCell Y q) η)| ≤
        (U.Cs * E) * ∑ b, Real.exp (-(2 ^ 4 * U.κ * realCellDist (bondCell b) Y)) * ‖η b‖ *
          (x * Real.sqrt (∑ b', Real.exp (-(2 ^ 5 * U.κ * realCellDist (bondCell b') Y)) * ‖η b'‖ ^ 2)
            + 1) := by
      intro η hη
      have h := abs_sub_restrict_le (q := (q : ℝ)) hρ hκ.le hc0 hx0 hterm (bondsNearCell Y q)
        (Nat.cast_nonneg q)
        (fun b hb => by
          have h1 : ¬ 2 * cellSupDist (enclosingCell b.1.1) Y ≤ q := fun h =>
            hb (by simp [bondsNearCell, h])
          have h2 : (q : ℝ) < 2 * (cellSupDist (enclosingCell b.1.1) Y : ℝ) := by
            exact_mod_cast not_le.1 h1
          exact h2.le) hη
      have e : A η - A (freezeOutside (bondsNearCell Y q) η) =
          interpolatedBlockExponent s U.a U.chainParams.ρA x (frameRadius x) Y V η -
            interpolatedBlockExponent s U.a U.chainParams.ρA x (frameRadius x) Y V
              (restrictToBonds (bondsNearCell Y q) η) := by
        simp only [hA, cellExponentRemainder, cellQuadratic_freezeOutside]
        rw [freezeOutside_eq_restrict]
        ring
      rw [e]
      exact h
    have hmain := abs_expectation_le_of_slopes hρ fa.form D.one_le_x (abs_nonneg _) fa.secondMoment
      (fun b => Real.exp (-(2 ^ 5 * U.κ * realCellDist (bondCell b) Y)))
      (fun b => Real.exp (-(2 ^ 4 * U.κ * realCellDist (bondCell b) Y)))
      (fun b => (Real.exp_pos _).le) (fun b => (Real.exp_pos _).le) hw hu (hnice.sub hfn)
      (mul_nonneg hc0 (Real.exp_pos _).le) hpt
    refine hmain.trans ?_
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    calc _ = (U.Cs * W * (|Cm (momentParameters U) 1| * (1 + W) / 2 +
            (1 + |Cm (momentParameters U) 1|) / 2)) * E := by
          ring
      _ ≤ α * E := mul_le_mul_of_nonneg_right hα2 hE0
private theorem abs_expectation_remainder_le (hMeans : CutoffExpectationIsPositiveForm)
    {Co Cm : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ} {Cr : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℕ → ℕ → ℝ} {U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ}
    (D : ChosenParams U x) (hS : ObservableSizesAt Co U) (hM : MomentBoundsAt Cm Cr U) (hC : ConvexityAt U)
    (hP : StepLawLocalDecomposition U) (hB : ExponentBoundsAt U) {t : ℕ} {s τ : ℝ} [Fintype F.Cell]
    {V : F.GaugeField F.top} (Y : F.Cell) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hF : IsCubicTopTorus U.L t U.n₀ F) (hV : IsSmallCurvature (5 / 4 * U.σ) V) {W : ℝ}
    (hWs : ∀ z : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(U.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ W) {N : ℕ}
    (hN : (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = Y).card ≤ N) :
    |ballExpectation (cutoffFactor U.ballRadius U.p)
        (weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V)
        (cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V)| ≤
      U.Cs * ((W + U.chainParams.lam / 2 * N) * |Cm (momentParameters U) 1| + 1) := by
  have hρ := D.ballRadius_pos
  have hκ := D.κ_pos
  have hlam := D.lam_pos
  have hc1 := D.one_le_Cs
  have hc0 : 0 ≤ U.Cs := by linarith
  have hx1 := D.one_le_x
  have hx0 : 0 < x := by linarith
  obtain ⟨-, hnice⟩ := remainder_regular D hP hB Y hs hs1 hF hV
  obtain ⟨-, hval⟩ := interpolatedBlockExponent_facts D hP hB Y hs hs1 hF hV
  obtain ⟨fa, -, -⟩ := along_freezingHomotopy hMeans D hS hM hC (t := t) (V := V) Y Finset.univ hs hs1 hτ
    hτ1 hF hV (zero_le_one) le_rfl
  have e1 : freezingHomotopy U.chainParams.lam x Finset.univ
      (weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V) 1 =
      weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V := by
    funext η
    simp [freezingHomotopy]
  rw [e1] at fa
  set w : ↥(chordBonds (finiteCells F)) → ℝ := fun b =>
    Real.exp (-(2 ^ 6 * U.κ * cellSupDist (enclosingCell b.1.1) Y)) +
      (if enclosingCell b.1.1 = Y then U.chainParams.lam / 2 else 0) with hw
  have hw0 : ∀ b, 0 ≤ w b := fun b => by
    simp only [hw]
    have h1 := Real.exp_pos (-(2 ^ 6 * U.κ * cellSupDist (enclosingCell b.1.1) Y))
    split_ifs <;> positivity
  have hsum : ∑ b, w b ≤ W + U.chainParams.lam / 2 * N := by
    simp only [hw]
    rw [Finset.sum_add_distrib]
    refine add_le_add (le_trans (Finset.sum_le_sum fun b _ => ?_) (hWs Y)) ?_
    · apply Real.exp_le_exp.mpr
      have : 0 ≤ U.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ) := by positivity
      linarith
    · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have : ((Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) =>
          enclosingCell b.1.1 = Y).card : ℝ) ≤ N := by
        exact_mod_cast hN
      nlinarith
  refine abs_expectation_le_of_quadratic hρ fa.form hx0 (abs_nonneg _) fa.secondMoment w hw0 hsum hnice hc0
    fun η hη => ?_
  have h1 := hval η hη
  have hq : cellQuadratic U.chainParams.lam x Y η =
      x * ∑ b, (if enclosingCell b.1.1 = Y then U.chainParams.lam / 2 else 0) * ‖η b‖ ^ 2 := by
    rw [cellQuadratic_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : enclosingCell b.1.1 = Y <;> simp [h]
    ring
  have hq0 : 0 ≤ ∑ b : ↥(chordBonds (finiteCells F)),
      (if enclosingCell b.1.1 = Y then U.chainParams.lam / 2 else 0) * ‖η b‖ ^ 2 := by
    refine Finset.sum_nonneg fun b _ => mul_nonneg ?_ (by positivity)
    split_ifs <;> positivity
  have hsplit : ∑ b, w b * ‖η b‖ ^ 2 = localSqNorm U.κ Y η +
      ∑ b : ↥(chordBonds (finiteCells F)),
        (if enclosingCell b.1.1 = Y then U.chainParams.lam / 2 else 0) * ‖η b‖ ^ 2 := by
    simp only [hw, add_mul]
    rw [Finset.sum_add_distrib]
    rfl
  rw [hsplit]
  show |interpolatedBlockExponent s U.a U.chainParams.ρA x (frameRadius x) Y V η -
    cellQuadratic U.chainParams.lam x Y η| ≤ _
  rw [hq]
  set Q := ∑ b : ↥(chordBonds (finiteCells F)),
    (if enclosingCell b.1.1 = Y then U.chainParams.lam / 2 else 0) * ‖η b‖ ^ 2 with hQ
  have h2 := abs_sub (interpolatedBlockExponent s U.a U.chainParams.ρA x (frameRadius x) Y V η) (x * Q)
  rw [abs_of_nonneg (a := x * Q) (by positivity)] at h2
  have h3 : x * Q ≤ U.Cs * (x * Q) := by
    have : 0 ≤ x * Q := by positivity
    nlinarith
  nlinarith
end OneTorus
section PairedTori
variable {F F' : BlockFrame} {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem add_siteOfCoords_zero (G : BlockFrame) (Z : G.Cell) :
    Z + siteOfCoords G.top (0 : Fin 4 → ℤ) = Z := by apply _root_.YangMills.SharedProofs.p55653 <;> assumption
private theorem shortPairing_preserves (hDist : cellOffsetStatement) (hL : Odd F.blockSide)
    (hL' : Odd F'.blockSide) (hLL : F.blockSide = F'.blockSide) {q : ℕ} (hq : ∀ i, 2 * q + 2 < F.extent i)
    (hq' : ∀ i, 2 * q + 2 < F'.extent i)
    {Y : F.Cell} {Y' : F'.Cell} {j : ι → ↥(chordBonds (finiteCells F))}
    {j' : ι → ↥(chordBonds (finiteCells F'))} (hp : IsShortPairing Y Y' q j j') :
    (∀ i i', cellSupDist (enclosingCell (j' i).1.1) (enclosingCell (j' i').1.1) =
        cellSupDist (enclosingCell (j i).1.1) (enclosingCell (j i').1.1)) ∧
      (∀ i, cellSupDist (enclosingCell (j' i).1.1) Y' = cellSupDist (enclosingCell (j i).1.1) Y) ∧
      ∀ i, enclosingCell (j i).1.1 = Y ↔ enclosingCell (j' i).1.1 = Y' := by
  have two : ∀ {G : BlockFrame}, (∀ i, 2 * q + 2 < G.extent i) → ∀ i, 2 ≤ G.extent i := fun h i => by
    have := h i
    omega
  obtain ⟨d1, -, -, d4⟩ := hDist F hL (two hq)
  obtain ⟨e1, -, -, e4⟩ := hDist F' hL' (two hq')
  have cells : ∀ i, ∃ h : Fin 4 → ℤ, (∀ l, 2 * |h l| ≤ q) ∧
      enclosingCell (j i).1.1 = Y + siteOfCoords F.top h ∧
      enclosingCell (j' i).1.1 = Y' + siteOfCoords F'.top h := by
    intro i
    obtain ⟨h, o, k, hh, ho, e, e'⟩ := hp.short_offsets i
    refine ⟨h, hh, ?_, ?_⟩
    · rw [e]
      exact d1 Y h o k ho
    · rw [e']
      exact e1 Y' h o k (hLL ▸ ho)
  have zs : ∀ l : Fin 4, 2 * |(0 : Fin 4 → ℤ) l| ≤ q := fun l => by simp
  refine ⟨fun i i' => ?_, fun i => ?_, fun i => ?_⟩
  · obtain ⟨h, hh, a, a'⟩ := cells i
    obtain ⟨g, hg, b, b'⟩ := cells i'
    rw [a, a', b, b', (d4 q hq Y h g hh hg).2, (e4 q hq' Y' h g hh hg).2]
  · obtain ⟨h, hh, a, a'⟩ := cells i
    have h1 := (d4 q hq Y h 0 hh zs).2
    have h2 := (e4 q hq' Y' h 0 hh zs).2
    rw [add_siteOfCoords_zero] at h1 h2
    rw [a, a', h1, h2]
  · obtain ⟨h, hh, a, a'⟩ := cells i
    have o1 := (d4 q hq Y h 0 hh zs).1
    have o2 := (d4 q hq Y 0 0 zs zs).1
    have p1 := (e4 q hq' Y' h 0 hh zs).1
    have p2 := (e4 q hq' Y' 0 0 zs zs).1
    rw [add_siteOfCoords_zero] at o2 p2
    constructor
    · intro h3
      rw [a] at h3
      rw [h3, o2] at o1
      rw [a', ← o1, add_siteOfCoords_zero]
    · intro h3
      rw [a'] at h3
      rw [h3, p2] at p1
      rw [a, ← p1, add_siteOfCoords_zero]
private theorem cellQuadratic_toTorus {Y : F.Cell} {q : ℕ} {j : ι → ↥(chordBonds (finiteCells F))}
    (hj : Function.Injective j) (hr : ∀ b, b ∈ bondsNearCell Y q ↔ ∃ i, j i = b) (lam x : ℝ)
    (ζ : BondField ι) :
    cellQuadratic lam x Y (toTorus j ζ) =
      ∑ i, if enclosingCell (j i).1.1 = Y then x * lam / 2 * ‖ζ i‖ ^ 2 else 0 := by
  symm
  unfold cellQuadratic
  refine Fintype.sum_of_injective j hj _ _ (fun b hb => ?_) (fun i => ?_)
  · have : ¬ enclosingCell b.1.1 = Y := fun h => by
      have hb' : b ∈ bondsNearCell Y q := by
        simp [bondsNearCell, h, cellSupDist_self]
      obtain ⟨i, e⟩ := (hr b).1 hb'
      exact hb ⟨i, e⟩
    simp [this]
  · have e : toTorus j ζ (j i) = ζ i := pushforwardField_apply_image j hj ζ i
    rw [e]
private theorem pairingHomotopy_eq_mixture (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
    (lam x th : ℝ)
    (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F')))
    (Ψ : StepVariable (finiteCells F) → ℝ) (Ψ' : StepVariable (finiteCells F') → ℝ) :
    pairingHomotopy j j' Ψ Ψ' th = convexCombinationExponent lam x ![th, 1 - th]
      ![torusLaw V j Finset.univ Ψ, torusLaw V' j' Finset.univ Ψ'] := by
  funext ζ
  simp [convexCombinationExponent, LawOnBondVariables.exponent, Fin.sum_univ_two, pairingHomotopy,
    frozenExponent, toTorus]
private theorem boundedContinuous_toTorus {ρ : ℝ} (hρ : 0 < ρ) {j : ι → ↥(chordBonds (finiteCells F))}
    (hj : Function.Injective j) {A : StepVariable (finiteCells F) → ℝ} (hA : IsBoundedContinuousOn _ ρ A) :
    IsBoundedContinuousOn ι ρ (fun ζ => A (toTorus j ζ)) := by
  obtain ⟨hc, M, hM⟩ := hA
  have e : (fun ζ => A (toTorus j ζ)) = fun ζ => A (pushforwardFieldCLM j ζ) := by
    funext ζ
    rw [pushforwardFieldCLM_apply]
    rfl
  rw [e]
  refine ⟨hc.comp (pushforwardFieldCLM j).continuous.continuousOn fun ζ hζ => ?_, M,
    fun ζ hζ => hM _ ?_⟩
  · show pushforwardFieldCLM j ζ ∈ openPolyball _ ρ
    rw [pushforwardFieldCLM_apply]
    exact pushforwardField_mem_openPolyball hρ j hj hζ
  · rw [pushforwardFieldCLM_apply]
    exact pushforwardField_mem_openPolyball hρ j hj hζ
private theorem zero_isNormBoundedLocalFamily {L t n₀ : ℕ} {σ δ E E₃ : ℝ} (hE : 0 ≤ E) (hE₃ : 0 ≤ E₃) :
    IsNormBoundedLocalFamily L t n₀ σ δ E E₃ (0 : LocalFamily) := by
  have z : ∀ {G : BlockFrame} {n k : ℕ} (f : G.GaugeField n → ℝ) (W : G.GaugeField n)
      (c : Fin k → G.Site n × Fin 4)
      (X : Fin k → imaginaryQuaternions), (∀ W, f W = 0) → bondDeriv f W c X = 0 := by
    intro G n k f W c X hf
    unfold bondDeriv
    have e : (fun τ : Fin k → ℝ => f (leftTranslate (bondSpread c X τ) W)) = fun _ => 0 := by
      funext τ
      exact hf _
    rw [e]
    have h0 : iteratedFDeriv ℝ k (fun _ : Fin k → ℝ => (0 : ℝ)) = 0 := by
      funext y
      exact congrFun (iteratedFDeriv_fun_zero (𝕜 := ℝ) (E := Fin k → ℝ) (F := ℝ) (n := k)) y
    rw [h0]
    simp
  have wpos : ∀ (r : ℝ), 0 < torusDecayFactor L δ r := fun r =>
    mul_pos (lt_max_of_lt_left one_pos) (Real.exp_pos _)
  refine ⟨fun G _ y W _ k c X => contDiffAt_const, fun G _ y W γ _ => rfl, fun G _ y h W _ => rfl,
    fun G _ y W k c X _ _ _ _ => ?_, fun G G' _ _ y y' W W' r k h X _ _ _ _ _ _ => ?_⟩
  · rw [z ((0 : LocalFamily) G y) W c X (fun _ => rfl), abs_zero]
    refine div_nonneg ?_ (wpos _).le
    split_ifs <;> assumption
  · have e1 : ∀ (G : BlockFrame) (y : G.Site G.depth) (W : G.GaugeField G.depth),
        subtractTrivial (0 : LocalFamily) G y W = 0 := by
      intro G y W
      simp [subtractTrivial]
    rw [z (subtractTrivial 0 G y) W _ X (e1 G y), z (subtractTrivial 0 G' y') W' _ X (e1 G' y')]
    simp only [sub_zero, abs_zero]
    exact div_nonneg hE (wpos _).le
private theorem along_pairingHomotopy (hMeans : CutoffExpectationIsPositiveForm)
    {Co Cm : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ}
    {Cr : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℕ → ℕ → ℝ} {U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ} (D : ChosenParams U x)
    (hS : ObservableSizesAt Co U)
    (hM : MomentBoundsAt Cm Cr U) (hC : ConvexityAt U) {t : ℕ} {s τ : ℝ} {V : F.GaugeField F.top}
    {V' : F'.GaugeField F'.top}
    (Y : F.Cell) (Y' : F'.Cell) {j : ι → ↥(chordBonds (finiteCells F))}
    {j' : ι → ↥(chordBonds (finiteCells F'))} (hj : Function.Injective j) (hj' : Function.Injective j')
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hF : IsCubicTopTorus U.L t U.n₀ F)
    (hF' : IsCubicTopTorus U.L t U.n₀ F') (hV : IsSmallCurvature (5 / 4 * U.σ) V)
    (hV' : IsSmallCurvature (5 / 4 * U.σ) V')
    (hk1 : ∀ i i', cellSupDist (enclosingCell (j' i).1.1) (enclosingCell (j' i').1.1) =
      cellSupDist (enclosingCell (j i).1.1) (enclosingCell (j i').1.1))
    (hk2 : ∀ i, cellSupDist (enclosingCell (j' i).1.1) Y' = cellSupDist (enclosingCell (j i).1.1) Y)
    {th : ℝ} (h0 : 0 ≤ th) (h1 : th ≤ 1) :
    MixtureFacts U x |Cm (momentParameters U) 1|
        (pairingHomotopy j j'
          (weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V)
          (weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V') th) ∧
      HasLocalSize U.ballRadius (cutoffFactor U.ballRadius U.p)
        (pairingHomotopy j j'
          (weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V)
          (weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V') th)
        (Co (momentParameters U)) x U.κ U.Cs (fun i => bondDistToCell Y (j i))
        (fun ζ => cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V
          (toTorus j ζ)) ∧
      HasLocalSize U.ballRadius (cutoffFactor U.ballRadius U.p)
        (pairingHomotopy j j'
          (weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V)
          (weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V') th)
        (Co (momentParameters U)) x U.κ U.Cs (fun i => bondDistToCell Y (j i))
        (fun ζ => cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y' V'
          (toTorus j' ζ)) := by
  set Ψ := weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V with hΨ
  set Ψ' := weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V' with hΨ'
  set d : ι → ι → ℝ := fun i i' => (cellSupDist (enclosingCell (j i).1.1) (enclosingCell (j i').1.1) : ℝ)
    with hd
  have adm1 : (torusLaw V j Finset.univ Ψ).IsAdmissible U.a U.chainParams.ρA U.chainParams.lam x U.σ
      U.decayRate U.E
      U.energyRatio U.L t U.n₀ (frameRadius x) d :=
    ⟨hF, hV, IsIntermediateLaw.ofWeight s τ hs hs1 hτ hτ1, hj, fun _ _ => rfl⟩
  have adm2 : (torusLaw V' j' Finset.univ Ψ').IsAdmissible U.a U.chainParams.ρA U.chainParams.lam x U.σ
      U.decayRate U.E
      U.energyRatio U.L t U.n₀ (frameRadius x) d :=
    ⟨hF', hV', IsIntermediateLaw.ofWeight s τ hs hs1 hτ hτ1, hj', fun i i' => by
      show (cellSupDist (enclosingCell (j i).1.1) (enclosingCell (j i').1.1) : ℝ) =
        cellSupDist (enclosingCell (j' i).1.1) (enclosingCell (j' i').1.1)
      rw [hk1]⟩
  have hadm : ∀ l, (![torusLaw V j Finset.univ Ψ, torusLaw V' j' Finset.univ Ψ'] l).IsAdmissible U.a
      U.chainParams.ρA U.chainParams.lam x U.σ U.decayRate U.E U.energyRatio U.L t U.n₀ (frameRadius x) d :=
    Fin.forall_fin_two.2 ⟨adm1, adm2⟩
  rw [pairingHomotopy_eq_mixture V V' U.chainParams.lam x]
  refine ⟨mixtureFacts_of hMeans D hC hM t d 2 _ _ (isConvexWeights_pair h0 h1) hadm, ?_, ?_⟩
  · exact (hS t x D.coupling_le_x _ d 2 _ _ (isConvexWeights_pair h0 h1) hadm (torusLaw V j Finset.univ Ψ)
      adm1).exponent_sub_quadratic s Y hs hs1
  · have h := (hS t x D.coupling_le_x _ d 2 _ _ (isConvexWeights_pair h0 h1) hadm
      (torusLaw V' j' Finset.univ Ψ') adm2).exponent_sub_quadratic s Y' hs hs1
    have e : embeddedCellDist j' Y' = fun i => bondDistToCell Y (j i) := by
      funext i
      simp only [embeddedCellDist, bondDistToCell]
      rw [hk2]
    exact e ▸ h
private theorem abs_expectation_shared_sub_le [Fintype F.Cell] {U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {x : ℝ}
    (D : ChosenParams U x) (hSl : InterpolatedSlopesCompareAt U)
    (hGa : GapPartsCompareAt U) (hHa : HaarDensitiesCompareAt U) {t : ℕ} {s : ℝ} {V : F.GaugeField F.top}
    {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {q : ℕ} {j : ι → ↥(chordBonds (finiteCells F))}
    {j' : ι → ↥(chordBonds (finiteCells F'))} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hF : IsCubicTopTorus U.L t U.n₀ F)
    (hF' : IsCubicTopTorus U.L t U.n₀ F') (hV : IsSmallCurvature (5 / 4 * U.σ) V)
    (hV' : IsSmallCurvature (5 / 4 * U.σ) V')
    (hAg : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q)
    (hp : IsShortPairing Y Y' q j j') (hnq : U.blockIndex ≤ q) (hE : 0 ≤ U.E) (hE₃ : 0 ≤ U.energyRatio)
    (hiff : ∀ i, enclosingCell (j i).1.1 = Y ↔ enclosingCell (j' i).1.1 = Y') {Φ : BondField ι → ℝ}
    (hform : IsPositiveUnitalForm U.ballRadius U.p Φ) {m : ℝ} (hm0 : 0 ≤ m)
    (hsec : ∀ b, ballExpectation (cutoffFactor U.ballRadius U.p) Φ (fun η => ‖η b‖ ^ 2) ≤ m / x) {W : ℝ}
    (hWs : ∀ z : F.Cell, ∑ i, Real.exp (-(U.κ * (cellSupDist (enclosingCell (j i).1.1) z : ℝ))) ≤ W)
    (hn1 : IsBoundedContinuousOn ι U.ballRadius fun ζ =>
      cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V (toTorus j ζ))
    (hn2 : IsBoundedContinuousOn ι U.ballRadius fun ζ =>
      cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y' V' (toTorus j' ζ)) :
    |ballExpectation (cutoffFactor U.ballRadius U.p) Φ (fun ζ =>
        cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V (toTorus j ζ) -
          cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y' V'
            (toTorus j' ζ))| ≤
      |U.Ct| * Real.exp (-(4 * U.κ * q)) * (W * m + 1) := by
  have hκ := D.κ_pos
  have hρ := D.ballRadius_pos
  have hx1 := D.one_le_x
  have hx0 : 0 < x := by linarith
  have hset : InterpolatedComparisonSetting U t x s (0 : LocalFamily) V V' Y Y' q j j' 0 :=
    { coupling_le := D.coupling_le_x
      interp_mem := ⟨hs, hs1⟩
      family := zero_isNormBoundedLocalFamily hE hE₃
      top := hF
      top' := hF'
      small := hV
      small' := hV'
      agree := hAg
      radius_le := hnq
      injective := hp.isBoxPairing.injective_left
      injective' := hp.isBoxPairing.injective_right
      paired := fun i => by
        obtain ⟨h, o, k, hh, ho, e, e'⟩ := hp.short_offsets i
        refine ⟨h, o, k, ho, fun l => ?_, e, e'⟩
        have h1 := hh l
        linarith
      offset_le := fun i => by simp }
  have a1 := hSl t x s 0 F F' V V' Y Y' q ι j j' 0 hset
  have a2 := hGa t x s 0 F F' V V' Y Y' q ι j j' 0 hset
  have a3 := hHa t x s 0 F F' V V' Y Y' q ι j j' 0 hset
  rw [add_siteOfCoords_zero F Y, add_siteOfCoords_zero F' Y'] at a1 a2 a3
  set E := Real.exp (-(4 * U.κ * q)) with hE'
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hsum : ∑ k, Real.exp (-(2 ^ 5 * U.κ * blockDist F (bondBlock F (j k)) Y)) ≤ W := by
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) (hWs Y)
    apply Real.exp_le_exp.mpr
    have : 0 ≤ U.κ * (cellSupDist (enclosingCell (j k).1.1) Y : ℝ) := by positivity
    simp only [blockDist, bondBlock]
    linarith
  refine abs_expectation_le_of_quadratic hρ hform hx0 hm0 hsec
    (fun k => Real.exp (-(2 ^ 5 * U.κ * blockDist F (bondBlock F (j k)) Y)))
    (fun _ => (Real.exp_pos _).le) hsum (hn1.sub hn2) (mul_nonneg (abs_nonneg _) hE0) fun ξ hξ => ?_
  have b1 := (a1.2 ξ hξ).1
  have b2 := (a2.2 ξ hξ).1
  have b3 := (a3.2 ξ hξ).1
  set S := weightedSqNormNear U.κ (fun k => bondBlock F (j k)) (blockDist F) Y ξ with hS
  have hS0 : 0 ≤ S := weightedSqNormNear_nonneg _ _
  have hsq : cellQuadratic U.chainParams.lam x Y (toTorus j ξ) =
      cellQuadratic U.chainParams.lam x Y' (toTorus j' ξ) := by
    rw [cellQuadratic_toTorus hp.isBoxPairing.injective_left hp.isBoxPairing.mem_left_iff,
      cellQuadratic_toTorus hp.isBoxPairing.injective_right hp.isBoxPairing.mem_right_iff]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : enclosingCell (j i).1.1 = Y
    · simp [h, (hiff i).1 h]
    · have h' : ¬ enclosingCell (j' i).1.1 = Y' := fun e => h ((hiff i).2 e)
      simp [h, h']
  have e : cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V (toTorus j ξ) -
      cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y' V'
        (toTorus j' ξ) =
      -(interpolatedSlopePart s U.a U.chainParams.ρA x (frameRadius x) Y' V' (pushforwardField j' ξ) -
          interpolatedSlopePart s U.a U.chainParams.ρA x (frameRadius x) Y V (pushforwardField j ξ)) +
        (interpolatedGapPart s U.a U.chainParams.ρA x (frameRadius x) Y' V' (pushforwardField j' ξ) -
          interpolatedGapPart s U.a U.chainParams.ρA x (frameRadius x) Y V (pushforwardField j ξ)) +
        (interpolatedHaarPart s U.a U.chainParams.ρA (frameRadius x) Y' V' (pushforwardField j' ξ) -
          interpolatedHaarPart s U.a U.chainParams.ρA (frameRadius x) Y V (pushforwardField j ξ)) := by
    have c1 : cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V
        (toTorus j ξ) =
        interpolatedSlopePart s U.a U.chainParams.ρA x (frameRadius x) Y V (pushforwardField j ξ) -
          interpolatedGapPart s U.a U.chainParams.ρA x (frameRadius x) Y V (pushforwardField j ξ) -
          interpolatedHaarPart s U.a U.chainParams.ρA (frameRadius x) Y V (pushforwardField j ξ) -
          cellQuadratic U.chainParams.lam x Y (toTorus j ξ) := rfl
    have c2 : cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y' V'
        (toTorus j' ξ) =
        interpolatedSlopePart s U.a U.chainParams.ρA x (frameRadius x) Y' V' (pushforwardField j' ξ) -
          interpolatedGapPart s U.a U.chainParams.ρA x (frameRadius x) Y' V' (pushforwardField j' ξ) -
          interpolatedHaarPart s U.a U.chainParams.ρA (frameRadius x) Y' V' (pushforwardField j' ξ) -
          cellQuadratic U.chainParams.lam x Y' (toTorus j' ξ) := rfl
    rw [c1, c2, hsq]
    ring
  show |cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V (toTorus j ξ) -
      cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y' V'
        (toTorus j' ξ)| ≤ _
  rw [e]
  have hR : 0 ≤ x * S + 1 := by positivity
  have hCt := le_abs_self U.Ct
  have hfin : U.Ct / 3 * E * (x * S + 1) ≤ |U.Ct| / 3 * E * (x * S + 1) := by
    have : U.Ct / 3 ≤ |U.Ct| / 3 := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hE0) hR
  have t1 := abs_add_three
    (-(interpolatedSlopePart s U.a U.chainParams.ρA x (frameRadius x) Y' V' (pushforwardField j' ξ) -
          interpolatedSlopePart s U.a U.chainParams.ρA x (frameRadius x) Y V (pushforwardField j ξ)))
    (interpolatedGapPart s U.a U.chainParams.ρA x (frameRadius x) Y' V' (pushforwardField j' ξ) -
          interpolatedGapPart s U.a U.chainParams.ρA x (frameRadius x) Y V (pushforwardField j ξ))
    (interpolatedHaarPart s U.a U.chainParams.ρA (frameRadius x) Y' V' (pushforwardField j' ξ) -
          interpolatedHaarPart s U.a U.chainParams.ρA (frameRadius x) Y V (pushforwardField j ξ))
  rw [abs_neg] at t1
  refine t1.trans ?_
  have hgoal : |U.Ct| * E * (x * S + 1) = 3 * (|U.Ct| / 3 * E * (x * S + 1)) := by ring
  show _ ≤ |U.Ct| * E * (x * S + 1)
  rw [hgoal]
  linarith
private theorem card_shared_le {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j)
    (u : F.Cell) :
    (Finset.univ.filter fun i => enclosingCell (j i).1.1 = u).card ≤
      (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = u).card := by
  refine Finset.card_le_card_of_injOn j (fun i hi => ?_) hj.injOn
  simpa using hi
private theorem card_cellBonds_le (hCnt : cellBondsCardStatement) {G : BlockFrame} {L : ℕ}
    (hG : G.blockSide = L) (ho : Odd G.blockSide) (h2 : ∀ i, 2 ≤ G.extent i) (z : G.Cell) :
    (Finset.univ.filter fun b : ↥(chordBonds (finiteCells G)) => enclosingCell b.1.1 = z).card ≤
      4 * L ^ 4 := by
  have := hCnt G ho h2 z
  rwa [hG] at this
set_option maxHeartbeats 400000 in
private theorem comparisonBounds_at (hlaw : normalizedBallLawIsProbabilityStatement)
    (hMeans : CutoffExpectationIsPositiveForm)
    (hCnt : cellBondsCardStatement) (hDist : cellOffsetStatement)
    {Co Cm : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ} {Cr : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℕ → ℕ → ℝ} {U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters}
    {x α W : ℝ}
    (D : ChosenParams U x) (sz : ObservableSizesAt Co U) (mo : MomentBoundsAt Cm Cr U) (cv : ConvexityAt U)
    (pa : StepLawLocalDecomposition U) (bo : ExponentBoundsAt U) (sl : InterpolatedSlopesCompareAt U)
    (ga : GapPartsCompareAt U) (ha : HaarDensitiesCompareAt U) (hodd : Odd U.L) (hE : 1 ≤ U.E)
    (hη : 0 < U.η₃) (hn : 1 ≤ U.n₀)
    (hWall : ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (y : ι → F.Cell),
      (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ 4 * U.L ^ 4) →
      ∀ z : F.Cell, ∑ b, Real.exp (-(U.κ * (cellSupDist (y b) z : ℝ))) ≤ W)
    (a1 : |Co (momentParameters U) 2| * U.Cs ≤ α)
    (a2 : U.Cs * W * (|Cm (momentParameters U) 1| * (1 + W) / 2 + (1 + |Cm (momentParameters U) 1|) / 2)
      ≤ α)
    (a3 : 2 * (U.Cs * ((W + U.chainParams.lam / 2 * ((4 * U.L ^ 4 : ℕ) : ℝ)) * |Cm (momentParameters U) 1|
      + 1)) ≤ α)
    (a4 : |U.Ct| * (W * |Cm (momentParameters U) 1| + 1) ≤ α)
    {t : ℕ} {s τ : ℝ} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    {q : ℕ}
    {j : ι → ↥(chordBonds (finiteCells F))} {j' : ι → ↥(chordBonds (finiteCells F'))}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hTF : IsCubicTopTorus U.L t U.n₀ F) (hTF' : IsCubicTopTorus U.L t U.n₀ F')
    (hV : IsSmallCurvature (5 / 4 * U.σ) V) (hV' : IsSmallCurvature (5 / 4 * U.σ) V')
    (hAg : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q)
    (hpair : IsShortPairing Y Y' q j j') :
    (ComparisonHypotheses U.ballRadius U.chainParams.lam x U.κ α U.p U.blockIndex q Y Y' j j'
      (weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V)
      (cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V)
      (weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V')
      (cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y' V')) ∧
    ContDiffOn ℝ 1 (cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V)
      {η | ∀ b, ‖η b‖ < U.ballRadius} ∧
    ContDiffOn ℝ 1 (cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y' V')
      {η | ∀ b, ‖η b‖ < U.ballRadius} := by
  have hc := D.one_le_Cs
  have sides : ∀ {G : BlockFrame}, IsCubicTopTorus U.L t U.n₀ G →
      (∀ i, G.extent i = 0 ∨ 2 * q + 2 < G.extent i) → ∀ i, 2 * q + 2 < G.extent i := by
    intro G hG hA i
    obtain ⟨-, -, m, hm, hnm⟩ := hG
    rcases hA i with h | h
    · have := hm i
      omega
    · exact h
  have hq := sides hTF hAg.1
  have hq' := sides hTF' hAg.2.1
  have hL : Odd F.blockSide := by rw [hTF.1]; exact hodd
  have hL' : Odd F'.blockSide := by rw [hTF'.1]; exact hodd
  have hLL : F.blockSide = F'.blockSide := hTF.1.trans hTF'.1.symm
  have two : ∀ {G : BlockFrame}, (∀ i, 2 * q + 2 < G.extent i) → ∀ i, 2 ≤ G.extent i := fun h i => by
    have := h i
    omega
  have finite_cells : ∀ {G : BlockFrame}, (∀ i, 2 ≤ G.extent i) → Finite G.Cell := by
    intro G h
    have hne : ∀ i, NeZero (G.period G.top i) := fun i => ⟨by
      simp only [BlockFrame.period, Nat.sub_self, pow_zero, mul_one]
      have := h i
      omega⟩
    have : ∀ i, Finite (ZMod (G.period G.top i)) := fun i => by
      have := hne i
      exact inferInstance
    exact Pi.finite
  have := finite_cells (two hq)
  have := finite_cells (two hq')
  let : Fintype F.Cell := Fintype.ofFinite _
  let : Fintype F'.Cell := Fintype.ofFinite _
  have few : ∀ {G : BlockFrame}, G.blockSide = U.L → Odd G.blockSide → (∀ i, 2 ≤ G.extent i) →
      ∀ z : G.Cell,
      (Finset.univ.filter fun b : ↥(chordBonds (finiteCells G)) => enclosingCell b.1.1 = z).card ≤
        4 * U.L ^ 4 :=
    fun hG ho h2 z => card_cellBonds_le hCnt hG ho h2 z
  have sums : ∀ {G : BlockFrame}, G.blockSide = U.L → Odd G.blockSide → (∀ i, 2 ≤ G.extent i) →
      ∀ z : G.Cell,
      ∑ b : ↥(chordBonds (finiteCells G)), Real.exp (-(U.κ * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ W :=
    fun {G} hG ho h2 z =>
      hWall G ↥(chordBonds (finiteCells G)) (fun b => enclosingCell b.1.1) (few hG ho h2) z
  have first := comparisonBoundsOnTorus_of hlaw hMeans D sz mo cv pa bo (t := t) (s := s) (τ := τ) (V := V)
    Y q hs hs1 hτ hτ1 hTF hV (sums hTF.1 hL (two hq)) a1 a2
  have second := comparisonBoundsOnTorus_of hlaw hMeans D sz mo cv pa bo (t := t) (s := s) (τ := τ)
    (V := V') Y' q hs hs1 hτ hτ1 hTF' hV' (sums hTF'.1 hL' (two hq')) a1 a2
  have m1 := abs_expectation_remainder_le hMeans D sz mo cv pa bo (t := t) (s := s) (τ := τ) (V := V) Y hs
    hs1 hτ hτ1 hTF hV (sums hTF.1 hL (two hq)) (few hTF.1 hL (two hq) Y)
  have m2 := abs_expectation_remainder_le hMeans D sz mo cv pa bo (t := t) (s := s) (τ := τ) (V := V') Y' hs
    hs1 hτ hτ1 hTF' hV' (sums hTF'.1 hL' (two hq')) (few hTF'.1 hL' (two hq') Y')
  obtain ⟨k1, k2, k3⟩ := shortPairing_preserves hDist hL hL' hLL hq hq' hpair
  have hinj := hpair.isBoxPairing.injective_left
  have hinj' := hpair.isBoxPairing.injective_right
  have hρ := D.ballRadius_pos
  have hcut' : IsCutoff U.ballRadius U.p := D.isCutoff
  have hc0 : 0 ≤ U.Cs := by linarith
  obtain ⟨hcd, hnice⟩ := remainder_regular (s := s) (V := V) (t := t) D pa bo Y hs hs1 hTF hV
  obtain ⟨hcd', hnice'⟩ := remainder_regular (s := s) (V := V') (t := t) D pa bo Y' hs hs1 hTF' hV'
  have hn1 := boundedContinuous_toTorus hρ hinj hnice
  have hn2 := boundedContinuous_toTorus hρ hinj' hnice'
  have pair := fun th (h0 : 0 ≤ th) (h1 : th ≤ 1) =>
    along_pairingHomotopy hMeans D sz mo cv (t := t) (s := s) (τ := τ) (V := V) (V' := V') Y Y' hinj hinj'
      hs hs1 hτ hτ1 hTF hTF' hV hV' k1 k2 h0 h1
  have hWj : ∀ z : F.Cell, ∑ i, Real.exp (-(U.κ * (cellSupDist (enclosingCell (j i).1.1) z : ℝ))) ≤ W := by
    intro z
    exact hWall F ι (fun i => enclosingCell (j i).1.1)
      (fun u => (card_shared_le hinj u).trans (few hTF.1 hL (two hq) u)) z
  have hE0 : 0 ≤ U.E := by linarith
  have hE3 : 0 ≤ U.energyRatio := by
    show 0 ≤ U.E / U.η₃
    positivity
  refine ⟨⟨first, second, ?_, fun th h0 h1 => ?_, fun hnq th h0 h1 => ?_⟩, hcd, hcd'⟩
  · have h1 := abs_sub (ballExpectation (cutoffFactor U.ballRadius U.p)
      (weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V)
      (cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y V))
      (ballExpectation (cutoffFactor U.ballRadius U.p)
        (weightLawExponent s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) τ V')
        (cellExponentRemainder s U.a U.chainParams.ρA U.chainParams.lam x (frameRadius x) Y' V'))
    refine h1.trans ?_
    have h2 := add_le_add m1 m2
    refine h2.trans ?_
    refine le_trans (le_of_eq ?_) a3
    ring
  · obtain ⟨fa, s1, s2⟩ := pair th h0 h1
    obtain ⟨Ψ', c', ag'⟩ := fa.extension
    exact ⟨hasGradientBound_of_hasLocalSize hlaw hρ hcut' c' ag' hn1 hc0 a1 s1,
      hasGradientBound_of_hasLocalSize hlaw hρ hcut' c' ag' hn2 hc0 a1 s2⟩
  · obtain ⟨fa, -, -⟩ := pair th h0 h1
    have h := abs_expectation_shared_sub_le D sl ga ha (t := t) (s := s) hs hs1 hTF hTF' hV hV'
      hAg hpair hnq hE0 hE3 k3 fa.form (abs_nonneg _) fa.secondMoment hWj hn1 hn2
    refine h.trans ?_
    have he := (Real.exp_pos (-(4 * U.κ * q))).le
    calc _ = (|U.Ct| * (W * |Cm (momentParameters U) 1| + 1)) * Real.exp (-(4 * U.κ * q)) := by
          ring
      _ ≤ α * Real.exp (-(4 * U.κ * q)) := mul_le_mul_of_nonneg_right a4 he
end PairedTori
private def AllEstimatesAt (Co Cm : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ) (Cr : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℕ → ℕ → ℝ)
    (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ObservableSizesAt Co T ∧ MomentBoundsAt Cm Cr T ∧ ConvexityAt T ∧ StepLawLocalDecomposition T ∧
    ExponentBoundsAt T ∧ InterpolatedSlopesCompareAt T ∧ GapPartsCompareAt T ∧ HaarDensitiesCompareAt T
private def lowerBoundCs (Co Cm : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ) (Wf : ℕ → ℝ → ℝ) (U : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (c : ℝ) :
    ℝ :=
  max (max (|Co U 2| * c)
      (c * Wf (4 * U.L ^ 4) U.κ * (|Cm U 1| * (1 + Wf (4 * U.L ^ 4) U.κ) / 2 + (1 + |Cm U 1|) / 2)))
    (max (2 * (c * ((Wf (4 * U.L ^ 4) U.κ + U.chainParams.lam / 2 * ((4 * U.L ^ 4 : ℕ) : ℝ)) * |Cm U 1|
        + 1)))
      (|U.Ct| * (Wf (4 * U.L ^ 4) U.κ * |Cm U 1| + 1)))
end Parameters
end RemainderProof
open RemainderProof ColdStepAtMirrorFrames.LocalCalculus in
theorem remainderIsAdmissible_holds (hJ : joinAtLoweredSmallnessConstantStatement)
    (hObs : observableSizesStatement) (hMom : intermediateLawMoments)
    (hCv : mixturesOfIntermediateLawsConvex) (hParts : stepLawLocalDecomposition)
    (hBd : interpolatedExponentBoundsStatement) (hSl : interpolatedSlopesCompareStatement)
    (hGa : GapPartsCompare) (hHa : HaarDensitiesCompare)
    (hMeans : CutoffExpectationIsPositiveForm) (hlaw : normalizedBallLawIsProbabilityStatement)
    (hW : _root_.YangMills.Construction.CellCounting.ExpDecaySumBounded) (hCnt : cellBondsCardStatement)
    (hDist : cellOffsetStatement) : remainderIsAdmissible := by
  obtain ⟨Co, hO⟩ := hObs
  obtain ⟨Cm, Cr, hMo⟩ := hMom
  have hW' : ∀ (N : ℕ) (κ : ℝ), ∃ W : ℝ, 0 < κ → 0 ≤ W ∧
      ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (y : ι → F.Cell),
        (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ N) →
        ∀ z : F.Cell, ∑ b, Real.exp (-(κ * (cellSupDist (y b) z : ℝ))) ≤ W := by
    intro N κ
    by_cases h : 0 < κ
    · obtain ⟨W, h1, h2⟩ := hW N κ h
      exact ⟨W, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Wf hWf using hW'
  have hAll : EventuallyInParameters (AllEstimatesAt Co Cm Cr) :=
    eventuallyInParameters_and (P := ObservableSizesAt Co) hO
      (eventuallyInParameters_and (P := MomentBoundsAt Cm Cr) hMo
        (eventuallyInParameters_and (P := ConvexityAt) hCv
          (eventuallyInParameters_and hParts
            (eventuallyInParameters_and (P := ExponentBoundsAt) hBd
              (eventuallyInParameters_and hSl (eventuallyInParameters_and hGa hHa))))))
  refine hJ (AllEstimatesAt Co Cm Cr) (AllEstimatesAt Co Cm Cr) RemainderIsAdmissible (lowerBoundCs Co Cm Wf)
    hAll hAll ?_
  intro T c hc hodd hn hy hE hη hη1 hκ hσ hch hcut hGle hPk _
  obtain ⟨sz, mo, cv, pa, bo, sl, ga, ha⟩ := hPk
  intro t x s τ F F' V V' Y Y' q ι _ _ j j' hx hs hs1 hτ hτ1 hTF hTF' hV hV' hAg hpair
  have hx1 : 1 ≤ x := hy.trans hx
  have hlam : 0 < T.chainParams.lam := hch.positivity.2.2.1
  have D : ChosenParams { T with Cs := c } x := ⟨hκ, hσ, hcut, hlam, hx1, hx, hc⟩
  obtain ⟨-, hWall⟩ := hWf (4 * T.L ^ 4) T.κ hκ
  have hnum := hGle
  unfold lowerBoundCs at hnum
  rw [max_le_iff, max_le_iff, max_le_iff] at hnum
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hnum
  exact comparisonBounds_at (U := { T with Cs := c }) (α := T.Cs) hlaw hMeans hCnt hDist D sz mo cv pa bo
    sl ga ha hodd hE hη hn hWall a1 a2 a3 a4 hs hs1 hτ hτ1 hTF hTF' hV hV' hAg hpair
end TorusFreezing
end YangMills.Construction
end
