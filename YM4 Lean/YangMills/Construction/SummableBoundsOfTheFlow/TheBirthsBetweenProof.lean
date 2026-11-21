import YangMills.Construction.ColdStepAtMirrorFrames.CurvesOfTheFrames
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeAlongChosenBonds
import YangMills.Construction.ColdStepAtMirrorFrames.DominatedOnTheBalls
import YangMills.Construction.ColdStepAtMirrorFrames.MeanAlongAParameter
import YangMills.Construction.ColdStepAtMirrorFrames.PlainChainAtLevelZeroProof
import YangMills.Construction.RunningCouplingSlope.HaarDensityAtTheLeastFieldHasKernelsProof
import YangMills.Construction.SummableBoundsOfTheFlow.BondsOfACellAreFew
import YangMills.Construction.SummableBoundsOfTheFlow.BoundsMatchAtChosenConstant
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfTheMeanOfAPartProof
import YangMills.Construction.SummableBoundsOfTheFlow.FreezingOfTheWeightPart
import YangMills.Construction.SummableBoundsOfTheFlow.LinesOfTwoTops
import YangMills.Construction.SummableBoundsOfTheFlow.MeansOfTheWeightPartAreInvariant
import YangMills.Construction.SummableBoundsOfTheFlow.PartsBetweenAreSmoothInTheParameters
import YangMills.Construction.SummableBoundsOfTheFlow.TheBirthsBetween
import YangMills.Construction.SummableBoundsOfTheFlow.TheFramesBetween
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages hiding bondSpread
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation YangMills.Construction.TorusComparison YangMills.Construction.TorusFreezing YangMills.Construction.DerivativeInterpolation YangMills.Construction.SummableBounds YangMills.Construction.Estimates MeasureTheory Topology
namespace YangMills.Construction.InterpolatedBirths
variable {F : BlockFrame}
theorem leftTranslate_bondSpread_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top) :
    leftTranslate (bondSpread c X 0) V = V := by apply _root_.YangMills.SharedProofs.p2043 <;> assumption
theorem continuous_plaquetteDefect_translate {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top) (p : F.Site F.top × Fin 4 × Fin 4) :
    Continuous fun τ : Fin k → ℝ => plaquetteDefect (leftTranslate (bondSpread c X τ) V) p := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.continuous_plaquetteDefect <;> assumption
theorem eventually_isSmallCurvature_translate {k : ℕ} (hfin : Finite F.Cell) {s : ℝ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature s V) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0, IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by
  have hf : Finite (F.Site F.top × Fin 4 × Fin 4) := inferInstance
  exact show ∀ᶠ τ : Fin k → ℝ in 𝓝 0, ∀ p : F.Site F.top × Fin 4 × Fin 4, p.2.1 < p.2.2 →
      plaquetteDefect (leftTranslate (bondSpread c X τ) V) p < s from by
    rw [Filter.eventually_all]
    intro p
    by_cases hp : p.2.1 < p.2.2
    · have h1 := hV p hp
      have h2 : plaquetteDefect (leftTranslate (bondSpread c X (0 : Fin k → ℝ)) V) p < s := by
        rw [leftTranslate_bondSpread_zero]
        exact h1
      filter_upwards [(continuous_plaquetteDefect_translate c X V p).continuousAt.eventually_lt
        continuousAt_const h2] with τ hτ _ using hτ
    · exact Filter.Eventually.of_forall fun τ h => absurd h hp
theorem IsDominatedSmoothFamily.mono {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ}
    {B B' : Set (Fin k → ℝ)} {K K' : ℝ} {G : (Fin k → ℝ) → Ω → ℝ} (hB : B' ⊆ B) (hK : K ≤ K')
    (h : IsDominatedSmoothFamily μ 3 B K G) : IsDominatedSmoothFamily μ 3 B' K' G := by
  refine ⟨fun τ hτ => h.aestronglyMeasurable τ (hB hτ), ?_, ?_⟩
  · filter_upwards [h.contDiffOn] with ω hω using hω.mono hB
  · filter_upwards [h.norm_iteratedFDeriv_le] with ω hω j hj τ hτ using le_trans (hω j hj τ (hB hτ)) hK
theorem contDiff_totalQuadratic (lam x : ℝ) : ContDiff ℝ 3 (totalQuadratic (F := F) lam x) := by
  unfold totalQuadratic
  refine ContDiff.sum fun b _ => ?_
  exact contDiff_const.mul ((contDiff_apply ℝ _ b).norm_sq ℝ)
theorem contDiff_cellQuadratic (lam x : ℝ) (Y : F.Cell) :
    ContDiff ℝ 3 (cellQuadratic (F := F) lam x Y) := by
  unfold cellQuadratic
  refine ContDiff.sum fun b _ => ?_
  split_ifs
  · exact contDiff_const.mul ((contDiff_apply ℝ _ b).norm_sq ℝ)
  · exact contDiff_const
theorem gibbsMean_congr_ae {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {A A' H H' : Ω → ℝ}
    (hA : A =ᵐ[μ] A') (hH : H =ᵐ[μ] H') : gibbsMean μ A H = gibbsMean μ A' H' := by
  unfold gibbsMean
  congr 1
  · apply integral_congr_ae
    filter_upwards [hA, hH] with ω h1 h2
    rw [h1, h2]
  · apply integral_congr_ae
    filter_upwards [hA] with ω h1
    rw [h1]
theorem iteratedFDeriv_smul_sum_add_const {P α : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (S : Finset α) (φ : α → P → ℝ) (v r : ℝ)
    {n : ℕ} (hn : n ≠ 0) (hφ : ∀ i ∈ S, ContDiffAt ℝ n (φ i) 0) (w : Fin n → P) :
    iteratedFDeriv ℝ n (fun τ => v * ∑ i ∈ S, φ i τ + r) 0 w =
      v * ∑ i ∈ S, iteratedFDeriv ℝ n (φ i) 0 w := by
  classical
  have hsum : ContDiffAt ℝ n (fun τ => ∑ i ∈ S, φ i τ) 0 ∧
      iteratedFDeriv ℝ n (fun τ => ∑ i ∈ S, φ i τ) 0 w = ∑ i ∈ S, iteratedFDeriv ℝ n (φ i) 0 w := by
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨by simpa using contDiffAt_const, ?_⟩
      simp [iteratedFDeriv_const_of_ne hn]
    | insert i S hi ih =>
      obtain ⟨i1, i2⟩ := ih fun j hj => hφ j (Finset.mem_insert_of_mem hj)
      have h1 := hφ i (Finset.mem_insert_self i S)
      have e : (fun τ => ∑ j ∈ insert i S, φ j τ) = φ i + fun τ => ∑ j ∈ S, φ j τ := by
        funext τ
        simp [Finset.sum_insert hi]
      rw [e, Finset.sum_insert hi]
      refine ⟨h1.add i1, ?_⟩
      rw [iteratedFDeriv_add_apply h1 i1]
      simp only [add_apply, i2]
  obtain ⟨s1, s2⟩ := hsum
  have e : (fun τ => v * ∑ i ∈ S, φ i τ + r) = (v • fun τ => ∑ i ∈ S, φ i τ) + fun _ => r := by
    funext τ
    simp
  have s3 : ContDiffAt ℝ n (v • fun τ => ∑ i ∈ S, φ i τ) 0 := s1.const_smul v
  rw [e, iteratedFDeriv_add_apply s3 contDiffAt_const, iteratedFDeriv_const_of_ne hn,
    iteratedFDeriv_const_smul_apply s1]
  simp [s2]
theorem continuousOn_gibbsMean {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) {a h : ℝ → Ω → ℝ} {K : ℝ} (hm : ∀ v ∈ Set.Icc (0 : ℝ) 1, AEStronglyMeasurable (a v) μ)
    (hm' : ∀ v ∈ Set.Icc (0 : ℝ) 1, AEStronglyMeasurable (h v) μ)
    (hb : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ ω ∂μ, |a v ω| ≤ K) (hb' : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ ω ∂μ, |h v ω| ≤ K)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun v => a v ω) (Set.Icc (0 : ℝ) 1))
    (hc' : ∀ᵐ ω ∂μ, ContinuousOn (fun v => h v ω) (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun v => gibbsMean μ (a v) (h v)) (Set.Icc (0 : ℝ) 1) := by
  have hexpm : ∀ v ∈ Set.Icc (0 : ℝ) 1, AEStronglyMeasurable (fun ω => Real.exp (- a v ω)) μ := fun v hv =>
    Real.continuous_exp.comp_aestronglyMeasurable (hm v hv).neg
  have hexpb : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ ω ∂μ, ‖Real.exp (- a v ω)‖ ≤ Real.exp K := fun v hv => by
    filter_upwards [hb v hv] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hω).1])
  have hexpc : ∀ᵐ ω ∂μ, ContinuousOn (fun v => Real.exp (- a v ω)) (Set.Icc (0 : ℝ) 1) := by
    filter_upwards [hc] with ω hω
    exact Real.continuous_exp.comp_continuousOn hω.neg
  have hnum : ContinuousOn (fun v => ∫ ω, h v ω * Real.exp (- a v ω) ∂μ) (Set.Icc (0 : ℝ) 1) := by
    refine continuousOn_of_dominated (bound := fun _ => |K| * Real.exp K)
      (fun v hv => (hm' v hv).mul (hexpm v hv)) (fun v hv => ?_) (integrable_const _) ?_
    · filter_upwards [hb' v hv, hexpb v hv] with ω h1 h2
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (h1.trans (le_abs_self K)) h2 (norm_nonneg _) (abs_nonneg K)
    · filter_upwards [hc', hexpc] with ω h1 h2
      exact h1.mul h2
  have hden : ContinuousOn (fun v => ∫ ω, Real.exp (- a v ω) ∂μ) (Set.Icc (0 : ℝ) 1) :=
    continuousOn_of_dominated (bound := fun _ => Real.exp K) hexpm hexpb (integrable_const _) hexpc
  refine hnum.div hden fun v hv => ?_
  have hI : Integrable (fun ω => Real.exp (- a v ω)) μ :=
    Integrable.of_bound (hexpm v hv) (Real.exp K) (hexpb v hv)
  have hlow : ∫ _ω, Real.exp (-K) ∂μ ≤ ∫ ω, Real.exp (- a v ω) ∂μ := by
    refine integral_mono_ae (integrable_const _) hI ?_
    filter_upwards [hb v hv] with ω hω
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hω).2])
  have hpos : 0 < ∫ _ω, Real.exp (-K) ∂μ := by
    rw [integral_const, smul_eq_mul]
    have : 0 < μ.real Set.univ := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hμ) (measure_ne_top _ _)
    exact mul_pos this (Real.exp_pos _)
  exact (lt_of_lt_of_le hpos hlow).ne'
theorem bondDeriv_zero {j : ℕ} (g : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : Fin 0 → F.Site j × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) : bondDeriv g W c X = g W := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
theorem interpolation_sum_le {κ c τ : ℝ} {r k : ℕ} (hκ : 0 < κ) (hc : 0 < c) (hτ : 0 < τ) (hk1 : 1 ≤ k)
    (hk2 : k ≤ 2) :
    c * Real.exp (-(κ * r / 2 ^ 7)) / τ ^ k +
        (c * Real.exp (-(κ * r / 2 ^ 7))) ^ (1 - (k : ℝ) / 3) * c ^ ((k : ℝ) / 3) ≤
      c * (1 + 1 / τ + (1 / τ) ^ 2) * Real.exp (-(κ / 2 ^ 9 * r)) := by
  set E₀ := Real.exp (-(κ * r / 2 ^ 7)) with hE₀
  set E₁ := Real.exp (-(κ / 2 ^ 9 * r)) with hE₁
  have hκr : 0 ≤ κ * r := by positivity
  have hE₀0 : 0 < E₀ := Real.exp_pos _
  have h01 : E₀ ≤ E₁ := by
    apply Real.exp_le_exp.mpr
    have e : κ / 2 ^ 9 * r = κ * r / 2 ^ 9 := by ring
    rw [e]
    nlinarith
  have hiτ : 0 < 1 / τ := by positivity
  have h1 : c * E₀ / τ ^ k ≤ c * E₁ * (1 / τ + (1 / τ) ^ 2) := by
    have hcE : c * E₀ ≤ c * E₁ := mul_le_mul_of_nonneg_left h01 hc.le
    have hk : k = 1 ∨ k = 2 := by omega
    have hq : 0 < (1 / τ) ^ 2 := by positivity
    rcases hk with rfl | rfl
    · rw [pow_one, div_eq_mul_one_div]
      have : c * E₀ * (1 / τ) ≤ c * E₁ * (1 / τ) := mul_le_mul_of_nonneg_right hcE hiτ.le
      have h3 : c * E₁ * (1 / τ) ≤ c * E₁ * (1 / τ + (1 / τ) ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    · have e : c * E₀ / τ ^ 2 = c * E₀ * (1 / τ) ^ 2 := by
        field_simp
      rw [e]
      have : c * E₀ * (1 / τ) ^ 2 ≤ c * E₁ * (1 / τ) ^ 2 := mul_le_mul_of_nonneg_right hcE hq.le
      have h3 : c * E₁ * (1 / τ) ^ 2 ≤ c * E₁ * (1 / τ + (1 / τ) ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
  set α : ℝ := (k : ℝ) / 3 with hα
  have hα1 : α ≤ 2 / 3 := by
    have : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
    rw [hα]
    linarith
  have h2 : (c * E₀) ^ (1 - α) * c ^ α ≤ c * E₁ := by
    rw [Real.mul_rpow hc.le hE₀0.le]
    have e1 : c ^ (1 - α) * E₀ ^ (1 - α) * c ^ α = c * E₀ ^ (1 - α) := by
      have : c ^ (1 - α) * c ^ α = c := by
        rw [← Real.rpow_add hc]
        simp
      calc c ^ (1 - α) * E₀ ^ (1 - α) * c ^ α = (c ^ (1 - α) * c ^ α) * E₀ ^ (1 - α) := by ring
        _ = _ := by rw [this]
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ hc.le
    rw [hE₀, ← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have e : κ / 2 ^ 9 * r = κ * r / 2 ^ 9 := by ring
    rw [e]
    nlinarith
  calc c * E₀ / τ ^ k + (c * E₀) ^ (1 - α) * c ^ α
      ≤ c * E₁ * (1 / τ + (1 / τ) ^ 2) + c * E₁ := add_le_add h1 h2
    _ = c * (1 + 1 / τ + (1 / τ) ^ 2) * E₁ := by ring
theorem cutoffMean_eq_ballExpectation {ρ : ℝ} {p : ℝ → ℝ} {A₀ Ψ : StepVariable (finiteCells F) → ℝ}
    (hA : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → A₀ η = Ψ η)
    (g : StepVariable (finiteCells F) → ℝ) :
    cutoffMean ρ p A₀ g = ballExpectation (cutoffFactor ρ p) Ψ g := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.cutoffMean_eq_ballExpectation <;> assumption
def translatedExponent (s a ρA lam x : ℝ) (m : ℕ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (v : ℝ) (τ : Fin k → ℝ)
    (η : StepVariable (finiteCells F)) : ℝ :=
  v * ∑ Y' ∈ finiteCells F, interpolatedBlockExponent s a ρA x m Y' (leftTranslate (bondSpread c X τ) V) η +
    (1 - v) * totalQuadratic lam x η
def translatedRemainder (s a ρA lam x : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (η : StepVariable (finiteCells F)) : ℝ :=
  interpolatedBlockExponent s a ρA x m Y (leftTranslate (bondSpread c X τ) V) η - cellQuadratic lam x Y η
theorem translated_dominated_and_eq {s a ρA ρ lam x u : ℝ} {m k : ℕ} {p : ℝ → ℝ} {V : F.GaugeField F.top}
    (hρ : 0 < ρ) (hcut : IsCutoff ρ p) (hfin : Finite F.Cell) (hRim : CutoffMeanIsGibbsMean)
    (hDom : DominatedFamilyOnClosedBalls)
    (hSum : ∀ V' : F.GaugeField F.top, IsSmallCurvature u V' → ∀ η : StepVariable (finiteCells F),
      (∀ b, ‖η b‖ < ρ) → interpolatedExponent s a ρA x m V' η =
        ∑ Y ∈ finiteCells F, interpolatedBlockExponent s a ρA x m Y V' η)
    (hSm : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
        interpolatedBlockExponent s a ρA x m Y (leftTranslate (bondSpread c X q.1) V) q.2) (0, η))
    (hV : IsSmallCurvature u V) (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ∃ r M : ℝ, 0 < r ∧
      (∀ v ∈ Set.Icc (0 : ℝ) 1, IsDominatedSmoothFamily (cutoffLaw F ρ p) 3 (Metric.ball 0 r) M
        (translatedExponent s a ρA lam x m V c X v)) ∧
      (∀ v ∈ Set.Icc (0 : ℝ) 1, IsDominatedSmoothFamily (cutoffLaw F ρ p) 3 (Metric.ball 0 r) M
        (translatedRemainder s a ρA lam x m Y V c X)) ∧
      ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r,
        interpolatedBirth s a ρA ρ lam x m p F Y (leftTranslate (bondSpread c X τ) V) =
          -∫ v in (0 : ℝ)..1, gibbsMean (cutoffLaw F ρ p) (translatedExponent s a ρA lam x m V c X v τ)
            (translatedRemainder s a ρA lam x m Y V c X τ) := by
  classical
  set Vt : (Fin k → ℝ) → F.GaugeField F.top := fun τ => leftTranslate (bondSpread c X τ) V with hVt
  set Sv := StepVariable (finiteCells F) with hSv
  obtain ⟨hfinμ, hμ0, hμb, hμm⟩ := hRim F ρ p hρ hcut
  set μ := cutoffLaw F ρ p with hμ
  have hμc : ∀ᵐ η ∂μ, ∀ b, ‖η b‖ ≤ ρ := by
    filter_upwards [hμb] with η hη b using (hη b).le
  set P0 : (Fin k → ℝ) × Sv → ℝ := fun z =>
    ∑ Y' ∈ finiteCells F, interpolatedBlockExponent s a ρA x m Y' (Vt z.1) z.2 with hP0
  set HY : (Fin k → ℝ) × Sv → ℝ := fun z => interpolatedBlockExponent s a ρA x m Y (Vt z.1) z.2 with hHY
  have sP0 : ∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 P0 (0, η) := fun η hη =>
    ContDiffAt.sum fun Y' _ => hSm Y' η k c X hη
  have sHY : ∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 HY (0, η) := fun η hη => hSm Y η k c X hη
  set π : (Fin k → ℝ) × (ℝ × Sv) → (Fin k → ℝ) × Sv := fun z => (z.1, z.2.2) with hπ
  have hπs : ContDiff ℝ 3 π := contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
  have hvs : ContDiff ℝ 3 fun z : (Fin k → ℝ) × (ℝ × Sv) => z.2.1 := contDiff_fst.comp contDiff_snd
  have hηs : ContDiff ℝ 3 fun z : (Fin k → ℝ) × (ℝ × Sv) => z.2.2 := contDiff_snd.comp contDiff_snd
  have lift : ∀ {G : (Fin k → ℝ) × Sv → ℝ}, (∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 G (0, η)) →
      ∀ (v : ℝ) (η : Sv), (∀ b, ‖η b‖ ≤ ρ) →
        ContDiffAt ℝ 3 (fun z : (Fin k → ℝ) × (ℝ × Sv) => G (π z)) (0, v, η) := fun {G} hG v η hη =>
    ContDiffAt.comp (g := G) (f := π) (0, v, η) (hG η hη) hπs.contDiffAt
  obtain ⟨r₁, M₁, hr₁, hD₁⟩ := hDom _ k ρ μ
    (fun z => z.2.1 * P0 (π z) + (1 - z.2.1) * totalQuadratic lam x z.2.2) hμc (fun v η _ hη =>
      (hvs.contDiffAt.mul (lift sP0 v η hη)).add ((contDiff_const.sub hvs).contDiffAt.mul
        ((contDiff_totalQuadratic lam x).comp hηs).contDiffAt))
  obtain ⟨r₂, M₂, hr₂, hD₂⟩ := hDom _ k ρ μ
    (fun z => HY (π z) - cellQuadratic lam x Y z.2.2) hμc (fun v η _ hη =>
      (lift sHY v η hη).sub ((contDiff_cellQuadratic lam x Y).comp hηs).contDiffAt)
  obtain ⟨r₀, hr₀, hcold⟩ :=
    Metric.eventually_nhds_iff_ball.mp (eventually_isSmallCurvature_translate hfin c X hV)
  set r : ℝ := min r₀ (min r₁ r₂) with hr
  have hrpos : 0 < r := lt_min hr₀ (lt_min hr₁ hr₂)
  have sub₀ : Metric.ball (0 : Fin k → ℝ) r ⊆ Metric.ball 0 r₀ := Metric.ball_subset_ball (min_le_left _ _)
  have sub₁ : Metric.ball (0 : Fin k → ℝ) r ⊆ Metric.ball 0 r₁ := Metric.ball_subset_ball
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have sub₂ : Metric.ball (0 : Fin k → ℝ) r ⊆ Metric.ball 0 r₂ := Metric.ball_subset_ball
    (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨r, max M₁ M₂, hrpos, fun v hv => IsDominatedSmoothFamily.mono sub₁ (le_max_left _ _) (hD₁ v hv),
    fun v hv => IsDominatedSmoothFamily.mono sub₂ (le_max_right _ _) (hD₂ v hv), fun τ hτ => ?_⟩
  show (-∫ v in (0 : ℝ)..1, cutoffMean ρ p (weightLawExponent s a ρA lam x m v (Vt τ))
    (cellExponentRemainder s a ρA lam x m Y (Vt τ))) = _
  congr 1
  apply intervalIntegral.integral_congr
  intro v _
  simp only
  rw [hμm]
  apply gibbsMean_congr_ae
  · filter_upwards [hμb] with η hη
    have := hSum (leftTranslate (bondSpread c X τ) V) (hcold τ (sub₀ hτ)) η hη
    simp only [weightLawExponent, translatedExponent, hVt, this]
  · exact Filter.EventuallyEq.rfl
theorem contDiffAt_interpolatedBirth_translate {s a ρA ρ lam x u : ℝ} {m k : ℕ} {p : ℝ → ℝ}
    {V : F.GaugeField F.top} (hρ : 0 < ρ)
    (hcut : IsCutoff ρ p) (hfin : Finite F.Cell) (hRim : CutoffMeanIsGibbsMean)
    (hDom : DominatedFamilyOnClosedBalls) (hMean : IntervalIntegralGibbsMeanDifferentiation)
    (hSum : ∀ V' : F.GaugeField F.top, IsSmallCurvature u V' → ∀ η : StepVariable (finiteCells F),
      (∀ b, ‖η b‖ < ρ) → interpolatedExponent s a ρA x m V' η =
        ∑ Y ∈ finiteCells F, interpolatedBlockExponent s a ρA x m Y V' η)
    (hSm : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
        interpolatedBlockExponent s a ρA x m Y (leftTranslate (bondSpread c X q.1) V) q.2) (0, η))
    (hV : IsSmallCurvature u V) (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ 3 (fun τ : Fin k → ℝ =>
      interpolatedBirth s a ρA ρ lam x m p F Y (leftTranslate (bondSpread c X τ) V)) 0 := by
  obtain ⟨r, M, hr, hA, hH, heq⟩ :=
    translated_dominated_and_eq (lam := lam) hρ hcut hfin hRim hDom hSum hSm hV Y c X
  obtain ⟨hfinμ, hμ0, -, -⟩ := hRim F ρ p hρ hcut
  have hB0 : Metric.ball (0 : Fin k → ℝ) r ∈ 𝓝 (0 : Fin k → ℝ) := Metric.ball_mem_nhds _ hr
  have hM := hMean _ (cutoffLaw F ρ p) k (Metric.ball 0 r) M (translatedExponent s a ρA lam x m V c X)
    (fun _ => translatedRemainder s a ρA lam x m Y V c X) Metric.isOpen_ball hμ0 hA hH
    (fun τ _ => Filter.Eventually.of_forall fun η =>
      ⟨Continuous.continuousOn (by simp only [translatedExponent]; fun_prop), continuousOn_const⟩)
  refine (hM.1.neg.contDiffAt hB0).congr_of_eventuallyEq ?_
  filter_upwards [hB0] with τ hτ using heq τ hτ
theorem bondDeriv_interpolatedBirth_le {s a ρA ρ lam x κ Kc u : ℝ} {m : ℕ} {p : ℝ → ℝ} {Cq : ℕ → ℝ}
    {V : F.GaugeField F.top} (hρ : 0 < ρ)
    (hcut : IsCutoff ρ p) (hfin : Finite F.Cell) (hK0 : 0 ≤ Kc) (hRim : CutoffMeanIsGibbsMean)
    (hDom : DominatedFamilyOnClosedBalls) (hMean : IntervalIntegralGibbsMeanDifferentiation)
    (hSub : IteratedDerivAlongSubfamily)
    (hSum : ∀ V' : F.GaugeField F.top, IsSmallCurvature u V' → ∀ η : StepVariable (finiteCells F),
      (∀ b, ‖η b‖ < ρ) → interpolatedExponent s a ρA x m V' η =
        ∑ Y ∈ finiteCells F, interpolatedBlockExponent s a ρA x m Y V' η)
    (hSm : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
        interpolatedBlockExponent s a ρA x m Y (leftTranslate (bondSpread c X q.1) V) q.2) (0, η))
    (hV : IsSmallCurvature u V)
    (hconv : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∃ (Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ)
      (K : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ),
      (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
        Ψ η = weightLawExponent s a ρA lam x m v V η) ∧
      IsUniformlyConvexDecaying ρ (x * lam / 4) κ (chordBondDist F) Ψ K ∧
      ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
        |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖)
    (hObs : ∀ (Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ)
      (K : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ) (Y : F.Cell),
      IsUniformlyConvexDecaying ρ (x * lam / 4) κ (chordBondDist F) Ψ K →
      (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
        |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖) →
      ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
        AreUnitVectors X →
        ExponentPartsSizes ρ lam x κ p Cq (interpolatedBlockExponent s a ρA x m) Ψ Y V c X)
    (hKc : ∀ (v : ℝ) (Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ)
      (K : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ) (Y : F.Cell) (k : ℕ)
      (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (A H : (Fin k → ℝ) → StepVariable (finiteCells F) → ℝ) (B : Set (Fin k → ℝ)) (M : ℝ),
      0 ≤ v → v ≤ 1 → k ≤ 3 →
      IsUniformlyConvexDecaying ρ (x * lam / 4) κ (chordBondDist F) Ψ K →
      (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
        |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖) →
      IsOpen B → (0 : Fin k → ℝ) ∈ B →
      IsDominatedSmoothFamily (cutoffLaw F ρ p) 3 B M A → IsDominatedSmoothFamily (cutoffLaw F ρ p) 3 B M H →
      PartFamily (interpolatedBlockExponent s a ρA x m) ρ lam x v Ψ Y V c X A H →
      (∀ (j : ℕ) (l : Fin j → Fin k), j ≤ 3 →
        ExponentPartsSizes ρ lam x κ p Cq (interpolatedBlockExponent s a ρA x m) Ψ Y V (c ∘ l) (X ∘ l)) →
      |iteratedFDeriv ℝ k (fun s => gibbsMean (cutoffLaw F ρ p) (A s) (H s)) 0 (fun l => Pi.single l 1)| ≤
        Kc * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)))
    (Y : F.Cell) {k : ℕ} (hk : k ≤ 3) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) :
    |bondDeriv (interpolatedBirth s a ρA ρ lam x m p F Y) V c X| ≤ Kc * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) ∧
      IntervalIntegrable (fun v => cutoffMean ρ p (weightLawExponent s a ρA lam x m v V)
        (cellExponentRemainder s a ρA lam x m Y V)) volume 0 1 := by
  classical
  set Sv := StepVariable (finiteCells F) with hSv
  obtain ⟨r, Mb, hr, hA, hH, heq⟩ :=
    translated_dominated_and_eq (lam := lam) hρ hcut hfin hRim hDom hSum hSm hV Y c X
  obtain ⟨hfinμ, hμ0, hμb, hμm⟩ := hRim F ρ p hρ hcut
  set μ := cutoffLaw F ρ p with hμ
  set B := Metric.ball (0 : Fin k → ℝ) r with hB
  have hBo : IsOpen B := Metric.isOpen_ball
  have hB0 : B ∈ 𝓝 (0 : Fin k → ℝ) := Metric.ball_mem_nhds _ hr
  have h0B : (0 : Fin k → ℝ) ∈ B := mem_of_mem_nhds hB0
  set A := translatedExponent s a ρA lam x m V c X with hAd
  set H := translatedRemainder s a ρA lam x m Y V c X with hHd
  have hM := hMean Sv μ k B Mb A (fun _ => H) hBo hμ0 hA hH
    (fun τ _ => Filter.Eventually.of_forall fun η =>
      ⟨Continuous.continuousOn (by simp only [hAd, translatedExponent]; fun_prop), continuousOn_const⟩)
  have hev : (fun τ => interpolatedBirth s a ρA ρ lam x m p F Y (leftTranslate (bondSpread c X τ) V)) =ᶠ[𝓝 0]
      -(fun τ => ∫ v in (0 : ℝ)..1, gibbsMean μ (A v τ) (H τ)) := by
    filter_upwards [hB0] with τ hτ using heq τ hτ
  have hder : bondDeriv (interpolatedBirth s a ρA ρ lam x m p F Y) V c X =
      -∫ v in (0 : ℝ)..1, iteratedFDeriv ℝ k (fun τ => gibbsMean μ (A v τ) (H τ)) 0
        (fun l => Pi.single l 1) := by
    unfold bondDeriv
    rw [(hev.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds, iteratedFDeriv_neg_apply,
      neg_apply, hM.2 0 h0B k hk]
  have e0 : leftTranslate (bondSpread c X (0 : Fin k → ℝ)) V = V := leftTranslate_bondSpread_zero c X V
  have hsum0 : ∀ η : Sv, (∀ b, ‖η b‖ < ρ) → ∀ v : ℝ, A v 0 η = weightLawExponent s a ρA lam x m v V η := by
    intro η hη v
    have := hSum V hV η hη
    simp only [hAd, translatedExponent, weightLawExponent, e0, this]
  refine ⟨?_, ?_⟩
  swap
  · have hc : ContinuousOn (fun v => gibbsMean μ (A v 0) (H 0)) (Set.Icc (0 : ℝ) 1) := by
      refine continuousOn_gibbsMean (K := Mb) hμ0 (fun v hv => (hA v hv).aestronglyMeasurable 0 h0B)
        (fun v hv => (hH v hv).aestronglyMeasurable 0 h0B) (fun v hv => ?_) (fun v hv => ?_)
        (Filter.Eventually.of_forall fun η => by simp only [hAd, translatedExponent]; fun_prop)
        (Filter.Eventually.of_forall fun η => continuousOn_const)
      · filter_upwards [(hA v hv).norm_iteratedFDeriv_le] with ω hω
        have := hω 0 (by norm_num) 0 h0B
        simpa using this
      · filter_upwards [(hH v hv).norm_iteratedFDeriv_le] with ω hω
        have := hω 0 (by norm_num) 0 h0B
        simpa using this
    have hc' : ContinuousOn (fun v => cutoffMean ρ p (weightLawExponent s a ρA lam x m v V)
        (cellExponentRemainder s a ρA lam x m Y V)) (Set.Icc (0 : ℝ) 1) := by
      refine hc.congr fun v _ => ?_
      simp only
      rw [hμm]
      apply gibbsMean_congr_ae
      · filter_upwards [hμb] with η hη
        exact (hsum0 η hη v).symm
      · refine Filter.Eventually.of_forall fun η => ?_
        simp only [hHd, translatedRemainder, cellExponentRemainder, e0]
    exact hc'.intervalIntegrable_of_Icc zero_le_one
  rw [hder, abs_neg]
  have sB : ∀ (Y' : F.Cell) (η : Sv), (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × Sv =>
        interpolatedBlockExponent s a ρA x m Y' (leftTranslate (bondSpread c X q.1) V) q.2) (0, η) :=
    fun Y' η hη => hSm Y' η k c X hη
  have hpoint : ∀ v ∈ Set.Icc (0 : ℝ) 1,
      |iteratedFDeriv ℝ k (fun τ => gibbsMean μ (A v τ) (H τ)) 0 (fun l => Pi.single l 1)| ≤
        Kc * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) := by
    intro v hv
    obtain ⟨Ψ, K, hagree, hcv, hslope⟩ := hconv v hv
    have hfam : PartFamily (interpolatedBlockExponent s a ρA x m) ρ lam x v Ψ Y V c X (A v) H := by
      refine ⟨fun η hη => ?_, fun j l hj η hη => ?_, fun j l hj η hη => ?_⟩
      · exact (hsum0 η hη v).trans (hagree η hη).symm
      · have hηc : ∀ b, ‖η b‖ ≤ ρ := fun b => (hη b).le
        have hφ : ∀ Y' ∈ finiteCells F, ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞)
            (fun τ => interpolatedBlockExponent s a ρA x m Y' (leftTranslate (bondSpread c X τ) V) η) 0 :=
          fun Y' _ => by
            have hp : ContDiffAt ℝ 3 (fun z : Fin k → ℝ => (z, η)) 0 := contDiffAt_id.prodMk contDiffAt_const
            have h5 := ContDiffAt.comp (0 : Fin k → ℝ) (sB Y' η hηc) hp
            exact h5.of_le (by norm_cast)
        have h1 := iteratedFDeriv_smul_sum_add_const (finiteCells F)
          (fun Y' τ => interpolatedBlockExponent s a ρA x m Y' (leftTranslate (bondSpread c X τ) V) η) v
          ((1 - v) * totalQuadratic lam x η) (n := j + 1) (by omega) hφ (fun i => Pi.single (l i) 1)
        show iteratedFDeriv ℝ (j + 1) (fun τ => v * ∑ Y' ∈ finiteCells F,
            interpolatedBlockExponent s a ρA x m Y' (leftTranslate (bondSpread c X τ) V) η +
              (1 - v) * totalQuadratic lam x η) 0 _ = _
        rw [h1]
        unfold exponentDerivSum
        congr 1
        refine Finset.sum_congr rfl fun Y' hY' => ?_
        exact hSub F F.top k (j + 1) (fun V' => interpolatedBlockExponent s a ρA x m Y' V' η) V c X l
          (hφ Y' hY')
      · have hηc : ∀ b, ‖η b‖ ≤ ρ := fun b => (hη b).le
        have hp : ContDiffAt ℝ 3 (fun z : Fin k → ℝ => (z, η)) 0 := contDiffAt_id.prodMk contDiffAt_const
        have h5 := ContDiffAt.comp (0 : Fin k → ℝ) (sB Y η hηc) hp
        have h6 : ContDiffAt ℝ (j : WithTop ℕ∞) (fun τ => interpolatedBlockExponent s a ρA x m Y
            (leftTranslate (bondSpread c X τ) V) η - cellQuadratic lam x Y η) 0 :=
          (h5.of_le (by norm_cast)).sub contDiffAt_const
        exact hSub F F.top k j
          (fun V' => interpolatedBlockExponent s a ρA x m Y V' η - cellQuadratic lam x Y η) V c X l h6
    exact hKc v Ψ K Y k c X (A v) H B Mb hv.1 hv.2 hk hcv hslope hBo h0B (hA v hv) (hH v hv) hfam
      (fun j l hj => hObs Ψ K Y hcv hslope j (c ∘ l) (X ∘ l) hj (fun i => hX (l i)))
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun v => iteratedFDeriv ℝ k (fun τ => gibbsMean μ (A v τ) (H τ)) 0 (fun l => Pi.single l 1))
    (C := Kc * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c))) (fun v hv => by
      rw [Set.uIoc_of_le zero_le_one] at hv
      exact hpoint v ⟨hv.1.le, hv.2⟩)
  simpa using hb
theorem extendByZero_id (ζ : StepVariable (finiteCells F)) :
    _root_.YangMills.Construction.Interpolation.extendByZero (id : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F))) Finset.univ ζ = ζ := by
  funext b
  unfold _root_.YangMills.Construction.Interpolation.extendByZero
  rw [Finset.sum_eq_single b]
  · simp
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ b) h
theorem interpolatedBirth_congr {s a ρA ρ lam x : ℝ} {m : ℕ} {p : ℝ → ℝ} {Y Y' : F.Cell}
    {V V' : F.GaugeField F.top}
    (h : ∀ τ : ℝ, cutoffMean ρ p (weightLawExponent s a ρA lam x m τ V')
        (cellExponentRemainder s a ρA lam x m Y' V') =
      cutoffMean ρ p (weightLawExponent s a ρA lam x m τ V) (cellExponentRemainder s a ρA lam x m Y V)) :
    interpolatedBirth s a ρA ρ lam x m p F Y' V' = interpolatedBirth s a ρA ρ lam x m p F Y V := by
  unfold interpolatedBirth
  exact congrArg Neg.neg (intervalIntegral.integral_congr fun τ _ => h τ)
theorem exists_convex_potential_of_weight {T : StepParameters} {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ} {t : ℕ}
    {x s : ℝ} (fr : InterpolatedFrameBoundsAt T Cq Cz Cr t x) (hs : 0 ≤ s) (hs1 : s ≤ 1) (F : BlockFrame)
    (hF : IsCubicTopTorus T.L t T.n₀ F) (V : F.GaugeField F.top)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ)
      (K : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ),
      (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        Ψ η = weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) v V η) ∧
      IsUniformlyConvexDecaying T.ballRadius (x * T.chainParams.lam / 4) T.κ (chordBondDist F) Ψ K ∧
      ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
        |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * T.chainParams.lam / 4) * ‖e‖ := by
  let M : Fin 1 → LawOnBondVariables ↥(chordBonds (finiteCells F)) := fun _ =>
    ⟨F, V, id, Finset.univ, weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) v V⟩
  have hw : IsConvexWeights (fun _ : Fin 1 => (1 : ℝ)) := ⟨fun _ => zero_le_one, by simp⟩
  have hadm : ∀ l, (M l).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E
      T.energyRatio T.L t T.n₀ (frameRadius x) (chordBondDist F) := fun _ =>
    ⟨hF, hV, .ofWeight s v hs hs1 hv.1 hv.2, Function.injective_id, fun _ _ => rfl⟩
  obtain ⟨Ψ, K, hag, hc', hsl, -⟩ := (fr.laws _ (chordBondDist F) 1 _ M hw hadm).1
  refine ⟨Ψ, K, fun η hη => ?_, hc', hsl⟩
  rw [hag η hη]
  show ∑ _l : Fin 1, (1 : ℝ) * (weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) v V
      (_root_.YangMills.Construction.Interpolation.extendByZero id Finset.univ η) + ∑ i ∈ Finset.univ \ Finset.univ,
        x * T.chainParams.lam / 2 * ‖η i‖ ^ 2) = _
  rw [extendByZero_id]
  simp
def BirthBoundsOnTorus (T : StepParameters) (t : ℕ) (x s Kc : ℝ) : Prop :=
  ∀ F, IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
    IsSmallCurvature (5 / 4 * T.σ) V →
    ContDiffThreeAlongBonds (interpolatedBirthAt T x s F Y) V ∧
    (∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
      AreUnitVectors X →
      |bondDeriv (interpolatedBirthAt T x s F Y) V c' X| ≤ Kc * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c'))) ∧
    IntervalIntegrable (fun τ => cutoffMean T.ballRadius T.p
      (weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) τ V)
      (cellExponentRemainder s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) Y V))
      MeasureTheory.volume 0 1
theorem birthBoundsOnTorus {T : StepParameters} {t : ℕ} {x s c Kc : ℝ} {Cq : ℕ → ℝ}
    (hRim : CutoffMeanIsGibbsMean)
    (hDom : DominatedFamilyOnClosedBalls) (hMean : IntervalIntegralGibbsMeanDifferentiation)
    (hSub : IteratedDerivAlongSubfamily) (hFew : cellBondsCardStatement) (hL : Odd T.L)
    (hn₂ : 2 ≤ T.n₀) (hρ : 0 < T.ballRadius) (hcut : IsCutoff T.ballRadius T.p) (hx1 : 1 ≤ x) (hK0 : 0 ≤ Kc)
    (hO : ExponentPartsConstants T.L T.κ T.chainParams.lam c Cq)
    (hK : PartMeanDerivBound (4 * T.L ^ 4) T.κ T.chainParams.lam Cq Kc)
    (hps : ∀ (F : BlockFrame) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V →
      InterpolatedPartsSmooth s T.a T.chainParams.ρA T.ballRadius x (frameRadius x) V)
    (hbd : ∀ (F : BlockFrame) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V →
      InterpolatedExponentBounds s T.a T.chainParams.ρA T.ballRadius x T.κ c (frameRadius x) V)
    (hlaw : ∀ (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F → ∀ V : F.GaugeField F.top,
      IsSmallCurvature (5 / 4 * T.σ) V →
      ∀ v ∈ Set.Icc (0 : ℝ) 1, ∃ (Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ)
        (K : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ),
        (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
          Ψ η = weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) v V η) ∧
        IsUniformlyConvexDecaying T.ballRadius (x * T.chainParams.lam / 4) T.κ (chordBondDist F) Ψ K ∧
        ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
          |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * T.chainParams.lam / 4) * ‖e‖) :
    BirthBoundsOnTorus T t x s Kc := by
  intro F hF Y V hV
  have hx0 : 0 < x := by linarith
  have hFside : ∀ i, 2 ≤ F.extent i := by
    obtain ⟨-, -, n, hside, hn⟩ := hF
    intro i
    rw [hside]
    exact le_trans hn₂ hn
  have hfin : Finite F.Cell := by
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      have := hFside i
      rw [hper]
      omega⟩
    exact Pi.finite
  have hFL : F.blockSide = T.L := hF.1
  have hfew : ∀ z : F.Cell,
      (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤
        4 * T.L ^ 4 := by
    intro z
    rw [← hFL]
    exact hFew F (hFL ▸ hL) hFside z
  have hsum : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
      ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        interpolatedExponent s T.a T.chainParams.ρA x (frameRadius x) V' η =
          ∑ Y ∈ finiteCells F, interpolatedBlockExponent s T.a T.chainParams.ρA x (frameRadius x) Y V' η :=
    fun V' hV' η hη => (hps F V' hF hV').sum_eq η hη
  have hB : ExponentPartsBounds T.ballRadius x T.κ c
      (interpolatedBlockExponent s T.a T.chainParams.ρA x (frameRadius x)) V :=
    ⟨(hbd F V hF hV).deriv_top, (hbd F V hF hV).deriv_top_partial⟩
  have hs3 := (hps F V hF hV).smooth
  have hs4 : ∀ (Y' : F.Cell) (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (η : StepVariable (finiteCells F)), k ≤ 3 → (∀ b, ‖η b‖ ≤ T.ballRadius) →
      ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
        interpolatedBlockExponent s T.a T.chainParams.ρA x (frameRadius x) Y'
          (leftTranslate (bondSpread c' X q.1) V) q.2) (0, η) := by
    intro Y' k c' X η hk hη
    rcases Nat.lt_or_ge k 3 with h | h
    · exact (hs3 Y' η k c' X hη).of_le (by norm_cast)
    · obtain rfl : k = 3 := le_antisymm hk h
      exact (hps F V hF hV).third_deriv Y' c' X η hη
  have hsz : ∀ (Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ)
      (K : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ) (Y' : F.Cell),
      IsUniformlyConvexDecaying T.ballRadius (x * T.chainParams.lam / 4) T.κ (chordBondDist F) Ψ K →
      (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
        |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * T.chainParams.lam / 4) * ‖e‖) →
      ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
        AreUnitVectors X →
        ExponentPartsSizes T.ballRadius T.chainParams.lam x T.κ T.p Cq
          (interpolatedBlockExponent s T.a T.chainParams.ρA x (frameRadius x)) Ψ Y' V c' X :=
    fun Ψ K Y' hc' hsl k c' X hk hX =>
      hO F T.ballRadius x T.p _ V Ψ K Y' hFL hFside hρ hx1 hcut hB hs4 hc' hsl k c' X hk hX
  have hAt := fun {k : ℕ} (hk : k ≤ 3) (c' : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (hX : AreUnitVectors X) =>
    bondDeriv_interpolatedBirth_le (s := s) (a := T.a) (ρA := T.chainParams.ρA) (lam := T.chainParams.lam)
      (x := x) (κ := T.κ) (u := 5 / 4 * T.σ) (m := frameRadius x) (Cq := Cq) (V := V) hρ hcut hfin hK0
      hRim hDom hMean hSub hsum hs3 hV (hlaw F hF V hV) hsz
      (fun v Ψ K Y' k c' X A H B M hv0 hv1 hk hc' hsl hBo hB0 hdA hdH hfam hsz' =>
        hK F T.ballRadius x v T.p _ V Ψ K Y' k c' X A H B M hρ hx0 hcut hv0 hv1 hk hfew hc' hsl hBo hB0
          hdA hdH hfam hsz') Y hk c' X hX
  refine ⟨fun k c' X => ?_, fun k c' X hk hX => (hAt hk c' X hX).1, ?_⟩
  · exact contDiffAt_interpolatedBirth_translate (lam := T.chainParams.lam) (u := 5 / 4 * T.σ) hρ hcut hfin
      hRim hDom hMean hsum hs3 hV Y c' X
  · exact (hAt (k := 0) (by norm_num) Fin.elim0 Fin.elim0 (fun l => l.elim0)).2
theorem isLocalOnTori_interpolatedBirthAt {T : StepParameters} {t : ℕ} {x s c₂ Kc Ct : ℝ}
    (hLines : SmallCurvatureAlongLineAndAgreeOn)
    (hTw : ∀ (F F' : BlockFrame) (G : F.GaugeField F.top → ℝ) (G' : F'.GaugeField F'.top → ℝ)
      (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (c' : Fin k → F'.Site F'.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ₀ M₀ M₃ : ℝ),
      1 ≤ k → k ≤ 2 → 0 < τ₀ → 0 < M₀ → 0 ≤ M₃ →
      (∀ ς : Fin k → ℝ, (∀ l, ς l = 1 ∨ ς l = -1) →
        IsControlledAlongLine G V c (fun l => ς l • X l) τ₀ M₃ ∧
        IsControlledAlongLine G' V' c' (fun l => ς l • X l) τ₀ M₃ ∧
        ∀ s : ℝ, |s| ≤ τ₀ → |G (alongLine c (fun l => ς l • X l) s V) -
          G' (alongLine c' (fun l => ς l • X l) s V')| ≤ M₀) →
      |bondDeriv G V c X - bondDeriv G' V' c' X| ≤
        Ct * (M₀ / τ₀ ^ k + M₀ ^ (1 - (k : ℝ) / 3) * M₃ ^ ((k : ℝ) / 3)))
    (hCt : 0 < Ct) (hκ : 0 < T.κ) (hσ : 0 < T.σ) (hc0 : 0 < c₂) (hK0 : 0 ≤ Kc) (hKc₂ : Kc ≤ c₂)
    (hG' : c₂ * (1 + Ct * (1 + 1 / (T.σ / 64) + (1 / (T.σ / 64)) ^ 2)) ≤ T.Cs)
    (hone : BirthBoundsOnTorus T t x s Kc)
    (hmean : ∀ (τ : ℝ) (F F' : BlockFrame) (W : F.GaugeField F.top) (W' : F'.GaugeField F'.top) (Y : F.Cell)
      (Y' : F'.Cell) (r : ℕ),
      0 ≤ τ → τ ≤ 1 → IsCubicTopTorus T.L t T.n₀ F → IsCubicTopTorus T.L t T.n₀ F' →
      IsSmallCurvature (5 / 4 * T.σ) W → IsSmallCurvature (5 / 4 * T.σ) W' →
      AgreeOnBall (finiteCells F) W (finiteCells F') W' Y Y' r →
      |cutoffMean T.ballRadius T.p (weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) τ W')
          (cellExponentRemainder s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) Y' W') -
        cutoffMean T.ballRadius T.p
          (weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) τ W)
          (cellExponentRemainder s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) Y W)| ≤
        c₂ * Real.exp (-(T.κ * r / 2 ^ 7))) :
    IsLocalOnTori T.L t T.n₀ (9 / 8 * T.σ) (interpolatedBirthAt T x s)
      fun r => T.Cs * Real.exp (-(T.κ / 2 ^ 9 * r)) := by
  have hτ : 0 < T.σ / 64 := by positivity
  have hcC : c₂ ≤ T.Cs := by
    refine le_trans ?_ hG'
    have : 0 ≤ c₂ * (Ct * (1 + 1 / (T.σ / 64) + (1 / (T.σ / 64)) ^ 2)) := by positivity
    nlinarith
  have hmono : ∀ {j : ℕ} {F : BlockFrame} {W : F.GaugeField j}, IsSmallCurvature (9 / 8 * T.σ) W →
      IsSmallCurvature (5 / 4 * T.σ) W := fun h p hp => (h p hp).trans_le (by nlinarith)
  intro F F' hF hF' Y Y' V V' r k h X hV hV' hag hk hbox hX
  have hval : ∀ (W : F.GaugeField F.top) (W' : F'.GaugeField F'.top), IsSmallCurvature (5 / 4 * T.σ) W →
      IsSmallCurvature (5 / 4 * T.σ) W' → AgreeOnBall (finiteCells F) W (finiteCells F') W' Y Y' r →
      |interpolatedBirthAt T x s F Y W - interpolatedBirthAt T x s F' Y' W'| ≤
        c₂ * Real.exp (-(T.κ * r / 2 ^ 7)) := by
    intro W W' hW hW' hagW
    have hI := (hone F hF Y W hW).2.2
    have hI' := (hone F' hF' Y' W' hW').2.2
    have e : interpolatedBirthAt T x s F Y W - interpolatedBirthAt T x s F' Y' W' =
        ∫ v in (0 : ℝ)..1, (cutoffMean T.ballRadius T.p
            (weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) v W')
            (cellExponentRemainder s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) Y' W') -
          cutoffMean T.ballRadius T.p
            (weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) v W)
            (cellExponentRemainder s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) Y W)) := by
      rw [intervalIntegral.integral_sub hI' hI]
      show (-∫ v in (0 : ℝ)..1, _) - (-∫ v in (0 : ℝ)..1, _) = _
      ring
    rw [e]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := c₂ * Real.exp (-(T.κ * r / 2 ^ 7)))
      (f := fun v => cutoffMean T.ballRadius T.p
          (weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) v W')
          (cellExponentRemainder s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) Y' W') -
        cutoffMean T.ballRadius T.p
          (weightLawExponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) v W)
          (cellExponentRemainder s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) Y W))
      (fun v hv => by
        rw [Set.uIoc_of_le zero_le_one] at hv
        rw [Real.norm_eq_abs]
        exact hmean v F F' W W' Y Y' r hv.1.le hv.2 hF hF' hW hW' hagW)
    simpa using hb
  set E₁ := Real.exp (-(T.κ / 2 ^ 9 * r)) with hE₁
  have hE₁0 : 0 < E₁ := Real.exp_pos _
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [bondDeriv_zero, bondDeriv_zero]
    refine (hval V V' (hmono hV) (hmono hV') hag).trans ?_
    have hE : Real.exp (-(T.κ * r / 2 ^ 7)) ≤ E₁ := by
      apply Real.exp_le_exp.mpr
      have e : T.κ / 2 ^ 9 * r = T.κ * r / 2 ^ 9 := by ring
      have hr : 0 ≤ T.κ * r := by positivity
      rw [e]
      nlinarith
    exact mul_le_mul hcC hE (Real.exp_pos _).le (by linarith)
  · have hk2 : k ≤ 2 := hk
    have hM₀ : 0 < c₂ * Real.exp (-(T.κ * r / 2 ^ 7)) := by positivity
    have hmove : ∀ (ς : Fin k → ℝ), (∀ l, ς l = 1 ∨ ς l = -1) → ∀ l, ‖ς l • X l‖ = 1 := by
      intro ς hς l
      rw [norm_smul, hX l, mul_one]
      rcases hς l with h1 | h1 <;> simp [h1]
    have hline : ∀ {F₁ : BlockFrame} (V₁ : F₁.GaugeField F₁.top) (c₁ : Fin k → F₁.Site F₁.top × Fin 4)
        (X₁ : Fin k → imaginaryQuaternions) (u : ℝ),
        (∀ l, ‖X₁ l‖ = 1) → |u| ≤ T.σ / 64 → IsSmallCurvature (9 / 8 * T.σ) V₁ →
        IsSmallCurvature (5 / 4 * T.σ) (alongLine c₁ X₁ u V₁) := by
      intro F₁ V₁ c₁ X₁ u hu hs' hV₁ p hp
      have h1 := hLines.1 F₁ V₁ k c₁ X₁ u (9 / 8 * T.σ) (fun l => (hu l).le) hV₁ p hp
      refine h1.trans_le ?_
      have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
      nlinarith
    have hread : ∀ (F₁ : BlockFrame), IsCubicTopTorus T.L t T.n₀ F₁ → ∀ (Y₁ : F₁.Cell)
        (V₁ : F₁.GaugeField F₁.top) (c₁ : Fin k → F₁.Site F₁.top × Fin 4) (X₁ : Fin k → imaginaryQuaternions),
        (∀ l, ‖X₁ l‖ = 1) → IsSmallCurvature (9 / 8 * T.σ) V₁ →
        IsControlledAlongLine (interpolatedBirthAt T x s F₁ Y₁) V₁ c₁ X₁ (T.σ / 64) c₂ := by
      intro F₁ hF₁ Y₁ V₁ c₁ X₁ hu hV₁
      refine ⟨fun u hs' => (hone F₁ hF₁ Y₁ _ (hline V₁ c₁ X₁ u hu hs' hV₁)).1, fun u hs' e => ?_⟩
      have h1 := (hone F₁ hF₁ Y₁ _ (hline V₁ c₁ X₁ u hu hs' hV₁)).2.1 3 (c₁ ∘ e) (X₁ ∘ e) le_rfl
        (fun l => hu (e l))
      refine h1.trans ?_
      have he : Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y₁ (c₁ ∘ e))) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have : 0 ≤ T.κ / 2 ^ 6 * bondSpan Y₁ (c₁ ∘ e) := by positivity
        linarith
      calc Kc * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y₁ (c₁ ∘ e))) ≤ Kc * 1 :=
          mul_le_mul_of_nonneg_left he hK0
        _ ≤ c₂ := by linarith
    have h1 := hTw F F' (interpolatedBirthAt T x s F Y) (interpolatedBirthAt T x s F' Y') V V' k
      (bondsAt Y h) (bondsAt Y' h) X
      (T.σ / 64) (c₂ * Real.exp (-(T.κ * r / 2 ^ 7))) c₂ hk0 hk2 hτ hM₀ hc0.le (fun ς hς =>
        ⟨hread F hF Y V _ _ (hmove ς hς) hV, hread F' hF' Y' V' _ _ (hmove ς hς) hV', fun u hu =>
          hval _ _ (hline V _ _ u (hmove ς hς) hu hV) (hline V' _ _ u (hmove ς hς) hu hV')
            (hLines.2 F F' V V' Y Y' r k h _ u hag hbox)⟩)
    refine h1.trans ?_
    have h2 := interpolation_sum_le (r := r) hκ hc0 hτ hk0 hk2
    calc Ct * (c₂ * Real.exp (-(T.κ * r / 2 ^ 7)) / (T.σ / 64) ^ k +
          (c₂ * Real.exp (-(T.κ * r / 2 ^ 7))) ^ (1 - (k : ℝ) / 3) * c₂ ^ ((k : ℝ) / 3))
        ≤ Ct * (c₂ * (1 + 1 / (T.σ / 64) + (1 / (T.σ / 64)) ^ 2) * E₁) :=
          mul_le_mul_of_nonneg_left h2 hCt.le
      _ ≤ c₂ * (1 + Ct * (1 + 1 / (T.σ / 64) + (1 / (T.σ / 64)) ^ 2)) * E₁ := by
          have : 0 ≤ c₂ * E₁ := by positivity
          nlinarith
      _ ≤ T.Cs * E₁ := mul_le_mul_of_nonneg_right hG' hE₁0.le
theorem interpolatedBirthBoundsStatement_holds (hJ : EventuallyInParametersCombines)
    (hDrawn : joinAtLoweredSmallnessConstantStatement)
    (hFr : interpolatedFramesStatement) (hParts : interpolatedPartsSmoothStatement)
    (hFz : remainderExpectationDecouples) (hInv : remainderMeansInvariant)
    (hObs : exponentPartsSizes) (hBlk : partMeanDerivBoundStatement)
    (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedFamilyOnClosedBalls)
    (hMean : IntervalIntegralGibbsMeanDifferentiation) (hSub : IteratedDerivAlongSubfamily)
    (hFew : cellBondsCardStatement) (hTwo : DerivDiffLeOfCloseAlongLines)
    (hLines : SmallCurvatureAlongLineAndAgreeOn) : interpolatedBirthBoundsStatement := by
  obtain ⟨join, -⟩ := hJ
  obtain ⟨Cq₀, Cz₀, Cr₀, hFr⟩ := hFr
  obtain ⟨Ct, hCt, hTw⟩ := hTwo
  have h2 : EventuallyInParameters fun T => 2 ≤ T.n₀ := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨2, fun _ h => ⟨0, fun _ _ => ⟨0, fun _ _ => h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have key : ∀ (T' : StepParameters) (c : ℝ), ∃ Kc : ℝ, Odd T'.L → 0 < T'.κ → 0 < T'.chainParams.lam →
      0 ≤ c → ∃ Cq : ℕ → ℝ, ExponentPartsConstants T'.L T'.κ T'.chainParams.lam c Cq ∧ 0 ≤ Kc ∧
        PartMeanDerivBound (4 * T'.L ^ 4) T'.κ T'.chainParams.lam Cq Kc := by
    intro T' c
    by_cases hc : Odd T'.L ∧ 0 < T'.κ ∧ 0 < T'.chainParams.lam ∧ 0 ≤ c
    · obtain ⟨h1, h2, h3, h4⟩ := hc
      obtain ⟨Cq, hCq, hO⟩ := hObs T'.L T'.κ T'.chainParams.lam c h1 h2 h3 h4
      obtain ⟨Kc, hK0, hK⟩ := hBlk (4 * T'.L ^ 4) T'.κ T'.chainParams.lam Cq h2 h3 hCq
      exact ⟨Kc, fun _ _ _ _ => ⟨Cq, hO, hK0, hK⟩⟩
    · exact ⟨0, fun a b c d => absurd ⟨a, b, c, d⟩ hc⟩
  choose Gk hGk using key
  refine hDrawn (fun T => 2 ≤ T.n₀ ∧ ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x →
      InterpolatedFrameBoundsAt T (Cq₀ (momentParameters T)) (Cz₀ (momentParameters T))
        (Cr₀ (momentParameters T)) t x)
    (fun T => RemainderExpectationDecouples T ∧ InterpolatedPartsSmoothAt T ∧ remainderMeansInvariantAt T) _
    (fun T c => max c (Gk T c) * (1 + Ct * (1 + 1 / (T.σ / 64) + (1 / (T.σ / 64)) ^ 2)))
    (join _ _ h2 hFr) (join _ _ hFz (join _ _ hParts hInv))
    fun T c hc hL hn₁ hy hE hη hη' hκ hσ hchain hcut hG hP hR => ?_
  obtain ⟨hn₂, hfr⟩ := hP
  obtain ⟨hfz, hps, hinv⟩ := hR
  have hlam : 0 < T.chainParams.lam := hchain.positivity.2.2.1
  obtain ⟨Cq, hO, hK0, hK⟩ := hGk { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 } c hL hκ hlam
    (by linarith)
  set Kc := Gk { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 } c with hKc
  have hG' : max c Kc * (1 + Ct * (1 + 1 / (T.σ / 64) + (1 / (T.σ / 64)) ^ 2)) ≤ T.Cs := hG
  have hcc : c ≤ max c Kc := le_max_left _ _
  have hKc₂ : Kc ≤ max c Kc := le_max_right _ _
  have hc0 : 0 < max c Kc := by linarith
  have hτ : 0 < T.σ / 64 := by positivity
  have hJ0 : 0 ≤ 1 + 1 / (T.σ / 64) + (1 / (T.σ / 64)) ^ 2 := by positivity
  have hcC : max c Kc ≤ T.Cs := by
    refine le_trans ?_ hG'
    have : 0 ≤ max c Kc * (Ct * (1 + 1 / (T.σ / 64) + (1 / (T.σ / 64)) ^ 2)) := by positivity
    nlinarith
  have hρ : 0 < T.ballRadius := hτ
  intro t x s hx hs hs1
  have hx1 : 1 ≤ x := hy.trans hx
  have fr := hfr t x hx
  have hone : BirthBoundsOnTorus T t x s Kc :=
    birthBoundsOnTorus (c := c) (Cq := Cq) hRim hDom hMean hSub hFew hL hn₂ hρ hcut hx1 hK0 hO hK
      (fun F V hF hV => hps t x F V s hx hF hV hs hs1)
      (fun F V hF hV => (fr.one_torus F V s hF hV hs hs1).exponent)
      (fun F hF V hV v hv => exists_convex_potential_of_weight fr hs hs1 F hF V hV v hv)
  have hspan0 : ∀ {F : BlockFrame} (Y : F.Cell),
      bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) = 0 := by
    intro F Y
    simp [bondSpan]
  have hsize : ∀ F, IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
      IsSmallCurvature (5 / 4 * T.σ) V → |interpolatedBirthAt T x s F Y V| ≤ Kc := by
    intro F hF Y V hV
    have h1 := (hone F hF Y V hV).2.1 0 Fin.elim0 Fin.elim0 (by norm_num) (fun l => l.elim0)
    rw [bondDeriv_zero, hspan0] at h1
    simpa using h1
  refine ⟨fun F hF Y V hV => (hone F hF Y V hV).2.2, ⟨fun F hF Y V hV => (hone F hF Y V hV).1,
    fun F hF Y V γ hV => interpolatedBirth_congr fun τ => (hinv t x s τ F V hx hs hs1 hF hV).1 Y γ,
    fun F hF Y h V hV => interpolatedBirth_congr fun τ => (hinv t x s τ F V hx hs hs1 hF hV).2 Y h⟩,
    fun F hF Y V hV => (hsize F hF Y V hV).trans (hKc₂.trans hcC), ?_, ?_⟩
  · intro F hF Y V k c' X hV h1 h3 hX
    exact ((hone F hF Y V hV).2.1 k c' X h3 hX).trans
      (mul_le_mul_of_nonneg_right (hKc₂.trans hcC) (Real.exp_pos _).le)
  · refine isLocalOnTori_interpolatedBirthAt hLines hTw hCt hκ hσ hc0 hK0 hKc₂ hG' hone
      fun τ F F' W W' Y Y' r h0 h1 hF hF' hW hW' hag => ?_
    have h3 := hfz t x s τ F F' W W' Y Y' r hx hs hs1 h0 h1 hF hF' hW hW' hag
    rw [abs_sub_comm, cutoffMean_eq_ballExpectation (fun _ _ => rfl),
      cutoffMean_eq_ballExpectation (fun _ _ => rfl)]
    exact h3.trans (mul_le_mul_of_nonneg_right hcc (Real.exp_pos _).le)
end YangMills.Construction.InterpolatedBirths
end
