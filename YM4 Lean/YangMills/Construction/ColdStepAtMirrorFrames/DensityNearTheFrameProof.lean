import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrame
import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExponentsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.DensityNearTheFrame
import YangMills.Construction.ColdStepAtMirrorFrames.MeanAlongAParameterProof
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOnOneTorus
import YangMills.Construction.SummableBoundsOfTheFlow.TheBirthsBetweenProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreNearTheirLimitsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
namespace YangMills.Construction
open BlockAverages BlockMeans FamilyNorms Estimates
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace StepDensityNearFrame
private theorem leftTranslate_bondSpread_zero {j k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField j) :
    leftTranslate (bondSpread c X 0) V = V := by apply _root_.YangMills.SharedProofs.p1939 <;> assumption
private theorem plaquetteDefect_continuous {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top) (p : F.Site F.top × Fin 4 × Fin 4) :
    Continuous fun τ : Fin k → ℝ => plaquetteDefect (leftTranslate (bondSpread c X τ) V) p := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.continuous_plaquetteDefect <;> assumption
private theorem eventually_smallCurvature_leftTranslate (hfin : Finite F.Cell) {s : ℝ} {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature s V) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0, IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by
  have hf : Finite (F.Site F.top × Fin 4 × Fin 4) := inferInstance
  exact show ∀ᶠ τ : Fin k → ℝ in 𝓝 0, ∀ p : F.Site F.top × Fin 4 × Fin 4, p.2.1 < p.2.2 →
      plaquetteDefect (leftTranslate (bondSpread c X τ) V) p < s from by
    rw [Filter.eventually_all]
    intro p
    by_cases hp : p.2.1 < p.2.2
    · have h2 : plaquetteDefect (leftTranslate (bondSpread c X (0 : Fin k → ℝ)) V) p < s := by
        rw [leftTranslate_bondSpread_zero]
        exact hV p hp
      filter_upwards [(plaquetteDefect_continuous c X V p).continuousAt.eventually_lt continuousAt_const h2]
        with τ hτ _ using hτ
    · exact Filter.Eventually.of_forall fun τ h => absurd h hp
abbrev _root_.YangMills.SharedProofs.p38544 := @eventually_smallCurvature_leftTranslate
private theorem IsDominatedSmoothFamily.mono_local {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ}
    {B B' : Set (Fin k → ℝ)} {K K' : ℝ} {G : (Fin k → ℝ) → Ω → ℝ} (hB : B' ⊆ B) (hK : K ≤ K')
    (h : IsDominatedSmoothFamily μ 3 B K G) : IsDominatedSmoothFamily μ 3 B' K' G := by apply _root_.YangMills.Construction.InterpolatedBirths.IsDominatedSmoothFamily.mono <;> assumption
private theorem gibbsMean_congr_ae {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {A A' H H' : Ω → ℝ}
    (hA : A =ᵐ[μ] A') (hH : H =ᵐ[μ] H') : gibbsMean μ A H = gibbsMean μ A' H' := by apply _root_.YangMills.Construction.InterpolatedBirths.gibbsMean_congr_ae <;> assumption
private theorem integrable_exp_neg {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {A : Ω → ℝ} {R : ℝ} (hAm : AEStronglyMeasurable A μ) (hAb : ∀ᵐ ω ∂μ, |A ω| ≤ R) :
    Integrable (fun ω => Real.exp (- A ω)) μ := by
  refine Integrable.of_bound (Real.continuous_exp.comp_aestronglyMeasurable hAm.neg) (Real.exp R) ?_
  filter_upwards [hAb] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hω).1])
abbrev _root_.YangMills.SharedProofs.p11234 := @integrable_exp_neg
private theorem integral_exp_neg_pos {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} (hμ : μ ≠ 0) {A : Ω → ℝ}
    (hint : Integrable (fun ω => Real.exp (- A ω)) μ) : 0 < ∫ ω, Real.exp (- A ω) ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun ω => (Real.exp_pos _).le) hint]
  have : Function.support (fun ω => Real.exp (- A ω)) = Set.univ := by
    ext ω
    simp [(Real.exp_pos _).ne']
  rw [this]
  exact Measure.measure_univ_pos.mpr hμ
abbrev _root_.YangMills.SharedProofs.p23099 := @integral_exp_neg_pos
private theorem gibbsMean_add_const {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) {A H : Ω → ℝ} {R : ℝ} (c : ℝ) (hAm : AEStronglyMeasurable A μ)
    (hHm : AEStronglyMeasurable H μ) (hAb : ∀ᵐ ω ∂μ, |A ω| ≤ R) (hHb : ∀ᵐ ω ∂μ, |H ω| ≤ R) :
    gibbsMean μ A (fun ω => H ω + c) = gibbsMean μ A H + c := by
  have hint := integrable_exp_neg hAm hAb
  have hpos := integral_exp_neg_pos hμ hint
  have hHint : Integrable (fun ω => H ω * Real.exp (- A ω)) μ := by
    refine Integrable.mono' (hint.const_mul |R|) (hHm.mul hint.aestronglyMeasurable) ?_
    filter_upwards [hHb] with ω hω
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (le_trans hω (le_abs_self R)) (Real.exp_pos _).le
  unfold gibbsMean
  have hsplit : ∫ ω, (H ω + c) * Real.exp (- A ω) ∂μ =
      (∫ ω, H ω * Real.exp (- A ω) ∂μ) + c * ∫ ω, Real.exp (- A ω) ∂μ := by
    rw [← integral_const_mul, ← integral_add hHint (hint.const_mul c)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only; ring)
  rw [hsplit, add_div, mul_div_assoc, div_self hpos.ne', mul_one]
private theorem gibbsMean_continuousOn {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) {A H : ℝ → Ω → ℝ} {R : ℝ}
    (hAm : ∀ v ∈ Set.Icc (0 : ℝ) 1, AEStronglyMeasurable (A v) μ)
    (hHm : ∀ v ∈ Set.Icc (0 : ℝ) 1, AEStronglyMeasurable (H v) μ)
    (hAb : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ ω ∂μ, |A v ω| ≤ R)
    (hHb : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ ω ∂μ, |H v ω| ≤ R)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun v => A v ω) (Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn (fun v => H v ω) (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun v => gibbsMean μ (A v) (H v)) (Set.Icc (0 : ℝ) 1) := by apply _root_.YangMills.SharedProofs.p92269 <;> assumption
private theorem abs_le_of_dominated {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ}
    {G : (Fin k → ℝ) → Ω → ℝ} {B : Set (Fin k → ℝ)} {K : ℝ} {τ : Fin k → ℝ}
    (hG : IsDominatedSmoothFamily μ 3 B K G) (hτ : τ ∈ B) : ∀ᵐ ω ∂μ, |G τ ω| ≤ K := by
  filter_upwards [hG.norm_iteratedFDeriv_le] with ω hω
  have h0 := hω 0 (Nat.zero_le _) τ hτ
  rwa [norm_iteratedFDeriv_zero] at h0
private theorem stepExponent_eq_sub (a ρA x : ℝ) (m : ℕ) (f : LocalFamily) (ν : ℝ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    stepExponent false a ρA x m f ν V η = stepExponent false a ρA x m (fun _ _ _ => 0) 0 V η -
      ν * ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false a ρA m f y η V := by
  simp [stepExponent]
private theorem stepExponent_smul_one (a ρA x : ℝ) (m : ℕ) (f : LocalFamily) (ν : ℝ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    stepExponent false a ρA x m (ν • f) 1 V η = stepExponent false a ρA x m f ν V η := by
  have hrow : ∀ y, centredExpansion false a ρA m (ν • f) y η V = ν * centredExpansion false a ρA m f y η V := fun y => by
    simp [centredExpansion, subtractTrivial, mul_sub]
  simp only [stepExponent, hrow, one_mul, ← Finset.mul_sum]
private theorem bondDeriv_const_mul {j k : ℕ} (ν : ℝ) {G : F.GaugeField j → ℝ} {W : F.GaugeField j}
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3)
    (hG : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0) :
    bondDeriv (fun W' => ν * G W') W c X = ν * bondDeriv G W c X := by
  unfold bondDeriv
  have h := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := ν) (i := k)
    (f := fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) (x := 0)
    (hG.of_le (by exact_mod_cast hk))
  have he : (fun τ : Fin k → ℝ => ν * G (leftTranslate (bondSpread c X τ) W)) =
      ν • fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W) := rfl
  rw [he, h]
  rfl
private theorem IsRegularFamily.smul_of_mem_Icc {L t n₀ : ℕ} {σ δ E E₃ ν : ℝ} {f : LocalFamily}
    (hf : IsRegularFamily L t n₀ σ δ E E₃ f) (h0 : 0 ≤ ν) (h1 : ν ≤ 1) :
    IsNormBoundedLocalFamily L t n₀ σ δ E E₃ (ν • f) := by
  have habs : |ν| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
  have shrink : ∀ u : ℝ, |ν * u| ≤ |u| := fun u => by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) habs
  have hcent : ∀ (F : BlockFrame) (y : F.Site F.depth),
      subtractTrivial (ν • f) F y = fun W => ν * subtractTrivial f F y W := by
    intro F y
    funext W
    simp [subtractTrivial, mul_sub]
  have hsm : ∀ F, IsCubicTorusAbove L t n₀ F → ∀ (y : F.Site F.depth) (W : F.GaugeField F.depth),
      IsSmallCurvature σ W →
      ∀ (k : ℕ) (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => subtractTrivial f F y (leftTranslate (bondSpread c X τ) W)) 0 :=
    fun F hF y W hW k c X => (hf.smooth F hF y W hW k c X).sub contDiffAt_const
  refine ⟨fun F hF y W hW k c X => ?_, fun F hF y W γ hW => ?_, fun F hF y h W hW => ?_,
    fun F hF y W k c X hW hk1 hk3 hX => ?_, fun F F' hF hF' y y' W W' r k h X hW hW' hag hk hb hX => ?_⟩
  · exact contDiffAt_const.mul (hf.smooth F hF y W hW k c X)
  · show ν * f F y (gaugeTransform γ W) = ν * f F y W
    rw [hf.gauge_invariant F hF y W γ hW]
  · show ν * f F (y + h) (translateField h W) = ν * f F y W
    rw [hf.translation_invariant F hF y h W hW]
  · have hd : bondDeriv ((ν • f) F y) W c X = ν * bondDeriv (f F y) W c X :=
      bondDeriv_const_mul ν c X hk3 (hf.smooth F hF y W hW k c X)
    rw [hd]
    exact le_trans (shrink _) (hf.decay F hF y W k c X hW hk1 hk3 hX)
  · have hd : bondDeriv (subtractTrivial (ν • f) F y) W (bondsAt y h) X =
        ν * bondDeriv (subtractTrivial f F y) W (bondsAt y h) X := by
      rw [hcent]
      exact bondDeriv_const_mul ν _ X (by omega) (hsm F hF y W hW k _ X)
    have hd' : bondDeriv (subtractTrivial (ν • f) F' y') W' (bondsAt y' h) X =
        ν * bondDeriv (subtractTrivial f F' y') W' (bondsAt y' h) X := by
      rw [hcent]
      exact bondDeriv_const_mul ν _ X (by omega) (hsm F' hF' y' W' hW' k _ X)
    rw [hd, hd', ← mul_sub]
    exact le_trans (shrink _) (hf.locality F F' hF hF' y y' W W' r k h X hW hW' hag hk hb hX)
abbrev _root_.YangMills.SharedProofs.p82607 := @IsRegularFamily.smul_of_mem_Icc
private theorem expansionDensity_bondDeriv_sub_le {a ρA ρ x κ δ E E₃ C s D : ℝ} {L m k : ℕ} {p : ℝ → ℝ}
    {f : LocalFamily} {V : F.GaugeField F.top} (hρ : 0 < ρ) (hcut : IsCutoff ρ p) (hfin : Finite F.Cell)
    (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedFamilyOnClosedBalls)
    (hMean : IntervalIntegralGibbsMeanDifferentiation)
    (hE : ∀ V' : F.GaugeField F.top, IsSmallCurvature s V' → CellExponentBounds false a ρA ρ x κ C m V')
    (hR : CentredExpansionBounds false a ρA ρ κ δ E E₃ C L m f V) (hV : IsSmallCurvature s V) (Y : F.Cell)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3)
    (M : ℝ → F.GaugeField F.top → ℝ)
    (hM : ∀ v V', M v V' = cutoffMean ρ p (stepExponent false a ρA x m f v V') fun η =>
      cellCentredExpansion false a ρA m f Y η V')
    (hMs : ∀ v ∈ Set.Icc (0 : ℝ) 1,
      ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => M v (leftTranslate (bondSpread c X τ) V)) 0)
    (hb : ∀ v ∈ Set.Icc (0 : ℝ) 1,
      |bondDeriv (M v) V c X - bondDeriv (cellCentredExpansion false a ρA m f Y 0) V c X| ≤ D) :
    |bondDeriv (expansionDensity false a ρA ρ x m p f Y) V c X -
      bondDeriv (cellCentredExpansion false a ρA m f Y 0) V c X| ≤ D := by
  classical
  set Vt : (Fin k → ℝ) → F.GaugeField F.top := fun τ => leftTranslate (bondSpread c X τ) V with hVt
  set Sv := StepVariable (finiteCells F) with hSv
  obtain ⟨hfinμ, hμ0, hμb, hμm⟩ := hRim F ρ p hρ hcut
  set μ := cutoffLaw F ρ p with hμ
  have hμc : ∀ᵐ η ∂μ, ∀ b, ‖η b‖ ≤ ρ := by
    filter_upwards [hμb] with η hη b using (hη b).le
  set P0 : (Fin k → ℝ) × Sv → ℝ := fun z =>
    ∑ Y' ∈ finiteCells F, cellExponent false a ρA x m Y' (Vt z.1) z.2 with hP0
  set R0 : (Fin k → ℝ) × Sv → ℝ := fun z =>
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false a ρA m f y z.2 (Vt z.1) with hR0
  set FY : (Fin k → ℝ) × Sv → ℝ := fun z => cellCentredExpansion false a ρA m f Y z.2 (Vt z.1) with hFY
  have hEV := hE V hV
  have sP0 : ∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 P0 (0, η) := fun η hη =>
    ContDiffAt.sum fun Y' _ => hEV.smooth Y' η k c X hη
  have sR0 : ∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 R0 (0, η) := fun η hη =>
    ContDiffAt.sum fun y _ => hR.smooth y η k c X hη
  have sFY : ∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 FY (0, η) := fun η hη => by
    have : FY = fun z => ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
        centredExpansion false a ρA m f y z.2 (Vt z.1) := rfl
    rw [this]
    exact ContDiffAt.sum fun y _ => hR.smooth y η k c X hη
  have hz : ∀ b, ‖(0 : Sv) b‖ ≤ ρ := fun b => by
    rw [show (0 : Sv) b = 0 from rfl, norm_zero]
    exact hρ.le
  set π : (Fin k → ℝ) × (ℝ × Sv) → (Fin k → ℝ) × Sv := fun z => (z.1, z.2.2) with hπ
  have hπs : ContDiff ℝ 3 π := contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
  have hvs : ContDiff ℝ 3 fun z : (Fin k → ℝ) × (ℝ × Sv) => z.2.1 := contDiff_fst.comp contDiff_snd
  have hqs : ContDiff ℝ 3 fun z : (Fin k → ℝ) × (ℝ × Sv) => ((z.1, 0) : (Fin k → ℝ) × Sv) :=
    contDiff_fst.prodMk contDiff_const
  have lift : ∀ {G : (Fin k → ℝ) × Sv → ℝ}, (∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 G (0, η)) →
      ∀ (v : ℝ) (η : Sv), (∀ b, ‖η b‖ ≤ ρ) →
        ContDiffAt ℝ 3 (fun z : (Fin k → ℝ) × (ℝ × Sv) => G (π z)) (0, v, η) := fun {G} hG v η hη =>
    ContDiffAt.comp (g := G) (f := π) (0, v, η) (hG η hη) hπs.contDiffAt
  obtain ⟨r₃, M₃, hr₃, hD₃⟩ := hDom _ k ρ μ
    (fun z => P0 (π z) - z.2.1 * R0 (π z)) hμc (fun v η _ hη =>
      (lift sP0 v η hη).sub (hvs.contDiffAt.mul (lift sR0 v η hη)))
  obtain ⟨r₄, M₄, hr₄, hD₄⟩ := hDom _ k ρ μ
    (fun z => FY (π z) - FY (z.1, 0)) hμc (fun v η _ hη =>
      (lift sFY v η hη).sub (ContDiffAt.comp (g := FY)
        (f := fun z : (Fin k → ℝ) × (ℝ × Sv) => ((z.1, 0) : (Fin k → ℝ) × Sv)) (0, v, η) (sFY 0 hz)
        hqs.contDiffAt))
  obtain ⟨r₀, hr₀, hcold⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_smallCurvature_leftTranslate hfin c X hV)
  set r : ℝ := min r₀ (min r₃ r₄) with hr
  have hrpos : 0 < r := lt_min hr₀ (lt_min hr₃ hr₄)
  set B := Metric.ball (0 : Fin k → ℝ) r with hB
  have hBo : IsOpen B := Metric.isOpen_ball
  have hB0 : B ∈ 𝓝 (0 : Fin k → ℝ) := Metric.ball_mem_nhds _ hrpos
  have h0B : (0 : Fin k → ℝ) ∈ B := Metric.mem_ball_self hrpos
  have sub₀ : B ⊆ Metric.ball 0 r₀ := Metric.ball_subset_ball (min_le_left _ _)
  have sub₃ : B ⊆ Metric.ball 0 r₃ :=
    Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _))
  have sub₄ : B ⊆ Metric.ball 0 r₄ :=
    Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsum : ∀ τ ∈ B, ∀ᵐ η ∂μ, stepExponent false a ρA x m (fun _ _ _ => 0) 0 (Vt τ) η = P0 (τ, η) :=
    fun τ hτ => by
      filter_upwards [hμb] with η hη
      exact (hE (Vt τ) (hcold τ (sub₀ hτ))).sum_eq η hη
  set A : ℝ → (Fin k → ℝ) → Sv → ℝ := fun v τ η => P0 (τ, η) - v * R0 (τ, η) with hA
  set H : ℝ → (Fin k → ℝ) → Sv → ℝ := fun _ τ η => FY (τ, η) - FY (τ, 0) with hH
  set K : ℝ := max M₃ M₄ with hK
  have dA : ∀ v ∈ Set.Icc (0 : ℝ) 1, IsDominatedSmoothFamily μ 3 B K (A v) := fun v hv =>
    IsDominatedSmoothFamily.mono_local sub₃ (le_max_left _ _) (hD₃ v hv)
  have dH : ∀ v ∈ Set.Icc (0 : ℝ) 1, IsDominatedSmoothFamily μ 3 B K (H v) := fun v hv =>
    IsDominatedSmoothFamily.mono_local sub₄ (le_max_right _ _) (hD₄ v hv)
  have hcv : ∀ τ : Fin k → ℝ, ∀ᵐ η ∂μ, ContinuousOn (fun v => A v τ η) (Set.Icc (0 : ℝ) 1) ∧
      ContinuousOn (fun v => H v τ η) (Set.Icc (0 : ℝ) 1) := fun τ =>
    Filter.Eventually.of_forall fun η => ⟨by fun_prop, continuousOn_const⟩
  have hMM := hMean Sv μ k B K A H hBo hμ0 dA dH (fun τ _ => hcv τ)
  set Φ : (Fin k → ℝ) → ℝ := fun τ => ∫ v in (0 : ℝ)..1, gibbsMean μ (A v τ) (H v τ) with hΦdef
  set c0 : (Fin k → ℝ) → ℝ := fun τ => FY (τ, 0) with hc0
  have sc0 : ContDiffAt ℝ 3 c0 0 :=
    ContDiffAt.comp (g := FY) (f := fun τ : Fin k → ℝ => ((τ, 0) : (Fin k → ℝ) × Sv)) 0 (sFY 0 hz)
      (contDiff_id.prodMk contDiff_const).contDiffAt
  have hmean : ∀ τ ∈ B, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      M v (Vt τ) = gibbsMean μ (A v τ) (H v τ) + c0 τ := fun τ hτ v hv => by
    rw [hM, hμm]
    have e : gibbsMean μ (stepExponent false a ρA x m f v (Vt τ))
        (fun η => cellCentredExpansion false a ρA m f Y η (Vt τ)) =
        gibbsMean μ (A v τ) (fun η => H v τ η + c0 τ) := by
      apply gibbsMean_congr_ae
      · filter_upwards [hsum τ hτ] with η hη
        rw [stepExponent_eq_sub, hη]
      · exact Filter.Eventually.of_forall fun η => by
          simp [hH, hc0, hFY]
    rw [e]
    exact gibbsMean_add_const hμ0 (c0 τ) ((dA v hv).aestronglyMeasurable τ hτ)
      ((dH v hv).aestronglyMeasurable τ hτ) (abs_le_of_dominated (dA v hv) hτ)
      (abs_le_of_dominated (dH v hv) hτ)
  have hcontv : ∀ τ ∈ B, ContinuousOn (fun v => gibbsMean μ (A v τ) (H v τ)) (Set.Icc (0 : ℝ) 1) :=
    fun τ hτ => gibbsMean_continuousOn hμ0 (A := fun v => A v τ) (H := fun v => H v τ) (R := K)
      (fun v hv => (dA v hv).aestronglyMeasurable τ hτ) (fun v hv => (dH v hv).aestronglyMeasurable τ hτ)
      (fun v hv => abs_le_of_dominated (dA v hv) hτ) (fun v hv => abs_le_of_dominated (dH v hv) hτ) (hcv τ)
  have hs : ∀ τ ∈ B, expansionDensity false a ρA ρ x m p f Y (Vt τ) = Φ τ + c0 τ := fun τ hτ => by
    have e1 : expansionDensity false a ρA ρ x m p f Y (Vt τ) =
        ∫ v in (0 : ℝ)..1, (gibbsMean μ (A v τ) (H v τ) + c0 τ) := by
      unfold expansionDensity
      apply intervalIntegral.integral_congr
      intro v hv
      have hv' : v ∈ Set.Icc (0 : ℝ) 1 := by
        rwa [Set.uIcc_of_le zero_le_one] at hv
      exact (hM v (Vt τ)).symm.trans (hmean τ hτ v hv')
    rw [e1, intervalIntegral.integral_add ((hcontv τ hτ).intervalIntegrable_of_Icc zero_le_one)
      intervalIntegrable_const]
    simp [hΦdef]
  have hΦ : ContDiffAt ℝ 3 Φ 0 := hMM.1.contDiffAt hB0
  have hk' : ((k : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  set e : Fin k → Fin k → ℝ := fun l => Pi.single l 1 with he
  have d1 : bondDeriv (expansionDensity false a ρA ρ x m p f Y) V c X =
      iteratedFDeriv ℝ k Φ 0 e + bondDeriv (cellCentredExpansion false a ρA m f Y 0) V c X := by
    have ev : (fun τ => expansionDensity false a ρA ρ x m p f Y (Vt τ)) =ᶠ[𝓝 0] Φ + c0 := by
      filter_upwards [hB0] with τ hτ using hs τ hτ
    show iteratedFDeriv ℝ k (fun τ => expansionDensity false a ρA ρ x m p f Y (Vt τ)) 0 e = _
    rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) ev k).self_of_nhds,
      iteratedFDeriv_add_apply (hΦ.of_le hk') (sc0.of_le hk')]
    rfl
  have d2 : ∀ v ∈ Set.Icc (0 : ℝ) 1, bondDeriv (M v) V c X =
      iteratedFDeriv ℝ k (fun τ => gibbsMean μ (A v τ) (H v τ)) 0 e +
        bondDeriv (cellCentredExpansion false a ρA m f Y 0) V c X := fun v hv => by
    have ev : (fun τ => M v (Vt τ)) =ᶠ[𝓝 0] (fun τ => gibbsMean μ (A v τ) (H v τ)) + c0 := by
      filter_upwards [hB0] with τ hτ using hmean τ hτ v hv
    have hw : ContDiffAt ℝ 3 (fun τ => gibbsMean μ (A v τ) (H v τ)) 0 := by
      refine ((hMs v hv).sub sc0).congr_of_eventuallyEq ?_
      filter_upwards [hB0] with τ hτ
      show gibbsMean μ (A v τ) (H v τ) = M v (Vt τ) - c0 τ
      rw [hmean τ hτ v hv]
      ring
    show iteratedFDeriv ℝ k (fun τ => M v (Vt τ)) 0 e = _
    rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) ev k).self_of_nhds,
      iteratedFDeriv_add_apply (hw.of_le hk') (sc0.of_le hk')]
    rfl
  have d3 : iteratedFDeriv ℝ k Φ 0 e =
      ∫ v in (0 : ℝ)..1, iteratedFDeriv ℝ k (fun τ => gibbsMean μ (A v τ) (H v τ)) 0 e :=
    hMM.2 0 h0B k hk e
  rw [d1, add_sub_cancel_right, d3]
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := D)
    (f := fun v => iteratedFDeriv ℝ k (fun τ => gibbsMean μ (A v τ) (H v τ)) 0 e) (fun v hv => by
      have hv' : v ∈ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at hv
        exact Set.Ioc_subset_Icc_self hv
      have h1 := hb v hv'
      rw [d2 v hv', add_sub_cancel_right] at h1
      exact h1)
  simpa using hbd
private def NearFrameBound (T : StepParameters) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    ∀ F, IsCubicTopTorus T.L t T.n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
      IsSmallCurvature (5 / 4 * T.σ) V →
      ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
        AreUnitVectors X →
        |bondDeriv (stepDensityFamily T x f F Y) V c X - bondDeriv (expansionAtFrameFamily T false x f F Y) V c X| ≤
          C * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))
private theorem nearFrameBound_of_means (hRim : CutoffMeanIsGibbsMean)
    (hDom : DominatedFamilyOnClosedBalls) (hMean : IntervalIntegralGibbsMeanDifferentiation)
    (T : StepParameters) (hT : T.IsOrdered) (hn : 2 ≤ T.n₀) (hO : SingleTorusMeanBoundsAt T)
    (hX : CellExponentsBoundedAt T) (hR : CentredExpansionsBoundedAt T) : NearFrameBound T (T.CE * T.E) := by
  intro t x f hx hf F hF Y V hV k c X hk hU
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    show 0 < T.σ / 64
    positivity
  have hfin : Finite F.Cell := by
    obtain ⟨-, -, n, hside, hn'⟩ := hF
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      rw [hper, hside]
      omega⟩
    exact Pi.finite
  have hE0 : 0 < T.E := by linarith [hT.one_le_E]
  have hMc : ∀ v ∈ Set.Icc (0 : ℝ) 1, SingleTorusMeanBounds false T.a T.chainParams.ρA T.σ x T.κ T.decayRate T.E
      (T.E / T.η₃) T.CE T.L t T.n₀ (frameRadius x) T.p (v • f) f := fun v hv =>
    hO t x (v • f) f T.E false hx hE0 (IsRegularFamily.smul_of_mem_Icc hf hv.1 hv.2) hf
  refine expansionDensity_bondDeriv_sub_le (a := T.a) (ρA := T.chainParams.ρA) (ρ := T.ballRadius) (x := x)
    (m := frameRadius x) (p := T.p) (f := f) hρ hT.cutoff hfin hRim hDom hMean
    (fun V' hV' => (hX t x F V' false hx hF hV').1) (hR t x f F V false hx hf hF hV) hV Y c X (by omega)
    (fun v => conditionalExpansionMean false T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x) T.p (v • f) f F Y)
    (fun v V' => ?_) (fun v hv => (hMc v hv).density.smooth F hF Y V hV k c X)
    (fun v hv => (hMc v hv).near_block F hF Y V k c X hV hk hU)
  show cutoffMean T.ballRadius T.p (stepExponent false T.a T.chainParams.ρA x (frameRadius x) (v • f) 1 V') _ = _
  congr 1
  funext η
  exact stepExponent_smul_one _ _ _ _ _ _ _ _
private theorem EventuallyInParameters.of_rescaled_CE {Q' Q : StepParameters → Prop}
    (h : ∀ T : StepParameters, 1 ≤ T.E → Q' { T with CE := T.CE / T.E } → Q T)
    (hq : EventuallyInParameters Q') : EventuallyInParameters Q := by
  intro a ha
  obtain ⟨L₀, h1⟩ := hq a ha
  refine ⟨L₀, fun L hL hL₀ c hc => ?_⟩
  obtain ⟨Ct₀, h2⟩ := h1 L hL hL₀ c hc
  refine ⟨Ct₀, fun Ct hCt => ?_⟩
  obtain ⟨κ₀, hκ₀, h3⟩ := h2 Ct hCt
  refine ⟨κ₀, hκ₀, fun κ hκ hκ' => ?_⟩
  obtain ⟨η₀, hη₀, h4⟩ := h3 κ hκ hκ'
  refine ⟨η₀, hη₀, fun η₃ hη hη1 hη' => ?_⟩
  obtain ⟨N₀, h5⟩ := h4 η₃ hη hη1 hη'
  refine ⟨N₀, fun nss hN => ?_⟩
  obtain ⟨σ₀, hσ₀, h6⟩ := h5 nss hN
  refine ⟨σ₀, hσ₀, fun σ hσ hσ' p hp => ?_⟩
  obtain ⟨C₀, h7⟩ := h6 σ hσ hσ' p hp
  refine ⟨C₀, fun Cs hCs E hE => ?_⟩
  obtain ⟨m₀, h8⟩ := h7 Cs hCs E hE
  refine ⟨m₀, fun n₀ hn₀ => ?_⟩
  obtain ⟨C₁, h9⟩ := h8 n₀ hn₀
  have hE0 : 0 < E := by linarith
  refine ⟨C₁ * E, fun CE hCE => ?_⟩
  obtain ⟨y₀, h10⟩ := h9 (CE / E) ((le_div_iff₀ hE0).mpr hCE)
  exact ⟨y₀, fun y₁ hy => h _ hE (h10 y₁ hy)⟩
abbrev _root_.YangMills.SharedProofs.p51044 := @EventuallyInParameters.of_rescaled_CE
private theorem bondDeriv_fin_zero (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G V c X = G V := by apply _root_.YangMills.SharedProofs.p1654 <;> assumption
private theorem bondSpan_fin_zero {j : ℕ} (Y : F.Site j) (c : Fin 0 → F.Site j × Fin 4) : bondSpan Y c = 0 := by
  simp [bondSpan]
end StepDensityNearFrame
open StepDensityNearFrame in
theorem stepDensityNearFrame (hJ : EventuallyInParametersCombines) (hO : singleTorusMeanStatement)
    (hX : CellExponentsBounded) (hR : CentredExpansionsBounded)
    (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedFamilyOnClosedBalls)
    (hMean : IntervalIntegralGibbsMeanDifferentiation) : stepDensityNearFrameStatement := by
  obtain ⟨join, weaken⟩ := hJ
  have h2 : EventuallyInParameters fun T => 2 ≤ T.n₀ := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨2, fun _ h => ⟨0, fun _ _ => ⟨0, fun _ _ => h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have base : EventuallyInParameters fun T => NearFrameBound T (T.CE * T.E) :=
    weaken _ _ (fun T hT h => nearFrameBound_of_means hRim hDom hMean T hT h.1 h.2.1 h.2.2.1 h.2.2.2)
      (join _ _ h2 (join _ _ hO (join _ _ hX hR)))
  refine EventuallyInParameters.of_rescaled_CE (Q' := fun T => NearFrameBound T (T.CE * T.E))
    (fun T hE h => ?_) base
  have hE0 : T.E ≠ 0 := by
    have : 0 < T.E := by linarith
    exact this.ne'
  have h1 : NearFrameBound T (T.CE / T.E * T.E) := h
  rw [div_mul_cancel₀ _ hE0] at h1
  intro t x f hx hf F hF Y V hV
  have key := h1 t x f hx hf F hF Y V hV
  refine ⟨?_, fun k c X _ hk2 hU => key k c X hk2 hU⟩
  have h0 := key 0 Fin.elim0 Fin.elim0 (Nat.zero_le _) (fun l => l.elim0)
  rw [bondDeriv_fin_zero, bondDeriv_fin_zero, bondSpan_fin_zero] at h0
  have hexp : Real.exp (-(T.κ / 2 ^ 6 * ((0 : ℕ) : ℝ))) = 1 := by simp
  rw [hexp, mul_one] at h0
  exact h0
end ColdStepAtMirrorFrames
end YangMills.Construction
end
