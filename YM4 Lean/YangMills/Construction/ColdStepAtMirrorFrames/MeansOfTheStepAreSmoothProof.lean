import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrame
import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExponentsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfTheStepAreSmooth
import YangMills.Construction.SummableBoundsOfTheFlow.TheBirthsBetweenProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages MeasureTheory Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace MeansContDiff
private theorem eventually_isSmallCurvature_translate {k : ℕ} (hfin : Finite F.Cell) {s : ℝ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature s V) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0, IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by apply _root_.YangMills.Construction.InterpolatedBirths.eventually_isSmallCurvature_translate <;> assumption
private theorem IsDominatedSmoothFamily.mono' {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ}
    {B B' : Set (Fin k → ℝ)} {K K' : ℝ} {G : (Fin k → ℝ) → Ω → ℝ} (hB : B' ⊆ B) (hK : K ≤ K')
    (h : IsDominatedSmoothFamily μ 3 B K G) : IsDominatedSmoothFamily μ 3 B' K' G := by apply _root_.YangMills.Construction.InterpolatedBirths.IsDominatedSmoothFamily.mono <;> assumption
private theorem contDiff_totalQuadratic (lam x : ℝ) :
    ContDiff ℝ 3 (totalQuadratic (F := F) lam x) := by apply _root_.YangMills.Construction.InterpolatedBirths.contDiff_totalQuadratic <;> assumption
private theorem contDiff_cellQuadratic (lam x : ℝ) (Y : F.Cell) :
    ContDiff ℝ 3 (cellQuadratic (F := F) lam x Y) := by apply _root_.YangMills.Construction.InterpolatedBirths.contDiff_cellQuadratic <;> assumption
private theorem gibbsMean_congr_ae {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {A A' H H' : Ω → ℝ}
    (hA : A =ᵐ[μ] A') (hH : H =ᵐ[μ] H') : gibbsMean μ A H = gibbsMean μ A' H' := by apply _root_.YangMills.Construction.InterpolatedBirths.gibbsMean_congr_ae <;> assumption
private theorem stepExponent_eq_sub_centredExpansion (a ρA x : ℝ) (m : ℕ) (f : LocalFamily) (ν : ℝ)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    stepExponent false a ρA x m f ν V η = stepExponent false a ρA x m (fun _ _ _ => 0) 0 V η -
      ν * ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false a ρA m f y η V := by
  simp [stepExponent]
private theorem contDiffAt_densities_translate {a ρA ρ lam x κ δ E E₃ C s : ℝ} {L m k : ℕ}
    {p : ℝ → ℝ} {f : LocalFamily} {V : F.GaugeField F.top} (hρ : 0 < ρ) (hcut : IsCutoff ρ p)
    (hfin : Finite F.Cell) (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedFamilyOnClosedBalls)
    (hMean : IntervalIntegralGibbsMeanDifferentiation)
    (hE : ∀ V' : F.GaugeField F.top, IsSmallCurvature s V' → CellExponentBounds false a ρA ρ x κ C m V')
    (hR : CentredExpansionBounds false a ρA ρ κ δ E E₃ C L m f V) (hV : IsSmallCurvature s V) (Y : F.Cell)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    ContDiffAt ℝ 3 (fun τ : Fin k → ℝ =>
        interactionDensity false a ρA ρ lam x m p f Y (leftTranslate (bondSpread c X τ) V)) 0 ∧
      ContDiffAt ℝ 3 (fun τ : Fin k → ℝ =>
        expansionDensity false a ρA ρ x m p f Y (leftTranslate (bondSpread c X τ) V)) 0 := by
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
  set HY : (Fin k → ℝ) × Sv → ℝ := fun z => cellExponent false a ρA x m Y (Vt z.1) z.2 with hHY
  set FY : (Fin k → ℝ) × Sv → ℝ := fun z => cellCentredExpansion false a ρA m f Y z.2 (Vt z.1) with hFY
  have hEV := hE V hV
  have sP0 : ∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 P0 (0, η) := fun η hη =>
    ContDiffAt.sum fun Y' _ => hEV.smooth Y' η k c X hη
  have sR0 : ∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 R0 (0, η) := fun η hη =>
    ContDiffAt.sum fun y _ => hR.smooth y η k c X hη
  have sHY : ∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 HY (0, η) := fun η hη =>
    hEV.smooth Y η k c X hη
  have sFY : ∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 FY (0, η) := fun η hη => by
    have : FY = fun z => ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter
        (fun y => enclosingCell y = Y), centredExpansion false a ρA m f y z.2 (Vt z.1) := rfl
    rw [this]
    exact ContDiffAt.sum fun y _ => hR.smooth y η k c X hη
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
  obtain ⟨r₃, M₃, hr₃, hD₃⟩ := hDom _ k ρ μ
    (fun z => P0 (π z) - z.2.1 * R0 (π z)) hμc (fun v η _ hη =>
      (lift sP0 v η hη).sub (hvs.contDiffAt.mul (lift sR0 v η hη)))
  obtain ⟨r₄, M₄, hr₄, hD₄⟩ := hDom _ k ρ μ
    (fun z => FY (π z)) hμc (fun v η _ hη => lift sFY v η hη)
  obtain ⟨r₀, hr₀, hcold⟩ :=
    Metric.eventually_nhds_iff_ball.mp (eventually_isSmallCurvature_translate hfin c X hV)
  set r : ℝ := min r₀ (min (min r₁ r₂) (min r₃ r₄)) with hr
  have hrpos : 0 < r := lt_min hr₀ (lt_min (lt_min hr₁ hr₂) (lt_min hr₃ hr₄))
  set B := Metric.ball (0 : Fin k → ℝ) r with hB
  have hBo : IsOpen B := Metric.isOpen_ball
  have hB0 : B ∈ 𝓝 (0 : Fin k → ℝ) := Metric.ball_mem_nhds _ hrpos
  have sub₀ : B ⊆ Metric.ball 0 r₀ := Metric.ball_subset_ball (min_le_left _ _)
  have sub₁ : B ⊆ Metric.ball 0 r₁ := Metric.ball_subset_ball
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have sub₂ : B ⊆ Metric.ball 0 r₂ := Metric.ball_subset_ball
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have sub₃ : B ⊆ Metric.ball 0 r₃ := Metric.ball_subset_ball
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have sub₄ : B ⊆ Metric.ball 0 r₄ := Metric.ball_subset_ball
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hsum : ∀ τ ∈ B, ∀ᵐ η ∂μ,
      stepExponent false a ρA x m (fun _ _ _ => 0) 0 (Vt τ) η = P0 (τ, η) := fun τ hτ => by
    filter_upwards [hμb] with η hη
    exact (hE (Vt τ) (hcold τ (sub₀ hτ))).sum_eq η hη
  constructor
  · set A : ℝ → (Fin k → ℝ) → Sv → ℝ := fun v τ η =>
      v * P0 (τ, η) + (1 - v) * totalQuadratic lam x η with hA
    set H : ℝ → (Fin k → ℝ) → Sv → ℝ := fun _ τ η => HY (τ, η) - cellQuadratic lam x Y η with hH
    have hM := hMean Sv μ k B (max M₁ M₂) A H hBo hμ0
      (fun v hv => IsDominatedSmoothFamily.mono' sub₁ (le_max_left _ _) (hD₁ v hv))
      (fun v hv => IsDominatedSmoothFamily.mono' sub₂ (le_max_right _ _) (hD₂ v hv))
      (fun τ _ => Filter.Eventually.of_forall fun η =>
        ⟨by fun_prop, continuousOn_const⟩)
    have heq : ∀ τ ∈ B, interactionDensity false a ρA ρ lam x m p f Y (Vt τ) =
        -∫ v in (0 : ℝ)..1, gibbsMean μ (A v τ) (H v τ) := fun τ hτ => by
      unfold interactionDensity
      congr 1
      apply intervalIntegral.integral_congr
      intro v _
      simp only
      rw [hμm]
      apply gibbsMean_congr_ae
      · filter_upwards [hsum τ hτ] with η hη
        have h0 := stepExponent_eq_sub_centredExpansion a ρA x m f 0 (Vt τ) η
        simp only [zero_mul, sub_zero] at h0
        simp only [hA, h0, hη]
      · exact Filter.EventuallyEq.rfl
    refine (hM.1.neg.contDiffAt hB0).congr_of_eventuallyEq ?_
    filter_upwards [hB0] with τ hτ using heq τ hτ
  · set A : ℝ → (Fin k → ℝ) → Sv → ℝ := fun v τ η => P0 (τ, η) - v * R0 (τ, η) with hA
    set H : ℝ → (Fin k → ℝ) → Sv → ℝ := fun _ τ η => FY (τ, η) with hH
    have hM := hMean Sv μ k B (max M₃ M₄) A H hBo hμ0
      (fun v hv => IsDominatedSmoothFamily.mono' sub₃ (le_max_left _ _) (hD₃ v hv))
      (fun v hv => IsDominatedSmoothFamily.mono' sub₄ (le_max_right _ _) (hD₄ v hv))
      (fun τ _ => Filter.Eventually.of_forall fun η =>
        ⟨by fun_prop, continuousOn_const⟩)
    have heq : ∀ τ ∈ B, expansionDensity false a ρA ρ x m p f Y (Vt τ) =
        ∫ v in (0 : ℝ)..1, gibbsMean μ (A v τ) (H v τ) := fun τ hτ => by
      unfold expansionDensity
      apply intervalIntegral.integral_congr
      intro v _
      simp only
      rw [hμm]
      apply gibbsMean_congr_ae
      · filter_upwards [hsum τ hτ] with η hη
        rw [stepExponent_eq_sub_centredExpansion, hη]
      · exact Filter.EventuallyEq.rfl
    refine (hM.1.contDiffAt hB0).congr_of_eventuallyEq ?_
    filter_upwards [hB0] with τ hτ using heq τ hτ
end MeansContDiff
open MeansContDiff in
theorem meansContDiffThree_holds (hJ : EventuallyInParametersCombines)
    (hX : CellExponentsBounded) (hR : CentredExpansionsBounded)
    (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedFamilyOnClosedBalls)
    (hMean : IntervalIntegralGibbsMeanDifferentiation) : meansContDiffThree := by
  obtain ⟨join, weaken⟩ := hJ
  have h2 : EventuallyInParameters fun T => 2 ≤ T.n₀ := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨2, fun _ h => ⟨0, fun _ _ => ⟨0, fun _ _ => h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine weaken _ _ (fun T hT h t x hx f hf F hF Y V hV => ?_) (join _ _ h2 (join _ _ hX hR))
  obtain ⟨hn₂, hX, hR⟩ := h
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    show 0 < T.σ / 64
    positivity
  have hfin : Finite F.Cell := by
    obtain ⟨-, -, n, hside, hn⟩ := hF
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      rw [hper, hside]
      omega⟩
    exact Pi.finite
  have key := fun (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) =>
    contDiffAt_densities_translate (lam := T.chainParams.lam) hρ hT.cutoff hfin hRim hDom hMean
      (fun V' hV' => (hX t x F V' false hx hF hV').1) (hR t x f F V false hx hf hF hV) hV Y c X
  exact ⟨fun k c X => (key k c X).1, fun k c X => (key k c X).2⟩
end YangMills.Construction.ColdStepAtMirrorFrames
end
