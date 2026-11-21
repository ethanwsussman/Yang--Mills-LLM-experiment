import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExponentsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMembersAreClosed
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfTheMeanOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.MeanDensityOnOneTorusForm
import YangMills.Construction.ColdStepAtMirrorFrames.TermsInFixedVariables
import YangMills.Construction.SummableBoundsOfTheFlow.TheBirthsBetweenProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages MeasureTheory Topology YangMills.Construction.SummableBounds YangMills.Construction.Estimates
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace InteractionDensityOnTorus
variable {F : BlockFrame}
theorem leftTranslate_bondSpread_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (V : F.GaugeField F.top) :
    leftTranslate (bondSpread c X 0) V = V := by apply _root_.YangMills.SharedProofs.p2043 <;> assumption
theorem eventually_isSmallCurvature_leftTranslate {k : ℕ} (hfin : Finite F.Cell) {s : ℝ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature s V) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0, IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by apply _root_.YangMills.Construction.InterpolatedBirths.eventually_isSmallCurvature_translate <;> assumption
theorem isDominatedSmoothFamily_mono {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {k : ℕ}
    {B B' : Set (Fin k → ℝ)} {K K' : ℝ} {G : (Fin k → ℝ) → Ω → ℝ} (hB : B' ⊆ B) (hK : K ≤ K')
    (h : IsDominatedSmoothFamily μ 3 B K G) : IsDominatedSmoothFamily μ 3 B' K' G := by apply _root_.YangMills.Construction.InterpolatedBirths.IsDominatedSmoothFamily.mono <;> assumption
theorem contDiff_totalQuadratic (lam x : ℝ) : ContDiff ℝ 3 (totalQuadratic (F := F) lam x) := by apply _root_.YangMills.Construction.InterpolatedBirths.contDiff_totalQuadratic <;> assumption
theorem contDiff_cellQuadratic (lam x : ℝ) (Y : F.Cell) :
    ContDiff ℝ 3 (cellQuadratic (F := F) lam x Y) := by apply _root_.YangMills.Construction.InterpolatedBirths.contDiff_cellQuadratic <;> assumption
theorem gibbsMean_congr {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {A A' H H' : Ω → ℝ}
    (hA : A =ᵐ[μ] A') (hH : H =ᵐ[μ] H') : gibbsMean μ A H = gibbsMean μ A' H' := by apply _root_.YangMills.Construction.InterpolatedBirths.gibbsMean_congr_ae <;> assumption
theorem stepExponent_without_local_family (a ρA x : ℝ) (m : ℕ) (f : LocalFamily) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    stepExponent false a ρA x m f 0 V η = stepExponent false a ρA x m (fun _ _ _ => 0) 0 V η := by
  simp [stepExponent]
theorem iteratedFDeriv_smul_sum_add_const {P α : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (S : Finset α) (φ : α → P → ℝ) (v r : ℝ)
    {n : ℕ} (hn : n ≠ 0) (hφ : ∀ i ∈ S, ContDiffAt ℝ n (φ i) 0) (w : Fin n → P) :
    iteratedFDeriv ℝ n (fun τ => v * ∑ i ∈ S, φ i τ + r) 0 w =
      v * ∑ i ∈ S, iteratedFDeriv ℝ n (φ i) 0 w := by apply _root_.YangMills.Construction.InterpolatedBirths.iteratedFDeriv_smul_sum_add_const <;> assumption
theorem continuousOn_gibbsMean {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (hμ : μ ≠ 0)
    {a h : ℝ → Ω → ℝ} {K : ℝ} (hm : ∀ v ∈ Set.Icc (0 : ℝ) 1, AEStronglyMeasurable (a v) μ)
    (hm' : ∀ v ∈ Set.Icc (0 : ℝ) 1, AEStronglyMeasurable (h v) μ)
    (hb : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ ω ∂μ, |a v ω| ≤ K)
    (hb' : ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ ω ∂μ, |h v ω| ≤ K)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun v => a v ω) (Set.Icc (0 : ℝ) 1))
    (hc' : ∀ᵐ ω ∂μ, ContinuousOn (fun v => h v ω) (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun v => gibbsMean μ (a v) (h v)) (Set.Icc (0 : ℝ) 1) := by apply _root_.YangMills.Construction.InterpolatedBirths.continuousOn_gibbsMean <;> assumption
theorem interactionDensity_bound_of_convex {a ρA ρ lam x κ C Kc s : ℝ} {m : ℕ} {p : ℝ → ℝ}
    {f : LocalFamily} {N : ℕ} {Cq : ℕ → ℝ}
    {V : F.GaugeField F.top} (hρ : 0 < ρ) (hcut : IsCutoff ρ p) (hfin : Finite F.Cell) (hx : 1 ≤ x)
    (hlam : 0 < lam) (hκ : 0 < κ) (hK0 : 0 ≤ Kc)
    (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedFamilyOnClosedBalls)
    (hMean : IntervalIntegralGibbsMeanDifferentiation) (hSub : IteratedDerivAlongSubfamily)
    (hClosed : ConvexClassClosure)
    (hE : ∀ V' : F.GaugeField F.top, IsSmallCurvature s V' → CellExponentBounds false a ρA ρ x κ C m V')
    (hV : IsSmallCurvature s V)
    (hconvex : IsConvexClassMember ρ (x * lam / 4) κ (chordBondDist F) (stepExponent false a ρA x m f 0 V))
    (hdist : IsPseudoMetricOnBonds (chordBondDist F))
    (hfew : ∀ z : F.Cell,
      (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤ N)
    (hObs : ∀ (Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ)
      (K : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ) (Y : F.Cell),
      IsUniformlyConvexDecaying ρ (x * lam / 4) κ (chordBondDist F) Ψ K →
      (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
        |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖) →
      ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
        AreUnitVectors X → ObservableBounds a ρA ρ lam x κ m p Cq Ψ Y V c X)
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
      IsCellFamily a ρA ρ lam x v m Ψ Y V c X A H →
      (∀ (j : ℕ) (l : Fin j → Fin k), j ≤ 3 →
        ObservableBounds a ρA ρ lam x κ m p Cq Ψ Y V (c ∘ l) (X ∘ l)) →
      |iteratedFDeriv ℝ k (fun s => gibbsMean (cutoffLaw F ρ p) (A s) (H s)) 0 (fun l => Pi.single l 1)| ≤
        Kc * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)))
    (Y : F.Cell) {k : ℕ} (hk : k ≤ 3) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hX : AreUnitVectors X) :
    |bondDeriv (interactionDensity false a ρA ρ lam x m p f Y) V c X| ≤
        Kc * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) ∧
      IntervalIntegrable (fun v => cutoffMean ρ p (fun η => v * stepExponent false a ρA x m f 0 V η +
        (1 - v) * totalQuadratic lam x η) (fun η => cellExponent false a ρA x m Y V η - cellQuadratic lam x Y η))
        volume 0 1 := by
  classical
  have hx0 : 0 < x := by linarith
  set Vt : (Fin k → ℝ) → F.GaugeField F.top := fun τ => leftTranslate (bondSpread c X τ) V with hVt
  set Sv := StepVariable (finiteCells F) with hSv
  obtain ⟨hfinμ, hμ0, hμb, hμm⟩ := hRim F ρ p hρ hcut
  set μ := cutoffLaw F ρ p with hμ
  have hμc : ∀ᵐ η ∂μ, ∀ b, ‖η b‖ ≤ ρ := by
    filter_upwards [hμb] with η hη b using (hη b).le
  set P0 : (Fin k → ℝ) × Sv → ℝ := fun z =>
    ∑ Y' ∈ finiteCells F, cellExponent false a ρA x m Y' (Vt z.1) z.2 with hP0
  set HY : (Fin k → ℝ) × Sv → ℝ := fun z => cellExponent false a ρA x m Y (Vt z.1) z.2 with hHY
  have hEV := hE V hV
  have sB : ∀ (Y' : F.Cell) (η : Sv), (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ 3 (fun z : (Fin k → ℝ) × Sv => cellExponent false a ρA x m Y' (Vt z.1) z.2) (0, η) :=
    fun Y' η hη => hEV.smooth Y' η k c X hη
  have sP0 : ∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 P0 (0, η) := fun η hη =>
    ContDiffAt.sum fun Y' _ => sB Y' η hη
  have sHY : ∀ η : Sv, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 HY (0, η) := fun η hη => sB Y η hη
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
    Metric.eventually_nhds_iff_ball.mp (eventually_isSmallCurvature_leftTranslate hfin c X hV)
  set r : ℝ := min r₀ (min r₁ r₂) with hr
  have hrpos : 0 < r := lt_min hr₀ (lt_min hr₁ hr₂)
  set B := Metric.ball (0 : Fin k → ℝ) r with hB
  have hBo : IsOpen B := Metric.isOpen_ball
  have hB0 : B ∈ 𝓝 (0 : Fin k → ℝ) := Metric.ball_mem_nhds _ hrpos
  have h0B : (0 : Fin k → ℝ) ∈ B := mem_of_mem_nhds hB0
  have sub₀ : B ⊆ Metric.ball 0 r₀ := Metric.ball_subset_ball (min_le_left _ _)
  have sub₁ : B ⊆ Metric.ball 0 r₁ := Metric.ball_subset_ball
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have sub₂ : B ⊆ Metric.ball 0 r₂ := Metric.ball_subset_ball
    (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsum : ∀ τ ∈ B, ∀ᵐ η ∂μ, stepExponent false a ρA x m (fun _ _ _ => 0) 0 (Vt τ) η = P0 (τ, η) :=
    fun τ hτ => by
      filter_upwards [hμb] with η hη
      exact (hE (Vt τ) (hcold τ (sub₀ hτ))).sum_eq η hη
  set A : ℝ → (Fin k → ℝ) → Sv → ℝ := fun v τ η =>
    v * P0 (τ, η) + (1 - v) * totalQuadratic lam x η with hA
  set H : ℝ → (Fin k → ℝ) → Sv → ℝ := fun _ τ η => HY (τ, η) - cellQuadratic lam x Y η with hH
  have hdomA : ∀ v ∈ Set.Icc (0 : ℝ) 1, IsDominatedSmoothFamily μ 3 B (max M₁ M₂) (A v) := fun v hv =>
    isDominatedSmoothFamily_mono sub₁ (le_max_left _ _) (hD₁ v hv)
  have hdomH : ∀ v ∈ Set.Icc (0 : ℝ) 1, IsDominatedSmoothFamily μ 3 B (max M₁ M₂) (H v) := fun v hv =>
    isDominatedSmoothFamily_mono sub₂ (le_max_right _ _) (hD₂ v hv)
  have hM := hMean Sv μ k B (max M₁ M₂) A H hBo hμ0 hdomA hdomH
    (fun τ _ => Filter.Eventually.of_forall fun η => ⟨by fun_prop, continuousOn_const⟩)
  have heq : ∀ τ ∈ B, interactionDensity false a ρA ρ lam x m p f Y (Vt τ) =
      -∫ v in (0 : ℝ)..1, gibbsMean μ (A v τ) (H v τ) := fun τ hτ => by
    unfold interactionDensity
    congr 1
    apply intervalIntegral.integral_congr
    intro v _
    simp only
    rw [hμm]
    apply gibbsMean_congr
    · filter_upwards [hsum τ hτ] with η hη
      rw [stepExponent_without_local_family, hη]
    · exact Filter.EventuallyEq.rfl
  have hev : (fun τ => interactionDensity false a ρA ρ lam x m p f Y (Vt τ)) =ᶠ[𝓝 0]
      -(fun τ => ∫ v in (0 : ℝ)..1, gibbsMean μ (A v τ) (H v τ)) := by
    filter_upwards [hB0] with τ hτ using heq τ hτ
  have hcd : ContDiffAt ℝ k (fun τ => ∫ v in (0 : ℝ)..1, gibbsMean μ (A v τ) (H v τ)) 0 :=
    (hM.1.contDiffAt hB0).of_le (by norm_cast)
  have hder : bondDeriv (interactionDensity false a ρA ρ lam x m p f Y) V c X =
      -∫ v in (0 : ℝ)..1, iteratedFDeriv ℝ k (fun τ => gibbsMean μ (A v τ) (H v τ)) 0
        (fun l => Pi.single l 1) := by
    unfold bondDeriv
    rw [(hev.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds, iteratedFDeriv_neg_apply,
      ContinuousMultilinearMap.neg_apply, hM.2 0 h0B k hk]
  have e0 : Vt 0 = V := leftTranslate_bondSpread_zero c X V
  refine ⟨?_, ?_⟩
  swap
  · have hc : ContinuousOn (fun v => gibbsMean μ (A v 0) (H v 0)) (Set.Icc (0 : ℝ) 1) := by
      refine continuousOn_gibbsMean (K := max M₁ M₂) hμ0
        (fun v hv => (hdomA v hv).aestronglyMeasurable 0 h0B)
        (fun v hv => (hdomH v hv).aestronglyMeasurable 0 h0B) (fun v hv => ?_) (fun v hv => ?_)
        (Filter.Eventually.of_forall fun η => by fun_prop)
        (Filter.Eventually.of_forall fun η => continuousOn_const)
      · filter_upwards [(hdomA v hv).norm_iteratedFDeriv_le] with ω hω
        have := hω 0 (by norm_num) 0 h0B
        simpa using this
      · filter_upwards [(hdomH v hv).norm_iteratedFDeriv_le] with ω hω
        have := hω 0 (by norm_num) 0 h0B
        simpa using this
    have hc' : ContinuousOn (fun v => cutoffMean ρ p (fun η => v * stepExponent false a ρA x m f 0 V η +
        (1 - v) * totalQuadratic lam x η) (fun η => cellExponent false a ρA x m Y V η - cellQuadratic lam x Y η))
        (Set.Icc (0 : ℝ) 1) := by
      refine hc.congr fun v _ => ?_
      simp only
      rw [hμm]
      apply gibbsMean_congr
      · filter_upwards [hsum 0 h0B] with η hη
        rw [stepExponent_without_local_family]
        rw [e0] at hη
        rw [hη]
      · refine Filter.Eventually.of_forall fun η => ?_
        simp only [hH, hHY, e0]
    exact hc'.intervalIntegrable_of_Icc zero_le_one
  rw [hder, abs_neg]
  have hpoint : ∀ v ∈ Set.Icc (0 : ℝ) 1,
      |iteratedFDeriv ℝ k (fun τ => gibbsMean μ (A v τ) (H v τ)) 0 (fun l => Pi.single l 1)| ≤
        Kc * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c)) := by
    intro v hv
    have hm4 : 0 < x * lam / 4 := by positivity
    have hnn : ∀ b b' : ↥(chordBonds (finiteCells F)), 0 ≤ chordBondDist F b b' := fun b b' => by
      unfold chordBondDist
      positivity
    obtain ⟨hsq, hcomb, -⟩ := hClosed _ ρ (x * lam / 4) κ (chordBondDist F) hρ hm4 hκ.le hdist hnn
    obtain ⟨Ψ, K, hagree, hconv, hslope⟩ := hcomb _ _ v hv.1 hv.2 hconvex hsq
    have hfam : IsCellFamily a ρA ρ lam x v m Ψ Y V c X (A v) (H v) := by
      refine ⟨fun η hη => ?_, fun j l hj η hη => ?_, fun j l hj η hη => ?_⟩
      · refine Eq.trans ?_ (hagree η hη).symm
        have e1 : P0 (0, η) = stepExponent false a ρA x m f 0 V η := by
          rw [stepExponent_without_local_family, hEV.sum_eq η hη]
          simp only [hP0, e0]
        have e2 : totalQuadratic lam x η = ∑ b, 2 * (x * lam / 4) * ‖η b‖ ^ 2 := by
          unfold totalQuadratic
          exact Finset.sum_congr rfl fun b _ => by ring
        simp only [hA, e1, e2]
      · have hηc : ∀ b, ‖η b‖ ≤ ρ := fun b => (hη b).le
        have hφ : ∀ Y' ∈ finiteCells F, ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞)
            (fun τ => cellExponent false a ρA x m Y' (Vt τ) η) 0 := fun Y' _ => by
          have hp : ContDiffAt ℝ 3 (fun s : Fin k → ℝ => (s, η)) 0 := contDiffAt_id.prodMk contDiffAt_const
          have h5 := ContDiffAt.comp (0 : Fin k → ℝ) (sB Y' η hηc) hp
          exact h5.of_le (by norm_cast)
        have h1 := iteratedFDeriv_smul_sum_add_const (finiteCells F)
          (fun Y' τ => cellExponent false a ρA x m Y' (Vt τ) η) v ((1 - v) * totalQuadratic lam x η)
          (n := j + 1) (by omega) hφ (fun i => Pi.single (l i) 1)
        show iteratedFDeriv ℝ (j + 1) (fun τ => v * ∑ Y' ∈ finiteCells F,
            cellExponent false a ρA x m Y' (Vt τ) η + (1 - v) * totalQuadratic lam x η) 0 _ = _
        rw [h1]
        unfold exponentObservable
        congr 1
        refine Finset.sum_congr rfl fun Y' hY' => ?_
        exact hSub F F.top k (j + 1) (fun V' => cellExponent false a ρA x m Y' V' η) V c X l (hφ Y' hY')
      · have hηc : ∀ b, ‖η b‖ ≤ ρ := fun b => (hη b).le
        have hp : ContDiffAt ℝ 3 (fun s : Fin k → ℝ => (s, η)) 0 := contDiffAt_id.prodMk contDiffAt_const
        have h5 := ContDiffAt.comp (0 : Fin k → ℝ) (sB Y η hηc) hp
        have h6 : ContDiffAt ℝ (j : WithTop ℕ∞) (fun τ => cellExponent false a ρA x m Y (Vt τ) η -
            cellQuadratic lam x Y η) 0 := (h5.of_le (by norm_cast)).sub contDiffAt_const
        exact hSub F F.top k j (fun V' => cellExponent false a ρA x m Y V' η - cellQuadratic lam x Y η)
          V c X l h6
    exact hKc v Ψ K Y k c X (A v) (H v) B (max M₁ M₂) hv.1 hv.2 hk hconv hslope hBo h0B (hdomA v hv)
      (hdomH v hv) hfam (fun j l hj => hObs Ψ K Y hconv hslope j (c ∘ l) (X ∘ l) hj (fun i => hX (l i)))
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun v => iteratedFDeriv ℝ k (fun τ => gibbsMean μ (A v τ) (H v τ)) 0 (fun l => Pi.single l 1))
    (C := Kc * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c))) (fun v hv => by
      rw [Set.uIoc_of_le zero_le_one] at hv
      exact hpoint v ⟨hv.1.le, hv.2⟩)
  simpa using hb
theorem bondDeriv_of_no_bonds {j : ℕ} (g : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (c : Fin 0 → F.Site j × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv g W c X = g W := by apply _root_.YangMills.SharedProofs.p8307 <;> assumption
theorem cellSupDist_self (z : F.Cell) : cellSupDist z z = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem cellSupDist_triangle (x y z : F.Cell) : cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem isPseudoMetricOnBonds_chordBondDist : IsPseudoMetricOnBonds (chordBondDist F) where
  self b := by simp [chordBondDist, cellSupDist_self]
  symm b b' := by simp only [chordBondDist]; rw [cellSupDist_comm]
  triangle b b' b'' := by
    simp only [chordBondDist]
    exact_mod_cast cellSupDist_triangle _ _ _
end InteractionDensityOnTorus
open InteractionDensityOnTorus in
theorem InteractionDensityOnTorus.statement_holds (hJ : EventuallyInParametersCombines)
    (hDrawn : joinAtLoweredSmallnessConstantStatement)
    (hXb : CellExponentsBounded) (hCv : exponentConvexityStatement)
    (hObs : ExponentObservableBounds) (hBlk : CellMeanDerivBoundExists)
    (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedFamilyOnClosedBalls)
    (hMean : IntervalIntegralGibbsMeanDifferentiation) (hSub : IteratedDerivAlongSubfamily)
    (hClosed : ConvexClassClosure) (hFew : cellBondsCardStatement) :
    interactionDensityOnTorusStatement := by
  obtain ⟨join, -⟩ := hJ
  have h2 : EventuallyInParameters fun T => 2 ≤ T.n₀ := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨2, fun _ h => ⟨0, fun _ _ => ⟨0, fun _ _ => h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have key : ∀ T' : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters, ∃ Kc : ℝ, Odd T'.L → 0 < T'.κ → 0 < T'.chainParams.lam → 0 ≤ T'.Ct →
      ∃ Cq : ℕ → ℝ, ObservableBoundsWithConstants T'.L T'.κ T'.chainParams.lam T'.Ct Cq ∧ 0 ≤ Kc ∧
        CellMeanDerivBound (4 * T'.L ^ 4) T'.κ T'.chainParams.lam Cq Kc := by
    intro T'
    by_cases hc : Odd T'.L ∧ 0 < T'.κ ∧ 0 < T'.chainParams.lam ∧ 0 ≤ T'.Ct
    · obtain ⟨h1, h2, h3, h4⟩ := hc
      obtain ⟨Cq, hCq, hO⟩ := hObs T'.L T'.κ T'.chainParams.lam T'.Ct h1 h2 h3 h4
      obtain ⟨Kc, hK0, hK⟩ := hBlk (4 * T'.L ^ 4) T'.κ T'.chainParams.lam Cq h2 h3 hCq
      exact ⟨Kc, fun _ _ _ _ => ⟨Cq, hO, hK0, hK⟩⟩
    · exact ⟨0, fun a b c d => absurd ⟨a, b, c, d⟩ hc⟩
  choose Gk hGk using key
  refine hDrawn (fun T => 2 ≤ T.n₀ ∧ CellExponentsBoundedAt T) ExponentsConvexAt _
    (fun T _ => Gk T) (join _ _ h2 hXb) hCv fun T c hc hL hn₁ hy hE hη hη' hκ hσ hchain hcut hG hP hR => ?_
  obtain ⟨hn₂, hB⟩ := hP
  intro t x hx f hf F hF Y V hV
  have hρ : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  have hx1 : 1 ≤ x := hy.trans hx
  have hlam : 0 < T.chainParams.lam := hchain.positivity.2.2.1
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
  have hE' : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
      CellExponentBounds false T.a T.chainParams.ρA T.ballRadius x T.κ T.Ct (frameRadius x) V' :=
    fun V' hV' => (hB t x F V' false hx hF hV').1
  have hs4 := (hB t x F V false hx hF hV).2
  have hEV := hE' V hV
  have hC0 : 0 ≤ T.Ct := by
    have h1 := hEV.deriv_top Y 0 0 Fin.elim0 Fin.elim0 (fun b => by simpa using hρ) (by norm_num)
      (fun l => l.elim0)
    have h2 : localSqNorm T.κ Y (0 : StepVariable (finiteCells F)) = 0 := by
      simp [localSqNorm]
    have h3 : bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) = 0 := by
      simp [bondSpan]
    rw [h2, h3] at h1
    have := (abs_nonneg _).trans h1
    simpa using this
  obtain ⟨Cq, hO, hK0, hK⟩ :=
    hGk { T with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 } hL hκ hlam hC0
  have hFL : F.blockSide = T.L := hF.1
  have hfew : ∀ z : F.Cell,
      (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤
        4 * T.L ^ 4 := by
    intro z
    rw [← hFL]
    exact hFew F (hFL ▸ hL) hFside z
  have hconvex := hR t x f F V false 0 hx hf hF hV le_rfl zero_le_one
  have hAt := fun {k : ℕ} (hk : k ≤ 3) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (hX : AreUnitVectors X) =>
    interactionDensity_bound_of_convex (a := T.a) (ρA := T.chainParams.ρA) (lam := T.chainParams.lam) (κ := T.κ)
      (C := T.Ct) (s := 5 / 4 * T.σ)
      (m := frameRadius x) (f := f) (N := 4 * T.L ^ 4) (Cq := Cq) (V := V) hρ hcut hfin hx1 hlam hκ hK0 hRim
      hDom hMean hSub hClosed hE' hV hconvex isPseudoMetricOnBonds_chordBondDist hfew
      (fun Ψ K Y' hc hs k c X hk hX => hO F T.a T.chainParams.ρA T.ballRadius x (frameRadius x) T.p V Ψ K Y' hFL
        hFside hρ hx1 hcut hEV (fun Y'' k' c' X' η hη => hs4 Y'' k' c' X' η hη) hc hs k c X hk hX)
      (fun v Ψ K Y' k c X A H B M hv0 hv1 hk hc hs hBo hB0 hdA hdH hfam hsz =>
        hK F T.a T.chainParams.ρA T.ballRadius x v (frameRadius x) T.p V Ψ K Y' k c X A H B M hρ (by linarith) hcut
          hv0 hv1 hk hfew hc hs hBo hB0 hdA hdH hfam hsz) Y hk c X hX
  have hGT := hG
  refine ⟨?_, fun k c X hk1 hk3 hX => ?_, ?_⟩
  · have h1 := (hAt (k := 0) (by norm_num) Fin.elim0 Fin.elim0 (fun l => l.elim0)).1
    rw [bondDeriv_of_no_bonds] at h1
    have h3 : bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) = 0 := by
      simp [bondSpan]
    rw [h3] at h1
    simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h1
    exact h1.trans hGT
  · exact (hAt hk3 c X hX).1.trans (mul_le_mul_of_nonneg_right hGT (Real.exp_pos _).le)
  · exact (hAt (k := 0) (by norm_num) Fin.elim0 Fin.elim0 (fun l => l.elim0)).2
end YangMills.Construction.ColdStepAtMirrorFrames
end
