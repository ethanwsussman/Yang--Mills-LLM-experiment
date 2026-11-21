import YangMills.Construction.ColdStepAtMirrorFrames.SmoothOnATube
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfTheMeanOfASlope
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionOfTheMeanOfASlope
import YangMills.Construction.SummableBoundsOfTheFlow.FamilyExponentIsSmoothAlongTheFrames
import YangMills.Construction.SummableBoundsOfTheFlow.FromTheMirrorFramesToTheLeastFieldProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheBirthsBetweenProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheHigherDerivativesOfTheDensityOfTheStepProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion RealInnerProductSpace Topology
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation Estimates BlockMeans Cumulants
variable {F : BlockFrame}
namespace GapMeans
theorem leftTranslate_bondSpread_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (U : F.GaugeField F.top) :
    leftTranslate (ColdStepAtMirrorFrames.bondSpread c X 0) U = U := by apply _root_.YangMills.SharedProofs.p2043 <;> assumption
theorem eventually_isSmallCurvature_leftTranslate {k : ℕ} (hfin : Finite F.Cell) {s : ℝ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {U : F.GaugeField F.top}
    (hU : IsSmallCurvature s U) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0,
      IsSmallCurvature s (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) U) := by apply _root_.YangMills.Construction.InterpolatedBirths.eventually_isSmallCurvature_translate <;> assumption
theorem inner_toImaginary (v : BondVector) (w : imaginaryQuaternions) :
    ⟪((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]), (w : ℍ[ℝ])⟫ = ⟪v, _root_.YangMills.Construction.Interpolation.imaginaryCoords w⟫ := by apply _root_.YangMills.Construction.FrameInterpolationProof.inner_toImaginary <;> assumption
def imaginaryCoordsCLM : imaginaryQuaternions →L[ℝ] BondVector :=
  LinearMap.toContinuousLinearMap
    { toFun := _root_.YangMills.Construction.Interpolation.imaginaryCoords
      map_add' := fun u v => by
        ext i
        fin_cases i <;> simp [_root_.YangMills.Construction.Interpolation.imaginaryCoords]
      map_smul' := fun r u => by
        ext i
        fin_cases i <;> simp [_root_.YangMills.Construction.Interpolation.imaginaryCoords] }
theorem imaginaryCoordsCLM_apply (w : imaginaryQuaternions) : imaginaryCoordsCLM w = _root_.YangMills.Construction.Interpolation.imaginaryCoords w := rfl
def blockFrameGap (a ρA : ℝ) (m : ℕ) (Y : F.Cell) (U : F.GaugeField F.top) : StepVariable (finiteCells F) :=
  fun b => if enclosingCell b.1.1 = Y then _root_.YangMills.Construction.Interpolation.imaginaryCoords (frameGap a ρA m b.1 U) else 0
theorem blockGapObservable_eq (a ρA : ℝ) (m : ℕ) (p : ℝ → ℝ) (Y : F.Cell) (U : F.GaugeField F.top) :
    blockGapObservable a ρA m p Y U = fun η => cutoffSlopeAlong p (blockFrameGap a ρA m Y) η U := by
  funext η
  unfold blockGapObservable cutoffSlopeAlong cutoffSlope blockFrameGap
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [inner_toImaginary]
  · simp
theorem frameGap_eq_sub (a ρA : ℝ) (m : ℕ) (b : F.Site F.depth × Fin 4) (U : F.GaugeField F.top) :
    frameGap a ρA m b U = interpolatedFrame 1 a ρA m b U - interpolatedFrame 0 a ρA m b U := by
  simp [frameGap, interpolatedFrame]
theorem exists_ball_contDiffOn_bounded {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : ℕ}
    {f : (Fin K → ℝ) → E} (hf : ContDiffAt ℝ 3 f 0) :
    ∃ r M : ℝ, 0 < r ∧ ContDiffOn ℝ 3 f (Metric.ball 0 r) ∧ ∀ j, j ≤ 3 →
      ∀ τ ∈ Metric.ball (0 : Fin K → ℝ) r, ‖iteratedFDeriv ℝ j f τ‖ ≤ M := by
  obtain ⟨u, hu, hc⟩ := hf.contDiffOn (m := 3) le_rfl (by simp)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp hu
  have hc' : ContDiffOn ℝ 3 f (Metric.ball 0 r₀) := hc.mono hball
  have hK : IsCompact (Metric.closedBall (0 : Fin K → ℝ) (r₀ / 2)) := isCompact_closedBall _ _
  have hsub : Metric.closedBall (0 : Fin K → ℝ) (r₀ / 2) ⊆ Metric.ball 0 r₀ :=
    Metric.closedBall_subset_ball (by linarith)
  have hb : ∀ j : ℕ, j ≤ 3 → ∃ M, ∀ τ ∈ Metric.closedBall (0 : Fin K → ℝ) (r₀ / 2),
      ‖iteratedFDeriv ℝ j f τ‖ ≤ M := by
    intro j hj
    have hco0 : ContinuousOn (iteratedFDerivWithin ℝ j f (Metric.ball 0 r₀)) (Metric.ball 0 r₀) :=
      ContDiffOn.continuousOn_iteratedFDerivWithin hc' (by exact_mod_cast hj)
        Metric.isOpen_ball.uniqueDiffOn
    have hco : ContinuousOn (iteratedFDeriv ℝ j f) (Metric.ball 0 r₀) :=
      hco0.congr fun z hz => (iteratedFDerivWithin_of_isOpen j Metric.isOpen_ball hz).symm
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hco.mono hsub)
    exact ⟨M, hM⟩
  choose! M hM using hb
  refine ⟨r₀ / 2, ∑ j ∈ Finset.range 4, |M j|, by positivity,
    hc'.mono (Metric.ball_subset_ball (by linarith)), fun j hj τ hτ => ?_⟩
  refine ((hM j hj τ (Metric.ball_subset_closedBall hτ)).trans (le_abs_self _)).trans ?_
  exact Finset.single_le_sum (f := fun j => |M j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.mpr (by omega))
def tailCLM (k : ℕ) : (Fin (k + 1) → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + 1) => ℝ) i.succ
theorem tailCLM_cons {k : ℕ} (a : ℝ) (τ : Fin k → ℝ) : tailCLM k (Fin.cons a τ) = τ := by
  funext i
  simp [tailCLM]
theorem contDiffAt_comp_tail {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] {k : ℕ} {s₀ v : ℝ} {η : Q}
    {G : (Fin k → ℝ) × (ℝ × Q) → ℝ} (hG : ContDiffAt ℝ 3 G (0, s₀, η)) :
    ContDiffAt ℝ 3 (fun w : (Fin (k + 1) → ℝ) × (ℝ × Q) => G (tailCLM k w.1, s₀ + w.1 0, w.2.2)) (0, v, η) := by
  have hL : ContDiff ℝ 3 (fun w : (Fin (k + 1) → ℝ) × (ℝ × Q) =>
      ((tailCLM k w.1, s₀ + w.1 0, w.2.2) : (Fin k → ℝ) × (ℝ × Q))) := by
    refine ContDiff.prodMk ((tailCLM k).contDiff.comp contDiff_fst) (ContDiff.prodMk ?_ ?_)
    · exact contDiff_const.add ((contDiff_apply ℝ ℝ (0 : Fin (k + 1))).comp contDiff_fst)
    · exact contDiff_snd.comp contDiff_snd
  have h0 : ((tailCLM k ((0, v, η) : (Fin (k + 1) → ℝ) × (ℝ × Q)).1,
      s₀ + ((0, v, η) : (Fin (k + 1) → ℝ) × (ℝ × Q)).1 0,
      ((0, v, η) : (Fin (k + 1) → ℝ) × (ℝ × Q)).2.2) : (Fin k → ℝ) × (ℝ × Q)) = (0, s₀, η) := by simp
  have h2 : ContDiffAt ℝ 3 G ((tailCLM k ((0, v, η) : (Fin (k + 1) → ℝ) × (ℝ × Q)).1,
      s₀ + ((0, v, η) : (Fin (k + 1) → ℝ) × (ℝ × Q)).1 0,
      ((0, v, η) : (Fin (k + 1) → ℝ) × (ℝ × Q)).2.2)) := by
    rw [h0]
    exact hG
  exact ContDiffAt.comp (g := G) (0, v, η) h2 hL.contDiffAt
theorem contDiffAt_comp_cons {k : ℕ} {s₀ : ℝ} {M : (Fin (k + 1) → ℝ) → ℝ} (hM : ContDiffAt ℝ 3 M 0) :
    ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × ℝ => M (Fin.cons (q.2 - s₀) q.1)) (0, s₀) := by
  have hψ : ContDiff ℝ 3 (fun q : (Fin k → ℝ) × ℝ => (Fin.cons (q.2 - s₀) q.1 : Fin (k + 1) → ℝ)) := by
    refine contDiff_pi.mpr fun i => ?_
    refine Fin.cases ?_ (fun i' => ?_) i
    · simpa using contDiff_snd.sub contDiff_const
    · simpa [Function.comp_def] using (contDiff_apply ℝ ℝ i').comp
        (contDiff_fst (E := Fin k → ℝ) (F := ℝ))
  have hψ0 : (Fin.cons (((0, s₀) : (Fin k → ℝ) × ℝ).2 - s₀) ((0, s₀) : (Fin k → ℝ) × ℝ).1 :
      Fin (k + 1) → ℝ) = 0 := by
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i <;> simp
  have h3 : ContDiffAt ℝ 3 M (Fin.cons (((0, s₀) : (Fin k → ℝ) × ℝ).2 - s₀)
      ((0, s₀) : (Fin k → ℝ) × ℝ).1) := by
    rw [hψ0]
    exact hM
  exact ContDiffAt.comp (g := M) (0, s₀) h3 hψ.contDiffAt
theorem contDiffAt_ballExpectation_cutoffSlope_of (hDom : DominatedFamilyOnClosedBalls)
    (hSlp : cutoffSlopeMeanDerivFormulas) (hRim : CutoffMeanIsGibbsMean)
    (F : BlockFrame) {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) {k : ℕ}
    (Ex : (Fin k → ℝ) → ℝ → StepVariable (finiteCells F) → ℝ)
    (Ev : (Fin k → ℝ) → StepVariable (finiteCells F)) {s₀ : ℝ}
    (hj : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × (ℝ × StepVariable (finiteCells F)) => Ex q.1 q.2.1 q.2.2) (0, s₀, η))
    (he : ContDiffAt ℝ 3 Ev 0) :
    ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × ℝ => ballExpectation (cutoffFactor ρ p) (Ex q.1 q.2)
      (cutoffSlope p (Ev q.1))) (0, s₀) := by
  obtain ⟨hfin, hμ0, hμb, -⟩ := hRim F ρ p hρ hp
  haveI := hfin
  have hμc : ∀ᵐ η ∂cutoffLaw F ρ p, ∀ b, ‖η b‖ ≤ ρ := by
    filter_upwards [hμb] with η hη b using (hη b).le
  obtain ⟨r₁, M₁, h₁, d₁⟩ := hDom ↥(chordBonds (finiteCells F)) (k + 1) ρ (cutoffLaw F ρ p)
    (fun w => Ex (tailCLM k w.1) (s₀ + w.1 0) w.2.2) hμc
    (fun v η _ hη => contDiffAt_comp_tail (G := fun q => Ex q.1 q.2.1 q.2.2) (hj η hη))
  have hD := d₁ 0 (by simp)
  have hte : ContDiffAt ℝ 3 (fun z : Fin (k + 1) → ℝ => Ev (tailCLM k z)) 0 := by
    have h2 : ContDiffAt ℝ 3 Ev (tailCLM k 0) := by simpa using he
    exact ContDiffAt.comp (g := Ev) 0 h2 (tailCLM k).contDiff.contDiffAt
  obtain ⟨r₂, M₂, h₂, d₂, b₂⟩ := exists_ball_contDiffOn_bounded hte
  have hB : Metric.ball (0 : Fin (k + 1) → ℝ) (min r₁ r₂) ∈ 𝓝 (0 : Fin (k + 1) → ℝ) :=
    Metric.ball_mem_nhds _ (lt_min h₁ h₂)
  have hdomB : IsDominatedSmoothFamily (cutoffLaw F ρ p) 3 (Metric.ball 0 (min r₁ r₂)) (max M₁ M₂)
      (fun z η => Ex (tailCLM k z) (s₀ + z 0) η) := by
    refine ⟨fun τ hτ => hD.aestronglyMeasurable τ (Metric.ball_subset_ball (min_le_left _ _) hτ), ?_, ?_⟩
    · filter_upwards [hD.contDiffOn] with ω hω using hω.mono (Metric.ball_subset_ball (min_le_left _ _))
    · filter_upwards [hD.norm_iteratedFDeriv_le] with ω hω j hj' τ hτ using
        (hω j hj' τ (Metric.ball_subset_ball (min_le_left _ _) hτ)).trans (le_max_left _ _)
  have hM := (hSlp F ρ p (k + 1) (Metric.ball 0 (min r₁ r₂)) (max M₁ M₂)
    (fun z η => Ex (tailCLM k z) (s₀ + z 0) η) (fun z => Ev (tailCLM k z)) hρ hp Metric.isOpen_ball hdomB
    (d₂.mono (Metric.ball_subset_ball (min_le_right _ _)))
    (fun j hj' τ hτ => (b₂ j hj' τ (Metric.ball_subset_ball (min_le_right _ _) hτ)).trans
      (le_max_right _ _))).1.contDiffAt hB
  have h4 := contDiffAt_comp_cons (s₀ := s₀) hM
  refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
  show _ = ballExpectation (cutoffFactor ρ p) (fun η => Ex (tailCLM k (Fin.cons (q.2 - s₀) q.1))
    (s₀ + (Fin.cons (q.2 - s₀) q.1 : Fin (k + 1) → ℝ) 0) η)
    (cutoffSlope p (Ev (tailCLM k (Fin.cons (q.2 - s₀) q.1))))
  rw [tailCLM_cons, Fin.cons_zero, add_sub_cancel]
theorem contDiffAt_ballExpectation_cutoffSlope (hDom : DominatedFamilyOnClosedBalls)
    (hSlp : cutoffSlopeMeanDerivFormulas) (hRim : CutoffMeanIsGibbsMean) {ρ : ℝ} {p : ℝ → ℝ}
    (hρ : 0 < ρ) (hp : IsCutoff ρ p) {a ρA x : ℝ} {m : ℕ} {φ : LocalFamily} {U : F.GaugeField F.top}
    (Y : F.Cell) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {s₀ : ℝ}
    (hj : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × (ℝ × StepVariable (finiteCells F)) =>
        familyLawExponent q.2.1 a ρA x m φ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) U) q.2.2)
        (0, s₀, η))
    (he : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ =>
      blockFrameGap a ρA m Y (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) U)) 0) :
    ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × ℝ => ballExpectation (cutoffFactor ρ p)
      (familyLawExponent q.2 a ρA x m φ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) U))
      (cutoffSlope p (blockFrameGap a ρA m Y
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) U)))) (0, s₀) :=
  contDiffAt_ballExpectation_cutoffSlope_of hDom hSlp hRim F hρ hp
    (fun τ s η => familyLawExponent s a ρA x m φ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) U) η)
    (fun τ => blockFrameGap a ρA m Y (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) U)) hj he
def slopeMean (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (x : ℝ) (φ : LocalFamily) (Y : F.Cell) (U : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (q : (Fin k → ℝ) × ℝ) : ℝ :=
  ballExpectation (cutoffFactor T.ballRadius T.p)
    (familyLawExponent q.2 T.a T.chainParams.ρA x (frameRadius x) φ
      (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) U))
    (cutoffSlope T.p (blockFrameGap T.a T.chainParams.ρA (frameRadius x) Y
      (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) U)))
set_option maxHeartbeats 1600000 in
theorem gapMeansDominatedAt_of (hDom : DominatedFamilyOnClosedBalls) (hSlp : cutoffSlopeMeanDerivFormulas)
    (hRim : CutoffMeanIsGibbsMean) (hTube : UniformDerivBoundNearCompact)
    (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hT : T.IsOrdered) (h2 : 2 ≤ T.n₀) {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
    (hframes : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFrameBoundsAt T Cq Cz Cr t x)
    (hexp : familyLawExponentSmoothAt T) : GapMeansDominatedAt T := by
  classical
  intro t x φ F Y U k c X hx hφ hF hU
  have hD := hT
  have hσ := hD.σ_pos
  have hρ : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  have hfin : Finite F.Cell := by
    obtain ⟨-, -, n, hside, hn⟩ := hF
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      rw [hper, hside]
      omega⟩
    exact Pi.finite
  have hfr := fun (U' : F.GaugeField F.top) (hU' : IsSmallCurvature (5 / 4 * T.σ) U') (s' : ℝ) (a0 : 0 ≤ s')
    (a1 : s' ≤ 1) => (hframes t x hx).one_torus F U' s' hF hU' a0 a1
  have hev : ∀ U' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) U' → ∀ (k' : ℕ)
      (c' : Fin k' → F.Site F.top × Fin 4) (X' : Fin k' → imaginaryQuaternions),
      ContDiffAt ℝ 3 (fun τ : Fin k' → ℝ => blockFrameGap T.a T.chainParams.ρA (frameRadius x) Y
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c' X' τ) U')) 0 := by
    intro U' hU' k' c' X'
    have one0 := hfr U' hU' 0 le_rfl zero_le_one
    have one1 := hfr U' hU' 1 zero_le_one le_rfl
    refine contDiffAt_pi.mpr fun b => ?_
    by_cases hb : enclosingCell b.1.1 = Y
    · have a1 := one1.small.analytic b.1 b.2 k' c' X'
      have a0 := one0.small.analytic b.1 b.2 k' c' X'
      have e1 : (fun τ : Fin k' → ℝ => blockFrameGap T.a T.chainParams.ρA (frameRadius x) Y
          (leftTranslate (ColdStepAtMirrorFrames.bondSpread c' X' τ) U') b) =
          imaginaryCoordsCLM ∘ ((fun σ : Fin k' → ℝ => interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) b.1
            (rotatedField (BlockAverages.bondSpread c' X' σ) U')) -
            (fun σ : Fin k' → ℝ => interpolatedFrame 0 T.a T.chainParams.ρA (frameRadius x) b.1
            (rotatedField (BlockAverages.bondSpread c' X' σ) U'))) := by
        funext τ
        simp only [blockFrameGap, if_pos hb, Function.comp, imaginaryCoordsCLM_apply, Pi.sub_apply]
        rw [frameGap_eq_sub]
        rfl
      rw [e1]
      exact imaginaryCoordsCLM.contDiff.contDiffAt.comp 0 (a1.sub a0).contDiffAt
    · have e1 : (fun τ : Fin k' → ℝ => blockFrameGap T.a T.chainParams.ρA (frameRadius x) Y
          (leftTranslate (ColdStepAtMirrorFrames.bondSpread c' X' τ) U') b) = fun _ => 0 := by
        funext τ
        simp only [blockFrameGap, if_neg hb]
      rw [e1]
      exact contDiffAt_const
  have hJ : ∀ U' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) U' → ∀ (k' : ℕ)
      (c' : Fin k' → F.Site F.top × Fin 4) (X' : Fin k' → imaginaryQuaternions) (s₀ : ℝ),
      s₀ ∈ Set.Icc (0 : ℝ) 1 → ContDiffAt ℝ 3 (slopeMean T x φ Y U' c' X') (0, s₀) :=
    fun U' hU' k' c' X' s₀ hs =>
      contDiffAt_ballExpectation_cutoffSlope hDom hSlp hRim hρ hD.cutoff Y c' X'
        (fun η hη => hexp t x s₀ φ F U' k' c' X' η hx hs.1 hs.2 hφ hF hU' hη) (hev U' hU' k' c' X')
  have hgm : ∀ U' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) U' → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      gapObservableMean T x s φ Y U' = ballExpectation (cutoffFactor T.ballRadius T.p)
        (familyLawExponent s T.a T.chainParams.ρA x (frameRadius x) φ U')
        (cutoffSlope T.p (blockFrameGap T.a T.chainParams.ρA (frameRadius x) Y U')) := by
    intro U' hU' s hs
    unfold gapObservableMean
    rw [blockGapObservable_eq]
    rfl
  obtain ⟨r, M, hr, hTu⟩ := hTube k ℝ (slopeMean T x φ Y U c X) (Set.Icc 0 1) isCompact_Icc
    (fun s hs => hJ U hU k c X s hs)
  obtain ⟨r₀, hr₀, hcold⟩ :=
    Metric.eventually_nhds_iff_ball.mp (eventually_isSmallCurvature_leftTranslate hfin c X hU)
  refine ⟨min r r₀, M, lt_min hr hr₀, ?_⟩
  have sub₁ : Metric.ball (0 : Fin k → ℝ) (min r r₀) ⊆ Metric.ball 0 r :=
    Metric.ball_subset_ball (min_le_left _ _)
  have sub₂ : Metric.ball (0 : Fin k → ℝ) (min r r₀) ⊆ Metric.ball 0 r₀ :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hEq : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r₀,
      gapObservableMean T x s φ Y (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) U) =
        slopeMean T x φ Y U c X (τ, s) :=
    fun s hs τ hτ => hgm _ (hcold τ hτ) s hs
  refine ⟨fun τ hτ => ?_, ?_, ?_⟩
  · have hU' := hcold τ (sub₂ hτ)
    have hc : ContinuousOn (fun s => gapObservableMean T x s φ Y
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) U)) (Set.Icc 0 1) := by
      intro s hs
      have h1 := (hJ _ hU' 0 Fin.elim0 Fin.elim0 s hs).continuousAt
      have h2 : ContinuousAt (fun s' : ℝ => slopeMean T x φ Y
          (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) U) Fin.elim0 Fin.elim0 (0, s')) s :=
        ContinuousAt.comp (f := fun s' : ℝ => ((0 : Fin 0 → ℝ), s')) h1
          (continuous_const.prodMk continuous_id).continuousAt
      refine h2.continuousWithinAt.congr (fun s' hs' => ?_) ?_
      · rw [hgm _ hU' s' hs']
        simp only [slopeMean, leftTranslate_bondSpread_zero]
      · rw [hgm _ hU' s hs]
        simp only [slopeMean, leftTranslate_bondSpread_zero]
    exact hc.aestronglyMeasurable measurableSet_Icc
  · refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    exact ((hTu s hs).1.mono sub₁).congr fun τ hτ => hEq s hs τ (sub₂ hτ)
  · refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    intro j hj τ hτ
    have ev : (fun τ' : Fin k → ℝ => gapObservableMean T x s φ Y
        (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ') U)) =ᶠ[𝓝 τ]
        fun τ' => slopeMean T x φ Y U c X (τ', s) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hτ] with τ' hτ' using hEq s hs τ' (sub₂ hτ')
    rw [(ev.iteratedFDeriv ℝ j).self_of_nhds]
    exact (hTu s hs).2 j hj τ (sub₁ hτ)
theorem eventually_two_le_n₀ : EventuallyInParameters fun T => 2 ≤ T.n₀ := by apply _root_.YangMills.SharedProofs.p10519 <;> assumption
end GapMeans
open GapMeans in
theorem gapMeansDominated_of_parts (hframes : interpolatedFramesStatement)
    (hSm : FamilyLawExponentSmooth) (hJ : EventuallyInParametersCombines)
    (hDom : DominatedFamilyOnClosedBalls) (hSlp : cutoffSlopeMeanDerivFormulas)
    (hRim : CutoffMeanIsGibbsMean) (hTube : UniformDerivBoundNearCompact) :
    gapMeansDominated := by
  obtain ⟨Cq, Cz, Cr, hfb⟩ := hframes
  have j := hJ.1
  have J := j _ _ eventually_two_le_n₀ (j _ _ hfb hSm)
  refine hJ.2 _ _ (fun T hT h => ?_) J
  obtain ⟨h2, hf, hs⟩ := h
  exact gapMeansDominatedAt_of hDom hSlp hRim hTube T hT h2 hf hs
end YangMills.Construction
end
