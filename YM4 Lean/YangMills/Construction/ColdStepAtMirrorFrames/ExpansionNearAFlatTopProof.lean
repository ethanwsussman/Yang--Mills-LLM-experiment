import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import YangMills.Construction.ColdStepAtMirrorFrames.AxialGaugeOfATop
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAtANearFlatTop
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionNearAFlatTop
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionUnderAGaugeOfTheTopProof
import YangMills.Construction.ColdStepAtMirrorFrames.PlainChainAtLevelZeroProof
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages Interpolation
namespace ColdStepAtMirrorFrames
namespace NearFlatExpansion
open BlockOffsets
variable {F : BlockFrame}
def unitDist (a b : UnitQuaternion) : ℝ := ‖(a : ℍ[ℝ]) - (b : ℍ[ℝ])‖
theorem unitDist_mul_le (a a' b b' : UnitQuaternion) :
    unitDist (a * b) (a' * b') ≤ unitDist a a' + unitDist b b' := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.coe_mul_sub_mul_le <;> assumption
theorem unitDist_inv (a b : UnitQuaternion) : unitDist a⁻¹ b⁻¹ = unitDist a b := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
theorem unitDist_expUnit_mul_le (Z : imaginaryQuaternions) (a : UnitQuaternion) :
    unitDist (expUnit Z * a) a ≤ ‖Z‖ := by
  unfold unitDist
  have e : ((expUnit Z * a : UnitQuaternion) : ℍ[ℝ]) - (a : ℍ[ℝ]) =
      (((expUnit Z : UnitQuaternion) : ℍ[ℝ]) - 1) * (a : ℍ[ℝ]) := by
    have h1 : ((expUnit Z * a : UnitQuaternion) : ℍ[ℝ]) =
        ((expUnit Z : UnitQuaternion) : ℍ[ℝ]) * (a : ℍ[ℝ]) := rfl
    rw [h1]
    noncomm_ring
  rw [e, norm_mul, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.norm_coe_unitQuaternion, mul_one]
  exact _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le Z
theorem plaquetteDefect_leftTranslate_le {j : ℕ} (V : F.GaugeField j)
    (Z : F.Site j → Fin 4 → imaginaryQuaternions) (q : ℝ) (hq : ∀ y i, ‖Z y i‖ ≤ q)
    (p : F.Site j × Fin 4 × Fin 4) : plaquetteDefect (leftTranslate Z V) p ≤ plaquetteDefect V p + 4 * q := by
  obtain ⟨x, μ, ν⟩ := p
  have e1 : x + unitStep j μ + unitStep j ν - unitStep j μ = x + unitStep j ν := by abel
  have e2 : x + unitStep j μ + unitStep j ν + -unitStep j μ = x + unitStep j ν := by abel
  have e5 : x + unitStep j ν - unitStep j ν = x := by abel
  have hp : ∀ U : F.GaugeField j, plaquetteHolonomy U (x, μ, ν) =
      U x μ * (U (x + unitStep j μ) ν * ((U (x + unitStep j ν) μ)⁻¹ * (U x ν)⁻¹)) := by
    intro U
    simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
      if_false, e1, e2, e5, mul_one]
  have a1 : unitDist (leftTranslate Z V x μ) (V x μ) ≤ q :=
    (unitDist_expUnit_mul_le (Z x μ) (V x μ)).trans (hq _ _)
  have a2 : unitDist (leftTranslate Z V (x + unitStep j μ) ν) (V (x + unitStep j μ) ν) ≤ q :=
    (unitDist_expUnit_mul_le (Z (x + unitStep j μ) ν) (V (x + unitStep j μ) ν)).trans (hq _ _)
  have a3 : unitDist (leftTranslate Z V (x + unitStep j ν) μ)⁻¹ (V (x + unitStep j ν) μ)⁻¹ ≤ q := by
    rw [unitDist_inv]
    exact (unitDist_expUnit_mul_le (Z (x + unitStep j ν) μ) (V (x + unitStep j ν) μ)).trans (hq _ _)
  have a4 : unitDist (leftTranslate Z V x ν)⁻¹ (V x ν)⁻¹ ≤ q := by
    rw [unitDist_inv]
    exact (unitDist_expUnit_mul_le (Z x ν) (V x ν)).trans (hq _ _)
  have c3 := unitDist_mul_le _ _ _ _ |>.trans (add_le_add a3 a4)
  have c2 := unitDist_mul_le _ _ _ _ |>.trans (add_le_add a2 c3)
  have c1 := unitDist_mul_le _ _ _ _ |>.trans (add_le_add a1 c2)
  rw [← hp, ← hp] at c1
  have h := norm_sub_le_norm_sub_add_norm_sub
    ((plaquetteHolonomy (leftTranslate Z V) (x, μ, ν) : UnitQuaternion) : ℍ[ℝ])
    ((plaquetteHolonomy V (x, μ, ν) : UnitQuaternion) : ℍ[ℝ]) 1
  unfold unitDist at c1
  show ‖((plaquetteHolonomy (leftTranslate Z V) (x, μ, ν) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
    ‖((plaquetteHolonomy V (x, μ, ν) : UnitQuaternion) : ℍ[ℝ]) - 1‖ + 4 * q
  linarith
theorem eventually_isSmallCurvature_leftTranslate {k : ℕ} (hper : ∀ i, F.period F.top i ≠ 0)
    (V : F.GaugeField F.top) {s : ℝ} (hV : IsSmallCurvature s V)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) :
    ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by
  have hfin : Finite (F.Site F.top × Fin 4 × Fin 4) := by
    have : ∀ i, NeZero (F.period F.top i) := fun i => ⟨hper i⟩
    have h1 : Finite (F.Site F.top) := by
      have : ∀ i, Finite (ZMod (F.period F.top i)) := fun i => inferInstance
      exact Pi.finite
    infer_instance
  have hsp : ∀ (τ : Fin k → ℝ) y i, ‖bondSpread c X τ y i‖ ≤ k * ‖τ‖ := by
    intro τ y i
    unfold bondSpread
    refine (norm_sum_le _ _).trans ?_
    have : ∀ l ∈ Finset.univ, ‖if c l = (y, i) then τ l • X l else 0‖ ≤ ‖τ‖ := fun l _ => by
      split_ifs
      · rw [norm_smul, hX l, mul_one]
        exact norm_le_pi_norm τ l
      · simp
    simpa using Finset.sum_le_card_nsmul _ _ _ this
  exact show ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), ∀ p : F.Site F.top × Fin 4 × Fin 4, p.2.1 < p.2.2 →
      plaquetteDefect (leftTranslate (bondSpread c X τ) V) p < s from by
    refine Filter.eventually_all.mpr fun p => ?_
    by_cases hp : p.2.1 < p.2.2
    · have hc := hV p hp
      have hε : 0 < (s - plaquetteDefect V p) / (8 * ((k : ℝ) + 1)) := by
        have : 0 < s - plaquetteDefect V p := by linarith
        positivity
      have hb := Metric.ball_mem_nhds (0 : Fin k → ℝ) hε
      refine Filter.eventually_of_mem hb fun τ hτ => fun _ => ?_
      have hτ' : ‖τ‖ < (s - plaquetteDefect V p) / (8 * ((k : ℝ) + 1)) := by simpa using hτ
      have h1 := plaquetteDefect_leftTranslate_le V (bondSpread c X τ) _ (hsp τ) p
      have h2 : (k : ℝ) * ‖τ‖ ≤ (s - plaquetteDefect V p) / 8 := by
        rw [lt_div_iff₀ (by positivity)] at hτ'
        have hn := norm_nonneg τ
        nlinarith
      have : 0 < s - plaquetteDefect V p := by linarith
      linarith
    · exact Filter.Eventually.of_forall fun τ h => absurd h hp
theorem plaquetteHolonomy_gaugeTransform {j : ℕ} (γ : F.Site j → UnitQuaternion) (V : F.GaugeField j)
    (x : F.Site j) (μ ν : Fin 4) :
    plaquetteHolonomy (gaugeTransform γ V) (x, μ, ν) = γ x * plaquetteHolonomy V (x, μ, ν) * (γ x)⁻¹ := by apply _root_.YangMills.SharedProofs.p16452 <;> assumption
theorem isSmallCurvature_gaugeTransform {s : ℝ} (γ : F.Cell → UnitQuaternion) (V : F.GaugeField F.top)
    (hV : IsSmallCurvature s V) : IsSmallCurvature s (gaugeTransform γ V) := by
  rintro ⟨x, μ, ν⟩ hp
  have h := hV (x, μ, ν) hp
  show _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne _ < s
  rw [plaquetteHolonomy_gaugeTransform, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_conj]
  exact h
theorem norm_adjointAction (g : UnitQuaternion) (X : imaginaryQuaternions) : ‖adjointAction g X‖ = ‖X‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction <;> assumption
theorem expansionNearFlatAt_of_centred (hAx : AxialGaugeBondBound) (hG : GaugeCovarianceOfFrame)
    (hends : interpolationAtEndpoints) {T : StepParameters} {R : ℕ} (hd : T.IsOrdered) (hR : 4 * R + 8 ≤ T.n₀)
    (hfb : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFramesControlledAt T t x)
    (hft : FrameBoundsForParameters T)
    (hbody : CentredExpansionNearUniformTopAt T R) : ExpansionNearFlatAt T := by
  classical
  intro t x f F V hx hf hF hV star
  obtain ⟨hFL, _, n, hsn, hnn⟩ := id hF
  have hLp : 0 < T.L := hd.odd_L.pos
  have hlow : IsCubicTorusAbove T.L t T.n₀ F :=
    ⟨hFL, by assumption, n, hsn, hnn.trans (Nat.le_mul_of_pos_right n hLp)⟩
  have hs : ∀ i, 2 * R + 2 < F.extent i := fun i => by rw [hsn i]; omega
  have hperN : ∀ i, F.period F.top i ≠ 0 := fun i => by
    rw [period_top]
    have := hs i
    omega
  have hσ := hd.σ_pos
  obtain ⟨Cf, C, _, _, _, _, _, _, _, _, _, _, _, _, _, hFH⟩ := hft
  have hs0 : 0 ≤ segmentEnd star := by unfold segmentEnd; split_ifs <;> norm_num
  have hs1 : segmentEnd star ≤ 1 := by unfold segmentEnd; split_ifs <;> norm_num
  have hturn : ∀ (γ : F.Cell → UnitQuaternion) (V₁ : F.GaugeField F.top), IsSmallCurvature (5 / 4 * T.σ) V₁ →
      ∀ (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ T.σ / 64) → ∀ y : F.Site F.depth,
      centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y (adjointStepVariable γ η) (gaugeTransform γ V₁) =
        centredExpansion star T.a T.chainParams.ρA (frameRadius x) f y η V₁ := by
    intro γ V₁ hV₁ η hη y
    have hsm := (hFH t x F V₁ hx hF hV₁).2.1 star
    have hcov : ∀ b ∈ chordBonds (finiteCells F),
        stepFrame star T.a T.chainParams.ρA (frameRadius x) b (gaugeTransform γ V₁) =
          adjointAction (γ (enclosingCell b.1)) (stepFrame star T.a T.chainParams.ρA (frameRadius x) b V₁) :=
      fun b hb => Subtype.ext (hsm.gauge_covariant b hb γ)
    have h1 := hG.1 F (fun b V' => stepFrame star T.a T.chainParams.ρA (frameRadius x) b V') V₁ γ η
      (by rw [hFL]; exact hd.odd_L) (fun i => by have := hs i; omega) hcov
    have hbet := ((hfb t x hx).single F V₁ (segmentEnd star) hF hV₁ hs0 hs1).2
    obtain ⟨_, _, h3, -⟩ := hends F star T.a T.chainParams.ρA 0 0 0 (frameRadius x) V₁
    have hcold : IsSmallCurvature T.σ (fieldAboveFrame star T.a T.chainParams.ρA (frameRadius x) V₁ η) := by
      have := hbet.small_curvature_nearby η hη
      rw [h3 η] at this
      exact fun p hp => (this p hp).trans (by linarith)
    show subtractTrivial f F y
        (fieldAboveFrame star T.a T.chainParams.ρA (frameRadius x) (gaugeTransform γ V₁) (adjointStepVariable γ η)) =
      subtractTrivial f F y (fieldAboveFrame star T.a T.chainParams.ρA (frameRadius x) V₁ η)
    have h2 : fieldAboveFrame star T.a T.chainParams.ρA (frameRadius x) (gaugeTransform γ V₁)
        (adjointStepVariable γ η) =
        gaugeTransform (fun x' => γ (enclosingCell x'))
          (fieldAboveFrame star T.a T.chainParams.ρA (frameRadius x) V₁ η) := h1
    rw [h2]
    show f F y _ - _ = f F y _ - _
    rw [hf.gauge_invariant F hlow y _ _ hcold]
  have hblock : ∀ (γ : F.Cell → UnitQuaternion) (V₁ : F.GaugeField F.top), IsSmallCurvature (5 / 4 * T.σ) V₁ →
      ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ T.σ / 64) →
      cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y (adjointStepVariable γ η) (gaugeTransform γ V₁) =
        cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y η V₁ := fun γ V₁ hV₁ Y η hη => by
    unfold cellCentredExpansion
    exact Finset.sum_congr rfl fun y _ => hturn γ V₁ hV₁ η hη y
  have hnear : ∀ Y : F.Cell, IsNearUniformAbout (5 / 4 * T.σ) R (gaugeTransform (axialGaugeHolonomy V Y) V) Y := by
    intro Y r b hr hb
    have := hAx F V Y (5 / 4 * T.σ) r (fun i => by have := hs i; omega) (by positivity) hV b hb
    push_cast at this ⊢
    exact this
  have hV' : ∀ Y : F.Cell, IsSmallCurvature (5 / 4 * T.σ) (gaugeTransform (axialGaugeHolonomy V Y) V) :=
    fun Y => isSmallCurvature_gaugeTransform _ V hV
  have hfull := fun Y => hbody t x f F (gaugeTransform (axialGaugeHolonomy V Y) V) hx hf hF (hV' Y) star Y (hnear Y)
  have hball : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ < T.ballRadius) →
      ∀ b, ‖adjointStepVariable (axialGaugeHolonomy V Y) η b‖ < T.ballRadius := fun Y η hη b => by
    rw [hG.2.2 F _ η b]
    exact hη b
  have hcarry : ∀ {k : ℕ} (Y : F.Cell) (η : StepVariable (finiteCells F)) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ < T.ballRadius) → AreUnitVectors X →
      bondDeriv (cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y η) V c X =
        bondDeriv (cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y
            (adjointStepVariable (axialGaugeHolonomy V Y) η))
          (gaugeTransform (axialGaugeHolonomy V Y) V) c (axialGaugeRotated V Y c X) := by
    intro k Y η c X hη hX
    refine hG.2.1 F F.top k _ _ V (axialGaugeHolonomy V Y) c X ?_
    refine (eventually_isSmallCurvature_leftTranslate hperN V hV c X hX).mono fun τ hτ => ?_
    exact hblock _ _ hτ Y η fun b => (hη b).le
  refine ⟨fun Y η hη => ?_, fun Y η c X hη hX hc => ?_, fun Y η c X hη hX hc => ?_⟩
  · have e := hblock (axialGaugeHolonomy V Y) V hV Y η fun b => (hη b).le
    rw [← e]
    exact (hfull Y).1 _ (hball Y η hη)
  · rw [hcarry Y η c X hη hX]
    exact (hfull Y).2.1 _ c _ (hball Y η hη) (fun l => by
      show ‖adjointAction _ _‖ = 1
      rw [norm_adjointAction]
      exact hX l) hc
  · rw [hcarry Y η c X hη hX]
    exact (hfull Y).2.2 _ c _ (hball Y η hη) (fun l => by
      show ‖adjointAction _ _‖ = 1
      rw [norm_adjointAction]
      exact hX l) hc
end NearFlatExpansion
open NearFlatExpansion
theorem expansionNearFlat_holds (hAx : AxialGaugeBondBound) (hG : GaugeCovarianceOfFrame)
    (hends : interpolationAtEndpoints) (hfb : interpolatedFramesControlled)
    (hft : FrameBoundsEventually) (hN : CentredExpansionNearUniformTop) (hj : EventuallyInParametersCombines) :
    ExpansionNearFlat := by
  refine hj.2 _ _ (fun T hd h => ?_) (hj.1 _ _ hN (hj.1 _ _ hfb hft))
  obtain ⟨⟨R, hR, hb⟩, h1, h2⟩ := h
  exact expansionNearFlatAt_of_centred hAx hG hends hd hR h1 h2 hb
end ColdStepAtMirrorFrames
end YangMills.Construction
end
