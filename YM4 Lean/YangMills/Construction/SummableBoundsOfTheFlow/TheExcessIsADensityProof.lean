import YangMills.Construction.ColdStepAtMirrorFrames.FramesAreSmallProof
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOfAnExpansionIsInvariant
import YangMills.Construction.SummableBoundsOfTheFlow.TheBirthsBetween
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreNearTheirLimitsProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessIsADensity
import YangMills.Construction.SummableBoundsOfTheFlow.TheFramesBetween
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceIsAFamilyBelow
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation Estimates TorusComparison FamilyNorms ReferenceDensity
  MeasureTheory Set
namespace StepDensities
variable {F : BlockFrame}
private theorem bondDeriv_fin_zero (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G V c X = G V := by apply _root_.YangMills.SharedProofs.p1654 <;> assumption
private theorem isSmallCurvature_gaugeTransform {j : ℕ} {s : ℝ} (γ : F.Site j → UnitQuaternion)
    {X : F.GaugeField j} (hX : IsSmallCurvature s X) : IsSmallCurvature s (gaugeTransform γ X) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SmallFrames.isSmallCurvature_gaugeTransform <;> assumption
private theorem isSmallCurvature_translateField {j : ℕ} {s : ℝ} (u : F.Site j) {X : F.GaugeField j}
    (hX : IsSmallCurvature s X) : IsSmallCurvature s (translateField u X) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SmallFrames.isSmallCurvature_translateField <;> assumption
private theorem coordsAboveFrame_index (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    coordsAboveFrame true a ρ m V η = coordsAboveFrame true a ρ 0 V η := by
  funext x i
  simp [coordsAboveFrame, stepFrame]
private theorem fieldAboveFrame_index (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    fieldAboveFrame true a ρ m V η = fieldAboveFrame true a ρ 0 V η := by
  unfold fieldAboveFrame
  rw [coordsAboveFrame_index]
private theorem centredExpansion_index (a ρ : ℝ) (m : ℕ) (f : LocalFamily) (y : F.Site F.depth)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    centredExpansion true a ρ m f y η V = centredExpansion true a ρ 0 f y η V := by
  unfold centredExpansion
  rw [fieldAboveFrame_index]
private theorem stepExponent_index (a ρ x : ℝ) (m : ℕ) (f : LocalFamily) (ν : ℝ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    stepExponent true a ρ x m f ν V η = stepExponent true a ρ x 0 f ν V η := by
  unfold stepExponent
  simp only [coordsAboveFrame_index a ρ m, fieldAboveFrame_index a ρ m, centredExpansion_index a ρ m]
abbrev _root_.YangMills.SharedProofs.p27308 := @stepExponent_index
private theorem cellExponent_index (a ρ x : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    cellExponent true a ρ x m Y V η = cellExponent true a ρ x 0 Y V η := by
  unfold cellExponent
  simp only [coordsAboveFrame_index a ρ m, fieldAboveFrame_index a ρ m]
private theorem centredExpansion_smul (a ρ ν : ℝ) (f : LocalFamily) (y : F.Site F.depth) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    centredExpansion true a ρ 0 (ν • f) y η V = ν * centredExpansion true a ρ 0 f y η V := by
  unfold centredExpansion subtractTrivial
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
private theorem stepExponent_smul (a ρ x ν : ℝ) (f : LocalFamily) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    stepExponent true a ρ x 0 (ν • f) 1 V η = stepExponent true a ρ x 0 f ν V η := by
  unfold stepExponent
  simp only [centredExpansion_smul, one_mul, Finset.mul_sum]
private theorem interactionDensity_eq_birth (hE : interpolationAtEndpoints) (T : StepParameters) (x : ℝ)
    (f : LocalFamily) (Y : F.Cell) (V : F.GaugeField F.top) :
    interactionDensity true T.a T.ρA T.ballRadius T.lam x 0 T.p f Y V = interpolatedBirthAt T x 0 F Y V := by
  have hτ : ∀ τ : ℝ, cutoffMean T.ballRadius T.p
        (weightLawExponent 0 T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) τ V)
        (cellExponentRemainder 0 T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) Y V) =
      cutoffMean T.ballRadius T.p
        (fun η => τ * stepExponent true T.a T.chainParams.ρA x 0 f 0 V η +
          (1 - τ) * totalQuadratic T.chainParams.lam x η)
        (fun η => cellExponent true T.a T.chainParams.ρA x 0 Y V η - cellQuadratic T.chainParams.lam x Y η) := by
    intro τ
    obtain ⟨-, -, -, -, h5, -, h7⟩ := hE F true T.a T.chainParams.ρA T.chainParams.lam x τ (frameRadius x) V
    simp only [segmentEnd, if_true] at h5 h7
    have e1 : weightLawExponent 0 T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) τ V =
        fun η => τ * stepExponent true T.a T.chainParams.ρA x 0 f 0 V η +
          (1 - τ) * totalQuadratic T.chainParams.lam x η := by
      funext η
      rw [h7 f η, stepExponent_index]
    have e2 : cellExponentRemainder 0 T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) Y V =
        fun η => cellExponent true T.a T.chainParams.ρA x 0 Y V η - cellQuadratic T.chainParams.lam x Y η := by
      funext η
      unfold cellExponentRemainder
      rw [h5 Y η, cellExponent_index]
    rw [e1, e2]
  show (-∫ τ in (0 : ℝ)..1, cutoffMean T.ballRadius T.p
      (fun η => τ * stepExponent true T.a T.chainParams.ρA x 0 f 0 V η +
        (1 - τ) * totalQuadratic T.chainParams.lam x η)
      (fun η => cellExponent true T.a T.chainParams.ρA x 0 Y V η - cellQuadratic T.chainParams.lam x Y η)) =
    -∫ τ in (0 : ℝ)..1, cutoffMean T.ballRadius T.p
      (weightLawExponent 0 T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) τ V)
      (cellExponentRemainder 0 T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) Y V)
  simp only [hτ]
private theorem expansionDensity_eq_integral (a ρA ρ x : ℝ) (p : ℝ → ℝ) (f : LocalFamily) (Y : F.Cell)
    (V : F.GaugeField F.top) :
    expansionDensity true a ρA ρ x 0 p f Y V =
      ∫ ν in (0 : ℝ)..1, conditionalExpansionMean true a ρA ρ x 0 p (ν • f) f F Y V := by
  unfold expansionDensity conditionalExpansionMean
  apply intervalIntegral.integral_congr
  intro ν _
  have e : stepExponent true a ρA x 0 (ν • f) 1 V = stepExponent true a ρA x 0 f ν V :=
    funext fun η => stepExponent_smul a ρA x ν f V η
  simp only [e]
private theorem eq_zero_of_abs_le_inv {c C y : ℝ} (h : ∀ x, y ≤ x → 0 < x → |c| ≤ C * x⁻¹) : c = 0 := by
  by_contra hc
  have hc' : 0 < |c| := abs_pos.mpr hc
  set x : ℝ := max (max y 1) ((C + 1) / |c|) with hxdef
  have hx1 : 1 ≤ x := (le_max_right _ _).trans (le_max_left _ _)
  have hx0 : 0 < x := by linarith
  have h1 := h x ((le_max_left _ _).trans (le_max_left _ _)) hx0
  have h2 : C + 1 ≤ x * |c| := (div_le_iff₀ hc').mp (le_max_right _ _)
  have h3 : |c| * x ≤ C := by
    have hm := mul_le_mul_of_nonneg_right h1 hx0.le
    rwa [mul_assoc, inv_mul_cancel₀ hx0.ne', mul_one] at hm
  nlinarith
theorem densityExcess_isLocalDensity (hS : densityExcessSmallStatement)
    (hB : interpolatedBirthBoundsStatement) (hFr : interpolatedFramesStatement)
    (hE : interpolationAtEndpoints) (hI : conditionalExpansionMeanInvariantStatement)
    (hR : localReferenceBoundedFamily) (hCh : chartEquivarianceStatement) :
    densityExcessIsLocalDensity := by
  obtain ⟨Cq, Cz, Cr, hFr⟩ := hFr
  unfold densityExcessSmallStatement EventuallyOrdered at hS
  unfold localReferenceBoundedFamily EventuallyOrdered at hR
  unfold interpolatedBirthBoundsStatement at hB
  unfold densityExcessIsLocalDensity EventuallyOrdered
  have hn₂ : EventuallyInParameters fun T => 2 ≤ T.n₀ := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨2, fun _ h => ⟨0, fun _ _ => ⟨0, fun _ _ => h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine EventuallyInParameters.mono (EventuallyInParameters.and (EventuallyInParameters.and hS hR)
    (EventuallyInParameters.and (EventuallyInParameters.and hB hFr) hn₂)) ?_
  rintro T ⟨⟨cS, cR⟩, ⟨cB, cF⟩, hn⟩ hD h1 hroom
  obtain ⟨y₀, C, hy₀, hC, gS⟩ := cS hD h1 hroom
  obtain ⟨e, he⟩ := cR hD h1 hroom
  have hσ : 0 < T.σ := hD.σ_pos
  have hκ : 0 < T.κ := hD.κ_pos
  have hcold : ∀ {F : BlockFrame} {V : F.GaugeField F.top}, IsSmallCurvature (9 / 8 * T.σ) V →
      IsSmallCurvature (5 / 4 * T.σ) V := fun hV p hp => (hV p hp).trans (by linarith)
  refine ⟨max y₀ T.coupling, lt_max_of_lt_left hy₀, fun t x hx => ?_⟩
  set f : LocalFamily := T.localReference t with hf
  have hfam : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f := (he t).1
  have hsmall : ∀ (x' : ℝ), y₀ ≤ x' → ∀ (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top),
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 < x' →
      |densityExcess T t x' F Y V| ≤ C * x'⁻¹ := by
    intro x' hx' F Y V hF hV hx0
    have h := (gS t x' hx' F Y V hF hV).2 0 Fin.elim0 Fin.elim0 (by norm_num) fun l => l.elim0
    rw [bondDeriv_fin_zero] at h
    refine h.trans ?_
    have hexp : Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hnn : 0 ≤ T.κ / 2 ^ 6 * (bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) : ℝ) := by positivity
      linarith
    have hcx : 0 ≤ C * x'⁻¹ := by positivity
    exact mul_le_of_le_one_right hcx hexp
  have keep : ∀ (F : BlockFrame) (Y Y' : F.Cell) (V V' : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
      (∀ x' : ℝ, T.coupling ≤ x' →
        interactionDensity true T.a T.ρA T.ballRadius T.lam x' 0 T.p f Y' V' +
            expansionDensity true T.a T.ρA T.ballRadius x' 0 T.p f Y' V' =
          interactionDensity true T.a T.ρA T.ballRadius T.lam x' 0 T.p f Y V +
            expansionDensity true T.a T.ρA T.ballRadius x' 0 T.p f Y V) →
      densityExcess T t x F Y' V' = densityExcess T t x F Y V := by
    intro F Y Y' V V' hF hV hV' hsame
    set D : F.Cell → F.GaugeField F.top → ℝ := fun Z W =>
      stepDensity T.a T.ρA T.lam Z W + cellCentredExpansion true T.a T.ρA 0 f Z 0 W with hDdef
    have hform : ∀ (x' : ℝ) (Z : F.Cell) (W : F.GaugeField F.top), densityExcess T t x' F Z W =
        interactionDensity true T.a T.ρA T.ballRadius T.lam x' 0 T.p f Z W +
          expansionDensity true T.a T.ρA T.ballRadius x' 0 T.p f Z W - D Z W := by
      intro x' Z W
      simp only [hDdef, densityExcess, ← hf]
      ring
    have hD0 : D Y' V' - D Y V = 0 := by
      refine eq_zero_of_abs_le_inv (C := 2 * C) (y := max y₀ T.coupling) fun x' hx' hx0 => ?_
      have b₁ := hsmall x' ((le_max_left _ _).trans hx') F Y V hF hV hx0
      have b₂ := hsmall x' ((le_max_left _ _).trans hx') F Y' V' hF hV' hx0
      rw [hform] at b₁ b₂
      rw [hsame x' ((le_max_right _ _).trans hx')] at b₂
      obtain ⟨l₁, u₁⟩ := abs_le.mp b₁
      obtain ⟨l₂, u₂⟩ := abs_le.mp b₂
      rw [abs_le]
      constructor <;> linarith
    rw [hform, hform, hsame x ((le_max_right _ _).trans hx)]
    linarith
  have lowOf : ∀ F : BlockFrame, IsCubicTopTorus T.L t T.n₀ F → IsCubicTorusAbove T.L t T.n₀ F := fun F hF => by
    obtain ⟨hFL, hFt, n, hside, hn'⟩ := hF
    exact ⟨hFL, hFt, n, hside, le_trans hn' (Nat.le_mul_of_pos_right n hD.odd_L.pos)⟩
  have means : ∀ (x' : ℝ), T.coupling ≤ x' → ∀ (F : BlockFrame) (V : F.GaugeField F.top),
      IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → ∀ ν : ℝ,
      (∀ (γ : F.Cell → UnitQuaternion) (Y : F.Cell),
        conditionalExpansionMean true T.a T.ρA T.ballRadius x' 0 T.p (ν • f) f F Y (gaugeTransform γ V) =
          conditionalExpansionMean true T.a T.ρA T.ballRadius x' 0 T.p (ν • f) f F Y V) ∧
      ∀ Y h' : F.Cell,
        conditionalExpansionMean true T.a T.ρA T.ballRadius x' 0 T.p (ν • f) f F (Y + h') (translateField h' V) =
          conditionalExpansionMean true T.a T.ρA T.ballRadius x' 0 T.p (ν • f) f F Y V := by
    intro x' hx' F V hF hV ν
    have one := (cF t x' hx').one_torus F V 0 hF hV le_rfl zero_le_one
    obtain ⟨hFL, -, n, hside, hn'⟩ := id hF
    have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
      rw [hside]
      exact hn.trans hn'
    have hodd : Odd F.blockSide := by
      rw [hFL]
      exact hD.odd_L
    have hLow := lowOf F hF
    have hfr : ∀ (W : F.GaugeField F.top) (b : F.Site F.depth × Fin 4),
        interpolatedFrame 0 T.a T.chainParams.ρA (frameRadius x') b W = stepFrame true T.a T.ρA 0 b W :=
      fun W b => by
        have e := (hE F true T.a T.chainParams.ρA T.chainParams.lam x' 0 (frameRadius x') W).1 b
        simp only [segmentEnd, if_true] at e
        rw [e]
        simp [stepFrame]
        rfl
    have habove : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        IsSmallCurvature T.σ (fieldAboveFrame true T.a T.ρA 0 V η) := fun η hη q hq => by
      have h2 := one.small.small_curvature_nearby η (fun b => (hη b).le) q hq
      have e := (hE F true T.a T.chainParams.ρA T.chainParams.lam x' 0 (frameRadius x') V).2.2.1 η
      simp only [segmentEnd, if_true] at e
      rw [e, fieldAboveFrame_index] at h2
      exact h2.trans (by linarith)
    have inv := hI F true T.a T.ρA x' T.ballRadius 0 T.p (ν • f) f V T.σ (hCh F T.a hodd hs2) habove hσ
      ⟨fun y W γ hW => by
          simp only [Pi.smul_apply]
          rw [hfam.gauge_invariant F hLow y W γ hW],
        fun y h' W hW => by
          simp only [Pi.smul_apply]
          rw [hfam.translation_invariant F hLow y h' W hW]⟩
      ⟨fun y W γ hW => hfam.gauge_invariant F hLow y W γ hW,
        fun y h' W hW => hfam.translation_invariant F hLow y h' W hW⟩
    refine ⟨fun γ Y => inv.1 γ Y fun b hb => Subtype.ext ?_, fun Y h' => inv.2 Y h' fun b hb => ?_⟩
    · have g := one.small.gauge_covariant b hb γ
      rw [hfr, hfr] at g
      exact g
    · have g := one.small.translation_invariant b hb h'
      rw [hfr, hfr] at g
      exact g
  refine ⟨fun F hF Y V hV => (gS t x ((le_max_left _ _).trans hx) F Y V hF (hcold hV)).1,
    fun F hF Y V γ hV => ?_, fun F hF Y h V hV => ?_⟩
  · have hV5 := hcold hV
    refine keep F Y Y V (gaugeTransform γ V) hF hV5 (isSmallCurvature_gaugeTransform γ hV5) fun x' hx' => ?_
    have hu : interactionDensity true T.a T.ρA T.ballRadius T.lam x' 0 T.p f Y (gaugeTransform γ V) =
        interactionDensity true T.a T.ρA T.ballRadius T.lam x' 0 T.p f Y V := by
      rw [interactionDensity_eq_birth hE T x' f Y (gaugeTransform γ V), interactionDensity_eq_birth hE T x' f Y V]
      exact (cB t x' 0 hx' le_rfl zero_le_one).isLocalDensity.gauge_invariant F hF Y V γ hV5
    have hs : expansionDensity true T.a T.ρA T.ballRadius x' 0 T.p f Y (gaugeTransform γ V) =
        expansionDensity true T.a T.ρA T.ballRadius x' 0 T.p f Y V := by
      rw [expansionDensity_eq_integral T.a T.ρA T.ballRadius x' T.p f Y (gaugeTransform γ V),
        expansionDensity_eq_integral T.a T.ρA T.ballRadius x' T.p f Y V]
      exact intervalIntegral.integral_congr fun ν _ => (means x' hx' F V hF hV5 ν).1 γ Y
    rw [hu, hs]
  · have hV5 := hcold hV
    refine keep F Y (Y + h) V (translateField h V) hF hV5 (isSmallCurvature_translateField h hV5) fun x' hx' => ?_
    have hu : interactionDensity true T.a T.ρA T.ballRadius T.lam x' 0 T.p f (Y + h) (translateField h V) =
        interactionDensity true T.a T.ρA T.ballRadius T.lam x' 0 T.p f Y V := by
      rw [interactionDensity_eq_birth hE T x' f (Y + h) (translateField h V),
        interactionDensity_eq_birth hE T x' f Y V]
      exact (cB t x' 0 hx' le_rfl zero_le_one).isLocalDensity.translation_invariant F hF Y h V hV5
    have hs : expansionDensity true T.a T.ρA T.ballRadius x' 0 T.p f (Y + h) (translateField h V) =
        expansionDensity true T.a T.ρA T.ballRadius x' 0 T.p f Y V := by
      rw [expansionDensity_eq_integral T.a T.ρA T.ballRadius x' T.p f (Y + h) (translateField h V),
        expansionDensity_eq_integral T.a T.ρA T.ballRadius x' T.p f Y V]
      exact intervalIntegral.integral_congr fun ν _ => (means x' hx' F V hF hV5 ν).2 Y h
    rw [hu, hs]
end StepDensities
end YangMills.Construction
end
