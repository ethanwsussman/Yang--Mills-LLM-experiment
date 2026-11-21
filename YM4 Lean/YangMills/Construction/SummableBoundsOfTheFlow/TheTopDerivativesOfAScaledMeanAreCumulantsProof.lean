import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.SummableBoundsOfTheFlow.ACutIsSmoothThroughItsRim
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansAreTameMeansProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheTopDerivativesOfAScaledMeanAreCumulantsForm
import YangMills.Construction.SummableBoundsOfTheFlow.TheTopDerivativesOfATameMeanAreCumulants
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames Interpolation Cumulants
namespace ScaledVariables
variable {F : BlockFrame}
private theorem finite_cells (hF : ∀ i, F.extent i ≠ 0) : Finite F.Cell := by apply _root_.YangMills.Construction.ScaledVariables.TiltedMeans.finite_cell <;> assumption
private theorem mem_finiteCells (hF : ∀ i, F.extent i ≠ 0) (Y : F.Cell) : Y ∈ finiteCells F := by apply _root_.YangMills.SharedProofs.p16107 <;> assumption
private theorem sum_rescaledCellRemainder (hF : ∀ i, F.extent i ≠ 0) (a ρ lam l : ℝ) (V : F.GaugeField F.top)
    (ζ : StepVariable (finiteCells F)) :
    ∑ Y ∈ finiteCells F, rescaledCellRemainder a ρ lam l Y V ζ =
      (∑ Y ∈ finiteCells F, rescaledCellTerm a ρ l Y V ζ) - gaussianPart lam ζ := by apply _root_.YangMills.Construction.ScaledVariables.TiltedMeans.sum_rescaledCellRemainder <;> assumption
private theorem sum_rescaledCellExpansion (hF : ∀ i, F.extent i ≠ 0) (a ρ : ℝ) (f : LocalFamily) (l : ℝ)
    (V : F.GaugeField F.top) (ζ : StepVariable (finiteCells F)) :
    ∑ Y ∈ finiteCells F, rescaledCellExpansion a ρ f l Y V ζ =
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion true a ρ 0 f y (l • ζ) V := by apply _root_.YangMills.Construction.ScaledVariables.TiltedMeans.sum_rescaledCellExpansion <;> assumption
private theorem rescaledLawExponent_eq (hF : ∀ i, F.extent i ≠ 0) (a ρ lam : ℝ) (f : LocalFamily) (law : StepLaw)
    (l : ℝ) (V : F.GaugeField F.top) (ζ : StepVariable (finiteCells F)) :
    rescaledLawExponent a ρ lam f l V law ζ = gaussianPart lam ζ + -lawExponent a ρ lam f law l ζ V := by
  cases law with
  | tilted ν =>
    simp only [rescaledLawExponent, rescaledExponent, lawExponent, remainderCoefficient, expansionCoefficient]
    rw [sum_rescaledCellRemainder hF a ρ lam l V ζ, sum_rescaledCellExpansion hF]
    ring
  | interpolated τ =>
    simp only [rescaledLawExponent, rescaledExponent, lawExponent, remainderCoefficient, expansionCoefficient]
    rw [sum_rescaledCellRemainder hF a ρ lam l V ζ]
    unfold gaussianPart
    ring
private theorem iteratedFDeriv_const_add' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ) (g : E → ℝ)
    {n : ℕ} (hn : n ≠ 0) : iteratedFDeriv ℝ n (fun τ => a + g τ) = iteratedFDeriv ℝ n g := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  funext x
  have e : fderiv ℝ (fun τ => a + g τ) = fderiv ℝ g := funext fun y => fderiv_const_add a
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, e]
private theorem jointCumulant_congr {Ω α : Type} [DecidableEq α] (m : (Ω → ℝ) → ℝ) (S : Finset α)
    {f g : α → Ω → ℝ} (h : ∀ j ∈ S, f j = g j) : jointCumulant m S f = jointCumulant m S g := by
  unfold jointCumulant
  refine Finset.sum_congr rfl fun π _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun J hJ => ?_
  congr 1
  funext ω
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [h j (π.le hJ hj)]
private theorem IsTameOnScales.mono_bound {s ρ lo hi D D' : ℝ}
    {O : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    (h : IsTameOnScales s ρ lo hi D O) (hD : D ≤ D') : IsTameOnScales s ρ lo hi D' O :=
  ⟨h.contDiffAt, fun V' hV' k i c X l ζ ho hX h1 h2 hb => (h.deriv_le V' hV' k i c X l ζ ho hX h1 h2 hb).trans hD⟩
theorem topDerivsOfScaledMeanAreCumulants_holds (hA : tiltedMeanDerivEqCumulantsStatement)
    (hM : scaledMeansTameStatement) (hC : Estimates.CutoffWeightContDiff) :
    topDerivsOfScaledMeanAreCumulants := by
  unfold topDerivsOfScaledMeanAreCumulants ForallSmoothObservables
  refine EventuallyOrdered.mono hM ?_
  intro T hT hn g e
  obtain ⟨l₀, hl₀, g⟩ := g e
  refine ⟨l₀, 1, hl₀, one_pos, ?_⟩
  intro l₁ hl₁ hle t f F V Y law K Ob k c X hfam hTor hV hlaw hK hob hX hk l h0 h1
  have S := g l₁ hl₁ hle t f F law hfam hTor
  have hside : ∀ i, F.extent i ≠ 0 := by
    obtain ⟨-, -, m, hm, hm₀⟩ := hTor
    intro i
    rw [hm i]
    omega
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hlo : 0 < l / 2 := by positivity
  obtain ⟨D₁, hD₁, tA⟩ := S.exponent_tame (l / 2) hlo
  obtain ⟨D₂, hD₂, tO⟩ := S.observable_tame K Y Ob hK hob (l / 2) hlo
  have hq : Continuous (gaussianPart (F := F) T.lam) := by
    unfold gaussianPart
    fun_prop
  have hformula := (hA F (5 / 4 * T.σ) T.ballRadius (l / 2) (2 * l₁) (max D₁ D₂) l
    (cutoffWeight T.ballRadius T.p) (gaussianPart T.lam)
    (lawExponent T.a T.ρA T.lam f law) Ob V k c X hside hρ hlo (by linarith) (by linarith)
    (le_max_of_le_left hD₁) (hC T.ballRadius T.p hρ hT.cutoff)
    (fun x hx => by
      have h2 : max x 0 < T.ballRadius := max_lt hx hρ
      simp [cutoffWeight, cutoffFactor, h2, Real.exp_pos])
    (fun x hx => by
      have h2 : ¬ max x 0 < T.ballRadius := not_lt.2 (hx.trans (le_max_left _ _))
      simp only [cutoffWeight, cutoffFactor]
      rw [if_neg h2])
    hq (IsTameOnScales.mono_bound tA (le_max_left _ _)) (IsTameOnScales.mono_bound tO (le_max_right _ _))
    hV hX hk).2
  have hmean : ∀ H : StepVariable (finiteCells F) → ℝ,
      rescaledMean T.a T.ρA T.ballRadius T.lam l T.p f law V H =
        tiltedAverage (cutoffWeight T.ballRadius T.p) (gaussianPart T.lam) (lawExponent T.a T.ρA T.lam f law) l V H :=
    fun H => S.mean_eq V l (fun _ ζ _ => H ζ) hV h0 (by linarith)
  have e1 : bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l) V c X =
      bondDeriv (tiltedMean (cutoffWeight T.ballRadius T.p) (gaussianPart T.lam)
        (lawExponent T.a T.ρA T.lam f law) Ob l) V c X := by
    have hcold := ResponseInTheExpansion.eventually_isSmallCurvature_leftTranslate (finite_cells hside) c X hV
    have h3 : (fun τ : Fin k → ℝ =>
        observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l (leftTranslate (bondSpread c X τ) V)) =ᶠ[𝓝 0]
        fun τ => tiltedMean (cutoffWeight T.ballRadius T.p) (gaussianPart T.lam) (lawExponent T.a T.ρA T.lam f law)
          Ob l (leftTranslate (bondSpread c X τ) V) := by
      filter_upwards [hcold] with τ hτ using S.mean_eq _ l Ob hτ h0 (by linarith)
    unfold bondDeriv
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ h3 k).self_of_nhds]
  rw [e1, hformula]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun π _ => ?_
  have hfun : (fun H => rescaledMean T.a T.ρA T.ballRadius T.lam l T.p f law V H) =
      tiltedAverage (cutoffWeight T.ballRadius T.p) (gaussianPart T.lam) (lawExponent T.a T.ρA T.lam f law) l V :=
    funext hmean
  rw [hfun]
  refine jointCumulant_congr _ _ fun j hj => ?_
  rcases j with _ | J
  · rfl
  · have hJ : J ∈ π.parts := by
      rcases Finset.mem_insert.1 hj with h | h
      · cases h
      · obtain ⟨J', hJ', h2⟩ := Finset.mem_image.1 h
        cases h2
        exact hJ'
    have hJ0 : J.card ≠ 0 := Finset.card_ne_zero.2 (π.nonempty_of_mem_parts hJ)
    funext ζ
    simp only [cumulantEntries, topDerivCumulantEntries, derivAlongSubset, bondDeriv]
    have h4 : (fun τ : Fin J.card → ℝ => rescaledLawExponent T.a T.ρA T.lam f l
        (leftTranslate (bondSpread (c ∘ J.orderEmbOfFin rfl) (X ∘ J.orderEmbOfFin rfl) τ) V) law ζ) =
        fun τ => gaussianPart T.lam ζ + -lawExponent T.a T.ρA T.lam f law l ζ
          (leftTranslate (bondSpread (c ∘ J.orderEmbOfFin rfl) (X ∘ J.orderEmbOfFin rfl) τ) V) :=
      funext fun τ => rescaledLawExponent_eq hside _ _ _ _ _ _ _ _
    rw [h4, iteratedFDeriv_const_add' _ _ hJ0]
    have h5 : iteratedFDeriv ℝ J.card (fun τ : Fin J.card → ℝ => -lawExponent T.a T.ρA T.lam f law l ζ
        (leftTranslate (bondSpread (c ∘ J.orderEmbOfFin rfl) (X ∘ J.orderEmbOfFin rfl) τ) V)) 0 =
        -iteratedFDeriv ℝ J.card (fun τ : Fin J.card → ℝ => lawExponent T.a T.ρA T.lam f law l ζ
          (leftTranslate (bondSpread (c ∘ J.orderEmbOfFin rfl) (X ∘ J.orderEmbOfFin rfl) τ) V)) 0 :=
      iteratedFDeriv_neg_apply
    rw [h5]
    simp
end ScaledVariables
end YangMills.Construction
end
