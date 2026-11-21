import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrame
import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExponentsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesAcrossTwoVariables
import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.ResponseInTheExpansion.DominatedOnTheBallsAtOrderTwo
import YangMills.Construction.ResponseInTheExpansion.MeanOfASlotOfOrderTwo
import YangMills.Construction.ResponseInTheExpansion.MeanOfATwiceDominatedFamily
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAtTheirEnds
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open MeasureTheory
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames WeightedResponses Interpolation Cumulants ConvexObservables LinearResponse
namespace ResponseInTheExpansion
namespace SecondOrderSlotMean
variable {F : BlockFrame}
theorem matrix_single_one {k : ℕ} (a : Fin k) :
    (![Pi.single a 1] : Fin 1 → Fin k → ℝ) = fun l => Pi.single ((![a] : Fin 1 → Fin k) l) 1 := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.basisVectors_one <;> assumption
theorem matrix_single_two {k : ℕ} (a b : Fin k) :
    (![Pi.single a 1, Pi.single b 1] : Fin 2 → Fin k → ℝ) =
      fun l => Pi.single ((![a, b] : Fin 2 → Fin k) l) 1 := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.basisVectors_two <;> assumption
theorem bondSpan_le_two_mul (hsym : ∀ a b : F.Cell, cellSupDist a b = cellSupDist b a)
    (htri : ∀ a b d : F.Cell, cellSupDist a d ≤ cellSupDist a b + cellSupDist b d) {k : ℕ} (Y : F.Cell)
    (c : Fin k → F.Site F.top × Fin 4) (R : ℕ) (hall : ∀ l, cellSupDist Y (c l).1 ≤ R) : bondSpan Y c ≤ 2 * R := by
  unfold bondSpan
  refine max_le (Finset.sup_le fun l _ => ?_) (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
  · have := hall l
    show cellSupDist Y (c l).1 ≤ 2 * R
    omega
  · have h1 := htri (c l).1 Y (c l').1
    have h2 := hall l
    have h3 := hall l'
    have h4 := hsym (c l).1 Y
    show cellSupDist (c l).1 (c l').1 ≤ 2 * R
    omega
theorem exp_product_le {κ n s D d₁ d₂ d₃ : ℝ} (hκ : 0 ≤ κ) (hn : n ≤ 2 * (s + D + d₁ + d₂ + d₃))
    (hs : 0 ≤ s) (hD : 0 ≤ D) (h1 : 0 ≤ d₁) (h2 : 0 ≤ d₂) (h3 : 0 ≤ d₃) :
    Real.exp (-(2 ^ 5 * κ * s)) * Real.exp (-(2 ^ 3 * κ * d₁)) * Real.exp (-(2 ^ 3 * κ * d₂)) *
        Real.exp (-(2 ^ 3 * κ * d₃)) * Real.exp (-(κ / 8 * D)) ≤ Real.exp (-(κ / 2 ^ 5 * n)) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have a1 : κ * n ≤ κ * (2 * (s + D + d₁ + d₂ + d₃)) := mul_le_mul_of_nonneg_left hn hκ
  nlinarith [mul_nonneg hκ hs, mul_nonneg hκ hD, mul_nonneg hκ h1, mul_nonneg hκ h2, mul_nonneg hκ h3]
section Terms
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def CumulantBoundsHold (ρ x κ T₀ : ℝ) (r : ℝ → ℝ) (Ψ : BondField ι → ℝ) (y : ι → F.Cell) : Prop :=
  ∀ (M : ℕ) (H : Fin M → BondField ι → ℝ) (Z : Fin M → F.Cell) (hh : Fin M → ℝ) (C : Fin M → ℕ → ℝ),
    2 ≤ M → M ≤ 9 → (∀ i, ContDiffOn ℝ 1 (H i) {η | ∀ b, ‖η b‖ < ρ}) → (∀ i, 0 ≤ hh i) → (∀ i q, 0 ≤ C i q) →
    (∀ i, HasLocalSize ρ r Ψ (C i) x κ (hh i) (fun b => (cellSupDist (y b) (Z i) : ℝ)) (H i)) →
    |cumulantFromMoments r Ψ H| ≤ T₀ * (∏ i, (sizeConstantSum (C i) M * hh i)) *
      Real.exp (-(κ / 8 * cellsDiameter Z))
variable {ρ x κ T₀ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ} {y : ι → F.Cell}
structure SizedObservable (ρ x κ : ℝ) (r : ℝ → ℝ) (Ψ : BondField ι → ℝ) (y : ι → F.Cell) (C : ℕ → ℝ) (a : ℝ)
    (Z : F.Cell) (G : BondField ι → ℝ) : Prop where
  smooth : ContDiffOn ℝ 1 G {η | ∀ b, ‖η b‖ < ρ}
  hasLocalSize : HasLocalSize ρ r Ψ C x κ a (fun b => (cellSupDist (y b) Z : ℝ)) G
  amplitude_nonneg : 0 ≤ a
  constants_nonneg : ∀ q, 0 ≤ C q
theorem abs_ballCovariance_le (cb : CumulantBoundsHold ρ x κ T₀ r Ψ y)
    (he : ∀ H : Fin 2 → BondField ι → ℝ, cumulantFromMoments r Ψ H = ballCovariance r Ψ (H 0) (H 1))
    {C₀ C₁ : ℕ → ℝ} {a₀ a₁ : ℝ} {Z₀ Z₁ : F.Cell} {G₀ G₁ : BondField ι → ℝ}
    (o₀ : SizedObservable ρ x κ r Ψ y C₀ a₀ Z₀ G₀) (o₁ : SizedObservable ρ x κ r Ψ y C₁ a₁ Z₁ G₁) :
    |ballCovariance r Ψ G₀ G₁| ≤ T₀ * ((sizeConstantSum C₀ 2 * a₀) * (sizeConstantSum C₁ 2 * a₁)) *
      Real.exp (-(κ / 8 * cellsDiameter ![Z₀, Z₁])) := by
  have := cb 2 ![G₀, G₁] ![Z₀, Z₁] ![a₀, a₁] ![C₀, C₁] le_rfl (by norm_num)
    (fun i => by fin_cases i; exacts [o₀.smooth, o₁.smooth])
    (fun i => by fin_cases i; exacts [o₀.amplitude_nonneg, o₁.amplitude_nonneg])
    (fun i q => by fin_cases i; exacts [o₀.constants_nonneg q, o₁.constants_nonneg q])
    (fun i => by fin_cases i; exacts [o₀.hasLocalSize, o₁.hasLocalSize])
  rw [he] at this
  simpa [Fin.prod_univ_two] using this
theorem abs_ballThirdCumulant_le (cb : CumulantBoundsHold ρ x κ T₀ r Ψ y)
    (he : ∀ H : Fin 3 → BondField ι → ℝ, cumulantFromMoments r Ψ H = ballThirdCumulant r Ψ (H 0) (H 1) (H 2))
    {C₀ C₁ C₂ : ℕ → ℝ} {a₀ a₁ a₂ : ℝ} {Z₀ Z₁ Z₂ : F.Cell} {G₀ G₁ G₂ : BondField ι → ℝ}
    (o₀ : SizedObservable ρ x κ r Ψ y C₀ a₀ Z₀ G₀) (o₁ : SizedObservable ρ x κ r Ψ y C₁ a₁ Z₁ G₁)
    (o₂ : SizedObservable ρ x κ r Ψ y C₂ a₂ Z₂ G₂) :
    |ballThirdCumulant r Ψ G₀ G₁ G₂| ≤ T₀ * ((sizeConstantSum C₀ 3 * a₀) * (sizeConstantSum C₁ 3 * a₁) *
      (sizeConstantSum C₂ 3 * a₂)) * Real.exp (-(κ / 8 * cellsDiameter ![Z₀, Z₁, Z₂])) := by
  have := cb 3 ![G₀, G₁, G₂] ![Z₀, Z₁, Z₂] ![a₀, a₁, a₂] ![C₀, C₁, C₂] (by norm_num) (by norm_num)
    (fun i => by fin_cases i; exacts [o₀.smooth, o₁.smooth, o₂.smooth])
    (fun i => by fin_cases i; exacts [o₀.amplitude_nonneg, o₁.amplitude_nonneg, o₂.amplitude_nonneg])
    (fun i q => by fin_cases i; exacts [o₀.constants_nonneg q, o₁.constants_nonneg q, o₂.constants_nonneg q])
    (fun i => by fin_cases i; exacts [o₀.hasLocalSize, o₁.hasLocalSize, o₂.hasLocalSize])
  rw [he] at this
  simpa [Fin.prod_univ_three] using this
end Terms
theorem gibbsMean_congr_ae {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {A A' H H' : Ω → ℝ}
    (hA : A =ᵐ[μ] A') (hH : H =ᵐ[μ] H') : gibbsMean μ A H = gibbsMean μ A' H' := by apply _root_.YangMills.Construction.InterpolatedBirths.gibbsMean_congr_ae <;> assumption
def translatedExponent (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (x : ℝ) (f : LocalFamily) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ Y ∈ finiteCells F, cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y (leftTranslate (bondSpread c X τ) V) η -
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y η (leftTranslate (bondSpread c X τ) V)
theorem coldHalfLaw_exponent_eq (hEnds : interpolationAtEndpoints) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) {x : ℝ} {f : LocalFamily}
    {V' : F.GaugeField F.top}
    (hX : CellExponentBounds false T.a T.chainParams.ρA T.ballRadius x T.κ T.Ct (frameRadius x) V')
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < T.ballRadius) :
    (coldHalfLawAt T x f).exponent V' η =
      ∑ Y ∈ finiteCells F, cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y V' η -
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y η V' := by
  have h1 := (hEnds F false T.a T.chainParams.ρA T.chainParams.lam x 0 (frameRadius x) V').2.2.2.2.2.1 f η
  have h2 : familyLawExponent 1 T.a T.chainParams.ρA x (frameRadius x) f V' η =
      stepExponent false T.a T.chainParams.ρA x (frameRadius x) f 1 V' η := by
    simpa [segmentEnd] using h1
  show familyLawExponent 1 T.a T.chainParams.ρA x (frameRadius x) f V' η = _
  rw [h2, ← hX.sum_eq η hη]
  simp [stepExponent]
theorem translated_expectation_dominated (hRim : CutoffMeanIsGibbsMean)
    (hDom : DominatedOfContDiffTwoOnClosedBalls)
    (hEnds : interpolationAtEndpoints) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hρ : 0 < T.ballRadius) (hcut : IsCutoff T.ballRadius T.p)
    {x : ℝ} {f : LocalFamily} {V : F.GaugeField F.top} (K : AboveFrames F) (hfin : Finite F.Cell)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V)
    (hXc : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
      CellExponentBounds false T.a T.chainParams.ρA T.ballRadius x T.κ T.Ct (frameRadius x) V')
    (hR : CentredExpansionBounds false T.a T.chainParams.ρA T.ballRadius T.κ T.decayRate T.E T.energyRatio T.Ct T.L
      (frameRadius x) f V)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hK : ∀ (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      ContDiffAt ℝ 2 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
        K q.2 (leftTranslate (bondSpread c X q.1) V)) (0, η)) :
    ∃ (B : Set (Fin k → ℝ)) (Kb : ℝ), IsOpen B ∧ B ∈ 𝓝 (0 : Fin k → ℝ) ∧
      IsDominatedSmoothFamily (cutoffLaw F T.ballRadius T.p) 2 B Kb (translatedExponent T x f V c X) ∧
      IsDominatedSmoothFamily (cutoffLaw F T.ballRadius T.p) 2 B Kb
        (fun τ η => K η (leftTranslate (bondSpread c X τ) V)) ∧
      ∀ τ ∈ B, (coldHalfLawAt T x f).expectationOf K (leftTranslate (bondSpread c X τ) V) =
        gibbsMean (cutoffLaw F T.ballRadius T.p) (translatedExponent T x f V c X τ)
          (fun η => K η (leftTranslate (bondSpread c X τ) V)) := by
  classical
  set Sv := StepVariable (finiteCells F) with hSv
  obtain ⟨hfinμ, hμ0, hμb, hμm⟩ := hRim F T.ballRadius T.p hρ hcut
  have hμc : ∀ᵐ η ∂cutoffLaw F T.ballRadius T.p, ∀ b, ‖η b‖ ≤ T.ballRadius := by
    filter_upwards [hμb] with η hη b using (hη b).le
  have hEV := hXc V hV
  let Gm : (Fin k → ℝ) × Sv → ℝ := fun z => translatedExponent T x f V c X z.1 z.2
  let Gk : (Fin k → ℝ) × Sv → ℝ := fun z => K z.2 (leftTranslate (bondSpread c X z.1) V)
  have sGm : ∀ η : Sv, (∀ b, ‖η b‖ ≤ T.ballRadius) → ContDiffAt ℝ 2 Gm (0, η) := fun η hη =>
    ((ContDiffAt.sum fun Y _ => hEV.smooth Y η k c X hη).sub
      (ContDiffAt.sum fun y _ => hR.smooth y η k c X hη)).of_le (by norm_num)
  obtain ⟨r₁, M₁, hr₁, hD₁⟩ := hDom _ k T.ballRadius (cutoffLaw F T.ballRadius T.p) Gm hμc sGm
  obtain ⟨r₂, M₂, hr₂, hD₂⟩ := hDom _ k T.ballRadius (cutoffLaw F T.ballRadius T.p) Gk hμc hK
  obtain ⟨r₀, hr₀, hcold⟩ :=
    Metric.eventually_nhds_iff_ball.mp (eventually_isSmallCurvature_leftTranslate hfin c X hV)
  have dom_mono : ∀ {r M r' M' : ℝ} {G : (Fin k → ℝ) → Sv → ℝ}, r' ≤ r → M ≤ M' →
      IsDominatedSmoothFamily (cutoffLaw F T.ballRadius T.p) 2 (Metric.ball 0 r) M G →
      IsDominatedSmoothFamily (cutoffLaw F T.ballRadius T.p) 2 (Metric.ball 0 r') M' G :=
    fun {r M r' M' G} hr hM h => by
    have hB := Metric.ball_subset_ball (x := (0 : Fin k → ℝ)) hr
    refine ⟨fun τ hτ => h.aestronglyMeasurable τ (hB hτ), ?_, ?_⟩
    · filter_upwards [h.contDiffOn] with ω hω using hω.mono hB
    · filter_upwards [h.norm_iteratedFDeriv_le] with ω hω j hj τ hτ using le_trans (hω j hj τ (hB hτ)) hM
  set r : ℝ := min r₀ (min r₁ r₂) with hr
  have hrpos : 0 < r := lt_min hr₀ (lt_min hr₁ hr₂)
  refine ⟨Metric.ball 0 r, max M₁ M₂, Metric.isOpen_ball, Metric.ball_mem_nhds _ hrpos, ?_, ?_, ?_⟩
  · exact dom_mono ((min_le_right _ _).trans (min_le_left _ _)) (le_max_left _ _) hD₁
  · exact dom_mono ((min_le_right _ _).trans (min_le_right _ _)) (le_max_right _ _) hD₂
  · intro τ hτ
    have hc := hcold τ (Metric.ball_subset_ball (min_le_left _ _) hτ)
    show cutoffMean T.ballRadius T.p _ _ = _
    rw [hμm]
    apply gibbsMean_congr_ae
    · filter_upwards [hμb] with η hη
      exact coldHalfLaw_exponent_eq hEnds T (hXc _ hc) η hη
    · exact Filter.EventuallyEq.rfl
theorem cellSupDist_le_cellsDiameter {M : ℕ} (Z : Fin M → F.Cell) (i j : Fin M) :
    cellSupDist (Z i) (Z j) ≤ cellsDiameter Z := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.cellSupDist_le_cellsDiameter <;> assumption
theorem cellSupDist_le_add_bondListDiameter
    (htri : ∀ a b d : F.Cell, cellSupDist a d ≤ cellSupDist a b + cellSupDist b d) {j : ℕ}
    (c' : Fin j → F.Site F.top × Fin 4) (Y : F.Cell) (l₀ m : Fin j) :
    cellSupDist Y (c' m).1 ≤ cellSupDist Y (c' l₀).1 + _root_.YangMills.Construction.BlockAverages.bondListDiameter c' := by
  have h1 := htri Y (c' l₀).1 (c' m).1
  have h2 : cellSupDist (c' l₀).1 (c' m).1 ≤ _root_.YangMills.Construction.BlockAverages.bondListDiameter c' := by
    unfold _root_.YangMills.Construction.BlockAverages.bondListDiameter
    exact le_trans (Finset.le_sup (f := fun l' => cellSupDist (c' l₀).1 (c' l').1) (Finset.mem_univ m))
      (Finset.le_sup (f := fun l => Finset.univ.sup fun l' => cellSupDist (c' l).1 (c' l').1) (Finset.mem_univ l₀))
  omega
theorem cellSupDist_le_bondSpan {j : ℕ} (c' : Fin j → F.Site F.top × Fin 4) (Y : F.Cell) (m : Fin j) :
    cellSupDist Y (c' m).1 ≤ bondSpan Y c' :=
  le_trans (Finset.le_sup (f := fun l : Fin j => siteSupDist Y (c' l).1) (Finset.mem_univ m)) (le_max_left _ _)
theorem sizeConstantSum_le_four {C : ℕ → ℝ} (hC : ∀ q, 0 ≤ C q) {M : ℕ} (hM : M ≤ 4) :
    sizeConstantSum C M ≤ sizeConstantSum C 4 := by
  unfold sizeConstantSum
  have : ∑ q ∈ Finset.range (2 * M + 1), C q ≤ ∑ q ∈ Finset.range (2 * 4 + 1), C q :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega)) fun q _ _ => hC q
  linarith
theorem one_le_sizeConstantSum {C : ℕ → ℝ} (hC : ∀ q, 0 ≤ C q) (M : ℕ) : 1 ≤ sizeConstantSum C M := by
  unfold sizeConstantSum
  have : 0 ≤ ∑ q ∈ Finset.range (2 * M + 1), C q := Finset.sum_nonneg fun q _ => hC q
  linarith
theorem second_order_product_le {T₀ c₀ c₁ A h E₀ E₁ ED cK cP E : ℝ} (hT : 0 ≤ T₀) (hh : 0 ≤ h) (hA : 0 ≤ A)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (h₀ : c₀ ≤ cK) (h₁ : c₁ ≤ cP) (hcP : 1 ≤ cP) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁)
    (hED : 0 ≤ ED) (hE : E₀ * E₁ * ED ≤ E) :
    T₀ * ((c₀ * (h * E₀)) * (c₁ * (A * E₁))) * ED ≤ T₀ * (cK * (cP * (1 + A)) ^ 3) * h * E := by
  have hP : 1 ≤ cP * (1 + A) := by nlinarith
  have hcK : 0 ≤ cK := hc₀.trans h₀
  have a1 : c₀ * (c₁ * A) ≤ cK * (cP * (1 + A)) ^ 3 := by
    have b1 : c₁ * A ≤ cP * (1 + A) := mul_le_mul h₁ (by linarith) hA (by linarith)
    have b2 : cP * (1 + A) ≤ (cP * (1 + A)) ^ 3 := le_self_pow₀ hP (by norm_num)
    exact mul_le_mul h₀ (b1.trans b2) (by positivity) hcK
  calc T₀ * ((c₀ * (h * E₀)) * (c₁ * (A * E₁))) * ED = T₀ * (c₀ * (c₁ * A)) * h * (E₀ * E₁ * ED) := by ring
    _ ≤ T₀ * (cK * (cP * (1 + A)) ^ 3) * h * E := by gcongr
theorem third_order_product_le {T₀ c₀ c₁ c₂ A h E₀ E₁ E₂ ED cK cP E : ℝ} (hT : 0 ≤ T₀) (hh : 0 ≤ h) (hA : 0 ≤ A)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (h₀ : c₀ ≤ cK) (h₁ : c₁ ≤ cP) (h₂ : c₂ ≤ cP) (hcP : 1 ≤ cP)
    (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) (hED : 0 ≤ ED) (hE : E₀ * E₁ * E₂ * ED ≤ E) :
    T₀ * ((c₀ * (h * E₀)) * (c₁ * (A * E₁)) * (c₂ * (A * E₂))) * ED ≤ T₀ * (cK * (cP * (1 + A)) ^ 3) * h * E := by
  have hP : 1 ≤ cP * (1 + A) := by nlinarith
  have hcK : 0 ≤ cK := hc₀.trans h₀
  have a1 : c₀ * ((c₁ * A) * (c₂ * A)) ≤ cK * (cP * (1 + A)) ^ 3 := by
    have b1 : c₁ * A ≤ cP * (1 + A) := mul_le_mul h₁ (by linarith) hA (by linarith)
    have b2 : c₂ * A ≤ cP * (1 + A) := mul_le_mul h₂ (by linarith) hA (by linarith)
    have b3 : (c₁ * A) * (c₂ * A) ≤ (cP * (1 + A)) ^ 2 := by
      rw [sq]; exact mul_le_mul b1 b2 (by positivity) (by linarith)
    have b4 : (cP * (1 + A)) ^ 2 ≤ (cP * (1 + A)) ^ 3 := pow_le_pow_right₀ hP (by norm_num)
    exact mul_le_mul h₀ (b3.trans b4) (by positivity) hcK
  calc T₀ * ((c₀ * (h * E₀)) * (c₁ * (A * E₁)) * (c₂ * (A * E₂))) * ED =
        T₀ * (c₀ * ((c₁ * A) * (c₂ * A))) * h * (E₀ * E₁ * E₂ * ED) := by ring
    _ ≤ T₀ * (cK * (cP * (1 + A)) ^ 3) * h * E := by gcongr
theorem slotMean_deriv_bound (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedOfContDiffTwoOnClosedBalls)
    (hDW : GibbsMeanSecondDerivative) (hEnds : interpolationAtEndpoints)
    (hTwo : Calculus.IteratedFDerivParamDiff) (hExp : lowOrderCumulantFormulas)
    (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hρ : 0 < T.ballRadius) (hcut : IsCutoff T.ballRadius T.p) (hκ : 0 < T.κ) {Cq Cp : ℕ → ℝ}
    (hCq : ∀ q, 0 ≤ Cq q) (hCp : ∀ q, 0 ≤ Cp q) {A T₀ : ℝ} (hA : 0 ≤ A) (hT₀ : 0 ≤ T₀) {t : ℕ}
    {x h : ℝ} {f : LocalFamily} {V : F.GaugeField F.top} {Y : F.Cell} {K : AboveFrames F}
    (hst : IsAdmissibleAt T t x f F V) (hrow : IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f)
    (hh0 : 0 < h)
    (hfin : Finite F.Cell) (hsym : ∀ a b : F.Cell, cellSupDist a b = cellSupDist b a)
    (htri : ∀ a b d : F.Cell, cellSupDist a d ≤ cellSupDist a b + cellSupDist b d)
    (Ψ' : StepVariable (finiteCells F) → ℝ)
    (hd : ballDensity (cutoffFactor T.ballRadius T.p) ((coldHalfLawAt T x f).exponent V) =
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ')
    (hz : ∀ η : BondField ↥(chordBonds (finiteCells F)), ¬ (∀ b, ‖η b‖ < T.ballRadius) →
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ' η = 0)
    (cb : CumulantBoundsHold T.ballRadius x T.κ T₀ (cutoffFactor T.ballRadius T.p) Ψ'
      (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1))
    (hXc : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
      CellExponentBounds false T.a T.chainParams.ρA T.ballRadius x T.κ T.Ct (frameRadius x) V')
    (hR : CentredExpansionBounds false T.a T.chainParams.ρA T.ballRadius T.κ T.decayRate T.E T.energyRatio T.Ct T.L
      (frameRadius x) f V)
    (hEL : IsLocalExponentAt T Cp A) (hsl : IsSmoothBoundedSlot (coldHalfLawAt T x f) Cq 2 h Y K V) :
    (∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2
        (fun τ : Fin k → ℝ => (coldHalfLawAt T x f).expectationOf K (leftTranslate (bondSpread c X τ) V)) 0) ∧
    ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 2 →
      AreUnitVectors X →
      |bondDeriv ((coldHalfLawAt T x f).expectationOf K) V c X -
          (coldHalfLawAt T x f).expectation V (fun η => bondDeriv (K η) V c X)| ≤
        (4 * (T₀ * (sizeConstantSum Cq 4 * (sizeConstantSum Cp 4 * (1 + A)) ^ 3))) * h *
          Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c)) := by
  classical
  have hh : 0 ≤ h := hh0.le
  set Q := coldHalfLawAt T x f with hQ
  set r := cutoffFactor T.ballRadius T.p with hr
  set y : ↥(chordBonds (finiteCells F)) → F.Cell := fun b => enclosingCell b.1.1 with hy
  obtain ⟨hfinμ, hμ0, hμb, hμm⟩ := hRim F T.ballRadius T.p hρ hcut
  have hfm := hfinμ
  set μ := cutoffLaw F T.ballRadius T.p with hμ
  have hO : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} := by
    have : {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} =
        ⋂ b, {η : StepVariable (finiteCells F) | ‖η b‖ < T.ballRadius} := by
      ext η; simp
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
  have hwm : ∀ {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (g : StepVariable (finiteCells F) → ℝ),
      gibbsMean μ (translatedExponent T x f V c X 0) g = ballExpectation r Ψ' g := by
    intro k c X g
    have e1 : gibbsMean μ (translatedExponent T x f V c X 0) g = gibbsMean μ (Q.exponent V) g := by
      refine gibbsMean_congr_ae ?_ Filter.EventuallyEq.rfl
      filter_upwards [hμb] with η hη
      have := coldHalfLaw_exponent_eq (f := f) hEnds T (hXc V hst.small_curvature) η hη
      simp only [translatedExponent, leftTranslate_bondSpread_zero]
      exact this.symm
    rw [e1, ← hμm]
    show ballExpectation r (Q.exponent V) g = _
    unfold ballExpectation
    rw [hd]
  have mean_ball : ∀ g g' : StepVariable (finiteCells F) → ℝ,
      (∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) → g η = g' η) →
      ballExpectation r Ψ' g = ballExpectation r Ψ' g' := by
    intro g g' hg
    unfold ballExpectation
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    by_cases hη : ∀ b, ‖η b‖ < T.ballRadius
    · show g η * _ = g' η * _
      rw [hg η hη]
    · show g η * _ = g' η * _
      rw [hz η hη]; simp
  refine ⟨fun k c X => ?_, fun k c X hk1 hk3 hX => ?_⟩
  · obtain ⟨B, Kb, hBo, hB0, dA, dH, heq⟩ := translated_expectation_dominated (f := f) hRim hDom hEnds T hρ hcut K hfin
      hst.small_curvature hXc hR c X (fun η hη => hsl.smooth η k c X hη)
    obtain ⟨hcd, -⟩ := hDW _ μ k B Kb _ _ hBo hμ0 dA dH
    exact (hcd.contDiffAt hB0).congr_of_eventuallyEq (Filter.eventually_of_mem hB0 heq)
  obtain ⟨B, Kb, hBo, hB0, dA, dH, heq⟩ := translated_expectation_dominated (f := f) hRim hDom hEnds T hρ hcut K hfin
    hst.small_curvature hXc hR c X (fun η hη => hsl.smooth η k c X hη)
  obtain ⟨hcd, hform⟩ := hDW _ μ k B Kb _ _ hBo hμ0 dA dH
  have h0B : (0 : Fin k → ℝ) ∈ B := mem_of_mem_nhds hB0
  let Af := translatedExponent T x f V c X
  let Hf : (Fin k → ℝ) → StepVariable (finiteCells F) → ℝ := fun τ η => K η (leftTranslate (bondSpread c X τ) V)
  let units : ∀ {j : ℕ}, (Fin j → Fin k) → Fin j → Fin k → ℝ := fun ι l => Pi.single (ι l) 1
  let GH : ∀ {j : ℕ}, (Fin j → Fin k) → StepVariable (finiteCells F) → ℝ :=
    fun ι => paramIteratedDeriv Hf (units ι) 0
  let GA : ∀ {j : ℕ}, (Fin j → Fin k) → StepVariable (finiteCells F) → ℝ :=
    fun ι => paramIteratedDeriv Af (units ι) 0
  have hline : ∀ {n : WithTop ℕ∞} {G : (Fin k → ℝ) × StepVariable (finiteCells F) → ℝ}
      {η : StepVariable (finiteCells F)},
      ContDiffAt ℝ n G (0, η) → ContDiffAt ℝ n (fun τ : Fin k → ℝ => G (τ, η)) 0 := fun {n G η} hG =>
    ContDiffAt.comp (g := G) (f := fun τ : Fin k → ℝ => (τ, η)) 0 hG
      ((contDiff_id.prodMk contDiff_const).contDiffAt)
  have hofle : ∀ {j : ℕ}, j ≤ 3 → ((j : ℕ) : WithTop ℕ∞) ≤ 3 := fun {j} hj => by exact_mod_cast hj
  have hofle2 : ∀ {j : ℕ}, j ≤ 2 → ((j : ℕ) : WithTop ℕ∞) ≤ 2 := fun {j} hj => by exact_mod_cast hj
  have obsH : ∀ {j : ℕ} (ι : Fin j → Fin k), j ≤ 1 →
      SizedObservable T.ballRadius x T.κ r Ψ' y Cq (h * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y (c ∘ ι)))) Y (GH ι) := by
    intro j ι hj
    have hu : AreUnitVectors (X ∘ ι) := fun l => hX (ι l)
    have hs1 := hsl.deriv_bound j (c ∘ ι) (X ∘ ι) (by omega) hu
    have eqb : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        bondDeriv (K η) V (c ∘ ι) (X ∘ ι) = GH ι η := fun η hη =>
      (iteratedFDeriv_single_eq_bondDeriv (K η) V c X ι
        ((hline (hsl.smooth η k c X fun b => (hη b).le)).of_le (hofle2 (by omega)))).symm
    have hc1 : ContDiffOn ℝ 1 (fun η => bondDeriv (K η) V (c ∘ ι) (X ∘ ι))
        {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} :=
      fun η hη => by
        have hs := hsl.smooth η j (c ∘ ι) (X ∘ ι) fun b => (hη b).le
        have h1 := (hTwo (Fin j → ℝ) (StepVariable (finiteCells F)) j
          (fun q => K q.2 (leftTranslate (bondSpread (c ∘ ι) (X ∘ ι) q.1) V)) η
          (fun l => Pi.single l 1) (hs.of_le (by exact_mod_cast (by omega : j + 1 ≤ 2)))).1
        exact h1.contDiffWithinAt
    refine ⟨hc1.congr fun η hη => (eqb η hη).symm, ?_, by positivity, hCq⟩
    exact hasLocalSize_congr_of_eqOn_balls hO (fun η hη => by
        show ballDensity r Ψ' η = 0
        exact hz η hη) eqb (hasLocalSize_congr_density hd hs1)
  have eqA : ∀ {j : ℕ} (ι : Fin j → Fin k), j ≤ 3 → ∀ η : StepVariable (finiteCells F),
      (∀ b, ‖η b‖ < T.ballRadius) →
      bondDeriv (fun V' => Q.exponent V' η) V (c ∘ ι) (X ∘ ι) = GA ι η := by
    intro j ι hj3 η hη
    have ev : (fun τ : Fin k → ℝ => Q.exponent (leftTranslate (bondSpread c X τ) V) η) =ᶠ[𝓝 0]
        fun τ => Af τ η := by
      filter_upwards [eventually_isSmallCurvature_leftTranslate hfin c X hst.small_curvature] with τ hτ
      exact coldHalfLaw_exponent_eq hEnds T (hXc _ hτ) η hη
    have smA : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => Af τ η) 0 := by
      have h1 := (ContDiffAt.sum fun Y' _ =>
          hline ((hXc V hst.small_curvature).smooth Y' η k c X fun b => (hη b).le) :
        ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => ∑ Y' ∈ finiteCells F,
          cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y' (leftTranslate (bondSpread c X τ) V) η) 0)
      have h2 := (ContDiffAt.sum fun y' _ => hline (hR.smooth y' η k c X fun b => (hη b).le) :
        ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => ∑ y' ∈ sitesOfCells (finiteCells F) F.depth,
          centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y' η (leftTranslate (bondSpread c X τ) V)) 0)
      exact h1.sub h2
    have smE : ContDiffAt ℝ j (fun τ : Fin k → ℝ => Q.exponent (leftTranslate (bondSpread c X τ) V) η) 0 :=
      (smA.congr_of_eventuallyEq ev).of_le (hofle hj3)
    have e1 := (Filter.EventuallyEq.iteratedFDeriv ℝ ev j).eq_of_nhds
    rw [← iteratedFDeriv_single_eq_bondDeriv (fun V' => Q.exponent V' η) V c X ι smE, e1]
    rfl
  have obsA : ∀ {j : ℕ} (ι : Fin j → Fin k) (l₀ : Fin j), j ≤ 2 →
      SizedObservable T.ballRadius x T.κ r Ψ' y Cp (A * Real.exp (-(2 ^ 3 * T.κ * _root_.YangMills.Construction.BlockAverages.bondListDiameter (c ∘ ι))))
        (c (ι l₀)).1 (GA ι) := by
    intro j ι l₀ hj
    have hu : AreUnitVectors (X ∘ ι) := fun l => hX (ι l)
    obtain ⟨hc1, hs1⟩ := hEL t x f F V j (c ∘ ι) (X ∘ ι) l₀ hst hrow hj hu
    have eqb := eqA ι (by omega : j ≤ 3)
    refine ⟨hc1.congr fun η hη => (eqb η hη).symm, ?_, by positivity, hCp⟩
    exact hasLocalSize_congr_of_eqOn_balls hO (fun η hη => by
        show ballDensity r Ψ' η = 0
        exact hz η hη) eqb (hasLocalSize_congr_density hd hs1)
  set cK := sizeConstantSum Cq 4 with hcK
  set cP := sizeConstantSum Cp 4 with hcP
  have hcP1 : 1 ≤ cP := one_le_sizeConstantSum hCp 4
  have hκ0 := hκ.le
  have hc0 : ∀ (C : ℕ → ℝ) (M : ℕ), (∀ q, 0 ≤ C q) → 0 ≤ sizeConstantSum C M := fun C M hC =>
    le_trans zero_le_one (one_le_sizeConstantSum hC M)
  set E : ℝ := Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c)) with hEdef
  set b : ℝ := T₀ * (cK * (cP * (1 + A)) ^ 3) * h * E with hb
  obtain ⟨he2, he3, he4⟩ := hExp _ r Ψ'
  have hz0 : Real.exp (-(2 ^ 3 * T.κ * (0 : ℝ))) = 1 := by simp
  have t2 : ∀ {j₀ j₁ : ℕ} (ι₀ : Fin j₀ → Fin k) (ι₁ : Fin j₁ → Fin k) (l₁ : Fin j₁), j₀ ≤ 1 → j₁ ≤ 2 →
      (∀ l : Fin k, (∃ m, ι₀ m = l) ∨ (∃ m, ι₁ m = l)) → |ballCovariance r Ψ' (GH ι₀) (GA ι₁)| ≤ b := by
    intro j₀ j₁ ι₀ ι₁ l₁ h₀ h₁ hcov
    have hc := abs_ballCovariance_le cb he2 (obsH ι₀ h₀) (obsA ι₁ l₁ h₁)
    refine hc.trans ?_
    set s := bondSpan Y (c ∘ ι₀)
    set d₁ := _root_.YangMills.Construction.BlockAverages.bondListDiameter (c ∘ ι₁)
    set D := cellsDiameter ![Y, (c (ι₁ l₁)).1]
    have hall : ∀ l, cellSupDist Y (c l).1 ≤ s + D + d₁ := by
      intro l
      rcases hcov l with ⟨m', rfl⟩ | ⟨m', rfl⟩
      · have := cellSupDist_le_bondSpan (c ∘ ι₀) Y m'
        simp only [Function.comp] at this
        omega
      · have h1 := cellSupDist_le_add_bondListDiameter htri (c ∘ ι₁) Y l₁ m'
        have h2 := cellSupDist_le_cellsDiameter ![Y, (c (ι₁ l₁)).1] 0 1
        simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
        omega
    have hn := bondSpan_le_two_mul hsym htri Y c _ hall
    have hn' : (bondSpan Y c : ℝ) ≤ 2 * ((s : ℝ) + D + d₁ + 0 + 0) := by
      have : (bondSpan Y c : ℝ) ≤ ((2 * (s + D + d₁) : ℕ) : ℝ) := Nat.cast_le.2 hn
      push_cast at this
      linarith
    have hE := exp_product_le hκ0 hn' (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) le_rfl le_rfl
    rw [hz0, mul_one, mul_one] at hE
    exact second_order_product_le hT₀ hh hA (hc0 _ _ hCq) (hc0 _ _ hCp) (sizeConstantSum_le_four hCq (by norm_num))
      (sizeConstantSum_le_four hCp (by norm_num)) hcP1 (Real.exp_pos _).le (Real.exp_pos _).le
      (Real.exp_pos _).le hE
  have t3 : ∀ {j₀ j₁ j₂ : ℕ} (ι₀ : Fin j₀ → Fin k) (ι₁ : Fin j₁ → Fin k) (ι₂ : Fin j₂ → Fin k) (l₁ : Fin j₁)
      (l₂ : Fin j₂), j₀ ≤ 1 → j₁ ≤ 2 → j₂ ≤ 2 →
      (∀ l : Fin k, (∃ m, ι₀ m = l) ∨ (∃ m, ι₁ m = l) ∨ (∃ m, ι₂ m = l)) →
      |ballThirdCumulant r Ψ' (GH ι₀) (GA ι₁) (GA ι₂)| ≤ b := by
    intro j₀ j₁ j₂ ι₀ ι₁ ι₂ l₁ l₂ h₀ h₁ h₂ hcov
    have hc := abs_ballThirdCumulant_le cb he3 (obsH ι₀ h₀) (obsA ι₁ l₁ h₁) (obsA ι₂ l₂ h₂)
    refine hc.trans ?_
    set s := bondSpan Y (c ∘ ι₀)
    set d₁ := _root_.YangMills.Construction.BlockAverages.bondListDiameter (c ∘ ι₁)
    set d₂ := _root_.YangMills.Construction.BlockAverages.bondListDiameter (c ∘ ι₂)
    set D := cellsDiameter ![Y, (c (ι₁ l₁)).1, (c (ι₂ l₂)).1]
    have hall : ∀ l, cellSupDist Y (c l).1 ≤ s + D + d₁ + d₂ := by
      intro l
      rcases hcov l with ⟨m', rfl⟩ | ⟨m', rfl⟩ | ⟨m', rfl⟩
      · have := cellSupDist_le_bondSpan (c ∘ ι₀) Y m'
        simp only [Function.comp] at this
        omega
      · have h1 := cellSupDist_le_add_bondListDiameter htri (c ∘ ι₁) Y l₁ m'
        have h2 := cellSupDist_le_cellsDiameter ![Y, (c (ι₁ l₁)).1, (c (ι₂ l₂)).1] 0 1
        simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
        omega
      · have h1 := cellSupDist_le_add_bondListDiameter htri (c ∘ ι₂) Y l₂ m'
        have h2 := cellSupDist_le_cellsDiameter ![Y, (c (ι₁ l₁)).1, (c (ι₂ l₂)).1] 0 2
        simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val] at h1 h2
        omega
    have hn := bondSpan_le_two_mul hsym htri Y c _ hall
    have hn' : (bondSpan Y c : ℝ) ≤ 2 * ((s : ℝ) + D + d₁ + d₂ + 0) := by
      have : (bondSpan Y c : ℝ) ≤ ((2 * (s + D + d₁ + d₂) : ℕ) : ℝ) := Nat.cast_le.2 hn
      push_cast at this
      linarith
    have hE := exp_product_le hκ0 hn' (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) le_rfl
    rw [hz0, mul_one] at hE
    exact third_order_product_le hT₀ hh hA (hc0 _ _ hCq) (hc0 _ _ hCp) (hc0 _ _ hCp)
      (sizeConstantSum_le_four hCq (by norm_num)) (sizeConstantSum_le_four hCp (by norm_num))
      (sizeConstantSum_le_four hCp (by norm_num)) hcP1 (Real.exp_pos _).le
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le hE
  have cvU : ∀ f₁ f₂ : StepVariable (finiteCells F) → ℝ,
      gibbsCovariance μ (Af 0) f₁ f₂ = ballCovariance r Ψ' f₁ f₂ := fun f₁ f₂ => by
    unfold gibbsCovariance ballCovariance
    simp only [Af, hwm c X]
  have c3U : ∀ f₁ f₂ f₃ : StepVariable (finiteCells F) → ℝ,
      gibbsCumulantThree μ (Af 0) f₁ f₂ f₃ = ballThirdCumulant r Ψ' f₁ f₂ f₃ := fun f₁ f₂ f₃ => by
    unfold gibbsCumulantThree ballThirdCumulant
    simp only [Af, hwm c X]
  have e0H : GH (Fin.elim0 : Fin 0 → Fin k) = Hf 0 := by
    funext η
    simp [GH, paramIteratedDeriv]
  have hH1 : ∀ a : Fin k, paramIteratedDeriv Hf ![Pi.single a 1] 0 = GH ![a] := fun a => by
    show _ = paramIteratedDeriv Hf (units ![a]) 0
    simp only [units]
    rw [matrix_single_one]
  have hA1 : ∀ a : Fin k, paramIteratedDeriv Af ![Pi.single a 1] 0 = GA ![a] := fun a => by
    show _ = paramIteratedDeriv Af (units ![a]) 0
    simp only [units]
    rw [matrix_single_one]
  have hA2 : ∀ a d : Fin k, paramIteratedDeriv Af ![Pi.single a 1, Pi.single d 1] 0 = GA ![a, d] := fun a d => by
    show _ = paramIteratedDeriv Af (units ![a, d]) 0
    simp only [units]
    rw [matrix_single_two]
  have hMeq : bondDeriv (Q.expectationOf K) V c X =
      iteratedFDeriv ℝ k (fun τ => gibbsMean μ (Af τ) (Hf τ)) 0 (fun l => Pi.single l 1) := by
    have ev : (fun τ : Fin k → ℝ => Q.expectationOf K (leftTranslate (bondSpread c X τ) V)) =ᶠ[𝓝 0]
        fun τ => gibbsMean μ (Af τ) (Hf τ) := Filter.eventually_of_mem hB0 heq
    have e1 := (Filter.EventuallyEq.iteratedFDeriv ℝ ev k).eq_of_nhds
    unfold bondDeriv
    rw [e1]
  have hmain : Q.expectation V (fun η => bondDeriv (K η) V c X) =
      gibbsMean μ (Af 0) (paramIteratedDeriv Hf (fun l => Pi.single l 1) 0) := by
    have hj3 : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        bondDeriv (K η) V c X = paramIteratedDeriv Hf (fun l => Pi.single l 1) 0 η := fun η hη => by
      have := iteratedFDeriv_single_eq_bondDeriv (K η) V c X id
        ((hline (hsl.smooth η k c X fun b => (hη b).le)).of_le (hofle2 hk3))
      simp only [Function.comp_id, id] at this
      exact this.symm
    show ballExpectation r (Q.exponent V) _ = _
    rw [show Af 0 = translatedExponent T x f V c X 0 from rfl, hwm]
    have : ballExpectation r (Q.exponent V) (fun η => bondDeriv (K η) V c X) =
        ballExpectation r Ψ' (fun η => bondDeriv (K η) V c X) := by
      unfold ballExpectation
      rw [hd]
    rw [this]
    exact mean_ball _ _ hj3
  have hbn : 0 ≤ b := by
    have := hc0 _ 4 hCq
    positivity
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hrhs : (4 * (T₀ * (cK * (cP * (1 + A)) ^ 3))) * h * E = 4 * b := by
    rw [hb]; ring
  rw [hrhs, hmain, hMeq]
  have F1 : ∀ u : Fin k → ℝ, iteratedFDeriv ℝ 1 (fun τ => gibbsMean μ (Af τ) (Hf τ)) 0 ![u] =
      gibbsMean μ (Af 0) (paramIteratedDeriv Hf ![u] 0) -
        gibbsCovariance μ (Af 0) (Hf 0) (paramIteratedDeriv Af ![u] 0) :=
    fun u => (hform 0 h0B u u).1
  have F2 : ∀ u v : Fin k → ℝ, iteratedFDeriv ℝ 2 (fun τ => gibbsMean μ (Af τ) (Hf τ)) 0 ![v, u] =
      gibbsMean μ (Af 0) (paramIteratedDeriv Hf ![v, u] 0) -
        gibbsCovariance μ (Af 0) (paramIteratedDeriv Hf ![u] 0) (paramIteratedDeriv Af ![v] 0) -
        gibbsCovariance μ (Af 0) (paramIteratedDeriv Hf ![v] 0) (paramIteratedDeriv Af ![u] 0) -
        gibbsCovariance μ (Af 0) (Hf 0) (paramIteratedDeriv Af ![v, u] 0) +
        gibbsCumulantThree μ (Af 0) (Hf 0) (paramIteratedDeriv Af ![u] 0) (paramIteratedDeriv Af ![v] 0) :=
    fun u v => (hform 0 h0B u v).2
  rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
  · have u1 : (fun l : Fin 1 => (Pi.single l 1 : Fin 1 → ℝ)) = ![Pi.single 0 1] := by
      funext l; fin_cases l; rfl
    rw [u1, F1]
    rw [cvU, hA1, ← e0H]
    have a1 := abs_le.1 (t2 (Fin.elim0 : Fin 0 → Fin 1) ![0] 0 (by norm_num) (by norm_num) (by decide))
    refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [a1.1, a1.2]
  · have u2 : (fun l : Fin 2 => (Pi.single l 1 : Fin 2 → ℝ)) = ![Pi.single 0 1, Pi.single 1 1] := by
      funext l; fin_cases l <;> rfl
    rw [u2, F2]
    simp only [cvU, c3U, hA1, hH1, hA2, ← e0H]
    have a1 := abs_le.1 (t2 ![1] ![0] 0 (by norm_num) (by norm_num) (by decide))
    have a2 := abs_le.1 (t2 ![0] ![1] 0 (by norm_num) (by norm_num) (by decide))
    have a3 := abs_le.1 (t2 (Fin.elim0 : Fin 0 → Fin 2) ![0, 1] 0 (by norm_num) (by norm_num) (by decide))
    have a4 := abs_le.1
      (t3 (Fin.elim0 : Fin 0 → Fin 2) ![1] ![0] 0 0 (by norm_num) (by norm_num) (by norm_num) (by decide))
    refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]
end SecondOrderSlotMean
open SecondOrderSlotMean in
theorem secondOrderSlotMeanStatement_proof (hRim : CutoffMeanIsGibbsMean)
    (hDom : DominatedOfContDiffTwoOnClosedBalls)
    (hDW : GibbsMeanSecondDerivative) (hEnds : interpolationAtEndpoints)
    (hTwo : Calculus.IteratedFDerivParamDiff) (hExp : lowOrderCumulantFormulas)
    (hEL : exponentLocalityStatement)
    (hCum : cumulantDecayBound) (hFew : Estimates.cellBondsCardStatement)
    (hLaw : normalizedBallLawIsProbabilityStatement)
    (hFB : interpolatedFramesStatement) (hB : CellExponentsBounded)
    (hRw : CentredExpansionsBounded) (hG : CubicTorusCellGeometry)
    (hJ : EventuallyInParametersCombines) : secondOrderSlotMeanStatement := by
  classical
  intro Cq hCq
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cm, Cz, Cr, hP⟩ := hFB
  obtain ⟨Cp, A, hCp, hA, hLoc⟩ := hEL
  obtain ⟨hg1, -⟩ := hG
  choose! T₀ hT₀ hT₀' using hCum
  have h64 : EventuallyInParameters fun T => 64 ≤ T.n₀ ∧ 1 ≤ T.coupling := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨64, fun _ h => ⟨0, fun _ _ => ⟨1, fun _ hy => ⟨h, hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine ⟨fun U => |4 * (T₀ (4 * U.L ^ 4) U.κ U.chainParams.lam * (sizeConstantSum (Cq U) 4 *
      (sizeConstantSum (Cp (sizeParameters U)) 4 * (1 + A U)) ^ 3))|, fun T => abs_nonneg _, ?_⟩
  refine weaken _ _ ?_ (join _ _ hP (join _ _ h64 (join _ _ hLoc (join _ _ hB hRw))))
  rintro T hDr ⟨hPT, ⟨h64', hy1⟩, hLocT, hXb, hRb⟩
  intro t x h f F V Y K hst hrow hh hsl
  have hfl : T.coupling ≤ x := hst.coupling_le
  have hx1 : 1 ≤ x := hy1.trans hfl
  have hx : 0 < x := by linarith
  have hPT' := hPT t x hfl
  set Q := coldHalfLawAt T x f with hQ
  let M : LawOnBondVariables ↥(chordBonds (finiteCells F)) := lawAtTop V (Q.exponent V)
  have hadm : M.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀
      (frameRadius x) (chordBondDist F) :=
    ⟨hst.torus, hst.small_curvature, IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hst.family_bounded,
      Function.injective_id, fun _ _ => rfl⟩
  obtain ⟨hconv, -, -⟩ := hPT'.laws _ (chordBondDist F) 1 (fun _ => 1) (fun _ => M)
    ⟨fun _ => zero_le_one, by simp⟩ (fun _ => hadm)
  rw [convexCombinationExponent_lawAtTop] at hconv
  obtain ⟨Ψ', K', hΨ', hconvex, hslope, -⟩ := hconv
  have hΨc : Continuous Ψ' := hconvex.smooth.continuous
  have hρ : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  have hκ : 0 < T.κ := hDr.κ_pos
  have hlam : 0 < T.chainParams.lam := hDr.chain_admissible.positivity.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hnz, -⟩ := hLaw _ T.ballRadius T.p Ψ' hρ hDr.cutoff hΨc
  have hz : ∀ η : BondField ↥(chordBonds (finiteCells F)), ¬ (∀ b, ‖η b‖ < T.ballRadius) →
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ' η = 0 := fun η hη => by
    by_contra hne
    exact hη ((hnz η).1 hne)
  have hd : ballDensity (cutoffFactor T.ballRadius T.p) (Q.exponent V) =
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ' := by
    funext η
    by_cases hη' : ∀ b, ‖η b‖ < T.ballRadius
    · unfold ballDensity
      rw [hΨ' η hη']
    · have h0 := hz η hη'
      have h1 : radialWeightProd (cutoffFactor T.ballRadius T.p) η = 0 := by
        unfold ballDensity at h0
        rcases mul_eq_zero.1 h0 with h | h
        · exact h
        · exact absurd h (Real.exp_pos _).ne'
      rw [h0]
      unfold ballDensity
      rw [h1, zero_mul]
  obtain ⟨hLF, htt, n, hside, hn⟩ := hst.torus
  have hnpos : 64 ≤ n := h64'.trans hn
  have hoddF : Odd F.blockSide := by rw [hLF]; exact hDr.odd_L
  have hcub : IsLargeCubicTorus F := ⟨n, hnpos, hside⟩
  have hfin : Finite F.Cell := by
    have hper : ∀ i, F.period F.top i = F.extent i := fun i => by simp [BlockFrame.period]
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      rw [hper, hside]
      omega⟩
    exact Pi.finite
  obtain ⟨-, -, hsym, htri, -⟩ := hg1 F hoddF hcub
  have hN : ∀ z : F.Cell,
      (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤
      4 * T.L ^ 4 := fun z => by
    have := hFew F hoddF (fun i => by rw [hside]; omega) z
    rwa [hLF] at this
  have cb : CumulantBoundsHold T.ballRadius x T.κ (T₀ (4 * T.L ^ 4) T.κ T.chainParams.lam)
      (cutoffFactor T.ballRadius T.p) Ψ'
      (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) :=
    fun M' H Z hh' C h2 h9 hc h0 hq hs =>
      (hT₀' (4 * T.L ^ 4) T.κ T.chainParams.lam hκ hlam F _
        (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) T.ballRadius x T.p Ψ' K'
        hρ hx hDr.cutoff hN hconvex hslope M' H Z hh' C h2 h9 hc h0 hq hs).2
  have hres := slotMean_deriv_bound hRim hDom hDW hEnds hTwo hExp T hρ hDr.cutoff hκ
    (Cq := Cq (parametersBeforeSide T))
    (Cp := Cp (sizeParameters T)) (fun q => hCq _ q) (fun q => (hCp _ q).le) (hA (parametersBeforeSide T))
    (hT₀ _ _ _ hκ hlam) hst hrow hh hfin hsym htri Ψ' hd hz cb
    (fun V' hV' => (hXb t x F V' false hfl ⟨hLF, htt, n, hside, hn⟩ hV').1)
    (hRb t x f F V false hfl hrow ⟨hLF, htt, n, hside, hn⟩ hst.small_curvature) hLocT hsl
  refine ⟨hres.1, fun k c X h1 h3 hX => (hres.2 k c X h1 h3 hX).trans ?_⟩
  have hE := (Real.exp_pos (-(T.κ / 2 ^ 5 * (bondSpan Y c : ℝ)))).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hh.le) hE
end ResponseInTheExpansion
end YangMills.Construction
end
