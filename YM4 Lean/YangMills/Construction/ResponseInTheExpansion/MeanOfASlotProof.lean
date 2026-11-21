import YangMills.Construction.ResponseInTheExpansion.MeanOfASlot
import YangMills.Construction.ResponseInTheExpansion.MeanOfASlotOfOrderTwoProof
import YangMills.Construction.ResponseInTheExpansion.ThirdOrderOfASlot
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open MeasureTheory
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames WeightedResponses Interpolation Cumulants ConvexObservables
namespace ResponseInTheExpansion
namespace SlotExpectation
variable {F : BlockFrame}
theorem single_vec_one {k : ℕ} (a : Fin k) :
    (![Pi.single a 1] : Fin 1 → Fin k → ℝ) = fun l => Pi.single ((![a] : Fin 1 → Fin k) l) 1 := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.basisVectors_one <;> assumption
theorem single_vec_two {k : ℕ} (a b : Fin k) :
    (![Pi.single a 1, Pi.single b 1] : Fin 2 → Fin k → ℝ) =
      fun l => Pi.single ((![a, b] : Fin 2 → Fin k) l) 1 := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.basisVectors_two <;> assumption
theorem single_vec_three {k : ℕ} (a b d : Fin k) :
    (![Pi.single a 1, Pi.single b 1, Pi.single d 1] : Fin 3 → Fin k → ℝ) =
      fun l => Pi.single ((![a, b, d] : Fin 3 → Fin k) l) 1 := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.basisVectors_three <;> assumption
theorem bondSpan_le_two_mul (hsym : ∀ a b : F.Cell, cellSupDist a b = cellSupDist b a)
    (htri : ∀ a b d : F.Cell, cellSupDist a d ≤ cellSupDist a b + cellSupDist b d) {k : ℕ} (Y : F.Cell)
    (c : Fin k → F.Site F.top × Fin 4) (R : ℕ) (hall : ∀ l, cellSupDist Y (c l).1 ≤ R) : bondSpan Y c ≤ 2 * R := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.bondSpan_le_two_mul <;> assumption
theorem exp_product_le_exp_span {κ n s D d₁ d₂ d₃ : ℝ} (hκ : 0 ≤ κ) (hn : n ≤ 2 * (s + D + d₁ + d₂ + d₃))
    (hs : 0 ≤ s) (hD : 0 ≤ D) (h1 : 0 ≤ d₁) (h2 : 0 ≤ d₂) (h3 : 0 ≤ d₃) :
    Real.exp (-(2 ^ 5 * κ * s)) * Real.exp (-(2 ^ 3 * κ * d₁)) * Real.exp (-(2 ^ 3 * κ * d₂)) *
        Real.exp (-(2 ^ 3 * κ * d₃)) * Real.exp (-(κ / 8 * D)) ≤ Real.exp (-(κ / 2 ^ 5 * n)) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.exp_product_le <;> assumption
section Terms
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def CumulantBoundsHold (ρ x κ T₀ : ℝ) (r : ℝ → ℝ) (Ψ : BondField ι → ℝ) (y : ι → F.Cell) : Prop :=
  ∀ (M : ℕ) (H : Fin M → BondField ι → ℝ) (Z : Fin M → F.Cell) (hh : Fin M → ℝ) (C : Fin M → ℕ → ℝ),
    2 ≤ M → M ≤ 9 → (∀ i, ContDiffOn ℝ 1 (H i) {η | ∀ b, ‖η b‖ < ρ}) → (∀ i, 0 ≤ hh i) → (∀ i q, 0 ≤ C i q) →
    (∀ i, HasLocalSize ρ r Ψ (C i) x κ (hh i) (fun b => (cellSupDist (y b) (Z i) : ℝ)) (H i)) →
    |cumulantFromMoments r Ψ H| ≤ T₀ * (∏ i, (sizeConstantSum (C i) M * hh i)) *
      Real.exp (-(κ / 8 * cellsDiameter Z))
variable {ρ x κ T₀ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ} {y : ι → F.Cell}
structure LocalObservable (ρ x κ : ℝ) (r : ℝ → ℝ) (Ψ : BondField ι → ℝ) (y : ι → F.Cell) (C : ℕ → ℝ) (a : ℝ)
    (Z : F.Cell) (G : BondField ι → ℝ) : Prop where
  smooth : ContDiffOn ℝ 1 G {η | ∀ b, ‖η b‖ < ρ}
  hasLocalSize : HasLocalSize ρ r Ψ C x κ a (fun b => (cellSupDist (y b) Z : ℝ)) G
  amplitude_nonneg : 0 ≤ a
  constants_nonneg : ∀ q, 0 ≤ C q
theorem abs_ballCovariance_le (cb : CumulantBoundsHold ρ x κ T₀ r Ψ y)
    (he : ∀ H : Fin 2 → BondField ι → ℝ, cumulantFromMoments r Ψ H = ballCovariance r Ψ (H 0) (H 1))
    {C₀ C₁ : ℕ → ℝ} {a₀ a₁ : ℝ} {Z₀ Z₁ : F.Cell} {G₀ G₁ : BondField ι → ℝ}
    (o₀ : LocalObservable ρ x κ r Ψ y C₀ a₀ Z₀ G₀) (o₁ : LocalObservable ρ x κ r Ψ y C₁ a₁ Z₁ G₁) :
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
    (o₀ : LocalObservable ρ x κ r Ψ y C₀ a₀ Z₀ G₀) (o₁ : LocalObservable ρ x κ r Ψ y C₁ a₁ Z₁ G₁)
    (o₂ : LocalObservable ρ x κ r Ψ y C₂ a₂ Z₂ G₂) :
    |ballThirdCumulant r Ψ G₀ G₁ G₂| ≤ T₀ * ((sizeConstantSum C₀ 3 * a₀) * (sizeConstantSum C₁ 3 * a₁) *
      (sizeConstantSum C₂ 3 * a₂)) * Real.exp (-(κ / 8 * cellsDiameter ![Z₀, Z₁, Z₂])) := by
  have := cb 3 ![G₀, G₁, G₂] ![Z₀, Z₁, Z₂] ![a₀, a₁, a₂] ![C₀, C₁, C₂] (by norm_num) (by norm_num)
    (fun i => by fin_cases i; exacts [o₀.smooth, o₁.smooth, o₂.smooth])
    (fun i => by fin_cases i; exacts [o₀.amplitude_nonneg, o₁.amplitude_nonneg, o₂.amplitude_nonneg])
    (fun i q => by fin_cases i; exacts [o₀.constants_nonneg q, o₁.constants_nonneg q, o₂.constants_nonneg q])
    (fun i => by fin_cases i; exacts [o₀.hasLocalSize, o₁.hasLocalSize, o₂.hasLocalSize])
  rw [he] at this
  simpa [Fin.prod_univ_three] using this
theorem abs_ballFourthCumulant_le (cb : CumulantBoundsHold ρ x κ T₀ r Ψ y)
    (he : ∀ H : Fin 4 → BondField ι → ℝ,
      cumulantFromMoments r Ψ H = ballFourthCumulant r Ψ (H 0) (H 1) (H 2) (H 3))
    {C₀ C₁ C₂ C₃ : ℕ → ℝ} {a₀ a₁ a₂ a₃ : ℝ} {Z₀ Z₁ Z₂ Z₃ : F.Cell} {G₀ G₁ G₂ G₃ : BondField ι → ℝ}
    (o₀ : LocalObservable ρ x κ r Ψ y C₀ a₀ Z₀ G₀) (o₁ : LocalObservable ρ x κ r Ψ y C₁ a₁ Z₁ G₁)
    (o₂ : LocalObservable ρ x κ r Ψ y C₂ a₂ Z₂ G₂) (o₃ : LocalObservable ρ x κ r Ψ y C₃ a₃ Z₃ G₃) :
    |ballFourthCumulant r Ψ G₀ G₁ G₂ G₃| ≤ T₀ * ((sizeConstantSum C₀ 4 * a₀) * (sizeConstantSum C₁ 4 * a₁) *
      (sizeConstantSum C₂ 4 * a₂) * (sizeConstantSum C₃ 4 * a₃)) *
      Real.exp (-(κ / 8 * cellsDiameter ![Z₀, Z₁, Z₂, Z₃])) := by
  have := cb 4 ![G₀, G₁, G₂, G₃] ![Z₀, Z₁, Z₂, Z₃] ![a₀, a₁, a₂, a₃] ![C₀, C₁, C₂, C₃] (by norm_num) (by norm_num)
    (fun i => by fin_cases i; exacts [o₀.smooth, o₁.smooth, o₂.smooth, o₃.smooth])
    (fun i => by fin_cases i; exacts [o₀.amplitude_nonneg, o₁.amplitude_nonneg, o₂.amplitude_nonneg, o₃.amplitude_nonneg])
    (fun i q => by fin_cases i; exacts [o₀.constants_nonneg q, o₁.constants_nonneg q, o₂.constants_nonneg q,
      o₃.constants_nonneg q])
    (fun i => by fin_cases i; exacts [o₀.hasLocalSize, o₁.hasLocalSize, o₂.hasLocalSize, o₃.hasLocalSize])
  rw [he] at this
  simpa [Fin.prod_univ_four] using this
end Terms
theorem gibbsMean_congr_ae {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {A A' H H' : Ω → ℝ}
    (hA : A =ᵐ[μ] A') (hH : H =ᵐ[μ] H') : gibbsMean μ A H = gibbsMean μ A' H' := by apply _root_.YangMills.Construction.InterpolatedBirths.gibbsMean_congr_ae <;> assumption
def translatedExponent (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (x : ℝ) (f : LocalFamily) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ Y ∈ finiteCells F, cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y (leftTranslate (bondSpread c X τ) V) η -
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth,
      centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y η (leftTranslate (bondSpread c X τ) V)
theorem exponent_eq_sum (hEnds : interpolationAtEndpoints) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) {x : ℝ} {f : LocalFamily}
    {V' : F.GaugeField F.top}
    (hX : CellExponentBounds false T.a T.chainParams.ρA T.ballRadius x T.κ T.Ct (frameRadius x) V')
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < T.ballRadius) :
    (coldHalfLawAt T x f).exponent V' η =
      ∑ Y ∈ finiteCells F, cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y V' η -
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y η V' := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.coldHalfLaw_exponent_eq <;> assumption
theorem translated_expectation (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedFamilyOnClosedBalls)
    (hEnds : interpolationAtEndpoints) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hρ : 0 < T.ballRadius) (hcut : IsCutoff T.ballRadius T.p)
    {x : ℝ} {f : LocalFamily} {V : F.GaugeField F.top} (K : AboveFrames F) (hfin : Finite F.Cell)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V)
    (hXc : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
      CellExponentBounds false T.a T.chainParams.ρA T.ballRadius x T.κ T.Ct (frameRadius x) V')
    (hR : CentredExpansionBounds false T.a T.chainParams.ρA T.ballRadius T.κ T.decayRate T.E T.energyRatio T.Ct T.L
      (frameRadius x) f V)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hK : ∀ (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      ContDiffAt ℝ 3 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
        K q.2 (leftTranslate (bondSpread c X q.1) V)) (0, η)) :
    ∃ (B : Set (Fin k → ℝ)) (Kb : ℝ), IsOpen B ∧ B ∈ 𝓝 (0 : Fin k → ℝ) ∧
      IsDominatedSmoothFamily (cutoffLaw F T.ballRadius T.p) 3 B Kb (translatedExponent T x f V c X) ∧
      IsDominatedSmoothFamily (cutoffLaw F T.ballRadius T.p) 3 B Kb
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
  have sGm : ∀ η : Sv, (∀ b, ‖η b‖ ≤ T.ballRadius) → ContDiffAt ℝ 3 Gm (0, η) := fun η hη =>
    (ContDiffAt.sum fun Y _ => hEV.smooth Y η k c X hη).sub (ContDiffAt.sum fun y _ => hR.smooth y η k c X hη)
  let π : (Fin k → ℝ) × (ℝ × Sv) → (Fin k → ℝ) × Sv := fun z => (z.1, z.2.2)
  have hπs : ContDiff ℝ 3 π := contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
  have lift : ∀ {G : (Fin k → ℝ) × Sv → ℝ}, (∀ η : Sv, (∀ b, ‖η b‖ ≤ T.ballRadius) → ContDiffAt ℝ 3 G (0, η)) →
      ∀ (v : ℝ) (η : Sv), (∀ b, ‖η b‖ ≤ T.ballRadius) →
        ContDiffAt ℝ 3 (fun z : (Fin k → ℝ) × (ℝ × Sv) => G (π z)) (0, v, η) := fun {G} hG v η hη =>
    ContDiffAt.comp (g := G) (f := π) (0, v, η) (hG η hη) hπs.contDiffAt
  obtain ⟨r₁, M₁, hr₁, hD₁⟩ := hDom _ k T.ballRadius (cutoffLaw F T.ballRadius T.p) (fun z => Gm (π z)) hμc
    (fun v η _ hη => lift sGm v η hη)
  obtain ⟨r₂, M₂, hr₂, hD₂⟩ := hDom _ k T.ballRadius (cutoffLaw F T.ballRadius T.p) (fun z => Gk (π z)) hμc
    (fun v η _ hη => lift hK v η hη)
  obtain ⟨r₀, hr₀, hcold⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_isSmallCurvature_leftTranslate hfin c X hV)
  have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have dom_mono : ∀ {r M r' M' : ℝ} {G : (Fin k → ℝ) → Sv → ℝ}, r' ≤ r → M ≤ M' →
      IsDominatedSmoothFamily (cutoffLaw F T.ballRadius T.p) 3 (Metric.ball 0 r) M G →
      IsDominatedSmoothFamily (cutoffLaw F T.ballRadius T.p) 3 (Metric.ball 0 r') M' G :=
    fun {r M r' M' G} hr hM h => by
    have hB := Metric.ball_subset_ball (x := (0 : Fin k → ℝ)) hr
    refine ⟨fun τ hτ => h.aestronglyMeasurable τ (hB hτ), ?_, ?_⟩
    · filter_upwards [h.contDiffOn] with ω hω using hω.mono hB
    · filter_upwards [h.norm_iteratedFDeriv_le] with ω hω j hj τ hτ using le_trans (hω j hj τ (hB hτ)) hM
  set r : ℝ := min r₀ (min r₁ r₂) with hr
  have hrpos : 0 < r := lt_min hr₀ (lt_min hr₁ hr₂)
  refine ⟨Metric.ball 0 r, max M₁ M₂, Metric.isOpen_ball, Metric.ball_mem_nhds _ hrpos, ?_, ?_, ?_⟩
  · exact dom_mono ((min_le_right _ _).trans (min_le_left _ _)) (le_max_left _ _) (hD₁ 0 h01)
  · exact dom_mono ((min_le_right _ _).trans (min_le_right _ _)) (le_max_right _ _) (hD₂ 0 h01)
  · intro τ hτ
    have hc := hcold τ (Metric.ball_subset_ball (min_le_left _ _) hτ)
    show cutoffMean T.ballRadius T.p _ _ = _
    rw [hμm]
    apply gibbsMean_congr_ae
    · filter_upwards [hμb] with η hη
      exact exponent_eq_sum hEnds T (hXc _ hc) η hη
    · exact Filter.EventuallyEq.rfl
theorem cellSupDist_le_cellsDiameter {M : ℕ} (Z : Fin M → F.Cell) (i j : Fin M) :
    cellSupDist (Z i) (Z j) ≤ cellsDiameter Z := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.cellSupDist_le_cellsDiameter <;> assumption
theorem cellSupDist_le_add_bondListDiameter
    (htri : ∀ a b d : F.Cell, cellSupDist a d ≤ cellSupDist a b + cellSupDist b d) {j : ℕ}
    (c' : Fin j → F.Site F.top × Fin 4) (Y : F.Cell) (l₀ m : Fin j) :
    cellSupDist Y (c' m).1 ≤ cellSupDist Y (c' l₀).1 + _root_.YangMills.Construction.BlockAverages.bondListDiameter c' := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.cellSupDist_le_add_bondListDiameter <;> assumption
theorem cellSupDist_le_bondSpan {j : ℕ} (c' : Fin j → F.Site F.top × Fin 4) (Y : F.Cell) (m : Fin j) :
    cellSupDist Y (c' m).1 ≤ bondSpan Y c' :=
  le_trans (Finset.le_sup (f := fun l : Fin j => siteSupDist Y (c' l).1) (Finset.mem_univ m)) (le_max_left _ _)
theorem sizeConstantSum_le_four {C : ℕ → ℝ} (hC : ∀ q, 0 ≤ C q) {M : ℕ} (hM : M ≤ 4) :
    sizeConstantSum C M ≤ sizeConstantSum C 4 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.sizeConstantSum_le_four <;> assumption
theorem one_le_sizeConstantSum {C : ℕ → ℝ} (hC : ∀ q, 0 ≤ C q) (M : ℕ) : 1 ≤ sizeConstantSum C M := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.one_le_sizeConstantSum <;> assumption
theorem product_bound_two {T₀ c₀ c₁ A h E₀ E₁ ED cK cP E : ℝ} (hT : 0 ≤ T₀) (hh : 0 ≤ h) (hA : 0 ≤ A)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (h₀ : c₀ ≤ cK) (h₁ : c₁ ≤ cP) (hcP : 1 ≤ cP) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁)
    (hED : 0 ≤ ED) (hE : E₀ * E₁ * ED ≤ E) :
    T₀ * ((c₀ * (h * E₀)) * (c₁ * (A * E₁))) * ED ≤ T₀ * (cK * (cP * (1 + A)) ^ 3) * h * E := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.second_order_product_le <;> assumption
theorem product_bound_three {T₀ c₀ c₁ c₂ A h E₀ E₁ E₂ ED cK cP E : ℝ} (hT : 0 ≤ T₀) (hh : 0 ≤ h) (hA : 0 ≤ A)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (h₀ : c₀ ≤ cK) (h₁ : c₁ ≤ cP) (h₂ : c₂ ≤ cP) (hcP : 1 ≤ cP)
    (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) (hED : 0 ≤ ED) (hE : E₀ * E₁ * E₂ * ED ≤ E) :
    T₀ * ((c₀ * (h * E₀)) * (c₁ * (A * E₁)) * (c₂ * (A * E₂))) * ED ≤ T₀ * (cK * (cP * (1 + A)) ^ 3) * h * E := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.third_order_product_le <;> assumption
theorem product_bound_four {T₀ c₀ c₁ c₂ c₃ A h E₀ E₁ E₂ E₃ ED cK cP E : ℝ} (hT : 0 ≤ T₀) (hh : 0 ≤ h)
    (hA : 0 ≤ A) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (h₀ : c₀ ≤ cK) (h₁ : c₁ ≤ cP)
    (h₂ : c₂ ≤ cP) (h₃ : c₃ ≤ cP) (hcP : 1 ≤ cP) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) (hE₃ : 0 ≤ E₃)
    (hED : 0 ≤ ED) (hE : E₀ * E₁ * E₂ * E₃ * ED ≤ E) :
    T₀ * ((c₀ * (h * E₀)) * (c₁ * (A * E₁)) * (c₂ * (A * E₂)) * (c₃ * (A * E₃))) * ED ≤
      T₀ * (cK * (cP * (1 + A)) ^ 3) * h * E := by
  have hcK : 0 ≤ cK := hc₀.trans h₀
  have a1 : c₀ * ((c₁ * A) * (c₂ * A) * (c₃ * A)) ≤ cK * (cP * (1 + A)) ^ 3 := by
    have b1 : c₁ * A ≤ cP * (1 + A) := mul_le_mul h₁ (by linarith) hA (by linarith)
    have b2 : c₂ * A ≤ cP * (1 + A) := mul_le_mul h₂ (by linarith) hA (by linarith)
    have b3 : c₃ * A ≤ cP * (1 + A) := mul_le_mul h₃ (by linarith) hA (by linarith)
    have b4 : (c₁ * A) * (c₂ * A) * (c₃ * A) ≤ (cP * (1 + A)) ^ 3 := by
      have e : (cP * (1 + A)) ^ 3 = (cP * (1 + A)) * (cP * (1 + A)) * (cP * (1 + A)) := by ring
      rw [e]
      have hP0 : 0 ≤ cP * (1 + A) := mul_nonneg (by linarith) (by linarith)
      exact mul_le_mul (mul_le_mul b1 b2 (by positivity) hP0) b3 (by positivity) (by positivity)
    exact mul_le_mul h₀ b4 (by positivity) hcK
  calc T₀ * ((c₀ * (h * E₀)) * (c₁ * (A * E₁)) * (c₂ * (A * E₂)) * (c₃ * (A * E₃))) * ED =
        T₀ * (c₀ * ((c₁ * A) * (c₂ * A) * (c₃ * A))) * h * (E₀ * E₁ * E₂ * E₃ * ED) := by ring
    _ ≤ T₀ * (cK * (cP * (1 + A)) ^ 3) * h * E := by gcongr
theorem slot_expectation_deriv_bound (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedFamilyOnClosedBalls)
    (hDW : GibbsMeanDifferentiation) (hEnds : interpolationAtEndpoints)
    (hTwo : Calculus.IteratedFDerivParamDiff) (hExp : lowOrderCumulantFormulas)
    (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hρ : 0 < T.ballRadius) (hcut : IsCutoff T.ballRadius T.p) (hκ : 0 < T.κ) {Cq Cp : ℕ → ℝ}
    (hCq : ∀ q, 0 ≤ Cq q) (hCp : ∀ q, 0 ≤ Cp q) {A B₃ T₀ : ℝ} (hA : 0 ≤ A) (hB₃ : 0 ≤ B₃) (hT₀ : 0 ≤ T₀) {t : ℕ}
    {x h : ℝ} {f : LocalFamily} {V : F.GaugeField F.top} {Y : F.Cell} {K : AboveFrames F}
    (hst : IsAdmissibleAt T t x f F V) (hrow : IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f)
    (hh0 : 0 < h) (hfin : Finite F.Cell) (hsym : ∀ a b : F.Cell, cellSupDist a b = cellSupDist b a)
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
    (hEL : IsLocalExponentAt T Cp A) (hTO : slotThirdOrderCovarianceAt T Cq B₃)
    (hsl : IsSlot (coldHalfLawAt T x f) Cq h Y K V) :
    (∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 3 (fun τ : Fin k → ℝ =>
        (coldHalfLawAt T x f).expectationOf K (leftTranslate (bondSpread c X τ) V)) 0) ∧
    ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
      AreUnitVectors X →
      |bondDeriv ((coldHalfLawAt T x f).expectationOf K) V c X -
          (coldHalfLawAt T x f).expectation V (fun η => bondDeriv (K η) V c X)| ≤
        (14 * (T₀ * (sizeConstantSum Cq 4 * (sizeConstantSum Cp 4 * (1 + A)) ^ 3)) + B₃) * h *
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
      have := exponent_eq_sum (f := f) hEnds T (hXc V hst.small_curvature) η hη
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
  · obtain ⟨B, Kb, hBo, hB0, dA, dH, heq⟩ := translated_expectation (f := f) hRim hDom hEnds T hρ hcut K hfin
      hst.small_curvature hXc hR c X (fun η hη => hsl.smoothBounded.smooth η k c X hη)
    obtain ⟨hcd, -⟩ := hDW.2 _ μ k B Kb _ _ hBo hμ0 dA dH
    exact (hcd.contDiffAt hB0).congr_of_eventuallyEq (Filter.eventually_of_mem hB0 heq)
  obtain ⟨B, Kb, hBo, hB0, dA, dH, heq⟩ := translated_expectation (f := f) hRim hDom hEnds T hρ hcut K hfin
    hst.small_curvature hXc hR c X (fun η hη => hsl.smoothBounded.smooth η k c X hη)
  obtain ⟨hcd, hform⟩ := hDW.2 _ μ k B Kb _ _ hBo hμ0 dA dH
  have h0B : (0 : Fin k → ℝ) ∈ B := mem_of_mem_nhds hB0
  let Af := translatedExponent T x f V c X
  let Hf : (Fin k → ℝ) → StepVariable (finiteCells F) → ℝ := fun τ η => K η (leftTranslate (bondSpread c X τ) V)
  let units : ∀ {j : ℕ}, (Fin j → Fin k) → Fin j → Fin k → ℝ := fun ι l => Pi.single (ι l) 1
  let GH : ∀ {j : ℕ}, (Fin j → Fin k) → StepVariable (finiteCells F) → ℝ :=
    fun ι => paramIteratedDeriv Hf (units ι) 0
  let GA : ∀ {j : ℕ}, (Fin j → Fin k) → StepVariable (finiteCells F) → ℝ :=
    fun ι => paramIteratedDeriv Af (units ι) 0
  have hline : ∀ {G : (Fin k → ℝ) × StepVariable (finiteCells F) → ℝ} {η : StepVariable (finiteCells F)},
      ContDiffAt ℝ 3 G (0, η) → ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => G (τ, η)) 0 := fun {G η} hG =>
    ContDiffAt.comp (g := G) (f := fun τ : Fin k → ℝ => (τ, η)) 0 hG
      ((contDiff_id.prodMk contDiff_const).contDiffAt)
  have hofle : ∀ {j : ℕ}, j ≤ 3 → ((j : ℕ) : WithTop ℕ∞) ≤ 3 := fun {j} hj => by exact_mod_cast hj
  have obsH : ∀ {j : ℕ} (ι : Fin j → Fin k), j ≤ 2 →
      LocalObservable T.ballRadius x T.κ r Ψ' y Cq (h * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y (c ∘ ι)))) Y (GH ι) := by
    intro j ι hj
    have hu : AreUnitVectors (X ∘ ι) := fun l => hX (ι l)
    have hs1 := hsl.smoothBounded.deriv_bound j (c ∘ ι) (X ∘ ι) (by omega) hu
    have eqb : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
        bondDeriv (K η) V (c ∘ ι) (X ∘ ι) = GH ι η := fun η hη =>
      (iteratedFDeriv_single_eq_bondDeriv (K η) V c X ι
        ((hline (hsl.smoothBounded.smooth η k c X fun b => (hη b).le)).of_le (hofle (by omega)))).symm
    have hc1 : ContDiffOn ℝ 1 (fun η => bondDeriv (K η) V (c ∘ ι) (X ∘ ι))
        {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} :=
      fun η hη => by
        have hs := hsl.smoothBounded.smooth η j (c ∘ ι) (X ∘ ι) fun b => (hη b).le
        have h1 := (hTwo (Fin j → ℝ) (StepVariable (finiteCells F)) j
          (fun q => K q.2 (leftTranslate (bondSpread (c ∘ ι) (X ∘ ι) q.1) V)) η
          (fun l => Pi.single l 1) (hs.of_le (by exact_mod_cast (by omega : j + 1 ≤ 3)))).1
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
      exact exponent_eq_sum hEnds T (hXc _ hτ) η hη
    have smA : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => Af τ η) 0 := by
      have h1 := (ContDiffAt.sum fun Y' _ => hline ((hXc V hst.small_curvature).smooth Y' η k c X
          fun b => (hη b).le) :
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
      LocalObservable T.ballRadius x T.κ r Ψ' y Cp (A * Real.exp (-(2 ^ 3 * T.κ * _root_.YangMills.Construction.BlockAverages.bondListDiameter (c ∘ ι))))
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
  have t2 : ∀ {j₀ j₁ : ℕ} (ι₀ : Fin j₀ → Fin k) (ι₁ : Fin j₁ → Fin k) (l₁ : Fin j₁), j₀ ≤ 2 → j₁ ≤ 2 →
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
    have hE := exp_product_le_exp_span hκ0 hn' (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      le_rfl le_rfl
    rw [hz0, mul_one, mul_one] at hE
    exact product_bound_two hT₀ hh hA (hc0 _ _ hCq) (hc0 _ _ hCp) (sizeConstantSum_le_four hCq (by norm_num))
      (sizeConstantSum_le_four hCp (by norm_num)) hcP1 (Real.exp_pos _).le (Real.exp_pos _).le
      (Real.exp_pos _).le hE
  have t3 : ∀ {j₀ j₁ j₂ : ℕ} (ι₀ : Fin j₀ → Fin k) (ι₁ : Fin j₁ → Fin k) (ι₂ : Fin j₂ → Fin k) (l₁ : Fin j₁)
      (l₂ : Fin j₂), j₀ ≤ 2 → j₁ ≤ 2 → j₂ ≤ 2 →
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
    have hE := exp_product_le_exp_span hκ0 hn' (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) le_rfl
    rw [hz0, mul_one] at hE
    exact product_bound_three hT₀ hh hA (hc0 _ _ hCq) (hc0 _ _ hCp) (hc0 _ _ hCp)
      (sizeConstantSum_le_four hCq (by norm_num)) (sizeConstantSum_le_four hCp (by norm_num))
      (sizeConstantSum_le_four hCp (by norm_num)) hcP1 (Real.exp_pos _).le
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le hE
  have t4 : ∀ {j₀ j₁ j₂ j₃ : ℕ} (ι₀ : Fin j₀ → Fin k) (ι₁ : Fin j₁ → Fin k) (ι₂ : Fin j₂ → Fin k)
      (ι₃ : Fin j₃ → Fin k) (l₁ : Fin j₁) (l₂ : Fin j₂) (l₃ : Fin j₃), j₀ ≤ 2 → j₁ ≤ 2 → j₂ ≤ 2 → j₃ ≤ 2 →
      (∀ l : Fin k, (∃ m, ι₀ m = l) ∨ (∃ m, ι₁ m = l) ∨ (∃ m, ι₂ m = l) ∨ (∃ m, ι₃ m = l)) →
      |ballFourthCumulant r Ψ' (GH ι₀) (GA ι₁) (GA ι₂) (GA ι₃)| ≤ b := by
    intro j₀ j₁ j₂ j₃ ι₀ ι₁ ι₂ ι₃ l₁ l₂ l₃ h₀ h₁ h₂ h₃ hcov
    have hc := abs_ballFourthCumulant_le cb he4 (obsH ι₀ h₀) (obsA ι₁ l₁ h₁) (obsA ι₂ l₂ h₂) (obsA ι₃ l₃ h₃)
    refine hc.trans ?_
    set s := bondSpan Y (c ∘ ι₀)
    set d₁ := _root_.YangMills.Construction.BlockAverages.bondListDiameter (c ∘ ι₁)
    set d₂ := _root_.YangMills.Construction.BlockAverages.bondListDiameter (c ∘ ι₂)
    set d₃ := _root_.YangMills.Construction.BlockAverages.bondListDiameter (c ∘ ι₃)
    set D := cellsDiameter ![Y, (c (ι₁ l₁)).1, (c (ι₂ l₂)).1, (c (ι₃ l₃)).1]
    have hall : ∀ l, cellSupDist Y (c l).1 ≤ s + D + d₁ + d₂ + d₃ := by
      intro l
      rcases hcov l with ⟨m', rfl⟩ | ⟨m', rfl⟩ | ⟨m', rfl⟩ | ⟨m', rfl⟩
      · have := cellSupDist_le_bondSpan (c ∘ ι₀) Y m'
        simp only [Function.comp] at this
        omega
      · have h1 := cellSupDist_le_add_bondListDiameter htri (c ∘ ι₁) Y l₁ m'
        have h2 := cellSupDist_le_cellsDiameter ![Y, (c (ι₁ l₁)).1, (c (ι₂ l₂)).1, (c (ι₃ l₃)).1] 0 1
        simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
        omega
      · have h1 := cellSupDist_le_add_bondListDiameter htri (c ∘ ι₂) Y l₂ m'
        have h2 := cellSupDist_le_cellsDiameter ![Y, (c (ι₁ l₁)).1, (c (ι₂ l₂)).1, (c (ι₃ l₃)).1] 0 2
        simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val] at h1 h2
        omega
      · have h1 := cellSupDist_le_add_bondListDiameter htri (c ∘ ι₃) Y l₃ m'
        have h2 := cellSupDist_le_cellsDiameter ![Y, (c (ι₁ l₁)).1, (c (ι₂ l₂)).1, (c (ι₃ l₃)).1] 0 3
        simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val] at h1 h2
        omega
    have hn := bondSpan_le_two_mul hsym htri Y c _ hall
    have hn' : (bondSpan Y c : ℝ) ≤ 2 * ((s : ℝ) + D + d₁ + d₂ + d₃) := by
      have : (bondSpan Y c : ℝ) ≤ ((2 * (s + D + d₁ + d₂ + d₃) : ℕ) : ℝ) := Nat.cast_le.2 hn
      push_cast at this
      linarith
    have hE := exp_product_le_exp_span hκ0 hn' (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact product_bound_four hT₀ hh hA (hc0 _ _ hCq) (hc0 _ _ hCp) (hc0 _ _ hCp) (hc0 _ _ hCp)
      (sizeConstantSum_le_four hCq (by norm_num)) (sizeConstantSum_le_four hCp (by norm_num))
      (sizeConstantSum_le_four hCp (by norm_num)) (sizeConstantSum_le_four hCp (by norm_num)) hcP1
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le hE
  have cvU : ∀ f₁ f₂ : StepVariable (finiteCells F) → ℝ,
      gibbsCovariance μ (Af 0) f₁ f₂ = ballCovariance r Ψ' f₁ f₂ := fun f₁ f₂ => by
    unfold gibbsCovariance ballCovariance
    simp only [Af, hwm c X]
  have c3U : ∀ f₁ f₂ f₃ : StepVariable (finiteCells F) → ℝ,
      gibbsCumulantThree μ (Af 0) f₁ f₂ f₃ = ballThirdCumulant r Ψ' f₁ f₂ f₃ := fun f₁ f₂ f₃ => by
    unfold gibbsCumulantThree ballThirdCumulant
    simp only [Af, hwm c X]
  have c4U : ∀ f₁ f₂ f₃ f₄ : StepVariable (finiteCells F) → ℝ,
      gibbsCumulantFour μ (Af 0) f₁ f₂ f₃ f₄ = ballFourthCumulant r Ψ' f₁ f₂ f₃ f₄ := fun f₁ f₂ f₃ f₄ => by
    unfold gibbsCumulantFour ballFourthCumulant
    simp only [Af, hwm c X]
  have e0H : GH (Fin.elim0 : Fin 0 → Fin k) = Hf 0 := by
    funext η
    simp [GH, paramIteratedDeriv]
  have hH1 : ∀ a : Fin k, paramIteratedDeriv Hf ![Pi.single a 1] 0 = GH ![a] := fun a => by
    show _ = paramIteratedDeriv Hf (units ![a]) 0
    simp only [units]
    rw [single_vec_one]
  have hA1 : ∀ a : Fin k, paramIteratedDeriv Af ![Pi.single a 1] 0 = GA ![a] := fun a => by
    show _ = paramIteratedDeriv Af (units ![a]) 0
    simp only [units]
    rw [single_vec_one]
  have hH2 : ∀ a d : Fin k, paramIteratedDeriv Hf ![Pi.single a 1, Pi.single d 1] 0 = GH ![a, d] := fun a d => by
    show _ = paramIteratedDeriv Hf (units ![a, d]) 0
    simp only [units]
    rw [single_vec_two]
  have hA2 : ∀ a d : Fin k, paramIteratedDeriv Af ![Pi.single a 1, Pi.single d 1] 0 = GA ![a, d] := fun a d => by
    show _ = paramIteratedDeriv Af (units ![a, d]) 0
    simp only [units]
    rw [single_vec_two]
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
        ((hline (hsl.smoothBounded.smooth η k c X fun b => (hη b).le)).of_le (hofle hk3))
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
  have hB3 : 0 ≤ B₃ * h * E := by positivity
  have hrhs : (14 * (T₀ * (cK * (cP * (1 + A)) ^ 3)) + B₃) * h * E = 14 * b + B₃ * h * E := by
    rw [hb]; ring
  rw [hrhs, hmain, hMeq]
  have F1 : ∀ u : Fin k → ℝ, iteratedFDeriv ℝ 1 (fun τ => gibbsMean μ (Af τ) (Hf τ)) 0 ![u] =
      gibbsMean μ (Af 0) (paramIteratedDeriv Hf ![u] 0) -
        gibbsCovariance μ (Af 0) (Hf 0) (paramIteratedDeriv Af ![u] 0) :=
    fun u => (hform 0 h0B u u u).1
  have F2 : ∀ u v : Fin k → ℝ, iteratedFDeriv ℝ 2 (fun τ => gibbsMean μ (Af τ) (Hf τ)) 0 ![v, u] =
      gibbsMean μ (Af 0) (paramIteratedDeriv Hf ![v, u] 0) -
        gibbsCovariance μ (Af 0) (paramIteratedDeriv Hf ![u] 0) (paramIteratedDeriv Af ![v] 0) -
        gibbsCovariance μ (Af 0) (paramIteratedDeriv Hf ![v] 0) (paramIteratedDeriv Af ![u] 0) -
        gibbsCovariance μ (Af 0) (Hf 0) (paramIteratedDeriv Af ![v, u] 0) +
        gibbsCumulantThree μ (Af 0) (Hf 0) (paramIteratedDeriv Af ![u] 0) (paramIteratedDeriv Af ![v] 0) :=
    fun u v => (hform 0 h0B u v v).2.1
  have F3 : ∀ u v w : Fin k → ℝ, iteratedFDeriv ℝ 3 (fun τ => gibbsMean μ (Af τ) (Hf τ)) 0 ![w, v, u] =
      gibbsMean μ (Af 0) (paramIteratedDeriv Hf ![w, v, u] 0) -
        gibbsCovariance μ (Af 0) (paramIteratedDeriv Hf ![v, u] 0) (paramIteratedDeriv Af ![w] 0) -
        gibbsCovariance μ (Af 0) (paramIteratedDeriv Hf ![w, u] 0) (paramIteratedDeriv Af ![v] 0) -
        gibbsCovariance μ (Af 0) (paramIteratedDeriv Hf ![w, v] 0) (paramIteratedDeriv Af ![u] 0) -
        gibbsCovariance μ (Af 0) (paramIteratedDeriv Hf ![u] 0) (paramIteratedDeriv Af ![w, v] 0) -
        gibbsCovariance μ (Af 0) (paramIteratedDeriv Hf ![v] 0) (paramIteratedDeriv Af ![w, u] 0) -
        gibbsCovariance μ (Af 0) (paramIteratedDeriv Hf ![w] 0) (paramIteratedDeriv Af ![v, u] 0) +
        gibbsCumulantThree μ (Af 0) (paramIteratedDeriv Hf ![u] 0) (paramIteratedDeriv Af ![v] 0)
          (paramIteratedDeriv Af ![w] 0) +
        gibbsCumulantThree μ (Af 0) (paramIteratedDeriv Hf ![v] 0) (paramIteratedDeriv Af ![u] 0)
          (paramIteratedDeriv Af ![w] 0) +
        gibbsCumulantThree μ (Af 0) (paramIteratedDeriv Hf ![w] 0) (paramIteratedDeriv Af ![u] 0)
          (paramIteratedDeriv Af ![v] 0) -
        gibbsCovariance μ (Af 0) (Hf 0) (paramIteratedDeriv Af ![w, v, u] 0) +
        gibbsCumulantThree μ (Af 0) (Hf 0) (paramIteratedDeriv Af ![v, u] 0) (paramIteratedDeriv Af ![w] 0) +
        gibbsCumulantThree μ (Af 0) (Hf 0) (paramIteratedDeriv Af ![w, u] 0) (paramIteratedDeriv Af ![v] 0) +
        gibbsCumulantThree μ (Af 0) (Hf 0) (paramIteratedDeriv Af ![w, v] 0) (paramIteratedDeriv Af ![u] 0) -
        gibbsCumulantFour μ (Af 0) (Hf 0) (paramIteratedDeriv Af ![u] 0) (paramIteratedDeriv Af ![v] 0)
          (paramIteratedDeriv Af ![w] 0) := fun u v w => (hform 0 h0B u v w).2.2
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
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
    have a4 := abs_le.1 (t3 (Fin.elim0 : Fin 0 → Fin 2) ![1] ![0] 0 0 (by norm_num) (by norm_num) (by norm_num)
      (by decide))
    refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]
  · have u3 : (fun l : Fin 3 => (Pi.single l 1 : Fin 3 → ℝ)) = ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] := by
      funext l; fin_cases l <;> rfl
    rw [u3, F3]
    simp only [cvU, c3U, c4U, hA1, hH1, hA2, hH2, ← e0H]
    have a1 := abs_le.1 (t2 ![1, 2] ![0] 0 (by norm_num) (by norm_num) (by decide))
    have a2 := abs_le.1 (t2 ![0, 2] ![1] 0 (by norm_num) (by norm_num) (by decide))
    have a3 := abs_le.1 (t2 ![0, 1] ![2] 0 (by norm_num) (by norm_num) (by decide))
    have a4 := abs_le.1 (t2 ![2] ![0, 1] 0 (by norm_num) (by norm_num) (by decide))
    have a5 := abs_le.1 (t2 ![1] ![0, 2] 0 (by norm_num) (by norm_num) (by decide))
    have a6 := abs_le.1 (t2 ![0] ![1, 2] 0 (by norm_num) (by norm_num) (by decide))
    have a7 := abs_le.1 (t3 ![2] ![1] ![0] 0 0 (by norm_num) (by norm_num) (by norm_num) (by decide))
    have a8 := abs_le.1 (t3 ![1] ![2] ![0] 0 0 (by norm_num) (by norm_num) (by norm_num) (by decide))
    have a9 := abs_le.1 (t3 ![0] ![2] ![1] 0 0 (by norm_num) (by norm_num) (by norm_num) (by decide))
    have a10 := abs_le.1 (t3 (Fin.elim0 : Fin 0 → Fin 3) ![1, 2] ![0] 0 0 (by norm_num) (by norm_num)
      (by norm_num) (by decide))
    have a11 := abs_le.1 (t3 (Fin.elim0 : Fin 0 → Fin 3) ![0, 2] ![1] 0 0 (by norm_num) (by norm_num)
      (by norm_num) (by decide))
    have a12 := abs_le.1 (t3 (Fin.elim0 : Fin 0 → Fin 3) ![0, 1] ![2] 0 0 (by norm_num) (by norm_num)
      (by norm_num) (by decide))
    have a13 := abs_le.1 (t4 (Fin.elim0 : Fin 0 → Fin 3) ![2] ![1] ![0] 0 0 0 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by decide))
    have a14 := hTO t x h f F V Y K c X hst hrow hh0 hsl hX
    have hi3 : c ∘ (![0, 1, 2] : Fin 3 → Fin 3) = c := by
      funext l; fin_cases l <;> rfl
    have hx3 : X ∘ (![0, 1, 2] : Fin 3 → Fin 3) = X := by
      funext l; fin_cases l <;> rfl
    have hG3 : paramIteratedDeriv Af ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] 0 =
        GA (![0, 1, 2] : Fin 3 → Fin 3) := by
      show _ = paramIteratedDeriv Af (units ![0, 1, 2]) 0
      simp only [units]
      rw [single_vec_three]
    have hcv : Q.covariance V (fun η => K η V) (fun η => bondDeriv (fun V' => Q.exponent V' η) V c X) =
        ballCovariance r Ψ' (GH (Fin.elim0 : Fin 0 → Fin 3))
          (paramIteratedDeriv Af ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] 0) := by
      have f1 : GH (Fin.elim0 : Fin 0 → Fin 3) = fun η => K η V := by
        rw [e0H]
        funext η
        simp only [Hf, leftTranslate_bondSpread_zero]
      have s1 : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
          bondDeriv (fun V' => Q.exponent V' η) V c X = GA (![0, 1, 2] : Fin 3 → Fin 3) η := fun η hη => by
        have := eqA (![0, 1, 2] : Fin 3 → Fin 3) le_rfl η hη
        rwa [hi3, hx3] at this
      rw [f1, hG3]
      show ballCovariance r (Q.exponent V) _ _ = _
      unfold ballCovariance
      have e1 : ∀ g : StepVariable (finiteCells F) → ℝ, ballExpectation r (Q.exponent V) g =
          ballExpectation r Ψ' g := fun g => by
        unfold ballExpectation
        rw [hd]
      have m1 := mean_ball (fun η => K η V * bondDeriv (fun V' => Q.exponent V' η) V c X)
        (fun η => K η V * GA (![0, 1, 2] : Fin 3 → Fin 3) η) (fun η hη => by
          show K η V * bondDeriv (fun V' => Q.exponent V' η) V c X = K η V * GA (![0, 1, 2] : Fin 3 → Fin 3) η
          rw [s1 η hη])
      have m2 := mean_ball (fun η => bondDeriv (fun V' => Q.exponent V' η) V c X)
        (GA (![0, 1, 2] : Fin 3 → Fin 3)) s1
      rw [e1, e1, e1, m1, m2]
    rw [hcv, ← hEdef] at a14
    have a14' := abs_le.1 a14
    refine abs_le.2 ⟨?_, ?_⟩ <;>
      linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2, a5.1, a5.2, a6.1, a6.2, a7.1, a7.2, a8.1, a8.2,
        a9.1, a9.2, a10.1, a10.2, a11.1, a11.2, a12.1, a12.2, a13.1, a13.2, a14'.1, a14'.2]
end SlotExpectation
open SlotExpectation in
theorem slotExpectationDerivStatement_holds (hRim : CutoffMeanIsGibbsMean) (hDom : DominatedFamilyOnClosedBalls)
    (hDW : GibbsMeanDifferentiation) (hEnds : interpolationAtEndpoints)
    (hTwo : Calculus.IteratedFDerivParamDiff) (hExp : lowOrderCumulantFormulas)
    (hEL : exponentLocalityStatement) (hTO : slotThirdOrderCovarianceStatement)
    (hCum : cumulantDecayBound) (hFew : Estimates.cellBondsCardStatement)
    (hLaw : normalizedBallLawIsProbabilityStatement)
    (hFB : interpolatedFramesStatement) (hB : CellExponentsBounded)
    (hRw : CentredExpansionsBounded) (hG : CubicTorusCellGeometry)
    (hJ : EventuallyInParametersCombines) : slotExpectationDerivStatement := by
  classical
  intro Cq hCq
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cm, Cz, Cr, hP⟩ := hFB
  obtain ⟨Cp, A, hCp, hA, hLoc⟩ := hEL
  obtain ⟨B₃, hB₃, hThird⟩ := hTO Cq hCq
  obtain ⟨hg1, -⟩ := hG
  choose! T₀ hT₀ hT₀' using hCum
  have h64 : EventuallyInParameters fun T => 64 ≤ T.n₀ ∧ 1 ≤ T.coupling := fun _ _ => ⟨0, fun _ _ _ _ _ =>
    ⟨0, fun _ _ => ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨64, fun _ h => ⟨0, fun _ _ => ⟨1, fun _ hy => ⟨h, hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine ⟨fun U => |14 * (T₀ (4 * U.L ^ 4) U.κ U.chainParams.lam * (sizeConstantSum (Cq (sizeParameters U)) 4 *
      (sizeConstantSum (Cp (sizeParameters U)) 4 * (1 + A U)) ^ 3)) + B₃ U|, fun T => abs_nonneg _, ?_⟩
  refine weaken _ _ ?_ (join _ _ hP (join _ _ h64 (join _ _ hLoc (join _ _ hThird (join _ _ hB hRw)))))
  rintro T hDr ⟨hPT, ⟨h64', hy1⟩, hLocT, hThirdT, hXb, hRb⟩
  intro t x h f F V Y K hst hrow hh hsl
  have hfl : T.coupling ≤ x := hst.coupling_le
  have hx1 : 1 ≤ x := hy1.trans hfl
  have hx : 0 < x := by linarith
  have hPT' := hPT t x hfl
  set Q := coldHalfLawAt T x f with hQ
  let M : LawOnBondVariables ↥(chordBonds (finiteCells F)) := lawAtTop V (Q.exponent V)
  have hadm : M.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t
      T.n₀ (frameRadius x) (chordBondDist F) :=
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
      (cutoffFactor T.ballRadius T.p) Ψ' (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) :=
    fun M' H Z hh' C h2 h9 hc h0 hq hs =>
      (hT₀' (4 * T.L ^ 4) T.κ T.chainParams.lam hκ hlam F _
        (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) T.ballRadius x T.p Ψ' K'
        hρ hx hDr.cutoff hN hconvex hslope M' H Z hh' C h2 h9 hc h0 hq hs).2
  have hres := slot_expectation_deriv_bound hRim hDom hDW hEnds hTwo hExp T hρ hDr.cutoff hκ
    (Cq := Cq (sizeParameters T)) (Cp := Cp (sizeParameters T)) (fun q => hCq _ q) (fun q => (hCp _ q).le)
    (hA (parametersBeforeSide T)) (hB₃ (parametersBeforeSide T)) (hT₀ _ _ _ hκ hlam) hst hrow hh hfin hsym htri
    Ψ' hd hz cb
    (fun V' hV' => (hXb t x F V' false hfl ⟨hLF, htt, n, hside, hn⟩ hV').1)
    (hRb t x f F V false hfl hrow ⟨hLF, htt, n, hside, hn⟩ hst.small_curvature) hLocT hThirdT hsl
  refine ⟨hres.1, fun k c X h1 h3 hX => (hres.2 k c X h1 h3 hX).trans ?_⟩
  have hE := (Real.exp_pos (-(T.κ / 2 ^ 5 * (bondSpan Y c : ℝ)))).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hh.le) hE
end ResponseInTheExpansion
end YangMills.Construction
end
