import YangMills.Construction.ResponseInTheExpansion.ExponentIsLocalProof
import YangMills.Construction.ResponseInTheExpansion.MeanOfASlotOfOrderTwoProof
import YangMills.Construction.ResponseInTheExpansion.ThirdOrderOfASlot
import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftExists
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open MeasureTheory
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames Interpolation Cumulants ConvexObservables TorusComparison WeightedResponses
namespace ResponseInTheExpansion
namespace ThirdOrderSlot
variable {F : BlockFrame}
section Terms
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def CumulantBoundsHold (ρ x κ T₀ : ℝ) (r : ℝ → ℝ) (Ψ : BondField ι → ℝ) (y : ι → F.Cell) : Prop :=
  ∀ (M : ℕ) (H : Fin M → BondField ι → ℝ) (Z : Fin M → F.Cell) (hh : Fin M → ℝ) (C : Fin M → ℕ → ℝ),
    2 ≤ M → M ≤ 9 → (∀ i, ContDiffOn ℝ 1 (H i) {η | ∀ b, ‖η b‖ < ρ}) → (∀ i, 0 ≤ hh i) → (∀ i q, 0 ≤ C i q) →
    (∀ i, HasLocalSize ρ r Ψ (C i) x κ (hh i) (fun b => (cellSupDist (y b) (Z i) : ℝ)) (H i)) →
    |cumulantFromMoments r Ψ H| ≤ T₀ * (∏ i, (sizeConstantSum (C i) M * hh i)) *
      Real.exp (-(κ / 8 * cellsDiameter Z))
variable {ρ x κ T₀ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ} {y : ι → F.Cell}
structure PlacedObservable (ρ x κ : ℝ) (r : ℝ → ℝ) (Ψ : BondField ι → ℝ) (y : ι → F.Cell) (C : ℕ → ℝ) (a : ℝ)
    (Z : F.Cell) (G : BondField ι → ℝ) : Prop where
  smooth : ContDiffOn ℝ 1 G {η | ∀ b, ‖η b‖ < ρ}
  size : HasLocalSize ρ r Ψ C x κ a (fun b => (cellSupDist (y b) Z : ℝ)) G
  amplitude_nonneg : 0 ≤ a
  const_nonneg : ∀ q, 0 ≤ C q
theorem abs_ballCovariance_le (cb : CumulantBoundsHold ρ x κ T₀ r Ψ y)
    (he : ∀ H : Fin 2 → BondField ι → ℝ, cumulantFromMoments r Ψ H = ballCovariance r Ψ (H 0) (H 1))
    {C₀ C₁ : ℕ → ℝ} {a₀ a₁ : ℝ} {Z₀ Z₁ : F.Cell} {G₀ G₁ : BondField ι → ℝ}
    (o₀ : PlacedObservable ρ x κ r Ψ y C₀ a₀ Z₀ G₀) (o₁ : PlacedObservable ρ x κ r Ψ y C₁ a₁ Z₁ G₁) :
    |ballCovariance r Ψ G₀ G₁| ≤ T₀ * ((sizeConstantSum C₀ 2 * a₀) * (sizeConstantSum C₁ 2 * a₁)) *
      Real.exp (-(κ / 8 * cellsDiameter ![Z₀, Z₁])) := by
  have := cb 2 ![G₀, G₁] ![Z₀, Z₁] ![a₀, a₁] ![C₀, C₁] le_rfl (by norm_num)
    (fun i => by fin_cases i; exacts [o₀.smooth, o₁.smooth])
    (fun i => by fin_cases i; exacts [o₀.amplitude_nonneg, o₁.amplitude_nonneg])
    (fun i q => by fin_cases i; exacts [o₀.const_nonneg q, o₁.const_nonneg q])
    (fun i => by fin_cases i; exacts [o₀.size, o₁.size])
  rw [he] at this
  simpa [Fin.prod_univ_two] using this
end Terms
theorem exponent_eq_sum_sub_sum (hEnds : interpolationAtEndpoints) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) {x : ℝ} {f : LocalFamily}
    {V' : F.GaugeField F.top}
    (hX : CellExponentBounds false T.a T.chainParams.ρA T.ballRadius x T.κ T.Ct (frameRadius x) V')
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < T.ballRadius) :
    (coldHalfLawAt T x f).exponent V' η =
      ∑ Y ∈ finiteCells F, cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y V' η -
        ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y η V' := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SecondOrderSlotMean.coldHalfLaw_exponent_eq <;> assumption
theorem continuousAt_iteratedFDeriv_partial {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q]
    [NormedSpace ℝ Q] (j : ℕ) (G : P × Q → ℝ) (η : Q) (v : Fin j → P) (hG : ContDiffAt ℝ j G (0, η)) :
    ContinuousAt (fun ζ => iteratedFDeriv ℝ j (fun s => G (s, ζ)) 0 v) η := by
  have hev : ∀ᶠ ζ in 𝓝 η, ContDiffAt ℝ j G (0, ζ) := by
    have h1 : ∀ᶠ z in 𝓝 ((0, η) : P × Q), ContDiffAt ℝ j G z := hG.eventually (by simp)
    have h2 : Filter.Tendsto (fun ζ : Q => ((0, ζ) : P × Q)) (𝓝 η) (𝓝 (0, η)) :=
      (Continuous.prodMk continuous_const continuous_id).continuousAt
    exact h2.eventually h1
  have key : ∀ ζ, ContDiffAt ℝ j G (0, ζ) → iteratedFDeriv ℝ j (fun s => G (s, ζ)) 0 v =
      iteratedFDeriv ℝ j G (0, ζ) (fun l => ContinuousLinearMap.inl ℝ P Q (v l)) := by
    intro ζ hζ
    have e : (fun s : P => G (s, ζ)) =
        (fun z : P × Q => G (z + (0, ζ))) ∘ (ContinuousLinearMap.inl ℝ P Q) := by
      funext s
      simp
    have h0 : (ContinuousLinearMap.inl ℝ P Q) (0 : P) = 0 := map_zero _
    have hsh : ContDiffAt ℝ j (fun z : P × Q => G (z + (0, ζ))) ((ContinuousLinearMap.inl ℝ P Q) (0 : P)) := by
      rw [h0]
      have hz : ContDiffAt ℝ j (fun z : P × Q => z + (0, ζ)) 0 := (contDiff_id.add contDiff_const).contDiffAt
      exact ContDiffAt.comp (g := G) 0 (by simpa using hζ) hz
    rw [e, iteratedFDeriv_comp_continuousLinearMap_apply _ hsh, h0, iteratedFDeriv_comp_add_right]
    simp
  have hc : ContinuousAt (fun z => iteratedFDeriv ℝ j G z) ((0, η) : P × Q) :=
    (hG.iteratedFDeriv_right (m := 0) (i := j) (by simp)).continuousAt
  have h2 : ContinuousAt (fun ζ : Q => iteratedFDeriv ℝ j G ((0, ζ) : P × Q)) η :=
    ContinuousAt.comp (g := fun z => iteratedFDeriv ℝ j G z) (f := fun ζ : Q => ((0, ζ) : P × Q)) hc
      (Continuous.prodMk continuous_const continuous_id).continuousAt
  have h3 : ContinuousAt (fun ζ : Q => iteratedFDeriv ℝ j G ((0, ζ) : P × Q)
      (fun l => ContinuousLinearMap.inl ℝ P Q (v l))) η :=
    (ContinuousMultilinearMap.apply ℝ _ ℝ (fun l => ContinuousLinearMap.inl ℝ P Q (v l))).continuous.continuousAt.comp h2
  refine h3.congr ?_
  filter_upwards [hev] with ζ hζ
  exact (key ζ hζ).symm
structure IsBoundedContinuousOnBall {ι : Type} [Fintype ι] (ρ : ℝ) (g : BondField ι → ℝ) : Prop where
  cont : ContinuousOn g {η | ∀ b, ‖η b‖ < ρ}
  bound : ∃ M : ℝ, ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |g η| ≤ M
theorem isBoundedContinuousOnBall_of_continuousAt {ι : Type} [Fintype ι] {ρ : ℝ} {g : BondField ι → ℝ}
    (hc : ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContinuousAt g η) : IsBoundedContinuousOnBall ρ g := by
  have hK : IsCompact {η : BondField ι | ∀ b, ‖η b‖ ≤ ρ} := by
    have : {η : BondField ι | ∀ b, ‖η b‖ ≤ ρ} = Set.univ.pi fun _ => Metric.closedBall (0 : BondVector) ρ := by
      ext η; simp [Set.mem_pi]
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (fun η hη => (hc η hη).continuousWithinAt)
  exact ⟨fun η hη => (hc η fun b => (hη b).le).continuousWithinAt, M, fun η hη => hM η fun b => (hη b).le⟩
section Linear
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ}
structure BallLawFacts (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) : Prop where
  prob : IsProbabilityMeasure (normalizedBallLaw (cutoffFactor ρ p) Ψ)
  mean : ∀ f : BondField ι → ℝ, ∫ η, f η ∂normalizedBallLaw (cutoffFactor ρ p) Ψ = ballExpectation (cutoffFactor ρ p) Ψ f
  ae_mem_ball : ∀ᵐ η ∂normalizedBallLaw (cutoffFactor ρ p) Ψ, ∀ b, ‖η b‖ < ρ
theorem integrable_of_isBoundedContinuousOnBall (hL : BallLawFacts ρ p Ψ) (hO : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ})
    {g : BondField ι → ℝ} (hg : IsBoundedContinuousOnBall ρ g) : Integrable g (normalizedBallLaw (cutoffFactor ρ p) Ψ) := by
  have := hL.prob
  obtain ⟨M, hM⟩ := hg.bound
  have h1 := hg.cont.aestronglyMeasurable (μ := normalizedBallLaw (cutoffFactor ρ p) Ψ) hO.measurableSet
  rw [Measure.restrict_eq_self_of_ae_mem (by exact hL.ae_mem_ball)] at h1
  refine Integrable.of_bound h1 M ?_
  filter_upwards [hL.ae_mem_ball] with η hη
  exact hM η hη
theorem isBoundedContinuousOnBall_mul {f g : BondField ι → ℝ} (hf : IsBoundedContinuousOnBall ρ f)
    (hg : IsBoundedContinuousOnBall ρ g) : IsBoundedContinuousOnBall ρ fun η => f η * g η := by
  obtain ⟨M, hM⟩ := hf.bound
  obtain ⟨N, hN⟩ := hg.bound
  refine ⟨hf.cont.mul hg.cont, M * N, fun η hη => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hM η hη) (hN η hη) (abs_nonneg _) ((abs_nonneg _).trans (hM η hη))
theorem ballCovariance_finsetSum (hL : BallLawFacts ρ p Ψ) (hO : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ}) {J : Type}
    (S : Finset J) {f : BondField ι → ℝ} {g : J → BondField ι → ℝ} (hf : IsBoundedContinuousOnBall ρ f)
    (hg : ∀ j, IsBoundedContinuousOnBall ρ (g j)) :
    ballCovariance (cutoffFactor ρ p) Ψ f (fun η => ∑ j ∈ S, g j η) =
      ∑ j ∈ S, ballCovariance (cutoffFactor ρ p) Ψ f (g j) := by
  classical
  unfold ballCovariance
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  · simp only [← hL.mean, Finset.mul_sum]
    exact integral_finsetSum _ fun j _ =>
      integrable_of_isBoundedContinuousOnBall hL hO (isBoundedContinuousOnBall_mul hf (hg j))
  · congr 1
    simp only [← hL.mean]
    exact integral_finsetSum _ fun j _ => integrable_of_isBoundedContinuousOnBall hL hO (hg j)
end Linear
theorem bondSpan_le_two_mul (hsym : ∀ a b : F.Cell, cellSupDist a b = cellSupDist b a)
    (htri : ∀ a b d : F.Cell, cellSupDist a d ≤ cellSupDist a b + cellSupDist b d) {k : ℕ} (Y Y' : F.Cell)
    (c : Fin k → F.Site F.top × Fin 4) : bondSpan Y c ≤ 2 * (cellSupDist Y Y' + bondSpan Y' c) := by
  have hall : ∀ l, cellSupDist Y (c l).1 ≤ cellSupDist Y Y' + bondSpan Y' c := fun l => by
    have h1 := htri Y Y' (c l).1
    have h2 : cellSupDist Y' (c l).1 ≤ bondSpan Y' c :=
      le_trans (Finset.le_sup (f := fun l : Fin k => siteSupDist Y' (c l).1) (Finset.mem_univ l)) (le_max_left _ _)
    omega
  generalize cellSupDist Y Y' + bondSpan Y' c = R at hall ⊢
  unfold bondSpan
  refine max_le (Finset.sup_le fun l _ => ?_) (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
  · have := hall l
    show cellSupDist Y (c l).1 ≤ _
    omega
  · have h1 := htri (c l).1 Y (c l').1
    have h2 := hall l
    have h3 := hall l'
    have h4 := hsym (c l).1 Y
    show cellSupDist (c l).1 (c l').1 ≤ _
    omega
theorem cellSupDist_le_cellsDiameter (Y Y' : F.Cell) : cellSupDist Y Y' ≤ cellsDiameter ![Y, Y'] := by
  unfold cellsDiameter
  exact le_trans (Finset.le_sup (f := fun j => cellSupDist ((![Y, Y'] : Fin 2 → F.Cell) 0) ((![Y, Y'] : Fin 2 → F.Cell) j))
      (Finset.mem_univ (1 : Fin 2)))
    (Finset.le_sup (f := fun i => Finset.univ.sup fun j =>
        cellSupDist ((![Y, Y'] : Fin 2 → F.Cell) i) ((![Y, Y'] : Fin 2 → F.Cell) j))
      (Finset.mem_univ (0 : Fin 2)))
theorem exp_mul_exp_le {κ n s d D : ℝ} (hκ : 0 ≤ κ) (hn : n ≤ 2 * (d + s)) (hs : 0 ≤ s) (hd : 0 ≤ d) (hD : d ≤ D) :
    Real.exp (-(2 ^ 5 * κ * s)) * Real.exp (-(κ / 8 * D)) ≤
      Real.exp (-(κ / 2 ^ 5 * n)) * Real.exp (-(κ / 16 * d)) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have a1 : κ * n ≤ κ * (2 * (d + s)) := mul_le_mul_of_nonneg_left hn hκ
  have a2 : κ * d ≤ κ * D := mul_le_mul_of_nonneg_left hD hκ
  nlinarith [mul_nonneg hκ hs, mul_nonneg hκ hd]
theorem bondDeriv_exponent_eq (hEnds : interpolationAtEndpoints) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) {x : ℝ} {f : LocalFamily}
    {V : F.GaugeField F.top} (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hfin : Finite F.Cell)
    (hXc : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
      CellExponentBounds false T.a T.chainParams.ρA T.ballRadius x T.κ T.Ct (frameRadius x) V')
    (hR : CentredExpansionBounds false T.a T.chainParams.ρA T.ballRadius T.κ T.decayRate T.E T.energyRatio T.Ct T.L (frameRadius x) f V)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3)
    (η : StepVariable (finiteCells F)) (hη : ∀ b, ‖η b‖ < T.ballRadius) :
    bondDeriv (fun V' => (coldHalfLawAt T x f).exponent V' η) V c X =
      ∑ Y' ∈ finiteCells F, bondDeriv (fun V' => cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y' V' η) V c X -
        ∑ y' ∈ sitesOfCells (finiteCells F) F.depth,
          bondDeriv (fun V' => centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y' η V') V c X := by
  classical
  have hev : (fun τ : Fin k → ℝ => (coldHalfLawAt T x f).exponent (leftTranslate (bondSpread c X τ) V) η) =ᶠ[𝓝 0]
      fun τ => ∑ Y' ∈ finiteCells F, cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y' (leftTranslate (bondSpread c X τ) V) η -
        ∑ y' ∈ sitesOfCells (finiteCells F) F.depth,
          centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y' η (leftTranslate (bondSpread c X τ) V) := by
    filter_upwards [eventually_isSmallCurvature_leftTranslate hfin c X hV] with τ hτ
    exact exponent_eq_sum_sub_sum hEnds T (hXc _ hτ) η hη
  have hline : ∀ {G : (Fin k → ℝ) × StepVariable (finiteCells F) → ℝ}, ContDiffAt ℝ 3 G (0, η) →
      ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (τ, η)) 0 := fun {G} hG => by
    have h1 : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => G (τ, η)) 0 :=
      ContDiffAt.comp (g := G) (f := fun τ : Fin k → ℝ => (τ, η)) 0 hG
        ((contDiff_id.prodMk contDiff_const).contDiffAt)
    exact h1.of_le (by exact_mod_cast hk)
  have sY : ∀ Y' ∈ finiteCells F, ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
      cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y' (leftTranslate (bondSpread c X τ) V) η) 0 := fun Y' _ =>
    hline ((hXc V hV).smooth Y' η k c X fun b => (hη b).le)
  have sy : ∀ y' ∈ sitesOfCells (finiteCells F) F.depth, ContDiffAt ℝ k (fun τ : Fin k → ℝ =>
      centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y' η (leftTranslate (bondSpread c X τ) V)) 0 := fun y' _ =>
    hline (hR.smooth y' η k c X fun b => (hη b).le)
  have e1 := (Filter.EventuallyEq.iteratedFDeriv ℝ hev k).eq_of_nhds
  have hA : ContDiffAt ℝ k (fun τ : Fin k → ℝ => ∑ Y' ∈ finiteCells F,
      cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y' (leftTranslate (bondSpread c X τ) V) η) 0 := ContDiffAt.sum sY
  have hBd : ContDiffAt ℝ k (fun τ : Fin k → ℝ => ∑ y' ∈ sitesOfCells (finiteCells F) F.depth,
      centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y' η (leftTranslate (bondSpread c X τ) V)) 0 := ContDiffAt.sum sy
  show iteratedFDeriv ℝ k (fun τ : Fin k → ℝ => (coldHalfLawAt T x f).exponent (leftTranslate (bondSpread c X τ) V) η) 0
      (fun l => Pi.single l 1) = _
  rw [e1]
  have e2 := iteratedFDeriv_sub_apply (i := k) hA hBd
  have e3 : (fun τ : Fin k → ℝ => ∑ Y' ∈ finiteCells F, cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y'
      (leftTranslate (bondSpread c X τ) V) η - ∑ y' ∈ sitesOfCells (finiteCells F) F.depth,
      centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y' η (leftTranslate (bondSpread c X τ) V)) =
      (fun τ : Fin k → ℝ => ∑ Y' ∈ finiteCells F, cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y'
      (leftTranslate (bondSpread c X τ) V) η) - fun τ => ∑ y' ∈ sitesOfCells (finiteCells F) F.depth,
      centredExpansion false T.a T.chainParams.ρA (frameRadius x) f y' η (leftTranslate (bondSpread c X τ) V) := rfl
  rw [e3, e2]
  simp only [ContinuousMultilinearMap.sub_apply]
  rw [iteratedFDeriv_finsetSum_apply _ k _ 0 sY, iteratedFDeriv_finsetSum_apply _ k _ 0 sy]
  rfl
theorem abs_covariance_bondDeriv_exponent_le (hEnds : interpolationAtEndpoints)
    (hTwo : Calculus.IteratedFDerivParamDiff)
    (hExp2 : ∀ (ι : Type) [Fintype ι] (r : ℝ → ℝ) (Ψ : BondField ι → ℝ) (H : Fin 2 → BondField ι → ℝ),
      cumulantFromMoments r Ψ H = ballCovariance r Ψ (H 0) (H 1))
    (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hρ : 0 < T.ballRadius) (hκ : 0 < T.κ) {Cq Cz : ℕ → ℝ}
    (hCq : ∀ q, 0 ≤ Cq q) (hCz : ∀ q, 0 ≤ Cz q) {T₀ W : ℝ} (hT₀ : 0 ≤ T₀) (hCs : 0 < T.Cs) {t : ℕ} {x h : ℝ}
    {f : LocalFamily} {V : F.GaugeField F.top} {Y : F.Cell} {K : AboveFrames F} (hh : 0 < h) (hx : 0 < x)
    (hst : IsAdmissibleAt T t x f F V) (hrow : IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f)
    (hfin : Finite F.Cell) (hsym : ∀ a b : F.Cell, cellSupDist a b = cellSupDist b a)
    (htri : ∀ a b d : F.Cell, cellSupDist a d ≤ cellSupDist a b + cellSupDist b d)
    (Ψ' : StepVariable (finiteCells F) → ℝ)
    (hd : ballDensity (cutoffFactor T.ballRadius T.p) ((coldHalfLawAt T x f).exponent V) =
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ')
    (hz : ∀ η : BondField ↥(chordBonds (finiteCells F)), ¬ (∀ b, ‖η b‖ < T.ballRadius) →
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ' η = 0)
    (hL : BallLawFacts T.ballRadius T.p Ψ')
    (cb : CumulantBoundsHold T.ballRadius x T.κ T₀ (cutoffFactor T.ballRadius T.p) Ψ'
      (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1))
    (hXc : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
      CellExponentBounds false T.a T.chainParams.ρA T.ballRadius x T.κ T.Ct (frameRadius x) V')
    (hX4 : ∀ (Y' : F.Cell) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      ContDiffAt ℝ 4 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
        cellExponent false T.a T.chainParams.ρA x (frameRadius x) Y' (leftTranslate (bondSpread c X q.1) V) q.2) (0, η))
    (hR : CentredExpansionBounds false T.a T.chainParams.ρA T.ballRadius T.κ T.decayRate T.E T.energyRatio T.Ct T.L (frameRadius x) f V)
    (hsz : ∀ (Y' : F.Cell) (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions), AreUnitVectors X →
      HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) ((coldHalfLawAt T x f).exponent V) Cz x T.κ
        (T.Cs * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y' c))) (fun b => (cellSupDist (enclosingCell b.1.1) Y' : ℝ))
        (fun ζ => bondDeriv (fun V' => interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) Y' V' ζ) V c X))
    (hTW : thirdOrderCovarianceBoundAt T Cq) (Th : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions)
    (hTh : ∀ w X' : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X' (Th w X'))
    (hWY : ∑ Y' ∈ finiteCells F, Real.exp (-(T.κ / 16 * cellSupDist Y Y')) ≤ W)
    (hsl : IsSlot (coldHalfLawAt T x f) Cq h Y K V) (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions)
    (hX : AreUnitVectors X) :
    |(coldHalfLawAt T x f).covariance V (fun η => K η V)
        (fun η => bondDeriv (fun V' => (coldHalfLawAt T x f).exponent V' η) V c X)| ≤
      (T₀ * (sizeConstantSum Cq 2 * sizeConstantSum Cz 2 * T.Cs) * W +
        T.Cs * (1 + ∑ q ∈ Finset.range 7, Cq q) * T.energyRatio * 2) * h *
          Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c)) := by
  classical
  set Q := coldHalfLawAt T x f with hQ
  set r := cutoffFactor T.ballRadius T.p with hr
  set y : ↥(chordBonds (finiteCells F)) → F.Cell := fun b => enclosingCell b.1.1 with hy
  set m := frameRadius x with hm
  set E : ℝ := Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c)) with hE
  have hO : IsOpen {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} := by
    have : {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ < T.ballRadius} =
        ⋂ b, {η : StepVariable (finiteCells F) | ‖η b‖ < T.ballRadius} := by
      ext η; simp
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
  have hbe : ∀ (V' : F.GaugeField F.top) (Y' : F.Cell) (η : StepVariable (finiteCells F)),
      interpolatedBlockExponent 1 T.a T.chainParams.ρA x m Y' V' η = cellExponent false T.a T.chainParams.ρA x m Y' V' η :=
    fun V' Y' η => by
      have := (hEnds F false T.a T.chainParams.ρA T.chainParams.lam x 0 m V').2.2.2.2.1 Y' η
      simpa [segmentEnd] using this
  have hrb : ∀ (V' : F.GaugeField F.top) (y' : F.Site F.depth) (η : StepVariable (finiteCells F)),
      interpolatedExpansion 1 T.a T.chainParams.ρA m f y' η V' = centredExpansion false T.a T.chainParams.ρA m f y' η V' := fun V' y' η => by
    have := (hEnds F false T.a T.chainParams.ρA T.chainParams.lam x 0 m V').2.2.2.1 f y' η
    simpa [segmentEnd] using this
  have e1 : ∀ g : StepVariable (finiteCells F) → ℝ, ballExpectation r (Q.exponent V) g = ballExpectation r Ψ' g :=
    fun g => by
      unfold ballExpectation
      rw [hd]
  have ec : ∀ a g : StepVariable (finiteCells F) → ℝ, ballCovariance r (Q.exponent V) a g = ballCovariance r Ψ' a g :=
    fun a g => by
      unfold ballCovariance
      rw [e1, e1, e1]
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
  let Kv : StepVariable (finiteCells F) → ℝ := fun η => K η V
  let Dy : F.Cell → StepVariable (finiteCells F) → ℝ := fun Y' ζ =>
    bondDeriv (fun V' => cellExponent false T.a T.chainParams.ρA x m Y' V' ζ) V c X
  let Dr : F.Site F.depth → StepVariable (finiteCells F) → ℝ := fun y' ζ =>
    bondDeriv (interpolatedExpansion 1 T.a T.chainParams.ρA m f y' ζ) V c X
  have hsl0 := hsl.smoothBounded.smooth
  have hKt : IsBoundedContinuousOnBall T.ballRadius Kv := isBoundedContinuousOnBall_of_continuousAt fun η hη => by
    have hs := (hsl0 η 0 (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions) hη)
    have h1 := continuousAt_iteratedFDeriv_partial (P := Fin 0 → ℝ) 0
      (fun q : (Fin 0 → ℝ) × StepVariable (finiteCells F) =>
        K q.2 (leftTranslate (bondSpread (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
          (Fin.elim0 : Fin 0 → imaginaryQuaternions) q.1) V)) η
      (fun l => l.elim0) (hs.of_le (by norm_num))
    refine h1.congr (Filter.Eventually.of_forall fun ζ => ?_)
    simp only [iteratedFDeriv_zero_apply, leftTranslate_bondSpread_zero, Kv]
  have hYt : ∀ Y', IsBoundedContinuousOnBall T.ballRadius (Dy Y') := fun Y' =>
    isBoundedContinuousOnBall_of_continuousAt fun η hη => by
      have h1 := continuousAt_iteratedFDeriv_partial (P := Fin 3 → ℝ) 3
        (fun q : (Fin 3 → ℝ) × StepVariable (finiteCells F) =>
          cellExponent false T.a T.chainParams.ρA x m Y' (leftTranslate (bondSpread c X q.1) V) q.2) η (fun l => Pi.single l 1)
        ((hXc V hst.small_curvature).smooth Y' η 3 c X hη)
      exact h1
  have hDr : ∀ (y' : F.Site F.depth) (ζ : StepVariable (finiteCells F)), Dr y' ζ =
      bondDeriv (fun V' => centredExpansion false T.a T.chainParams.ρA m f y' ζ V') V c X := fun y' ζ => by
    have : interpolatedExpansion 1 T.a T.chainParams.ρA m f y' ζ = fun V' => centredExpansion false T.a T.chainParams.ρA m f y' ζ V' := by
      funext V'
      exact hrb V' y' ζ
    simp only [Dr, this]
  have hRt : ∀ y', IsBoundedContinuousOnBall T.ballRadius (Dr y') := fun y' =>
    isBoundedContinuousOnBall_of_continuousAt fun η hη => by
      have h1 := continuousAt_iteratedFDeriv_partial (P := Fin 3 → ℝ) 3
        (fun q : (Fin 3 → ℝ) × StepVariable (finiteCells F) =>
          centredExpansion false T.a T.chainParams.ρA m f y' q.2 (leftTranslate (bondSpread c X q.1) V)) η (fun l => Pi.single l 1)
        (hR.smooth y' η 3 c X hη)
      refine h1.congr (Filter.Eventually.of_forall fun ζ => ?_)
      exact (hDr y' ζ).symm
  have hnegt : ∀ y', IsBoundedContinuousOnBall T.ballRadius (fun ζ => - Dr y' ζ) := fun y' => by
    obtain ⟨M, hM⟩ := (hRt y').bound
    exact ⟨(hRt y').cont.neg, M, fun η hη => by rw [abs_neg]; exact hM η hη⟩
  let g : F.Cell ⊕ F.Site F.depth → StepVariable (finiteCells F) → ℝ := Sum.elim Dy fun y' ζ => - Dr y' ζ
  let S : Finset (F.Cell ⊕ F.Site F.depth) := (finiteCells F).disjSum (sitesOfCells (finiteCells F) F.depth)
  have hgt : ∀ j, IsBoundedContinuousOnBall T.ballRadius (g j) := fun j => by
    rcases j with Y' | y'
    · exact hYt Y'
    · exact hnegt y'
  have eqBall : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
      bondDeriv (fun V' => Q.exponent V' η) V c X = ∑ j ∈ S, g j η := by
    intro η hη
    rw [Finset.sum_disjSum]
    simp only [g, Sum.elim_inl, Sum.elim_inr, Finset.sum_neg_distrib]
    rw [bondDeriv_exponent_eq hEnds T hst.small_curvature hfin hXc hR c X (by norm_num) η hη]
    simp only [Dy, hDr, sub_eq_add_neg]
    rfl
  have hsplit : Q.covariance V Kv (fun η => bondDeriv (fun V' => Q.exponent V' η) V c X) =
      ∑ j ∈ S, ballCovariance r Ψ' Kv (g j) := by
    have h1 : Q.covariance V Kv (fun η => bondDeriv (fun V' => Q.exponent V' η) V c X) =
        ballCovariance r Ψ' Kv (fun η => bondDeriv (fun V' => Q.exponent V' η) V c X) := ec _ _
    rw [h1, ← ballCovariance_finsetSum hL hO S hKt hgt]
    unfold ballCovariance
    rw [mean_ball (fun η => Kv η * bondDeriv (fun V' => Q.exponent V' η) V c X)
        (fun η => Kv η * ∑ j ∈ S, g j η) (fun η hη => by
          show Kv η * bondDeriv (fun V' => Q.exponent V' η) V c X = _
          rw [eqBall η hη]),
      mean_ball (fun η => bondDeriv (fun V' => Q.exponent V' η) V c X) (fun η => ∑ j ∈ S, g j η) eqBall]
  have hneg : ∀ y', ballCovariance r Ψ' Kv (fun ζ => - Dr y' ζ) = - ballCovariance r Ψ' Kv (Dr y') := fun y' => by
    unfold ballCovariance
    have a1 : ballExpectation r Ψ' (fun η => Kv η * - Dr y' η) = - ballExpectation r Ψ' (fun η => Kv η * Dr y' η) := by
      rw [← hL.mean, ← hL.mean, ← integral_neg]
      congr 1
      funext η
      ring
    have a2 : ballExpectation r Ψ' (fun ζ => - Dr y' ζ) = - ballExpectation r Ψ' (Dr y') := by
      rw [← hL.mean, ← hL.mean, ← integral_neg]
    rw [a1, a2]
    ring
  have hsize0 : HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) (familyLawExponent 1 T.a T.chainParams.ρA x m f V)
      Cq x T.κ h (bondDistToCell Y) Kv := by
    have h1 := hsl.smoothBounded.deriv_bound 0 (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
      (Fin.elim0 : Fin 0 → imaginaryQuaternions) (by norm_num) (fun l => l.elim0)
    have e1' : (fun η : StepVariable (finiteCells F) => bondDeriv (K η) V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions)) = Kv := by
      funext η
      simp only [bondDeriv, iteratedFDeriv_zero_apply, leftTranslate_bondSpread_zero, Kv]
    have e2 : bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) = 0 := by
      simp [bondSpan]
    rw [e1', e2] at h1
    exact show Q.HasSize Cq V h Y Kv from by simpa using h1
  have hcl : ThirdOrderHypotheses Th 1 T.a T.chainParams.ρA T.ballRadius x T.κ h (Real.sqrt x * h) m T.p Cq V Y c X
      (familyLawExponent 1 T.a T.chainParams.ρA x m f V) Kv :=
    ⟨hsl.contDiffAt_two, hsize0, fun b l => hsl.decaysAlongTopField Th hTh (c l) (X l) b (hX l)⟩
  have hrow' := hTW t x 1 h (Real.sqrt x * h) f f F V Y c X Th Kv hst.coupling_le zero_le_one le_rfl hh
    (by positivity) hst.family_bounded hst.family_bounded hst.torus hst.small_curvature hX hTh hcl
  have hxs : x ^ (-(1 / 2 : ℝ)) * (Real.sqrt x * h) = h := by
    rw [Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add hx]
    norm_num
  rw [hxs] at hrow'
  set Cy : ℝ := T₀ * (sizeConstantSum Cq 2 * sizeConstantSum Cz 2 * T.Cs) with hCy
  have hS2 : ∀ C : ℕ → ℝ, (∀ q, 0 ≤ C q) → 0 ≤ sizeConstantSum C 2 := fun C hC => by
    unfold sizeConstantSum
    have : 0 ≤ ∑ q ∈ Finset.range (2 * 2 + 1), C q := Finset.sum_nonneg fun q _ => hC q
    linarith
  have hblock : ∀ Y' : F.Cell, |ballCovariance r Ψ' Kv (Dy Y')| ≤
      Cy * h * E * Real.exp (-(T.κ / 16 * cellSupDist Y Y')) := fun Y' => by
    have o₀ : PlacedObservable T.ballRadius x T.κ r Ψ' y Cq h Y Kv := by
      refine ⟨fun η hη => ?_, ?_, hh.le, hCq⟩
      · have hO' := hO.mem_nhds hη
        exact ((hsl.contDiffAt_two η hη).of_le (by norm_num)).contDiffWithinAt
      · exact hasLocalSize_congr_density hd hsize0
    have o₁ : PlacedObservable T.ballRadius x T.κ r Ψ' y Cz (T.Cs * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y' c))) Y'
        (Dy Y') := by
      refine ⟨fun η hη => ?_, ?_, by positivity, hCz⟩
      · have h1 := (hTwo (Fin 3 → ℝ) (StepVariable (finiteCells F)) 3 (fun q => cellExponent false T.a T.chainParams.ρA x m Y'
          (leftTranslate (bondSpread c X q.1) V) q.2) η (fun l => Pi.single l 1)
          (hX4 Y' 3 c X η fun b => (hη b).le)).1
        exact h1.contDiffWithinAt
      · have h1 := hsz Y' c X hX
        simp only [hbe] at h1
        exact hasLocalSize_congr_density hd h1
    have hc := abs_ballCovariance_le cb (hExp2 _ r Ψ') o₀ o₁
    refine hc.trans ?_
    set s : ℝ := (bondSpan Y' c : ℝ)
    set dd : ℝ := (cellSupDist Y Y' : ℝ)
    set D : ℝ := (cellsDiameter ![Y, Y'] : ℝ)
    have hn : (bondSpan Y c : ℝ) ≤ 2 * (dd + s) := by
      have := bondSpan_le_two_mul hsym htri Y Y' c
      have h2 : (bondSpan Y c : ℝ) ≤ ((2 * (cellSupDist Y Y' + bondSpan Y' c) : ℕ) : ℝ) := Nat.cast_le.2 this
      push_cast at h2
      exact h2
    have hdD : dd ≤ D := Nat.cast_le.2 (cellSupDist_le_cellsDiameter Y Y')
    have hp := exp_mul_exp_le hκ.le hn (Nat.cast_nonneg _) (Nat.cast_nonneg _) hdD
    have c1 := hS2 Cq hCq
    have c2 := hS2 Cz hCz
    calc T₀ * ((sizeConstantSum Cq 2 * h) * (sizeConstantSum Cz 2 * (T.Cs * Real.exp (-(2 ^ 5 * T.κ * s))))) *
          Real.exp (-(T.κ / 8 * D))
        = Cy * h * (Real.exp (-(2 ^ 5 * T.κ * s)) * Real.exp (-(T.κ / 8 * D))) := by
          rw [hCy]; ring
      _ ≤ Cy * h * (Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c)) * Real.exp (-(T.κ / 16 * dd))) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  have hCy0 : 0 ≤ Cy := by
    have c1 := hS2 Cq hCq
    have c2 := hS2 Cz hCz
    positivity
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  show |Q.covariance V Kv _| ≤ _
  rw [hsplit, Finset.sum_disjSum]
  simp only [g, Sum.elim_inl, Sum.elim_inr, hneg, Finset.sum_neg_distrib]
  have b1 : |∑ Y' ∈ finiteCells F, ballCovariance r Ψ' Kv (Dy Y')| ≤ Cy * h * E * W := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun Y' _ => hblock Y').trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hWY (by positivity)
  have b2 : |∑ y' ∈ sitesOfCells (finiteCells F) F.depth, ballCovariance r Ψ' Kv (Dr y')| ≤
      T.Cs * (1 + ∑ q ∈ Finset.range 7, Cq q) * T.energyRatio * (h + h) * E := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (le_of_eq ?_) hrow'
    refine Finset.sum_congr rfl fun y' _ => ?_
    rw [← ec]
    rfl
  have e9 := abs_add_le (∑ Y' ∈ finiteCells F, ballCovariance r Ψ' Kv (Dy Y'))
    (-∑ y' ∈ sitesOfCells (finiteCells F) F.depth, ballCovariance r Ψ' Kv (Dr y'))
  rw [abs_neg] at e9
  refine e9.trans ((add_le_add b1 b2).trans (le_of_eq ?_))
  ring
theorem sum_sites_le_sum_fineBonds (r : ℝ) (Z : F.Cell) :
    ∑ y ∈ sitesOfCells (finiteCells F) F.depth, Real.exp (-(r * cellSupDist (enclosingCell y) Z)) ≤
      ∑ b ∈ fineBonds F, Real.exp (-(r * cellSupDist (enclosingCell b.1) Z)) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.ExponentLocality.sum_sites_le_sum_fineBonds <;> assumption
theorem sum_cells_le_sum_sites (hL : Odd F.blockSide) (r : ℝ) (Z : F.Cell) :
    ∑ Y ∈ finiteCells F, Real.exp (-(r * cellSupDist Y Z)) ≤
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, Real.exp (-(r * cellSupDist (enclosingCell y) Z)) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.ExponentLocality.sum_cells_le_sum_sites <;> assumption
end ThirdOrderSlot
open ThirdOrderSlot in
theorem slotThirdOrderCovariance_holds (hEnds : interpolationAtEndpoints)
    (hTwo : Calculus.IteratedFDerivParamDiff) (hExp : lowOrderCumulantFormulas)
    (hCum : cumulantDecayBound) (hFew : Estimates.cellBondsCardStatement)
    (hLaw : normalizedBallLawIsProbabilityStatement)
    (hFB : interpolatedFramesStatement) (hB : CellExponentsBounded)
    (hRw : CentredExpansionsBounded) (hG : CubicTorusCellGeometry)
    (hTW : thirdOrderCovarianceBound) (hRS : rightTranslationDerivExistsStatement)
    (hJ : EventuallyInParametersCombines) : slotThirdOrderCovarianceStatement := by
  classical
  intro Cq hCq
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cm, Cz, Cr, hP⟩ := hFB
  obtain ⟨hg1, hg2⟩ := hG
  choose! Wc hWc0 hWc using hg2
  choose! T₀ hT₀ hT₀' using hCum
  obtain ⟨Th, hTh⟩ := hRS
  have h64 : EventuallyInParameters fun T => 1 ≤ T.Cs ∧ 64 ≤ T.n₀ ∧ 1 ≤ T.coupling := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨1, fun _ hCs _ _ => ⟨64, fun _ h => ⟨0, fun _ _ => ⟨1, fun _ hy => ⟨hCs, h, hy⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine ⟨fun U => |T₀ (4 * U.L ^ 4) U.κ U.chainParams.lam * (sizeConstantSum (Cq (sizeParameters U)) 2 *
      sizeConstantSum (fun q => |Cz (momentParameters U) q|) 2 * U.Cs) * (Wc (U.κ / 16) * (U.L : ℝ) ^ 4) +
      U.Cs * (1 + ∑ q ∈ Finset.range 7, Cq (sizeParameters U) q) * U.energyRatio * 2|, fun T => abs_nonneg _, ?_⟩
  refine weaken _ _ ?_ (join _ _ hP (join _ _ h64 (join _ _ hTW (join _ _ hB hRw))))
  rintro T hDr ⟨hPT, ⟨hc1, h64', hy1⟩, hTWT, hXb, hRb⟩
  intro t x h f F V Y K c X hst hrow hh hsl hX
  have hfl : T.coupling ≤ x := hst.coupling_le
  have hx1 : 1 ≤ x := hy1.trans hfl
  have hx : 0 < x := by linarith
  have hPT' := hPT t x hfl
  set Q := coldHalfLawAt T x f with hQ
  let M : LawOnBondVariables ↥(chordBonds (finiteCells F)) := lawAtTop V (Q.exponent V)
  have hadm : M.IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio T.L t T.n₀ (frameRadius x)
      (chordBondDist F) :=
    ⟨hst.torus, hst.small_curvature, IsIntermediateLaw.ofFamily 1 f zero_le_one le_rfl hst.family_bounded,
      Function.injective_id, fun _ _ => rfl⟩
  obtain ⟨hconv, -, hsizes⟩ := hPT'.laws _ (chordBondDist F) 1 (fun _ => 1) (fun _ => M)
    ⟨fun _ => zero_le_one, by simp⟩ (fun _ => hadm)
  have hszM := hsizes M hadm
  rw [convexCombinationExponent_lawAtTop] at hconv hszM
  obtain ⟨Ψ', K', hΨ', hconvex, hslope, -⟩ := hconv
  have hΨc : Continuous Ψ' := hconvex.smooth.continuous
  have hρ : 0 < T.ballRadius := by
    have := hDr.σ_pos
    show 0 < T.σ / 64
    positivity
  have hκ : 0 < T.κ := hDr.κ_pos
  have hlam : 0 < T.chainParams.lam := hDr.chain_admissible.positivity.2.2.1
  obtain ⟨hpr, hme, -, hob, -, -, -, -, -, hnz, -⟩ := hLaw _ T.ballRadius T.p Ψ' hρ hDr.cutoff hΨc
  have hLF' : BallLawFacts T.ballRadius T.p Ψ' := ⟨hpr, hme, hob⟩
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
        rcases mul_eq_zero.1 h0 with h' | h'
        · exact h'
        · exact absurd h' (Real.exp_pos _).ne'
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
  have hN : ∀ z : F.Cell, (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤
      4 * T.L ^ 4 := fun z => by
    have := hFew F hoddF (fun i => by rw [hside]; omega) z
    rwa [hLF] at this
  have cb : CumulantBoundsHold T.ballRadius x T.κ (T₀ (4 * T.L ^ 4) T.κ T.chainParams.lam) (cutoffFactor T.ballRadius T.p) Ψ'
      (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1) :=
    fun M' H Z hh' C h2 h9 hc h0 hq hs =>
      (hT₀' (4 * T.L ^ 4) T.κ T.chainParams.lam hκ hlam F _ (fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1)
        T.ballRadius x T.p Ψ' K' hρ hx hDr.cutoff hN hconvex hslope M' H Z hh' C h2 h9 hc h0 hq hs).2
  have hr16 : 0 < T.κ / 16 := by positivity
  have hWb := hWc (T.κ / 16) hr16 F hoddF hcub Y
  rw [hLF] at hWb
  have hWY : ∑ Y' ∈ finiteCells F, Real.exp (-(T.κ / 16 * cellSupDist Y Y')) ≤ Wc (T.κ / 16) * (T.L : ℝ) ^ 4 := by
    have h1 := (sum_cells_le_sum_sites hoddF (T.κ / 16) Y).trans
      ((sum_sites_le_sum_fineBonds (F := F) (T.κ / 16) Y).trans hWb)
    refine le_trans (le_of_eq ?_) h1
    refine Finset.sum_congr rfl fun Y' _ => ?_
    rw [hsym Y Y']
  have hsz' : ∀ (Y' : F.Cell) (c' : Fin 3 → F.Site F.top × Fin 4) (X' : Fin 3 → imaginaryQuaternions), AreUnitVectors X' →
      HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) (Q.exponent V) (fun q => |Cz (momentParameters T) q|) x T.κ
        (T.Cs * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y' c'))) (fun b => (cellSupDist (enclosingCell b.1.1) Y' : ℝ))
        (fun ζ => bondDeriv (fun V' => interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) Y' V' ζ) V c' X') := by
    intro Y' c' X' hX'
    have h1 : HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) (Q.exponent V) (Cz (momentParameters T)) x T.κ
        (T.Cs * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y' c')))
        (embeddedCellDist id Y') (fun ζ => bondDeriv (fun V' =>
          interpolatedBlockExponent 1 T.a T.chainParams.ρA x (frameRadius x) Y' V' (_root_.YangMills.Construction.Interpolation.extendByZero id Finset.univ ζ)) V c' X') :=
      hszM.exponent_deriv 1 Y' 3 c' X' zero_le_one le_rfl le_rfl hX'
    simp only [extendByZero_id] at h1
    exact hasLocalSize_mono (fun q => le_rfl) (by positivity) le_rfl h1
  have hres := abs_covariance_bondDeriv_exponent_le hEnds hTwo (fun ι _ r Ψ H => (hExp ι r Ψ).1 H) T hρ hκ
    (Cq := Cq (sizeParameters T)) (Cz := fun q => |Cz (momentParameters T) q|) (fun q => hCq _ q)
    (fun q => abs_nonneg _) (hT₀ _ _ _ hκ hlam)
    (by linarith) hh hx hst hrow hfin hsym htri Ψ' hd hz hLF' cb
    (fun V' hV' => (hXb t x F V' false hfl ⟨hLF, htt, n, hside, hn⟩ hV').1)
    ((hXb t x F V false hfl ⟨hLF, htt, n, hside, hn⟩ hst.small_curvature).2)
    (hRb t x f F V false hfl hrow ⟨hLF, htt, n, hside, hn⟩ hst.small_curvature) hsz'
    (hTWT _ fun q => hCq _ q) Th hTh hWY hsl c X hX
  refine hres.trans ?_
  have hE := (Real.exp_pos (-(T.κ / 2 ^ 5 * (bondSpan Y c : ℝ)))).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hh.le) hE
end ResponseInTheExpansion
end YangMills.Construction
end
