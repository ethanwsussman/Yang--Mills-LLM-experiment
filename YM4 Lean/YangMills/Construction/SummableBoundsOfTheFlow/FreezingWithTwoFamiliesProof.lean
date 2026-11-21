import YangMills.Construction.ColdStepAtMirrorFrames.FreezingOfTheStepProof
import YangMills.Construction.ColdStepAtMirrorFrames.FrozenMeasureSplits
import YangMills.Construction.SummableBoundsOfTheFlow.ComparisonOfAFunction
import YangMills.Construction.SummableBoundsOfTheFlow.FreezingWithTwoFamilies
import YangMills.Construction.SummableBoundsOfTheFlow.MatchedPartsOfTwoLawsCompare
import YangMills.Construction.SummableBoundsOfTheFlow.WeightPartIsAdmittedProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusComparison TorusFreezing Freezing Interpolation Estimates
  ConvexObservables CellCounting SummableBounds
namespace TorusFreezing
namespace Decoupling
open YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus
section BallLaws
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {p : ℝ → ℝ}
theorem radialWeightProd_eq_zero_of_not_mem {η : BondField ι} (hη : η ∉ openPolyball ι ρ) :
    radialWeightProd (cutoffFactor ρ p) η = 0 := by apply _root_.YangMills.SharedProofs.p17620 <;> assumption
theorem ballDensity_congr {V₁ V₂ : BondField ι → ℝ} (h : ∀ η ∈ openPolyball ι ρ, V₁ η = V₂ η) :
    ballDensity (cutoffFactor ρ p) V₁ = ballDensity (cutoffFactor ρ p) V₂ := by apply _root_.YangMills.SharedProofs.p18172 <;> assumption
theorem ballExpectation_congr_density {V₁ V₂ : BondField ι → ℝ}
    (h : ballDensity (cutoffFactor ρ p) V₁ = ballDensity (cutoffFactor ρ p) V₂) (f : BondField ι → ℝ) :
    ballExpectation (cutoffFactor ρ p) V₁ f = ballExpectation (cutoffFactor ρ p) V₂ f := by apply _root_.YangMills.SharedProofs.p53358 <;> assumption
theorem ballExpectation_sub_eq_neg (V : BondField ι → ℝ) (f g : BondField ι → ℝ) :
    ballExpectation (cutoffFactor ρ p) V (fun η => f η - g η) =
      - ballExpectation (cutoffFactor ρ p) V (fun η => g η - f η) := by
  unfold ballExpectation
  rw [← neg_div, ← integral_neg]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  simp only
  ring
theorem hasFrozenGradientBound_of_hasGradientBound {P : Type} {pos : ι → P} {D : P → P → ℝ} {Y : P}
    {x κ h : ℝ} {T V H : BondField ι → ℝ} {dZ : ι → ℝ}
    (hd : ballDensity (cutoffFactor ρ p) T = ballDensity (cutoffFactor ρ p) V)
    (hs : ContDiffOn ℝ 1 H (openPolyball ι ρ)) (hg : HasGradientBound ρ (cutoffFactor ρ p) V x κ h dZ H)
    (hZ : ∀ b, dZ b = D (pos b) Y) (hh : 0 ≤ h) :
    HasFrozenGradientBound ρ κ (Real.sqrt x * h) p pos D Y T H := by
  obtain ⟨-, hm, hn⟩ := hg
  refine ⟨hs, ?_, fun b => ?_, fun b => ?_⟩
  · rw [hd]
    simpa only [sq_abs] using (hm 2 (by norm_num)).1
  · rw [hd]
    simpa only [sq_abs] using (hm 2 (by norm_num)).2 b
  · have h2 := (hn b).2
    simp only [sq_abs] at h2
    unfold ballL2Norm
    rw [ballExpectation_congr_density hd]
    have hB : 0 ≤ Real.sqrt x * h * Real.exp (-(2 * κ * dZ b)) := by positivity
    refine (Real.sqrt_le_sqrt h2).trans ?_
    rw [Real.sqrt_sq hB, hZ b]
theorem contDiffOn_comp_restrictToBonds (hρ : 0 < ρ) (Λ : Finset ι) {A : BondField ι → ℝ}
    (hA : ContDiffOn ℝ 1 A (openPolyball ι ρ)) :
    ContDiffOn ℝ 1 (fun η => A (restrictToBonds Λ η)) (openPolyball ι ρ) := by
  have e : (fun η => A (restrictToBonds Λ η)) = fun ζ => A (restrictToBondsCLM Λ ζ) := by
    funext ζ
    simp [restrictToBondsCLM_apply]
  rw [e]
  exact hA.comp (restrictToBondsCLM Λ).contDiff.contDiffOn (fun η hη => by
    rw [restrictToBondsCLM_apply]
    exact restrictToBonds_mem_openPolyball hρ Λ hη)
theorem integrable_mul_radialWeightProd {W H : BondField ι → ℝ} (hW : Continuous W) {M : ℝ}
    (hM : ∀ η ∈ openPolyball ι ρ, |W η| ≤ M)
    (hi : Integrable fun η => H η * ballDensity (cutoffFactor ρ p) W η) :
    Integrable fun η => H η * radialWeightProd (cutoffFactor ρ p) η := by
  set g : BondField ι → ℝ := fun η => Real.exp (max (-M) (min M (W η))) with hg
  have hgc : Continuous g := by
    simp only [hg]
    exact Real.continuous_exp.comp (continuous_const.max (continuous_const.min hW))
  have hb : ∀ η, ‖g η‖ ≤ Real.exp |M| := by
    intro η
    simp only [hg, Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    refine max_le ?_ ((min_le_left _ _).trans (le_abs_self M))
    have := neg_abs_le M
    linarith
  have h1 : Integrable fun η => (H η * ballDensity (cutoffFactor ρ p) W η) * g η :=
    hi.mul_bdd (c := Real.exp |M|) hgc.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine h1.congr (Filter.Eventually.of_forall fun η => ?_)
  by_cases hη : η ∈ openPolyball ι ρ
  · have h3 := abs_le.1 (hM η hη)
    have e1 : max (-M) (min M (W η)) = W η := by
      rw [min_eq_right h3.2, max_eq_right h3.1]
    simp only [hg, e1, ballDensity]
    rw [mul_assoc, mul_assoc, ← Real.exp_add]
    simp
  · simp [ballDensity, radialWeightProd_eq_zero_of_not_mem hη]
theorem integrable_mul_ballDensity_of_sq (hlaw : normalizedBallLawIsProbabilityStatement) (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) {W H : BondField ι → ℝ} (hW : Continuous W) (hc : ContinuousOn H (openPolyball ι ρ))
    (h2 : Integrable fun η => H η ^ 2 * ballDensity (cutoffFactor ρ p) W η) :
    Integrable fun η => H η * ballDensity (cutoffFactor ρ p) W η := by
  obtain ⟨l1, -, l3, l4, -⟩ := hlaw ι ρ p W hρ hp hW
  refine (l3 _).1 ?_
  have hsq := (l3 _).2 h2
  have hm : AEStronglyMeasurable H (normalizedBallLaw (cutoffFactor ρ p) W) := by
    have h := Measure.restrict_eq_self_of_ae_mem (μ := normalizedBallLaw (cutoffFactor ρ p) W)
      (s := openPolyball ι ρ) l4
    rw [← h]
    exact hc.aestronglyMeasurable (isOpen_openPolyball hρ).measurableSet
  exact ((memLp_two_iff_integrable_sq hm).2 hsq).integrable (by norm_num)
end BallLaws
section CellDistances
variable {F : BlockFrame}
theorem freezeOutside_eq_restrictToBonds (Λ : Finset ↥(chordBonds (finiteCells F)))
    (η : StepVariable (finiteCells F)) : freezeOutside Λ η = restrictToBonds Λ η := by
  funext b
  simp only [freezeOutside, _root_.YangMills.Construction.Interpolation.extendByZero, restrictToBonds, id]
  rw [Finset.sum_ite_eq' Λ b]
theorem segmentInterpolant_eq_freezingHomotopy {Φ Ψ : StepVariable (finiteCells F) → ℝ} {ρ lam x v : ℝ}
    (hρ : 0 < ρ) (Λ : Finset ↥(chordBonds (finiteCells F))) (h : ∀ η ∈ openPolyball _ ρ, Ψ η = Φ η) :
    ∀ η ∈ openPolyball _ ρ, segmentInterpolant (frozenPotential Λ (x * lam) Ψ) Ψ v η =
      freezingHomotopy lam x Λ Φ v η := by
  intro η hη
  have e1 := h η hη
  have e2 := h _ (restrictToBonds_mem_openPolyball hρ Λ hη)
  simp only [segmentInterpolant, frozenPotential, freezingHomotopy, frozenExponent, halfSqNormOn]
  have e3 : _root_.YangMills.Construction.Interpolation.extendByZero id Λ η = restrictToBonds Λ η := freezeOutside_eq_restrictToBonds Λ η
  rw [e3, e1, e2, Finset.compl_eq_univ_sdiff]
theorem isPseudoMetricOnBonds_realCellDist : IsPseudoMetricOnBonds (realCellDist (F := F)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepFreezing.isPseudoMetricOnBonds_cellDistance <;> assumption
end CellDistances
theorem abs_expectation_sub_frozen_le (hF1 : frozenExpectationDifferenceBound) {F : BlockFrame}
    [Fintype F.Cell] {ρ κ S lam x c α : ℝ} {p : ℝ → ℝ} {Φ Ψ A : StepVariable (finiteCells F) → ℝ}
    {θ : F.Cell → StepVariable (finiteCells F) → ℝ} {Y : F.Cell} {q : ℕ}
    (hρ : 0 < ρ) (hκ : 0 < κ) (hlam : 0 < lam) (hx : 1 ≤ x) (hc : 1 ≤ c) (hα : 0 ≤ α) (hp : IsCutoff ρ p)
    (hag : ∀ η ∈ openPolyball _ ρ, Ψ η = Φ η)
    (hgood : IsAdmissiblePotential ρ (x * lam / 4) κ (fun b b' => realCellDist (bondCell b) (bondCell b')) Ψ)
    (hS : ∀ z : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(κ / 4 * realCellDist (bondCell b) z)) ≤ S)
    (hSp : ∀ z : F.Cell, ∑ z' : F.Cell, Real.exp (-(κ / 4 * realCellDist z' z)) ≤ S)
    (hθ : ∀ z, IsLocalTermAt ρ κ c x bondCell realCellDist z (θ z)) (hsum : ∀ η ∈ openPolyball _ ρ, Ψ η = ∑ z, θ z η)
    (hA : ContDiffOn ℝ 1 A (openPolyball _ ρ))
    (hadm : ComparisonHypothesesOnTorus ρ lam x κ α p q Y Φ A) :
    |ballExpectation (cutoffFactor ρ p) Φ A -
      ballExpectation (cutoffFactor ρ p) (frozenPotential (bondsNearCell Y q) (x * lam) Ψ)
        (fun η => A (restrictToBonds (bondsNearCell Y q) η))| ≤
      α * Real.exp (-(4 * κ * q)) +
        α * c * freezeGradientConstant lam S * Real.exp (-(κ * q / 16)) := by
  have hx0 : 0 < x := by linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hΛ : ∀ b, b ∈ bondsNearCell Y q ↔ realCellDist (bondCell b) Y ≤ (q : ℝ) / 2 := by
    intro b
    simp only [_root_.YangMills.Construction.TorusComparison.bondsNearCell, Finset.mem_filter, Finset.mem_univ, true_and, realCellDist, bondCell]
    constructor
    · intro h
      have : ((2 * cellSupDist (enclosingCell b.1.1) Y : ℕ) : ℝ) ≤ q := by exact_mod_cast h
      push_cast at this
      linarith
    · intro h
      have : ((2 * cellSupDist (enclosingCell b.1.1) Y : ℕ) : ℝ) ≤ q := by
        push_cast
        linarith
      exact_mod_cast this
  have hfz : (fun η => A (freezeOutside (bondsNearCell Y q) η)) =
      fun η => A (restrictToBonds (bondsNearCell Y q) η) := by
    funext η
    rw [freezeOutside_eq_restrictToBonds]
  have hi1 := hadm.integrable_mul
  have hi2 := hadm.integrable_freeze_mul
  simp only [freezeOutside_eq_restrictToBonds] at hi2
  have key := hF1 (↥(chordBonds (finiteCells F))) F.Cell ρ κ S lam x c (q : ℝ) (Real.sqrt x * α)
    (α * Real.exp (-(4 * κ * q))) p bondCell realCellDist Ψ A θ Y (bondsNearCell Y q) hρ hκ hlam hx hc hq0
    (by positivity) hp isPseudoMetricOnBonds_realCellDist hgood hS hSp hθ hsum hΛ hi1 hi2 (fun v hv0 hv1 => by
      have hd := ballDensity_congr (p := p)
        (segmentInterpolant_eq_freezingHomotopy (v := v) (lam := lam) (x := x) hρ (bondsNearCell Y q) hag)
      refine ⟨hasFrozenGradientBound_of_hasGradientBound hd hA (hadm.hasGradientBound v hv0 hv1)
        (fun b => rfl) hα, ?_, ?_⟩
      · have h3 := hadm.hasGradientBound_freeze v hv0 hv1
        rw [hfz] at h3
        exact hasFrozenGradientBound_of_hasGradientBound hd (contDiffOn_comp_restrictToBonds hρ _ hA) h3
          (fun b => rfl) hα
      · have h3 := hadm.expectation_freeze_sub_le v hv0 hv1
        simp only [freezeOutside_eq_restrictToBonds] at h3
        rw [ballExpectation_congr_density hd]
        exact h3)
  rw [ballExpectation_congr_density (ballDensity_congr hag).symm A]
  refine key.trans (le_of_eq ?_)
  field_simp
theorem exists_offset_matching (hDist : cellOffsetStatement) {F F' : BlockFrame} [Fintype F.Cell]
    [Fintype F'.Cell] (hL : Odd F.blockSide) (hL' : Odd F'.blockSide) {q : ℕ} (hq : ∀ i, 2 * q + 2 < F.extent i)
    (hq' : ∀ i, 2 * q + 2 < F'.extent i) (Y : F.Cell) (Y' : F'.Cell) :
    ∃ (M : Finset F.Cell) (M' : Finset F'.Cell) (φ : {z // z ∈ M} ≃ {z // z ∈ M'}),
      (∀ z, z ∉ M → (q : ℝ) / 8 ≤ realCellDist z Y) ∧ (∀ z, z ∉ M' → (q : ℝ) / 8 ≤ realCellDist z Y') ∧
      ∀ z : {z // z ∈ M}, ∃ h : Fin 4 → ℤ, (∀ i, 8 * |h i| ≤ q) ∧ z.1 = Y + siteOfCoords F.top h ∧
        (φ z).1 = Y' + siteOfCoords F'.top h := by
  classical
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by have := hq i; omega
  have hs' : ∀ i, 2 ≤ F'.extent i := fun i => by have := hq' i; omega
  obtain ⟨-, d2, d3, d4⟩ := hDist F hL hs
  obtain ⟨-, e2, e3, e4⟩ := hDist F' hL' hs'
  set M : Finset F.Cell := Finset.univ.filter fun z => 8 * cellSupDist z Y ≤ q with hM
  set M' : Finset F'.Cell := Finset.univ.filter fun z => 8 * cellSupDist z Y' ≤ q with hM'
  have small : ∀ {G : BlockFrame} {Z z : G.Cell}, (∀ i, ((cellOffset Z z i).natAbs ≤ cellSupDist z Z)) →
      8 * cellSupDist z Z ≤ q → ∀ i, 8 * |cellOffset Z z i| ≤ q := by
    intro G Z z h1 h2 i
    have h3 := h1 i
    have : 8 * (cellOffset Z z i).natAbs ≤ q := by omega
    have h4 : |cellOffset Z z i| = ((cellOffset Z z i).natAbs : ℤ) := Int.abs_eq_natAbs _
    rw [h4]
    exact_mod_cast this
  have half : ∀ (h : Fin 4 → ℤ), (∀ i, 8 * |h i| ≤ q) → ∀ i, 2 * |h i| ≤ q := by
    intro h hh i
    have := hh i
    have h0 := abs_nonneg (h i)
    linarith
  have zero_small : ∀ l : Fin 4, 2 * |(0 : Fin 4 → ℤ) l| ≤ q := fun l => by simp
  have toF : ∀ (G : BlockFrame) (Z : G.Cell) (h : Fin 4 → ℤ),
      (∀ (a b : Fin 4 → ℤ), (∀ l, 2 * |a l| ≤ q) → (∀ l, 2 * |b l| ≤ q) →
        cellOffset Z (Z + siteOfCoords G.top a) = a ∧
        cellSupDist (Z + siteOfCoords G.top a) (Z + siteOfCoords G.top b) =
          Finset.univ.sup fun i => (a i - b i).natAbs) →
      (∀ i, 8 * |h i| ≤ q) → 8 * cellSupDist (Z + siteOfCoords G.top h) Z ≤ q := by
    intro G Z h hd hh
    have h1 := (hd h 0 (half h hh) zero_small).2
    have h0 : (Z + siteOfCoords G.top (0 : Fin 4 → ℤ) : G.Cell) = Z := by
      funext i
      simp [siteOfCoords]
    rw [h0] at h1
    rw [h1]
    have : (Finset.univ.sup fun i => (h i - (0 : Fin 4 → ℤ) i).natAbs) ≤ q / 8 := by
      refine Finset.sup_le fun i _ => ?_
      have h2 := hh i
      have h3 : |h i| = ((h i).natAbs : ℤ) := Int.abs_eq_natAbs _
      rw [h3] at h2
      have : 8 * (h i).natAbs ≤ q := by exact_mod_cast h2
      simp only [Pi.zero_apply, sub_zero]
      omega
    omega
  have mem_M : ∀ h : Fin 4 → ℤ, (∀ i, 8 * |h i| ≤ q) → Y + siteOfCoords F.top h ∈ M := fun h hh =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, toF F Y h (d4 q hq Y) hh⟩
  have mem_M' : ∀ h : Fin 4 → ℤ, (∀ i, 8 * |h i| ≤ q) → Y' + siteOfCoords F'.top h ∈ M' := fun h hh =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, toF F' Y' h (e4 q hq' Y') hh⟩
  have sm : ∀ z : {z // z ∈ M}, ∀ i, 8 * |cellOffset Y z.1 i| ≤ q := fun z =>
    small (d3 Y z.1) (Finset.mem_filter.1 z.2).2
  have sm' : ∀ z : {z // z ∈ M'}, ∀ i, 8 * |cellOffset Y' z.1 i| ≤ q := fun z =>
    small (e3 Y' z.1) (Finset.mem_filter.1 z.2).2
  refine ⟨M, M', ⟨fun z => ⟨Y' + siteOfCoords F'.top (cellOffset Y z.1), mem_M' _ (sm z)⟩,
    fun w => ⟨Y + siteOfCoords F.top (cellOffset Y' w.1), mem_M _ (sm' w)⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro z
    apply Subtype.ext
    show Y + siteOfCoords F.top (cellOffset Y' (Y' + siteOfCoords F'.top (cellOffset Y z.1))) = z.1
    rw [(e4 q hq' Y' _ 0 (half _ (sm z)) zero_small).1, d2]
  · intro w
    apply Subtype.ext
    show Y' + siteOfCoords F'.top (cellOffset Y (Y + siteOfCoords F.top (cellOffset Y' w.1))) = w.1
    rw [(d4 q hq Y _ 0 (half _ (sm' w)) zero_small).1, e2]
  · intro z hz
    have : ¬ 8 * cellSupDist z Y ≤ q := fun h => hz (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    simp only [realCellDist]
    have h2 : (q : ℝ) < 8 * (cellSupDist z Y : ℝ) := by exact_mod_cast not_le.1 this
    linarith
  · intro z hz
    have : ¬ 8 * cellSupDist z Y' ≤ q := fun h => hz (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    simp only [realCellDist]
    have h2 : (q : ℝ) < 8 * (cellSupDist z Y' : ℝ) := by exact_mod_cast not_le.1 this
    linarith
  · intro z
    exact ⟨cellOffset Y z.1, sm z, (d2 Y z.1).symm, rfl⟩
theorem three_term_bound {α c N₁ N₂ e₁ e₂ e₃ e₄ : ℝ} (hα : 0 ≤ α) (hc : 1 ≤ c) (h1 : 0 ≤ N₁) (h2 : 0 ≤ N₂)
    (he₁ : e₁ ≤ e₄) (he₂ : e₂ ≤ e₄) (he₃ : e₃ ≤ e₄) (he₁0 : 0 ≤ e₁) (he₄ : 0 ≤ e₄) :
    (α * e₁ + α * c * N₁ * e₂) + (α * e₁ + α * c * N₂ * (e₁ + e₃)) + (α * e₁ + α * c * N₁ * e₂) ≤
      α * c * (3 + 2 * N₁ + 2 * N₂) * e₄ := by
  have a1 : α * e₁ ≤ α * c * e₄ := by
    have : e₁ ≤ c * e₄ := by nlinarith
    calc α * e₁ ≤ α * (c * e₄) := mul_le_mul_of_nonneg_left this hα
      _ = _ := by ring
  have a2 : α * c * N₁ * e₂ ≤ α * c * N₁ * e₄ := mul_le_mul_of_nonneg_left he₂ (by positivity)
  have a3 : α * c * N₂ * (e₁ + e₃) ≤ α * c * N₂ * (2 * e₄) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith
end Decoupling
set_option maxHeartbeats 1000000 in
open Decoupling YangMills.Construction.ColdStepAtMirrorFrames.LocalCalculus in
theorem expectationDecouples_of_parts (hJ : joinAtLoweredSmallnessConstantStatement)
    (hP : stepLawLocalDecomposition) (hM : matchedCellPartsGradientBound)
    (hF1 : frozenExpectationDifferenceBound) (hF2 : expectationComparisonBound)
    (hFz : FrozenPotentialExpectationFactorizes) (hW : _root_.YangMills.Construction.CellCounting.ExpDecaySumBounded)
    (hCnt : cellBondsCardStatement) (hDist : cellOffsetStatement)
    (hlaw : normalizedBallLawIsProbabilityStatement) : expectationDecouples := by
  classical
  have hW' : ∀ (N : ℕ) (κ : ℝ), ∃ W : ℝ, 0 < κ → 0 ≤ W ∧
      ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (y : ι → F.Cell),
        (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ N) →
        ∀ z : F.Cell, ∑ b, Real.exp (-(κ * (cellSupDist (y b) z : ℝ))) ≤ W := by
    intro N κ
    by_cases h : 0 < κ
    · obtain ⟨W, h1, h2⟩ := hW N κ h
      exact ⟨W, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Wf hWf using hW'
  set Sf : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ := fun U => Wf (4 * U.L ^ 4) (U.κ / 4) + Wf 1 (U.κ / 4) with hSf
  set G : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → ℝ → ℝ := fun U c =>
    max (c * (3 + 2 * freezeGradientConstant U.chainParams.lam (Sf U) +
      2 * comparisonConstant U.chainParams.lam (Sf U))) (Real.exp (U.κ * U.blockIndex / 2 ^ 7)) with hG
  refine hJ StepLawLocalDecomposition matchedCellPartsGradientBoundAt ExpectationDecouples G hP hM ?_
  intro T c hc hodd hn hy hE hη hη1 hκ hσ hch hcut hGle hParts hMatch
  intro t x s l F F' V V' Y Y' q ι _ _ j j' α A A' hx hs hs1 hl hTF hTF' hV hV' hAg hpair hα hdA hdA' hadm
  have hρ : 0 < T.ballRadius := by
    show 0 < T.σ / 64
    positivity
  have hcut' : IsCutoff T.ballRadius T.p := hcut
  have hlam : 0 < T.chainParams.lam := hch.positivity.2.2.1
  have hx1 : 1 ≤ x := hy.trans hx
  have hκ4 : 0 < T.κ / 4 := by positivity
  set S := Sf T with hSdef
  have hW1 := hWf (4 * T.L ^ 4) (T.κ / 4) hκ4
  have hW2 := hWf 1 (T.κ / 4) hκ4
  have hSn : 0 ≤ S := add_nonneg hW1.1 hW2.1
  have sides : ∀ {G : BlockFrame}, IsCubicTopTorus T.L t T.n₀ G →
      (∀ i, G.extent i = 0 ∨ 2 * q + 2 < G.extent i) → ∀ i, 2 * q + 2 < G.extent i := by
    intro G hG hA i
    obtain ⟨-, -, m, hm, hnm⟩ := hG
    rcases hA i with h | h
    · have := hm i
      omega
    · exact h
  have hq := sides hTF hAg.1
  have hq' := sides hTF' hAg.2.1
  have hL : Odd F.blockSide := by rw [hTF.1]; exact hodd
  have hL' : Odd F'.blockSide := by rw [hTF'.1]; exact hodd
  have two : ∀ {G : BlockFrame}, (∀ i, 2 * q + 2 < G.extent i) → ∀ i, 2 ≤ G.extent i := fun h i => by
    have := h i
    omega
  have finite_cells : ∀ {G : BlockFrame}, (∀ i, 2 ≤ G.extent i) → Finite G.Cell := by
    intro G h
    have hne : ∀ i, NeZero (G.period G.top i) := fun i => ⟨by
      simp only [BlockFrame.period, Nat.sub_self, pow_zero, mul_one]
      have := h i
      omega⟩
    have : ∀ i, Finite (ZMod (G.period G.top i)) := fun i => by
      have := hne i
      exact inferInstance
    exact Pi.finite
  haveI := finite_cells (two hq)
  haveI := finite_cells (two hq')
  letI : Fintype F.Cell := Fintype.ofFinite _
  letI : Fintype F'.Cell := Fintype.ofFinite _
  have sums : ∀ (G : BlockFrame) [Fintype G.Cell], G.blockSide = T.L → Odd G.blockSide →
      (∀ i, 2 ≤ G.extent i) →
      (∀ z : G.Cell, ∑ b : ↥(chordBonds (finiteCells G)),
        Real.exp (-(T.κ / 4 * realCellDist (bondCell b) z)) ≤ S) ∧
      (∀ z : G.Cell, ∑ z' : G.Cell, Real.exp (-(T.κ / 4 * realCellDist z' z)) ≤ S) := by
    intro G _ hGL hGo hG2
    constructor
    · intro z
      have h1 := hW1.2 G (↥(chordBonds (finiteCells G))) bondCell (fun z' => by
        have := hCnt G hGo hG2 z'
        rw [hGL] at this
        exact this) z
      exact h1.trans (by linarith [hW2.1])
    · intro z
      have h1 := hW2.2 G G.Cell id (fun z' => by
        refine Finset.card_le_one.2 fun a ha b hb => ?_
        have e1 := (Finset.mem_filter.1 ha).2
        have e2 := (Finset.mem_filter.1 hb).2
        simp only [id] at e1 e2
        rw [e1, e2]) z
      exact h1.trans (by linarith [hW1.1])
  obtain ⟨hS, hSp⟩ := sums F hTF.1 hL (two hq)
  obtain ⟨hS2, hSp2⟩ := sums F' hTF'.1 hL' (two hq')
  obtain ⟨Ψ, ag, good, sum, terms⟩ := hParts t x s l F V hx hs hs1 hl hTF hV
  obtain ⟨Ψ', ag', good', sum', terms'⟩ := hParts t x s l F' V' hx hs hs1 hl hTF' hV'
  set Eo := l.amplitude T.energyRatio with hEo
  have hE₃ : 0 ≤ T.energyRatio := by
    show 0 ≤ T.E / T.η₃
    have : 0 ≤ T.E := by linarith
    positivity
  have hEo1 : 1 ≤ Eo := by
    cases l with
    | ofFamily φ =>
      show 1 ≤ 1 + T.energyRatio
      linarith
    | ofWeight τ =>
      show (1 : ℝ) ≤ 1
      exact le_rfl
  set cc := c * Eo with hcc
  have hcc1 : 1 ≤ cc := by nlinarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  set Φ := l.exponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) V with hΦ
  set Φ' := l.exponent s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) V' with hΦ'
  set e₄ := Real.exp (-(T.κ * q / 2 ^ 7)) with he₄
  have he₄0 : 0 < e₄ := Real.exp_pos _
  have hnum : (max (c * (3 + 2 * freezeGradientConstant T.chainParams.lam S +
      2 * comparisonConstant T.chainParams.lam S)) (Real.exp (T.κ * T.blockIndex / 2 ^ 7))) ≤ T.Cs := hGle
  have hCs1 := (le_max_left _ _).trans hnum
  have hCs2 := (le_max_right _ _).trans hnum
  have hEo2 : Eo ≤ Eo ^ 2 := by nlinarith
  by_cases hnq : T.blockIndex ≤ q
  swap
  · have hm := hadm.expectation_sub_le
    refine hm.trans ?_
    have hexp : 1 ≤ T.Cs * e₄ := by
      have h1 : Real.exp (T.κ * T.blockIndex / 2 ^ 7) * e₄ ≤ T.Cs * e₄ :=
        mul_le_mul_of_nonneg_right hCs2 he₄0.le
      refine le_trans ?_ h1
      rw [he₄, ← Real.exp_add]
      apply Real.one_le_exp
      have h2 : (q : ℝ) ≤ T.blockIndex := by exact_mod_cast (not_le.1 hnq).le
      have h3 : T.κ * q ≤ T.κ * T.blockIndex := mul_le_mul_of_nonneg_left h2 hκ.le
      have : T.κ * T.blockIndex / 2 ^ 7 + -(T.κ * q / 2 ^ 7) = (T.κ * T.blockIndex - T.κ * q) / 2 ^ 7 := by ring
      rw [this]
      apply div_nonneg <;> [linarith; norm_num]
    have h1 : 1 ≤ Eo ^ 2 := by nlinarith
    calc α = 1 * 1 * α := by ring
      _ ≤ (T.Cs * e₄) * Eo ^ 2 * α := by
        apply mul_le_mul_of_nonneg_right _ hα
        exact mul_le_mul hexp h1 (by norm_num) (by linarith)
      _ = _ := by ring
  have hS1 := abs_expectation_sub_frozen_le hF1 (F := F) (Y := Y) (q := q) (A := A) hρ hκ hlam hx1 hcc1 hα
    hcut' ag good hS hSp terms sum hdA hadm.left
  have hS3 := abs_expectation_sub_frozen_le hF1 (F := F') (Y := Y') (q := q) (A := A') hρ hκ hlam hx1 hcc1 hα
    hcut' ag' good' hS2 hSp2 terms' sum' hdA' hadm.right
  have hpr := hpair.isBoxPairing
  have contΨ : Continuous Ψ := by
    obtain ⟨K, hK, _⟩ := good
    exact hK.smooth.continuous
  have contΨ' : Continuous Ψ' := by
    obtain ⟨K, hK, _⟩ := good'
    exact hK.smooth.continuous
  have hμ : 0 ≤ x * T.chainParams.lam := by positivity
  have splitOf : ∀ (G : BlockFrame) (Ψ₀ H₀ : StepVariable (finiteCells G) → ℝ) (Z : G.Cell)
      (j₀ : ι → ↥(chordBonds (finiteCells G))), Continuous Ψ₀ → Function.Injective j₀ →
      (∀ b, b ∈ bondsNearCell Z q ↔ ∃ i, j₀ i = b) →
      ballExpectation (cutoffFactor T.ballRadius T.p) (frozenPotential (bondsNearCell Z q) (x * T.chainParams.lam) Ψ₀)
        (fun η => H₀ (restrictToBonds (bondsNearCell Z q) η)) =
      ballExpectation (cutoffFactor T.ballRadius T.p) (fun ξ => Ψ₀ (pushforwardField j₀ ξ))
        (fun ξ => H₀ (pushforwardField j₀ ξ)) := by
    intro G Ψ₀ H₀ Z j₀ hc₀ hinj hrange
    let e₀ : ι ≃ {b // b ∈ bondsNearCell Z q} :=
      Equiv.ofBijective (fun i => ⟨j₀ i, (hrange (j₀ i)).2 ⟨i, rfl⟩⟩)
        ⟨fun a b h => hinj (congrArg Subtype.val h), fun b => by
          obtain ⟨i, hi⟩ := (hrange b.1).1 b.2
          exact ⟨i, Subtype.ext hi⟩⟩
    exact hFz (↥(chordBonds (finiteCells G))) ι (bondsNearCell Z q) e₀ T.ballRadius (x * T.chainParams.lam) T.p Ψ₀ H₀
      hρ hcut' hc₀ hμ
  have eq₁ := splitOf F Ψ A Y j contΨ hpr.injective_left hpr.mem_left_iff
  have eq₃ := splitOf F' Ψ' A' Y' j' contΨ' hpr.injective_right hpr.mem_right_iff
  rw [eq₁] at hS1
  rw [eq₃] at hS3
  obtain ⟨d1, -, -, d4⟩ := hDist F hL (two hq)
  obtain ⟨f1, -, -, f4⟩ := hDist F' hL' (two hq')
  have offs : ∀ k, ∃ h : Fin 4 → ℤ, (∀ l, 2 * |h l| ≤ q) ∧ bondCell (j k) = Y + siteOfCoords F.top h ∧
      bondCell (j' k) = Y' + siteOfCoords F'.top h := by
    intro k
    obtain ⟨h, o, k₀, hs₀, ho, e1, e2⟩ := hpair.short_offsets k
    refine ⟨h, hs₀, ?_, ?_⟩
    · show enclosingCell (j k).1.1 = _
      rw [e1]
      exact d1 Y h o k₀ ho
    · show enclosingCell (j' k).1.1 = _
      rw [e2]
      have ho' : o ∈ centredCube F'.blockSide := by
        rw [hTF'.1, ← hTF.1]
        exact ho
      exact f1 Y' h o k₀ ho'
  have hzero : ∀ l : Fin 4, 2 * |(0 : Fin 4 → ℤ) l| ≤ q := fun l => by simp
  have hY0 : (Y + siteOfCoords F.top (0 : Fin 4 → ℤ) : F.Cell) = Y := by
    funext i
    simp [siteOfCoords]
  have hY0' : (Y' + siteOfCoords F'.top (0 : Fin 4 → ℤ) : F'.Cell) = Y' := by
    funext i
    simp [siteOfCoords]
  have hdist : ∀ k k', realCellDist (bondCell (j k)) (bondCell (j k')) =
      realCellDist (bondCell (j' k)) (bondCell (j' k')) := by
    intro k k'
    obtain ⟨a, ha, e1, e2⟩ := offs k
    obtain ⟨b, hb, e3, e4⟩ := offs k'
    simp only [realCellDist]
    rw [e1, e2, e3, e4, (d4 q hq Y a b ha hb).2, (f4 q hq' Y' a b ha hb).2]
  have hYd : ∀ k, realCellDist (bondCell (j k)) Y = realCellDist (bondCell (j' k)) Y' := by
    intro k
    obtain ⟨a, ha, e1, e2⟩ := offs k
    simp only [realCellDist]
    have h1 := (d4 q hq Y a 0 ha hzero).2
    have h2 := (f4 q hq' Y' a 0 ha hzero).2
    rw [hY0] at h1
    rw [hY0'] at h2
    rw [e1, e2, h1, h2]
  obtain ⟨M, M', φ, hfar, hfar', hmatch⟩ := exists_offset_matching hDist hL hL' hq hq' Y Y'
  have hcomp : ∀ (z : {z // z ∈ M}), ∀ ξ ∈ openPolyball ι T.ballRadius, ∀ k,
      bondGradNorm (fun ζ =>
        stepLawCellPart l s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) V' (φ z).1 (pushforwardField j' ζ) -
        stepLawCellPart l s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) V z.1 (pushforwardField j ζ)) k ξ ≤
        cc * Real.exp (-(4 * T.κ * q)) *
          (x * Real.sqrt (weightedSqNormNear T.κ (fun k => bondCell (j k)) realCellDist z.1 ξ) + 1) *
          Real.exp (-(2 * T.κ * realCellDist (bondCell (j k)) z.1)) := by
    intro z ξ hξ k
    obtain ⟨h, hh, e1, e2⟩ := hmatch z
    have := hMatch t x s l F F' V V' Y Y' q ι j j' h hx hs hs1 hl hTF hTF' hV hV' hAg hpair hnq hh ξ hξ k
    rw [e1, e2]
    exact this
  have embAg : ∀ ξ ∈ openPolyball ι T.ballRadius, Ψ (pushforwardField j ξ) = Φ (pushforwardField j ξ) :=
    fun ξ hξ => ag _ (pushforwardField_mem_openPolyball hρ j hpr.injective_left hξ)
  have embAg' : ∀ ξ ∈ openPolyball ι T.ballRadius, Ψ' (pushforwardField j' ξ) = Φ' (pushforwardField j' ξ) :=
    fun ξ hξ => ag' _ (pushforwardField_mem_openPolyball hρ j' hpr.injective_right hξ)
  have segAg : ∀ v : ℝ, ∀ ξ ∈ openPolyball ι T.ballRadius,
      segmentInterpolant (fun ξ => Ψ (pushforwardField j ξ)) (fun ξ => Ψ' (pushforwardField j' ξ)) v ξ =
        pairingHomotopy j j' Φ Φ' (1 - v) ξ := by
    intro v ξ hξ
    simp only [segmentInterpolant, pairingHomotopy, toTorus]
    have e1 : _root_.YangMills.Construction.Interpolation.extendByZero j Finset.univ ξ = pushforwardField j ξ := rfl
    have e2 : _root_.YangMills.Construction.Interpolation.extendByZero j' Finset.univ ξ = pushforwardField j' ξ := rfl
    rw [e1, e2, embAg ξ hξ, embAg' ξ hξ]
    ring
  have smoothEmb : ∀ {G : BlockFrame} (j₀ : ι → ↥(chordBonds (finiteCells G)))
      {H₀ : StepVariable (finiteCells G) → ℝ}, Function.Injective j₀ →
      ContDiffOn ℝ 1 H₀ (openPolyball _ T.ballRadius) →
      ContDiffOn ℝ 1 (fun ξ => H₀ (pushforwardField j₀ ξ)) (openPolyball ι T.ballRadius) := by
    intro G j₀ H₀ hinj hH
    have e : (fun ξ => H₀ (pushforwardField j₀ ξ)) = fun ζ => H₀ (pushforwardFieldCLM j₀ ζ) := by
      funext ζ
      simp [pushforwardFieldCLM_apply]
    rw [e]
    exact hH.comp (pushforwardFieldCLM j₀).contDiff.contDiffOn (fun ξ hξ => by
      rw [pushforwardFieldCLM_apply]
      exact pushforwardField_mem_openPolyball hρ j₀ hinj hξ)
  have hgrad : ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
      HasFrozenGradientBound T.ballRadius T.κ (Real.sqrt x * α) T.p (fun k => bondCell (j k)) realCellDist Y
        (segmentInterpolant (fun ξ => Ψ (pushforwardField j ξ)) (fun ξ => Ψ' (pushforwardField j' ξ)) v)
        (fun ξ => A (pushforwardField j ξ)) ∧
      HasFrozenGradientBound T.ballRadius T.κ (Real.sqrt x * α) T.p (fun k => bondCell (j k)) realCellDist Y
        (segmentInterpolant (fun ξ => Ψ (pushforwardField j ξ)) (fun ξ => Ψ' (pushforwardField j' ξ)) v)
        (fun ξ => A' (pushforwardField j' ξ)) ∧
      |ballExpectation (cutoffFactor T.ballRadius T.p)
        (segmentInterpolant (fun ξ => Ψ (pushforwardField j ξ)) (fun ξ => Ψ' (pushforwardField j' ξ)) v)
        (fun ξ => A' (pushforwardField j' ξ) - A (pushforwardField j ξ))| ≤ α * Real.exp (-(4 * T.κ * q)) := by
    intro v hv0 hv1
    have hd := ballDensity_congr (p := T.p) (segAg v)
    obtain ⟨g1, g2⟩ := hadm.hasGradientBound_shared (1 - v) (by linarith) (by linarith)
    refine ⟨hasFrozenGradientBound_of_hasGradientBound hd (smoothEmb j hpr.injective_left hdA) g1 (fun b => rfl) hα,
      hasFrozenGradientBound_of_hasGradientBound hd (smoothEmb j' hpr.injective_right hdA') g2 (fun b => rfl) hα, ?_⟩
    rw [ballExpectation_congr_density hd, ballExpectation_sub_eq_neg, abs_neg]
    exact hadm.expectation_shared_le hnq (1 - v) (by linarith) (by linarith)
  have rimOf : ∀ (ψ₀ H₀ : BondField ι → ℝ), Continuous ψ₀ →
      (Integrable fun η => H₀ η * ballDensity (cutoffFactor T.ballRadius T.p) ψ₀ η) →
      Integrable fun η => H₀ η * radialWeightProd (cutoffFactor T.ballRadius T.p) η := by
    intro ψ₀ H₀ hc₀ hi
    obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : BondField ι) T.ballRadius).exists_bound_of_continuousOn
      hc₀.continuousOn
    refine integrable_mul_radialWeightProd hc₀ (M := M₀) (fun η hη => ?_) hi
    have : η ∈ Metric.closedBall (0 : BondField ι) T.ballRadius := by
      rw [openPolyball_eq_ball hρ] at hη
      exact Metric.ball_subset_closedBall hη
    simpa using hM₀ η this
  have cEmb : Continuous fun ξ : BondField ι => Ψ (pushforwardField j ξ) := by
    have : (fun ξ : BondField ι => pushforwardField j ξ) = fun ζ => pushforwardFieldCLM j ζ := by
      funext ζ
      rw [pushforwardFieldCLM_apply]
    rw [show (fun ξ : BondField ι => Ψ (pushforwardField j ξ)) = fun ζ => Ψ (pushforwardFieldCLM j ζ) by
      funext ζ
      rw [pushforwardFieldCLM_apply]]
    exact contΨ.comp (pushforwardFieldCLM j).continuous
  have cEmb' : Continuous fun ξ : BondField ι => Ψ' (pushforwardField j' ξ) := by
    rw [show (fun ξ : BondField ι => Ψ' (pushforwardField j' ξ)) = fun ζ => Ψ' (pushforwardFieldCLM j' ζ) by
      funext ζ
      rw [pushforwardFieldCLM_apply]]
    exact contΨ'.comp (pushforwardFieldCLM j').continuous
  have seg0 : segmentInterpolant (fun ξ => Ψ (pushforwardField j ξ)) (fun ξ => Ψ' (pushforwardField j' ξ)) 0 =
      fun ξ => Ψ (pushforwardField j ξ) := by
    funext ξ
    simp [segmentInterpolant]
  have seg1 : segmentInterpolant (fun ξ => Ψ (pushforwardField j ξ)) (fun ξ => Ψ' (pushforwardField j' ξ)) 1 =
      fun ξ => Ψ' (pushforwardField j' ξ) := by
    funext ξ
    simp [segmentInterpolant]
  have hI₁ : Integrable fun ξ => A (pushforwardField j ξ) * radialWeightProd (cutoffFactor T.ballRadius T.p) ξ := by
    have g := (hgrad 0 le_rfl zero_le_one).1
    rw [seg0] at g
    exact rimOf _ _ cEmb
      (integrable_mul_ballDensity_of_sq hlaw hρ hcut' cEmb g.smooth.continuousOn g.sq_integrable)
  have hI₂ : Integrable fun ξ => A' (pushforwardField j' ξ) * radialWeightProd (cutoffFactor T.ballRadius T.p) ξ := by
    have g := (hgrad 1 zero_le_one le_rfl).2.1
    rw [seg1] at g
    exact rimOf _ _ cEmb'
      (integrable_mul_ballDensity_of_sq hlaw hρ hcut' cEmb' g.smooth.continuousOn g.sq_integrable)
  have hS2' := hF2 (↥(chordBonds (finiteCells F))) (↥(chordBonds (finiteCells F'))) ι F.Cell F'.Cell T.ballRadius
    T.κ S T.chainParams.lam x cc (Real.exp (-(4 * T.κ * q))) (q : ℝ) (Real.sqrt x * α) (α * Real.exp (-(4 * T.κ * q)))
    T.p bondCell realCellDist Ψ
    (stepLawCellPart l s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) V) Y
    bondCell realCellDist Ψ' (stepLawCellPart l s T.a T.chainParams.ρA T.chainParams.lam x (frameRadius x) V') Y'
    j j' M M' φ (fun ξ => A (pushforwardField j ξ)) (fun ξ => A' (pushforwardField j' ξ)) hρ hκ hlam hx1 hcc1
    (Real.exp_pos _).le hq0 (by positivity) hcut' isPseudoMetricOnBonds_realCellDist
    isPseudoMetricOnBonds_realCellDist good good' hS hSp hS2 hSp2
    terms sum terms' sum' hpr.injective_left hpr.injective_right hdist hYd hfar hfar' hcomp hI₁ hI₂ hgrad
  have hx0 : 0 < x := by linarith
  have e_simp : Real.sqrt x * α * (Real.sqrt x)⁻¹ = α := by
    field_simp
  set N₁ := freezeGradientConstant T.chainParams.lam S with hN₁
  set N₂ := comparisonConstant T.chainParams.lam S with hN₂
  have hN₁0 : 0 ≤ N₁ := by
    simp only [hN₁, freezeGradientConstant]
    positivity
  have hN₂0 : 0 ≤ N₂ := by
    simp only [hN₂, comparisonConstant]
    positivity
  set e₁ := Real.exp (-(4 * T.κ * q)) with he₁
  set e₂ := Real.exp (-(T.κ * q / 16)) with he₂
  set e₃ := Real.exp (-(T.κ * q / 32)) with he₃
  have hκq : 0 ≤ T.κ * q := by positivity
  have l1 : e₁ ≤ e₄ := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have l2 : e₂ ≤ e₄ := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have l3 : e₃ ≤ e₄ := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have b2 : |ballExpectation (cutoffFactor T.ballRadius T.p) (fun ξ => Ψ' (pushforwardField j' ξ))
      (fun ξ => A' (pushforwardField j' ξ)) -
      ballExpectation (cutoffFactor T.ballRadius T.p) (fun ξ => Ψ (pushforwardField j ξ))
        (fun ξ => A (pushforwardField j ξ))| ≤
      α * e₁ + α * cc * N₂ * (e₁ + e₃) := by
    refine hS2'.trans (le_of_eq ?_)
    rw [show Real.sqrt x * α * (Real.sqrt x)⁻¹ * cc * N₂ * (e₁ + e₃) =
      (Real.sqrt x * α * (Real.sqrt x)⁻¹) * cc * N₂ * (e₁ + e₃) by ring, e_simp]
  have tri : |ballExpectation (cutoffFactor T.ballRadius T.p) Φ A -
      ballExpectation (cutoffFactor T.ballRadius T.p) Φ' A'| ≤
      (α * e₁ + α * cc * N₁ * e₂) + (α * e₁ + α * cc * N₂ * (e₁ + e₃)) +
        (α * e₁ + α * cc * N₁ * e₂) := by
    have := abs_sub_le (ballExpectation (cutoffFactor T.ballRadius T.p) Φ A)
      (ballExpectation (cutoffFactor T.ballRadius T.p) (fun ξ => Ψ (pushforwardField j ξ))
        (fun ξ => A (pushforwardField j ξ)))
      (ballExpectation (cutoffFactor T.ballRadius T.p) Φ' A')
    have h2 := abs_sub_le (ballExpectation (cutoffFactor T.ballRadius T.p) (fun ξ => Ψ (pushforwardField j ξ))
        (fun ξ => A (pushforwardField j ξ)))
      (ballExpectation (cutoffFactor T.ballRadius T.p) (fun ξ => Ψ' (pushforwardField j' ξ))
        (fun ξ => A' (pushforwardField j' ξ)))
      (ballExpectation (cutoffFactor T.ballRadius T.p) Φ' A')
    have h3 : |ballExpectation (cutoffFactor T.ballRadius T.p) (fun ξ => Ψ (pushforwardField j ξ))
          (fun ξ => A (pushforwardField j ξ)) -
        ballExpectation (cutoffFactor T.ballRadius T.p) (fun ξ => Ψ' (pushforwardField j' ξ))
          (fun ξ => A' (pushforwardField j' ξ))| ≤
        α * e₁ + α * cc * N₂ * (e₁ + e₃) := by
      rw [abs_sub_comm]
      exact b2
    have h4 : |ballExpectation (cutoffFactor T.ballRadius T.p) (fun ξ => Ψ' (pushforwardField j' ξ))
          (fun ξ => A' (pushforwardField j' ξ)) -
        ballExpectation (cutoffFactor T.ballRadius T.p) Φ' A'| ≤ α * e₁ + α * cc * N₁ * e₂ := by
      rw [abs_sub_comm]
      exact hS3
    linarith
  refine tri.trans ((three_term_bound hα hcc1 hN₁0 hN₂0 l1 l2 l3 (Real.exp_pos _).le he₄0.le).trans ?_)
  have hk : 0 ≤ α * e₄ := by positivity
  have h5 : c * (3 + 2 * N₁ + 2 * N₂) * Eo ≤ T.Cs * Eo ^ 2 := by
    have h6 := mul_le_mul_of_nonneg_right hCs1 (by linarith : (0 : ℝ) ≤ Eo)
    have h7 : T.Cs * Eo ≤ T.Cs * Eo ^ 2 := by
      have hCs0 : 0 ≤ T.Cs := le_trans (Real.exp_pos _).le hCs2
      exact mul_le_mul_of_nonneg_left hEo2 hCs0
    exact h6.trans h7
  calc α * cc * (3 + 2 * N₁ + 2 * N₂) * e₄
      = (c * (3 + 2 * N₁ + 2 * N₂) * Eo) * (α * e₄) := by
        simp only [hcc]
        ring
    _ ≤ (T.Cs * Eo ^ 2) * (α * e₄) := mul_le_mul_of_nonneg_right h5 hk
    _ = T.Cs * Eo ^ 2 * α * e₄ := by ring
end TorusFreezing
end YangMills.Construction
end
