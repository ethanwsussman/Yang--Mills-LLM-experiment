import YangMills.Construction.SummableBoundsOfTheFlow.FloorOfTheScaledExponentsProof
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongTheScaleAndATop
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.SmoothObservablesOfTheStep
import YangMills.Construction.SummableBoundsOfTheFlow.TheFramesBetween
import Mathlib
set_option autoImplicit false

noncomputable section
open Filter MeasureTheory
namespace YangMills.Construction.ScaledVariables
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.ScaleDerivatives YangMills.Construction.DensityMeans YangMills.Construction.Interpolation YangMills.Construction.FamilyNorms
variable {F : BlockFrame}
def StepLaw.exponentWeight : StepLaw → ℝ
  | .tilted _ => 1
  | .interpolated τ => τ
def StepLaw.familyWeight : StepLaw → ℝ
  | .tilted ν => ν
  | .interpolated _ => 0
def RescaledExponentsAgree (T : ColdStepAtMirrorFrames.StepParameters) (l₀ : ℝ) : Prop :=
  ∀ (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (f : LocalFamily) (ν l : ℝ) (Y : F.Cell)
    (ζ : StepVariable (finiteCells F)), IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
    0 < l → l ≤ l₀ → MemScaledBalls T.ballRadius l ζ →
    stepExponent true T.a T.ρA (l⁻¹ ^ 2) 0 f ν V (l • ζ) = rescaledExponent T.a T.ρA f ν l V ζ ∧
    cellExponent true T.a T.ρA (l⁻¹ ^ 2) 0 Y V (l • ζ) = rescaledCellTerm T.a T.ρA l Y V ζ ∧
    cellQuadratic T.lam (l⁻¹ ^ 2) Y (l • ζ) = T.lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)),
      if enclosingCell b.1.1 = Y then ‖ζ b‖ ^ 2 else 0
def chordBondCell (F : BlockFrame) (b : ↥(chordBonds (finiteCells F))) : F.Cell := enclosingCell b.1.1
structure StepLawAtScale (T : ColdStepAtMirrorFrames.StepParameters) (Cq : ℕ → ℝ) (Cr : ℕ → ℕ → ℕ → ℝ) (l : ℝ)
    (f : LocalFamily) (V : F.GaugeField F.top)
    (law : StepLaw) (Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ)
    (K : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ) : Prop where
  convex : IsUniformlyConvexDecaying T.ballRadius (l⁻¹ ^ 2 * T.lam / 4) T.κ
    (fun b b' => (cellSupDist (chordBondCell F b) (chordBondCell F b') : ℝ)) Ψ K
  firstDeriv_le : ∀ (b : ↥(chordBonds (finiteCells F))) (u : BondVector),
    |bondPartialDeriv Ψ b 0 u| ≤ Real.sqrt (l⁻¹ ^ 2 * T.lam / 4) * ‖u‖
  moments : ∀ (q : ℕ) (b : ↥(chordBonds (finiteCells F))),
    ballExpectation (cutoffFactor T.ballRadius T.p) Ψ (fun η => ‖η b‖ ^ (2 * q)) ≤ Cq q * ((l⁻¹ ^ 2) ^ q)⁻¹
  cutoff_deriv_moments : ∀ (j q N : ℕ) (b : ↥(chordBonds (finiteCells F))), 1 ≤ j → 1 ≤ q →
    Integrable (fun η => |iteratedDeriv j T.p ‖η b‖| ^ q * ballDensity (cutoffFactor T.ballRadius T.p) Ψ η) ∧
    ballExpectation (cutoffFactor T.ballRadius T.p) Ψ (fun η => |iteratedDeriv j T.p ‖η b‖| ^ q) ≤
      Cr j q N * ((l⁻¹ ^ 2) ^ N)⁻¹
  density_eq : ∀ ζ : StepVariable (finiteCells F), ballDensity (cutoffFactor T.ballRadius T.p) Ψ (l • ζ) =
    scaledCutoff T.ballRadius T.p l ζ * Real.exp (-rescaledLawExponent T.a T.ρA T.lam f l V law ζ)
def stepLawAtScaleStatement : Prop :=
  (∀ (F : BlockFrame), Finite F.Cell → ∀ (a ρ lam : ℝ) (f : LocalFamily) (l : ℝ) (V : F.GaugeField F.top) (law : StepLaw)
    (ζ : StepVariable (finiteCells F)),
    rescaledLawExponent a ρ lam f l V law ζ =
      (∑ Y ∈ finiteCells F, (StepLaw.exponentWeight law * rescaledCellRemainder a ρ lam l Y V ζ -
        StepLaw.familyWeight law * rescaledCellExpansion a ρ f l Y V ζ)) +
        lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2) ∧
  (∀ (T : ColdStepAtMirrorFrames.StepParameters) (l₀ : ℝ), RescaledExponentsAgree T l₀ →
    ∀ (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (f : LocalFamily)
    (law : StepLaw) (l : ℝ) (Y : F.Cell), IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → 0 < l →
    l ≤ l₀ →
    ∀ Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ,
      observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l V =
      densityMean volume (fun ζ => scaledCutoff T.ballRadius T.p l ζ *
        Real.exp (-rescaledLawExponent T.a T.ρA T.lam f l V law ζ))
        fun ζ => Ob l ζ V) ∧
  ∀ (T : ColdStepAtMirrorFrames.StepParameters) (Cq Cz : ℕ → ℝ) (Cr : ℕ → ℕ → ℕ → ℝ) (t : ℕ) (l l₀ : ℝ)
    (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
    (law : StepLaw) (Y : F.Cell), InterpolatedFrameBoundsAt T Cq Cz Cr t (l⁻¹ ^ 2) →
    IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → StepLaw.IsUnitWeight law → 0 < l → l ≤ l₀ →
    RescaledExponentsAgree T l₀ →
    ∃ (Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ)
      (K : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ), StepLawAtScale T Cq Cr l f V law Ψ K
end YangMills.Construction.ScaledVariables
end

noncomputable section
namespace YangMills.Construction.ScaledVariables
open Set Filter Topology MeasureTheory
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.Interpolation YangMills.Construction.DensityMeans
open YangMills.Construction.ScaleDerivatives YangMills.Construction.FamilyNorms
variable {F : BlockFrame}
theorem stepExponent_frameRadius_indep (a ρA x : ℝ) (m : ℕ) (f : LocalFamily) (ν : ℝ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) : stepExponent true a ρA x m f ν V η = stepExponent true a ρA x 0 f ν V η := by apply _root_.YangMills.SharedProofs.p27308 <;> assumption
theorem mem_finiteCells (h : Finite F.Cell) (Y : F.Cell) : Y ∈ finiteCells F := by apply _root_.YangMills.SharedProofs.p8277 <;> assumption
theorem rescaledLawExponent_eq_sum (hfin : Finite F.Cell) (a ρ lam : ℝ) (f : LocalFamily) (l : ℝ)
    (V : F.GaugeField F.top) (law : StepLaw) (ζ : StepVariable (finiteCells F)) :
    rescaledLawExponent a ρ lam f l V law ζ =
      (∑ Y ∈ finiteCells F, (StepLaw.exponentWeight law * rescaledCellRemainder a ρ lam l Y V ζ -
          StepLaw.familyWeight law * rescaledCellExpansion a ρ f l Y V ζ)) +
        lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2 := by
  classical
  have hq : ∑ Y ∈ finiteCells F, (lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)),
      if enclosingCell b.1.1 = Y then ‖ζ b‖ ^ 2 else 0) =
      lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_ite_eq]
    simp [mem_finiteCells hfin]
  have hp : ∑ Y ∈ finiteCells F, rescaledCellTerm a ρ l Y V ζ =
      (∑ Y ∈ finiteCells F, rescaledCellRemainder a ρ lam l Y V ζ) +
      lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2 := by
    rw [← hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Y _ => ?_
    simp only [rescaledCellRemainder]
    ring
  have hr : ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion true a ρ 0 f y (l • ζ) V =
      ∑ Y ∈ finiteCells F, rescaledCellExpansion a ρ f l Y V ζ := by
    simp only [rescaledCellExpansion, cellCentredExpansion]
    rw [← Finset.sum_fiberwise_of_maps_to (s := sitesOfCells (finiteCells F) F.depth) (t := finiteCells F)
      (g := fun y => enclosingCell y) (fun y _ => mem_finiteCells hfin _)]
  cases law with
  | tilted ν =>
    simp only [rescaledLawExponent, rescaledExponent, StepLaw.exponentWeight, StepLaw.familyWeight,
      Finset.sum_sub_distrib, one_mul, ← Finset.mul_sum]
    rw [hp, hr]
    ring
  | interpolated τ =>
    simp only [rescaledLawExponent, rescaledExponent, StepLaw.exponentWeight, StepLaw.familyWeight,
      Finset.sum_sub_distrib, zero_mul, ← Finset.mul_sum]
    rw [hp]
    simp only [Finset.sum_const_zero, sub_zero]
    ring
theorem stepLawExponent_smul {T : StepParameters} {l₀ : ℝ} (hE : RescaledExponentsAgree T l₀) {t : ℕ}
    {V : F.GaugeField F.top} {f : LocalFamily} (law : StepLaw) {l : ℝ} (Y : F.Cell) {ζ : StepVariable (finiteCells F)}
    (hF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hl : 0 < l) (hl₀ : l ≤ l₀)
    (hζ : MemScaledBalls T.ballRadius l ζ) :
    stepLawExponent T.a T.ρA T.lam (l⁻¹ ^ 2) f V law (l • ζ) = rescaledLawExponent T.a T.ρA T.lam f l V law ζ := by
  cases law with
  | tilted ν => exact (hE t F V f ν l Y ζ hF hV hl hl₀ hζ).1
  | interpolated τ =>
    simp only [stepLawExponent, rescaledLawExponent]
    rw [(hE t F V f 0 l Y ζ hF hV hl hl₀ hζ).1]
    congr 2
    simp only [totalQuadratic, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e : ‖(l • ζ) b‖ ^ 2 = l ^ 2 * ‖ζ b‖ ^ 2 := by
      rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hl.le, mul_pow]
    rw [e]
    field_simp
theorem cutoff_mul_exp_smul {T : StepParameters} {l₀ : ℝ} (hE : RescaledExponentsAgree T l₀) {t : ℕ}
    {V : F.GaugeField F.top} {f : LocalFamily} (law : StepLaw) {l : ℝ} (Y : F.Cell) (ζ : StepVariable (finiteCells F))
    (hF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hl : 0 < l) (hl₀ : l ≤ l₀) :
    cutoffWeight T.ballRadius T.p (l • ζ) * Real.exp (-stepLawExponent T.a T.ρA T.lam (l⁻¹ ^ 2) f V law (l • ζ)) =
      scaledCutoff T.ballRadius T.p l ζ * Real.exp (-rescaledLawExponent T.a T.ρA T.lam f l V law ζ) := by
  have e : cutoffWeight T.ballRadius T.p (l • ζ) = scaledCutoff T.ballRadius T.p l ζ := rfl
  rw [e]
  by_cases hζ : MemScaledBalls T.ballRadius l ζ
  · rw [stepLawExponent_smul hE law Y hF hV hl hl₀ hζ]
  · have h1 : scaledCutoff T.ballRadius T.p l ζ = 0 := by
      simp only [MemScaledBalls, not_forall, not_lt] at hζ
      obtain ⟨b, hb⟩ := hζ
      refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
      have h2 : T.ballRadius ≤ ‖l • ζ b‖ := by
        rw [norm_smul, Real.norm_of_nonneg hl.le]
        exact hb
      simp [cutoffFactor, not_lt.mpr h2]
    simp [h1]
theorem integral_ratio_comp_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {l : ℝ} (hl : l ≠ 0) (f g : E → ℝ) :
    (∫ x, f (l • x) ∂μ) / (∫ x, g (l • x) ∂μ) = (∫ x, f x ∂μ) / ∫ x, g x ∂μ := by
  rw [Measure.integral_comp_smul, Measure.integral_comp_smul, smul_eq_mul, smul_eq_mul]
  have : |(l ^ Module.finrank ℝ E)⁻¹| ≠ 0 := by
    simp [hl]
  exact mul_div_mul_left _ _ this
theorem observableMean_eq_densityMean {T : StepParameters} {l₀ : ℝ} (hE : RescaledExponentsAgree T l₀) {t : ℕ}
    {V : F.GaugeField F.top} {f : LocalFamily} (law : StepLaw) {l : ℝ} (Y : F.Cell) (hF : IsCubicTopTorus T.L t T.n₀ F)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hl : 0 < l) (hl₀ : l ≤ l₀)
    (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) :
    observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l V =
      densityMean volume
        (fun ζ => scaledCutoff T.ballRadius T.p l ζ * Real.exp (-rescaledLawExponent T.a T.ρA T.lam f l V law ζ))
        fun ζ => Ob l ζ V := by
  unfold observableMean rescaledMean cutoffMean densityMean
  rw [← integral_ratio_comp_smul volume hl.ne']
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    show _ = _
    simp only []
    rw [cutoff_mul_exp_smul hE law Y ζ hF hV hl hl₀, inv_smul_smul₀ hl.ne']
  · refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    show _ = _
    simp only []
    rw [cutoff_mul_exp_smul hE law Y ζ hF hV hl hl₀]
def fullBondLaw (V : F.GaugeField F.top) (Ψ : StepVariable (finiteCells F) → ℝ) :
    LawOnBondVariables ↥(chordBonds (finiteCells F)) :=
  ⟨F, V, id, Finset.univ, Ψ⟩
theorem fullBondLaw_exponent (lam x : ℝ) (V : F.GaugeField F.top) (Ψ : StepVariable (finiteCells F) → ℝ) :
    (fullBondLaw V Ψ).exponent lam x = Ψ := by
  funext ζ
  have h : extendByZero (F := F) id Finset.univ ζ = ζ := by
    funext b
    simp [extendByZero]
  show Ψ (extendByZero id Finset.univ ζ) + ∑ i ∈ Finset.univ \ Finset.univ, _ = Ψ ζ
  rw [h]
  simp
theorem ballDensity_eq_zero_of_not_mem {ρ : ℝ} {p : ℝ → ℝ} {ι : Type} [Fintype ι] {Φ : BondField ι → ℝ}
    {η : BondField ι} (h : ¬ ∀ b, ‖η b‖ < ρ) : ballDensity (cutoffFactor ρ p) Φ η = 0 := by
  push Not at h
  obtain ⟨b, hb⟩ := h
  unfold ballDensity radialWeightProd
  rw [Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, not_lt.mpr hb]), zero_mul]
theorem ballDensity_congr {ρ : ℝ} {p : ℝ → ℝ} {ι : Type} [Fintype ι] {Ψ Φ : BondField ι → ℝ}
    (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → Ψ η = Φ η) :
    ballDensity (cutoffFactor ρ p) Ψ = ballDensity (cutoffFactor ρ p) Φ := by
  funext η
  by_cases hη : ∀ b, ‖η b‖ < ρ
  · unfold ballDensity
    rw [h η hη]
  · rw [ballDensity_eq_zero_of_not_mem hη, ballDensity_eq_zero_of_not_mem hη]
theorem exists_stepLawAtScale (hEnds : interpolationAtEndpoints) {T : StepParameters} {Cq Cz : ℕ → ℝ}
    {Cr : ℕ → ℕ → ℕ → ℝ} {t : ℕ} {l l₀ : ℝ} {f : LocalFamily} {V : F.GaugeField F.top} {law : StepLaw} (Y : F.Cell)
    (hfr : InterpolatedFrameBoundsAt T Cq Cz Cr t (l⁻¹ ^ 2))
    (hf : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f)
    (hF : IsCubicTopTorus T.L t T.n₀ F) (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hlaw : StepLaw.IsUnitWeight law)
    (hl : 0 < l) (hl₀ : l ≤ l₀) (hE : RescaledExponentsAgree T l₀) :
    ∃ (Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ)
      (K : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ), StepLawAtScale T Cq Cr l f V law Ψ K := by
  set x : ℝ := l⁻¹ ^ 2 with hx
  set m : ℕ := frameRadius x with hm
  set ι := ↥(chordBonds (finiteCells F)) with hι
  set d : ι → ι → ℝ := fun b b' => (cellSupDist (chordBondCell F b) (chordBondCell F b') : ℝ) with hd
  have hfam : ∀ η, familyLawExponent 0 T.a T.ρA x m f V η = stepExponent true T.a T.ρA x 0 f 1 V η := fun η => by
    have := (hEnds F true T.a T.ρA T.lam x 1 m V).2.2.2.2.2.1 f η
    simp only [segmentEnd, if_true] at this
    rw [this, stepExponent_frameRadius_indep]
  have hwei : ∀ τ η, weightLawExponent 0 T.a T.ρA T.lam x m τ V η =
      τ * stepExponent true T.a T.ρA x 0 f 0 V η + (1 - τ) * totalQuadratic T.lam x η := fun τ η => by
    have := (hEnds F true T.a T.ρA T.lam x τ m V).2.2.2.2.2.2 f η
    simp only [segmentEnd, if_true] at this
    rw [this, stepExponent_frameRadius_indep]
  have hadm : ∀ Ψ₀ : StepVariable (finiteCells F) → ℝ,
      IsIntermediateLaw T.a T.ρA T.lam x m (IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio) V Ψ₀ →
      (fullBondLaw V Ψ₀).IsAdmissible T.a T.chainParams.ρA T.chainParams.lam x T.σ T.decayRate T.E T.energyRatio
        T.L t T.n₀ m d := fun Ψ₀ h =>
    ⟨hF, hV, h, Function.injective_id, fun _ _ => rfl⟩
  obtain ⟨w₁, Ψ₁, Ψ₂, hw0, hw1, h₁, h₂, hmix⟩ : ∃ (w₁ : ℝ) (Ψ₁ Ψ₂ : StepVariable (finiteCells F) → ℝ), 0 ≤ w₁ ∧ w₁ ≤ 1 ∧
      IsIntermediateLaw T.a T.ρA T.lam x m (IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio) V Ψ₁ ∧
      IsIntermediateLaw T.a T.ρA T.lam x m (IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio) V Ψ₂ ∧
      ∀ η, w₁ * Ψ₁ η + (1 - w₁) * Ψ₂ η = stepLawExponent T.a T.ρA T.lam x f V law η := by
    cases law with
    | tilted ν =>
      refine ⟨ν, familyLawExponent 0 T.a T.ρA x m f V, weightLawExponent 0 T.a T.ρA T.lam x m 1 V, hlaw.1, hlaw.2,
        IsIntermediateLaw.ofFamily 0 f le_rfl zero_le_one hf,
        IsIntermediateLaw.ofWeight 0 1 le_rfl zero_le_one zero_le_one le_rfl, fun η => ?_⟩
      rw [hfam, hwei]
      simp only [stepLawExponent, stepExponent]
      ring
    | interpolated τ =>
      refine ⟨1, weightLawExponent 0 T.a T.ρA T.lam x m τ V, weightLawExponent 0 T.a T.ρA T.lam x m τ V, zero_le_one,
        le_rfl, IsIntermediateLaw.ofWeight 0 τ le_rfl zero_le_one hlaw.1 hlaw.2,
        IsIntermediateLaw.ofWeight 0 τ le_rfl zero_le_one hlaw.1 hlaw.2, fun η => ?_⟩
      rw [hwei]
      simp only [stepLawExponent]
      ring
  have hlaws := hfr.laws ι d 2 ![w₁, 1 - w₁] ![fullBondLaw V Ψ₁, fullBondLaw V Ψ₂]
    ⟨fun i => by
      fin_cases i
      · simpa using hw0
      · simpa using hw1, by simp⟩
    (fun i => by
      fin_cases i
      · exact hadm _ h₁
      · exact hadm _ h₂)
  set Φ : BondField ι → ℝ :=
    convexCombinationExponent T.chainParams.lam x ![w₁, 1 - w₁] ![fullBondLaw V Ψ₁, fullBondLaw V Ψ₂] with hΦ
  have hΦe : ∀ η, Φ η = stepLawExponent T.a T.ρA T.lam x f V law η := fun η => by
    rw [← hmix η]
    have e : Φ η = w₁ * (fullBondLaw V Ψ₁).exponent T.chainParams.lam x η +
        (1 - w₁) * (fullBondLaw V Ψ₂).exponent T.chainParams.lam x η := by
      simp [hΦ, convexCombinationExponent, Fin.sum_univ_two]
    rw [e, fullBondLaw_exponent, fullBondLaw_exponent]
  obtain ⟨⟨Ψ, K, hag, hconv, hsl, -⟩, hmom, -⟩ := hlaws
  have hdens : ballDensity (cutoffFactor T.ballRadius T.p) Ψ = ballDensity (cutoffFactor T.ballRadius T.p) Φ :=
    ballDensity_congr hag
  have hmean : ∀ g : BondField ι → ℝ,
      ballExpectation (cutoffFactor T.ballRadius T.p) Ψ g = ballExpectation (cutoffFactor T.ballRadius T.p) Φ g :=
    fun g => by
      simp only [ballExpectation, hdens]
  refine ⟨Ψ, K, hconv, hsl, fun q b => ?_, fun j q N b hj hq => ?_, fun ζ => ?_⟩
  · rw [hmean]
    exact hmom.moments q b
  · rw [hmean, hdens]
    exact hmom.cutoff_deriv_moments j q N b hj hq
  · rw [hdens]
    have h1 := cutoff_mul_exp_smul hE (f := f) law Y ζ hF hV hl hl₀
    rw [← h1, ← hx]
    unfold ballDensity
    rw [hΦe]
    rfl
theorem stepLawAtScale_holds (hEnds : interpolationAtEndpoints) : stepLawAtScaleStatement :=
  ⟨fun _ hfin a ρ lam f l V law ζ => rescaledLawExponent_eq_sum hfin a ρ lam f l V law ζ,
    fun _ _ hE _ _ _ _ law _ Y hF hV hl hl₀ Ob => observableMean_eq_densityMean hE law Y hF hV hl hl₀ Ob,
    fun _ _ _ _ _ _ _ _ _ _ _ Y hfr hf hF hV hlaw hl hl₀ hE => exists_stepLawAtScale hEnds Y hfr hf hF hV hlaw hl hl₀ hE⟩
end YangMills.Construction.ScaledVariables
end
