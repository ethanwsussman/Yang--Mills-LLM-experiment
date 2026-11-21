import YangMills.Construction.SummableBoundsOfTheFlow.BondsAtACell
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOverASetOfIndices
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongTheScaleAndATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.PartsOfAnExponentHaveTheirSizesProof
import YangMills.Construction.SummableBoundsOfTheFlow.SizesOfObservablesOfTheWeightForm
import YangMills.Construction.SummableBoundsOfTheFlow.SizesOfTheDerivativesOfTheCut
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensityOfTheStepHasItsLowOrdersProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheLawOfTheStepAtAScaleProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansHaveTheirBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ScaledMeanBounds
open Set Filter Topology MeasureTheory BlockAverages ColdStepAtMirrorFrames ScaledVariables ScaleDerivatives Cumulants
  Interpolation DensityMeans CellCounting
def scaleTopLinear (i k : ℕ) : (Fin (i + k) → ℝ) →L[ℝ] ℝ × (Fin k → ℝ) :=
  ContinuousLinearMap.prod
    (∑ a : Fin i, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (i + k) => ℝ) (Fin.castAdd k a))
    (ContinuousLinearMap.pi fun b => ContinuousLinearMap.proj (Fin.natAdd i b))
theorem scaleTopLinear_apply (i k : ℕ) (τ : Fin (i + k) → ℝ) : scaleTopLinear i k τ = scaleTopSplit i k τ := by
  simp [scaleTopLinear, scaleTopSplit]
variable {F : BlockFrame} {i k : ℕ}
theorem exponentWeight_mem_Icc {law : StepLaw} (h : StepLaw.IsUnitWeight law) :
    0 ≤ StepLaw.exponentWeight law ∧ StepLaw.exponentWeight law ≤ 1 := by
  cases law with
  | tilted ν => simp [StepLaw.exponentWeight]
  | interpolated τ => exact h
theorem familyWeight_mem_Icc {law : StepLaw} (h : StepLaw.IsUnitWeight law) :
    0 ≤ StepLaw.familyWeight law ∧ StepLaw.familyWeight law ≤ 1 := by
  cases law with
  | tilted ν => exact h
  | interpolated τ => simp [StepLaw.familyWeight]
theorem finite_cell (h : ∀ i, 1 ≤ F.extent i) : Finite F.Cell := by
  have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
    simp only [BlockFrame.period, Nat.sub_self, pow_zero, mul_one]
    have := h i
    omega⟩
  have : ∀ i, Finite (ZMod (F.period F.top i)) := fun i => by
    have := hne i
    exact inferInstance
  exact Pi.finite
theorem mem_finiteCells (h : Finite F.Cell) (Y : F.Cell) : Y ∈ finiteCells F := by apply _root_.YangMills.SharedProofs.p8277 <;> assumption
theorem integral_ratio_comp_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {l : ℝ} (hl : l ≠ 0) (f g : E → ℝ) :
    (∫ x, f (l • x) ∂μ) / (∫ x, g (l • x) ∂μ) = (∫ x, f x ∂μ) / ∫ x, g x ∂μ := by apply _root_.YangMills.Construction.ScaledVariables.integral_ratio_comp_smul <;> assumption
theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem cellSupDist_self (x : F.Cell) : cellSupDist x x = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem cellSupDist_triangle (x y z : F.Cell) : cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem cellSupDist_le_bondSpan (Y : F.Cell) {r : ℕ} (c : Fin r → F.Site F.top × Fin 4) (u : Fin r) :
    cellSupDist Y (c u).1 ≤ bondSpan Y c :=
  le_trans (Finset.le_sup (f := fun l : Fin r => siteSupDist Y (c l).1) (Finset.mem_univ u)) (le_max_left _ _)
theorem cellSupDist_pair_le_bondSpan (Y : F.Cell) {r : ℕ} (c : Fin r → F.Site F.top × Fin 4) (u v : Fin r) :
    cellSupDist (c u).1 (c v).1 ≤ bondSpan Y c := by apply _root_.YangMills.Construction.Interpolation.PartsSizes.cellSupDist_pair_le_bondSpan <;> assumption
theorem bondSpan_le_cons (Y : F.Cell) {r : ℕ} (x : F.Site F.top × Fin 4) (c : Fin r → F.Site F.top × Fin 4) :
    bondSpan Y c ≤ bondSpan Y (Fin.cons x c : Fin (r + 1) → F.Site F.top × Fin 4) ∧
      cellSupDist Y x.1 ≤ bondSpan Y (Fin.cons x c : Fin (r + 1) → F.Site F.top × Fin 4) := by
  constructor
  · refine max_le (Finset.sup_le fun l _ => ?_) (Finset.sup_le fun l _ => Finset.sup_le fun l' _ => ?_)
    · have := cellSupDist_le_bondSpan Y (Fin.cons x c : Fin (r + 1) → F.Site F.top × Fin 4) l.succ
      simp only [Fin.cons_succ] at this
      exact this
    · have := cellSupDist_pair_le_bondSpan Y (Fin.cons x c : Fin (r + 1) → F.Site F.top × Fin 4) l.succ l'.succ
      simp only [Fin.cons_succ] at this
      exact this
  · have := cellSupDist_le_bondSpan Y (Fin.cons x c : Fin (r + 1) → F.Site F.top × Fin 4) 0
    simp only [Fin.cons_zero] at this
    exact this
theorem smoothObservable_component_bounds (hY : derivAlongParameterListStatement) {κ ρ l₁ K : ℝ} {Y : F.Cell}
    {V : F.GaugeField F.top} {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} (hκ : 0 < κ)
    (hs : IsSmoothObservable κ ρ l₁ K Y V Ob)
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} (hX : AreUnitVectors X) (I : Finset (Fin (i + k)))
    (hread : IsControlledOrder (I.card - scaleCount I) (scaleCount I)) (hK : 0 ≤ K) {l : ℝ} (hl : 0 < l) (hl₁ : l ≤ l₁)
    (hreg : ∀ ζ : StepVariable (finiteCells F), (∀ b, l * ‖ζ b‖ < ρ) →
      ContDiffAt ℝ (6 : ℕ) (observableAlongList Ob V c X) ((l, ζ), 0))
    (hI : I.card ≤ 5) (a : ℝ) (ha : |a| ≤ 1) :
    ContDiffOn ℝ 1 (fun ζ => a * mixedDerivAt (shiftedAlongScale i l (observableAlongList Ob V c X)) I ζ)
        {ζ : StepVariable (finiteCells F) | ∀ b, l * ‖ζ b‖ < ρ} ∧
      (∀ ζ : StepVariable (finiteCells F), (∀ b, l * ‖ζ b‖ < ρ) →
        |a * mixedDerivAt (shiftedAlongScale i l (observableAlongList Ob V c X)) I ζ| ≤
          K * Real.exp (-(14 * κ * bondSpan Y (c ∘ topIndices I))) *
            (1 + weightedL1Norm κ (chordBondCell F) Y ζ) ^ 7) ∧
      ∀ (ζ : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
        (∀ b, l * ‖ζ b‖ < ρ) → ‖e‖ = 1 →
        |bondPartialDeriv (fun ζ => a * mixedDerivAt (shiftedAlongScale i l (observableAlongList Ob V c X)) I ζ) b ζ e| ≤
          K * Real.exp (-(14 * κ * bondSpan Y (c ∘ topIndices I))) *
            Real.exp (-(2 * κ * cellSupDist (chordBondCell F b) Y)) *
            (1 + weightedL1Norm κ (chordBondCell F) Y ζ) ^ 7 := by
  set D : StepVariable (finiteCells F) → ℝ := mixedDerivAt (shiftedAlongScale i l (observableAlongList Ob V c X)) I with hD
  set SD : StepVariable (finiteCells F) → ℝ :=
    fun ζ => scaleDeriv Ob V (c ∘ topIndices I) (X ∘ topIndices I) (scaleCount I) ζ l with hSD
  set U : Set (StepVariable (finiteCells F)) := {ζ | ∀ b, l * ‖ζ b‖ < ρ} with hU
  have hUo : IsOpen U := by
    have : U = ⋂ b, {ζ | l * ‖ζ b‖ < ρ} := by
      ext ζ
      simp [hU]
    rw [this]
    refine isOpen_iInter_of_finite fun b => isOpen_lt ?_ continuous_const
    exact continuous_const.mul (continuous_norm.comp (continuous_apply b))
  have hDC : ∀ ζ ∈ U, ContDiffAt ℝ 1 D ζ := fun ζ hζ => hY.2.1 F i k _ l ζ 6 (hreg ζ hζ) I (by omega)
  have hDS : ∀ ζ ∈ U, D ζ = SD ζ := fun ζ hζ => hY.1 F i k Ob V c X l ζ 6 (hreg ζ hζ) I (by omega)
  have hXt : AreUnitVectors (X ∘ topIndices I) := fun u => hX _
  have hscaled : ∀ ζ ∈ U, MemScaledBalls ρ l ζ := fun ζ hζ => hζ
  have hnear : ∀ ζ, localWeight κ Y ζ = weightedL1Norm κ (chordBondCell F) Y ζ := fun _ => rfl
  have hwn : ∀ ζ : StepVariable (finiteCells F), 0 ≤ weightedL1Norm κ (chordBondCell F) Y ζ := fun ζ =>
    Finset.sum_nonneg fun b _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  refine ⟨fun ζ hζ => (contDiffAt_const.mul (hDC ζ hζ)).contDiffWithinAt, fun ζ hζ => ?_, fun ζ b e hζ he => ?_⟩
  · show |a * D ζ| ≤ _
    rw [hDS ζ hζ, abs_mul]
    have h1 := hs.deriv_le _ _ (c ∘ topIndices I) (X ∘ topIndices I) l ζ hread hXt hl hl₁ (hscaled ζ hζ)
    rw [hnear] at h1
    have hspan : (0 : ℝ) ≤ bondSpan Y (c ∘ topIndices I) := by positivity
    have h2 : Real.exp (-(2 ^ 4 * κ * bondSpan Y (c ∘ topIndices I))) ≤
        Real.exp (-(14 * κ * bondSpan Y (c ∘ topIndices I))) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [mul_nonneg hκ.le hspan]
    have hp : 0 ≤ K * (1 + weightedL1Norm κ (chordBondCell F) Y ζ) ^ 7 := by
      have := hwn ζ
      positivity
    calc |a| * |SD ζ| ≤ 1 * |SD ζ| := by gcongr
      _ = |SD ζ| := one_mul _
      _ ≤ K * (1 + weightedL1Norm κ (chordBondCell F) Y ζ) ^ 7 *
            Real.exp (-(2 ^ 4 * κ * bondSpan Y (c ∘ topIndices I))) := h1
      _ ≤ K * (1 + weightedL1Norm κ (chordBondCell F) Y ζ) ^ 7 *
            Real.exp (-(14 * κ * bondSpan Y (c ∘ topIndices I))) :=
        mul_le_mul_of_nonneg_left h2 hp
      _ = _ := by ring
  · have hdiff : DifferentiableAt ℝ D ζ := (hDC ζ hζ).differentiableAt (by norm_num)
    have e1 : bondPartialDeriv (fun ζ => a * D ζ) b ζ e = a * bondPartialDeriv SD b ζ e := by
      have hev : D =ᶠ[𝓝 ζ] SD := by
        filter_upwards [hUo.mem_nhds hζ] with z hz using hDS z hz
      unfold bondPartialDeriv
      rw [fderiv_const_mul hdiff, hev.fderiv_eq]
      simp
    rw [e1, abs_mul]
    have h1 := hs.partialDeriv_le _ _ (c ∘ topIndices I) (X ∘ topIndices I) l ζ b e hread hXt hl hl₁ (hscaled ζ hζ) he
    rw [hnear] at h1
    obtain ⟨hc1, hc2⟩ := bondSpan_le_cons Y (enclosingCell b.1.1, (0 : Fin 4)) (c ∘ topIndices I)
    set S' : ℕ := bondSpan Y (Fin.cons (enclosingCell b.1.1, (0 : Fin 4)) (c ∘ topIndices I) :
      Fin (I.card - scaleCount I + 1) → F.Site F.top × Fin 4) with hS'
    have hc3 : cellSupDist (chordBondCell F b) Y ≤ S' := by
      rw [cellSupDist_comm]
      exact hc2
    have hc1' : (bondSpan Y (c ∘ topIndices I) : ℝ) ≤ S' := by exact_mod_cast hc1
    have hc3' : (cellSupDist (chordBondCell F b) Y : ℝ) ≤ S' := by exact_mod_cast hc3
    have h2 : Real.exp (-(2 ^ 4 * κ * S')) ≤ Real.exp (-(14 * κ * bondSpan Y (c ∘ topIndices I))) *
        Real.exp (-(2 * κ * cellSupDist (chordBondCell F b) Y)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [mul_le_mul_of_nonneg_left hc1' hκ.le, mul_le_mul_of_nonneg_left hc3' hκ.le]
    have hp : 0 ≤ K * (1 + weightedL1Norm κ (chordBondCell F) Y ζ) ^ 7 := by
      have := hwn ζ
      positivity
    calc |a| * |bondPartialDeriv SD b ζ e| ≤ 1 * |bondPartialDeriv SD b ζ e| := by gcongr
      _ = |bondPartialDeriv SD b ζ e| := one_mul _
      _ ≤ K * (1 + weightedL1Norm κ (chordBondCell F) Y ζ) ^ 7 * Real.exp (-(2 ^ 4 * κ * S')) := h1
      _ ≤ K * (1 + weightedL1Norm κ (chordBondCell F) Y ζ) ^ 7 *
            (Real.exp (-(14 * κ * bondSpan Y (c ∘ topIndices I))) *
            Real.exp (-(2 * κ * cellSupDist (chordBondCell F b) Y))) := mul_le_mul_of_nonneg_left h2 hp
      _ = _ := by ring
section LocalSizes
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ x κ : ℝ} {r : ℝ → ℝ} {Ψ : BondField ι → ℝ}
theorem momentBound_mono {H : BondField ι → ℝ} {q : ℕ} {B B' : ℝ} (h : MomentBound r Ψ H q B) (h0 : 0 ≤ B)
    (hB : B ≤ B') : MomentBound r Ψ H q B' :=
  ⟨h.1, h.2.trans (pow_le_pow_left₀ h0 hB q)⟩
theorem hasLocalSize_mono {Cs Cs' : ℕ → ℝ} {h h' : ℝ} {dZ : ι → ℝ} {H : BondField ι → ℝ}
    (hs : HasLocalSize ρ r Ψ Cs x κ h dZ H) (hC : ∀ q, Cs q ≤ Cs' q) (hC0 : ∀ q, 0 ≤ Cs q) (hh : h ≤ h')
    (h0 : 0 ≤ h) : HasLocalSize ρ r Ψ Cs' x κ h' dZ H := by
  obtain ⟨hd, H₀, hm⟩ := hs
  refine ⟨hd, H₀, fun q hq => ⟨momentBound_mono (hm q hq).1 (mul_nonneg (hC0 q) h0) ?_, fun b => ?_⟩⟩
  · exact mul_le_mul (hC q) hh h0 ((hC0 q).trans (hC q))
  · refine momentBound_mono ((hm q hq).2 b) (by have := hC0 q; positivity) ?_
    have h1 : 0 ≤ Cs' q := (hC0 q).trans (hC q)
    have h2 : Cs q * Real.sqrt x * h ≤ Cs' q * Real.sqrt x * h' :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hC q) (Real.sqrt_nonneg _)) hh h0 (by positivity)
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
theorem hasLocalSize_neg {Cs : ℕ → ℝ} {h : ℝ} {dZ : ι → ℝ} {H : BondField ι → ℝ}
    (hs : HasLocalSize ρ r Ψ Cs x κ h dZ H) : HasLocalSize ρ r Ψ Cs x κ h dZ fun η => -H η := by
  obtain ⟨hd, H₀, hm⟩ := hs
  have hp : ∀ b, bondGradNorm (fun η => -H η) b = bondGradNorm H b := fun b => by
    funext η
    unfold bondGradNorm
    rw [fderiv_fun_neg]
    have : (-fderiv ℝ H η).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b) =
        -((fderiv ℝ H η).comp (ContinuousLinearMap.single ℝ (fun _ : ι => BondVector) b)) := by
      ext1 v
      simp
    rw [this, norm_neg]
  refine ⟨fun η h1 => (hd η h1).neg, -H₀, fun q hq => ⟨?_, fun b => ?_⟩⟩
  · have e : ∀ η, |(-H η - -H₀)| ^ q = |H η - H₀| ^ q := fun η => by
      rw [show -H η - -H₀ = -(H η - H₀) by ring, abs_neg]
    have := (hm q hq).1
    unfold MomentBound at this ⊢
    simpa only [e] using this
  · rw [hp]
    exact (hm q hq).2 b
theorem hasLocalSize_zero {Cs : ℕ → ℝ} {h : ℝ} {dZ : ι → ℝ} (hC : ∀ q, 0 ≤ Cs q) (hx : 0 ≤ x) (h0 : 0 ≤ h) :
    HasLocalSize ρ r Ψ Cs x κ h dZ fun _ => 0 := by
  refine ⟨fun η _ => differentiableAt_const _, 0, fun q hq => ⟨?_, fun b => ?_⟩⟩
  · have hq0 : q ≠ 0 := by omega
    refine ⟨by simp [hq0], ?_⟩
    have : ballExpectation r Ψ (fun η : BondField ι => |(0 : ℝ) - 0| ^ q) = 0 := by
      simp [ballExpectation, hq0]
    rw [this]
    have := hC q
    positivity
  · have hq0 : q ≠ 0 := by omega
    have hz : bondGradNorm (fun _ : BondField ι => (0 : ℝ)) b = fun _ => 0 := by
      funext η
      simp [bondGradNorm]
    rw [hz]
    refine ⟨by simp [hq0], ?_⟩
    have : ballExpectation r Ψ (fun η : BondField ι => |(0 : ℝ)| ^ q) = 0 := by
      simp [ballExpectation, hq0]
    rw [this]
    have := hC q
    positivity
end LocalSizes
def exponentAlongList (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (f : LocalFamily) (V : F.GaugeField F.top) (law : StepLaw)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (q : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)) : ℝ :=
  rescaledLawExponent T.a T.ρA T.lam f q.1.1 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.2) V) law q.1.2
def remainderObservable (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (Y : F.Cell) :
    ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ
def expansionObservable (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (f : LocalFamily) (Y : F.Cell) :
    ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ
theorem exponentAlongList_eq (hLaw : stepLawAtScaleStatement) (hfin : Finite F.Cell) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters)
    (f : LocalFamily) (V : F.GaugeField F.top) (law : StepLaw)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (q : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)) :
    exponentAlongList T f V law c X q =
      (∑ Y ∈ finiteCells F, (StepLaw.exponentWeight law * observableAlongList (remainderObservable T Y) V c X q -
        StepLaw.familyWeight law * observableAlongList (expansionObservable T f Y) V c X q)) +
        T.lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖q.1.2 b‖ ^ 2 := by
  unfold exponentAlongList
  rw [hLaw.1 F hfin]
  rfl
theorem mixedDerivAt_exponentAlongList (hLaw : stepLawAtScaleStatement) (hfin : Finite F.Cell) {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters}
    {f : LocalFamily} {V : F.GaugeField F.top} {law : StepLaw}
    {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {l : ℝ} {ζ : StepVariable (finiteCells F)}
    (J : Finset (Fin (i + k))) (hJ : J.Nonempty)
    (hB : ∀ Y, ContDiffAt ℝ J.card (observableAlongList (remainderObservable T Y) V c X) ((l, ζ), 0))
    (hR : ∀ Y, ContDiffAt ℝ J.card (observableAlongList (expansionObservable T f Y) V c X) ((l, ζ), 0)) :
    mixedDerivAt (shiftedAlongScale i l (exponentAlongList T f V law c X)) J ζ =
      ∑ Y ∈ finiteCells F, (StepLaw.exponentWeight law *
          mixedDerivAt (shiftedAlongScale i l (observableAlongList (remainderObservable T Y) V c X)) J ζ -
        StepLaw.familyWeight law *
          mixedDerivAt (shiftedAlongScale i l (observableAlongList (expansionObservable T f Y) V c X)) J ζ) := by
  have hslice : ∀ {g : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) → ℝ}, ContDiffAt ℝ J.card g ((l, ζ), 0) →
      ContDiffAt ℝ J.card (fun τ => shiftedAlongScale i l g τ ζ) 0 := by
    intro g hg
    have hm : ContDiff ℝ J.card (fun τ : Fin (i + k) → ℝ =>
        (((l + (scaleTopLinear i k τ).1, ζ), (scaleTopLinear i k τ).2) :
          (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ))) := by
      have h1 : ContDiff ℝ J.card (scaleTopLinear i k) := (scaleTopLinear i k).contDiff
      exact ((contDiff_const.add h1.fst).prodMk contDiff_const).prodMk h1.snd
    have h2 : ContDiffAt ℝ J.card (g ∘ fun τ : Fin (i + k) → ℝ =>
        (((l + (scaleTopLinear i k τ).1, ζ), (scaleTopLinear i k τ).2) :
          (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ))) 0 := by
      refine ContDiffAt.comp (0 : Fin (i + k) → ℝ) ?_ hm.contDiffAt
      simpa using hg
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
    simp only [shiftedAlongScale, Function.comp, scaleTopLinear_apply]
  unfold mixedDerivAt
  set v : Fin J.card → Fin (i + k) → ℝ := fun j => Pi.single (J.orderEmbOfFin rfl j) 1 with hv
  have hcard : J.card ≠ 0 := (Finset.card_pos.mpr hJ).ne'
  have e : (fun τ => shiftedAlongScale i l (exponentAlongList T f V law c X) τ ζ) = fun τ =>
      (∑ Y ∈ finiteCells F, (StepLaw.exponentWeight law •
          shiftedAlongScale i l (observableAlongList (remainderObservable T Y) V c X) τ ζ -
        StepLaw.familyWeight law • shiftedAlongScale i l (observableAlongList (expansionObservable T f Y) V c X) τ ζ)) +
        T.lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2 := by
    funext τ
    simp only [shiftedAlongScale, smul_eq_mul]
    exact exponentAlongList_eq hLaw hfin T f V law c X _
  rw [e]
  have hterm : ∀ Y ∈ finiteCells F, ContDiffAt ℝ J.card (fun τ => StepLaw.exponentWeight law •
      shiftedAlongScale i l (observableAlongList (remainderObservable T Y) V c X) τ ζ -
      StepLaw.familyWeight law • shiftedAlongScale i l (observableAlongList (expansionObservable T f Y) V c X) τ ζ) 0 :=
    fun Y _ => ((hslice (hB Y)).const_smul _).sub ((hslice (hR Y)).const_smul _)
  have h1 := fun_iteratedFDeriv_add_apply (𝕜 := ℝ) (x := (0 : Fin (i + k) → ℝ)) (ContDiffAt.sum hterm)
    (contDiffAt_const (c := T.lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖ζ b‖ ^ 2))
  rw [h1, iteratedFDeriv_fun_sum_apply hterm, iteratedFDeriv_const_of_ne hcard, Pi.zero_apply, add_zero, sum_apply]
  refine Finset.sum_congr rfl fun Y hY => ?_
  have h2 := fun_iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := (0 : Fin (i + k) → ℝ))
    ((hslice (hB Y)).const_smul (StepLaw.exponentWeight law))
    ((hslice (hR Y)).const_smul (StepLaw.familyWeight law))
  rw [h2]
  have h3 := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := StepLaw.exponentWeight law) (hslice (hB Y))
  have h4 := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := StepLaw.familyWeight law) (hslice (hR Y))
  rw [h3, h4]
  simp
abbrev EntryPlace (F : BlockFrame) : Type :=
  Unit ⊕ (↥(finiteCells F) ⊕ (↥(finiteCells F) ⊕ ↥(chordBonds (finiteCells F))))
def entryPlaceCell (Y : F.Cell) : EntryPlace F → F.Cell
  | .inl _ => Y
  | .inr (.inl Y') => Y'.1
  | .inr (.inr (.inl Y')) => Y'.1
  | .inr (.inr (.inr b)) => chordBondCell F b
def entryPlaceMem : Option (Finset (Fin (i + k))) → EntryPlace F → Prop
  | none, .inl _ => True
  | some _, .inr _ => True
  | _, _ => False
def blockIndices (I : Finset (Fin (i + k))) : Option (Finset (Fin (i + k))) → Finset (Fin (i + k))
  | none => I
  | some J => J
def entryPlaceSpan (Y : F.Cell) (c : Fin k → F.Site F.top × Fin 4) (I : Finset (Fin (i + k)))
    (o : Option (Finset (Fin (i + k)))) (q : EntryPlace F) : ℝ :=
  (bondSpan (entryPlaceCell Y q) (c ∘ topIndices (blockIndices I o)) : ℝ)
def entryPlaceObservable (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (f : LocalFamily) (law : StepLaw)
    (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (V : F.GaugeField F.top) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (l : ℝ)
    (I : Finset (Fin (i + k))) :
    Option (Finset (Fin (i + k))) → EntryPlace F → BondField ↥(chordBonds (finiteCells F)) → ℝ
  | none, .inl _ => fun η => 1 * mixedDerivAt (shiftedAlongScale i l (observableAlongList Ob V c X)) I (l⁻¹ • η)
  | some J, .inr (.inl Y') => fun η =>
      (-StepLaw.exponentWeight law) *
        mixedDerivAt (shiftedAlongScale i l (observableAlongList (remainderObservable T Y'.1) V c X)) J (l⁻¹ • η)
  | some J, .inr (.inr (.inl Y')) => fun η =>
      StepLaw.familyWeight law *
        mixedDerivAt (shiftedAlongScale i l (observableAlongList (expansionObservable T f Y'.1) V c X)) J (l⁻¹ • η)
  | some J, .inr (.inr (.inr b)) => fun η => -cutoffDerivAlong i k T.p l J b (l⁻¹ • η)
  | _, _ => fun _ => 0
theorem jointCumulant_congr {Ω α : Type} [DecidableEq α] {m m' : (Ω → ℝ) → ℝ} {S : Finset α} {f f' : α → Ω → ℝ}
    (h : ∀ J : Finset α, J ⊆ S → m (blockProd f J) = m' (blockProd f' J)) :
    jointCumulant m S f = jointCumulant m' S f' := by
  unfold jointCumulant
  refine Finset.sum_congr rfl fun π _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun J hJ => h J (π.le hJ)
theorem ballExpectation_congr {ι : Type} [Fintype ι] {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ}
    {g g' : BondField ι → ℝ} (h : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → g η = g' η) :
    ballExpectation (cutoffFactor ρ p) Ψ g = ballExpectation (cutoffFactor ρ p) Ψ g' := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.ballExpectation_congr <;> assumption
theorem bondSpan_cast_le {Y : F.Cell} {r : ℕ} {c : Fin r → F.Site F.top × Fin 4} {R : ℝ} (hR : 0 ≤ R)
    (h1 : ∀ u, (siteSupDist Y (c u).1 : ℝ) ≤ R) (h2 : ∀ u v, (siteSupDist (c u).1 (c v).1 : ℝ) ≤ R) :
    (bondSpan Y c : ℝ) ≤ R := by
  have h3 : bondSpan Y c ≤ ⌊R⌋₊ := by
    refine max_le (Finset.sup_le fun u _ => Nat.le_floor (h1 u))
      (Finset.sup_le fun u _ => Finset.sup_le fun v _ => Nat.le_floor (h2 u v))
  exact (Nat.cast_le.mpr h3).trans (Nat.floor_le hR)
theorem bondSpan_le_blocks (hLs : derivAlongParameterListStatement) {Y : F.Cell} {c : Fin k → F.Site F.top × Fin 4}
    {I : Finset (Fin (i + k))} {π : Finpartition ((Finset.univ : Finset (Fin (i + k))) \ I)}
    (s : Option (Finset (Fin (i + k))) → EntryPlace F) (D : ℕ)
    (hs : ∀ o ∈ insert none (π.parts.image some), entryPlaceMem o (s o))
    (hD : ∀ o ∈ insert none (π.parts.image some), ∀ o' ∈ insert none (π.parts.image some),
      cellSupDist (entryPlaceCell Y (s o)) (entryPlaceCell Y (s o')) ≤ D) :
    (bondSpan Y c : ℝ) ≤ D + ∑ o ∈ insert none (π.parts.image some), entryPlaceSpan Y c I o (s o) := by
  classical
  set S : Finset (Option (Finset (Fin (i + k)))) := insert none (π.parts.image some) with hS
  have hnone : none ∈ S := Finset.mem_insert_self _ _
  have hen : ∀ o q, 0 ≤ entryPlaceSpan (i := i) Y c I o q := fun o q => by
    unfold entryPlaceSpan
    positivity
  have hsum0 : 0 ≤ ∑ o ∈ S, entryPlaceSpan Y c I o (s o) := Finset.sum_nonneg fun o _ => hen _ _
  have hY : entryPlaceCell Y (s none) = Y := by
    have h := hs none hnone
    cases hq : s none with
    | inl u => rfl
    | inr q => rw [hq] at h; exact absurd h (by simp [entryPlaceMem])
  have hblock : ∀ l : Fin k, ∃ o ∈ S, ∃ u, topIndices (blockIndices I o) u = l := by
    intro l
    by_cases hl : Fin.natAdd i l ∈ I
    · exact ⟨none, hnone, hLs.2.2.2.2 i k I l hl⟩
    · have h1 : Fin.natAdd i l ∈ (Finset.univ : Finset (Fin (i + k))) \ I := by simp [hl]
      obtain ⟨J, hJ, hlJ⟩ := π.exists_mem h1
      exact ⟨some J, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hJ), hLs.2.2.2.2 i k J l hlJ⟩
  have hnear : ∀ l : Fin k, ∃ o ∈ S,
      (cellSupDist (entryPlaceCell Y (s o)) (c l).1 : ℝ) ≤ entryPlaceSpan Y c I o (s o) := by
    intro l
    obtain ⟨o, ho, u, hu⟩ := hblock l
    refine ⟨o, ho, ?_⟩
    have h1 := cellSupDist_le_bondSpan (entryPlaceCell Y (s o)) (c ∘ topIndices (blockIndices I o)) u
    simp only [Function.comp, hu] at h1
    unfold entryPlaceSpan
    exact_mod_cast h1
  have hD' : ∀ o ∈ S, ∀ o' ∈ S, (cellSupDist (entryPlaceCell Y (s o)) (entryPlaceCell Y (s o')) : ℝ) ≤ D :=
    fun o ho o' ho' => by
      exact_mod_cast hD o ho o' ho'
  have hone : ∀ o ∈ S, entryPlaceSpan Y c I o (s o) ≤ ∑ o ∈ S, entryPlaceSpan Y c I o (s o) := fun o ho =>
    Finset.single_le_sum (f := fun o => entryPlaceSpan Y c I o (s o)) (fun o _ => hen _ _) ho
  refine bondSpan_cast_le (by positivity) (fun u => ?_) fun u v => ?_
  · obtain ⟨o, ho, h1⟩ := hnear u
    have h2 : cellSupDist Y (c u).1 ≤ cellSupDist Y (entryPlaceCell Y (s o)) +
        cellSupDist (entryPlaceCell Y (s o)) (c u).1 :=
      cellSupDist_triangle _ _ _
    have h3 : (cellSupDist Y (c u).1 : ℝ) ≤ cellSupDist Y (entryPlaceCell Y (s o)) +
        cellSupDist (entryPlaceCell Y (s o)) (c u).1 := by
      exact_mod_cast h2
    have h4 := hD' none hnone o ho
    rw [hY] at h4
    have h5 := hone o ho
    show (cellSupDist Y (c u).1 : ℝ) ≤ _
    linarith
  · obtain ⟨o, ho, u', hu⟩ := hblock u
    obtain ⟨o', ho', v', hv⟩ := hblock v
    by_cases hoo : o = o'
    · subst hoo
      have h1 := cellSupDist_pair_le_bondSpan (entryPlaceCell Y (s o)) (c ∘ topIndices (blockIndices I o)) u' v'
      simp only [Function.comp, hu, hv] at h1
      have h2 : (cellSupDist (c u).1 (c v).1 : ℝ) ≤ entryPlaceSpan Y c I o (s o) := by
        unfold entryPlaceSpan
        exact_mod_cast h1
      have h5 := hone o ho
      show (cellSupDist (c u).1 (c v).1 : ℝ) ≤ _
      have : (0 : ℝ) ≤ D := by positivity
      linarith
    · have h1 := cellSupDist_le_bondSpan (entryPlaceCell Y (s o)) (c ∘ topIndices (blockIndices I o)) u'
      have h2 := cellSupDist_le_bondSpan (entryPlaceCell Y (s o')) (c ∘ topIndices (blockIndices I o')) v'
      simp only [Function.comp, hu, hv] at h1 h2
      have h1' : (cellSupDist (entryPlaceCell Y (s o)) (c u).1 : ℝ) ≤ entryPlaceSpan Y c I o (s o) := by
        unfold entryPlaceSpan
        exact_mod_cast h1
      have h2' : (cellSupDist (entryPlaceCell Y (s o')) (c v).1 : ℝ) ≤ entryPlaceSpan Y c I o' (s o') := by
        unfold entryPlaceSpan
        exact_mod_cast h2
      have h3 : cellSupDist (c u).1 (c v).1 ≤ cellSupDist (c u).1 (entryPlaceCell Y (s o)) +
          (cellSupDist (entryPlaceCell Y (s o)) (entryPlaceCell Y (s o')) +
            cellSupDist (entryPlaceCell Y (s o')) (c v).1) :=
        (cellSupDist_triangle _ _ _).trans (Nat.add_le_add_left (cellSupDist_triangle _ _ _) _)
      rw [cellSupDist_comm (c u).1 (entryPlaceCell Y (s o))] at h3
      have h3' : (cellSupDist (c u).1 (c v).1 : ℝ) ≤ cellSupDist (entryPlaceCell Y (s o)) (c u).1 +
          (cellSupDist (entryPlaceCell Y (s o)) (entryPlaceCell Y (s o')) +
            cellSupDist (entryPlaceCell Y (s o')) (c v).1) := by
        exact_mod_cast h3
      have h4 := hD' o ho o' ho'
      have h5 : entryPlaceSpan Y c I o (s o) + entryPlaceSpan Y c I o' (s o') ≤
          ∑ o ∈ S, entryPlaceSpan Y c I o (s o) := by
        have hsub : ({o, o'} : Finset _) ⊆ S := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact ho
          · exact ho'
        have h6 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun o => entryPlaceSpan Y c I o (s o)) hsub
          (fun o _ _ => hen _ _)
        rwa [Finset.sum_pair hoo] at h6
      show (cellSupDist (c u).1 (c v).1 : ℝ) ≤ _
      linarith
def WeightedSizeBound (κ : ℝ) (Cq Cs : ℕ → ℝ) (W : ℝ) : Prop :=
  ∀ (F : BlockFrame) (ι : Type) [Fintype ι] [DecidableEq ι] (y : ι → F.Cell) (ρ l A : ℝ) (p : ℝ → ℝ)
      (Ψ : BondField ι → ℝ) (Y : F.Cell) (H : BondField ι → ℝ),
      0 < ρ → 0 < l → 0 ≤ A → IsCutoff ρ p → Continuous Ψ →
      (∑ b, Real.exp (-(2 ^ 4 * κ * cellSupDist (y b) Y)) ≤ W) →
      (∀ (q : ℕ) (b : ι), ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b‖ ^ (2 * q)) ≤
        Cq q * ((l⁻¹ ^ 2) ^ q)⁻¹) →
      ContDiffOn ℝ 1 H {ζ | ∀ b, l * ‖ζ b‖ < ρ} →
      (∀ ζ : BondField ι, (∀ b, l * ‖ζ b‖ < ρ) → |H ζ| ≤ A * (1 + weightedL1Norm κ y Y ζ) ^ 7) →
      (∀ (ζ : BondField ι) (b : ι) (e : BondVector), (∀ b, l * ‖ζ b‖ < ρ) → ‖e‖ = 1 →
        |bondPartialDeriv H b ζ e| ≤
          A * Real.exp (-(2 * κ * cellSupDist (y b) Y)) * (1 + weightedL1Norm κ y Y ζ) ^ 7) →
      (∀ q : ℕ, 1 ≤ q → MomentBound (cutoffFactor ρ p) Ψ (fun η => H (l⁻¹ • η)) q (Cs q * A)) ∧
        HasLocalSize ρ (cutoffFactor ρ p) Ψ Cs (l⁻¹ ^ 2) κ A (fun b => (cellSupDist (y b) Y : ℝ))
          fun η => H (l⁻¹ • η)
def CutoffDerivSizeBound (ρ : ℝ) (p : ℝ → ℝ) (Cr : ℕ → ℕ → ℕ → ℝ) (j : ℕ) (Cs : ℕ → ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b₀ : ι) (l κ : ℝ) (Ψ : BondField ι → ℝ) (dZ : ι → ℝ),
    0 < l → l ≤ 1 → Continuous Ψ → dZ b₀ = 0 →
    (∀ (j q N : ℕ) (b : ι), 1 ≤ j → 1 ≤ q →
      Integrable (fun η => |iteratedDeriv j p ‖η b‖| ^ q * ballDensity (cutoffFactor ρ p) Ψ η) ∧
      ballExpectation (cutoffFactor ρ p) Ψ (fun η => |iteratedDeriv j p ‖η b‖| ^ q) ≤
        Cr j q N * ((l⁻¹ ^ 2) ^ N)⁻¹) →
    ContDiffOn ℝ 1 (fun η : BondField ι => ‖(l⁻¹ • η) b₀‖ ^ j * iteratedDeriv j p (l * ‖(l⁻¹ • η) b₀‖))
      {η | ∀ b, ‖η b‖ < ρ} ∧
    (∀ q : ℕ, 1 ≤ q → MomentBound (cutoffFactor ρ p) Ψ
      (fun η => ‖(l⁻¹ • η) b₀‖ ^ j * iteratedDeriv j p (l * ‖(l⁻¹ • η) b₀‖)) q (Cs q * 1)) ∧
    HasLocalSize ρ (cutoffFactor ρ p) Ψ Cs (l⁻¹ ^ 2) κ 1 dZ
      fun η => ‖(l⁻¹ • η) b₀‖ ^ j * iteratedDeriv j p (l * ‖(l⁻¹ • η) b₀‖)
structure CumulantTermHyps (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (f : LocalFamily) (V : F.GaugeField F.top) (law : StepLaw)
    (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (Y : F.Cell) (K K₀ l l₁ : ℝ)
    (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (Cq : ℕ → ℝ) (Cr : ℕ → ℕ → ℕ → ℝ)
    (Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ)
    (Km : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ) : Prop where
  fin : Finite F.Cell
  κpos : 0 < T.κ
  ρpos : 0 < T.ballRadius
  cut : IsCutoff T.ballRadius T.p
  lists : derivAlongParameterListStatement
  lawEq : stepLawAtScaleStatement
  lampos : 0 < T.lam
  lpos : 0 < l
  lone : l ≤ 1
  llt : l < l₁
  weight : StepLaw.IsUnitWeight law
  units : AreUnitVectors X
  Kn : 0 ≤ K
  K₀n : 0 ≤ K₀
  ob : IsSmoothObservable T.κ T.ballRadius l₁ K Y V Ob
  birth : ∀ Y' : F.Cell, IsSmoothObservable T.κ T.ballRadius l₁ K₀ Y' V (remainderObservable T Y')
  row : ∀ Y' : F.Cell, IsSmoothObservable T.κ T.ballRadius l₁ K₀ Y' V (expansionObservable T f Y')
  law : StepLawAtScale T Cq Cr l f V law Ψ Km
theorem controlledOrder_block (hY : derivAlongParameterListStatement) {J : Finset (Fin (i + k))}
    (h : IsControlledOrder k i) : IsControlledOrder (J.card - scaleCount J) (scaleCount J) := by
  have h1 := (hY.2.2.1 i k J).1
  have h2 := (hY.2.2.1 i k J).2
  rcases h with h | h
  · exact Or.inl ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩
theorem card_le_five_of_controlledOrder {J : Finset (Fin (i + k))} (h : IsControlledOrder k i) : J.card ≤ 5 := by
  have h1 : J.card ≤ i + k := by simpa using J.card_le_univ
  rcases h with h | h <;> omega
section
variable {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {f : LocalFamily} {V : F.GaugeField F.top} {law : StepLaw}
  {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {Y : F.Cell} {K K₀ l l₁ : ℝ}
  {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {Cq : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
  {Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ}
  {Km : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ}
theorem entry_hasLocalSize (D : CumulantTermHyps T f V law Ob Y K K₀ l l₁ c X Cq Cr Ψ Km) {Cs : ℕ → ℝ} {W : ℝ}
    (hP : WeightedSizeBound T.κ (fun q => |Cq q|) Cs W)
    (hW : ∀ Y' : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(2 ^ 4 * T.κ * cellSupDist (chordBondCell F b) Y')) ≤ W)
    {Y' : F.Cell} {K' : ℝ} {Ob' : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    (hs : IsSmoothObservable T.κ T.ballRadius l₁ K' Y' V Ob') (hK' : 0 ≤ K') (a : ℝ)
    (ha : |a| ≤ 1) (J : Finset (Fin (i + k))) (hread : IsControlledOrder k i) :
    ContDiffOn ℝ 1 (fun η => a * mixedDerivAt (shiftedAlongScale i l (observableAlongList Ob' V c X)) J (l⁻¹ • η))
        {η : BondField ↥(chordBonds (finiteCells F)) | ∀ b, ‖η b‖ < T.ballRadius} ∧
      (∀ q : ℕ, 1 ≤ q → MomentBound (cutoffFactor T.ballRadius T.p) Ψ
        (fun η => a * mixedDerivAt (shiftedAlongScale i l (observableAlongList Ob' V c X)) J (l⁻¹ • η)) q
        (Cs q * (K' * Real.exp (-(14 * T.κ * bondSpan Y' (c ∘ topIndices J)))))) ∧
      HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) Ψ Cs (l⁻¹ ^ 2) T.κ
        (K' * Real.exp (-(14 * T.κ * bondSpan Y' (c ∘ topIndices J))))
        (fun b => (cellSupDist (chordBondCell F b) Y' : ℝ))
        (fun η => a * mixedDerivAt (shiftedAlongScale i l (observableAlongList Ob' V c X)) J (l⁻¹ • η)) := by
  have hl := D.lpos
  have hlinv : 0 < l⁻¹ := by positivity
  obtain ⟨hC, hb, hsl⟩ := smoothObservable_component_bounds D.lists D.κpos hs D.units J (controlledOrder_block D.lists hread)
    hK' hl D.llt.le
    (fun ζ hζ => hs.contDiffAt l ζ k c X fun b => by rw [abs_of_pos hl]; exact hζ b)
    (card_le_five_of_controlledOrder hread) a ha
  have hmom : ∀ (q : ℕ) (b : ↥(chordBonds (finiteCells F))),
      ballExpectation (cutoffFactor T.ballRadius T.p) Ψ (fun η => ‖η b‖ ^ (2 * q)) ≤
        |Cq q| * ((l⁻¹ ^ 2) ^ q)⁻¹ := fun q b =>
    (D.law.moments q b).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  obtain ⟨h1, h2⟩ := hP F ↥(chordBonds (finiteCells F)) (chordBondCell F) T.ballRadius l _ T.p Ψ Y' _ D.ρpos hl
    (mul_nonneg hK' (Real.exp_pos _).le) D.cut D.law.convex.smooth.continuous (hW Y') hmom hC hb
    (fun ζ b e hζ he => hsl ζ b e hζ he)
  refine ⟨?_, h1, h2⟩
  refine hC.comp (contDiff_id.const_smul l⁻¹).contDiffOn fun η hη b => ?_
  show l * ‖(l⁻¹ • η) b‖ < T.ballRadius
  rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hlinv.le, ← mul_assoc, mul_inv_cancel₀ hl.ne', one_mul]
  exact hη b
end
def blockAmplitude (K A₀ : ℝ) : Option (Finset (Fin (i + k))) → ℝ
  | none => K
  | some _ => A₀
theorem bondSpan_of_eq_zero {r : ℕ} (hr : r = 0) (y : F.Cell) (c : Fin r → F.Site F.top × Fin 4) :
    bondSpan y c = 0 := by
  subst hr
  simp [bondSpan]
section
variable {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {f : LocalFamily} {V : F.GaugeField F.top} {law : StepLaw}
  {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {Y : F.Cell} {K K₀ l l₁ : ℝ}
  {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {Cq : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
  {Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ}
  {Km : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ}
theorem entryPlace_properties (D : CumulantTermHyps T f V law Ob Y K K₀ l l₁ c X Cq Cr Ψ Km) {Cs : ℕ → ℝ} {W : ℝ}
    (hP : WeightedSizeBound T.κ (fun q => |Cq q|) Cs W)
    (hW : ∀ Y' : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(2 ^ 4 * T.κ * cellSupDist (chordBondCell F b) Y')) ≤ W)
    {CsCut : ℕ → ℕ → ℝ}
    (hCut : ∀ j, CutoffDerivSizeBound T.ballRadius T.p (fun j q N => |Cr j q N|) (j + 1) (CsCut j))
    (hCs0 : ∀ q, 0 ≤ Cs q) (hCut0 : ∀ j q, 0 ≤ CsCut j q) {Cq₀ : ℕ → ℝ} (hq1 : ∀ q, Cs q ≤ Cq₀ q)
    (hq2 : ∀ j, j < 5 → ∀ q, CsCut j q ≤ Cq₀ q) (hread : IsControlledOrder k i) (I : Finset (Fin (i + k)))
    (o : Option (Finset (Fin (i + k)))) (hne : ∀ J, o = some J → J.Nonempty) (q : EntryPlace F)
    (hq : entryPlaceMem o q) :
    ContDiffOn ℝ 1 (entryPlaceObservable T f law Ob V c X l I o q) {η | ∀ b, ‖η b‖ < T.ballRadius} ∧
      (∀ m : ℕ, 1 ≤ m → Integrable fun η => |entryPlaceObservable T f law Ob V c X l I o q η| ^ m *
        ballDensity (cutoffFactor T.ballRadius T.p) Ψ η) ∧
      HasLocalSize T.ballRadius (cutoffFactor T.ballRadius T.p) Ψ Cq₀ (l⁻¹ ^ 2) T.κ
        (blockAmplitude K (K₀ + 1) o * Real.exp (-(14 * T.κ * entryPlaceSpan Y c I o q)))
        (fun b => (cellSupDist (chordBondCell F b) (entryPlaceCell Y q) : ℝ))
        (entryPlaceObservable T f law Ob V c X l I o q) := by
  have hK₀1 : 0 ≤ K₀ + 1 := by linarith [D.K₀n]
  have hx0 : (0 : ℝ) ≤ l⁻¹ ^ 2 := by positivity
  have hw := exponentWeight_mem_Icc D.weight
  have hn := familyWeight_mem_Icc D.weight
  cases o with
  | none =>
    cases q with
    | inl u =>
      obtain ⟨h1, h2, h3⟩ := entry_hasLocalSize D hP hW D.ob D.Kn 1 (by simp) I hread
      exact ⟨h1, fun m hm => (h2 m hm).1, hasLocalSize_mono h3 hq1 hCs0 le_rfl (mul_nonneg D.Kn (Real.exp_pos _).le)⟩
    | inr w => exact absurd hq (by simp [entryPlaceMem])
  | some J =>
    cases q with
    | inl u => exact absurd hq (by simp [entryPlaceMem])
    | inr w =>
      cases w with
      | inl Y' =>
        obtain ⟨h1, h2, h3⟩ := entry_hasLocalSize D hP hW (D.birth Y'.1) D.K₀n (-StepLaw.exponentWeight law)
          (by rw [abs_neg, abs_of_nonneg hw.1]; exact hw.2) J hread
        exact ⟨h1, fun m hm => (h2 m hm).1, hasLocalSize_mono h3 hq1 hCs0
          (mul_le_mul_of_nonneg_right (by show K₀ ≤ K₀ + 1; linarith) (Real.exp_pos _).le)
          (mul_nonneg D.K₀n (Real.exp_pos _).le)⟩
      | inr w =>
        cases w with
        | inl Y' =>
          obtain ⟨h1, h2, h3⟩ := entry_hasLocalSize D hP hW (D.row Y'.1) D.K₀n (StepLaw.familyWeight law)
            (by rw [abs_of_nonneg hn.1]; exact hn.2) J hread
          exact ⟨h1, fun m hm => (h2 m hm).1, hasLocalSize_mono h3 hq1 hCs0
            (mul_le_mul_of_nonneg_right (by show K₀ ≤ K₀ + 1; linarith) (Real.exp_pos _).le)
            (mul_nonneg D.K₀n (Real.exp_pos _).le)⟩
        | inr b =>
          by_cases hall : ∀ a ∈ J, (a : ℕ) < i
          · have hJ1 : 1 ≤ J.card := Finset.card_pos.mpr (hne J rfl)
            have hJ5 : J.card ≤ 5 := card_le_five_of_controlledOrder hread
            have hcl : CutoffDerivSizeBound T.ballRadius T.p (fun j q N => |Cr j q N|) J.card (CsCut (J.card - 1)) := by
              have := hCut (J.card - 1)
              rwa [Nat.sub_add_cancel hJ1] at this
            obtain ⟨h1, h2, h3⟩ := hcl ↥(chordBonds (finiteCells F)) b l T.κ Ψ
              (fun b' => (cellSupDist (chordBondCell F b')
                (entryPlaceCell Y (Sum.inr (Sum.inr (Sum.inr b)))) : ℝ)) D.lpos D.lone
              D.law.convex.smooth.continuous (by simp [entryPlaceCell, cellSupDist_self])
              (fun j q N b' hj hq' => ⟨(D.law.cutoff_deriv_moments j q N b' hj hq').1,
                (D.law.cutoff_deriv_moments j q N b' hj hq').2.trans
                (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))⟩)
            set H : BondField ↥(chordBonds (finiteCells F)) → ℝ := fun η =>
              ‖(l⁻¹ • η) b‖ ^ J.card * iteratedDeriv J.card T.p (l * ‖(l⁻¹ • η) b‖) with hH
            have e : entryPlaceObservable T f law Ob V c X l I (some J) (Sum.inr (Sum.inr (Sum.inr b))) =
                fun η => -H η := by
              funext η
              simp only [entryPlaceObservable, cutoffDerivAlong]
              rw [if_pos hall]
            rw [e]
            refine ⟨h1.neg, fun m hm => ?_, ?_⟩
            · have := (h2 m hm).1
              simpa only [sub_zero, abs_neg] using this
            · have hsp : entryPlaceSpan Y c I (some J) (Sum.inr (Sum.inr (Sum.inr b))) = 0 := by
                unfold entryPlaceSpan
                rw [bondSpan_of_eq_zero (by simp only [blockIndices]; rw [D.lists.2.2.2.1 i k J hall]; omega)]
                simp
              rw [hsp]
              refine hasLocalSize_mono (hasLocalSize_neg h3) (hq2 _ (by omega)) (hCut0 _) ?_ zero_le_one
              show (1 : ℝ) ≤ (K₀ + 1) * Real.exp (-(14 * T.κ * 0))
              simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
              linarith [D.K₀n]
          · have e : entryPlaceObservable T f law Ob V c X l I (some J) (Sum.inr (Sum.inr (Sum.inr b))) =
                fun _ => 0 := by
              funext η
              simp only [entryPlaceObservable, cutoffDerivAlong]
              rw [if_neg hall, neg_zero]
            rw [e]
            refine ⟨contDiffOn_const, fun m hm => ?_, ?_⟩
            · have hm0 : m ≠ 0 := by omega
              simp [hm0]
            · refine hasLocalSize_zero (fun q => (hCs0 q).trans (hq1 q)) hx0 ?_
              exact mul_nonneg hK₀1 (Real.exp_pos _).le
end
theorem jointCumulant_singleton {Ω α : Type} [DecidableEq α] (m : (Ω → ℝ) → ℝ) (a : α) (f : α → Ω → ℝ) :
    jointCumulant m {a} f = m (f a) := by
  unfold jointCumulant
  have hu : ∀ π : Finpartition ({a} : Finset α), π.parts = {{a}} := by
    intro π
    ext J
    simp only [Finset.mem_singleton]
    constructor
    · intro hJ
      have h1 : J ⊆ {a} := π.le hJ
      rcases Finset.subset_singleton_iff.mp h1 with h | h
      · exact absurd h (π.nonempty_of_mem_parts hJ).ne_empty
      · exact h
    · rintro rfl
      obtain ⟨t, ht, hat⟩ := π.exists_mem (Finset.mem_singleton_self a)
      have h1 : t ⊆ {a} := π.le ht
      have h2 : t = {a} := by
        rcases Finset.subset_singleton_iff.mp h1 with h | h
        · rw [h] at hat
          simp at hat
        · exact h
      rwa [h2] at ht
  have hsub : Subsingleton (Finpartition ({a} : Finset α)) :=
    ⟨fun π π' => Finpartition.ext ((hu π).trans (hu π').symm)⟩
  rw [Fintype.sum_subsingleton _ (Finpartition.indiscrete (Finset.singleton_ne_empty a)), hu]
  simp only [Finset.card_singleton, cumulantWeight, Finset.prod_singleton]
  have e : blockProd f {a} = f a := by
    funext ω
    simp [blockProd]
  rw [e]
  simp
section
variable {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {f : LocalFamily} {V : F.GaugeField F.top} {law : StepLaw}
  {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {Y : F.Cell} {K K₀ l l₁ : ℝ}
  {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {Cq : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
  {Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ}
  {Km : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ}
theorem densityMean_eq_ballExpectation (D : CumulantTermHyps T f V law Ob Y K K₀ l l₁ c X Cq Cr Ψ Km)
    (H : StepVariable (finiteCells F) → ℝ) :
    densityMean volume (scaledDensity T.ballRadius T.p (exponentAlongList T f V law c X) (l, 0)) H =
      ballExpectation (cutoffFactor T.ballRadius T.p) Ψ fun η => H (l⁻¹ • η) := by
  have hl := D.lpos
  have hd : ∀ ζ, scaledDensity T.ballRadius T.p (exponentAlongList T f V law c X) (l, 0) ζ =
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ (l • ζ) := fun ζ => by
    rw [D.law.density_eq]
    simp only [scaledDensity, exponentAlongList]
    rw [FrameCurves.leftTranslate_bondSpread_zero]
  unfold densityMean ballExpectation
  rw [← integral_ratio_comp_smul volume hl.ne'
    (fun η => H (l⁻¹ • η) * ballDensity (cutoffFactor T.ballRadius T.p) Ψ η)
    (ballDensity (cutoffFactor T.ballRadius T.p) Ψ)]
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    simp only [hd, inv_smul_smul₀ hl.ne']
  · refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    exact hd ζ
open Classical in
theorem sum_positionObservable (D : CumulantTermHyps T f V law Ob Y K K₀ l l₁ c X Cq Cr Ψ Km)
    (I : Finset (Fin (i + k)))
    (o : Option (Finset (Fin (i + k)))) (hne : ∀ J, o = some J → J.Nonempty) (hread : IsControlledOrder k i)
    (η : BondField ↥(chordBonds (finiteCells F))) (hη : ∀ b, ‖η b‖ < T.ballRadius) :
    ∑ q ∈ Finset.univ.filter (entryPlaceMem o), entryPlaceObservable T f law Ob V c X l I o q η =
      scaleCumulantEntries i T.p l (exponentAlongList T f V law c X) (observableAlongList Ob V c X) I o (l⁻¹ • η) := by
  have hl := D.lpos
  have hlinv : 0 < l⁻¹ := by positivity
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  cases o with
  | none =>
    simp [entryPlaceMem, entryPlaceObservable, scaleCumulantEntries]
  | some J =>
    have hJ := hne J rfl
    have hζ : MemScaledBalls T.ballRadius |l| (l⁻¹ • η) := fun b => by
      rw [abs_of_pos hl, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hlinv.le, ← mul_assoc,
        mul_inv_cancel₀ hl.ne', one_mul]
      exact hη b
    have hcard : (J.card : ℕ) ≤ 6 := (card_le_five_of_controlledOrder hread).trans (by norm_num)
    have hE := mixedDerivAt_exponentAlongList (T := T) (f := f) (V := V) (law := law) (c := c) (X := X) (l := l)
      (ζ := l⁻¹ • η) D.lawEq D.fin J hJ
      (fun Y' => ((D.birth Y').contDiffAt l _ k c X hζ).of_le (by exact_mod_cast hcard))
      (fun Y' => ((D.row Y').contDiffAt l _ k c X hζ).of_le (by exact_mod_cast hcard))
    have t1 : ∀ a₁ : Unit, (if entryPlaceMem (some J) (Sum.inl a₁ : EntryPlace F) then
        entryPlaceObservable T f law Ob V c X l I (some J) (Sum.inl a₁) η else 0) = 0 :=
      fun a₁ => if_neg (by simp [entryPlaceMem])
    have t2 : ∀ w, (if entryPlaceMem (some J) (Sum.inr w : EntryPlace F) then
        entryPlaceObservable T f law Ob V c X l I (some J) (Sum.inr w) η else 0) =
        entryPlaceObservable T f law Ob V c X l I (some J) (Sum.inr w) η := fun w => if_pos (by simp [entryPlaceMem])
    rw [Finset.sum_congr rfl fun a₁ _ => t1 a₁, Finset.sum_congr rfl fun w _ => t2 w]
    simp only [Finset.sum_const_zero, zero_add, Fintype.sum_sum_type, entryPlaceObservable, scaleCumulantEntries]
    rw [hE, Finset.sum_coe_sort (finiteCells F) (fun Y' => -StepLaw.exponentWeight law *
        mixedDerivAt (shiftedAlongScale i l (observableAlongList (remainderObservable T Y') V c X)) J (l⁻¹ • η)),
      Finset.sum_coe_sort (finiteCells F) (fun Y' => StepLaw.familyWeight law *
        mixedDerivAt (shiftedAlongScale i l (observableAlongList (expansionObservable T f Y') V c X)) J (l⁻¹ • η)),
      Finset.sum_sub_distrib]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring
end
theorem ballDensity_nonneg {ι : Type} [Fintype ι] (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) (η : BondField ι) :
    0 ≤ ballDensity (cutoffFactor ρ p) Ψ η := by apply _root_.YangMills.Construction.ConvexMeasures.LocalCovariance.ballDensity_nonneg <;> assumption
theorem abs_ballExpectation_le {ι : Type} [Fintype ι] (ρ : ℝ) (p : ℝ → ℝ) (Ψ H : BondField ι → ℝ)
    (hI : Integrable fun η => |H η| ^ 1 * ballDensity (cutoffFactor ρ p) Ψ η) :
    |ballExpectation (cutoffFactor ρ p) Ψ H| ≤ ballExpectation (cutoffFactor ρ p) Ψ fun η => |H η| ^ 1 := by
  unfold ballExpectation
  have hb : 0 ≤ ∫ η, ballDensity (cutoffFactor ρ p) Ψ η := integral_nonneg fun η => ballDensity_nonneg ρ p Ψ η
  rw [abs_div, abs_of_nonneg hb]
  refine div_le_div_of_nonneg_right ?_ hb
  refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [abs_mul, abs_of_nonneg (ballDensity_nonneg ρ p Ψ η), pow_one]
section
variable {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {f : LocalFamily} {V : F.GaugeField F.top} {law : StepLaw}
  {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {Y : F.Cell} {K K₀ l l₁ : ℝ}
  {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {Cq : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
  {Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ}
  {Km : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ}
theorem integrable_ballDensity (D : CumulantTermHyps T f V law Ob Y K K₀ l l₁ c X Cq Cr Ψ Km) {Cs : ℕ → ℝ} {W : ℝ}
    (hP : WeightedSizeBound T.κ (fun q => |Cq q|) Cs W)
    (hW : ∀ Y' : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(2 ^ 4 * T.κ * cellSupDist (chordBondCell F b) Y')) ≤ W) :
    Integrable (ballDensity (cutoffFactor T.ballRadius T.p) Ψ) := by
  have hmom : ∀ (q : ℕ) (b : ↥(chordBonds (finiteCells F))),
      ballExpectation (cutoffFactor T.ballRadius T.p) Ψ (fun η => ‖η b‖ ^ (2 * q)) ≤
        |Cq q| * ((l⁻¹ ^ 2) ^ q)⁻¹ := fun q b =>
    (D.law.moments q b).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hwn : ∀ ζ : BondField ↥(chordBonds (finiteCells F)), 0 ≤ weightedL1Norm T.κ (chordBondCell F) Y ζ := fun ζ =>
    Finset.sum_nonneg fun b _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  obtain ⟨h1, -⟩ := hP F ↥(chordBonds (finiteCells F)) (chordBondCell F) T.ballRadius l 1 T.p Ψ Y (fun _ => 1)
    D.ρpos D.lpos zero_le_one D.cut
    D.law.convex.smooth.continuous (hW Y) hmom contDiffOn_const
    (fun ζ _ => by
      have := hwn ζ
      simp only [abs_one, one_mul]
      exact one_le_pow₀ (by linarith))
    (fun ζ b e _ _ => by
      have := hwn ζ
      have h0 : bondPartialDeriv (fun _ : BondField ↥(chordBonds (finiteCells F)) => (1 : ℝ)) b ζ e = 0 := by
        simp [bondPartialDeriv]
      rw [h0, abs_zero]
      positivity)
  have := (h1 1 le_rfl).1
  simpa using this
open Classical in
theorem abs_jointCumulant_term_le (D : CumulantTermHyps T f V law Ob Y K K₀ l l₁ c X Cq Cr Ψ Km) {Cs : ℕ → ℝ}
    {W : ℝ} (hP : WeightedSizeBound T.κ (fun q => |Cq q|) Cs W)
    (hW : ∀ Y' : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(2 ^ 4 * T.κ * cellSupDist (chordBondCell F b) Y')) ≤ W)
    {CsCut : ℕ → ℕ → ℝ}
    (hCut : ∀ j, CutoffDerivSizeBound T.ballRadius T.p (fun j q N => |Cr j q N|) (j + 1) (CsCut j))
    (hCs0 : ∀ q, 0 ≤ Cs q) (hCut0 : ∀ j q, 0 ≤ CsCut j q) {Cq₀ : ℕ → ℝ} (hq1 : ∀ q, Cs q ≤ Cq₀ q)
    (hq2 : ∀ j, j < 5 → ∀ q, CsCut j q ≤ Cq₀ q) (hCq₀ : ∀ q, 0 ≤ Cq₀ q) (hread : IsControlledOrder k i) {N : ℕ}
    (hy : ∀ z, (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => chordBondCell F b = z).card ≤ N)
    {B : ℕ → (ℕ → ℝ) → ℝ} (hB : SetIndexedCumulantBound N (N + 3) T.κ T.lam B)
    (hB0 : ∀ M, 2 ≤ M → M ≤ 9 → 0 ≤ B M Cq₀) (I : Finset (Fin (i + k)))
    (π : Finpartition ((Finset.univ : Finset (Fin (i + k))) \ I)) :
    |jointCumulant (densityMean volume (scaledDensity T.ballRadius T.p (exponentAlongList T f V law c X) (l, 0)))
        (insert none (π.parts.image some))
        (scaleCumulantEntries i T.p l (exponentAlongList T f V law c X) (observableAlongList Ob V c X) I)| ≤
      ((∑ M ∈ Finset.Icc 2 9, B M Cq₀) * (K₀ + 1) ^ 5 + Cs 1) * K * Real.exp (-(T.κ / 16 * bondSpan Y c)) := by
  set S : Finset (Option (Finset (Fin (i + k)))) := insert none (π.parts.image some) with hS
  have hκ := D.κpos
  have hK := D.Kn
  have hK₀ := D.K₀n
  have hneS : ∀ o ∈ S, ∀ J, o = some J → J.Nonempty := by
    intro o ho J hJ
    subst hJ
    rcases Finset.mem_insert.mp ho with h | h
    · exact absurd h (by simp)
    · obtain ⟨J', hJ', he⟩ := Finset.mem_image.mp h
      have : J' = J := Option.some_injective _ he
      rw [← this]
      exact π.nonempty_of_mem_parts hJ'
  have hcum : jointCumulant (densityMean volume
        (scaledDensity T.ballRadius T.p (exponentAlongList T f V law c X) (l, 0))) S
      (scaleCumulantEntries i T.p l (exponentAlongList T f V law c X) (observableAlongList Ob V c X) I) =
      jointCumulant (ballExpectation (cutoffFactor T.ballRadius T.p) Ψ) S fun o η =>
        ∑ q ∈ Finset.univ.filter (entryPlaceMem o), entryPlaceObservable T f law Ob V c X l I o q η := by
    refine jointCumulant_congr fun J hJ => ?_
    rw [densityMean_eq_ballExpectation D]
    refine ballExpectation_congr fun η hη => ?_
    simp only [blockProd]
    exact Finset.prod_congr rfl fun o ho => (sum_positionObservable D I o (hneS o (hJ ho)) hread η hη).symm
  rw [hcum]
  set E : ℝ := Real.exp (-(T.κ / 16 * bondSpan Y c)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hCs1 : 0 ≤ Cs 1 * K * E := mul_nonneg (mul_nonneg (hCs0 1) hK) hE0
  have hsumB : 0 ≤ ∑ M ∈ Finset.Icc 2 9, B M Cq₀ := Finset.sum_nonneg fun M hM => by
    have := Finset.mem_Icc.mp hM
    exact hB0 M this.1 this.2
  have hA1 : 1 ≤ K₀ + 1 := by linarith
  by_cases hempty : π.parts = ∅
  · have hS1 : S = {none} := by
      simp [hS, hempty]
    rw [hS1, jointCumulant_singleton]
    obtain ⟨-, h2, -⟩ := entry_hasLocalSize D hP hW D.ob D.Kn 1 (by simp) I hread
    obtain ⟨hi, hm⟩ := h2 1 le_rfl
    have hsame : ballExpectation (cutoffFactor T.ballRadius T.p) Ψ (fun η =>
        ∑ q ∈ Finset.univ.filter (entryPlaceMem (none : Option (Finset (Fin (i + k))))),
          entryPlaceObservable T f law Ob V c X l I none q η) =
        ballExpectation (cutoffFactor T.ballRadius T.p) Ψ
          (fun η => 1 * mixedDerivAt (shiftedAlongScale i l (observableAlongList Ob V c X)) I (l⁻¹ • η)) := by
      refine ballExpectation_congr fun η hη => ?_
      rw [sum_positionObservable D I none (by simp) hread η hη]
      simp [scaleCumulantEntries]
    rw [hsame]
    have h3 := (abs_ballExpectation_le T.ballRadius T.p Ψ _ hi).trans hm
    rw [pow_one] at h3
    have hreach := bondSpan_le_blocks D.lists (Y := Y) (c := c) (I := I) (π := π) (fun _ => Sum.inl ()) 0
      (fun o ho => by
        rw [← hS, hS1] at ho
        obtain rfl := Finset.mem_singleton.mp ho
        simp [entryPlaceMem])
      (fun o ho o' ho' => by
        simp [entryPlaceCell, cellSupDist_self])
    rw [← hS, hS1, Finset.sum_singleton] at hreach
    set e₀ : ℝ := (bondSpan Y (c ∘ topIndices I) : ℝ) with he₀
    have he₀0 : 0 ≤ e₀ := by positivity
    have hn : (bondSpan Y c : ℝ) ≤ e₀ := by
      have : entryPlaceSpan Y c I none (Sum.inl () : EntryPlace F) = e₀ := rfl
      simpa [this] using hreach
    have h4 : Real.exp (-(14 * T.κ * e₀)) ≤ E := by
      refine Real.exp_le_exp.mpr ?_
      have h5 : (0 : ℝ) ≤ bondSpan Y c := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hn hκ.le, mul_nonneg hκ.le h5, mul_nonneg hκ.le he₀0]
    have h6 : Cs 1 * (K * Real.exp (-(14 * T.κ * e₀))) ≤ Cs 1 * K * E := by
      calc Cs 1 * (K * Real.exp (-(14 * T.κ * e₀))) ≤ Cs 1 * (K * E) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hK) (hCs0 1)
        _ = Cs 1 * K * E := by ring
    refine h3.trans (h6.trans ?_)
    have h7 : 0 ≤ (∑ M ∈ Finset.Icc 2 9, B M Cq₀) * (K₀ + 1) ^ 5 := by positivity
    have h8 : 0 ≤ K * E := by positivity
    nlinarith [mul_nonneg h7 h8]
  · have hnotin : none ∉ π.parts.image some := by simp
    have hcard : S.card = π.parts.card + 1 := by
      rw [hS, Finset.card_insert_of_notMem hnotin, Finset.card_image_of_injective _ (Option.some_injective _)]
    have hpos : 1 ≤ π.parts.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
    have hle : π.parts.card ≤ 5 := by
      have h1 := π.card_parts_le_card
      have h2 : ((Finset.univ : Finset (Fin (i + k))) \ I).card ≤ i + k :=
        (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
      rcases hread with h | h <;> omega
    have hnone : none ∈ S := Finset.mem_insert_self _ _
    have hfacts := fun o ho q hq =>
      entryPlace_properties (Y := Y) D hP hW hCut hCs0 hCut0 hq1 hq2 hread I o (hneS o ho) q hq
    have key := hB (Option (Finset (Fin (i + k)))) S none F ↥(chordBonds (finiteCells F)) (chordBondCell F)
      T.ballRadius (l⁻¹ ^ 2) T.p Ψ Km (EntryPlace F)
      (entryPlaceCell Y) entryPlaceMem (entryPlaceObservable T f law Ob V c X l I) (entryPlaceSpan Y c I)
      (blockAmplitude K (K₀ + 1)) Cq₀ (14 * T.κ) (bondSpan Y c) Y hnone
      (by omega) (by omega) D.ρpos (by have := D.lpos; positivity) D.cut hy D.law.convex D.law.firstDeriv_le
      (integrable_ballDensity D hP hW) hCq₀
      (fun o _ => by
        cases o with
        | none => exact hK
        | some J => show 0 ≤ K₀ + 1; linarith)
      (fun o _ q => by
        unfold entryPlaceSpan
        positivity)
      (by linarith)
      (fun o _ => by
        cases o with
        | none => exact ⟨Sum.inl (), by simp [entryPlaceMem]⟩
        | some J =>
          have hmem : Y ∈ finiteCells F := _root_.YangMills.Construction.ScaledMeanBounds.mem_finiteCells D.fin Y
          exact ⟨Sum.inr (Sum.inl ⟨Y, hmem⟩), by simp [entryPlaceMem]⟩)
      (fun u => by
        rw [Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
        have h1 : ∑ x : Unit, (if entryPlaceCell Y (Sum.inl x : EntryPlace F) = u then 1 else 0) ≤ 1 := by
          simp only [entryPlaceCell, Finset.univ_unique, Finset.sum_singleton]
          by_cases h : Y = u
          · simp [h]
          · simp [h]
        have h2 : ∀ g : ↥(finiteCells F) → EntryPlace F, (∀ a, entryPlaceCell Y (g a) = a.1) →
            ∑ x : ↥(finiteCells F), (if entryPlaceCell Y (g x) = u then 1 else 0) ≤ 1 := by
          intro g hg
          rw [← Finset.card_filter]
          refine Finset.card_le_one.mpr fun a ha b hb => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hg] at ha hb
          exact Subtype.ext (ha.trans hb.symm)
        have h3 : ∑ x : ↥(chordBonds (finiteCells F)),
            (if entryPlaceCell Y (Sum.inr (Sum.inr (Sum.inr x)) : EntryPlace F) = u then 1 else 0) ≤ N := by
          rw [← Finset.card_filter]
          exact hy u
        have h4 := h2 (fun a => Sum.inr (Sum.inl a)) fun _ => rfl
        have h5 := h2 (fun a => Sum.inr (Sum.inr (Sum.inl a))) fun _ => rfl
        omega)
      (fun q hq => by
        cases q with
        | inl u => rfl
        | inr w => exact absurd hq (by simp [entryPlaceMem]))
      (fun o ho q hq => (hfacts o ho q hq).1)
      (fun o ho q hq => (hfacts o ho q hq).2.1)
      (fun o ho q hq => (hfacts o ho q hq).2.2)
      (fun s Dn hs hD => bondSpan_le_blocks D.lists s Dn hs hD)
    refine key.trans ?_
    have hprod : ∏ o ∈ S, blockAmplitude K (K₀ + 1) o = K * (K₀ + 1) ^ π.parts.card := by
      rw [hS, Finset.prod_insert hnotin, Finset.prod_image fun a _ b _ h => Option.some_injective _ h]
      simp [blockAmplitude]
    rw [hprod]
    have hBM : B S.card Cq₀ ≤ ∑ M ∈ Finset.Icc 2 9, B M Cq₀ :=
      Finset.single_le_sum (f := fun M => B M Cq₀) (fun M hM => by
        have := Finset.mem_Icc.mp hM
        exact hB0 M this.1 this.2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hpow : (K₀ + 1) ^ π.parts.card ≤ (K₀ + 1) ^ 5 := pow_le_pow_right₀ hA1 hle
    have hb0 : 0 ≤ B S.card Cq₀ := hB0 _ (by omega) (by omega)
    calc B S.card Cq₀ * (K * (K₀ + 1) ^ π.parts.card) * E
        ≤ (∑ M ∈ Finset.Icc 2 9, B M Cq₀) * (K * (K₀ + 1) ^ 5) * E := by gcongr
      _ = ((∑ M ∈ Finset.Icc 2 9, B M Cq₀) * (K₀ + 1) ^ 5) * K * E := by ring
      _ ≤ _ := by
        have : 0 ≤ Cs 1 * (K * E) := by
          rw [← mul_assoc]
          exact hCs1
        nlinarith
end
def cumulantTermCount (n : ℕ) : ℕ :=
  ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset, Fintype.card (Finpartition ((Finset.univ : Finset (Fin n)) \ I))
section
variable {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {f : LocalFamily} {V : F.GaugeField F.top} {law : StepLaw}
  {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {Y : F.Cell} {K K₀ l l₁ : ℝ}
  {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {Cq : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
  {Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ}
  {Km : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ}
theorem scaledDensity_eq_ballDensity (D : CumulantTermHyps T f V law Ob Y K K₀ l l₁ c X Cq Cr Ψ Km)
    (ζ : StepVariable (finiteCells F)) :
    scaledDensity T.ballRadius T.p (exponentAlongList T f V law c X) (l, 0) ζ =
      ballDensity (cutoffFactor T.ballRadius T.p) Ψ (l • ζ) := by
  rw [D.law.density_eq]
  simp only [scaledDensity, exponentAlongList]
  rw [FrameCurves.leftTranslate_bondSpread_zero]
theorem integrable_cutoffDeriv_scaled (D : CumulantTermHyps T f V law Ob Y K K₀ l l₁ c X Cq Cr Ψ Km) (j q : ℕ)
    (b : ↥(chordBonds (finiteCells F))) (hj : 1 ≤ j)
    (hq : 1 ≤ q) : Integrable fun ζ : StepVariable (finiteCells F) => |iteratedDeriv j T.p (l * ‖ζ b‖)| ^ q *
      scaledDensity T.ballRadius T.p (exponentAlongList T f V law c X) (l, 0) ζ := by
  have hl := D.lpos
  have h1 := (D.law.cutoff_deriv_moments j q 0 b hj hq).1.comp_smul hl.ne'
  refine h1.congr (Eventually.of_forall fun ζ => ?_)
  have e : ‖(l • ζ) b‖ = l * ‖ζ b‖ := by
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hl.le]
  simp only [e, scaledDensity_eq_ballDensity D]
end
theorem densityMean_congr {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {Z H H' : Ω → ℝ}
    (h : ∀ ζ, Z ζ ≠ 0 → H ζ = H' ζ) :
    densityMean μ Z H = densityMean μ Z H' := by apply _root_.YangMills.Construction.ScaleDerivatives.densityMean_congr_of_ne_zero <;> assumption
theorem eventuallyEq_of_scaledBalls {ρ L l : ℝ} {ζ : StepVariable (finiteCells F)}
    {f g : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) → ℝ}
    (h : ∀ᶠ τ : Fin k → ℝ in 𝓝 0, ∀ (l' : ℝ) (ζ' : StepVariable (finiteCells F)), 0 < l' → l' ≤ L →
      MemScaledBalls ρ l' ζ' → f ((l', ζ'), τ) = g ((l', ζ'), τ)) (hl : 0 < l) (hL : l < L)
    (hζ : ∀ b, l * ‖ζ b‖ < ρ) :
    ∀ᶠ q in 𝓝 (((l, ζ), 0) : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)), f q = g q := by
  have h1 : ∀ᶠ q in 𝓝 (((l, ζ), 0) : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)),
      ∀ (l' : ℝ) (ζ' : StepVariable (finiteCells F)),
      0 < l' → l' ≤ L → MemScaledBalls ρ l' ζ' → f ((l', ζ'), q.2) = g ((l', ζ'), q.2) :=
    (continuous_snd.tendsto (((l, ζ), 0) : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ))).eventually h
  have hc1 : Continuous fun q : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) => q.1.1 :=
    continuous_fst.comp continuous_fst
  have h2 : ∀ᶠ q in 𝓝 (((l, ζ), 0) : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)), 0 < q.1.1 :=
    hc1.continuousAt.eventually (lt_mem_nhds hl)
  have h3 : ∀ᶠ q in 𝓝 (((l, ζ), 0) : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)), q.1.1 ≤ L :=
    hc1.continuousAt.eventually (ge_mem_nhds hL)
  have h4 : ∀ᶠ q in 𝓝 (((l, ζ), 0) : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)),
      MemScaledBalls ρ q.1.1 q.1.2 := by
    have : ∀ᶠ q in 𝓝 (((l, ζ), 0) : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)),
        ∀ b, q.1.1 * ‖q.1.2 b‖ < ρ := by
      rw [eventually_all]
      intro b
      have hc : Continuous fun q : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) => q.1.1 * ‖q.1.2 b‖ :=
        hc1.mul (continuous_norm.comp ((continuous_apply b).comp (continuous_snd.comp continuous_fst)))
      exact hc.continuousAt.eventually (gt_mem_nhds (hζ b))
    exact this
  filter_upwards [h1, h2, h3, h4] with q a1 a2 a3 a4
  exact a1 _ _ a2 a3 a4
theorem mixedDerivAt_congr {l : ℝ} {ζ : StepVariable (finiteCells F)}
    {f g : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) → ℝ}
    (h : ∀ᶠ q in 𝓝 (((l, ζ), 0) : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)), f q = g q)
    (J : Finset (Fin (i + k))) :
    mixedDerivAt (shiftedAlongScale i l f) J ζ = mixedDerivAt (shiftedAlongScale i l g) J ζ := by
  unfold mixedDerivAt
  have hc : Continuous fun τ : Fin (i + k) → ℝ =>
      (((l + (scaleTopLinear i k τ).1, ζ), (scaleTopLinear i k τ).2) :
        (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)) := by
    have h1 := (scaleTopLinear i k).continuous
    exact ((continuous_const.add h1.fst).prodMk continuous_const).prodMk h1.snd
  have h0 : (((l + (scaleTopLinear i k 0).1, ζ), (scaleTopLinear i k 0).2) :
      (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ)) = ((l, ζ), 0) := by
    simp
  have ht : Filter.Tendsto (fun τ : Fin (i + k) → ℝ =>
      (((l + (scaleTopLinear i k τ).1, ζ), (scaleTopLinear i k τ).2) :
        (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ))) (𝓝 0) (𝓝 ((l, ζ), 0)) := by
    have := hc.tendsto 0
    rwa [h0] at this
  have hev : (fun τ => shiftedAlongScale i l f τ ζ) =ᶠ[𝓝 0] fun τ => shiftedAlongScale i l g τ ζ := by
    filter_upwards [ht.eventually h] with τ hτ
    simpa only [shiftedAlongScale, scaleTopLinear_apply] using hτ
  rw [(hev.iteratedFDeriv ℝ J.card).eq_of_nhds]
section
variable {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {f : LocalFamily} {V : F.GaugeField F.top} {law : StepLaw}
  {Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ} {Y : F.Cell} {K K₀ l l₁ : ℝ}
  {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions} {Cq : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
  {Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ}
  {Km : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ}
theorem scaledCutoff_eq_zero {ρ l' : ℝ} {p : ℝ → ℝ} {ζ : StepVariable (finiteCells F)} (hl : 0 < l')
    (h : ¬ MemScaledBalls ρ l' ζ) : scaledCutoff ρ p l' ζ = 0 := by
  simp only [MemScaledBalls, not_forall, not_lt] at h
  obtain ⟨b, hb⟩ := h
  refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
  have h2 : ρ ≤ ‖l' • ζ b‖ := by
    rw [norm_smul, Real.norm_of_nonneg hl.le]
    exact hb
  simp [cutoffFactor, not_lt.mpr h2]
open Classical in
theorem abs_scaledTopMean_deriv_le (hM : ScaledMeanCumulantExpansion)
    (D : CumulantTermHyps T f V law Ob Y K K₀ l l₁ c X Cq Cr Ψ Km) {Cs : ℕ → ℝ} {W : ℝ}
    (hP : WeightedSizeBound T.κ (fun q => |Cq q|) Cs W)
    (hW : ∀ Y' : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(2 ^ 4 * T.κ * cellSupDist (chordBondCell F b) Y')) ≤ W)
    {CsCut : ℕ → ℕ → ℝ}
    (hCut : ∀ j, CutoffDerivSizeBound T.ballRadius T.p (fun j q N => |Cr j q N|) (j + 1) (CsCut j))
    (hCs0 : ∀ q, 0 ≤ Cs q) (hCut0 : ∀ j q, 0 ≤ CsCut j q) {Cq₀ : ℕ → ℝ} (hq1 : ∀ q, Cs q ≤ Cq₀ q)
    (hq2 : ∀ j, j < 5 → ∀ q, CsCut j q ≤ Cq₀ q) (hCq₀ : ∀ q, 0 ≤ Cq₀ q) (hread : IsControlledOrder k i) {N : ℕ}
    (hy : ∀ z, (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => chordBondCell F b = z).card ≤ N)
    {B : ℕ → (ℕ → ℝ) → ℝ} (hB : SetIndexedCumulantBound N (N + 3) T.κ T.lam B)
    (hB0 : ∀ M, 2 ≤ M → M ≤ 9 → 0 ≤ B M Cq₀) :
    |iteratedDeriv i (fun l' => iteratedFDeriv ℝ k (fun τ => scaledTopMean T.ballRadius T.p
        (exponentAlongList T f V law c X) (observableAlongList Ob V c X) (l', τ)) 0 fun j => Pi.single j 1) l| ≤
      (cumulantTermCount (i + k) : ℝ) * (((∑ M ∈ Finset.Icc 2 9, B M Cq₀) * (K₀ + 1) ^ 5 + Cs 1) * K *
        Real.exp (-(T.κ / 16 * bondSpan Y c))) := by
  have hsix : ((i + k : ℕ) : WithTop ℕ∞) ≤ ((6 : ℕ) : WithTop ℕ∞) := by
    have : i + k ≤ 6 := by rcases hread with h | h <;> omega
    exact_mod_cast this
  have hl := D.lpos
  have hfin := D.fin
  obtain ⟨Gt, aO, cO⟩ := D.ob.exists_smooth_extension k c X
  choose GB aB cB using fun Y' : F.Cell => (D.birth Y').exists_smooth_extension k c X
  choose GR aR cR using fun Y' : F.Cell => (D.row Y').exists_smooth_extension k c X
  set A : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) → ℝ := exponentAlongList T f V law c X with hA
  set G : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) → ℝ := observableAlongList Ob V c X with hG
  set At : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) → ℝ := fun q =>
    (∑ Y ∈ finiteCells F, (StepLaw.exponentWeight law * GB Y q - StepLaw.familyWeight law * GR Y q)) +
      T.lam / 2 * ∑ b : ↥(chordBonds (finiteCells F)), ‖q.1.2 b‖ ^ 2 with hAt
  have hAc : ∀ (l' : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l' → l' ≤ l₁ → (∀ b, l' * ‖ζ b‖ ≤ T.ballRadius) →
      ContDiffAt ℝ (6 : ℕ) At ((l', ζ), 0) := by
    intro l' ζ h0 h1 hb
    refine ContDiffAt.add (ContDiffAt.sum fun Y' _ => ?_) ?_
    · exact (contDiffAt_const.mul (cB Y' l' ζ h0 h1 hb)).sub (contDiffAt_const.mul (cR Y' l' ζ h0 h1 hb))
    · refine contDiffAt_const.mul (ContDiffAt.sum fun b _ => ?_)
      have h2 : ContDiff ℝ (6 : ℕ) (fun q : (ℝ × StepVariable (finiteCells F)) × (Fin k → ℝ) => q.1.2 b) :=
        (contDiff_apply ℝ BondVector b).comp (contDiff_snd.comp contDiff_fst)
      exact (h2.norm_sq ℝ).contDiffAt
  have hAa : ∀ᶠ τ : Fin k → ℝ in 𝓝 0, ∀ (l' : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l' → l' ≤ l₁ →
      MemScaledBalls T.ballRadius l' ζ → At ((l', ζ), τ) = A ((l', ζ), τ) := by
    filter_upwards [eventually_all.mpr aB, eventually_all.mpr aR] with τ h1 h2 l' ζ h0 h3 hb
    rw [hA, exponentAlongList_eq D.lawEq hfin]
    simp only [hAt]
    congr 1
    refine Finset.sum_congr rfl fun Y' _ => ?_
    rw [h1 Y' l' ζ h0 h3 hb, h2 Y' l' ζ h0 h3 hb]
    rfl
  have hGa : ∀ᶠ τ : Fin k → ℝ in 𝓝 0, ∀ (l' : ℝ) (ζ : StepVariable (finiteCells F)), 0 < l' → l' ≤ l₁ →
      MemScaledBalls T.ballRadius l' ζ → Gt ((l', ζ), τ) = G ((l', ζ), τ) := aO
  have hdens : ∀ᶠ τ : Fin k → ℝ in 𝓝 0, ∀ (l' : ℝ), 0 < l' → l' ≤ l₁ →
      scaledDensity T.ballRadius T.p At (l', τ) = scaledDensity T.ballRadius T.p A (l', τ) := by
    filter_upwards [hAa] with τ h1 l' h0 h2
    funext ζ
    by_cases hb : MemScaledBalls T.ballRadius l' ζ
    · simp only [scaledDensity]
      rw [h1 l' ζ h0 h2 hb]
    · simp only [scaledDensity]
      rw [scaledCutoff_eq_zero h0 hb, zero_mul, zero_mul]
  have hd0 : scaledDensity T.ballRadius T.p At (l, 0) = scaledDensity T.ballRadius T.p A (l, 0) :=
    hdens.self_of_nhds l hl D.llt.le
  have hmeanEq : ∀ᶠ τ : Fin k → ℝ in 𝓝 0, ∀ (l' : ℝ), 0 < l' → l' ≤ l₁ →
      scaledTopMean T.ballRadius T.p A G (l', τ) = scaledTopMean T.ballRadius T.p At Gt (l', τ) := by
    filter_upwards [hdens, hGa] with τ h1 h2 l' h0 h3
    unfold scaledTopMean
    rw [h1 l' h0 h3]
    refine densityMean_congr volume fun ζ hz => ?_
    have hb : MemScaledBalls T.ballRadius l' ζ := by
      by_contra hb
      apply hz
      simp only [scaledDensity]
      rw [scaledCutoff_eq_zero h0 hb, zero_mul]
    exact (h2 l' ζ h0 h3 hb).symm
  have hder : iteratedDeriv i (fun l' => iteratedFDeriv ℝ k (fun τ => scaledTopMean T.ballRadius T.p A G (l', τ)) 0
        fun j => Pi.single j 1) l =
      iteratedDeriv i (fun l' => iteratedFDeriv ℝ k (fun τ => scaledTopMean T.ballRadius T.p At Gt (l', τ)) 0
        fun j => Pi.single j 1) l := by
    refine Filter.EventuallyEq.iteratedDeriv_eq i ?_
    filter_upwards [lt_mem_nhds hl, gt_mem_nhds D.llt] with l' h0 h1
    have hev : (fun τ => scaledTopMean T.ballRadius T.p A G (l', τ)) =ᶠ[𝓝 0]
        fun τ => scaledTopMean T.ballRadius T.p At Gt (l', τ) := by
      filter_upwards [hmeanEq] with τ hτ
      exact hτ l' h0 h1.le
    rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
  obtain ⟨-, hform⟩ := hM ↥(chordBonds (finiteCells F)) T.ballRadius T.p i k At Gt l D.ρpos D.cut hl
    (fun ζ hζ => (hAc l ζ hl D.llt.le hζ).of_le hsix)
    (fun ζ hζ => (cO l ζ hl D.llt.le hζ).of_le hsix)
    (fun j q b hj hq => by
      rw [hd0]
      exact integrable_cutoffDeriv_scaled D j q b hj hq)
  rw [hder, hform]
  set R : ℝ := ((∑ M ∈ Finset.Icc 2 9, B M Cq₀) * (K₀ + 1) ^ 5 + Cs 1) * K *
    Real.exp (-(T.κ / 16 * bondSpan Y c)) with hR
  have hterm : ∀ (I : Finset (Fin (i + k))) (π : Finpartition ((Finset.univ : Finset (Fin (i + k))) \ I)),
      jointCumulant (densityMean volume (scaledDensity T.ballRadius T.p At (l, 0))) (insert none (π.parts.image some))
        (scaleCumulantEntries i T.p l At Gt I) =
      jointCumulant (densityMean volume (scaledDensity T.ballRadius T.p A (l, 0))) (insert none (π.parts.image some))
        (scaleCumulantEntries i T.p l A G I) := by
    intro I π
    rw [hd0]
    refine jointCumulant_congr fun J _ => densityMean_congr volume fun ζ hz => ?_
    have hb : ∀ b, l * ‖ζ b‖ < T.ballRadius := by
      by_contra hb
      apply hz
      simp only [scaledDensity]
      rw [scaledCutoff_eq_zero hl hb, zero_mul]
    have eA := eventuallyEq_of_scaledBalls hAa hl D.llt hb
    have eG := eventuallyEq_of_scaledBalls hGa hl D.llt hb
    refine Finset.prod_congr rfl fun o _ => ?_
    cases o with
    | none => exact mixedDerivAt_congr eG I
    | some J' =>
      simp only [scaleCumulantEntries]
      rw [mixedDerivAt_congr eA J']
  have h1 : ∀ I ∈ (Finset.univ : Finset (Fin (i + k))).powerset,
      |∑ π : Finpartition ((Finset.univ : Finset (Fin (i + k))) \ I), jointCumulant
        (densityMean volume (scaledDensity T.ballRadius T.p At (l, 0))) (insert none (π.parts.image some))
        (scaleCumulantEntries i T.p l At Gt I)| ≤
      (Fintype.card (Finpartition ((Finset.univ : Finset (Fin (i + k))) \ I)) : ℝ) * R := by
    intro I _
    calc _ ≤ ∑ π : Finpartition ((Finset.univ : Finset (Fin (i + k))) \ I), |jointCumulant
          (densityMean volume (scaledDensity T.ballRadius T.p At (l, 0))) (insert none (π.parts.image some))
          (scaleCumulantEntries i T.p l At Gt I)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _π : Finpartition ((Finset.univ : Finset (Fin (i + k))) \ I), R := Finset.sum_le_sum fun π _ => by
          rw [hterm I π]
          exact abs_jointCumulant_term_le D hP hW hCut hCs0 hCut0 hq1 hq2 hCq₀ hread hy hB hB0 I π
      _ = _ := by
          simp [Finset.card_univ]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum h1).trans (le_of_eq ?_))
  rw [← Finset.sum_mul]
  simp [cumulantTermCount]
end
theorem eventually_isSmallCurvature_leftTranslate (hs : ∀ a, 1 ≤ F.extent a) {s : ℝ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature s V) :
    ∀ᶠ τ : Fin k → ℝ in 𝓝 0, IsSmallCurvature s (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) := by apply _root_.YangMills.SharedProofs.p42166 <;> assumption
theorem iteratedDeriv_observableMean_eq (hLaw : stepLawAtScaleStatement) {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} {l₀ : ℝ}
    (hE : RescaledExponentsAgree T l₀) {t : ℕ} {f : LocalFamily} {V : F.GaugeField F.top}
    (law : StepLaw) {l : ℝ} (Y : F.Cell) (hF : IsCubicTopTorus T.L t T.n₀ F) (hs : ∀ a, 1 ≤ F.extent a)
    (hV : IsSmallCurvature (5 / 4 * T.σ) V) (hl : 0 < l) (hl₀ : l < l₀)
    (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (i : ℕ) :
    iteratedDeriv i (fun l' => bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l') V c X) l =
      iteratedDeriv i (fun l' => iteratedFDeriv ℝ k (fun τ => scaledTopMean T.ballRadius T.p
        (exponentAlongList T f V law c X) (observableAlongList Ob V c X) (l', τ)) 0 fun j => Pi.single j 1) l := by
  refine Filter.EventuallyEq.iteratedDeriv_eq i ?_
  filter_upwards [lt_mem_nhds hl, gt_mem_nhds hl₀] with l' h0 h1
  unfold bondDeriv
  have hev : (fun τ : Fin k → ℝ =>
      observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l' (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) =ᶠ[𝓝 0]
      fun τ => scaledTopMean T.ballRadius T.p (exponentAlongList T f V law c X) (observableAlongList Ob V c X)
        (l', τ) := by
    filter_upwards [eventually_isSmallCurvature_leftTranslate hs c X hV] with τ hτ
    exact hLaw.2.1 T _ hE t F _ f law l' Y hF hτ h0 h1.le Ob
  rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
set_option maxRecDepth 20000 in
theorem scaledMeans_bound_core (hLaw : stepLawAtScaleStatement) (hY : derivAlongParameterListStatement)
    (hM : ScaledMeanCumulantExpansion)
    (hS1 : ObservableSizeOfWeightedBound) (hS2 : cutoffDerivSizesStatement)
    (hCum : setIndexedCumulantBoundStatement) (hBonds : BondsPerCellBounded) (hWts : _root_.YangMills.Construction.CellCounting.ExpDecaySumBounded)
    {T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters} (hT : T.IsOrdered) (hn : 1 ≤ T.n₀) {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
    (hfr : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFrameBoundsAt T Cq Cz Cr t x)
    (hparts : ∀ e : ℕ → ℝ, ∃ l₀ K : ℝ, 0 < l₀ ∧ 0 ≤ K ∧ ∀ l₁ : ℝ, 0 < l₁ → l₁ ≤ l₀ →
      ∀ (t : ℕ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell),
        T.IsBoundedFamilyOrderSix e t f →
        IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
        IsSmoothObservable T.κ T.ballRadius l₁ K Y V (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) ∧
        IsSmoothObservable T.κ T.ballRadius l₁ K Y V (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ))
    (hex : ∃ l₀ : ℝ, 0 < l₀ ∧ RescaledExponentsAgree T l₀) (e : ℕ → ℝ) :
    ∃ l₀ C : ℝ, 0 < l₀ ∧ 0 < C ∧ ∀ l₁ : ℝ, 0 < l₁ → l₁ ≤ l₀ →
    ∀ (t : ℕ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell) (law : StepLaw) (K : ℝ)
      (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (X : Fin k → imaginaryQuaternions), T.IsBoundedFamilyOrderSix e t f → IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → StepLaw.IsUnitWeight law → 0 ≤ K →
      IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius (2 * l₁) K Y Ob → AreUnitVectors X →
      ∀ (i : ℕ) (l : ℝ), IsControlledOrder k i → 0 < l → l ≤ l₁ →
        |iteratedDeriv i (fun l' => bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l') V c X) l| ≤
          C * K * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c)) := by
  classical
  obtain ⟨l₀p, K₀, hl₀p, hK₀, hPt⟩ := hparts e
  obtain ⟨l₀e, hl₀e, hE⟩ := hex
  have hκ : 0 < T.κ := hT.κ_pos
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    simp only [StepParameters.ballRadius]
    positivity
  have hcut : IsCutoff T.ballRadius T.p := hT.cutoff
  have hlam : 0 < T.lam := hT.chain_admissible.positivity.2.2.1
  have hLpos : 0 < T.L := hT.odd_L.pos
  obtain ⟨N, hN⟩ := hBonds T.L hLpos
  obtain ⟨W, hW0, hWt⟩ := hWts N (2 ^ 4 * T.κ) (by positivity)
  obtain ⟨Cs, hCs0, hClaim⟩ := hS1 T.κ W (fun q => |Cq q|) hW0 fun q => abs_nonneg _
  have hcutex := fun j : ℕ => hS2 T.ballRadius T.p (fun j q N => |Cr j q N|) (j + 1) hρ hcut (by omega)
    (fun _ _ _ => abs_nonneg _)
  choose CsCut hCut0 hCut using hcutex
  set Cq₀ : ℕ → ℝ := fun q => Cs q + ∑ j ∈ Finset.range 5, CsCut j q with hCq₀
  have hq1 : ∀ q, Cs q ≤ Cq₀ q := fun q => by
    have : 0 ≤ ∑ j ∈ Finset.range 5, CsCut j q := Finset.sum_nonneg fun j _ => hCut0 j q
    simp only [hCq₀]
    linarith
  have hq2 : ∀ j, j < 5 → ∀ q, CsCut j q ≤ Cq₀ q := fun j hj q => by
    have h1 : CsCut j q ≤ ∑ j ∈ Finset.range 5, CsCut j q :=
      Finset.single_le_sum (f := fun j => CsCut j q) (fun j _ => hCut0 j q) (Finset.mem_range.mpr hj)
    have := hCs0 q
    simp only [hCq₀]
    linarith
  have hCq0 : ∀ q, 0 ≤ Cq₀ q := fun q => (hCs0 q).trans (hq1 q)
  obtain ⟨B, hBn, hB⟩ := hCum N (N + 3) T.κ T.lam hκ hlam
  have hB0 : ∀ M, 2 ≤ M → M ≤ 9 → 0 ≤ B M Cq₀ := fun M h2 h9 => hBn M h2 h9 Cq₀ hCq0
  obtain ⟨Bt, hBt⟩ : ∃ Bt : ℝ, Bt = (∑ M ∈ Finset.Icc 2 9, B M Cq₀) * (K₀ + 1) ^ 5 + Cs 1 := ⟨_, rfl⟩
  have hBt0 : 0 ≤ Bt := by
    have h1 : 0 ≤ ∑ M ∈ Finset.Icc 2 9, B M Cq₀ := Finset.sum_nonneg fun M hM => by
      have := Finset.mem_Icc.mp hM
      exact hB0 M this.1 this.2
    have := hCs0 1
    rw [hBt]
    positivity
  obtain ⟨N₅, hN₅⟩ : ∃ N₅ : ℕ, N₅ = ∑ n ∈ Finset.range 6, cumulantTermCount n := ⟨_, rfl⟩
  set l₀y : ℝ := 1 / (1 + |T.coupling|) with hl₀y
  have hl₀yp : 0 < l₀y := by positivity
  have hl₀y1 : l₀y ≤ 1 := by
    rw [hl₀y, div_le_one (by positivity)]
    linarith [abs_nonneg T.coupling]
  set l₀ : ℝ := min (l₀p / 2) (min (l₀e / 2) l₀y) with hl₀
  have h₀p : l₀ ≤ l₀p / 2 := min_le_left _ _
  have h₀e : l₀ ≤ l₀e / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have h₀y : l₀ ≤ l₀y := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨l₀, (N₅ : ℝ) * Bt + 1, by simp [hl₀, hl₀p, hl₀e, hl₀yp],
    add_pos_of_nonneg_of_pos (mul_nonneg (Nat.cast_nonneg _) hBt0) one_pos, ?_⟩
  intro l₁ hl₁ hle t f F V Y law K Ob k c X hf hF hV hlaw hK hO hXu i l hread hl hll₁
  obtain ⟨hFL, hFt, nS, hside, hnS⟩ := hF
  have hF' : IsCubicTopTorus T.L t T.n₀ F := ⟨hFL, hFt, nS, hside, hnS⟩
  have hs1 : ∀ a, 1 ≤ F.extent a := fun a => by
    rw [hside a]
    omega
  have hfin : Finite F.Cell := finite_cell hs1
  have hl0 : l ≤ l₀ := hll₁.trans hle
  have hl1 : l ≤ 1 := (hl0.trans h₀y).trans hl₀y1
  have hlinv : (1 + |T.coupling|) ≤ l⁻¹ := by
    have h1 : l ≤ 1 / (1 + |T.coupling|) := hl0.trans h₀y
    rw [le_div_iff₀ (by positivity)] at h1
    rw [le_inv_comm₀ (by positivity) hl, inv_eq_one_div]
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hy₁ : T.coupling ≤ l⁻¹ ^ 2 := by
    have h1 : 1 ≤ l⁻¹ := by linarith [abs_nonneg T.coupling]
    have h2 : l⁻¹ ≤ l⁻¹ ^ 2 := le_self_pow₀ h1 (by norm_num)
    linarith [le_abs_self T.coupling]
  have hle₀ : l < l₀e := by
    have : l ≤ l₀e / 2 := hl0.trans h₀e
    linarith
  obtain ⟨Ψ, Km, hL⟩ := hLaw.2.2 T Cq Cz Cr t l l₀e f F V law Y (hfr t _ hy₁) hf.1 hF' hV hlaw hl hle₀.le hE
  have hparts' := fun Y' => hPt (2 * l₁) (by positivity) (by linarith [hle.trans h₀p]) t f F V Y' hf hF' hV
  have D : CumulantTermHyps T f V law Ob Y K K₀ l (2 * l₁) c X Cq Cr Ψ Km :=
    { fin := hfin, κpos := hκ, ρpos := hρ, cut := hcut, lists := hY, lawEq := hLaw, lampos := hlam, lpos := hl,
      lone := hl1, llt := by linarith,
      weight := hlaw, units := hXu, Kn := hK, K₀n := hK₀, ob := hO V hV, birth := fun Y' => (hparts' Y').1,
      row := fun Y' => (hparts' Y').2, law := hL }
  have hy : ∀ z, (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => chordBondCell F b = z).card ≤ N :=
    fun z => by
      have := hN F hFL ↥(chordBonds (finiteCells F)) (fun b => b.1) Subtype.val_injective z
      convert this
      rfl
  have hW : ∀ Y' : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(2 ^ 4 * T.κ * cellSupDist (chordBondCell F b) Y')) ≤ W :=
    fun Y' => hWt F ↥(chordBonds (finiteCells F)) (chordBondCell F) (by
      intro z
      convert hy z) Y'
  have hsum := abs_scaledTopMean_deriv_le hM D hClaim hW hCut hCs0 hCut0 hq1 hq2 hCq0 hread hy hB hB0
  rw [← hBt] at hsum
  rw [iteratedDeriv_observableMean_eq hLaw hE law Y hF' hs1 hV hl hle₀ Ob c X i]
  refine hsum.trans ?_
  have hik : i + k ≤ 5 := by rcases hread with h | h <;> omega
  have hcount : (cumulantTermCount (i + k) : ℝ) ≤ N₅ := by
    have h1 : cumulantTermCount (i + k) ≤ N₅ := by
      rw [hN₅]
      exact Finset.single_le_sum (f := fun n => cumulantTermCount n) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega : i + k < 6))
    exact_mod_cast h1
  have hspan : (0 : ℝ) ≤ bondSpan Y c := Nat.cast_nonneg _
  have hexp : Real.exp (-(T.κ / 16 * bondSpan Y c)) ≤ Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c)) := by
    refine Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right ?_ hspan))
    exact div_le_div_of_nonneg_left hκ.le (by norm_num) (by norm_num)
  have h0 : 0 ≤ Bt * K := mul_nonneg hBt0 hK
  calc (cumulantTermCount (i + k) : ℝ) * (Bt * K * Real.exp (-(T.κ / 16 * bondSpan Y c)))
      ≤ (N₅ : ℝ) * (Bt * K * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))) :=
        mul_le_mul hcount (mul_le_mul_of_nonneg_left hexp h0) (mul_nonneg h0 (Real.exp_pos _).le)
          (Nat.cast_nonneg _)
    _ = (N₅ : ℝ) * Bt * K * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c)) := by ring
    _ ≤ ((N₅ : ℝ) * Bt + 1) * K * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hK)
        (Real.exp_pos _).le
end ScaledMeanBounds
open ScaledMeanBounds ColdStepAtMirrorFrames ScaledVariables in
theorem ScaledVariables.scaledMeansBounded_holds (hFr : Interpolation.interpolatedFramesStatement)
    (hLaw : ScaledVariables.stepLawAtScaleStatement) (hParts : StepDensities.rescaledPartsSmoothStatement)
    (hY : ScaleDerivatives.derivAlongParameterListStatement) (hExp : ScaledVariables.RescaledExponentAgrees)
    (hM : ScaleDerivatives.ScaledMeanCumulantExpansion)
    (hS1 : Interpolation.ObservableSizeOfWeightedBound)
    (hS2 : Interpolation.cutoffDerivSizesStatement)
    (hCum : Cumulants.setIndexedCumulantBoundStatement) (hBonds : CellCounting.BondsPerCellBounded)
    (hWts : CellCounting.ExpDecaySumBounded) : ScaledVariables.scaledMeansBounded := by
  obtain ⟨Cq, Cz, Cr, hF⟩ := hFr
  unfold ScaledVariables.scaledMeansBounded ForallSmoothObservables
  have hF' : EventuallyOrdered _ := EventuallyInParameters.mono hF fun T g _ _ => g
  refine EventuallyOrdered.mono (EventuallyOrdered.and hF'
    (EventuallyOrdered.and hParts hExp)) ?_
  rintro T hT hn ⟨g₁, g₂, g₄⟩
  exact scaledMeans_bound_core hLaw hY hM hS1 hS2 hCum hBonds hWts hT hn g₁ g₂ g₄
end YangMills.Construction
end
