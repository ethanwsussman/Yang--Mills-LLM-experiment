import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionsOfTheChartEnergyProof
import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import YangMills.Construction.ResponseInTheExpansion.InverseOfACoordinateHessian
import Mathlib
import YangMills.Construction.ResponseInTheExpansion.EntriesOfTheHessianOfTheMirrorProof
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.MomentLaw
def hessianOverExpFieldStatement : Prop :=
  ∀ (a : ℝ) (L : ℕ) [NeZero L] (c : ColdStepAtMirrorFrames.ColdChainParameters), 1 ≤ a → Odd L →
    2 ^ 40 ≤ L → c.Admissible a L →
    ∀ s₁ e₀ Cw : ℝ, 0 < s₁ → 0 ≤ e₀ → e₀ ≤ 1 / (64 * (L : ℝ)) → s₁ + 8 * e₀ < c.σA → 0 ≤ Cw →
    ∃ P r : ℝ, 0 ≤ P ∧ 0 < r ∧ ∀ (u n : ℕ) [NeZero n], 64 ≤ n →
      (∀ b b', WeightedResponses.trivialHessian a L u n b b' = WeightedResponses.trivialHessian a L u n b' b) →
      ∀ (B : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) (O : TorusFields.TorusSite n)
        (v sT : ℝ), 0 ≤ v → (∀ d, ‖B d‖ ≤ 4 * ((TorusFields.supDist d.1 O : ℝ) + 1) * v) →
      (∀ d, ‖B d‖ ≤ sT) → 4 * sT < s₁ →
      ∀ w : (TorusFields.torusFrame L u n).Site (TorusFields.torusFrame L u n).depth → Fin 4 →
          BlockAverages.imaginaryQuaternions,
      (∀ d ∈ BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u n)),
        ‖w d.1 d.2‖ ≤ e₀) →
      (∀ d ∈ BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L u n)),
        ‖w d.1 d.2‖ ≤ Cw * v) →
      ∀ (b : ChartBondIndex L u n) (e : Fin 3) (q : ChartBondIndex L u n × Fin 3),
        |LinearResponse.bondCoordinateHessian
            (ColdStepAtMirrorFrames.chartedEnergyAt a w
              (TorusFields.readAtLevel (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top
                (expField 1 B))) (b, e) q -
            (if q.2 = e then WeightedResponses.trivialHessian a L u n b q.1 else 0)| ≤
          P * Real.exp (-(r * ColdStepAtMirrorFrames.chordBondDist (TorusFields.torusFrame L u n) q.1 b)) *
            (1 + (BlockAverages.cellSupDist (BlockAverages.enclosingCell q.1.1.1)
              (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).top O) :
                ℝ)) * v
end YangMills.Construction.MomentLaw
end

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion Topology
open MeasureTheory
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames.ChartKernelCalculus
open BlockAverages
section Calculus
variable {P Q R : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R]
theorem fderiv_fderiv_comp_clm_apply {Φ : Q → R} (l : P →L[ℝ] Q) {x : P} (hΦ : ContDiffAt ℝ 3 Φ (l x))
    (u v : P) :
    fderiv ℝ (fderiv ℝ (Φ ∘ l)) x v u = fderiv ℝ (fderiv ℝ Φ) (l x) (l v) (l u) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartEnergyRows.fderiv_fderiv_comp_clm <;> assumption
end Calculus
def toImaginaryCLM : BondVector →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => toImaginary v
      map_add' := fun u v => by
        apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · change (0 : ℝ) = 0 + 0
          simp
        · change (u + v) 0 = u 0 + v 0
          simp
        · change (u + v) 1 = u 1 + v 1
          simp
        · change (u + v) 2 = u 2 + v 2
          simp
      map_smul' := fun c v => by
        apply Subtype.ext
        refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
        · change (0 : ℝ) = c * 0
          simp
        · change (c • v) 0 = c * v 0
          simp
        · change (c • v) 1 = c * v 1
          simp
        · change (c • v) 2 = c * v 2
          simp }
theorem toImaginaryCLM_apply (v : BondVector) : toImaginaryCLM v = toImaginary v := rfl
variable {F : BlockFrame}
abbrev ChordBond (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F))
theorem leftTranslate_of_base_directions {k : ℕ} (V : F.GaugeField F.top) (q : Fin k → ChartDirection F)
    (hq : ∀ l, ∃ p, q l = .inl p) (σ : Fin k → ℝ) :
    leftTranslate (fun y i => ∑ l, σ l • directionMove (q l) y i) V = V := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartEnergyRows.leftTranslate_of_bondDirections <;> assumption
def chordDirection (b : ChordBond F) (e : BondVector) : ChartDirection F :=
  .inl (b.1.1, b.1.2, toImaginaryCLM e)
theorem stepCoordinates_bondVariation (b : ChordBond F) (e : BondVector) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (bondVariation b e : StepVariable (finiteCells F)) x i =
      directionCoordinate (chordDirection b e) x i := by
  classical
  simp only [stepCoordinates, directionCoordinate, chordDirection]
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · rw [dif_pos h]
    by_cases hb : b.1.1 = x ∧ b.1.2 = i
    · have hbb : (⟨(x, i), h⟩ : ChordBond F) = b := Subtype.ext (Prod.ext hb.1.symm hb.2.symm)
      rw [if_pos hb, hbb]
      simp [bondVariation, toImaginaryCLM_apply]
    · have hbb : (⟨(x, i), h⟩ : ChordBond F) ≠ b := by
        intro hc
        apply hb
        rw [← hc]
        exact ⟨rfl, rfl⟩
      have : (bondVariation b e : StepVariable (finiteCells F)) ⟨(x, i), h⟩ = 0 :=
        Pi.single_eq_of_ne hbb _
      rw [if_neg hb, this]
      exact map_zero toImaginaryCLM
  · rw [dif_neg h, if_neg]
    rintro ⟨rfl, rfl⟩
    exact h b.2
theorem stepCoordinates_smul (r : ℝ) (η : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (r • η) x i = r • stepCoordinates η x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_smul <;> assumption
theorem stepCoordinates_sum {ι : Type} (s : Finset ι) (g : ι → StepVariable (finiteCells F))
    (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (∑ l ∈ s, g l) x i = ∑ l ∈ s, stepCoordinates (g l) x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartEnergyRows.stepCoordinates_sum <;> assumption
theorem chartRestriction_chordDirections {k : ℕ} (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (b : Fin k → ChordBond F) (e : Fin k → BondVector) (σ : Fin k → ℝ) :
    chartRestriction a w V (fun l => chordDirection (b l) (e l)) σ =
      chartedEnergyAt a w V (∑ l, σ l • (bondVariation (b l) (e l) : StepVariable (finiteCells F))) := by
  have ht : leftTranslate (fun y i => ∑ l, σ l • directionMove (chordDirection (b l) (e l)) y i) V = V :=
    leftTranslate_of_base_directions V (fun l => chordDirection (b l) (e l)) (fun l => ⟨_, rfl⟩) σ
  simp only [chartRestriction, chartedEnergyAt, ht]
  congr 1
  funext x i
  rw [stepCoordinates_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [stepCoordinates_smul, stepCoordinates_bondVariation]
theorem contDiffAt_chartedEnergyAt {a : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top}
    (h : ∀ (k : ℕ) (q : Fin k → ChartDirection F), AnalyticAt ℝ (chartRestriction a w V q) 0) :
    ContDiffAt ℝ 3 (chartedEnergyAt a w V) 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartEnergyRows.contDiffAt_chartedEnergyAt <;> assumption
def twoBondPlane (b b' : ChordBond F) (e e' : BondVector) :
    (Fin 2 → ℝ) →L[ℝ] StepVariable (finiteCells F) :=
  ((ContinuousLinearMap.proj (0 : Fin 2)).smulRight (bondVariation b e : StepVariable (finiteCells F))) +
    ((ContinuousLinearMap.proj (1 : Fin 2)).smulRight (bondVariation b' e' : StepVariable (finiteCells F)))
theorem chartMixedDeriv_chordDirections {a : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top}
    (hA : ContDiffAt ℝ 3 (chartedEnergyAt a w V) 0) (b b' : ChordBond F) (e e' : BondVector) :
    chartMixedDeriv a w V ![chordDirection b e, chordDirection b' e'] =
      fderiv ℝ (fderiv ℝ (chartedEnergyAt a w V)) 0 (bondVariation b e) (bondVariation b' e') := by
  have h1 : chartRestriction a w V ![chordDirection b e, chordDirection b' e'] =
      chartedEnergyAt a w V ∘ twoBondPlane b b' e e' := by
    funext σ
    have hq : (![chordDirection b e, chordDirection b' e'] : Fin 2 → ChartDirection F) =
        fun l => chordDirection ((![b, b'] : Fin 2 → ChordBond F) l) ((![e, e'] : Fin 2 → BondVector) l) := by
      funext l
      fin_cases l <;> rfl
    rw [hq, chartRestriction_chordDirections]
    simp only [Function.comp, twoBondPlane, Fin.sum_univ_two]
    rfl
  unfold chartMixedDeriv
  rw [h1, iteratedFDeriv_two_apply]
  have h0 : twoBondPlane b b' e e' 0 = 0 := map_zero _
  have h2 := fderiv_fderiv_comp_clm_apply (Φ := chartedEnergyAt a w V) (twoBondPlane b b' e e') (x := 0)
    (by rw [h0]; exact hA) (Pi.single 1 1) (Pi.single 0 1)
  change fderiv ℝ (fderiv ℝ (chartedEnergyAt a w V ∘ twoBondPlane b b' e e')) 0 (Pi.single 0 1)
    (Pi.single 1 1) = _
  rw [h2, h0]
  simp [twoBondPlane]
end ColdStepAtMirrorFrames.ChartKernelCalculus
namespace MomentLaw
open BlockAverages ColdStepAtMirrorFrames ColdStepAtMirrorFrames.ChartKernelCalculus TorusFrame
  StepCosts WeightedResponses LinearResponse
open TorusFields hiding unitStep
namespace HessianOverExpFieldSteps
section GroupFacts
variable {F : BlockFrame}
private theorem norm_mul_sub_one_le (g h : UnitQuaternion) :
    ‖((g * h : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(g : ℍ[ℝ]) - 1‖ + ‖(h : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
private theorem norm_inv_sub_one (g : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
private theorem norm_expUnit_sub_one_le (x : imaginaryQuaternions) :
    ‖((expUnit x : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖x‖ := by apply _root_.YangMills.SharedProofs.p28543 <;> assumption
private theorem plaquetteHolonomy_eq {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (μ ν : Fin 4) :
    plaquetteHolonomy X (x, μ, ν) =
      X x μ * X (x + unitStep j μ) ν * (X (x + unitStep j ν) μ)⁻¹ * (X x ν)⁻¹ := by apply _root_.YangMills.Construction.PlaquetteExpansion.plaquetteHolonomy_eq <;> assumption
private theorem chartedField_congr (V : F.GaugeField F.top)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (h : ∀ z i, ¬ IsAxialTreeBond ((z, i) : F.Site F.depth × Fin 4) → w z i = w' z i) :
    chartedField w V = chartedField w' V := by apply _root_.YangMills.SharedProofs.p9062 <;> assumption
private theorem isAdmissibleChartPoint_of_small (hcov : BlocksCoverLowerLevel) {L : ℕ} {σA s₁ e : ℝ}
    (hF : IsBlockTorus L F) (hL : Odd L)
    (he0 : 0 ≤ e) (he : e ≤ 1 / (64 * (L : ℝ))) (hs₁ : 0 ≤ s₁) (hlt : s₁ + 8 * e < σA)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (hw : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ e) (hV : IsSmallCurvature s₁ V) :
    IsAdmissibleChartPoint L σA w V := by apply _root_.YangMills.SharedProofs.p28958 (s₁ := s₁) (e := e) <;> assumption
private theorem exp_neg_mul_max_le (δ : ℝ) (hδ : 0 ≤ δ) (D d : ℕ) :
    Real.exp (-(δ * (max D d : ℕ))) ≤ Real.exp (-(δ / 2 * D)) * Real.exp (-(δ / 2 * d)) := by apply _root_.YangMills.SharedProofs.p848 <;> assumption
end GroupFacts
private theorem leftTranslate_zero {F : BlockFrame} (V : F.GaugeField F.top) :
    leftTranslate (fun _ _ => (0 : imaginaryQuaternions)) V = V := by apply _root_.YangMills.SharedProofs.p46723 <;> assumption
private theorem trivialHessian_eq_chartMixedDeriv (a : ℝ) (L u n : ℕ)
    (b b' : ↥(chordBonds (finiteCells (torusFrame L u n))))
    (han : AnalyticAt ℝ (chartRestriction a (fun _ _ => 0) (uniformField (torusFrame L u n) (torusFrame L u n).top)
      ![Sum.inl (b.1.1, b.1.2, FlatHessian.colourUnit 0), Sum.inl (b'.1.1, b'.1.2, FlatHessian.colourUnit 0)]) 0) :
    trivialHessian a L u n b b' =
      chartMixedDeriv a (fun _ _ => 0) (uniformField (torusFrame L u n) (torusFrame L u n).top)
        ![Sum.inl (b.1.1, b.1.2, FlatHessian.colourUnit 0), Sum.inl (b'.1.1, b'.1.2, FlatHessian.colourUnit 0)] := by apply _root_.YangMills.SharedProofs.p9762 <;> assumption
section UnitNorms
private theorem norm_colourUnit (e : Fin 3) : ‖FlatHessian.colourUnit e‖ = 1 := by apply _root_.YangMills.SharedProofs.p39739 <;> assumption
end UnitNorms
section KernelEntries
variable {F : BlockFrame}
private theorem chartRestriction_congr (a : ℝ) (V : F.GaugeField F.top)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (h : ∀ x i, ¬ IsAxialTreeBond ((x, i) : F.Site F.depth × Fin 4) → w x i = w' x i) {k : ℕ}
    (q : Fin k → ChartDirection F) :
    chartRestriction a w V q = chartRestriction a w' V q := by
  funext σ
  unfold chartRestriction chartedEnergy
  rw [chartedField_congr _ (w := fun x i => w x i + ∑ l, σ l • directionCoordinate (q l) x i)
    (w' := fun x i => w' x i + ∑ l, σ l • directionCoordinate (q l) x i) fun x i ht => by rw [h x i ht]]
private theorem isSmallCurvature_leftTranslate (A : F.Site F.top → Fin 4 → imaginaryQuaternions) {sT s₁ : ℝ}
    (hA : ∀ y i, ‖A y i‖ ≤ sT) (h4 : 4 * sT < s₁)
    (ϑ : F.Site F.top → Fin 4 → ℝ) (hϑ : ∀ y i, 0 ≤ ϑ y i ∧ ϑ y i ≤ 1) :
    IsSmallCurvature s₁ (leftTranslate (fun y i => ϑ y i • A y i) (uniformField F F.top)) := by
  rintro ⟨x, μ, ν⟩ hp
  set U := leftTranslate (fun y i => ϑ y i • A y i) (uniformField F F.top) with hU
  have bond : ∀ y i, ‖((U y i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ sT := by
    intro y i
    have e : U y i = expUnit (ϑ y i • A y i) := by
      simp [hU, leftTranslate, uniformField]
    rw [e]
    refine (norm_expUnit_sub_one_le _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hϑ y i).1]
    have h1 := hϑ y i
    have h2 := hA y i
    have h3 := norm_nonneg (A y i)
    nlinarith
  have b1 := bond x μ
  have b2 := bond (x + unitStep F.top μ) ν
  have b3 := bond (x + unitStep F.top ν) μ
  have b4 := bond x ν
  unfold plaquetteDefect
  rw [plaquetteHolonomy_eq]
  have m1 := norm_mul_sub_one_le (U x μ * U (x + unitStep F.top μ) ν * (U (x + unitStep F.top ν) μ)⁻¹) (U x ν)⁻¹
  have m2 := norm_mul_sub_one_le (U x μ * U (x + unitStep F.top μ) ν) (U (x + unitStep F.top ν) μ)⁻¹
  have m3 := norm_mul_sub_one_le (U x μ) (U (x + unitStep F.top μ) ν)
  rw [norm_inv_sub_one] at m1 m2
  linarith
private theorem one_add_mul_exp_le {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    (1 + t) * Real.exp (-(δ / 2 * t)) ≤ (1 + 4 / δ) * Real.exp (-(δ / 4 * t)) := by
  have h1 : 1 + t ≤ (1 + 4 / δ) * Real.exp (δ / 4 * t) := by
    have h2 : 1 + δ / 4 * t ≤ Real.exp (δ / 4 * t) := by
      have := Real.add_one_le_exp (δ / 4 * t)
      linarith
    have h3 : 0 ≤ 1 + 4 / δ := by positivity
    have h4 : (1 + 4 / δ) * (1 + δ / 4 * t) = 1 + δ / 4 * t + 4 / δ + t := by
      field_simp
      ring
    have h5 : 0 ≤ δ / 4 * t := by positivity
    have h6 : 0 ≤ 4 / δ := by positivity
    calc 1 + t ≤ (1 + 4 / δ) * (1 + δ / 4 * t) := by rw [h4]; linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 h3
  have h7 : Real.exp (δ / 4 * t) * Real.exp (-(δ / 2 * t)) = Real.exp (-(δ / 4 * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc (1 + t) * Real.exp (-(δ / 2 * t)) ≤ ((1 + 4 / δ) * Real.exp (δ / 4 * t)) * Real.exp (-(δ / 2 * t)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, h7]
abbrev _root_.YangMills.SharedProofs.p70520 := @one_add_mul_exp_le
set_option maxHeartbeats 1000000 in
private theorem chartMixedDeriv_near_uniform (hE : ChartResponse.HessianEntryLipschitz)
    (hD : decaySumOnTorusStatement) (hcov : BlocksCoverLowerLevel) {a : ℝ} {L : ℕ} {c : ColdChainParameters}
    (ha : 1 ≤ a) (hL : Odd L) (hL0 : 2 ^ 40 ≤ L)
    (hc : c.Admissible a L) {s₁ e₀ Cw : ℝ} (hs₁ : 0 ≤ s₁) (he₀ : 0 ≤ e₀) (hroom : e₀ ≤ 1 / (64 * (L : ℝ)))
    (hcold : s₁ + 8 * e₀ < c.σA) (hCw : 0 ≤ Cw) :
    ∃ P r : ℝ, 0 ≤ P ∧ 0 < r ∧ ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
      (A : F.Site F.top → Fin 4 → imaginaryQuaternions) (o : F.Cell)
      (v sT : ℝ) (b b' : ↥(chordBonds (finiteCells F))) (X X' : imaginaryQuaternions),
      IsBlockTorus L F → 0 ≤ v → ‖X‖ = 1 → ‖X'‖ = 1 →
      (∀ d ∈ chordBonds (finiteCells F), ‖w d.1 d.2‖ ≤ e₀) →
      (∀ d ∈ chordBonds (finiteCells F), ‖w d.1 d.2‖ ≤ Cw * v) →
      (∀ y i, ‖A y i‖ ≤ sT) → 4 * sT < s₁ → (∀ y i, ‖A y i‖ ≤ 4 * ((cellSupDist y o : ℝ) + 1) * v) →
      |chartMixedDeriv a w (leftTranslate A (uniformField F F.top))
            ![Sum.inl (b.1.1, b.1.2, X), Sum.inl (b'.1.1, b'.1.2, X')] -
          chartMixedDeriv a (fun _ _ => 0) (uniformField F F.top)
            ![Sum.inl (b.1.1, b.1.2, X), Sum.inl (b'.1.1, b'.1.2, X')]| ≤
        P * Real.exp (-(r * chordBondDist F b b')) * (1 + (cellSupDist (enclosingCell b.1.1) o : ℝ)) * v := by
  classical
  obtain ⟨C₁, hC₁, hmove⟩ := hE a L c ha hL hL0 hc
  have hδ : 0 < c.δ₁ := hc.positivity.1
  obtain ⟨S, hS⟩ := hD L (c.δ₁ / 4) hL (by positivity)
  refine ⟨C₁ * |S| * (Cw + 16 * (1 + 4 / c.δ₁)), c.δ₁ / 2, by positivity, by positivity, ?_⟩
  intro F w A o v sT b b' X X' hF hv hX hX' hw hwv hAs hsT hA
  obtain ⟨hFL, n, hn, hsd⟩ := id hF
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hsd i]; omega
  have hs0 : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hn2 : 2 ≤ n := by omega
  set Bn : Finset (F.Site F.top × Fin 4) := finiteCells F ×ˢ (Finset.univ : Finset (Fin 4)) with hBn
  set u : F.Site F.depth → Fin 4 → imaginaryQuaternions :=
    fun z i => if (z, i) ∈ (chordBonds (finiteCells F)) then w z i else 0 with hu
  have hub : ∀ d, d ∉ (chordBonds (finiteCells F)) → u d.1 d.2 = 0 := fun d hd => by simp [hu, hd]
  have hvb : ∀ d, d ∉ Bn → A d.1 d.2 = 0 := fun d hd => by
    exfalso
    exact hd (Finset.mem_product.2 ⟨TopLevelSites.mem_finiteCells hs0 _, Finset.mem_univ _⟩)
  have hpts : ∀ (θ : F.Site F.depth → Fin 4 → ℝ) (ϑ : F.Site F.top → Fin 4 → ℝ),
      (∀ z i, 0 ≤ θ z i ∧ θ z i ≤ 1) → (∀ y i, 0 ≤ ϑ y i ∧ ϑ y i ≤ 1) →
      IsAdmissibleChartPoint L c.σA (fun z i => (fun _ _ => (0 : imaginaryQuaternions)) z i + θ z i • u z i)
        (leftTranslate (fun y i => ϑ y i • A y i) (uniformField F F.top)) := by
    intro θ ϑ hθ hϑ
    refine isAdmissibleChartPoint_of_small hcov hF hL he₀ hroom hs₁ hcold _ _ (fun d hd => ?_)
      (isSmallCurvature_leftTranslate A hAs hsT ϑ hϑ)
    have e : u d.1 d.2 = w d.1 d.2 := by
      have : (d.1, d.2) ∈ (chordBonds (finiteCells F)) := hd
      simp [hu, this]
    simp only [zero_add]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hθ d.1 d.2).1]
    have h1 := hθ d.1 d.2
    have h2 := hw d hd
    have h3 := norm_nonneg (w d.1 d.2)
    nlinarith
  have hstep := hmove F (fun _ _ => 0) u (uniformField F F.top) A (chordBonds (finiteCells F)) Bn
    (b.1.1, b.1.2, X) (b'.1.1, b'.1.2, X') hF hX hX' hub hvb hpts
  have hall := hcov F (hFL ▸ hL) fun i => by have := hs i; omega
  have hchart : ∀ d : F.Site F.depth × Fin 4, ¬ IsAxialTreeBond d → d ∈ (chordBonds (finiteCells F)) :=
    fun d hd => by
      have : d.1 + unitStep F.depth d.2 ∈ sitesOfCells (finiteCells F) F.depth := hall _
      simp [chordBonds, innerBonds, hall, hd]
  have ekern : chartMixedDeriv a (fun z i => (fun _ _ => (0 : imaginaryQuaternions)) z i + u z i)
        (leftTranslate A (uniformField F F.top)) ![Sum.inl (b.1.1, b.1.2, X), Sum.inl (b'.1.1, b'.1.2, X')] =
      chartMixedDeriv a w (leftTranslate A (uniformField F F.top))
        ![Sum.inl (b.1.1, b.1.2, X), Sum.inl (b'.1.1, b'.1.2, X')] := by
    unfold chartMixedDeriv
    rw [chartRestriction_congr a _ (w' := w) (fun x i ht => ?_)]
    have : (x, i) ∈ (chordBonds (finiteCells F)) := hchart _ ht
    simp [hu, this]
  rw [ekern] at hstep
  refine hstep.trans ?_
  set z : F.Cell := enclosingCell b.1.1 with hz
  set D : ℕ := cellSupDist z (enclosingCell b'.1.1) with hDd
  set δ := c.δ₁ with hδd
  have hD0 : (chordBondDist F b b') = (D : ℝ) := rfl
  have hSs : ∑ d : ↥(chordBonds (finiteCells F)),
      Real.exp (-(δ / 4 * (cellSupDist (enclosingCell d.1.1) z : ℝ))) ≤ |S| :=
    ((hS F n hFL hn2 hsd z).1).trans (le_abs_self _)
  have hSc : ∑ y ∈ finiteCells F, Real.exp (-(δ / 4 * (cellSupDist y z : ℝ))) ≤ |S| :=
    ((hS F n hFL hn2 hsd z).2).trans (le_abs_self _)
  have hE0 : 0 ≤ Real.exp (-(δ / 2 * (D : ℝ))) := (Real.exp_pos _).le
  have hexp1 : ∀ d : ℕ, Real.exp (-(δ * (max D d : ℕ))) ≤
      Real.exp (-(δ / 2 * (D : ℝ))) * Real.exp (-(δ / 2 * (d : ℝ))) :=
    fun d => exp_neg_mul_max_le δ hδ.le D d
  have hcomm : ∀ y : F.Cell, cellSupDist z y = cellSupDist y z := fun y => CellSums.cellSupDist_comm z y
  have hsum1 : ∑ d ∈ (chordBonds (finiteCells F)),
      C₁ * Real.exp (-(δ * (max D (cellSupDist z (enclosingCell d.1)) : ℕ))) * ‖u d.1 d.2‖ ≤
      C₁ * Real.exp (-(δ / 2 * (D : ℝ))) * |S| * (Cw * v) := by
    rw [← Finset.sum_coe_sort (chordBonds (finiteCells F))]
    calc ∑ d : ↥(chordBonds (finiteCells F)),
          C₁ * Real.exp (-(δ * (max D (cellSupDist z (enclosingCell d.1.1)) : ℕ))) * ‖u d.1.1 d.1.2‖
        ≤ ∑ d : ↥(chordBonds (finiteCells F)), C₁ * Real.exp (-(δ / 2 * (D : ℝ))) * (Cw * v) *
            Real.exp (-(δ / 4 * (cellSupDist (enclosingCell d.1.1) z : ℝ))) := by
          refine Finset.sum_le_sum fun d _ => ?_
          have e : u d.1.1 d.1.2 = w d.1.1 d.1.2 := by
            have : (d.1.1, d.1.2) ∈ (chordBonds (finiteCells F)) := d.2
            simp [hu, this]
          have h1 := hexp1 (cellSupDist z (enclosingCell d.1.1))
          rw [hcomm] at h1
          have h2 : Real.exp (-(δ / 2 * (cellSupDist (enclosingCell d.1.1) z : ℝ))) ≤
              Real.exp (-(δ / 4 * (cellSupDist (enclosingCell d.1.1) z : ℝ))) := by
            apply Real.exp_le_exp.2
            have : 0 ≤ δ / 4 * (cellSupDist (enclosingCell d.1.1) z : ℝ) := by positivity
            linarith
          have h3 := hwv d.1 d.2
          rw [e, hcomm]
          have h4 : 0 ≤ Cw * v := by positivity
          have h5 := norm_nonneg (w d.1.1 d.1.2)
          calc C₁ * Real.exp (-(δ * (max D (cellSupDist (enclosingCell d.1.1) z) : ℕ))) * ‖w d.1.1 d.1.2‖
              ≤ C₁ * (Real.exp (-(δ / 2 * (D : ℝ))) *
                  Real.exp (-(δ / 4 * (cellSupDist (enclosingCell d.1.1) z : ℝ)))) * (Cw * v) := by
                gcongr
                exact h1.trans (mul_le_mul_of_nonneg_left h2 hE0)
            _ = _ := by ring
      _ = C₁ * Real.exp (-(δ / 2 * (D : ℝ))) * (Cw * v) *
            ∑ d : ↥(chordBonds (finiteCells F)),
              Real.exp (-(δ / 4 * (cellSupDist (enclosingCell d.1.1) z : ℝ))) := by rw [Finset.mul_sum]
      _ ≤ C₁ * Real.exp (-(δ / 2 * (D : ℝ))) * (Cw * v) * |S| := by
          apply mul_le_mul_of_nonneg_left hSs
          positivity
      _ = _ := by ring
  have hsum2 : ∑ d ∈ Bn, C₁ * Real.exp (-(δ * (max D (cellSupDist z d.1) : ℕ))) * ‖A d.1 d.2‖ ≤
      C₁ * Real.exp (-(δ / 2 * (D : ℝ))) * |S| * (16 * (1 + 4 / δ) * (1 + (cellSupDist z o : ℝ)) * v) := by
    rw [hBn, Finset.sum_product]
    have hrow : ∀ y ∈ finiteCells F, ∑ i : Fin 4,
        C₁ * Real.exp (-(δ * (max D (cellSupDist z y) : ℕ))) * ‖A y i‖ ≤
        C₁ * Real.exp (-(δ / 2 * (D : ℝ))) * (16 * (1 + 4 / δ) * (1 + (cellSupDist z o : ℝ)) * v) *
          Real.exp (-(δ / 4 * (cellSupDist y z : ℝ))) := by
      intro y _
      have h1 := hexp1 (cellSupDist z y)
      rw [hcomm] at h1
      have htri : (cellSupDist y o : ℝ) ≤ (cellSupDist y z : ℝ) + (cellSupDist z o : ℝ) := by
        exact_mod_cast CellSums.cellSupDist_triangle hs0 y z o
      set t : ℝ := (cellSupDist y z : ℝ) with ht
      have ht0 : 0 ≤ t := by positivity
      set g : ℝ := (cellSupDist z o : ℝ) with hg
      have hg0 : 0 ≤ g := by positivity
      have hAb : ∀ i, ‖A y i‖ ≤ 4 * ((1 + t) * (1 + g)) * v := fun i => by
        refine (hA y i).trans ?_
        have : (cellSupDist y o : ℝ) + 1 ≤ (1 + t) * (1 + g) := by nlinarith
        gcongr
      have h2 := one_add_mul_exp_le hδ ht0
      have hterm : ∀ i : Fin 4, C₁ * Real.exp (-(δ * (max D (cellSupDist z y) : ℕ))) * ‖A y i‖ ≤
          C₁ * Real.exp (-(δ / 2 * (D : ℝ))) * (4 * (1 + 4 / δ) * (1 + g) * v) * Real.exp (-(δ / 4 * t)) := by
        intro i
        rw [hcomm]
        calc C₁ * Real.exp (-(δ * (max D (cellSupDist y z) : ℕ))) * ‖A y i‖
            ≤ C₁ * (Real.exp (-(δ / 2 * (D : ℝ))) * Real.exp (-(δ / 2 * t))) *
                (4 * ((1 + t) * (1 + g)) * v) := by
              exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC₁.le) (hAb i) (norm_nonneg _) (by positivity)
          _ = C₁ * Real.exp (-(δ / 2 * (D : ℝ))) * (4 * (1 + g) * v) *
                ((1 + t) * Real.exp (-(δ / 2 * t))) := by ring
          _ ≤ C₁ * Real.exp (-(δ / 2 * (D : ℝ))) * (4 * (1 + g) * v) *
                ((1 + 4 / δ) * Real.exp (-(δ / 4 * t))) := by
              apply mul_le_mul_of_nonneg_left h2
              positivity
          _ = _ := by ring
      calc ∑ i : Fin 4, C₁ * Real.exp (-(δ * (max D (cellSupDist z y) : ℕ))) * ‖A y i‖
          ≤ ∑ _i : Fin 4, C₁ * Real.exp (-(δ / 2 * (D : ℝ))) * (4 * (1 + 4 / δ) * (1 + g) * v) *
              Real.exp (-(δ / 4 * t)) :=
            Finset.sum_le_sum fun i _ => hterm i
        _ = _ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    calc ∑ y ∈ finiteCells F, ∑ i : Fin 4, C₁ * Real.exp (-(δ * (max D (cellSupDist z y) : ℕ))) * ‖A y i‖
        ≤ ∑ y ∈ finiteCells F, C₁ * Real.exp (-(δ / 2 * (D : ℝ))) *
            (16 * (1 + 4 / δ) * (1 + (cellSupDist z o : ℝ)) * v) *
            Real.exp (-(δ / 4 * (cellSupDist y z : ℝ))) := Finset.sum_le_sum hrow
      _ = C₁ * Real.exp (-(δ / 2 * (D : ℝ))) * (16 * (1 + 4 / δ) * (1 + (cellSupDist z o : ℝ)) * v) *
            ∑ y ∈ finiteCells F, Real.exp (-(δ / 4 * (cellSupDist y z : ℝ))) := by rw [Finset.mul_sum]
      _ ≤ C₁ * Real.exp (-(δ / 2 * (D : ℝ))) * (16 * (1 + 4 / δ) * (1 + (cellSupDist z o : ℝ)) * v) * |S| := by
          apply mul_le_mul_of_nonneg_left hSc
          positivity
      _ = _ := by ring
  have hgt : (0 : ℝ) ≤ (cellSupDist z o : ℝ) := by positivity
  have hfin : C₁ * Real.exp (-(δ / 2 * (D : ℝ))) * |S| * (Cw * v) +
      C₁ * Real.exp (-(δ / 2 * (D : ℝ))) * |S| * (16 * (1 + 4 / δ) * (1 + (cellSupDist z o : ℝ)) * v) ≤
      C₁ * |S| * (Cw + 16 * (1 + 4 / δ)) * Real.exp (-(δ / 2 * chordBondDist F b b')) *
        (1 + (cellSupDist z o : ℝ)) * v := by
    rw [hD0]
    have h0 : 0 ≤ C₁ * Real.exp (-(δ / 2 * (D : ℝ))) * |S| * v := by positivity
    have h1 : 0 ≤ Cw * (cellSupDist z o : ℝ) := by positivity
    nlinarith [mul_nonneg h0 h1]
  exact (add_le_add hsum1 hsum2).trans hfin
end KernelEntries
section AgainstUniform
variable {L u n : ℕ} [NeZero L] [NeZero n]
open Classical in
private theorem bondCoordinateHessian_near_trivial (hK : ChartEnergyKernelBound)
    (hCol : FlatHessian.HessianAtFlatIsColourDiagonal)
    {a : ℝ} {c : ColdChainParameters} (ha : 1 ≤ a) (hL : Odd L) (hL0 : 2 ^ 40 ≤ L) (hc : c.Admissible a L)
    (hF : IsBlockTorus L (torusFrame L u n))
    (w : (torusFrame L u n).Site (torusFrame L u n).depth → Fin 4 → imaginaryQuaternions)
    (Vt : (torusFrame L u n).GaugeField (torusFrame L u n).top)
    (hsm : IsAdmissibleChartPoint L c.σA w Vt)
    (hfl : IsAdmissibleChartPoint L c.σA (fun _ _ => 0) (uniformField (torusFrame L u n) (torusFrame L u n).top))
    (hsym : ∀ b b', trivialHessian a L u n b b' = trivialHessian a L u n b' b)
    (Dk : ChartBondIndex L u n → ChartBondIndex L u n → ℝ)
    (hbd : ∀ (b b' : ChartBondIndex L u n) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
      |chartMixedDeriv a w Vt ![Sum.inl (b.1.1, b.1.2, X), Sum.inl (b'.1.1, b'.1.2, X')] -
        chartMixedDeriv a (fun _ _ => 0) (uniformField (torusFrame L u n) (torusFrame L u n).top)
          ![Sum.inl (b.1.1, b.1.2, X), Sum.inl (b'.1.1, b'.1.2, X')]| ≤ Dk b b')
    (b : ChartBondIndex L u n) (e : Fin 3) (r : ChartBondIndex L u n × Fin 3) :
    |bondCoordinateHessian (chartedEnergyAt a w Vt) (b, e) r -
        (if r.2 = e then trivialHessian a L u n b r.1 else 0)| ≤ Dk r.1 b := by
  obtain ⟨Ck, hCk, hker⟩ := hK a L c ha hL hL0 hc
  have hEC : ContDiffAt ℝ 3 (chartedEnergyAt a w Vt) 0 :=
    contDiffAt_chartedEnergyAt fun k q => (hker _ w Vt hF hsm k q).1
  have hd : DifferentiableAt ℝ (fderiv ℝ (chartedEnergyAt a w Vt)) 0 :=
    (hEC.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have e1 : bondCoordinateHessian (chartedEnergyAt a w Vt) (b, e) r =
      chartMixedDeriv a w Vt ![chordDirection r.1 (EuclideanSpace.single r.2 1),
        chordDirection b (EuclideanSpace.single e 1)] := by
    rw [chartMixedDeriv_chordDirections hEC]
    show secondDerivAlong (chartedEnergyAt a w Vt) 0 (bondCoordinateVector (b, e)) (bondCoordinateVector r) = _
    unfold secondDerivAlong
    have h1 := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const (bondCoordinateVector (b, e) : BondField _)
      (0 : BondField _))).fderiv
    rw [h1]
    simp [bondCoordinateVector]
  have e2 : chartMixedDeriv a (fun _ _ => 0) (uniformField (torusFrame L u n) (torusFrame L u n).top)
      ![chordDirection r.1 (EuclideanSpace.single r.2 1), chordDirection b (EuclideanSpace.single e 1)] =
      if r.2 = e then trivialHessian a L u n b r.1 else 0 := by
    have h1 := hCol a L c ha hL hL0 hc (torusFrame L u n) r.1.1 b.1 r.2 e hF r.1.2 b.2
    have h2 := trivialHessian_eq_chartMixedDeriv a L u n r.1 b ((hker _ _ _ hF hfl _ _).1)
    rw [hsym, h2]
    exact h1
  rw [e1, ← e2]
  exact hbd r.1 b _ _ (norm_colourUnit r.2) (norm_colourUnit e)
end AgainstUniform
section TorusTop
variable {L u n : ℕ} [NeZero L] [NeZero n]
private theorem bondCoordinateHessian_expField (hK : ChartEnergyKernelBound)
    (hCol : FlatHessian.HessianAtFlatIsColourDiagonal)
    (hcov : BlocksCoverLowerLevel) {a : ℝ} {c : ColdChainParameters} (ha : 1 ≤ a) (hL : Odd L) (hL0 : 2 ^ 40 ≤ L)
    (hc : c.Admissible a L) {s₁ e₀ Cw P r : ℝ} (hs₁ : 0 < s₁) (he₀ : 0 ≤ e₀) (hroom : e₀ ≤ 1 / (64 * (L : ℝ)))
    (hcold : s₁ + 8 * e₀ < c.σA)
    (hnear : ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
      (A : F.Site F.top → Fin 4 → imaginaryQuaternions) (o : F.Cell)
      (v sT : ℝ) (b b' : ↥(chordBonds (finiteCells F))) (X X' : imaginaryQuaternions),
      IsBlockTorus L F → 0 ≤ v → ‖X‖ = 1 → ‖X'‖ = 1 →
      (∀ d ∈ chordBonds (finiteCells F), ‖w d.1 d.2‖ ≤ e₀) →
      (∀ d ∈ chordBonds (finiteCells F), ‖w d.1 d.2‖ ≤ Cw * v) →
      (∀ y i, ‖A y i‖ ≤ sT) → 4 * sT < s₁ → (∀ y i, ‖A y i‖ ≤ 4 * ((cellSupDist y o : ℝ) + 1) * v) →
      |chartMixedDeriv a w (leftTranslate A (uniformField F F.top))
            ![Sum.inl (b.1.1, b.1.2, X), Sum.inl (b'.1.1, b'.1.2, X')] -
          chartMixedDeriv a (fun _ _ => 0) (uniformField F F.top)
            ![Sum.inl (b.1.1, b.1.2, X), Sum.inl (b'.1.1, b'.1.2, X')]| ≤
        P * Real.exp (-(r * chordBondDist F b b')) * (1 + (cellSupDist (enclosingCell b.1.1) o : ℝ)) * v)
    (h64 : 64 ≤ n) (hsym : ∀ b b', trivialHessian a L u n b b' = trivialHessian a L u n b' b)
    (B : TorusBond n → imaginaryQuaternions) (O : TorusSite n) {v sT : ℝ} (hv : 0 ≤ v)
    (hB1 : ∀ d, ‖B d‖ ≤ 4 * ((TorusFields.supDist d.1 O : ℝ) + 1) * v) (hB2 : ∀ d, ‖B d‖ ≤ sT) (hsT : 4 * sT < s₁)
    (w : (torusFrame L u n).Site (torusFrame L u n).depth → Fin 4 → imaginaryQuaternions)
    (hw1 : ∀ d ∈ chordBonds (finiteCells (torusFrame L u n)), ‖w d.1 d.2‖ ≤ e₀)
    (hw2 : ∀ d ∈ chordBonds (finiteCells (torusFrame L u n)), ‖w d.1 d.2‖ ≤ Cw * v)
    (b : ChartBondIndex L u n) (e : Fin 3) (q : ChartBondIndex L u n × Fin 3) :
    |bondCoordinateHessian (chartedEnergyAt a w
          (readAtLevel (torusFrame L u n) (torusFrame L u n).top (expField 1 B))) (b, e) q -
        (if q.2 = e then trivialHessian a L u n b q.1 else 0)| ≤
      P * Real.exp (-(r * chordBondDist (torusFrame L u n) q.1 b)) *
        (1 + (cellSupDist (enclosingCell q.1.1.1)
          (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top O) : ℝ)) * v := by
  have hF : IsBlockTorus L (torusFrame L u n) := ⟨rfl, n, h64, fun _ => rfl⟩
  set A : (torusFrame L u n).Site (torusFrame L u n).top → Fin 4 → imaginaryQuaternions :=
    fun y i => B (siteOfCell y, i) with hA
  have hVt : readAtLevel (torusFrame L u n) (torusFrame L u n).top (expField 1 B) =
      leftTranslate A (uniformField (torusFrame L u n) (torusFrame L u n).top) := by
    funext y i
    rw [readAtLevel_torusFrame]
    simp [leftTranslate, uniformField, expField, hA]
  have hAs : ∀ y i, ‖A y i‖ ≤ sT := fun y i => hB2 _
  have hAo : ∀ y i, ‖A y i‖ ≤
      4 * ((cellSupDist y (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top O) : ℝ) + 1) * v := by
    intro y i
    rw [cellSupDist_torusFrame, siteOfCell_torusSiteInFrame]
    exact hB1 (siteOfCell y, i)
  have hcoldV := isSmallCurvature_leftTranslate A hAs hsT (fun _ _ => 1) (fun _ _ => ⟨zero_le_one, le_rfl⟩)
  simp only [one_smul] at hcoldV
  have hsm : IsAdmissibleChartPoint L c.σA w
      (leftTranslate A (uniformField (torusFrame L u n) (torusFrame L u n).top)) :=
    isAdmissibleChartPoint_of_small hcov hF hL he₀ hroom hs₁.le hcold _ _ hw1 hcoldV
  have hflc : IsSmallCurvature s₁ (uniformField (torusFrame L u n) (torusFrame L u n).top) := by
    have h1 := isSmallCurvature_leftTranslate (F := torusFrame L u n) (fun _ _ => (0 : imaginaryQuaternions))
      (sT := 0) (s₁ := s₁) (fun _ _ => by simp) (by linarith)
      (fun _ _ => 0) (fun _ _ => ⟨le_rfl, zero_le_one⟩)
    simp only [smul_zero] at h1
    rwa [leftTranslate_zero] at h1
  have hfl : IsAdmissibleChartPoint L c.σA (fun _ _ => 0)
      (uniformField (torusFrame L u n) (torusFrame L u n).top) :=
    isAdmissibleChartPoint_of_small hcov hF hL he₀ hroom hs₁.le hcold _ _ (fun d _ => by simpa using he₀) hflc
  rw [hVt]
  exact bondCoordinateHessian_near_trivial hK hCol ha hL hL0 hc hF w _ hsm hfl hsym
    (fun b₁ b₂ => P * Real.exp (-(r * chordBondDist (torusFrame L u n) b₁ b₂)) *
      (1 + (cellSupDist (enclosingCell b₁.1.1)
        (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top O) : ℝ)) * v)
    (fun b₁ b₂ X X' hX hX' => hnear _ w A _ v sT b₁ b₂ X X' hF hv hX hX' hw1 hw2 hAs hsT hAo) b e q
end TorusTop
end HessianOverExpFieldSteps
open HessianOverExpFieldSteps in
theorem hessianOverExpField_proof (hE : ChartResponse.HessianEntryLipschitz)
    (hCol : FlatHessian.HessianAtFlatIsColourDiagonal)
    (hK : ChartEnergyKernelBound) (hD : decaySumOnTorusStatement) (hcov : BlocksCoverLowerLevel) :
    hessianOverExpFieldStatement := by
  intro a L _ c ha hL hL0 hc s₁ e₀ Cw hs₁ he₀ hroom hcold hCw
  obtain ⟨P, r, hP, hr, hnear⟩ :=
    chartMixedDeriv_near_uniform hE hD hcov ha hL hL0 hc hs₁.le he₀ hroom hcold hCw
  refine ⟨P, r, hP, hr, ?_⟩
  intro u n _ h64 hsym B O v sT hv hB1 hB2 hsT w hw1 hw2 b e q
  exact bondCoordinateHessian_expField hK hCol hcov ha hL hL0 hc hs₁ he₀ hroom hcold hnear h64 hsym B O hv
    hB1 hB2 hsT w hw1 hw2 b e q
end MomentLaw
end YangMills.Construction
end
