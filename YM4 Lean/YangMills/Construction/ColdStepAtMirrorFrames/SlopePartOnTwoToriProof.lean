import YangMills.Construction.ClusterExpansionOfAStep.BondInCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.CommonBondsOfTwoToriProof
import YangMills.Construction.ColdStepAtMirrorFrames.GapPartOnTwoToriProof
import YangMills.Construction.ColdStepAtMirrorFrames.SlopePartOnTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.SlopesOfAChartInCoordinates
import YangMills.Construction.RunningCouplingSlope.LocalMatrixOfABoundedSymbolProof
import YangMills.Construction.SummableBoundsOfTheFlow.MoveOfTheTopAlongItsFieldProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace SlopeComponentBounds
open ChartSlopes
section
variable {F : BlockFrame}
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
theorem mem_centredCube_odd (R : ℕ) (h : Fin 4 → ℤ) : h ∈ centredCube (2 * R + 1) ↔ ∀ i, |h i| ≤ (R : ℤ) := by apply _root_.YangMills.Construction.HoleSavings.mem_centredCube_odd <;> assumption
theorem siteOfCoords_add_injective {n : ℕ} (hn : 0 < n) (hs : ∀ i, F.extent i = n) {Y : F.Cell} {c c' : Fin 4 → ℤ}
    (h : ∀ i, 2 * |c i - c' i| < n) (he : Y + siteOfCoords F.top c = Y + siteOfCoords F.top c') : c = c' := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TorusBonds.siteOfCoords_add_injective <;> assumption
theorem fineBondAt_cell_offset (hS : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) (Y : F.Cell)
    {h o : Fin 4 → ℤ} (i : Fin 4) (ho : o ∈ centredCube F.blockSide) :
    enclosingCell (fineBondAt Y h o i).1 = Y + siteOfCoords F.top h ∧ cellOffset (fineBondAt Y h o i).1 = o :=
  (hS F hL hs).1 _ _ ho
theorem fineBondAt_mem_chordBonds_transfer {F₂ : BlockFrame} (hS : SiteDecomposition)
    (hC : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hL₂ : Odd F₂.blockSide) (hLL : F.blockSide = F₂.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (hs₂ : ∀ i, 2 ≤ F₂.extent i) (Y : F.Cell) (Y₂ : F₂.Cell)
    {h o : Fin 4 → ℤ} {i : Fin 4} (ho : o ∈ centredCube F.blockSide)
    (hb : fineBondAt Y h o i ∈ chordBonds (finiteCells F)) :
    fineBondAt Y₂ h o i ∈ chordBonds (finiteCells F₂) := by
  exact _root_.YangMills.Construction.ColdStepAtMirrorFrames.TorusBonds.fineBondAt_mem_chordBonds_transfer (F := F) (F₂ := F₂)
    hS hC hL hL₂ hLL hs hs₂ Y Y₂ ho hb
variable {F' : BlockFrame} {Y : F.Cell} {Y' : F'.Cell}
theorem mem_commonBondOffsets {R : ℕ} {q : (Fin 4 → ℤ) × (Fin 4 → ℤ) × Fin 4} (hq : q ∈ commonBondOffsets Y Y' R) :
    q.1 ∈ centredCube (2 * R + 1) ∧ q.2.1 ∈ centredCube F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TorusBonds.mem_commonBondOffsets <;> assumption
section ZeroExtension
variable {Λ ι : Type} [Fintype Λ] [Fintype ι] [DecidableEq ι]
theorem zeroExtensionL_apply_self {e : Λ → ι} (he : Function.Injective e) (ζ : BondField Λ) (l : Λ) :
    zeroExtensionL e ζ (e l) = ζ l := by apply _root_.YangMills.SharedProofs.p32108 <;> assumption
theorem zeroExtensionL_apply_of_not_mem {e : Λ → ι} (ζ : BondField Λ) {b : ι} (hb : b ∉ Set.range e) :
    zeroExtensionL e ζ b = 0 := by
  have hx : ¬ ∃ l', e l' = b := fun ⟨l, hl⟩ => hb ⟨l, hl⟩
  simp only [zeroExtensionL, ContinuousLinearMap.coe_pi', dif_neg hx]
  rfl
end ZeroExtension
theorem toImaginary_zero : toImaginary (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by apply _root_.YangMills.Construction.BondCoordinates.toImaginary_zero <;> assumption
theorem toImaginary_smul (u : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : toImaginary (u • v) = u • toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_smul <;> assumption
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem chartedSlope_zero (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (b : F.Site F.depth × Fin 4) :
    chartedSlope a w V b 0 = 0 := by
  unfold chartedSlope
  simp
section Embedded
variable {ι : Type} [Fintype ι]
theorem stepCoordinates_smul_zeroExtension [DecidableEq ↥(chordBonds (finiteCells F))]
    {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) (ζ : BondField ι) (u : ℝ) :
    stepCoordinates (u • zeroExtensionL j ζ) = fun x i => u • bondBumps j (fun q => toImaginary (ζ q)) x i := by
  classical
  funext x i
  unfold stepCoordinates
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · rw [dif_pos h]
    by_cases hq : ∃ q, j q = ⟨(x, i), h⟩
    · obtain ⟨q, hq⟩ := hq
      have e1 : x = (j q).1.1 := by rw [hq]
      have e2 : i = (j q).1.2 := by rw [hq]
      simp only [Pi.smul_apply]
      rw [← hq, zeroExtensionL_apply_self hj, toImaginary_smul]
      congr 1
      rw [e1, e2, bondBumps_apply_self hj]
    · have hoff : (⟨(x, i), h⟩ : ↥(chordBonds (finiteCells F))) ∉ Set.range j := fun ⟨q, hq'⟩ => hq ⟨q, hq'⟩
      simp only [Pi.smul_apply]
      rw [zeroExtensionL_apply_of_not_mem ζ hoff, smul_zero, toImaginary_zero, bondBumps_apply_of_ne, smul_zero]
      intro q hq'
      exact hq ⟨q, Subtype.ext hq'.symm⟩
  · rw [dif_neg h, bondBumps_apply_of_ne, smul_zero]
    intro q hq'
    exact h (hq' ▸ (j q).2)
theorem slopeComponent_zeroExtension [DecidableEq ↥(chordBonds (finiteCells F))] (star : Bool) (a ρA x : ℝ) (m : ℕ)
    (V : F.GaugeField F.top)
    {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j) (ζ : BondField ι) (Z : F.Cell)
    (P : ι → Prop) [DecidablePred P] (hP : ∀ q, enclosingCell (j q).1.1 = Z ↔ P q) :
    slopeComponent star a ρA x m Z V (zeroExtensionL j ζ) = x * ∑ q, if P q then
      ∫ v in (0 : ℝ)..1, chartedSlope a (shiftChart (frameCoordField star a ρA m V)
        fun x i => v • bondBumps j (fun q => toImaginary (ζ q)) x i) V (j q).1 (toImaginary (ζ q)) else 0 := by
  classical
  unfold slopeComponent
  congr 1
  symm
  refine Fintype.sum_of_injective j hj _ _ ?_ ?_
  · intro b hb
    rw [zeroExtensionL_apply_of_not_mem ζ hb, toImaginary_zero]
    simp [chartedSlope_zero]
  · intro q
    rw [zeroExtensionL_apply_self hj]
    by_cases hq : P q
    · rw [if_pos hq, if_pos ((hP q).mpr hq)]
      refine intervalIntegral.integral_congr fun v _ => ?_
      have e : coordsAboveFrame star a ρA m V (v • zeroExtensionL j ζ) = shiftChart (frameCoordField star a ρA m V)
          fun x i => v • bondBumps j (fun q => toImaginary (ζ q)) x i := by
        funext x i
        simp only [coordsAboveFrame, shiftChart, frameCoordField]
        rw [stepCoordinates_smul_zeroExtension hj]
      simp only [e]
    · rw [if_neg hq, if_neg (fun h => hq ((hP q).mp h))]
theorem weightedSqNormAt_zeroExtension [DecidableEq ↥(chordBonds (finiteCells F))] (κ : ℝ)
    {j : ι → ↥(chordBonds (finiteCells F))}
    (hj : Function.Injective j) (ζ : BondField ι) (Z : F.Cell) :
    weightedSqNormAt κ (chordBondCell F) (cellDistReal F) Z (zeroExtensionL j ζ) =
      ∑ q, Real.exp (-(2 ^ 6 * κ * cellDistReal F Z (chordBondCell F (j q)))) * ‖ζ q‖ ^ 2 := by
  classical
  unfold weightedSqNormAt
  symm
  refine Fintype.sum_of_injective j hj _ _ ?_ ?_
  · intro b hb
    rw [zeroExtensionL_apply_of_not_mem ζ hb]
    simp
  · intro q
    rw [zeroExtensionL_apply_self hj]
end Embedded
theorem isSmallCurvature_mono {j : ℕ} {s s' : ℝ} {X : F.GaugeField j} (h : IsSmallCurvature s X) (hs : s ≤ s') :
    IsSmallCurvature s' X :=
  fun p hp => (h p hp).trans_le hs
theorem isAdmissibleChartPoint_shiftChart (hexp : QuaternionExp.ExpUnitLipschitzInjective)
    (hhol : PathHolonomyLipschitz)
    {L : ℕ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top} {s₁ s m P : ℝ}
    (hw : ∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ P) (hP : P + m ≤ 1 / (64 * (L : ℝ))) (hm0 : 0 ≤ m)
    (hc : IsSmallCurvature s₁ (chartedField w V)) (hs : s₁ + 4 * m ≤ s)
    {dw : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hdw : ∀ x i, ‖dw x i‖ ≤ m) : IsAdmissibleChartPoint L s (shiftChart w dw) V where
  coord_small := fun b hb => by
    have h1 := norm_add_le (w b.1 b.2) (dw b.1 b.2)
    have h2 := hw b hb
    have h3 := hdw b.1 b.2
    simp only [shiftChart]
    linarith
  small_curvature := isSmallCurvature_mono (isSmallCurvature_shiftChart hexp hhol hm0 hdw hc) hs
theorem slopeControl_of_admissible {a : ℝ} {L : ℕ} {c : ColdChainParameters} {Ck : ℕ → ℝ}
    (hCk : ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
        IsBlockTorus L F →
        IsAdmissibleChartPoint L c.σA w V → ∀ (k : ℕ) (q : Fin k → ChartDirection F),
          AnalyticAt ℝ (chartRestriction a w V q) 0 ∧
          (2 ≤ k → (∀ l, ‖directionVector (q l)‖ = 1) →
            |chartMixedDeriv a w V q| ≤ Ck k * Real.exp (-(c.δ₁ * directionDiameter q))))
    {m : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top} (hF : IsBlockTorus L F)
    (h : ∀ dw : F.Site F.depth → Fin 4 → imaginaryQuaternions, (∀ x i, ‖dw x i‖ ≤ m) →
      IsAdmissibleChartPoint L c.σA (shiftChart w dw) V) :
    SlopeControl a c.δ₁ (Ck 2) (Ck 3) m w V where
  analytic := fun dw hdw => (hCk F _ V hF (h dw hdw) _ (chartDirections F)).1
  secondKernel := fun dw hdw q' hu => (hCk F _ V hF (h dw hdw) 2 q').2 le_rfl hu
  thirdKernel := fun dw hdw q' hu => (hCk F _ V hF (h dw hdw) 3 q').2 (by norm_num) hu
theorem agreeOnBall_mono {F' : BlockFrame} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell}
    {Y' : F'.Cell} {r r' : ℕ}
    (h : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r) (hr : r' ≤ r) :
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r' := by apply _root_.YangMills.SharedProofs.p37458 <;> assumption
end
section
variable {F F' : BlockFrame}
theorem cellSupDist_self (y : F.Cell) : cellSupDist y y = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem abs_slope_difference_sub_le_weighted (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i)
    (hL' : Odd F'.blockSide) (hs' : ∀ i, 2 ≤ F'.extent i) {a δ₁ C2 C3 m Mh τ D P Pn R : ℝ}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top}
    {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions} {V' : F'.GaugeField F'.top}
    (hS : SlopeControl a δ₁ C2 C3 m w V) (hS' : SlopeControl a δ₁ C2 C3 m w' V') (hδ₁ : 0 ≤ δ₁) (hC2 : 0 ≤ C2)
    (hC3 : 0 ≤ C3)
    (hτ : 0 < τ) {ι : Type} [Fintype ι]
    {j : ι → ↥(chordBonds (finiteCells F))} {j' : ι → ↥(chordBonds (finiteCells F'))}
    (hj : Function.Injective j) (hj' : Function.Injective j') (c dc : ι → imaginaryQuaternions)
    (hDc : ∀ q, ‖dc q‖ ≤ D) (hP0 : 0 ≤ P) (hP : ∀ q, ‖c q‖ ≤ P) (hm : D + P + τ ≤ m) (hD0 : 0 ≤ D) (hR0 : 0 ≤ R)
    {b : F.Site F.depth × Fin 4} {b' : F'.Site F'.depth × Fin 4}
    (hb : b ∈ chordBonds (finiteCells F)) (hb' : b' ∈ chordBonds (finiteCells F'))
    (hdist : ∀ q, cellSupDist (enclosingCell (j' q).1.1) (enclosingCell b'.1) =
      cellSupDist (enclosingCell (j q).1.1) (enclosingCell b.1))
    (e : imaginaryQuaternions)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ q, ∀ e₂ : imaginaryQuaternions, ‖e₂‖ = 1 → ∀ s ∈ Set.Icc (0 : ℝ) τ,
      |chartedSlope a (shiftChart w fun x i => (bondBumps j dc x i + t • bondBumps j c x i) +
          s • bondBump (j q).1 e₂ x i) V b e -
        chartedSlope a (shiftChart w' fun x i => ((0 : imaginaryQuaternions) + t • bondBumps j' c x i) +
          s • bondBump (j' q).1 e₂ x i) V' b' e| ≤ Mh * ‖e‖)
    (hPn : 2 * Mh / τ + 2 * (27 * C3) * τ ≤ Pn)
    (hR : ∀ q, min Pn (18 * C2 * Real.exp (-(δ₁ * cellSupDist (enclosingCell (j q).1.1) (enclosingCell b.1)))) ≤
      R * Real.exp (-(δ₁ / 2 * cellSupDist (enclosingCell (j q).1.1) (enclosingCell b.1))))
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    |(chartedSlope a (shiftChart w fun x i => u • bondBumps j c x i) V b e -
        chartedSlope a (shiftChart w' fun x i => u • bondBumps j' c x i) V' b' e) -
      (chartedSlope a (shiftChart w fun _ _ => 0) V b e - chartedSlope a (shiftChart w' fun _ _ => 0) V' b' e)| ≤
      ‖e‖ * ((27 * C3 * (D * ∑ q, Real.exp (-(δ₁ / 2 * cellSupDist (enclosingCell (j q).1.1) (enclosingCell b.1)))) +
        R) * ∑ q, ‖c q‖ * Real.exp (-(δ₁ / 2 * cellSupDist (enclosingCell (j q).1.1) (enclosingCell b.1)))) := by
  obtain ⟨wq, hwq⟩ : ∃ wq : ι → ℝ,
      wq = fun q => Real.exp (-(δ₁ / 2 * cellSupDist (enclosingCell (j q).1.1) (enclosingCell b.1))) := ⟨_, rfl⟩
  have hw0 : ∀ q, 0 ≤ wq q := fun q => by rw [hwq]; exact (Real.exp_pos _).le
  have e1 : ∀ q, Real.exp (-(δ₁ / 2 * cellSupDist (enclosingCell (j q).1.1) (enclosingCell b.1))) = wq q :=
    fun q => by rw [hwq]
  simp only [e1] at hR ⊢
  have h := abs_slope_difference_sub_le hCE hL hs hL' hs' (M := Mh * ‖e‖) (D := D) (P := P) hS hS' hδ₁ hC2 hC3 hτ
    hj hj' c (bondBumps j dc)
    (norm_bondBumps_le hj hD0 hDc) hP0 hP hm hD0 hb hb' hdist e hM u hu
  refine h.trans ?_
  obtain ⟨Wc, hWc⟩ : ∃ Wc, Wc = ∑ q, ‖c q‖ * wq q := ⟨_, rfl⟩
  obtain ⟨Sw, hSw⟩ : ∃ Sw, Sw = ∑ q, wq q := ⟨_, rfl⟩
  rw [← hWc, ← hSw]
  have hWc0 : 0 ≤ Wc := by
    rw [hWc]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (norm_nonneg _) (hw0 q)
  have hSw0 : 0 ≤ Sw := by
    rw [hSw]
    exact Finset.sum_nonneg fun q _ => hw0 q
  have hn : Calculus.weightedNorm (cellWeight (δ₁ / 2) (enclosingCell b.1)) (chartOffset (bondBumps j c)) ≤
      3 * Wc := by
    rw [chartOffset_bondBumps]
    refine (weightedNorm_sum_le (cellWeight_nonneg _ _) _ _).trans ?_
    rw [hWc, Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    have := _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSlopes.weightedNorm_bondBumpCoords_le (δ₁ / 2) (enclosingCell b.1) (j q).1 (j q).2 (c q)
    rw [← mul_assoc, ← e1 q]
    exact this
  have hd : Calculus.weightedNorm (cellWeight (δ₁ / 2) (enclosingCell b.1)) (chartOffset (bondBumps j dc)) ≤
      3 * (D * Sw) := by
    rw [chartOffset_bondBumps]
    refine (weightedNorm_sum_le (cellWeight_nonneg _ _) _ _).trans ?_
    rw [hSw, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    have h1 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSlopes.weightedNorm_bondBumpCoords_le (δ₁ / 2) (enclosingCell b.1) (j q).1 (j q).2 (dc q)
    rw [e1 q] at h1
    have h2 : 3 * ‖dc q‖ * wq q ≤ 3 * (D * wq q) := by
      have := mul_le_mul_of_nonneg_right (hDc q) (hw0 q)
      linarith
    exact h1.trans h2
  have hn0 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSlopes.weightedNorm_nonneg (cellWeight_nonneg (δ₁ / 2) (enclosingCell b.1)) (chartOffset (bondBumps j c))
  have hd0 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartSlopes.weightedNorm_nonneg (cellWeight_nonneg (δ₁ / 2) (enclosingCell b.1)) (chartOffset (bondBumps j dc))
  have hτ0 := hτ.le
  have t2 : ∑ q, ‖c q‖ * min (2 * (Mh * ‖e‖) / τ + 2 * (27 * C3 * ‖e‖) * τ)
      (18 * C2 * ‖e‖ * Real.exp (-(δ₁ * cellSupDist (enclosingCell (j q).1.1) (enclosingCell b.1)))) ≤
      ‖e‖ * (R * Wc) := by
    rw [hWc, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    have e2 : 2 * (Mh * ‖e‖) / τ + 2 * (27 * C3 * ‖e‖) * τ = ‖e‖ * (2 * Mh / τ + 2 * (27 * C3) * τ) := by ring
    have e3 : 18 * C2 * ‖e‖ * Real.exp (-(δ₁ * cellSupDist (enclosingCell (j q).1.1) (enclosingCell b.1))) =
        ‖e‖ * (18 * C2 * Real.exp (-(δ₁ * cellSupDist (enclosingCell (j q).1.1) (enclosingCell b.1)))) := by ring
    rw [e2, e3, ← mul_min_of_nonneg _ _ (norm_nonneg e)]
    have h3 : min (2 * Mh / τ + 2 * (27 * C3) * τ)
        (18 * C2 * Real.exp (-(δ₁ * cellSupDist (enclosingCell (j q).1.1) (enclosingCell b.1)))) ≤
        R * wq q := (min_le_min hPn le_rfl).trans (hR q)
    have h4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg e)) (norm_nonneg (c q))
    calc _ ≤ _ := h4
      _ = _ := by ring
  have t1 : (3 * C3 * ‖e‖) * (Calculus.weightedNorm (cellWeight (δ₁ / 2) (enclosingCell b.1))
      (chartOffset (bondBumps j c)) *
      Calculus.weightedNorm (cellWeight (δ₁ / 2) (enclosingCell b.1)) (chartOffset (bondBumps j dc))) ≤
      ‖e‖ * (27 * C3 * (D * Sw) * Wc) := by
    have h5 : 0 ≤ 3 * C3 * ‖e‖ := by positivity
    have h6 := mul_le_mul hn hd hd0 (by positivity)
    calc _ ≤ (3 * C3 * ‖e‖) * ((3 * Wc) * (3 * (D * Sw))) := mul_le_mul_of_nonneg_left h6 h5
      _ = _ := by ring
  calc _ ≤ ‖e‖ * (27 * C3 * (D * Sw) * Wc) + ‖e‖ * (R * Wc) := add_le_add t1 t2
    _ = _ := by ring
theorem abs_integral_sum_sub_le {ι : Type} [Fintype ι] {x : ℝ} (hx : 0 ≤ x) (P : ι → Prop) [DecidablePred P]
    (f f' : ι → ℝ → ℝ) (hf : ∀ q, P q → ContinuousOn (f q) (Set.Icc 0 1))
    (hf' : ∀ q, P q → ContinuousOn (f' q) (Set.Icc 0 1))
    (B : ι → ℝ) (hB : ∀ q, P q → ∀ u ∈ Set.Icc (0 : ℝ) 1, |f q u - f' q u| ≤ B q) :
    |x * (∑ q, if P q then ∫ v in (0 : ℝ)..1, f q v else 0) - x * ∑ q, if P q then ∫ v in (0 : ℝ)..1, f' q v else 0| ≤
      x * ∑ q, if P q then B q else 0 := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hx]
  refine mul_le_mul_of_nonneg_left ?_ hx
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  by_cases hq : P q
  · simp only [if_pos hq]
    have hi : ∀ g : ℝ → ℝ, ContinuousOn g (Set.Icc 0 1) → IntervalIntegrable g MeasureTheory.volume 0 1 :=
      fun g hg => ContinuousOn.intervalIntegrable (by rwa [Set.uIcc_of_le zero_le_one])
    rw [← intervalIntegral.integral_sub (hi _ (hf q hq)) (hi _ (hf' q hq))]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun v => f q v - f' q v) (C := B q) (fun u hu => by
        rw [Set.uIoc_of_le zero_le_one] at hu
        exact hB q hq u ⟨hu.1.le, hu.2⟩)
    simpa using h
  · simp [if_neg hq]
theorem continuousOn_chartedSlope_segment (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i)
    {a δ₁ C2 C3 m : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top}
    (hS : SlopeControl a δ₁ C2 C3 m w V)
    {eta : F.Site F.depth → Fin 4 → imaginaryQuaternions} (hm : ∀ x i, ‖eta x i‖ ≤ m)
    (b : F.Site F.depth × Fin 4) (e : imaginaryQuaternions) :
    ContinuousOn (fun u : ℝ => chartedSlope a (shiftChart w fun x i => u • eta x i) V b e) (Set.Icc 0 1) := by
  have hsm : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ x i, ‖u • eta x i‖ ≤ m := fun u hu x i => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.1]
    exact (mul_le_mul hu.2 (hm x i) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have e1 : ∀ u ∈ Set.Icc (0 : ℝ) 1, chartedSlope a (shiftChart w fun x i => u • eta x i) V b e =
      slopeFunction a w V b e (u • chartOffset eta) := fun u hu => by
    rw [chartedSlope_eq_slopeFunction hCE hL hs hS (hsm u hu) b e, chartOffset_smul]
  refine ContinuousOn.congr (f := fun u : ℝ => slopeFunction a w V b e (u • chartOffset eta)) ?_ e1
  intro u hu
  have h1 : ContinuousAt (slopeFunction a w V b e) (u • chartOffset eta) := by
    have := (slopeFunction_analyticAt hCE hL hs hS (hsm u hu) b e).continuousAt
    rwa [chartOffset_smul] at this
  have h2 : ContinuousAt (fun u : ℝ => u • chartOffset eta) u := by fun_prop
  exact (ContinuousAt.comp (f := fun u : ℝ => u • chartOffset eta) h1 h2).continuousWithinAt
theorem chartedSlope_smul (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    {a δ₁ C2 C3 m : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top}
    (hS : SlopeControl a δ₁ C2 C3 m w V)
    {dw : F.Site F.depth → Fin 4 → imaginaryQuaternions} (hm : ∀ x i, ‖dw x i‖ ≤ m)
    (b : F.Site F.depth × Fin 4) (c : ℝ) (e : imaginaryQuaternions) :
    chartedSlope a (shiftChart w dw) V b (c • e) = c * chartedSlope a (shiftChart w dw) V b e := by
  rw [chartedSlope_eq_slopeFunction hCE hL hs hS hm, chartedSlope_eq_slopeFunction hCE hL hs hS hm]
  simp only [slopeFunction, bondBumpCoords_smul, map_smul, smul_eq_mul]
theorem abs_chartedSlope_sub_le_of_unit (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i)
    (hL' : Odd F'.blockSide) (hs' : ∀ i, 2 ≤ F'.extent i) {a δ₁ C2 C3 m M : ℝ}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top}
    {w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions} {V' : F'.GaugeField F'.top}
    (hS : SlopeControl a δ₁ C2 C3 m w V) (hS' : SlopeControl a δ₁ C2 C3 m w' V')
    {dw : F.Site F.depth → Fin 4 → imaginaryQuaternions} {dw' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions}
    (hm : ∀ x i, ‖dw x i‖ ≤ m) (hm' : ∀ x i, ‖dw' x i‖ ≤ m) (b : F.Site F.depth × Fin 4)
    (b' : F'.Site F'.depth × Fin 4)
    (hU : ∀ e : imaginaryQuaternions, ‖e‖ = 1 →
      |chartedSlope a (shiftChart w dw) V b e - chartedSlope a (shiftChart w' dw') V' b' e| ≤ M)
    (e : imaginaryQuaternions) :
    |chartedSlope a (shiftChart w dw) V b e - chartedSlope a (shiftChart w' dw') V' b' e| ≤ M * ‖e‖ := by
  by_cases he : e = 0
  · subst he
    simp [chartedSlope_zero]
  · have hn : ‖e‖ ≠ 0 := by simpa using he
    obtain ⟨u, hu⟩ : ∃ u : imaginaryQuaternions, u = ‖e‖⁻¹ • e := ⟨_, rfl⟩
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have heu : e = ‖e‖ • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ hn, one_smul]
    have h := hU u hu1
    have e2 : chartedSlope a (shiftChart w dw) V b e - chartedSlope a (shiftChart w' dw') V' b' e =
        ‖e‖ * (chartedSlope a (shiftChart w dw) V b u - chartedSlope a (shiftChart w' dw') V' b' u) := by
      conv_lhs => rw [heu, chartedSlope_smul hCE hL hs hS hm, chartedSlope_smul hCE hL' hs' hS' hm']
      ring
    rw [e2, abs_mul, abs_of_nonneg (norm_nonneg e), mul_comm]
    exact mul_le_mul_of_nonneg_right h (norm_nonneg e)
end
section
variable {F F' : BlockFrame}
theorem mul_weighted_sum_le_weighted_sq {ι : Type} [Fintype ι] (u : ι → ℝ) (wq vq : ι → ℝ) (q : ι) {S : ℝ}
    (hu : ∀ q, 0 ≤ u q)
    (hw : ∀ q, 0 ≤ wq q) (hwv : ∀ q, wq q ≤ vq q) (hv1 : vq q = 1) (hS : ∑ q, wq q ≤ S) :
    u q * ∑ q', u q' * wq q' ≤ (S + 1) / 2 * ∑ q', vq q' * u q' ^ 2 := by
  have hv0 : ∀ q, 0 ≤ vq q := fun q => (hw q).trans (hwv q)
  obtain ⟨N2, hN2⟩ : ∃ N2, N2 = ∑ q', vq q' * u q' ^ 2 := ⟨_, rfl⟩
  rw [← hN2]
  have hN0 : 0 ≤ N2 := by
    rw [hN2]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (hv0 q) (sq_nonneg _)
  have h1 : u q ^ 2 ≤ N2 := by
    have := Finset.single_le_sum (f := fun q' => vq q' * u q' ^ 2)
      (fun q' _ => mul_nonneg (hv0 q') (sq_nonneg _)) (Finset.mem_univ q)
    simp only [hv1, one_mul] at this
    rw [hN2]
    exact this
  have h2 : ∑ q', wq q' * u q' ^ 2 ≤ N2 := by
    rw [hN2]
    exact Finset.sum_le_sum fun q' _ => mul_le_mul_of_nonneg_right (hwv q') (sq_nonneg _)
  have h3 : u q * ∑ q', u q' * wq q' ≤ ∑ q', (u q ^ 2 * wq q' + wq q' * u q' ^ 2) / 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q' _ => ?_
    have := mul_nonneg (sq_nonneg (u q - u q')) (hw q')
    nlinarith
  have h4 : ∑ q', (u q ^ 2 * wq q' + wq q' * u q' ^ 2) / 2 =
      (u q ^ 2 * ∑ q', wq q' + ∑ q', wq q' * u q' ^ 2) / 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h5 : u q ^ 2 * ∑ q', wq q' ≤ N2 * S := by
    have hSw0 : 0 ≤ ∑ q', wq q' := Finset.sum_nonneg fun q _ => hw q
    exact mul_le_mul h1 hS hSw0 hN0
  rw [h4] at h3
  nlinarith
theorem abs_slopeComponent_sub_le_at_cell (hCE : ChartedEnergyInCoordinates) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i)
    (hL' : Odd F'.blockSide) (hs' : ∀ i, 2 ≤ F'.extent i) {a δ₁ C2 C3 m Mh τ D P Pn R I S x κ ρA : ℝ}
    (star : Bool) (mr : ℕ)
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top}
    (hS : SlopeControl a δ₁ C2 C3 m (frameCoordField star a ρA mr V) V)
    (hS' : SlopeControl a δ₁ C2 C3 m (frameCoordField star a ρA mr V') V')
    (hδ₁ : 0 ≤ δ₁) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) (hτ : 0 < τ) (hx : 0 ≤ x) {ι : Type} [Fintype ι]
    [DecidableEq ↥(chordBonds (finiteCells F))] [DecidableEq ↥(chordBonds (finiteCells F'))]
    {j : ι → ↥(chordBonds (finiteCells F))} {j' : ι → ↥(chordBonds (finiteCells F'))}
    (hj : Function.Injective j) (hj' : Function.Injective j') (ζ : BondField ι) (dc : ι → imaginaryQuaternions)
    (hDc : ∀ q, ‖dc q‖ ≤ D) (hP0 : 0 ≤ P) (hP : ∀ q, ‖ζ q‖ ≤ P) (hm : D + P + τ ≤ m) (hD0 : 0 ≤ D) (hR0 : 0 ≤ R)
    (Z : F.Cell) (Z' : F'.Cell) (Pr : ι → Prop)
    (hZ : ∀ q, enclosingCell (j q).1.1 = Z ↔ Pr q) (hZ' : ∀ q, enclosingCell (j' q).1.1 = Z' ↔ Pr q)
    (hdist : ∀ q₀, Pr q₀ → ∀ q, cellSupDist (enclosingCell (j' q).1.1) Z' = cellSupDist (enclosingCell (j q).1.1) Z)
    (hM : ∀ q₀, Pr q₀ → ∀ e : imaginaryQuaternions, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ q, ∀ e₂ : imaginaryQuaternions,
      ‖e₂‖ = 1 → ∀ s ∈ Set.Icc (0 : ℝ) τ,
      |chartedSlope a (shiftChart (frameCoordField star a ρA mr V) fun x i =>
          (bondBumps j dc x i + t • bondBumps j (fun q => toImaginary (ζ q)) x i) +
            s • bondBump (j q).1 e₂ x i) V (j q₀).1 e -
        chartedSlope a (shiftChart (frameCoordField star a ρA mr V') fun x i =>
          ((0 : imaginaryQuaternions) + t • bondBumps j' (fun q => toImaginary (ζ q)) x i) +
            s • bondBump (j' q).1 e₂ x i) V' (j' q₀).1 e| ≤ Mh * ‖e‖)
    (hPn : 2 * Mh / τ + 2 * (27 * C3) * τ ≤ Pn)
    (hR : ∀ q, min Pn (18 * C2 * Real.exp (-(δ₁ * cellSupDist (enclosingCell (j q).1.1) Z))) ≤
      R * Real.exp (-(δ₁ / 2 * cellSupDist (enclosingCell (j q).1.1) Z)))
    (hI : ∀ q₀, Pr q₀ → ∀ e : imaginaryQuaternions,
      x * |chartedSlope a (shiftChart (frameCoordField star a ρA mr V) fun _ _ => 0) V (j q₀).1 e -
      chartedSlope a (shiftChart (frameCoordField star a ρA mr V') fun _ _ => 0) V' (j' q₀).1 e| ≤ I * ‖e‖)
    (hI0 : 0 ≤ I)
    (hSw : ∑ q, Real.exp (-(δ₁ / 2 * cellSupDist (enclosingCell (j q).1.1) Z)) ≤ S) (hκ : 2 ^ 7 * κ ≤ δ₁) :
    |slopeComponent star a ρA x mr Z V (zeroExtensionL j ζ) -
        slopeComponent star a ρA x mr Z' V' (zeroExtensionL j' ζ)| ≤
      S * (I * P + x * ((27 * C3 * (D * S) + R) * ((S + 1) / 2 *
        weightedSqNormAt κ (chordBondCell F) (cellDistReal F) Z (zeroExtensionL j ζ)))) := by
  classical
  obtain ⟨wF, hwF⟩ : ∃ wF, wF = frameCoordField star a ρA mr V := ⟨_, rfl⟩
  obtain ⟨wF', hwF'⟩ : ∃ wF', wF' = frameCoordField star a ρA mr V' := ⟨_, rfl⟩
  have hE := slopeComponent_zeroExtension star a ρA x mr V hj ζ Z Pr hZ
  have hE' := slopeComponent_zeroExtension star a ρA x mr V' hj' ζ Z' Pr hZ'
  rw [← hwF] at hE hM hI hS
  rw [← hwF'] at hE' hM hI hS'
  obtain ⟨c, hc⟩ : ∃ c : ι → imaginaryQuaternions, c = fun q => toImaginary (ζ q) := ⟨_, rfl⟩
  rw [← hc] at hE hE' hM
  have hcn : ∀ q, ‖c q‖ = ‖ζ q‖ := fun q => by rw [hc]; exact norm_toImaginary _
  have hcP : ∀ q, ‖c q‖ ≤ P := fun q => by rw [hcn]; exact hP q
  have e0 : ∀ q, toImaginary (ζ q) = c q := fun q => by rw [hc]
  simp only [e0] at hE hE'
  obtain ⟨wq, hwq⟩ : ∃ wq : ι → ℝ, wq = fun q => Real.exp (-(δ₁ / 2 * cellSupDist (enclosingCell (j q).1.1) Z)) :=
    ⟨_, rfl⟩
  have ewq : ∀ q, Real.exp (-(δ₁ / 2 * cellSupDist (enclosingCell (j q).1.1) Z)) = wq q := fun q => by rw [hwq]
  have hw0 : ∀ q, 0 ≤ wq q := fun q => by rw [← ewq]; exact (Real.exp_pos _).le
  simp only [ewq] at hR hSw
  obtain ⟨Wc, hWc⟩ : ∃ Wc, Wc = ∑ q, ‖c q‖ * wq q := ⟨_, rfl⟩
  obtain ⟨Sw, hSwd⟩ : ∃ Sw, Sw = ∑ q, wq q := ⟨_, rfl⟩
  rw [← hSwd] at hSw
  have hSw0 : 0 ≤ Sw := by
    rw [hSwd]
    exact Finset.sum_nonneg fun q _ => hw0 q
  have hS0 : 0 ≤ S := hSw0.trans hSw
  have hWc0 : 0 ≤ Wc := by
    rw [hWc]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (norm_nonneg _) (hw0 q)
  obtain ⟨Aw, hAw⟩ : ∃ Aw, Aw = 27 * C3 * (D * Sw) + R := ⟨_, rfl⟩
  have hbond : ∀ q₀, Pr q₀ → ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |chartedSlope a (shiftChart wF fun x i => u • bondBumps j c x i) V (j q₀).1 (c q₀) -
        chartedSlope a (shiftChart wF' fun x i => u • bondBumps j' c x i) V' (j' q₀).1 (c q₀)| ≤
      |chartedSlope a (shiftChart wF fun _ _ => 0) V (j q₀).1 (c q₀) -
        chartedSlope a (shiftChart wF' fun _ _ => 0) V' (j' q₀).1 (c q₀)| + ‖c q₀‖ * (Aw * Wc) := by
    intro q₀ hq₀ u hu
    have hcell : enclosingCell (j q₀).1.1 = Z := (hZ q₀).mpr hq₀
    have hcell' : enclosingCell (j' q₀).1.1 = Z' := (hZ' q₀).mpr hq₀
    have h := abs_slope_difference_sub_le_weighted hCE hL hs hL' hs' (Mh := Mh) (τ := τ) (D := D) (P := P)
      (Pn := Pn) (R := R) hS hS' hδ₁ hC2 hC3 hτ
      hj hj' c dc hDc hP0 hcP hm hD0 hR0 (j q₀).2 (j' q₀).2
      (fun q => by rw [hcell, hcell']; exact hdist q₀ hq₀ q) (c q₀)
      (fun t ht q e₂ he₂ s hs₁ => hM q₀ hq₀ (c q₀) t ht q e₂ he₂ s hs₁) hPn
      (fun q => by
        rw [hcell, ewq q]
        exact hR q) u hu
    simp only [hcell, ewq] at h
    rw [← hWc, ← hSwd, ← hAw] at h
    have h2 := abs_add_le ((chartedSlope a (shiftChart wF fun x i => u • bondBumps j c x i) V (j q₀).1 (c q₀) -
        chartedSlope a (shiftChart wF' fun x i => u • bondBumps j' c x i) V' (j' q₀).1 (c q₀)) -
      (chartedSlope a (shiftChart wF fun _ _ => 0) V (j q₀).1 (c q₀) -
        chartedSlope a (shiftChart wF' fun _ _ => 0) V' (j' q₀).1 (c q₀)))
      (chartedSlope a (shiftChart wF fun _ _ => 0) V (j q₀).1 (c q₀) -
        chartedSlope a (shiftChart wF' fun _ _ => 0) V' (j' q₀).1 (c q₀))
    rw [sub_add_cancel] at h2
    linarith
  have hmF : ∀ x i, ‖bondBumps j c x i‖ ≤ m := fun x i =>
    (norm_bondBumps_le hj hP0 hcP x i).trans (by linarith [hτ.le])
  have hmF' : ∀ x i, ‖bondBumps j' c x i‖ ≤ m := fun x i =>
    (norm_bondBumps_le hj' hP0 hcP x i).trans (by linarith [hτ.le])
  have hPart := abs_integral_sum_sub_le hx Pr
    (fun q u => chartedSlope a (shiftChart wF fun x i => u • bondBumps j c x i) V (j q).1 (c q))
    (fun q u => chartedSlope a (shiftChart wF' fun x i => u • bondBumps j' c x i) V' (j' q).1 (c q))
    (fun q _ => continuousOn_chartedSlope_segment hCE hL hs hS hmF (j q).1 (c q))
    (fun q _ => continuousOn_chartedSlope_segment hCE hL' hs' hS' hmF' (j' q).1 (c q))
    (fun q => |chartedSlope a (shiftChart wF fun _ _ => 0) V (j q).1 (c q) -
        chartedSlope a (shiftChart wF' fun _ _ => 0) V' (j' q).1 (c q)| + ‖c q‖ * (Aw * Wc)) hbond
  rw [hE, hE']
  refine hPart.trans ?_
  obtain ⟨vq, hvq⟩ : ∃ vq : ι → ℝ,
      vq = fun q => Real.exp (-(2 ^ 6 * κ * cellDistReal F Z (chordBondCell F (j q)))) := ⟨_, rfl⟩
  have hN : weightedSqNormAt κ (chordBondCell F) (cellDistReal F) Z (zeroExtensionL j ζ) =
      ∑ q, vq q * ‖c q‖ ^ 2 := by
    rw [weightedSqNormAt_zeroExtension κ hj ζ Z, hvq]
    simp only [hcn]
  rw [hN]
  obtain ⟨N2, hN2⟩ : ∃ N2, N2 = ∑ q, vq q * ‖c q‖ ^ 2 := ⟨_, rfl⟩
  rw [← hN2]
  have hwv : ∀ q, wq q ≤ vq q := by
    intro q
    rw [← ewq, hvq]
    apply Real.exp_le_exp.mpr
    have e1 : cellDistReal F Z (chordBondCell F (j q)) = (cellSupDist (enclosingCell (j q).1.1) Z : ℝ) := by
      unfold cellDistReal chordBondCell
      rw [cellSupDist_comm]
    rw [e1]
    have h0 : (0 : ℝ) ≤ cellSupDist (enclosingCell (j q).1.1) Z := by positivity
    have h1 : 2 ^ 6 * κ ≤ δ₁ / 2 := by linarith
    have := mul_le_mul_of_nonneg_right h1 h0
    linarith
  have hv0 : ∀ q, 0 ≤ vq q := fun q => (hw0 q).trans (hwv q)
  have hN0 : 0 ≤ N2 := by
    rw [hN2]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (hv0 q) (sq_nonneg _)
  obtain ⟨Aa, hAa⟩ : ∃ Aa, Aa = 27 * C3 * (D * S) + R := ⟨_, rfl⟩
  rw [← hAa]
  have hAwAa : Aw ≤ Aa := by
    rw [hAw, hAa]
    have := mul_le_mul_of_nonneg_left hSw hD0
    have h3 := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 27 * C3)
    linarith
  have hAw0 : 0 ≤ Aw := by
    rw [hAw]
    positivity
  have hAa0 : 0 ≤ Aa := hAw0.trans hAwAa
  obtain ⟨G, hG⟩ : ∃ G, G = I * P + x * (Aa * ((S + 1) / 2 * N2)) := ⟨_, rfl⟩
  rw [← hG]
  have hG0 : 0 ≤ G := by
    rw [hG]
    positivity
  have hq : ∀ q, Pr q → x * (|chartedSlope a (shiftChart wF fun _ _ => 0) V (j q).1 (c q) -
      chartedSlope a (shiftChart wF' fun _ _ => 0) V' (j' q).1 (c q)| + ‖c q‖ * (Aw * Wc)) ≤ G := by
    intro q hPq
    have h1 := hI q hPq (c q)
    have h2 : I * ‖c q‖ ≤ I * P := mul_le_mul_of_nonneg_left (hcP q) hI0
    have hv1 : vq q = 1 := by
      have hcell : enclosingCell (j q).1.1 = Z := (hZ q).mpr hPq
      rw [hvq]
      simp only
      have e1 : cellDistReal F Z (chordBondCell F (j q)) = 0 := by
        unfold cellDistReal chordBondCell
        rw [hcell, cellSupDist_self]
        simp
      rw [e1]
      simp
    have h3 : ‖c q‖ * Wc ≤ (S + 1) / 2 * N2 := by
      rw [hWc, hN2]
      exact mul_weighted_sum_le_weighted_sq (S := S) (fun q => ‖c q‖) wq vq q (fun q => norm_nonneg _) hw0 hwv hv1
        (hSwd ▸ hSw)
    have h4 : ‖c q‖ * (Aw * Wc) ≤ Aa * ((S + 1) / 2 * N2) := by
      have h5 : 0 ≤ (S + 1) / 2 * N2 := by positivity
      calc ‖c q‖ * (Aw * Wc) = Aw * (‖c q‖ * Wc) := by ring
        _ ≤ Aw * ((S + 1) / 2 * N2) := mul_le_mul_of_nonneg_left h3 hAw0
        _ ≤ _ := mul_le_mul_of_nonneg_right hAwAa h5
    have h6 := mul_le_mul_of_nonneg_left h4 hx
    rw [hG]
    nlinarith
  have hcount : ∑ q, (if Pr q then (1 : ℝ) else 0) ≤ S := by
    refine le_trans (Finset.sum_le_sum fun q _ => ?_) (hSwd ▸ hSw)
    by_cases hPq : Pr q
    · have hcell : enclosingCell (j q).1.1 = Z := (hZ q).mpr hPq
      rw [if_pos hPq, ← ewq, hcell, cellSupDist_self]
      simp
    · rw [if_neg hPq]
      exact hw0 q
  rw [Finset.mul_sum]
  calc _ ≤ ∑ q, (if Pr q then (1 : ℝ) else 0) * G := by
        refine Finset.sum_le_sum fun q _ => ?_
        by_cases hPq : Pr q
        · simp only [if_pos hPq, one_mul]
          exact hq q hPq
        · simp [if_neg hPq]
    _ = (∑ q, (if Pr q then (1 : ℝ) else 0)) * G := by rw [Finset.sum_mul]
    _ ≤ S * G := mul_le_mul_of_nonneg_right hcount hG0
end
section
variable {F F' : BlockFrame}
theorem valMinAbs_intCast_of_small {n : ℕ} (hn : 0 < n) (hs : ∀ i, F.extent i = n) (i : Fin 4) {z : ℤ}
    (hz : 2 * |z| < n) : ((z : ZMod (F.period F.top i))).valMinAbs = z := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TorusBonds.valMinAbs_intCast_of_small <;> assumption
theorem cellSupDist_add_siteOfCoords_le {n B : ℕ} (hn : 0 < n) (hs : ∀ i, F.extent i = n) (Y : F.Cell)
    (g : Fin 4 → ℤ)
    (hg : ∀ i, |g i| ≤ (B : ℤ)) (hB : 2 * B < n) : cellSupDist Y (Y + siteOfCoords F.top g) ≤ B := by
  unfold cellSupDist
  refine Finset.sup_le fun i _ => ?_
  have e : Y i - (Y + siteOfCoords F.top g : F.Cell) i = ((-(g i) : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  rw [e, valMinAbs_intCast_of_small hn hs i (by rw [abs_neg]; have := hg i; omega)]
  have := abs_le.mp (hg i)
  omega
theorem withinRadius_mono {r r' : ℕ} {h : Fin 4 → ℤ} (hh : WithinRadius r h) (hr : r ≤ r') :
    WithinRadius r' h := fun i =>
  (hh i).trans (by exact_mod_cast hr)
theorem isFineBondWithinRadius_mono {Y : F.Cell} {r r' : ℕ} {h o : Fin 4 → ℤ} {i : Fin 4}
    (hb : IsFineBondWithinRadius Y r h o i)
    (hr : r ≤ r') : IsFineBondWithinRadius Y r' h o i := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb
  exact ⟨h1, h2, withinRadius_mono h3 hr, h4.trans hr, h5.trans hr⟩
theorem isFineBondWithinRadius_succ (hS : SiteDecomposition) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    {n : ℕ} (hn : 0 < n)
    (hsn : ∀ i, F.extent i = n) (Y : F.Cell) {R : ℕ} {h o : Fin 4 → ℤ} {i : Fin 4} (hh : WithinRadius R h)
    (ho : o ∈ centredCube F.blockSide)
    (hb : fineBondAt Y h o i ∈ chordBonds (finiteCells F)) (hR : 2 * (R + 1) < n) :
    IsFineBondWithinRadius Y (R + 1) h o i := by
  have hc : enclosingCell (fineBondAt Y h o i).1 = Y + siteOfCoords F.top h := (fineBondAt_cell_offset hS hL hs Y i ho).1
  have hR1 : WithinRadius (R + 1) h := withinRadius_mono hh (Nat.le_succ R)
  refine ⟨ho, hb, hR1, ?_, ?_⟩
  · rw [hc]
    exact cellSupDist_add_siteOfCoords_le hn hsn Y h hR1 hR
  · rcases (hS F hL hs).2.2.2 (fineBondAt Y h o i).1 i with e | e
    · rw [e, hc]
      exact cellSupDist_add_siteOfCoords_le hn hsn Y h hR1 hR
    · rw [e, hc]
      have e2 : Y + siteOfCoords F.top h + unitStep F.top i = Y + siteOfCoords F.top (h + Pi.single i 1) := by
        funext l
        simp [siteOfCoords, unitStep, add_assoc]
      rw [e2]
      refine cellSupDist_add_siteOfCoords_le hn hsn Y _ (fun l => ?_) hR
      have h1 := hh l
      by_cases hl : l = i
      · subst hl
        simp only [Pi.add_apply, Pi.single_eq_same]
        have := abs_le.mp h1
        rw [abs_le]
        push_cast
        omega
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
        have := abs_le.mp h1
        rw [abs_le]
        push_cast
        omega
theorem bondBump_apply_commonBond {ι : Type} {j : ι → ↥(chordBonds (finiteCells F))} (hj : Function.Injective j)
    [DecidableEq ι]
    (e : imaginaryQuaternions) (q qq : ι) : bondBump (j q).1 e (j qq).1.1 (j qq).1.2 = if qq = q then e else 0 := by
  classical
  unfold bondBump
  by_cases h : qq = q
  · subst h
    simp
  · have hne : ((j qq).1.1, (j qq).1.2) ≠ (j q).1 := fun he => h (hj (Subtype.ext he))
    simp [h, hne]
theorem shiftChart_commonBond_eq {ι : Type} [Fintype ι] [DecidableEq ι] {j : ι → ↥(chordBonds (finiteCells F))}
    {j' : ι → ↥(chordBonds (finiteCells F'))} (hj : Function.Injective j) (hj' : Function.Injective j')
    (wF : F.Site F.depth → Fin 4 → imaginaryQuaternions) (wF' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions)
    (c dc : ι → imaginaryQuaternions)
    (hdc : ∀ q, dc q = wF' (j' q).1.1 (j' q).1.2 - wF (j q).1.1 (j q).1.2) (t s : ℝ) (q : ι)
    (e₂ : imaginaryQuaternions) (qq : ι) :
    shiftChart wF (fun x i => (bondBumps j dc x i + t • bondBumps j c x i) + s • bondBump (j q).1 e₂ x i)
        (j qq).1.1 (j qq).1.2 =
      shiftChart wF' (fun x i => ((0 : imaginaryQuaternions) + t • bondBumps j' c x i) +
        s • bondBump (j' q).1 e₂ x i) (j' qq).1.1 (j' qq).1.2 := by
  simp only [shiftChart, bondBumps_apply_self hj, bondBumps_apply_self hj', bondBump_apply_commonBond hj,
    bondBump_apply_commonBond hj', hdc qq]
  abel
theorem sum_comp_injective_le {ι κ : Type} [Fintype ι] [Fintype κ] {j : ι → κ} (hj : Function.Injective j)
    (f : κ → ℝ)
    (hf : ∀ b, 0 ≤ f b) : ∑ q, f (j q) ≤ ∑ b, f b := by apply _root_.YangMills.SharedProofs.p12339 <;> assumption
theorem min_exp_le_mul_exp {Kp Qn δ₂ r δ₁ dd : ℝ} (hK : 0 ≤ Kp) (hQ : 0 ≤ Qn) :
    min (Kp * Real.exp (-(δ₂ * r))) (Qn * Real.exp (-(δ₁ * dd))) ≤
      ((Kp + Qn) * Real.exp (-(δ₂ * r / 2))) * Real.exp (-(δ₁ / 2 * dd)) := by
  rw [mul_assoc, ← Real.exp_add]
  by_cases h : δ₁ * dd ≤ δ₂ * r
  · refine (min_le_left _ _).trans ?_
    have h1 : Real.exp (-(δ₂ * r)) ≤ Real.exp (-(δ₂ * r / 2) + -(δ₁ / 2 * dd)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have h2 := Real.exp_pos (-(δ₂ * r / 2) + -(δ₁ / 2 * dd))
    nlinarith
  · refine (min_le_right _ _).trans ?_
    have h1 : Real.exp (-(δ₁ * dd)) ≤ Real.exp (-(δ₂ * r / 2) + -(δ₁ / 2 * dd)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have h2 := Real.exp_pos (-(δ₂ * r / 2) + -(δ₁ / 2 * dd))
    nlinarith
theorem final_constant_bound {X S I P C3 D Rr x N2 Cw σ Kq E₂ E₈ E₉ Ct : ℝ}
    (hX : X ≤ S * (I * P + x * ((27 * C3 * (D * S) + Rr) * ((S + 1) / 2 * N2))))
    (hS0 : 0 ≤ S) (hx : 0 ≤ x) (hN2 : 0 ≤ N2) (hC3 : 0 ≤ C3) (hI : I = Cw * E₉) (hCw : 0 ≤ Cw) (hP0 : 0 ≤ P)
    (hP1 : P ≤ 1)
    (hD : D = Cw * σ * E₈) (hCσ : Cw * σ ≤ 1) (hCσ0 : 0 ≤ Cw * σ) (hRr : Rr ≤ Kq * E₈) (hKq : 0 ≤ Kq)
    (hE₉ : E₉ ≤ E₂) (hE₈ : E₈ ≤ E₂)
    (hE₉0 : 0 ≤ E₉) (hE₈0 : 0 ≤ E₈) (hE₂0 : 0 ≤ E₂)
    (h1 : S * Cw ≤ Ct / 4) (h2 : S * ((27 * C3 * S + Kq) * ((S + 1) / 2)) ≤ Ct / 4) :
    X ≤ (Ct / 4 * E₂) * (x * N2 + 1) := by
  have hIP : I * P ≤ Cw * E₂ := by
    rw [hI]
    have : Cw * E₉ ≤ Cw * E₂ := mul_le_mul_of_nonneg_left hE₉ hCw
    have h3 : Cw * E₉ * P ≤ Cw * E₉ * 1 := mul_le_mul_of_nonneg_left hP1 (mul_nonneg hCw hE₉0)
    linarith
  have hA : 27 * C3 * (D * S) + Rr ≤ (27 * C3 * S + Kq) * E₂ := by
    have h3 : D ≤ E₂ := by
      rw [hD]
      calc Cw * σ * E₈ ≤ 1 * E₈ := mul_le_mul_of_nonneg_right hCσ hE₈0
        _ ≤ E₂ := by linarith
    have h4 : 27 * C3 * (D * S) ≤ 27 * C3 * (E₂ * S) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hS0) (by positivity)
    have h5 : Kq * E₈ ≤ Kq * E₂ := mul_le_mul_of_nonneg_left hE₈ hKq
    nlinarith
  have hT : 0 ≤ (S + 1) / 2 * N2 := by positivity
  have hB : S * (I * P + x * ((27 * C3 * (D * S) + Rr) * ((S + 1) / 2 * N2))) ≤
      S * (Cw * E₂ + x * (((27 * C3 * S + Kq) * E₂) * ((S + 1) / 2 * N2))) := by
    refine mul_le_mul_of_nonneg_left (add_le_add hIP ?_) hS0
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hT) hx
  have e : S * (Cw * E₂ + x * (((27 * C3 * S + Kq) * E₂) * ((S + 1) / 2 * N2))) =
      (S * Cw) * E₂ + (S * ((27 * C3 * S + Kq) * ((S + 1) / 2))) * (E₂ * (x * N2)) := by ring
  have h3 := mul_le_mul_of_nonneg_right h1 hE₂0
  have h4 := mul_le_mul_of_nonneg_right h2 (mul_nonneg hE₂0 (mul_nonneg hx hN2))
  calc X ≤ _ := hX
    _ ≤ _ := hB
    _ = _ := e
    _ ≤ Ct / 4 * E₂ + Ct / 4 * (E₂ * (x * N2)) := add_le_add h3 h4
    _ = _ := by ring
end
section
variable {F F' : BlockFrame}
theorem isAdmissibleChartPoint_frame (hexp : QuaternionExp.ExpUnitLipschitzInjective)
    (hhol : PathHolonomyLipschitz)
    {star : Bool} {a ρ δ₂ κ₂ C σ s₀ m₀ : ℝ} {Kk : ℕ → ℝ} {m L : ℕ} {V : F.GaugeField F.top}
    (hSm : FrameSmallness star a ρ δ₂ κ₂ C σ Kk m V) (hσ0 : 0 < σ) (hm₀ : 0 ≤ m₀)
    (h1 : C * σ + m₀ ≤ 1 / (64 * (L : ℝ))) (h2 : σ + 4 * m₀ ≤ s₀)
    {dw : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (hdw : ∀ x i, ‖dw x i‖ ≤ m₀) :
    IsAdmissibleChartPoint L s₀ (shiftChart (frameCoordField star a ρ m V) dw) V := by
  have hw : ∀ b ∈ chordBonds (finiteCells F), ‖frameCoordField star a ρ m V b.1 b.2‖ ≤ C * σ := by
    intro b hb
    unfold frameCoordField
    rw [Prod.mk.eta]
    exact hSm.norm_le b hb
  refine isAdmissibleChartPoint_shiftChart hexp hhol (P := C * σ) (s₁ := σ) hw h1 hm₀ ?_ h2 hdw
  refine isSmallCurvature_mono hSm.small_curvature ?_
  split_ifs <;> linarith
theorem norm_add_smul_add_smul_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A B C : E}
    {α β γ t s : ℝ} (hA : ‖A‖ ≤ α)
    (hB : ‖B‖ ≤ β) (hC : ‖C‖ ≤ 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) γ) :
    ‖(A + t • B) + s • C‖ ≤ α + β + γ := by
  have h1 : ‖t • B‖ ≤ β := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_mul ht.2 hB (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have h2 : ‖s • C‖ ≤ γ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact (mul_le_mul hs.2 hC (norm_nonneg _) (hs.1.trans hs.2)).trans_eq (mul_one _)
  have h3 := norm_add_le (A + t • B) (s • C)
  have h4 := norm_add_le A (t • B)
  linarith
set_option maxHeartbeats 4000000 in
theorem nearCellsClose_of_agreeingTopPair (hexp : QuaternionExp.ExpUnitLipschitzInjective)
    (hhol : PathHolonomyLipschitz)
    (hCE : ChartedEnergyInCoordinates) (hSt : SiteDecomposition) (hCv : BlocksCoverLowerLevel)
    (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) {Ck : ℕ → ℝ} {Csl S Cw m₀ : ℝ} {t : ℕ} {x : ℝ}
    (hodd : Odd T.L) (hL40 : 2 ^ 40 ≤ T.L) (h64 : 64 ≤ T.n₀) (hδ₁ : 0 < T.chainParams.δ₁) (hδ₂ : 0 < T.chainParams.δ₂)
    (hs₀ : T.chainParams.s₀ ≤ T.chainParams.σA)
    (hCk : ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
        IsBlockTorus T.L F →
        IsAdmissibleChartPoint T.L T.chainParams.σA w V → ∀ (k : ℕ) (q : Fin k → ChartDirection F),
          AnalyticAt ℝ (chartRestriction T.a w V q) 0 ∧
          (2 ≤ k → (∀ l, ‖directionVector (q l)‖ = 1) →
            |chartMixedDeriv T.a w V q| ≤ Ck k * Real.exp (-(T.chainParams.δ₁ * directionDiameter q))))
    (hCsl : ∀ (F F' : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
        (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
        (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ), 1 ≤ r → IsBlockTorus T.L F →
        IsBlockTorus T.L F' →
        F'.depth = F.depth → IsAdmissibleChartPoint T.L T.chainParams.s₀ w V →
        IsAdmissibleChartPoint T.L T.chainParams.s₀ w' V' →
        AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
        (∀ (h o : Fin 4 → ℤ) (i : Fin 4), WithinRadius r h → o ∈ centredCube T.L →
          fineBondAt Y h o i ∈ chordBonds (finiteCells F) →
            w (fineBondAt Y h o i).1 i = w' (fineBondAt Y' h o i).1 i) →
        ∀ (h o : Fin 4 → ℤ) (i : Fin 4) (e : imaginaryQuaternions), IsFineBondWithinRadius Y (r / 2) h o i →
          ‖e‖ = 1 →
          |chartedSlope T.a w V (fineBondAt Y h o i) e - chartedSlope T.a w' V' (fineBondAt Y' h o i) e| ≤
            Csl * Real.exp (-(T.chainParams.δ₂ * ((T.L : ℝ) * ((r : ℝ) / 2) - 2 * T.L - 1))))
    (hC2 : 0 ≤ Ck 2) (hC3 : 0 ≤ Ck 3) (hCsl0 : 0 ≤ Csl) (hCw0 : 0 ≤ Cw) (hS0 : 0 ≤ S)
    (hm₀ : 0 < m₀) (hm₁ : m₀ ≤ T.chainParams.s₀ / 8) (hm₂ : m₀ ≤ 1 / (128 * (T.L : ℝ)))
    (hσ0 : 0 < T.σ) (hσ1 : T.σ ≤ 1) (hσs : T.σ ≤ T.chainParams.s₀ / 2) (hCσ : Cw * T.σ + T.σ ≤ m₀ / 2)
    (hCσ1 : Cw * T.σ ≤ 1)
    (hκ0 : 0 < T.κ) (hκ1 : 2 ^ 7 * T.κ ≤ T.chainParams.δ₁) (hκ2 : 16 * T.κ ≤ T.chainParams.δ₂)
    (hnss : 64 ≤ T.blockIndex) (hτe : Real.exp (-(T.chainParams.δ₂ * T.blockIndex)) ≤ m₀ / 2) (hx1 : 0 < x)
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ} {star : Bool}
    (hTwo : AgreeingTopPair T t x V V' Y Y' r)
    (hCB2 : ∀ (F F' : BlockFrame) (Y : F.Cell) (Y' : F'.Cell) (r n n' : ℕ), F.blockSide = T.L →
      F'.blockSide = T.L →
      (∀ i, F.extent i = n) → (∀ i, F'.extent i = n') → 2 * r + 2 < n → 2 * r + 2 < n' → HasCommonBonds Y Y' r)
    (hPl₀ : ∀ (F : BlockFrame) (n : ℕ) [Fintype F.Cell], F.blockSide = T.L → 2 ≤ n → (∀ i, F.extent i = n) →
      IsDecayingPlacement T.chainParams.δ₁ S (chordBondCell F) (cellDistReal F))
    (hSm : FrameSmallness star T.a T.chainParams.ρA T.chainParams.δ₂ T.chainParams.κ₂ Cw T.σ T.chainParams.Kk (frameRadius x) V)
    (hSm' : FrameSmallness star T.a T.chainParams.ρA T.chainParams.δ₂ T.chainParams.κ₂ Cw T.σ T.chainParams.Kk (frameRadius x) V')
    (hLoc : FrameLocality star T.a T.chainParams.ρA T.chainParams.δ₂ Cw T.σ (frameRadius x) V V' Y Y' r)
    (hSl : FrameFirstDerivLocal star T.a T.chainParams.ρA T.κ Cw x (frameRadius x) V V' Y Y' r)
    (h1 : S * Cw ≤ T.Ct / 4)
    (h2 : S * ((27 * Ck 3 * S + (2 * Csl + 54 * Ck 3 + 18 * Ck 2)) * ((S + 1) / 2)) ≤ T.Ct / 4) :
    NearCellsClose T.ballRadius x T.κ ((T.Ct / 4) * Real.exp (-(2 * T.κ * r))) Y Y' r
      (fun Z η => slopeComponent star T.a T.chainParams.ρA x (frameRadius x) Z V η)
      (fun Z η => slopeComponent star T.a T.chainParams.ρA x (frameRadius x) Z V' η) := by
  classical
  intro cc ζ hζ
  obtain ⟨hFL, hFt, n, hsn, hn₀⟩ := hTwo.top
  obtain ⟨hFL', hFt', n', hsn', hn₀'⟩ := hTwo.top'
  have hagree := hTwo.agree
  have hr : T.blockIndex ≤ r := hTwo.radius_le
  have hn0 : 0 < n := by omega
  have hn0' : 0 < n' := by omega
  have hrn : 2 * r + 2 < n := by
    rcases hagree.1 0 with h | h
    · rw [hsn] at h
      omega
    · rwa [hsn] at h
  have hrn' : 2 * r + 2 < n' := by
    rcases hagree.2.1 0 with h | h
    · rw [hsn'] at h
      omega
    · rwa [hsn'] at h
  have hO : Odd F.blockSide := hFL.symm ▸ hodd
  have hO' : Odd F'.blockSide := hFL'.symm ▸ hodd
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hsn]; omega
  have hs2' : ∀ i, 2 ≤ F'.extent i := fun i => by rw [hsn']; omega
  have hFc : IsBlockTorus T.L F := ⟨hFL, n, by omega, hsn⟩
  have hFc' : IsBlockTorus T.L F' := ⟨hFL', n', by omega, hsn'⟩
  have hFt2 : F'.depth = F.depth := hFt'.trans hFt.symm
  have hLL : F.blockSide = F'.blockSide := hFL.trans hFL'.symm
  have hLr : (0 : ℝ) < T.L := by
    have : 0 < T.L := hodd.pos
    exact_mod_cast this
  have hsmall₁ : Cw * T.σ + m₀ ≤ 1 / (64 * (T.L : ℝ)) := by
    have e : 1 / (64 * (T.L : ℝ)) = 2 * (1 / (128 * (T.L : ℝ))) := by
      field_simp
      norm_num
    rw [e]
    have hX : 0 ≤ 1 / (128 * (T.L : ℝ)) := by positivity
    linarith
  have hsmall₂ : T.σ + 4 * m₀ ≤ T.chainParams.s₀ := by linarith
  have hpoint := fun (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (hdw : ∀ x i, ‖dw x i‖ ≤ m₀) =>
    isAdmissibleChartPoint_frame hexp hhol hSm hσ0 hm₀.le hsmall₁ hsmall₂ hdw
  have hpoint' := fun (dw : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) (hdw : ∀ x i, ‖dw x i‖ ≤ m₀) =>
    isAdmissibleChartPoint_frame hexp hhol hSm' hσ0 hm₀.le hsmall₁ hsmall₂ hdw
  have hSide : SlopeControl T.a T.chainParams.δ₁ (Ck 2) (Ck 3) m₀
      (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V) V :=
    slopeControl_of_admissible hCk hFc fun dw hdw =>
      ⟨(hpoint dw hdw).coord_small, isSmallCurvature_mono (hpoint dw hdw).small_curvature hs₀⟩
  have hSide' : SlopeControl T.a T.chainParams.δ₁ (Ck 2) (Ck 3) m₀
      (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V') V' :=
    slopeControl_of_admissible hCk hFc' fun dw hdw =>
      ⟨(hpoint' dw hdw).coord_small, isSmallCurvature_mono (hpoint' dw hdw).small_curvature hs₀⟩
  have hAC : HasCommonBonds Y Y' r := hCB2 F F' Y Y' r n n' hFL hFL' hsn hsn' hrn hrn'
  have hPl : ∀ Z : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(T.chainParams.δ₁ / 2 * cellDistReal F Z (chordBondCell F b))) ≤ S := by
    have : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by rw [period_top, hsn]; omega⟩
    let : Fintype F.Cell := inferInstance
    exact (hPl₀ F n hFL (by omega) hsn).bonds
  have hj : Function.Injective (commonBondLeft Y Y' (r / 2)) := hAC.injective_left
  have hj' : Function.Injective (commonBondRight Y Y' (r / 2)) := hAC.injective_right
  have hq_box : ∀ q : ↥(commonBondOffsets Y Y' (r / 2)), WithinRadius (r / 2) q.1.1 := fun q =>
    (mem_centredCube_odd _ _).1 (mem_commonBondOffsets q.2).1
  have hq_o : ∀ q : ↥(commonBondOffsets Y Y' (r / 2)), q.1.2.1 ∈ centredCube F.blockSide := fun q =>
    (mem_commonBondOffsets q.2).2
  have hq_b : ∀ q : ↥(commonBondOffsets Y Y' (r / 2)),
      fineBondAt Y q.1.1 q.1.2.1 q.1.2.2 ∈ chordBonds (finiteCells F) :=
    fun q => (Finset.mem_filter.mp q.2).2.1
  have hcell : ∀ q, enclosingCell ((commonBondLeft Y Y' (r / 2)) q).1.1 = Y + siteOfCoords F.top q.1.1 := fun q =>
    (fineBondAt_cell_offset hSt hO hs2 Y q.1.2.2 (hq_o q)).1
  have hcell' : ∀ q, enclosingCell ((commonBondRight Y Y' (r / 2)) q).1.1 = Y' + siteOfCoords F'.top q.1.1 :=
    fun q => (fineBondAt_cell_offset hSt hO' hs2' Y' q.1.2.2 (hLL ▸ hq_o q)).1
  have hr64 : 64 ≤ r := hnss.trans hr
  have hrR : (0 : ℝ) ≤ r := by positivity
  obtain ⟨τ, hτd⟩ : ∃ τ, τ = Real.exp (-(T.chainParams.δ₂ * r)) := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by
    rw [hτd]
    exact Real.exp_pos _
  have hτm : τ ≤ m₀ / 2 := by
    refine le_trans ?_ hτe
    rw [hτd]
    apply Real.exp_le_exp.mpr
    have h3 : (T.blockIndex : ℝ) ≤ r := by exact_mod_cast hr
    have := mul_le_mul_of_nonneg_left h3 hδ₂.le
    linarith
  obtain ⟨E₈, hE₈⟩ : ∃ E₈, E₈ = Real.exp (-(T.chainParams.δ₂ * r / 8)) := ⟨_, rfl⟩
  have hE₈0 : 0 ≤ E₈ := by
    rw [hE₈]
    exact (Real.exp_pos _).le
  have hE₈1 : E₈ ≤ 1 := by
    rw [hE₈, Real.exp_le_one_iff]
    have := mul_nonneg hδ₂.le hrR
    linarith
  have hCs0 : 0 ≤ Cw * T.σ := mul_nonneg hCw0 hσ0.le
  obtain ⟨D, hDd⟩ : ∃ D, D = Cw * T.σ * E₈ := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hDd]
    exact mul_nonneg hCs0 hE₈0
  have hDle : D ≤ Cw * T.σ := by
    rw [hDd]
    exact mul_le_of_le_one_right hCs0 hE₈1
  obtain ⟨dc, hdc⟩ : ∃ dc : ↥(commonBondOffsets Y Y' (r / 2)) → imaginaryQuaternions, ∀ q, dc q =
      (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V') ((commonBondRight Y Y' (r / 2)) q).1.1
          ((commonBondRight Y Y' (r / 2)) q).1.2 -
        (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V) ((commonBondLeft Y Y' (r / 2)) q).1.1
          ((commonBondLeft Y Y' (r / 2)) q).1.2 := ⟨_, fun q => rfl⟩
  have hDc : ∀ q, ‖dc q‖ ≤ D := by
    intro q
    have hbox := isFineBondWithinRadius_mono
      (isFineBondWithinRadius_succ hSt hO hs2 hn0 hsn Y (R := r / 2) (hq_box q) (hq_o q) (hq_b q) (by omega))
      (show r / 2 + 1 ≤ r by omega)
    have hv := hLoc.value q.1.1 q.1.2.1 q.1.2.2 hbox
    have hd : cellSupDist Y (enclosingCell (fineBondAt Y q.1.1 q.1.2.1 q.1.2.2).1) ≤ r / 2 := by
      have e := hcell q
      change enclosingCell (fineBondAt Y q.1.1 q.1.2.1 q.1.2.2).1 = _ at e
      rw [e]
      exact cellSupDist_add_siteOfCoords_le hn0 hsn Y _ (hq_box q) (by omega)
    rw [hdc q]
    have e1 : ‖(frameCoordField star T.a T.chainParams.ρA (frameRadius x) V') ((commonBondRight Y Y' (r / 2)) q).1.1
          ((commonBondRight Y Y' (r / 2)) q).1.2 -
        (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V) ((commonBondLeft Y Y' (r / 2)) q).1.1
          ((commonBondLeft Y Y' (r / 2)) q).1.2‖ =
        ‖(stepFrame star T.a T.chainParams.ρA (frameRadius x) (fineBondAt Y q.1.1 q.1.2.1 q.1.2.2) V : ℍ[ℝ]) -
          stepFrame star T.a T.chainParams.ρA (frameRadius x) (fineBondAt Y' q.1.1 q.1.2.1 q.1.2.2) V'‖ := by
      rw [norm_sub_rev]
      rfl
    rw [e1]
    refine hv.trans ?_
    rw [hDd, hE₈]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCs0
    have hd2 : (cellSupDist Y (enclosingCell (fineBondAt Y q.1.1 q.1.2.1 q.1.2.2).1) : ℝ) ≤ (r : ℝ) / 2 := by
      have h3 : (cellSupDist Y (enclosingCell (fineBondAt Y q.1.1 q.1.2.1 q.1.2.2).1) : ℝ) ≤ ((r / 2 : ℕ) : ℝ) := by
        exact_mod_cast hd
      exact h3.trans (by simpa using (Nat.cast_div_le (α := ℝ) (m := r) (n := 2)))
    have := mul_le_mul_of_nonneg_left hd2 hδ₂.le
    linarith
  have hZ : ∀ q : ↥(commonBondOffsets Y Y' (r / 2)),
      enclosingCell ((commonBondLeft Y Y' (r / 2)) q).1.1 = offsetCell Y (r / 8) cc ↔ q.1.1 = cc.1 := by
    intro q
    rw [hcell q]
    unfold offsetCell
    constructor
    · intro he
      refine siteOfCoords_add_injective hn0 hsn (fun i => ?_) he
      have a1 := hq_box q i
      have a2 := (mem_centredCube_odd _ _).1 cc.2 i
      have a3 := abs_sub (q.1.1 i) (cc.1 i)
      omega
    · intro he
      rw [he]
  have hZ' : ∀ q : ↥(commonBondOffsets Y Y' (r / 2)),
      enclosingCell ((commonBondRight Y Y' (r / 2)) q).1.1 = offsetCell Y' (r / 8) cc ↔ q.1.1 = cc.1 := by
    intro q
    rw [hcell' q]
    unfold offsetCell
    constructor
    · intro he
      refine siteOfCoords_add_injective hn0' hsn' (fun i => ?_) he
      have a1 := hq_box q i
      have a2 := (mem_centredCube_odd _ _).1 cc.2 i
      have a3 := abs_sub (q.1.1 i) (cc.1 i)
      omega
    · intro he
      rw [he]
  have hdist : ∀ q₀ : ↥(commonBondOffsets Y Y' (r / 2)), q₀.1.1 = cc.1 →
      ∀ q : ↥(commonBondOffsets Y Y' (r / 2)),
      cellSupDist (enclosingCell ((commonBondRight Y Y' (r / 2)) q).1.1) (offsetCell Y' (r / 8) cc) =
        cellSupDist (enclosingCell ((commonBondLeft Y Y' (r / 2)) q).1.1) (offsetCell Y (r / 8) cc) := by
    intro q₀ h₀ q
    have e1 := (hZ q₀).mpr h₀
    have e2 := (hZ' q₀).mpr h₀
    have e3 := hAC.dist_eq q q₀
    unfold cellDistReal chordBondCell at e3
    rw [e1, e2] at e3
    exact_mod_cast e3.symm
  have box₀ : ∀ q₀ : ↥(commonBondOffsets Y Y' (r / 2)), q₀.1.1 = cc.1 →
      IsFineBondWithinRadius Y (r / 8 + 1) q₀.1.1 q₀.1.2.1 q₀.1.2.2 := fun q₀ h₀ =>
    isFineBondWithinRadius_succ hSt hO hs2 hn0 hsn Y (R := r / 8)
      (by rw [h₀]; exact (mem_centredCube_odd _ _).1 cc.2) (hq_o q₀) (hq_b q₀)
      (by omega)
  obtain ⟨c, hc⟩ : ∃ c : ↥(commonBondOffsets Y Y' (r / 2)) → imaginaryQuaternions,
      c = fun q => toImaginary (ζ q) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ T.ballRadius := by
    change 0 ≤ T.σ / 64
    positivity
  have hρσ : T.ballRadius ≤ T.σ := by
    change T.σ / 64 ≤ T.σ
    linarith
  have hP : ∀ q, ‖ζ q‖ ≤ T.ballRadius := fun q => (hζ q).le
  have hcP : ∀ q, ‖c q‖ ≤ T.ballRadius := fun q => by
    rw [hc]
    simp only
    rw [norm_toImaginary]
    exact hP q
  have hm : D + T.ballRadius + τ ≤ m₀ := by linarith
  have hmove₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ q, ∀ e₂ : imaginaryQuaternions, ‖e₂‖ = 1 →
      ∀ s ∈ Set.Icc (0 : ℝ) τ, ∀ x i,
      ‖(bondBumps (commonBondLeft Y Y' (r / 2)) dc x i + t • bondBumps (commonBondLeft Y Y' (r / 2)) c x i) +
        s • bondBump ((commonBondLeft Y Y' (r / 2)) q).1 e₂ x i‖ ≤ m₀ := by
    intro t ht q e₂ he₂ s hs₁ x i
    refine (norm_add_smul_add_smul_le (norm_bondBumps_le hj hD0 hDc x i) (norm_bondBumps_le hj hρ0 hcP x i) ?_ ht
      hs₁).trans hm
    exact (norm_bondBump_le _ _ _ _).trans he₂.le
  have hmove₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ q, ∀ e₂ : imaginaryQuaternions, ‖e₂‖ = 1 →
      ∀ s ∈ Set.Icc (0 : ℝ) τ, ∀ x i,
      ‖((0 : imaginaryQuaternions) + t • bondBumps (commonBondRight Y Y' (r / 2)) c x i) +
        s • bondBump ((commonBondRight Y Y' (r / 2)) q).1 e₂ x i‖ ≤ m₀ := by
    intro t ht q e₂ he₂ s hs₁ x i
    refine (norm_add_smul_add_smul_le (α := 0) (by simp) (norm_bondBumps_le hj' hρ0 hcP x i) ?_ ht hs₁).trans
      (by linarith)
    exact (norm_bondBump_le _ _ _ _).trans he₂.le
  obtain ⟨Mh, hMh⟩ : ∃ Mh,
      Mh = Csl * Real.exp (-(T.chainParams.δ₂ * ((T.L : ℝ) * (((r / 2 : ℕ) : ℝ) / 2) - 2 * T.L - 1))) := ⟨_, rfl⟩
  have hM : ∀ q₀ : ↥(commonBondOffsets Y Y' (r / 2)), q₀.1.1 = cc.1 → ∀ e : imaginaryQuaternions,
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ q, ∀ e₂ : imaginaryQuaternions,
      ‖e₂‖ = 1 → ∀ s ∈ Set.Icc (0 : ℝ) τ,
      |chartedSlope T.a (shiftChart (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V) fun x i =>
          (bondBumps (commonBondLeft Y Y' (r / 2)) dc x i + t • bondBumps (commonBondLeft Y Y' (r / 2)) c x i) +
            s • bondBump ((commonBondLeft Y Y' (r / 2)) q).1 e₂ x i) V ((commonBondLeft Y Y' (r / 2)) q₀).1 e -
        chartedSlope T.a (shiftChart (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V') fun x i =>
          ((0 : imaginaryQuaternions) + t • bondBumps (commonBondRight Y Y' (r / 2)) c x i) +
            s • bondBump ((commonBondRight Y Y' (r / 2)) q).1 e₂ x i) V'
              ((commonBondRight Y Y' (r / 2)) q₀).1 e| ≤ Mh * ‖e‖ := by
    intro q₀ h₀ e t ht q e₂ he₂ s hs₁
    refine abs_chartedSlope_sub_le_of_unit hCE hO hs2 hO' hs2' hSide hSide' (hmove₁ t ht q e₂ he₂ s hs₁)
      (hmove₂ t ht q e₂ he₂ s hs₁) _ _
      (fun e' he' => ?_) e
    rw [hMh]
    refine hCsl F F' _ _ V V' Y Y' (r / 2) (by omega) hFc hFc' hFt2 (hpoint _ (hmove₁ t ht q e₂ he₂ s hs₁))
      (hpoint' _ (hmove₂ t ht q e₂ he₂ s hs₁)) (agreeOnBall_mono hagree (by omega)) (fun h o i hh ho hb => ?_)
      q₀.1.1 q₀.1.2.1 q₀.1.2.2 e' (isFineBondWithinRadius_mono (box₀ q₀ h₀) (by omega)) he'
    have ho' : o ∈ centredCube F.blockSide := hFL.symm ▸ ho
    have hb' := fineBondAt_mem_chordBonds_transfer hSt hCv hO hO' hLL hs2 hs2' Y Y' ho' hb
    have hmem : (h, o, i) ∈ commonBondOffsets Y Y' (r / 2) := Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨(mem_centredCube_odd _ _).2 hh, Finset.mem_product.mpr ⟨ho', Finset.mem_univ _⟩⟩,
        hb, hb'⟩
    exact shiftChart_commonBond_eq hj hj' _ _ c dc hdc t s q e₂ ⟨(h, o, i), hmem⟩
  obtain ⟨E₉, hE₉⟩ : ∃ E₉, E₉ = Real.exp (-(2 ^ 8 * T.κ * r)) := ⟨_, rfl⟩
  have hE₉0 : 0 ≤ E₉ := by
    rw [hE₉]
    exact (Real.exp_pos _).le
  have hI : ∀ q₀ : ↥(commonBondOffsets Y Y' (r / 2)), q₀.1.1 = cc.1 → ∀ e : imaginaryQuaternions,
      x * |chartedSlope T.a (shiftChart (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V) fun _ _ => 0) V
          ((commonBondLeft Y Y' (r / 2)) q₀).1 e -
        chartedSlope T.a (shiftChart (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V') fun _ _ => 0) V'
          ((commonBondRight Y Y' (r / 2)) q₀).1 e| ≤ (Cw * E₉) * ‖e‖ := by
    intro q₀ h₀ e
    have hz : ∀ (x : F.Site F.depth) (i : Fin 4), ‖(0 : imaginaryQuaternions)‖ ≤ m₀ := fun _ _ => by
      simpa using hm₀.le
    have hz' : ∀ (x : F'.Site F'.depth) (i : Fin 4), ‖(0 : imaginaryQuaternions)‖ ≤ m₀ := fun _ _ => by
      simpa using hm₀.le
    have e3 : shiftChart (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V) (fun _ _ => 0) =
        (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V) := by
      funext y i
      simp [shiftChart]
    have e3' : shiftChart (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V') (fun _ _ => 0) =
        (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V') := by
      funext y i
      simp [shiftChart]
    have hU : ∀ e' : imaginaryQuaternions, ‖e'‖ = 1 →
        |chartedSlope T.a (shiftChart (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V) fun _ _ => 0) V
            ((commonBondLeft Y Y' (r / 2)) q₀).1 e' -
          chartedSlope T.a (shiftChart (frameCoordField star T.a T.chainParams.ρA (frameRadius x) V') fun _ _ => 0) V'
            ((commonBondRight Y Y' (r / 2)) q₀).1 e'| ≤ (Cw * E₉) / x := by
      intro e' he'
      have h3 := hSl q₀.1.1 q₀.1.2.1 q₀.1.2.2 e' (isFineBondWithinRadius_mono (box₀ q₀ h₀) (by omega)) he'
      rw [le_div_iff₀ hx1, mul_comm, hE₉, e3, e3']
      exact h3
    have h4 := abs_chartedSlope_sub_le_of_unit hCE hO hs2 hO' hs2' hSide hSide' hz hz' _ _ hU e
    calc _ ≤ x * ((Cw * E₉) / x * ‖e‖) := mul_le_mul_of_nonneg_left h4 hx1.le
      _ = _ := by field_simp
  have hI0 : 0 ≤ Cw * E₉ := mul_nonneg hCw0 hE₉0
  have hSw : ∑ q, Real.exp (-(T.chainParams.δ₁ / 2 *
      cellSupDist (enclosingCell ((commonBondLeft Y Y' (r / 2)) q).1.1) (offsetCell Y (r / 8) cc))) ≤ S := by
    have e : ∀ q, Real.exp (-(T.chainParams.δ₁ / 2 *
        cellSupDist (enclosingCell ((commonBondLeft Y Y' (r / 2)) q).1.1) (offsetCell Y (r / 8) cc))) =
        (fun b => Real.exp (-(T.chainParams.δ₁ / 2 * cellDistReal F (offsetCell Y (r / 8) cc) (chordBondCell F b))))
          ((commonBondLeft Y Y' (r / 2)) q) := by
      intro q
      simp only [cellDistReal, chordBondCell]
      rw [cellSupDist_comm]
    rw [Finset.sum_congr rfl (fun q _ => e q)]
    exact (sum_comp_injective_le hj
      (fun b => Real.exp (-(T.chainParams.δ₁ / 2 * cellDistReal F (offsetCell Y (r / 8) cc) (chordBondCell F b))))
      (fun b => (Real.exp_pos _).le)).trans (hPl (offsetCell Y (r / 8) cc))
  obtain ⟨Kp, hKp⟩ : ∃ Kp, Kp = 2 * Csl + 54 * Ck 3 := ⟨_, rfl⟩
  have hKp0 : 0 ≤ Kp := by
    rw [hKp]
    positivity
  have hQ0 : 0 ≤ 18 * Ck 2 := by positivity
  have hPn : 2 * Mh / τ + 2 * (27 * Ck 3) * τ ≤ Kp * Real.exp (-(T.chainParams.δ₂ * r)) := by
    have hL1 : (2 : ℝ) ^ 40 ≤ T.L := by exact_mod_cast hL40
    have hR1 : (r : ℝ) ≤ 2 * ((r / 2 : ℕ) : ℝ) + 1 := by
      have : r ≤ 2 * (r / 2) + 1 := by omega
      exact_mod_cast this
    have hr64' : (64 : ℝ) ≤ r := by exact_mod_cast hr64
    have hEx : 2 * (r : ℝ) ≤ (T.L : ℝ) * (((r / 2 : ℕ) : ℝ) / 2) - 2 * T.L - 1 := by
      have h3 : (T.L : ℝ) * (((r : ℝ) - 9) / 4) ≤ (T.L : ℝ) * (((r / 2 : ℕ) : ℝ) / 2) - 2 * T.L := by
        have : ((r : ℝ) - 9) / 4 ≤ ((r / 2 : ℕ) : ℝ) / 2 - 2 := by linarith
        have h4 := mul_le_mul_of_nonneg_left this hLr.le
        linarith
      have h5 : (64 : ℝ) * (((r : ℝ) - 9) / 4) ≤ (T.L : ℝ) * (((r : ℝ) - 9) / 4) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      linarith
    have hMτ : Mh ≤ Csl * (τ * τ) := by
      rw [hMh, hτd, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCsl0
      have := mul_le_mul_of_nonneg_left hEx hδ₂.le
      linarith
    have h6 : 2 * Mh / τ ≤ 2 * Csl * τ := by
      rw [div_le_iff₀ hτ0]
      linarith
    rw [← hτd, hKp]
    linarith
  have hR : ∀ q, min (Kp * Real.exp (-(T.chainParams.δ₂ * r)))
      (18 * Ck 2 * Real.exp (-(T.chainParams.δ₁ *
        cellSupDist (enclosingCell ((commonBondLeft Y Y' (r / 2)) q).1.1) (offsetCell Y (r / 8) cc)))) ≤
      ((Kp + 18 * Ck 2) * Real.exp (-(T.chainParams.δ₂ * r / 2))) *
        Real.exp (-(T.chainParams.δ₁ / 2 *
          cellSupDist (enclosingCell ((commonBondLeft Y Y' (r / 2)) q).1.1) (offsetCell Y (r / 8) cc))) :=
    fun q => min_exp_le_mul_exp hKp0 hQ0
  have hKq0 : 0 ≤ Kp + 18 * Ck 2 := by linarith
  subst hc
  have hcore := abs_slopeComponent_sub_le_at_cell hCE hO hs2 hO' hs2' (δ₁ := T.chainParams.δ₁) (C2 := Ck 2) (C3 := Ck 3)
    (m := m₀) (Mh := Mh) (τ := τ)
    (D := D) (P := T.ballRadius) (Pn := Kp * Real.exp (-(T.chainParams.δ₂ * r)))
    (R := (Kp + 18 * Ck 2) * Real.exp (-(T.chainParams.δ₂ * r / 2))) (I := Cw * E₉) (S := S) (x := x) (κ := T.κ)
    (ρA := T.chainParams.ρA) star (frameRadius x) hSide hSide' hδ₁.le hC2 hC3 hτ0 hx1.le hj hj' ζ dc hDc hρ0 hP hm hD0
    (mul_nonneg hKq0 (Real.exp_pos _).le) (offsetCell Y (r / 8) cc) (offsetCell Y' (r / 8) cc)
    (fun q => q.1.1 = cc.1)
    hZ hZ' hdist hM hPn hR hI hI0 hSw hκ1
  obtain ⟨E₂, hE₂⟩ : ∃ E₂, E₂ = Real.exp (-(2 * T.κ * r)) := ⟨_, rfl⟩
  have hN0 : 0 ≤ weightedSqNormAt T.κ (chordBondCell F) (cellDistReal F) (offsetCell Y (r / 8) cc)
      (zeroExtensionL (commonBondLeft Y Y' (r / 2)) ζ) := by
    unfold weightedSqNormAt
    exact Finset.sum_nonneg fun b _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hρ1 : T.ballRadius ≤ 1 := hρσ.trans hσ1
  rw [← hE₂]
  refine final_constant_bound (Kq := Kp + 18 * Ck 2) (E₈ := E₈) (E₉ := E₉) (Cw := Cw) (σ := T.σ) hcore hS0 hx1.le
    hN0 hC3 rfl hCw0
    hρ0 hρ1 hDd hCσ1 hCs0 ?_ hKq0 ?_ ?_ hE₉0 hE₈0 ?_ h1 ?_
  · rw [hE₈]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hKq0
    have := mul_nonneg hδ₂.le hrR
    linarith
  · rw [hE₉, hE₂]
    apply Real.exp_le_exp.mpr
    have := mul_nonneg hκ0.le hrR
    linarith
  · rw [hE₈, hE₂]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hκ2 hrR
    linarith
  · rw [hE₂]
    exact (Real.exp_pos _).le
  · rw [hKp]
    have e : 2 * Csl + 54 * Ck 3 + 18 * Ck 2 = 2 * Csl + 54 * Ck 3 + 18 * Ck 2 := rfl
    exact h2
end
end SlopeComponentBounds
set_option maxHeartbeats 4000000 in
open SlopeComponentBounds ChartSlopes in
theorem slopeComponentsCloseOnTwoTori_holds (hFr : FrameBoundsEventually) (hSl : ChartedSlopeComparison)
    (hK : ChartEnergyKernelBound) (hCE : ChartedEnergyInCoordinates)
    (hCB : commonBondsOfTwoTori) (hSt : SiteDecomposition) (hCv : BlocksCoverLowerLevel)
    (hexp : QuaternionExp.ExpUnitLipschitzInjective) (hhol : PathHolonomyLipschitz) :
    SlopeComponentsCloseOnTwoTori := by
  intro a ha
  obtain ⟨L₀, hL₀⟩ := hFr a ha
  refine ⟨max L₀ (2 ^ 40), fun L hodd hLL c hc => ?_⟩
  have hL40 : 2 ^ 40 ≤ L := le_trans (le_max_right _ _) hLL
  obtain ⟨Ct₀, hCt₀⟩ := hL₀ L hodd (le_trans (le_max_left _ _) hLL) c hc
  have hδ₁ : 0 < c.δ₁ := hc.positivity.1
  obtain ⟨hρp, hρ1, hs₀p, hδ₂, _, _, _, _⟩ := hc.classical.1
  have hs₀ : c.s₀ ≤ c.σA := by
    have := hc.inequalities.2.2.1
    linarith
  obtain ⟨Ck, hCk0, hCk⟩ := hK a L c ha hodd hL40 hc
  obtain ⟨Csl, hCsl0, hCsl⟩ := hSl a L c ha hodd hL40 hc
  obtain ⟨S₀, hS₀⟩ := (hCB L hodd).1 c.δ₁ hδ₁
  obtain ⟨S, hSd⟩ : ∃ S, S = max S₀ 1 := ⟨_, rfl⟩
  have hS1 : 1 ≤ S := by
    rw [hSd]
    exact le_max_right _ _
  have hSS : S₀ ≤ S := by
    rw [hSd]
    exact le_max_left _ _
  have hS0 : 0 ≤ S := by linarith
  obtain ⟨B₂, hB₂⟩ : ∃ B₂, B₂ = S * ((27 * Ck 3 * S + (2 * Csl + 54 * Ck 3 + 18 * Ck 2)) * ((S + 1) / 2)) :=
    ⟨_, rfl⟩
  have hLr : (0 : ℝ) < L := by
    have : 0 < L := hodd.pos
    exact_mod_cast this
  obtain ⟨m₀, hm₀d⟩ : ∃ m₀, m₀ = min (c.s₀ / 8) (1 / (128 * (L : ℝ))) := ⟨_, rfl⟩
  have hm₀ : 0 < m₀ := by
    rw [hm₀d]
    exact lt_min (by positivity) (by positivity)
  have hm₁ : m₀ ≤ c.s₀ / 8 := by
    rw [hm₀d]
    exact min_le_left _ _
  have hm₂ : m₀ ≤ 1 / (128 * (L : ℝ)) := by
    rw [hm₀d]
    exact min_le_right _ _
  have hm₃ : m₀ ≤ 1 := by
    refine hm₂.trans ?_
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ L := by
      have : 1 ≤ L := hodd.pos
      exact_mod_cast this
    linarith
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, Real.exp (-(c.δ₂ * N₁)) ≤ m₀ / 2 := by
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt (-Real.log (m₀ / 2) / c.δ₂)
    refine ⟨N₁, ?_⟩
    rw [div_lt_iff₀ hδ₂] at hN₁
    have h1 : -(c.δ₂ * N₁) ≤ Real.log (m₀ / 2) := by linarith
    have h2 := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by positivity)] at h2
  refine ⟨max (4 * S * Ct₀) (max (4 * B₂) 1), fun Ct hCt => ?_⟩
  have hCt1 : 1 ≤ Ct := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCt
  have hCtB : 4 * B₂ ≤ Ct := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCt
  have hCtS : 4 * S * Ct₀ ≤ Ct := le_trans (le_max_left _ _) hCt
  have h4S : 0 < 4 * S := by linarith
  obtain ⟨κ₀, hκ₀, hκ⟩ := hCt₀ (Ct / (4 * S)) (by
    rw [le_div_iff₀ h4S]
    linarith)
  refine ⟨min κ₀ (min (c.δ₂ / 16) (c.δ₁ / 2 ^ 7)), lt_min hκ₀ (lt_min (by positivity) (by positivity)),
    fun κ hκp hκle => ?_⟩
  have hκ₁ : κ ≤ κ₀ := hκle.trans (min_le_left _ _)
  have hκ₂ : 16 * κ ≤ c.δ₂ := by
    have := hκle.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hκ₃ : 2 ^ 7 * κ ≤ c.δ₁ := by
    have := hκle.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  obtain ⟨η₀, hη₀, hη⟩ := hκ κ hκp hκ₁
  refine ⟨η₀, hη₀, fun η₃ h₁ h₂ h₃ => ?_⟩
  obtain ⟨N₀, hN⟩ := hη η₃ h₁ h₂ h₃
  refine ⟨max N₀ (max N₁ 64), fun nss hnss => ?_⟩
  have hn₁ : N₀ ≤ nss := le_trans (le_max_left _ _) hnss
  have hn₂ : N₁ ≤ nss := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnss
  have hn₃ : 64 ≤ nss := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnss
  obtain ⟨σ₀, hσ₀, hσ⟩ := hN nss hn₁
  have hCtp : 0 < Ct + 1 := by linarith
  refine ⟨min σ₀ (min (m₀ / (2 * (Ct + 1))) (c.s₀ / 2)), lt_min hσ₀ (lt_min (by positivity) (by positivity)),
    fun σ hσp hσle p hp => ?_⟩
  have hσ₁ : σ ≤ σ₀ := hσle.trans (min_le_left _ _)
  have hσ₂ : σ ≤ m₀ / (2 * (Ct + 1)) := hσle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσ₃ : σ ≤ c.s₀ / 2 := hσle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₀, hC₀⟩ := hσ σ hσp hσ₁ p hp
  refine ⟨C₀, fun Cs hCs E hE => ?_⟩
  obtain ⟨mn, hmn⟩ := hC₀ Cs hCs E hE
  refine ⟨mn, fun n₀ hn₀ => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hmn n₀ hn₀
  refine ⟨C₁, fun CE hCE' => ?_⟩
  obtain ⟨y₀, hy⟩ := hC₁ CE hCE'
  refine ⟨y₀, fun y₁ hy₁ => ?_⟩
  obtain ⟨Cf, Cw, hCf0, hCw1, hCfCt, hCwCt, hL40', h64, hκ1', hσ1, hr1, hr2, hσA, hy1, hay, hAll⟩ := hy y₁ hy₁
  change Cw ≤ Ct / (4 * S) at hCwCt
  change 64 ≤ n₀ at h64
  change σ ≤ 1 at hσ1
  change 1 ≤ y₁ at hy1
  have hCw0 : 0 ≤ Cw := by linarith
  have hCwCt' : Cw ≤ Ct := by
    refine hCwCt.trans ?_
    rw [div_le_iff₀ h4S]
    have h3 := mul_nonneg (by linarith : (0 : ℝ) ≤ Ct) (by linarith : (0 : ℝ) ≤ 4 * S - 1)
    linarith
  have hSCw : S * Cw ≤ Ct / 4 := by
    rw [le_div_iff₀ h4S] at hCwCt
    linarith
  have hCσ : Cw * σ + σ ≤ m₀ / 2 := by
    rw [le_div_iff₀ (by positivity)] at hσ₂
    have h3 : (Cw + 1) * σ ≤ (Ct + 1) * σ := mul_le_mul_of_nonneg_right (by linarith) hσp.le
    linarith
  have hCσ1 : Cw * σ ≤ 1 := by linarith
  have hτe : Real.exp (-(c.δ₂ * nss)) ≤ m₀ / 2 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hN₁
    have h3 : (N₁ : ℝ) ≤ nss := by exact_mod_cast hn₂
    have := mul_le_mul_of_nonneg_left h3 hδ₂.le
    linarith
  intro t x F F' V V' Y Y' r star hTwo
  have hx1 : 0 < x := by
    have := hTwo.coupling_le
    change y₁ ≤ x at this
    linarith
  have hV := hAll t x F V hTwo.coupling_le hTwo.top hTwo.small
  have hV' := hAll t x F' V' hTwo.coupling_le hTwo.top' hTwo.small'
  have hloc := hV.2.2.2 F' V' Y Y' r hTwo.top' hTwo.small' hTwo.agree
  exact nearCellsClose_of_agreeingTopPair hexp hhol hCE hSt hCv _ (Ck := Ck) (Csl := Csl) (S := S) (Cw := Cw)
    (m₀ := m₀) hodd hL40 h64 hδ₁ hδ₂ hs₀
    (fun F w V h1 h2 k q => hCk F w V h1 h2 k q) hCsl (hCk0 2).le (hCk0 3).le hCsl0.le hCw0 hS0 hm₀ hm₁ hm₂ hσp
    hσ1 hσ₃ hCσ hCσ1
    hκp hκ₃ hκ₂ hn₃ hτe hx1 hTwo
    (fun F F' Y Y' r n n' h1 h2 h3 h4 h5 h6 => (hCB L hodd).2 F F' Y Y' r n n' h1 h2 h3 h4 h5 h6)
    (fun F n _ h1 h2 h3 => by
      have hp := hS₀ F n h1 h2 h3
      exact { self := hp.self, symm := hp.symm, triangle := hp.triangle, bonds := fun Z => (hp.bonds Z).trans hSS,
              cells := fun Z => (hp.cells Z).trans hSS })
    (hV.2.1 star) (hV'.2.1 star) (hloc.1 star) (hloc.2 star) hSCw (by
      change S * ((27 * Ck 3 * S + (2 * Csl + 54 * Ck 3 + 18 * Ck 2)) * ((S + 1) / 2)) ≤ Ct / 4
      rw [← hB₂]
      linarith)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
