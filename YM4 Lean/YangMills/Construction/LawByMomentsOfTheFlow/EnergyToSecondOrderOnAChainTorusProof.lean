import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionsOfTheChartEnergyProof
import YangMills.Construction.LawByMomentsOfTheFlow.EnergyToSecondOrderOnAChainTorus
import YangMills.Construction.ResponseInTheExpansion.SlopeToSecondOrderProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.MomentLaw
namespace SecondOrderCalculus
namespace Smoothness
variable {F : BlockFrame}
theorem contDiffAt_chartedEnergyAt {a : ℝ} {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top}
    (h : ∀ (k : ℕ) (q : Fin k → ChartDirection F), AnalyticAt ℝ (chartRestriction a w V q) 0) :
    ContDiffAt ℝ 3 (chartedEnergyAt a w V) 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartEnergyRows.contDiffAt_chartedEnergyAt <;> assumption
end Smoothness
section Calculus
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
theorem contDiffAt_of_contDiffAt_comp_add {f : P → ℝ} {η : P} (h : ContDiffAt ℝ 3 (fun ζ => f (η + ζ)) 0) :
    ContDiffAt ℝ 3 f η := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.contDiffAt_of_comp_add_left <;> assumption
theorem fderiv_three_comp_add_left (f : P → ℝ) (ζ : P) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ fun ξ => f (ζ + ξ))) 0 = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) ζ := by apply _root_.YangMills.Construction.WeightedResponses.SlopeExpansion.fderiv_three_comp_add_left <;> assumption
theorem iteratedFDeriv_three_comp_clm {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : P → ℝ}
    (hf : ContDiffAt ℝ 3 f 0) (A : G →L[ℝ] P) (m : Fin 3 → G) :
    iteratedFDeriv ℝ 3 (f ∘ A) 0 m = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) 0 (A (m 0)) (A (m 1)) (A (m 2)) := by apply _root_.YangMills.Construction.WeightedResponses.SlopeExpansion.iteratedFDeriv_three_comp_clm <;> assumption
theorem abs_taylor_second_order_le {E : P → ℝ} {η u : P} {M : ℝ} (hM0 : 0 ≤ M)
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 E (t • η))
    (hb : ∀ t ∈ Set.Ico (0 : ℝ) 1, |fderiv ℝ (fderiv ℝ (fderiv ℝ E)) (t • η) η η u| ≤ M) :
    |fderiv ℝ E η u - fderiv ℝ E 0 u - fderiv ℝ (fun ζ => fderiv ℝ E ζ u) 0 η| ≤ M := by apply _root_.YangMills.Construction.WeightedResponses.SlopeExpansion.abs_fderiv_sub_taylor_le <;> assumption
end Calculus
variable {F : BlockFrame}
abbrev ChordBond (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F))
theorem norm_toImaginary_eq (v : BondVector) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.norm_toImaginary <;> assumption
theorem stepCoordinates_add (η ζ : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (η + ζ) x i = stepCoordinates η x i + stepCoordinates ζ x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_add <;> assumption
theorem stepCoordinates_smul (r : ℝ) (η : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (r • η) x i = r • stepCoordinates η x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_smul <;> assumption
theorem stepCoordinates_bondVariation (b : ChordBond F) (e : BondVector) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (bondVariation b e : StepVariable (finiteCells F)) x i =
      directionCoordinate (Sum.inl (b.1.1, b.1.2, toImaginary e) : ChartDirection F) x i := by apply _root_.YangMills.Construction.WeightedResponses.SlopeExpansion.stepCoordinates_bondVariation <;> assumption
theorem chartedEnergyAt_add (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (η ζ : StepVariable (finiteCells F)) :
    chartedEnergyAt a w V (η + ζ) = chartedEnergyAt a (shiftCoordinates w η) V ζ := by apply _root_.YangMills.Construction.ResponseInTheExpansion.BasePointEnergy.chartedEnergyAt_add <;> assumption
theorem leftTranslate_zero (V : F.GaugeField F.top) :
    leftTranslate (fun _ _ => (0 : imaginaryQuaternions)) V = V := by apply _root_.YangMills.SharedProofs.p46723 <;> assumption
def directionsMap (u : Fin 3 → StepVariable (finiteCells F)) :
    (Fin 3 → ℝ) →L[ℝ] StepVariable (finiteCells F) :=
  ∑ l, (ContinuousLinearMap.proj l : (Fin 3 → ℝ) →L[ℝ] ℝ).smulRight (u l)
theorem directionsMap_apply (u : Fin 3 → StepVariable (finiteCells F)) (σ : Fin 3 → ℝ) :
    directionsMap u σ = σ 0 • u 0 + σ 1 • u 1 + σ 2 • u 2 := by
  simp [directionsMap, Fin.sum_univ_three]
theorem directionsMap_single (u : Fin 3 → StepVariable (finiteCells F)) (l : Fin 3) :
    directionsMap u (Pi.single l 1) = u l := by
  rw [directionsMap_apply]
  fin_cases l <;> simp
theorem chartRestriction_eq_comp (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (ζ : StepVariable (finiteCells F))
    (b : Fin 3 → ChordBond F) (e : Fin 3 → BondVector) :
    chartRestriction a (shiftCoordinates w ζ) V
        (fun l => (Sum.inl ((b l).1.1, (b l).1.2, toImaginary (e l)) : ChartDirection F)) =
      (fun ξ => chartedEnergyAt a w V (ζ + ξ)) ∘ directionsMap fun l => bondVariation (b l) (e l) := by
  funext σ
  simp only [Function.comp_apply]
  unfold chartRestriction chartedEnergyAt
  have hm : (fun (y : F.Site F.top) (i : Fin 4) => ∑ l, σ l •
      directionMove (Sum.inl ((b l).1.1, (b l).1.2, toImaginary (e l)) : ChartDirection F) y i) =
      fun _ _ => (0 : imaginaryQuaternions) := by
    funext y i
    simp [directionMove]
  rw [hm, leftTranslate_zero]
  congr 1
  funext x i
  rw [directionsMap_apply, stepCoordinates_add, stepCoordinates_add, stepCoordinates_add,
    stepCoordinates_smul, stepCoordinates_smul, stepCoordinates_smul,
    stepCoordinates_bondVariation, stepCoordinates_bondVariation, stepCoordinates_bondVariation,
    Fin.sum_univ_three]
  simp only [shiftCoordinates, add_assoc]
theorem bondVariation_eq_norm_smul (b : ChordBond F) {e : BondVector} (he : e ≠ 0) :
    (bondVariation b e : StepVariable (finiteCells F)) = ‖e‖ • bondVariation b (‖e‖⁻¹ • e) := by apply _root_.YangMills.Construction.WeightedResponses.SlopeExpansion.bondVariation_eq_norm_smul <;> assumption
theorem bondVariation_zero (b : ChordBond F) :
    (bondVariation b (0 : BondVector) : StepVariable (finiteCells F)) = 0 := by apply _root_.YangMills.Construction.WeightedResponses.SlopeExpansion.bondVariation_zero <;> assumption
theorem norm_inv_norm_smul_self {e : BondVector} (he : e ≠ 0) : ‖(‖e‖⁻¹ • e : BondVector)‖ = 1 := by apply _root_.YangMills.Construction.WeightedResponses.SlopeExpansion.norm_inv_norm_smul <;> assumption
theorem cellSupDist_le_directionDiameter {k : ℕ} (q : Fin k → ChartDirection F) (l l' : Fin k) :
    cellSupDist (directionCell (q l)) (directionCell (q l')) ≤ directionDiameter q := by apply _root_.YangMills.Construction.WeightedResponses.SlopeExpansion.cellSupDist_le_directionDiameter <;> assumption
theorem eq_sum_bondVariation (η : StepVariable (finiteCells F)) :
    η = ∑ b' : ChordBond F, (bondVariation b' (η b') : StepVariable (finiteCells F)) := by apply _root_.YangMills.Construction.WeightedResponses.SlopeExpansion.eq_sum_bondVariation <;> assumption
theorem trilinear_sum_sum {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {κ : Type} [Fintype κ]
    (T : P →L[ℝ] P →L[ℝ] P →L[ℝ] ℝ) (a : κ → P) (u : P) :
    T (∑ i, a i) (∑ j, a j) u = ∑ i, ∑ j, T (a i) (a j) u := by apply _root_.YangMills.Construction.WeightedResponses.SlopeExpansion.trilinear_sum_sum <;> assumption
end SecondOrderCalculus
open SecondOrderCalculus in
set_option maxHeartbeats 4000000 in
theorem chartEnergySecondOrder (hK : ChartEnergyKernelBound) :
    chartEnergySecondOrderStatement := by
  intro a L c ha hL hL0 hc
  obtain ⟨Ck, hCk, hker⟩ := hK a L c ha hL hL0 hc
  refine ⟨Ck 3, hCk 3, ?_⟩
  intro F V w hCT
  set E : StepVariable (finiteCells F) → ℝ := chartedEnergyAt a w V with hE
  have hsm0 : ∀ ζ : StepVariable (finiteCells F), IsAdmissibleChartPoint L c.σA (shiftCoordinates w ζ) V →
      ContDiffAt ℝ 3 (chartedEnergyAt a (shiftCoordinates w ζ) V) 0 := fun ζ hz =>
    SecondOrderCalculus.Smoothness.contDiffAt_chartedEnergyAt fun k q =>
      (hker F (shiftCoordinates w ζ) V hCT hz k q).1
  have hsm : ∀ ζ : StepVariable (finiteCells F), IsAdmissibleChartPoint L c.σA (shiftCoordinates w ζ) V →
      ContDiffAt ℝ 3 E ζ := by
    intro ζ hz
    apply contDiffAt_of_contDiffAt_comp_add
    have : (fun ξ => E (ζ + ξ)) = chartedEnergyAt a (shiftCoordinates w ζ) V :=
      funext fun ξ => chartedEnergyAt_add a w V ζ ξ
    rw [this]
    exact hsm0 ζ hz
  refine ⟨hsm, ?_⟩
  intro η hpts b e he
  have hthird : ∀ ζ : StepVariable (finiteCells F), IsAdmissibleChartPoint L c.σA (shiftCoordinates w ζ) V →
      ∀ (bb : Fin 3 → ChordBond F) (ee : Fin 3 → BondVector), (∀ l, ‖ee l‖ = 1) →
      |fderiv ℝ (fderiv ℝ (fderiv ℝ E)) ζ (bondVariation (bb 0) (ee 0)) (bondVariation (bb 1) (ee 1))
          (bondVariation (bb 2) (ee 2))| ≤
        Ck 3 * Real.exp (-(c.δ₁ * directionDiameter
          (fun l => (Sum.inl ((bb l).1.1, (bb l).1.2, toImaginary (ee l)) : ChartDirection F)))) := by
    intro ζ hz bb ee hu
    have hk := ((hker F (shiftCoordinates w ζ) V hCT hz 3
      (fun l => (Sum.inl ((bb l).1.1, (bb l).1.2, toImaginary (ee l)) : ChartDirection F))).2 (by norm_num)
      (fun l => by
        change ‖toImaginary (ee l)‖ = 1
        rw [norm_toImaginary_eq, hu]))
    unfold chartMixedDeriv at hk
    rw [chartRestriction_eq_comp] at hk
    have hf : ContDiffAt ℝ 3 (fun ξ => E (ζ + ξ)) 0 := by
      have : (fun ξ => E (ζ + ξ)) = chartedEnergyAt a (shiftCoordinates w ζ) V :=
        funext fun ξ => chartedEnergyAt_add a w V ζ ξ
      rw [this]
      exact hsm0 _ hz
    rw [iteratedFDeriv_three_comp_clm hf, directionsMap_single, directionsMap_single, directionsMap_single,
      fderiv_three_comp_add_left] at hk
    exact hk
  set kk : ChordBond F → ℝ := fun b' => Real.exp (-(c.δ₁ / 2 * chordBondDist F b b')) with hkk
  have hkk0 : ∀ b', 0 < kk b' := fun b' => Real.exp_pos _
  have hδ₁ : 0 < c.δ₁ := hc.positivity.1
  have hC3 : 0 < Ck 3 := hCk 3
  have hk2 : ∀ ζ : StepVariable (finiteCells F), IsAdmissibleChartPoint L c.σA (shiftCoordinates w ζ) V →
      ∀ (b₁ b₂ : ChordBond F) (e₁ e₂ : BondVector),
      |fderiv ℝ (fderiv ℝ (fderiv ℝ E)) ζ (bondVariation b₁ e₁) (bondVariation b₂ e₂) (bondVariation b e)| ≤
        Ck 3 * (kk b₁ * ‖e₁‖) * (kk b₂ * ‖e₂‖) := by
    intro ζ hz b₁ b₂ e₁ e₂
    by_cases h1 : e₁ = 0
    · subst h1
      rw [bondVariation_zero]
      simp
    by_cases h2 : e₂ = 0
    · subst h2
      rw [bondVariation_zero]
      simp
    have hb := hthird ζ hz ![b₁, b₂, b] ![‖e₁‖⁻¹ • e₁, ‖e₂‖⁻¹ • e₂, e] (by
      intro l
      fin_cases l
      · exact norm_inv_norm_smul_self h1
      · exact norm_inv_norm_smul_self h2
      · exact he)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hb
    set q : Fin 3 → ChartDirection F := fun l => (Sum.inl ((![b₁, b₂, b] l).1.1, (![b₁, b₂, b] l).1.2,
      toImaginary ((![‖e₁‖⁻¹ • e₁, ‖e₂‖⁻¹ • e₂, e] : Fin 3 → BondVector) l)) : ChartDirection F) with hq
    have hd1 : chordBondDist F b b₁ ≤ directionDiameter q := by
      exact show (cellSupDist (directionCell (q 2)) (directionCell (q 0)) : ℝ) ≤ directionDiameter q from by
        exact_mod_cast cellSupDist_le_directionDiameter q 2 0
    have hd2 : chordBondDist F b b₂ ≤ directionDiameter q := by
      exact show (cellSupDist (directionCell (q 2)) (directionCell (q 1)) : ℝ) ≤ directionDiameter q from by
        exact_mod_cast cellSupDist_le_directionDiameter q 2 1
    have hexp : Real.exp (-(c.δ₁ * directionDiameter q)) ≤ kk b₁ * kk b₂ := by
      simp only [hkk]
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith
    rw [bondVariation_eq_norm_smul b₁ h1, bondVariation_eq_norm_smul b₂ h2]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul, abs_norm]
    have hn1 := norm_nonneg e₁
    have hn2 := norm_nonneg e₂
    have hb' := hb.trans (mul_le_mul_of_nonneg_left hexp hC3.le)
    calc _ ≤ ‖e₂‖ * (‖e₁‖ * (Ck 3 * (kk b₁ * kk b₂))) := by gcongr
      _ = Ck 3 * (kk b₁ * ‖e₁‖) * (kk b₂ * ‖e₂‖) := by ring
  have hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 E (t • η) := fun t ht => hsm _ (hpts t ht.1 ht.2)
  have hM0 : 0 ≤ Ck 3 * (∑ b', kk b' * ‖η b'‖) ^ 2 := by positivity
  refine abs_taylor_second_order_le (u := bondVariation b e) hM0 hC fun t ht => ?_
  have hz := hpts t ht.1 ht.2.le
  have h1 := trilinear_sum_sum (fderiv ℝ (fderiv ℝ (fderiv ℝ E)) (t • η))
    (fun b' : ChordBond F => (bondVariation b' (η b') : StepVariable (finiteCells F))) (bondVariation b e)
  rw [← eq_sum_bondVariation] at h1
  rw [h1]
  calc _ ≤ ∑ b', |∑ b'', fderiv ℝ (fderiv ℝ (fderiv ℝ E)) (t • η) (bondVariation b' (η b'))
        (bondVariation b'' (η b'')) (bondVariation b e)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b', ∑ b'', |fderiv ℝ (fderiv ℝ (fderiv ℝ E)) (t • η) (bondVariation b' (η b'))
        (bondVariation b'' (η b'')) (bondVariation b e)| :=
        Finset.sum_le_sum fun b' _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b', ∑ b'', Ck 3 * (kk b' * ‖η b'‖) * (kk b'' * ‖η b''‖) :=
        Finset.sum_le_sum fun b' _ => Finset.sum_le_sum fun b'' _ =>
          hk2 _ hz b' b'' (η b') (η b'')
    _ = _ := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b'' _ => ?_
        ring
end YangMills.Construction.MomentLaw
end
