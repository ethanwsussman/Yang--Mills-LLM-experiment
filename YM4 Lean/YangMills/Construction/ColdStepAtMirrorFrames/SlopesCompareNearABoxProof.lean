import YangMills.Construction.ColdChainAtEveryLevel.LinesOfTheBlocksOfABond
import YangMills.Construction.ColdStepAtMirrorFrames.EnergyAboutAChartPoint
import YangMills.Construction.ColdStepAtMirrorFrames.GlueOfTwoCharts
import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeOfTheChartOnTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.SlopesCompareNearABox
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfADecayOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace ChartSlopeNearBall
variable {F : BlockFrame}
theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem chartedSlope_congr {a : ℝ} {w w₂ : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top}
    (hIso : ImaginaryCoordinatesIsometric) (hodd : Odd F.blockSide) (hpos : ∀ i, 0 < F.extent i)
    (h : ∀ b ∈ chordBonds (finiteCells F), w b.1 b.2 = w₂ b.1 b.2)
    (b : F.Site F.depth × Fin 4) (hb : b ∈ chordBonds (finiteCells F)) (e : imaginaryQuaternions) :
    chartedSlope a w V b e = chartedSlope a w₂ V b e := by
  classical
  unfold chartedSlope
  congr 1
  funext u
  unfold chartedEnergy blockEnergy
  have hcf := hIso.2.2.2.2.2.2 F (Function.update w b.1 (Function.update (w b.1) b.2 (w b.1 b.2 + u • e)))
    (Function.update w₂ b.1 (Function.update (w₂ b.1) b.2 (w₂ b.1 b.2 + u • e))) V hodd hpos (fun c hc => by
      have hwb := h b hb
      by_cases hx : c.1 = b.1
      · rw [hx]
        simp only [Function.update_self]
        by_cases hi : c.2 = b.2
        · rw [hi]
          simp only [Function.update_self, hwb]
        · simp only [Function.update_of_ne hi]
          have := h c hc
          rwa [hx] at this
      · simp only [Function.update_of_ne hx]
        exact h c hc)
  rw [hcf]
end ChartSlopeNearBall
open ChartSlopeNearBall in
theorem chartSlopeBoundNearBall_holds (hEn : ChartEnergyDerivBounds)
    (hSl : ChartedSlopeComparison) (hGl : TwoChartsGlue) (hW : decaySumOnTorusStatement)
    (hIso : ImaginaryCoordinatesIsometric) : ChartSlopeBoundNearBall := by
  intro a L c ha hodd hL hc
  obtain ⟨Ce, hCe, hE⟩ := hEn a L c ha hodd hL hc
  obtain ⟨Cs, hCs, hS⟩ := hSl a L c ha hodd hL hc
  have hδ₁ : 0 < c.δ₁ := hc.positivity.1
  obtain ⟨S, hW'⟩ := hW L c.δ₁ hodd hδ₁
  refine ⟨Cs + Ce * |S|, by positivity, ?_⟩
  intro F F' w w' V V' Y Y' r θ hr1 hT hT' ht hθ hw hw' hag hnear h o i e hbox he
  obtain ⟨hFL, n, hn, hside⟩ := id hT
  obtain ⟨hFL', n', hn', hside'⟩ := id hT'
  have hoddF : Odd F.blockSide := hFL ▸ hodd
  have hs0 : ∀ i, 0 < F.extent i := fun i => by rw [hside i]; omega
  have hs : ∀ i, 2 * r + 2 < F.extent i := fun i => (hag.1 i).resolve_left (hs0 i).ne'
  obtain ⟨Δ, wx, hΔ, _, hwx, heq⟩ := hGl F F' Y Y' r θ w w' (hFL.trans hFL'.symm) hoddF hs hθ
    (by rw [hFL]; exact hnear)
  obtain ⟨_, _, hnorm, honto, hmv, hm0, _⟩ := id hIso
  obtain ⟨e', he'⟩ := honto e
  have hu : ‖e'‖ = 1 := by rw [← hnorm, he', he]
  have hb : fineBondAt Y h o i ∈ chordBonds (finiteCells F) := hbox.2.1
  let b : ↥(chordBonds (finiteCells F)) := ⟨fineBondAt Y h o i, hb⟩
  have hs₀ : 0 < c.s₀ := hc.classical.1.2.2.1
  have hs₀σ : c.s₀ ≤ c.σA := by linarith [hc.inequalities.2.2.1]
  have hsm : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsAdmissibleChartPoint L c.σA (shiftCoordinates w (s • Δ)) V := fun s hs' => by
    have h1 := hw (s • Δ) fun b => by
      have : ‖(s • Δ) b‖ = |s| * ‖Δ b‖ := by simp [norm_smul]
      rw [this]
      have h2 : |s| ≤ 1 := by rw [abs_of_nonneg hs'.1]; exact hs'.2
      have h3 := hΔ b
      nlinarith [norm_nonneg (Δ b), abs_nonneg s]
    exact ⟨h1.coord_small, fun p hp => (h1.small_curvature p hp).trans_le hs₀σ⟩
  have hEd := fun s hs' => hE F w (s • Δ) V hT (hsm s hs')
  set G := chartedEnergyAt a w V with hG
  have hφd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => fderiv ℝ G (s • Δ) (bondVariation b e'))
      (secondDerivAlong G (s • Δ) (bondVariation b e') Δ) (Set.Icc 0 1) s := fun s hs' => by
    have hc2 : ContDiffAt ℝ 1 (fderiv ℝ G) (s • Δ) := (hEd s hs').1.fderiv_right (by norm_num)
    have h1 : DifferentiableAt ℝ (fun ζ => fderiv ℝ G ζ (bondVariation b e')) (s • Δ) :=
      (hc2.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
    have h3 : HasDerivAt (fun s : ℝ => s • Δ) Δ s := by
      simpa using (hasDerivAt_id s).smul_const Δ
    exact (h1.hasFDerivAt.comp_hasDerivAt s h3).hasDerivWithinAt
  have hsum : ∑ b'' : ↥(chordBonds (finiteCells F)), Real.exp (-(c.δ₁ * chordBondDist F b b'')) ≤ |S| := by
    have := (hW' F n hFL (by omega) hside (enclosingCell b.1.1)).1
    refine le_trans (le_of_eq ?_) (this.trans (le_abs_self S))
    refine Finset.sum_congr rfl fun b'' _ => ?_
    unfold chordBondDist
    rw [cellSupDist_comm]
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖secondDerivAlong G (s • Δ) (bondVariation b e') Δ‖ ≤ Ce * |S| * θ := fun s hs' => by
    have e1 : secondDerivAlong G (s • Δ) (bondVariation b e') Δ =
        ∑ b'' : ↥(chordBonds (finiteCells F)), secondDerivAlong G (s • Δ) (bondVariation b e') (bondVariation b'' (Δ b'')) := by
      unfold secondDerivAlong bondVariation
      rw [← map_sum, Finset.univ_sum_single]
    rw [e1, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ b'' ∈ (Finset.univ : Finset ↥(chordBonds (finiteCells F))),
        |secondDerivAlong G (s • Δ) (bondVariation b e') (bondVariation b'' (Δ b''))| ≤
          (Ce * θ) * Real.exp (-(c.δ₁ * chordBondDist F b b'')) := fun b'' _ => by
      have h1 := (hEd s hs').2.2.1 b b'' e' (Δ b'')
      refine h1.trans ?_
      rw [hu]
      have := hΔ b''
      have hpos : 0 ≤ Ce * Real.exp (-(c.δ₁ * chordBondDist F b b'')) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hpos]
    refine (Finset.sum_le_sum this).trans ?_
    rw [← Finset.mul_sum]
    have : Ce * θ * ∑ b'' : ↥(chordBonds (finiteCells F)), Real.exp (-(c.δ₁ * chordBondDist F b b'')) ≤
        Ce * θ * |S| := mul_le_mul_of_nonneg_left hsum (by positivity)
    linarith
  have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hφd hbound
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  have hzero : Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := rfl
  have s0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.2 zero_le_one
  have s1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.2 zero_le_one
  have e0 : chartedSlope a w V b.1 e = fderiv ℝ G ((0 : ℝ) • Δ) (bondVariation b e') := by
    have := (hEd 0 s0).2.1 b e'
    rw [zero_smul, hm0, he'] at this
    rw [zero_smul]
    exact this
  have e1 : chartedSlope a (shiftCoordinates w Δ) V b.1 e = fderiv ℝ G ((1 : ℝ) • Δ) (bondVariation b e') := by
    have := (hEd 1 s1).2.1 b e'
    rw [one_smul, he'] at this
    rw [one_smul]
    exact this
  have e2 : chartedSlope a wx V b.1 e = chartedSlope a (shiftCoordinates w Δ) V b.1 e :=
    chartedSlope_congr hIso hoddF hs0 hwx b.1 b.2 e
  have hfield : chartedField wx V = chartedField (shiftCoordinates w Δ) V := hIso.2.2.2.2.2.2 F _ _ V hoddF hs0 hwx
  have hsmx : IsAdmissibleChartPoint L c.s₀ wx V := by
    have h1 := hw Δ hΔ
    refine ⟨fun b hb => ?_, ?_⟩
    · rw [hwx b hb]
      exact h1.coord_small b hb
    · rw [hfield]
      exact h1.small_curvature
  have hC := hS F F' wx w' V V' Y Y' r hr1 hT hT' ht hsmx hw' hag
    (fun h₁ o₁ i₁ hh₁ ho₁ _ => heq h₁ o₁ i₁ hh₁ (by rw [hFL]; exact ho₁)) h o i e hbox he
  have hmvt' : |chartedSlope a (shiftCoordinates w Δ) V b.1 e - chartedSlope a w V b.1 e| ≤ Ce * |S| * θ := by
    rw [e0, e1]
    simpa using hmvt
  have hb1 : chartedSlope a w V (fineBondAt Y h o i) e = chartedSlope a w V b.1 e := rfl
  rw [hb1]
  have hCb : |chartedSlope a wx V b.1 e - chartedSlope a w' V' (fineBondAt Y' h o i) e| ≤
      Cs * Real.exp (-(c.δ₂ * ((L : ℝ) * ((r : ℝ) / 2) - 2 * L - 1))) := hC
  rw [e2] at hCb
  have htri := abs_sub_le (chartedSlope a w V b.1 e) (chartedSlope a (shiftCoordinates w Δ) V b.1 e)
    (chartedSlope a w' V' (fineBondAt Y' h o i) e)
  rw [abs_sub_comm (chartedSlope a w V b.1 e) (chartedSlope a (shiftCoordinates w Δ) V b.1 e)] at htri
  have hCes : 0 ≤ Ce * |S| := by positivity
  have hexp := Real.exp_pos (-(c.δ₂ * ((L : ℝ) * ((r : ℝ) / 2) - 2 * L - 1)))
  nlinarith [mul_nonneg hCes hexp.le, mul_nonneg hCs.le hθ]
end YangMills.Construction.ColdStepAtMirrorFrames
end
