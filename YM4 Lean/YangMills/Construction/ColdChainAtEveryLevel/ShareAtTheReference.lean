import YangMills.Construction.ColdChainAtEveryLevel.FitsInCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.ShareBelowTheTop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.ReferenceShare
variable {F : BlockAverages.BlockFrame}
open BlockAverages LowerShare
theorem one_sub_re_le_norm_sub_one_sq (g : UnitQuaternion) : 1 - (g : ℍ[ℝ]).re ≤ ‖(g : ℍ[ℝ]) - 1‖ ^ 2 := by
  have h1 := norm_coe_unitQuaternion g
  have h2 : ‖(g : ℍ[ℝ])‖ ^ 2 = 1 := by
    rw [h1]
    norm_num
  rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def'] at h2
  rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  simp only [Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub, Quaternion.re_one,
    Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one, sub_zero]
  nlinarith [sq_nonneg ((g : ℍ[ℝ]).re - 1)]
theorem gaugedBlockFit_one_le {j : ℕ} (X : F.GaugeField j) (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4)
    (hm : ‖contourAverage X c‖ ≤ 1) :
    gaugedBlockFit X (fun _ => 1) X' c ≤ ‖((X' c.1 c.2 * (polarUnit (contourAverage X c))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 := by
  unfold gaugedBlockFit
  rw [ChartFits.gaugedContourAverage_one]
  set m := contourAverage X c with hmdef
  by_cases h0 : m = 0
  · rw [h0]
    simp only [norm_zero, zero_mul, Quaternion.re_zero, sub_zero]
    positivity
  · set g := X' c.1 c.2 * (polarUnit m)⁻¹ with hg
    have hn : 0 < ‖m‖ := norm_pos_iff.2 h0
    have hu := coe_polarUnit h0
    have e1 : m = ‖m‖ • ((polarUnit m : UnitQuaternion) : ℍ[ℝ]) := by
      rw [hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have e2 : m * (((X' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = ‖m‖ • ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      have e3 : g⁻¹ = polarUnit m * (X' c.1 c.2)⁻¹ := by
        rw [hg]
        group
      rw [e3]
      conv_lhs => rw [e1]
      rw [smul_mul_assoc]
      rfl
    have e4 : (‖m‖ • ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = ‖m‖ * (g : ℍ[ℝ]).re := by
      rw [coe_unitQuaternion_inv]
      simp
    rw [e2, e4]
    have h3 := one_sub_re_le_norm_sub_one_sq g
    have h4 : 0 ≤ 1 - (g : ℍ[ℝ]).re := by
      have := quaternion_re_le_norm (g : ℍ[ℝ])
      rw [norm_coe_unitQuaternion] at this
      linarith
    nlinarith
theorem chartGauge_zeroChart (hodd : Odd F.blockSide) (R : F.FieldChain) (j : ℕ) :
    chartGauge R (zeroChart F) (j + 1) = fun _ => 1 := by
  funext y
  show balancingGauge (chartField R (zeroChart F) j) (R j) y = 1
  rw [ChartFits.chartField_zeroChart hodd]
  exact ChartFits.balancingGauge_self hodd _ y
variable {S : Finset F.Cell} {Y : F.Cell} {R : F.FieldChain} {C₀ s y : ℝ}
theorem mem_innerBonds_cellBall_of_bondWeight_ne_zero (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {j : ℕ} (hj : j ≤ F.top) {c : F.Site j × Fin 4}
    (hc : c ∈ innerBonds S j) (hn : bondWeight Y c ≠ 0) : c ∈ innerBonds (cellBall S Y 1) j := by
  classical
  have he := ChartCoordinates.innerBonds_ends hc
  have hz := enclosingCell_mem_cellBall_of_bondWeight_ne_zero hamb hodd hj hc hn
  have hY : enclosingCell c.1 = Y ∨ enclosingCell (c.1 + unitStep j c.2) = Y := by
    by_contra hcon
    push Not at hcon
    apply hn
    unfold bondWeight
    rw [if_neg hcon.1, if_neg hcon.2]
    simp
  have hYS : Y ∈ S := by
    rcases hY with h | h
    · exact h ▸ BlockLines.enclosingCell_mem hodd he.1
    · exact h ▸ BlockLines.enclosingCell_mem hodd he.2
  have hYb : Y ∈ cellBall S Y 1 := Finset.mem_filter.2 ⟨hYS, by rw [PatchLocality.cellSupDist_self]; omega⟩
  rcases hY with h | h
  · have hq : c ∈ bondsOver S {Y} j := Finset.mem_filter.2 ⟨hc, Finset.mem_singleton.2 h⟩
    exact BlockLines.mem_innerBonds_cellBall_of_mem_bondsOver hamb hodd S Y hj hq
  · exact ChartCoordinates.mem_innerBonds (BlockLines.mem_sitesOfCells_of_enclosingCell_mem hodd he.1 hz)
      (BlockLines.mem_sitesOfCells_of_enclosingCell_mem hodd he.2 (h ▸ hYb))
theorem sum_plaquetteWeight_zeroChart_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (ctx : ∀ z, CellSpans.CellHypotheses S z R C₀ s y) :
    ∑ p ∈ innerPlaquettes S 0, plaquetteWeight Y p * (1 - ((plaquetteHolonomy (R 0) p : UnitQuaternion) : ℍ[ℝ]).re) ≤
      81 * (1296 * (C₀ * s) ^ 2) := by
  classical
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
    positivity
  have e1 := sum_eq_sum_fiberwise_cell (innerPlaquettes S 0) (fun p => enclosingCell p.1) (cellBall S Y 1)
    (fun p => plaquetteWeight Y p * (1 - ((plaquetteHolonomy (R 0) p : UnitQuaternion) : ℍ[ℝ]).re))
    (fun p hp hn => enclosingCell_mem_cellBall_of_plaquetteWeight_ne_zero hamb hodd hp (fun h0 => hn (by simp [h0])))
  rw [e1]
  have hz : ∀ z ∈ cellBall S Y 1, ∑ p ∈ (innerPlaquettes S 0).filter (fun p => enclosingCell p.1 = z),
      plaquetteWeight Y p * (1 - ((plaquetteHolonomy (R 0) p : UnitQuaternion) : ℍ[ℝ]).re) ≤ 1296 * (C₀ * s) ^ 2 := by
    intro z _
    have e2 : (innerPlaquettes S 0).filter (fun p => enclosingCell p.1 = z) = plaquettesOver S {z} 0 := by
      ext p
      simp [plaquettesOver, Finset.mem_filter]
    rw [e2]
    have hq : ∀ q ∈ plaquettesOver S {z} 0, plaquetteWeight Y q * (1 - ((plaquetteHolonomy (R 0) q : UnitQuaternion) : ℍ[ℝ]).re) ≤
        (C₀ * s / ((F.blockSide : ℝ) ^ F.top) ^ 2) ^ 2 := by
      intro q hq
      have h1 := one_sub_re_le_norm_sub_one_sq (plaquetteHolonomy (R 0) q)
      have h2 := (ctx z).plaquette_le q hq
      rw [CellContexts.basePlaquetteHolonomy_eq_plaquetteHolonomy, CellContexts.norm_ofUnit_sub_one] at h2
      have h3 : 0 ≤ 1 - ((plaquetteHolonomy (R 0) q : UnitQuaternion) : ℍ[ℝ]).re := by
        have := quaternion_re_le_norm ((plaquetteHolonomy (R 0) q : UnitQuaternion) : ℍ[ℝ])
        rw [norm_coe_unitQuaternion] at this
        linarith
      have h4 : plaquetteWeight Y q * (1 - ((plaquetteHolonomy (R 0) q : UnitQuaternion) : ℍ[ℝ]).re) ≤
          1 - ((plaquetteHolonomy (R 0) q : UnitQuaternion) : ℍ[ℝ]).re :=
        mul_le_of_le_one_left h3 (plaquetteWeight_le_one Y q)
      have h5 : ‖((plaquetteHolonomy (R 0) q : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 ≤
          (C₀ * s / ((F.blockSide : ℝ) ^ F.top) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
      linarith
    refine (Finset.sum_le_card_nsmul _ _ _ hq).trans ?_
    rw [nsmul_eq_mul]
    have hc := CellNormBounds.card_plaquettesOver_singleton_le hamb hodd S z
    have hv : (C₀ * s / ((F.blockSide : ℝ) ^ F.top) ^ 2) ^ 2 * ((F.blockSide : ℝ) ^ F.top) ^ 4 = (C₀ * s) ^ 2 := by
      field_simp
    have h0 : 0 ≤ (C₀ * s / ((F.blockSide : ℝ) ^ F.top) ^ 2) ^ 2 := sq_nonneg _
    calc _ ≤ (1296 * ((F.blockSide : ℝ) ^ F.top) ^ 4) * (C₀ * s / ((F.blockSide : ℝ) ^ F.top) ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_right hc h0
      _ = 1296 * ((C₀ * s / ((F.blockSide : ℝ) ^ F.top) ^ 2) ^ 2 * ((F.blockSide : ℝ) ^ F.top) ^ 4) := by ring
      _ = _ := by rw [hv]
  refine (Finset.sum_le_card_nsmul _ _ _ hz).trans ?_
  rw [nsmul_eq_mul]
  have hc : ((cellBall S Y 1).card : ℝ) ≤ 81 := by exact_mod_cast BlockLines.card_cellBall_one_le S Y
  exact mul_le_mul_of_nonneg_right hc (by positivity)
theorem sum_bondWeight_zeroChart_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (hy : 0 ≤ y)
    (ctx : ∀ z, CellSpans.CellHypotheses S z R C₀ s y)
    (hm : ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds S (j + 1), ‖contourAverage (R j) c‖ ≤ 1) :
    ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ innerBonds S (j + 1),
      bondWeight Y c * gaugedBlockFit (R j) (fun _ => 1) (R (j + 1)) c ≤ y ^ 2 := by
  classical
  have h1 := (ctx Y).defect_le
  have h2 : LevelRecursion.finsetLpNorm 2 (ComplexCells.lowerBonds (cellBall S Y 1))
      (fun x => ‖ofUnit (referenceDefect R x.1 x.2) - 1‖) ^ 2 ≤ y ^ 2 :=
    pow_le_pow_left₀ (LevelRecursion.finsetLpNorm_nonneg _ _ _) h1 2
  rw [← ComplexCells.sum_sq_eq_finsetLpNorm_two_sq, ComplexCells.lowerBonds, Finset.sum_sigma] at h2
  refine le_trans (Finset.sum_le_sum fun j hj => ?_) h2
  have hj' : j + 1 < F.top := by
    have := Finset.mem_range.1 hj
    simp only [BlockFrame.top] at this ⊢
    omega
  have e0 : ∀ c ∈ (innerBonds S (j + 1)).filter (fun c => bondWeight Y c ≠ 0),
      bondWeight Y c * gaugedBlockFit (R j) (fun _ => 1) (R (j + 1)) c ≤ ‖ofUnit (referenceDefect R j c) - 1‖ ^ 2 := by
    intro c hc
    have hcS := (Finset.mem_filter.1 hc).1
    have h3 := gaugedBlockFit_one_le (R j) (R (j + 1)) c (hm j hj' c hcS)
    have h4 : 0 ≤ gaugedBlockFit (R j) (fun _ => 1) (R (j + 1)) c := PatchLocality.gaugedBlockFit_nonneg _ _ _ _
    have h5 := mul_le_of_le_one_left h4 (bondWeight_le_one Y c)
    rw [CellContexts.norm_ofUnit_sub_one]
    exact h5.trans h3
  rw [← Finset.sum_filter_of_ne (p := fun c => bondWeight Y c ≠ 0) (fun c _ hn h0 => hn (by rw [h0, zero_mul]))]
  refine (Finset.sum_le_sum e0).trans (Finset.sum_le_sum_of_subset_of_nonneg (fun c hc => ?_)
    fun _ _ _ => by positivity)
  obtain ⟨hcS, hn⟩ := Finset.mem_filter.1 hc
  exact mem_innerBonds_cellBall_of_bondWeight_ne_zero hamb hodd hj'.le hcS hn
theorem lowerEvaluation_zeroChart_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {a : ℝ} (ha : 0 ≤ a)
    (hy : 0 ≤ y) (ctx : ∀ z, CellSpans.CellHypotheses S z R C₀ s y)
    (hm : ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds S (j + 1), ‖contourAverage (R j) c‖ ≤ 1) :
    lowerEvaluation a S R Y (zeroChart F) ≤ 81 * (1296 * (C₀ * s) ^ 2) + a * y ^ 2 := by
  unfold lowerEvaluation
  simp only [ChartFits.chartField_zeroChart hodd, chartGauge_zeroChart hodd]
  exact add_le_add (sum_plaquetteWeight_zeroChart_le hamb hodd ctx)
    (mul_le_mul_of_nonneg_left (sum_bondWeight_zeroChart_le hamb hodd hy ctx hm) ha)
theorem lowerEvaluation_nonneg {a : ℝ} (ha : 0 ≤ a) (U : ChainChart F) : 0 ≤ lowerEvaluation a S R Y U := by
  unfold lowerEvaluation
  refine add_nonneg (Finset.sum_nonneg fun p _ => mul_nonneg (plaquetteWeight_nonneg Y p) ?_) (mul_nonneg ha ?_)
  · have := quaternion_re_le_norm ((plaquetteHolonomy (chartField R U 0) p : UnitQuaternion) : ℍ[ℝ])
    rw [norm_coe_unitQuaternion] at this
    linarith
  · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ =>
      mul_nonneg (bondWeight_nonneg Y c) (PatchLocality.gaugedBlockFit_nonneg _ _ _ _)
end YangMills.Construction.ReferenceShare
end
