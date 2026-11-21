import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfSmallMultiples
import YangMills.Construction.ColdChainAtEveryLevel.SecondDifferenceAtACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.SecondDifferences
open BlockAverages SmallMultiples LowerLevelTerms TopLevelTerms CellSums HullBounds ComplexLevels
  LevelRecursion BlockLines RealChartTerms PlaquetteTerms BondSecondDifference ComplexDifferences
variable {F : BlockFrame}
theorem chartAction_eq_sum (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (W : ChainChart F)
    (V : F.GaugeField F.top) :
    chartAction a S R W V = ∑ q ∈ innerPlaquettes S 0, plaquetteAction R W q +
      a * (∑ j ∈ Finset.range F.depth, ∑ b ∈ innerBonds S (j + 1), bondEnergy R W V j b +
        ∑ b ∈ innerBonds S (F.depth + 1), bondEnergy R W V F.depth b) := by
  have h0 : chartChain R W V 0 = chartField R W 0 := chartChain_of_ne_top R W V (by
    have : F.top = F.depth + 1 := rfl
    omega)
  simp only [chartAction, gaugedChainAction, wilsonAction, h0]
  rw [show F.top = F.depth + 1 from rfl, Finset.sum_range_succ]
  rfl
theorem sum_innerPlaquettes_eq_sum_cells (hodd : Odd F.blockSide) (S : Finset F.Cell)
    (f : F.Site 0 × Fin 4 × Fin 4 → ℝ) :
    ∑ q ∈ innerPlaquettes S 0, f q = ∑ z ∈ S, ∑ q ∈ plaquettesOver S {z} 0, f q := by
  classical
  have h : ∀ q ∈ innerPlaquettes S 0, enclosingCell q.1 ∈ S := fun q hq =>
    enclosingCell_mem hodd (Finset.mem_product.1 (Finset.mem_filter.1 hq).1).1
  rw [← Finset.sum_fiberwise_of_maps_to h]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr ?_ fun _ _ => rfl
  ext q
  simp [plaquettesOver]
theorem sum_innerBonds_eq_sum_cells (hodd : Odd F.blockSide) (S : Finset F.Cell) (j : ℕ)
    (f : F.Site j × Fin 4 → ℝ) :
    ∑ b ∈ innerBonds S j, f b = ∑ z ∈ S, ∑ b ∈ bondsOver S {z} j, f b := by
  classical
  have h : ∀ b ∈ innerBonds S j, enclosingCell b.1 ∈ S := fun b hb =>
    enclosingCell_mem hodd (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1
  rw [← Finset.sum_fiberwise_of_maps_to h]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr ?_ fun _ _ => rfl
  ext b
  simp [bondsOver]
theorem abs_chartAction_second_diff_sub_inner_le (hodd : Odd F.blockSide) {a : ℝ} (ha : 0 ≤ a)
    (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top) (W₁ W₂ W₃ : ChainChart F) :
    |chartAction a S R W₃ V - chartAction a S R W₁ V - chartAction a S R W₂ V +
        chartAction a S R (zeroChart F) V -
      (∑ q ∈ innerPlaquettes S 0, inner ℝ (linearizedCurl (R 0) W₁.fine q) (linearizedCurl (R 0) W₂.fine q) +
        a * ∑ j ∈ Finset.range F.depth, ∑ b ∈ innerBonds S (j + 1),
          inner ℝ (W₁.coarse j b.1 b.2 : ℍ[ℝ]) (W₂.coarse j b.1 b.2 : ℍ[ℝ]) +
        a * ∑ b ∈ innerBonds S (F.depth + 1),
          inner ℝ (linearPart R W₁ (F.depth + 1) b.1 b.2) (linearPart R W₂ (F.depth + 1) b.1 b.2))| ≤
      ∑ z ∈ S, cellSecondDiffError a S R V W₁ W₂ W₃ z := by
  set X : F.Site 0 × Fin 4 × Fin 4 → ℝ := fun q => plaquetteAction R W₃ q - plaquetteAction R W₁ q -
    plaquetteAction R W₂ q + plaquetteAction R (zeroChart F) q -
    inner ℝ (linearizedCurl (R 0) W₁.fine q) (linearizedCurl (R 0) W₂.fine q) with hX
  set Y : (j : ℕ) → F.Site (j + 1) × Fin 4 → ℝ := fun j b => bondEnergy R W₃ V j b - bondEnergy R W₁ V j b -
    bondEnergy R W₂ V j b + bondEnergy R (zeroChart F) V j b -
    inner ℝ (W₁.coarse j b.1 b.2 : ℍ[ℝ]) (W₂.coarse j b.1 b.2 : ℍ[ℝ]) with hY
  set Z : F.Site (F.depth + 1) × Fin 4 → ℝ := fun b => bondEnergy R W₃ V F.depth b -
    bondEnergy R W₁ V F.depth b - bondEnergy R W₂ V F.depth b + bondEnergy R (zeroChart F) V F.depth b -
    inner ℝ (linearPart R W₁ (F.depth + 1) b.1 b.2) (linearPart R W₂ (F.depth + 1) b.1 b.2) with hZ
  have hsplit : chartAction a S R W₃ V - chartAction a S R W₁ V - chartAction a S R W₂ V +
        chartAction a S R (zeroChart F) V -
      (∑ q ∈ innerPlaquettes S 0, inner ℝ (linearizedCurl (R 0) W₁.fine q) (linearizedCurl (R 0) W₂.fine q) +
        a * ∑ j ∈ Finset.range F.depth, ∑ b ∈ innerBonds S (j + 1),
          inner ℝ (W₁.coarse j b.1 b.2 : ℍ[ℝ]) (W₂.coarse j b.1 b.2 : ℍ[ℝ]) +
        a * ∑ b ∈ innerBonds S (F.depth + 1),
          inner ℝ (linearPart R W₁ (F.depth + 1) b.1 b.2) (linearPart R W₂ (F.depth + 1) b.1 b.2)) =
      ∑ q ∈ innerPlaquettes S 0, X q + a * ∑ j ∈ Finset.range F.depth, ∑ b ∈ innerBonds S (j + 1), Y j b +
        a * ∑ b ∈ innerBonds S (F.depth + 1), Z b := by
    simp only [chartAction_eq_sum, hX, hY, hZ, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  have bX : |∑ q ∈ innerPlaquettes S 0, X q| ≤ ∑ z ∈ S, ∑ q ∈ plaquettesOver S {z} 0, |X q| := by
    rw [← sum_innerPlaquettes_eq_sum_cells hodd]
    exact Finset.abs_sum_le_sum_abs _ _
  have bY : |∑ j ∈ Finset.range F.depth, ∑ b ∈ innerBonds S (j + 1), Y j b| ≤
      ∑ z ∈ S, ∑ j ∈ Finset.range F.depth, ∑ b ∈ bondsOver S {z} (j + 1), |Y j b| := by
    rw [Finset.sum_comm]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← sum_innerBonds_eq_sum_cells hodd]
    exact Finset.abs_sum_le_sum_abs _ _
  have bZ : |∑ b ∈ innerBonds S (F.depth + 1), Z b| ≤ ∑ z ∈ S, ∑ b ∈ bondsOver S {z} (F.depth + 1), |Z b| := by
    rw [← sum_innerBonds_eq_sum_cells hodd]
    exact Finset.abs_sum_le_sum_abs _ _
  have hcells : ∑ z ∈ S, cellSecondDiffError a S R V W₁ W₂ W₃ z = ∑ z ∈ S, ∑ q ∈ plaquettesOver S {z} 0, |X q| +
      a * ∑ z ∈ S, ∑ j ∈ Finset.range F.depth, ∑ b ∈ bondsOver S {z} (j + 1), |Y j b| +
      a * ∑ z ∈ S, ∑ b ∈ bondsOver S {z} (F.depth + 1), |Z b| := by
    simp only [cellSecondDiffError, Finset.sum_add_distrib, ← Finset.mul_sum]
    rfl
  rw [hcells]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add bX ?_)) ?_)
  · rw [abs_mul, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left bY ha
  · rw [abs_mul, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left bZ ha
def topErrorCold (L : ℕ) : ℝ :=
  hullFactor L * (284 * (5 * (4 + 200000 * (L : ℝ) ^ 2) * (hullFactor L * 82272))) +
    200000 * (L : ℝ) ^ 2 * (5 * (hullFactor L * 82272))
def topErrorChart (L : ℕ) (Ln : ℝ) : ℝ :=
  hullFactor L * (142 * (5 * Ln) + 284 * (3 + 5 * (200000 * (L : ℝ) ^ 2) * Ln * (hullFactor L * 82272))) +
    200000 * (L : ℝ) ^ 2 * (5 * (hullFactor L * 82272))
theorem linearPartError_eq (L : ℕ) (Ln c₀ T B : ℝ) :
    linearPartError L Ln c₀ T B = B * (c₀ * topErrorCold L + T * topErrorChart L Ln) := by
  simp only [linearPartError, topErrorCold, topErrorChart]
  ring
def cellSecondDiffConst (L : ℕ) (a : ℝ) : ℝ :=
  (200000 * 9216 + a * (2 * lowerMainConst L + topMainConst L)) +
    a * (20 * (hullFactor L * 82272) + 2 * topLinearConst L) * topErrorCold L
theorem smallnessThreshold_pos (hodd : Odd F.blockSide) : 0 < smallnessThreshold F.blockSide := by
  have hL0 : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hF0 := hullFactor_nonneg (F := F) hodd
  have hH0 := hullBondCount_nonneg F.blockSide
  unfold smallnessThreshold
  positivity
set_option maxHeartbeats 2000000 in
theorem cellSecondDiffError_scaled_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) {a : ℝ} (ha : 0 ≤ a) {S : Finset F.Cell}
    {z : F.Cell} {p : F.Site 0} {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {V : F.GaugeField F.top}
    (hV : R F.top = V) {U A : ChainChart F} {C₀ s Bu Ba c : ℝ} (hC : 0 < C₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (hx : C₀ * s ≤ smallnessThreshold F.blockSide) (ref : ReferenceNear (cellBall S z 1) R C₀ s)
    (hcurv : ∀ q ∈ innerPlaquettes (cellBall S z 1) 0,
      plaquetteDefect (R 0) q ≤ C₀ * s * ((1 / (F.blockSide : ℝ)) ^ F.top) ^ 2)
    (hc : 0 < c)
    (hcb : ∀ (W : ChainChart F) (B : ℝ), 0 ≤ B → B ≤ c →
      finsetLpNorm 4 (innerBonds (cellBall S z 1) 0) (fun b => ‖(W.fine b.1 b.2 : ℍ[ℝ])‖) ≤ B →
      (∀ j, j + 1 < F.top →
        finsetLpNorm 2 (innerBonds (cellBall S z 1) (j + 1)) (fun b => ‖(W.coarse j b.1 b.2 : ℍ[ℝ])‖) ≤ B) →
      DeviationBall R (cellBall S z 1) (realChart W) (4 * B) (4 * B))
    (nm : PairWeightedNorms (cellBall S z 1) p θ U A Bu Ba) (hBu : 0 ≤ Bu) (hBa : 0 ≤ Ba) :
    ∃ Y ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      cellSecondDiffError a S R V (scaledChart U ε) (scaledChart A ε) (scaledSumChart U A ε) z ≤
        ε ^ 2 * (C₀ * s * cellSecondDiffConst F.blockSide a * (Bu * Ba)) + ε ^ 3 * Y := by
  have hD := card_cellBall_one_le S z
  set D := cellBall S z 1 with hDd
  set Q := pairSize D U A with hQ
  have hQ0 : 0 ≤ Q := pairSize_nonneg D U A
  have hH0 := hullBondCount_nonneg F.blockSide
  have hF0 := hullFactor_nonneg (F := F) hodd
  set Sm := ∑ b ∈ innerBonds D (F.depth + 1), (topLinearSize R U b.1 b.2 + topLinearSize R A b.1 b.2) with hSm
  have hSm0 : 0 ≤ Sm := Finset.sum_nonneg fun b _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
  set M := Q + 8 * (hullBondCount F.blockSide * Q) + Bu + Ba + Sm with hM
  have hM0 : 0 ≤ M := by positivity
  set κ := smallnessThreshold F.blockSide with hκ
  have hκ0 : 0 < κ := smallnessThreshold_pos hodd
  set e := min (min κ (1 / 16000)) c with he
  have he0 : 0 < e := lt_min (lt_min hκ0 (by norm_num)) hc
  set Z := 1 + hullBondCount F.blockSide + hullFactor F.blockSide with hZ
  set Dn := 1 + M + 4 * Q * Z + Q with hDn
  have hDn0 : 0 < Dn := by positivity
  refine ⟨M * (a * (20 * (hullFactor F.blockSide * 82272) + 2 * topLinearConst F.blockSide) *
      topErrorChart F.blockSide ((F.blockSide : ℝ) ^ F.top) * (Bu * Ba)) +
    cellCubicWeight a S z * M ^ 3, e / Dn, by positivity, fun ε hε hεl => ?_⟩
  have hεD : ε * Dn < e := by
    rwa [lt_div_iff₀ hDn0] at hεl
  have hε0 : 0 ≤ ε := hε.le
  have le1 : ∀ X : ℝ, X ≤ Dn → ε * X ≤ e := fun X hX => (mul_le_mul_of_nonneg_left hX hε0).trans hεD.le
  have eκ : e ≤ κ := (min_le_left _ _).trans (min_le_left _ _)
  have e16 : e ≤ 1 / 16000 := (min_le_left _ _).trans (min_le_right _ _)
  have ec : e ≤ c := min_le_right _ _
  have hMD : M ≤ Dn := by
    have : 0 ≤ 4 * Q * Z := by positivity
    linarith
  have hQD : Q ≤ Dn := by
    have : 0 ≤ 4 * Q * Z := by positivity
    linarith
  have hZD : 4 * Q * Z ≤ Dn := by linarith
  have c1 : ε * M ≤ κ := (le1 M hMD).trans eκ
  have c2 : 4 * (ε * M) ≤ 1 / 4000 := by
    have := (le1 M hMD).trans e16
    linarith
  have c3 : (4 * (ε * Q)) * Z ≤ κ := by
    have := (le1 (4 * Q * Z) hZD).trans eκ
    calc (4 * (ε * Q)) * Z = ε * (4 * Q * Z) := by ring
      _ ≤ κ := this
  have c4 : ε * Q ≤ c := (le1 Q hQD).trans ec
  obtain ⟨dir, top⟩ := smallDirectionTriple_scaledChart hodd h2 hD hθ hC hs hs1 hx ref hcb nm hBu hBa hε le_rfl
    c1 c2 c3 c4
  have d₁ := dominatedBy_scaledChart_left U A hε0
  have d₂ := dominatedBy_scaledChart_right U A hε0
  have hQM : Q ≤ M := by
    have : 0 ≤ 8 * (hullBondCount F.blockSide * Q) := by positivity
    linarith
  have hQT : ε * Q ≤ ε * M := mul_le_mul_of_nonneg_left hQM hε0
  have key := cellSecondDiffError_le hamb hodd h2 ha hθ hV ref dir top hcurv c2
    (fun b hb => (d₁.norm_fine_le hε0 hb).trans hQT) (fun b hb => (d₂.norm_fine_le hε0 hb).trans hQT)
    (fun b _ => scaledSumChart_fine U A ε b.1 b.2)
    (weightedScaleNorm_le_of_abs_le hodd p θ (by norm_num) 0 hε0 (fun b _ => by
      rw [abs_of_nonneg (norm_nonneg _), scaledChart_fine, norm_coe_smul_imaginary ε hε0])
      (fun _ _ => norm_nonneg _) nm.fine_le)
    (weightedScaleNorm_le_of_abs_le hodd p (-θ) (by norm_num) 0 hε0 (fun b _ => by
      rw [abs_of_nonneg (norm_nonneg _), scaledChart_fine, norm_coe_smul_imaginary ε hε0])
      (fun _ _ => norm_nonneg _) nm.fine_inv_le)
  refine key.trans (le_of_eq ?_)
  rw [linearPartError_eq, linearPartError_eq]
  simp only [cellSecondDiffConst]
  ring
end YangMills.Construction.SecondDifferences
end
