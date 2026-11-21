import YangMills.Construction.ColdChainAtEveryLevel.AveragesAndLocalSizesOfALevelProof
import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfTheReferenceForm
import YangMills.Construction.ColdChainAtEveryLevel.LinesOfTheBlocksOfABond
import YangMills.Construction.ColdChainAtEveryLevel.LocalFormOfTheLines
import YangMills.Construction.ColdChainAtEveryLevel.TransportsInTheUnitsOfAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ReferenceBounds
open YangMills.Construction.BlockAverages YangMills.Construction.LatticePaths YangMills.Construction.LatticeFractionalIntegration YangMills.Construction.FiniteDifferences
section Averages
def quaternionReHom : ℍ[ℝ] →+ ℝ := AddMonoidHom.mk' (fun q => q.re) (fun a b => by simp)
theorem re_coe_unitQuaternion_eq (g : UnitQuaternion) :
    (g : ℍ[ℝ]).re = 1 - ‖(g : ℍ[ℝ]) - 1‖ ^ 2 / 2 := by
  have h1 : star ((g : ℍ[ℝ]) - 1) * ((g : ℍ[ℝ]) - 1) = ((Quaternion.normSq ((g : ℍ[ℝ]) - 1) : ℝ) : ℍ[ℝ]) :=
    Quaternion.star_mul_self _
  have h2 : star (g : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := by
    rw [← coe_unitQuaternion_inv]
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    rfl
  have h3 : star ((g : ℍ[ℝ]) - 1) * ((g : ℍ[ℝ]) - 1) = ((2 : ℝ) : ℍ[ℝ]) - ((g : ℍ[ℝ]) + star (g : ℍ[ℝ])) := by
    simp only [star_sub, star_one, sub_mul, mul_sub, one_mul, mul_one, h2]
    have : ((2 : ℝ) : ℍ[ℝ]) = 1 + 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Quaternion.coe_add]
      simp
    rw [this]
    abel
  have h4 := congrArg (fun q : ℍ[ℝ] => q.re) (h1.symm.trans h3)
  simp only [Quaternion.normSq_eq_norm_mul_self] at h4
  have h5 : ((‖(g : ℍ[ℝ]) - 1‖ * ‖(g : ℍ[ℝ]) - 1‖ : ℝ) : ℍ[ℝ]).re = ‖(g : ℍ[ℝ]) - 1‖ * ‖(g : ℍ[ℝ]) - 1‖ := rfl
  rw [h5] at h4
  have h6 : (((2 : ℝ) : ℍ[ℝ]) - ((g : ℍ[ℝ]) + star (g : ℍ[ℝ]))).re = 2 - 2 * (g : ℍ[ℝ]).re := by
    simp
    ring
  rw [h6] at h4
  rw [sq]
  linarith
variable {L : ℕ}
def averagingWeight (L : ℕ) : ℝ := 1 / (24 * (L : ℝ) ^ 4)
theorem card_perm_fin_four : (Finset.univ : Finset (Equiv.Perm (Fin 4))).card = 24 := by
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rfl
theorem averagingWeight_mul_sum_const (hodd : Odd L) {c : ℝ} :
    averagingWeight L * ∑ _h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), c = c := by
  have hL : (0 : ℝ) < L := by exact_mod_cast hodd.pos
  simp only [Finset.sum_const, card_perm_fin_four, card_centredCube hodd, averagingWeight, nsmul_eq_mul]
  push_cast
  field_simp
variable (hodd : Odd L) {Dd : Lattice4 → Equiv.Perm (Fin 4) → UnitQuaternion}
def weightedContourAverage (L : ℕ) (Dd : Lattice4 → Equiv.Perm (Fin 4) → UnitQuaternion) : ℍ[ℝ] :=
  averagingWeight L • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), ((Dd h π : UnitQuaternion) : ℍ[ℝ])
include hodd in
theorem norm_weightedContourAverage_sub_one_le {e : ℝ}
    (he : ∀ h ∈ centredCube L, ∀ π, ‖((Dd h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ e) :
    ‖weightedContourAverage L Dd - 1‖ ≤ e := by
  have hw : 0 ≤ averagingWeight L := by
    unfold averagingWeight
    positivity
  have e1 : weightedContourAverage L Dd - 1 =
      averagingWeight L • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
        (((Dd h π : UnitQuaternion) : ℍ[ℝ]) - 1) := by
    have hL : (0 : ℝ) < L := by exact_mod_cast hodd.pos
    have hs : (∑ _h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), (1 : ℍ[ℝ])) =
        ((24 * (L : ℝ) ^ 4 : ℝ) : ℍ[ℝ]) := by
      simp only [Finset.sum_const, card_perm_fin_four, card_centredCube hodd, nsmul_eq_mul, mul_one]
      rw [← Nat.cast_mul]
      have e : (24 * (L : ℝ) ^ 4) = ((L ^ 4 * 24 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [e]
      exact (map_natCast (algebraMap ℝ ℍ[ℝ]) _).symm
    simp only [weightedContourAverage, Finset.sum_sub_distrib, smul_sub, hs]
    congr 1
    rw [← Quaternion.coe_mul_eq_smul, ← Quaternion.coe_mul]
    have : averagingWeight L * (24 * (L : ℝ) ^ 4) = 1 := by
      unfold averagingWeight
      field_simp
    rw [this]
    simp
  rw [e1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
  have h2 : ‖∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), (((Dd h π : UnitQuaternion) : ℍ[ℝ]) - 1)‖ ≤
      ∑ _h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), e :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => he h hh π))
  calc _ ≤ averagingWeight L * ∑ _h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), e :=
        mul_le_mul_of_nonneg_left h2 hw
    _ = e := averagingWeight_mul_sum_const hodd
include hodd in
theorem re_weightedContourAverage_ge {e : ℝ} (he0 : 0 ≤ e)
    (he : ∀ h ∈ centredCube L, ∀ π, ‖((Dd h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ e) :
    1 - e ^ 2 / 2 ≤ (weightedContourAverage L Dd).re := by
  have hw : 0 ≤ averagingWeight L := by
    unfold averagingWeight
    positivity
  have e1 : (weightedContourAverage L Dd).re =
      averagingWeight L * ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), ((Dd h π : UnitQuaternion) : ℍ[ℝ]).re := by
    have h1 : (∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), ((Dd h π : UnitQuaternion) : ℍ[ℝ])).re =
        ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), ((Dd h π : UnitQuaternion) : ℍ[ℝ]).re := by
      have a := map_sum quaternionReHom
        (fun h => ∑ π : Equiv.Perm (Fin 4), ((Dd h π : UnitQuaternion) : ℍ[ℝ])) (centredCube L)
      have b : ∀ h, quaternionReHom (∑ π : Equiv.Perm (Fin 4), ((Dd h π : UnitQuaternion) : ℍ[ℝ])) =
          ∑ π : Equiv.Perm (Fin 4), quaternionReHom ((Dd h π : UnitQuaternion) : ℍ[ℝ]) :=
        fun h => map_sum quaternionReHom _ _
      simp only [b] at a
      exact a
    simp only [weightedContourAverage, Quaternion.re_smul, smul_eq_mul, h1]
  rw [e1]
  have h2 : ∑ _h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), (1 - e ^ 2 / 2) ≤
      ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), ((Dd h π : UnitQuaternion) : ℍ[ℝ]).re := by
    refine Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun π _ => ?_
    rw [re_coe_unitQuaternion_eq]
    have := pow_le_pow_left₀ (norm_nonneg _) (he h hh π) 2
    linarith
  calc 1 - e ^ 2 / 2 = averagingWeight L * ∑ _h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), (1 - e ^ 2 / 2) :=
        (averagingWeight_mul_sum_const hodd).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hw
include hodd in
theorem norm_weightedContourAverage_le_one : ‖weightedContourAverage L Dd‖ ≤ 1 := by
  have hw : 0 ≤ averagingWeight L := by
    unfold averagingWeight
    positivity
  unfold weightedContourAverage
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
  have h2 : ‖∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4), ((Dd h π : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ∑ _h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => (norm_coe_unitQuaternion _).le))
  calc _ ≤ averagingWeight L * ∑ _h ∈ centredCube L, ∑ _π : Equiv.Perm (Fin 4), (1 : ℝ) :=
        mul_le_mul_of_nonneg_left h2 hw
    _ = 1 := averagingWeight_mul_sum_const hodd
theorem pureComponent_weightedContourAverage : pureComponent (weightedContourAverage L Dd) =
    averagingWeight L • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
      pureComponent ((Dd h π : UnitQuaternion) : ℍ[ℝ]) := by
  unfold weightedContourAverage
  rw [pureComponent_smul, pureComponent_sum]
  simp only [pureComponent_sum]
theorem norm_polarUnit_sub_one_le_of_half_le_re {q : ℍ[ℝ]} (h : 1 / 2 ≤ q.re) :
    ‖((polarUnit q : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 4 * ‖pureComponent q‖ := by
  have hq : 1 / 2 ≤ ‖q‖ := h.trans (quaternion_re_le_norm q)
  have h0 : q ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  refine (norm_polarUnit_sub_one_le (by linarith) h0).trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (pureComponent q)]
end Averages
section Factoring
theorem polarUnit_coe_unitQuaternion (g : UnitQuaternion) : polarUnit (g : ℍ[ℝ]) = g := by apply _root_.YangMills.Construction.BlockLines.polarUnit_coe <;> assumption
variable {F : BlockFrame}
theorem contourAverage_polarUnit_factor {j : ℕ} {X : F.GaugeField j} (c' : F.Site (j + 1) × Fin 4)
    (hodd : Odd F.blockSide) {g0 g1 Q : UnitQuaternion}
    {Dd : Lattice4 → Equiv.Perm (Fin 4) → UnitQuaternion} {e e' : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 2)
    (he : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖((Dd h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ e)
    (hpure : ‖averagingWeight F.blockSide • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      pureComponent ((Dd h π : UnitQuaternion) : ℍ[ℝ])‖ ≤ e')
    (hol : ∀ h ∈ centredCube F.blockSide, ∀ π,
      pathHolonomy X (refineSite c'.1) (bondContour F.blockSide h π c'.2) = g0 * Dd h π * Q * g1⁻¹) :
    ∃ w : UnitQuaternion, polarUnit (contourAverage X c') = g0 * w * Q * g1⁻¹ ∧
      ‖(w : ℍ[ℝ]) - 1‖ ≤ 4 * e' ∧
      0 ≤ 1 - ‖contourAverage X c'‖ ∧ 1 - ‖contourAverage X c'‖ ≤ e ^ 2 / 2 := by
  set M := weightedContourAverage F.blockSide Dd with hM
  have hre := re_weightedContourAverage_ge hodd he0 he
  have hre2 : 1 / 2 ≤ M.re := by nlinarith
  have hM0 : M ≠ 0 := by
    intro h0
    rw [h0] at hre2
    norm_num at hre2
  have e1 : contourAverage X c' =
      (g0 : ℍ[ℝ]) * M * (Q : ℍ[ℝ]) * ((g1⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    have h1 : ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy X (refineSite c'.1) (bondContour F.blockSide h π c'.2) : UnitQuaternion) : ℍ[ℝ]) =
        ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
          (g0 : ℍ[ℝ]) * ((Dd h π : UnitQuaternion) : ℍ[ℝ]) * (Q : ℍ[ℝ]) * ((g1⁻¹ : UnitQuaternion) : ℍ[ℝ]) :=
      Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => by
        rw [hol h hh π]
        simp only [Submonoid.coe_mul]
    unfold contourAverage
    rw [h1]
    simp only [hM, weightedContourAverage, averagingWeight, mul_smul_comm, smul_mul_assoc, Finset.mul_sum,
      Finset.sum_mul]
  have hg0 := coe_unitQuaternion_ne_zero g0
  have hQ := coe_unitQuaternion_ne_zero Q
  have hg1 := coe_unitQuaternion_ne_zero g1⁻¹
  refine ⟨polarUnit M, ?_, ?_, ?_⟩
  · rw [e1, polarUnit_mul (mul_ne_zero (mul_ne_zero hg0 hM0) hQ) hg1, polarUnit_mul (mul_ne_zero hg0 hM0) hQ,
      polarUnit_mul hg0 hM0, polarUnit_coe_unitQuaternion, polarUnit_coe_unitQuaternion,
      polarUnit_coe_unitQuaternion]
  · refine (norm_polarUnit_sub_one_le_of_half_le_re hre2).trans ?_
    rw [hM, pureComponent_weightedContourAverage]
    linarith
  · have hn : ‖contourAverage X c'‖ = ‖M‖ := by
      rw [e1, norm_mul, norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion,
        norm_coe_unitQuaternion]
      ring
    rw [hn]
    have h1 := norm_weightedContourAverage_le_one (Dd := Dd) hodd
    have h2 := quaternion_re_le_norm M
    constructor <;> linarith
end Factoring
section Charts
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
def chartSite (S : Finset F.Cell) (z : F.Cell) (j : ℕ) (x0 a : Lattice4) : Lattice4 :=
  fun i => (F.blockSide : ℤ) ^ j * (closedOrthant S z i * a i) + x0 i
theorem patchSite_chartSite (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (j : ℕ)
    (x0 a : Lattice4) :
    GaugeMap.patchSite S z (chartSite S z j x0 a) =
      GaugeMap.patchSite S z x0 + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ j * a i) := by
  unfold GaugeMap.patchSite
  rw [add_assoc, ← siteOfCoords_add]
  congr 2
  funext i
  simp only [chartSite, Pi.add_apply]
  have h := closedOrthant_mul_self he i
  linear_combination ((F.blockSide : ℤ) ^ j * a i) * h
theorem baseSite_chartSite (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {j : ℕ}
    (hj : j ≤ F.top) {w0 : F.Site j} {x0 : Lattice4}
    (hw : baseSite w0 = GaugeMap.patchSite S z x0) (a : Lattice4) :
    baseSite (w0 + siteOfCoords j a) = GaugeMap.patchSite S z (chartSite S z j x0 a) := by
  rw [baseSite_add j hj, hw, patchSite_chartSite he]
theorem siteOfCoords_stepDisplacement (j : ℕ) (st : PathStep) :
    siteOfCoords (F := F) j (FlatPairing.stepDisplacement st) = BlockAverages.stepDisplacement j st := by
  rcases st with ⟨i, b⟩
  cases b
  · simp [FlatPairing.stepDisplacement, BlockAverages.stepDisplacement, siteOfCoords_neg, unitStep_eq]
  · simp [FlatPairing.stepDisplacement, BlockAverages.stepDisplacement, unitStep_eq]
def chartScaleHom (S : Finset F.Cell) (z : F.Cell) (j : ℕ) : Lattice4 →+ Lattice4 :=
  AddMonoidHom.mk' (fun a i => (F.blockSide : ℤ) ^ j * (closedOrthant S z i * a i)) (fun a b => by
    funext i
    simp only [Pi.add_apply]
    ring)
theorem inv_cellSideLength_mul_pow (hL : 0 < F.blockSide) {j : ℕ} (hj : j ≤ F.top) :
    1 / (GaugeMap.cellSideLength F : ℝ) * (F.blockSide : ℝ) ^ j = levelScale F j := by
  have hc : (GaugeMap.cellSideLength F : ℝ) = (F.blockSide : ℝ) ^ F.top := by simp [GaugeMap.cellSideLength]
  have e : F.top = (F.top - j) + j := by omega
  unfold levelScale
  rw [hc]
  nth_rewrite 1 [e]
  rw [pow_add, one_div_pow]
  field_simp
theorem zero_le_levelScale (j : ℕ) : 0 ≤ levelScale F j := by
  unfold levelScale
  positivity
theorem supNorm_chartScaleHom_le (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (j : ℕ)
    (a : Lattice4) :
    (supNorm (chartScaleHom S z j a) : ℝ) ≤ (F.blockSide : ℝ) ^ j * supNorm a := by
  have : supNorm (chartScaleHom S z j a) ≤ F.blockSide ^ j * supNorm a := by
    rw [supNorm_le_iff]
    intro i
    show ((F.blockSide : ℤ) ^ j * (closedOrthant S z i * a i)).natAbs ≤ _
    rw [Int.natAbs_mul, Int.natAbs_mul]
    have h1 : (closedOrthant S z i).natAbs = 1 := by
      rcases he i with h | h <;> rw [h] <;> rfl
    rw [h1, one_mul]
    have h2 : ((F.blockSide : ℤ) ^ j).natAbs = F.blockSide ^ j := by
      rw [Int.natAbs_pow]
      simp
    rw [h2]
    exact Nat.mul_le_mul_left _ (natAbs_le_supNorm a i)
  exact_mod_cast this
theorem finiteDiffBound_chartSite (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (hL : 0 < F.blockSide) {j : ℕ} (hj : j ≤ F.top) {x0 : Lattice4}
    {D : Set Lattice4} {W : Type} [NormedAddCommGroup W] {Bf : ℝ} {f : Lattice4 × Lattice4 → W} (hB : 0 ≤ Bf)
    (h : FiniteDiffBound (FlatPairing.scaledPairNorm (1 / (GaugeMap.cellSideLength F : ℝ))) 3 (D ×ˢ D) Bf f) :
    FiniteDiffBound (FlatPairing.scaledPairNorm (levelScale F j)) 3
      ({a | chartSite S z j x0 a ∈ D} ×ˢ {a | chartSite S z j x0 a ∈ D}) Bf
      (fun q => f (chartSite S z j x0 q.1, chartSite S z j x0 q.2)) := by
  have hN' : (0 : ℝ) < GaugeMap.cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
  have hlen : ∀ a, 0 ≤ FlatPairing.scaledPairNorm (1 / (GaugeMap.cellSideLength F : ℝ)) a := fun a => by
    unfold FlatPairing.scaledPairNorm
    positivity
  have h1 := h.comp_add_right (x0, x0)
  have h2 := h1.comp hlen (AddMonoidHom.prodMap (chartScaleHom S z j) (chartScaleHom S z j))
    (len' := FlatPairing.scaledPairNorm (levelScale F j)) (fun a => ?_) hB
  · refine (h2.mono ?_).congr fun q => ?_
    · rintro q ⟨q1, q2⟩
      exact ⟨q1, q2⟩
    · rfl
  · show 1 / (GaugeMap.cellSideLength F : ℝ) *
        ((supNorm (chartScaleHom S z j a.1) : ℝ) + supNorm (chartScaleHom S z j a.2)) ≤
      levelScale F j * ((supNorm a.1 : ℝ) + supNorm a.2)
    rw [← inv_cellSideLength_mul_pow hL hj]
    have s1 := supNorm_chartScaleHom_le he j a.1
    have s2 := supNorm_chartScaleHom_le he j a.2
    calc _ ≤ 1 / (GaugeMap.cellSideLength F : ℝ) *
          ((F.blockSide : ℝ) ^ j * supNorm a.1 + (F.blockSide : ℝ) ^ j * supNorm a.2) :=
          mul_le_mul_of_nonneg_left (add_le_add s1 s2) (by positivity)
      _ = _ := by ring
theorem pathHolonomy_eq_pathProduct {j : ℕ} {X : F.GaugeField j} {w0 : F.Site j}
    {R : Lattice4 → Lattice4 → UnitQuaternion} {g : Lattice4 → UnitQuaternion} {good : Lattice4 → Prop}
    (hstep : ∀ a st, good a → good (a + FlatPairing.stepDisplacement st) →
      linkValue X (w0 + siteOfCoords j a) st =
        g a * R a (a + FlatPairing.stepDisplacement st) * (g (a + FlatPairing.stepDisplacement st))⁻¹)
    {a : Lattice4} {l : List PathStep} (hp : AllAlong good a l) :
    pathHolonomy X (w0 + siteOfCoords j a) l = g a * FlatPairing.pathProduct R a l * (g (endpoint a l))⁻¹ := by
  induction l generalizing a with
  | nil => simp [pathHolonomy, FlatPairing.pathProduct, endpoint]
  | cons st r ih =>
    have e1 : w0 + siteOfCoords j a + BlockAverages.stepDisplacement j st =
        w0 + siteOfCoords j (a + FlatPairing.stepDisplacement st) := by
      rw [siteOfCoords_add, siteOfCoords_stepDisplacement, add_assoc]
    show linkValue X (w0 + siteOfCoords j a) st *
        pathHolonomy X (w0 + siteOfCoords j a + BlockAverages.stepDisplacement j st) r =
      g a * (R a (a + FlatPairing.stepDisplacement st) *
        FlatPairing.pathProduct R (a + FlatPairing.stepDisplacement st) r) *
        (g (endpoint (a + FlatPairing.stepDisplacement st) r))⁻¹
    rw [e1, ih hp.2, hstep a st hp.1 (allAlong_head hp.2)]
    group
theorem linkValue_eq_of_transport {j : ℕ} {X : F.GaugeField j} {w0 : F.Site j}
    {R : Lattice4 → Lattice4 → UnitQuaternion} {g : Lattice4 → UnitQuaternion} {good : Lattice4 → Prop}
    (hinv : ∀ a b, R b a = (R a b)⁻¹)
    (hlink : ∀ a i, good a → good (a + basisVector i) →
      X (w0 + siteOfCoords j a) i = g a * R a (a + basisVector i) * (g (a + basisVector i))⁻¹) :
    ∀ a st, good a → good (a + FlatPairing.stepDisplacement st) →
      linkValue X (w0 + siteOfCoords j a) st =
        g a * R a (a + FlatPairing.stepDisplacement st) * (g (a + FlatPairing.stepDisplacement st))⁻¹ := by
  rintro a ⟨i, b⟩ h0 h1
  cases b
  · have e0 : FlatPairing.stepDisplacement (i, false) = - basisVector i := by
      simp [FlatPairing.stepDisplacement]
    rw [e0] at h1 ⊢
    have e1 : a + - basisVector i + basisVector i = a := by abel
    have e2 : w0 + siteOfCoords j a - unitStep j i = w0 + siteOfCoords j (a + - basisVector i) := by
      rw [siteOfCoords_add, siteOfCoords_neg, unitStep_eq]
      abel
    have := hlink (a + - basisVector i) i h1 (by rw [e1]; exact h0)
    rw [e1] at this
    simp only [linkValue, Bool.false_eq_true, if_false]
    rw [e2, this, hinv (a + - basisVector i) a]
    group
  · have e0 : FlatPairing.stepDisplacement (i, true) = basisVector i := by
      simp [FlatPairing.stepDisplacement]
    rw [e0] at h1 ⊢
    simp only [linkValue, if_true]
    exact hlink a i h0 h1
theorem polarUnit_swap {P : Lattice4 → Lattice4 → ℍ[ℝ]} (hsym : ∀ a b, P b a = star (P a b))
    (a b : Lattice4) : polarUnit (P b a) = (polarUnit (P a b))⁻¹ := by
  rw [hsym a b, polarUnit_star]
theorem norm_pathProduct_sub_one_le {R : Lattice4 → Lattice4 → UnitQuaternion} {good : Lattice4 → Prop} {e : ℝ}
    (he : ∀ a st, good a → good (a + FlatPairing.stepDisplacement st) →
      ‖((R a (a + FlatPairing.stepDisplacement st) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ e)
    {a : Lattice4} {l : List PathStep} (hp : AllAlong good a l) :
    ‖((FlatPairing.pathProduct R a l : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ l.length * e := by
  induction l generalizing a with
  | nil => simp [FlatPairing.pathProduct]
  | cons st r ih =>
    show ‖((R a (a + FlatPairing.stepDisplacement st) *
      FlatPairing.pathProduct R (a + FlatPairing.stepDisplacement st) r : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ _
    refine (norm_coe_mul_sub_one_le _ _).trans ?_
    have h1 := he a st hp.1 (allAlong_head hp.2)
    have h2 := ih hp.2
    have hl : (((st :: r).length : ℕ) : ℝ) = r.length + 1 := by simp
    rw [hl]
    linarith
end Charts
section Sites
variable {F : BlockFrame} {S : Finset F.Cell}
theorem pow_smul_mem_centredCube (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) {h : Lattice4}
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    (fun i => (F.blockSide : ℤ) ^ j * h i) ∈ centredCube (F.blockSide ^ (F.top - 0)) := by
  simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc] at hh ⊢
  intro i
  have h1 := hh i
  have hP : Odd (F.blockSide ^ (F.top - j)) := hodd.pow
  obtain ⟨k, hk⟩ := hP
  have hQ : (1 : ℤ) ≤ (F.blockSide : ℤ) ^ j := by
    have : 1 ≤ F.blockSide ^ j := Nat.one_le_pow _ _ hodd.pos
    exact_mod_cast this
  have e1 : (((F.blockSide ^ (F.top - j) : ℕ) : ℤ) - 1) / 2 = k := by
    rw [hk]
    push_cast
    omega
  rw [e1] at h1
  have e2 : ((F.blockSide ^ (F.top - 0) : ℕ) : ℤ) =
      2 * ((F.blockSide : ℤ) ^ j * k) + (F.blockSide : ℤ) ^ j := by
    have e3 : F.blockSide ^ (F.top - 0) = F.blockSide ^ j * F.blockSide ^ (F.top - j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [e3, hk]
    push_cast
    ring
  rw [e2]
  have a1 : (F.blockSide : ℤ) ^ j * h i ≤ (F.blockSide : ℤ) ^ j * k :=
    mul_le_mul_of_nonneg_left h1.2 (by omega)
  have a2 : (F.blockSide : ℤ) ^ j * (-(k : ℤ)) ≤ (F.blockSide : ℤ) ^ j * h i :=
    mul_le_mul_of_nonneg_left h1.1 (by omega)
  rw [mul_neg] at a2
  constructor <;> omega
theorem baseSite_mem_sitesOfCells (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) {w : F.Site j}
    (hw : w ∈ sitesOfCells S j) : baseSite w ∈ sitesOfCells S 0 := by
  obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hw
  rw [mem_sitesOfCells]
  refine ⟨y, hy, fun i => (F.blockSide : ℤ) ^ j * h i, pow_smul_mem_centredCube hodd hj hh, ?_⟩
  rw [baseSite_add j hj, baseSite_cellCentre j hj]
theorem refineSite_add_mem_sitesOfCells (hodd : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    {w : F.Site (j + 1)} (hw : w ∈ sitesOfCells S (j + 1))
    {b : Lattice4} (hb : b ∈ centredCube F.blockSide) : refineSite w + siteOfCoords j b ∈ sitesOfCells S j := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.refineSite_add_mem_sitesOfCells <;> assumption
end Sites
section Bounds
variable {F : BlockFrame}
def NearlyFlatBounds (B C r : ℝ) : Prop :=
  ∀ (κ ρ : ℝ) (D : Set Lattice4) (P0 : Lattice4 × Lattice4 → ℝ) (P1 : Lattice4 × Lattice4 → ℍ[ℝ]),
      0 ≤ κ → 0 ≤ ρ → ρ ≤ 1 →
      FiniteDiffBound (FlatPairing.scaledPairNorm κ) 3 (D ×ˢ D) B P0 →
      FiniteDiffBound (FlatPairing.scaledPairNorm κ) 3 (D ×ˢ D) ρ P1 →
      (∀ a b, FlatPairing.pairingValue P0 P1 b a = star (FlatPairing.pairingValue P0 P1 a b)) →
      (∀ a ∈ D, 1 ≤ (FlatPairing.pairingValue P0 P1 a a).re) →
      (∀ a ∈ D, ∀ b ∈ D, κ * supNorm (b - a) ≤ r →
        ‖((polarUnit (FlatPairing.pairingValue P0 P1 a b) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
          C * ρ * (κ * supNorm (b - a))) ∧
      (∀ y ∈ D, ∀ x ∈ D, ∀ t : Lattice4, x + t ∈ D → κ * supNorm (x - y) ≤ r → κ * supNorm t ≤ r →
        ‖((polarUnit (FlatPairing.pairingValue P0 P1 y x) * polarUnit (FlatPairing.pairingValue P0 P1 x (x + t)) *
            polarUnit (FlatPairing.pairingValue P0 P1 (x + t) y) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
          C * ρ * (κ * supNorm (x - y)) * (κ * supNorm t)) ∧
      ∀ (L : ℕ) (i : Fin 4), Odd L → 3 ≤ L → κ * (3 * L) ≤ r → (∀ x ∈ FlatPairing.twoBlockHull L i, x ∈ D) →
        (∀ h ∈ centredCube L, ∀ π : Equiv.Perm (Fin 4),
          ‖((FlatPairing.closedBlockContour (fun a b => polarUnit (FlatPairing.pairingValue P0 P1 a b)) L h π i :
            UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ C * ρ * (κ * L) ^ 2) ∧
        ‖(1 / (24 * (L : ℝ) ^ 4)) • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
          pureComponent ((FlatPairing.closedBlockContour (fun a b => polarUnit (FlatPairing.pairingValue P0 P1 a b))
            L h π i : UnitQuaternion) : ℍ[ℝ])‖ ≤ C * ρ * (κ * L) ^ 3
structure ChartBounds (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (j : ℕ) (w0 : F.Site j)
    (D : Set Lattice4) (R : Lattice4 → Lattice4 → UnitQuaternion) (g : Lattice4 → UnitQuaternion)
    (Cρ r : ℝ) : Prop where
  inv_swap : ∀ a b, R b a = (R a b)⁻¹
  self_eq_one : ∀ a ∈ D, R a a = 1
  near_one : ∀ a ∈ D, ∀ b ∈ D, levelScale F j * supNorm (b - a) ≤ r →
    ‖((R a b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Cρ * (levelScale F j * supNorm (b - a))
  triangle : ∀ y ∈ D, ∀ x ∈ D, ∀ t : Lattice4, x + t ∈ D → levelScale F j * supNorm (x - y) ≤ r →
    levelScale F j * supNorm t ≤ r →
    ‖((R y x * R x (x + t) * R (x + t) y : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      Cρ * (levelScale F j * supNorm (x - y)) * (levelScale F j * supNorm t)
  contour_bounds : ∀ (L : ℕ) (i : Fin 4), Odd L → 3 ≤ L → levelScale F j * (3 * L) ≤ r →
    (∀ x ∈ FlatPairing.twoBlockHull L i, x ∈ D) →
    (∀ h ∈ centredCube L, ∀ π : Equiv.Perm (Fin 4),
      ‖((FlatPairing.closedBlockContour R L h π i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        Cρ * (levelScale F j * L) ^ 2) ∧
    ‖(1 / (24 * (L : ℝ) ^ 4)) • ∑ h ∈ centredCube L, ∑ π : Equiv.Perm (Fin 4),
      pureComponent ((FlatPairing.closedBlockContour R L h π i : UnitQuaternion) : ℍ[ℝ])‖ ≤
        Cρ * (levelScale F j * L) ^ 3
  transport_eq : ∀ a ∈ D, ∀ b ∈ D, levelScale F j * supNorm (b - a) ≤ r →
    polarUnit (quaternionPairing S (leadingFrame S V (baseSite (w0 + siteOfCoords j a)))
      (leadingFrame S V (baseSite (w0 + siteOfCoords j b)))) = g a * R a b * (g b)⁻¹
theorem exists_chartBounds {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell} {B C1 r rr ρ : ℝ}
    (hB : 1 ≤ B) (hN : NearlyFlatBounds B C1 r) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hrr : rr ≤ r)
    (hr : rr ≤ 1 / (8 * B))
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (hL : 0 < F.blockSide)
    {P0 : Lattice4 × Lattice4 → ℝ} {P1 : Lattice4 × Lattice4 → ℍ[ℝ]}
    (h0 : FiniteDiffBound (FlatPairing.scaledPairNorm (1 / (GaugeMap.cellSideLength F : ℝ))) 3
      (patchLocalSites S z ×ˢ patchLocalSites S z) B P0)
    (h1 : FiniteDiffBound (FlatPairing.scaledPairNorm (1 / (GaugeMap.cellSideLength F : ℝ))) 3
      (patchLocalSites S z ×ˢ patchLocalSites S z) ρ P1)
    (hsym : ∀ a b, FlatPairing.pairingValue P0 P1 b a = star (FlatPairing.pairingValue P0 P1 a b))
    (hlow : ∀ a ∈ patchLocalSites S z, 1 ≤ (FlatPairing.pairingValue P0 P1 a a).re)
    (hpair : ∀ a ∈ patchLocalSites S z, ∀ b ∈ patchLocalSites S z, FlatPairing.pairingValue P0 P1 a b ≠ 0 →
      polarUnit (quaternionPairing S (leadingFrame S V (GaugeMap.patchSite S z a))
        (leadingFrame S V (GaugeMap.patchSite S z b))) =
        GaugeMap.frameChange S V z (GaugeMap.patchSite S z a) * polarUnit (FlatPairing.pairingValue P0 P1 a b) *
          (GaugeMap.frameChange S V z (GaugeMap.patchSite S z b))⁻¹)
    {j : ℕ} (hj : j ≤ F.top) {w0 : F.Site j} {x0 : Lattice4} (hw : baseSite w0 = GaugeMap.patchSite S z x0) :
    ∃ R : Lattice4 → Lattice4 → UnitQuaternion,
      ChartBounds S V z j w0 {a | chartSite S z j x0 a ∈ patchLocalSites S z} R
        (fun a => GaugeMap.frameChange S V z (baseSite (w0 + siteOfCoords j a))) (C1 * ρ) rr := by
  set D : Set Lattice4 := {a | chartSite S z j x0 a ∈ patchLocalSites S z} with hD
  have hB0 : 0 ≤ B := by linarith
  have b0 := finiteDiffBound_chartSite (x0 := x0) he hL hj hB0 h0
  have b1 := finiteDiffBound_chartSite (x0 := x0) he hL hj hρ0 h1
  set Q0 : Lattice4 × Lattice4 → ℝ := fun q => P0 (chartSite S z j x0 q.1, chartSite S z j x0 q.2) with hQ0
  set Q1 : Lattice4 × Lattice4 → ℍ[ℝ] := fun q => P1 (chartSite S z j x0 q.1, chartSite S z j x0 q.2) with hQ1
  have hsym' : ∀ a b, FlatPairing.pairingValue Q0 Q1 b a = star (FlatPairing.pairingValue Q0 Q1 a b) :=
    fun a b => hsym _ _
  have hlow' : ∀ a ∈ D, 1 ≤ (FlatPairing.pairingValue Q0 Q1 a a).re := fun a ha => hlow _ ha
  obtain ⟨n1, n2, n3⟩ := hN (levelScale F j) ρ D Q0 Q1 (zero_le_levelScale j) hρ0 hρ1 b0 b1 hsym' hlow'
  refine ⟨fun a b => polarUnit (FlatPairing.pairingValue Q0 Q1 a b), ?_⟩
  have hne : ∀ a ∈ D, ∀ b ∈ D, levelScale F j * supNorm (b - a) ≤ rr →
      FlatPairing.pairingValue Q0 Q1 a b ≠ 0 := by
    intro a ha b hb hd h0'
    have e : ((a, a) : Lattice4 × Lattice4) + ((0 : Lattice4), b - a) = (a, b) := by simp
    have hl : FlatPairing.scaledPairNorm (levelScale F j) ((0 : Lattice4), b - a) =
        levelScale F j * supNorm (b - a) := by
      simp [FlatPairing.scaledPairNorm, supNorm_zero]
    have f0 := b0.norm_sub_le (x := (a, a)) (a := ((0 : Lattice4), b - a)) ⟨ha, ha⟩ (by rw [e]; exact ⟨ha, hb⟩)
    have f1 := b1.norm_sub_le (x := (a, a)) (a := ((0 : Lattice4), b - a)) ⟨ha, ha⟩ (by rw [e]; exact ⟨ha, hb⟩)
    rw [e, hl] at f0 f1
    have hlo := hlow' a ha
    have e2 : (FlatPairing.pairingValue Q0 Q1 a a - FlatPairing.pairingValue Q0 Q1 a b) =
        ((Q0 (a, a) - Q0 (a, b) : ℝ) : ℍ[ℝ]) + (Q1 (a, a) - Q1 (a, b)) := by
      simp only [FlatPairing.pairingValue, Quaternion.coe_sub]
      abel
    have h3 := quaternion_re_le_norm (FlatPairing.pairingValue Q0 Q1 a a - FlatPairing.pairingValue Q0 Q1 a b)
    rw [h0', sub_zero] at h3
    have h4 : ‖FlatPairing.pairingValue Q0 Q1 a a‖ ≤ (B + 1) * (levelScale F j * supNorm (b - a)) := by
      have e3 : FlatPairing.pairingValue Q0 Q1 a a =
          FlatPairing.pairingValue Q0 Q1 a a - FlatPairing.pairingValue Q0 Q1 a b := by rw [h0', sub_zero]
      rw [e3, e2]
      refine (norm_add_le _ _).trans ?_
      rw [Quaternion.norm_coe, norm_sub_rev, norm_sub_rev (Q1 (a, a))]
      have f2 : ‖Q1 (a, b) - Q1 (a, a)‖ ≤ 1 * (levelScale F j * supNorm (b - a)) :=
        f1.trans (mul_le_mul_of_nonneg_right hρ1 (by have := zero_le_levelScale (F := F) j; positivity))
      nlinarith
    have h5 : (B + 1) * (levelScale F j * supNorm (b - a)) ≤ (B + 1) * (1 / (8 * B)) :=
      mul_le_mul_of_nonneg_left (hd.trans hr) (by linarith)
    have h6 : (B + 1) * (1 / (8 * B)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith
    linarith
  refine ⟨fun a b => polarUnit_swap hsym' a b, fun a ha => ?_,
    fun a ha b hb hd => n1 a ha b hb (hd.trans hrr),
    fun y hy x hx t ht d1 d2 => n2 y hy x hx t ht (d1.trans hrr) (d2.trans hrr), ?_, ?_⟩
  · have hr' := eq_coe_re_of_star_eq (q := FlatPairing.pairingValue Q0 Q1 a a) (hsym' a a).symm
    have hl := hlow' a ha
    show polarUnit (FlatPairing.pairingValue Q0 Q1 a a) = 1
    rw [hr']
    exact polarUnit_coe (by linarith)
  · intro L i hodd hL3 hrL hDh
    exact n3 L i hodd hL3 (hrL.trans hrr) hDh
  · intro a ha b hb hd
    have := hpair _ ha _ hb (hne a ha b hb hd)
    rw [baseSite_chartSite he hj hw, baseSite_chartSite he hj hw]
    exact this
end Bounds
section Estimates
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell} {j : ℕ} {w0 : F.Site j}
  {D : Set Lattice4} {R : Lattice4 → Lattice4 → UnitQuaternion} {g : Lattice4 → UnitQuaternion} {Cρ rr : ℝ}
theorem exists_patch_chart (hodd : Odd F.blockSide)
    (hes : ∀ (z : F.Cell) (i : Fin 4), closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (hj : j ≤ F.top)
    {w : F.Site j} (hw : w ∈ sitesOfCells S j) :
    ∃ z ∈ S, ∃ x0 : Lattice4, baseSite w = GaugeMap.patchSite S z x0 ∧
      ∀ i, 0 ≤ x0 i ∧ x0 i < GaugeMap.cellSideLength F := by
  obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hw
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  refine ⟨y, hy, fun i => closedOrthant S y i * ((F.blockSide : ℤ) ^ j * h i) +
    (GaugeMap.cellSideLength F - 1) / 2, ?_, fun i => ?_⟩
  · rw [baseSite_add j hj, baseSite_cellCentre j hj]
    unfold GaugeMap.patchSite
    congr 2
    funext i
    have e := closedOrthant_mul_self (hes y) i
    simp only [add_sub_cancel_right]
    rw [← mul_assoc, e, one_mul]
  · have hm := (Fintype.mem_piFinset.1 (pow_smul_mem_centredCube hodd hj hh)) i
    have hcs : ((F.blockSide ^ (F.top - 0) : ℕ) : ℤ) = GaugeMap.cellSideLength F := by
      simp [GaugeMap.cellSideLength]
    simp only [Finset.mem_Icc, hcs] at hm
    dsimp only
    rcases hes y i with h1 | h1 <;> rw [h1] <;> constructor <;> omega
theorem mem_chart_of_bounded (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (hj : j ≤ F.top) {x0 a : Lattice4}
    (hw : baseSite w0 = GaugeMap.patchSite S z x0) (hx0 : ∀ i, 0 ≤ x0 i ∧ x0 i < GaugeMap.cellSideLength F)
    (hA : ∀ i, |(F.blockSide : ℤ) ^ j * a i| ≤ 3 * GaugeMap.cellSideLength F)
    (hs : w0 + siteOfCoords j a ∈ sitesOfCells S j) :
    a ∈ {a | chartSite S z j x0 a ∈ patchLocalSites S z} := by
  refine ⟨fun i => ?_, ?_⟩
  · have h1 := hx0 i
    have h2 := abs_le.1 (hA i)
    simp only [chartSite]
    have e : (F.blockSide : ℤ) ^ j * (closedOrthant S z i * a i) =
        closedOrthant S z i * ((F.blockSide : ℤ) ^ j * a i) := by ring
    rw [e]
    rcases he i with h | h <;> rw [h] <;> constructor <;> omega
  · rw [← baseSite_chartSite he hj hw]
    exact baseSite_mem_sitesOfCells hodd hj hs
theorem referenceFieldChain_of_lt (hj : j < F.top) : referenceFieldChain S V j = referenceGaugeField S V j := by
  classical
  unfold referenceFieldChain
  exact Function.update_of_ne hj.ne _ _
theorem referenceFieldChain_top : referenceFieldChain S V F.top = V := by
  classical
  unfold referenceFieldChain
  exact Function.update_self _ _ _
theorem ChartBounds.linkValue_eq (cf : ChartBounds S V z j w0 D R g Cρ rr) (hκ : levelScale F j ≤ rr)
    {good : Lattice4 → Prop} (hgood : ∀ a, good a → a ∈ D) :
    ∀ a st, good a → good (a + FlatPairing.stepDisplacement st) →
      linkValue (referenceGaugeField S V j) (w0 + siteOfCoords j a) st =
        g a * R a (a + FlatPairing.stepDisplacement st) * (g (a + FlatPairing.stepDisplacement st))⁻¹ := by
  refine linkValue_eq_of_transport cf.inv_swap fun a i h0 h1 => ?_
  have e : w0 + siteOfCoords j a + unitStep j i = w0 + siteOfCoords j (a + basisVector i) := by
    rw [siteOfCoords_add, unitStep_eq, add_assoc]
  have hd : levelScale F j * supNorm (a + basisVector i - a) ≤ rr := by
    rw [add_sub_cancel_left, supNorm_basisVector]
    simpa using hκ
  have := cf.transport_eq a (hgood a h0) _ (hgood _ h1) hd
  rw [← this]
  show polarUnit (quaternionPairing S _ _) = _
  simp only [e]
theorem norm_conj_product_sub_one_le (g0 g1 Q w Dd : UnitQuaternion) :
    ‖(((g0 * Dd * Q * g1⁻¹) * (g0 * w * Q * g1⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      ‖(Dd : ℍ[ℝ]) - 1‖ + ‖(w : ℍ[ℝ]) - 1‖ := by
  have e : (g0 * Dd * Q * g1⁻¹) * (g0 * w * Q * g1⁻¹)⁻¹ = g0 * (Dd * w⁻¹) * g0⁻¹ := by group
  rw [e, norm_coe_conj_sub_one]
  refine (norm_coe_mul_sub_one_le _ _).trans ?_
  rw [norm_coe_inv_sub_one]
theorem norm_conj_quotient_sub_one_eq (g0 g1 Q w : UnitQuaternion) :
    ‖(((g0 * Q * g1⁻¹) * (g0 * w * Q * g1⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(w : ℍ[ℝ]) - 1‖ := by
  have e : (g0 * Q * g1⁻¹) * (g0 * w * Q * g1⁻¹)⁻¹ = g0 * w⁻¹ * g0⁻¹ := by group
  rw [e, norm_coe_conj_sub_one, norm_coe_inv_sub_one]
theorem norm_mul_inv_factor_sub_one_le (g0 g1 w X : UnitQuaternion) :
    ‖((X * (g0 * w * 1 * g1⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      ‖((g0⁻¹ * X * g1 : UnitQuaternion) : ℍ[ℝ]) - 1‖ + ‖(w : ℍ[ℝ]) - 1‖ := by
  have e : X * (g0 * w * 1 * g1⁻¹)⁻¹ = g0 * ((g0⁻¹ * X * g1) * w⁻¹) * g0⁻¹ := by group
  rw [e, norm_coe_conj_sub_one]
  refine (norm_coe_mul_sub_one_le _ _).trans ?_
  rw [norm_coe_inv_sub_one]
theorem plaquetteDefect_referenceGaugeField_le (cf : ChartBounds S V z j w0 D R g Cρ rr)
    (hκ : levelScale F j ≤ rr) (hC : 0 ≤ Cρ)
    {μ ν : Fin 4} (hμν : μ ≠ ν) (h0 : (0 : Lattice4) ∈ D) (h1 : basisVector μ ∈ D) (h2 : basisVector ν ∈ D)
    (h3 : basisVector μ + basisVector ν ∈ D) :
    plaquetteDefect (referenceGaugeField S V j) (w0, μ, ν) ≤ 2 * Cρ * levelScale F j ^ 2 := by
  set v := basisVector μ + basisVector ν with hv
  set good : Lattice4 → Prop := fun a => a ∈ D with hgood
  have hs1 : FlatPairing.stepDisplacement (μ, true) = basisVector μ := by simp [FlatPairing.stepDisplacement]
  have hs2 : FlatPairing.stepDisplacement (ν, true) = basisVector ν := by simp [FlatPairing.stepDisplacement]
  have hs3 : FlatPairing.stepDisplacement (μ, false) = - basisVector μ := by simp [FlatPairing.stepDisplacement]
  have hs4 : FlatPairing.stepDisplacement (ν, false) = - basisVector ν := by simp [FlatPairing.stepDisplacement]
  have p1 : (0 : Lattice4) + basisVector μ = basisVector μ := zero_add _
  have p3 : v + - basisVector μ = basisVector ν := by rw [hv]; abel
  have p4 : basisVector ν + - basisVector ν = 0 := by abel
  have q1 : (0 : Lattice4) + FlatPairing.stepDisplacement (μ, true) = basisVector μ := by rw [hs1, zero_add]
  have q2 : basisVector μ + FlatPairing.stepDisplacement (ν, true) = v := by rw [hs2]
  have q3 : v + FlatPairing.stepDisplacement (μ, false) = basisVector ν := by rw [hs3]; exact p3
  have q4 : basisVector ν + FlatPairing.stepDisplacement (ν, false) = 0 := by rw [hs4]; exact p4
  set l : List PathStep := [(μ, true), (ν, true), (μ, false), (ν, false)] with hl
  have hp : AllAlong good 0 l := by
    refine ⟨h0, ?_⟩
    rw [q1]
    refine ⟨h1, ?_⟩
    rw [q2]
    refine ⟨h3, ?_⟩
    rw [q3]
    refine ⟨h2, ?_⟩
    rw [q4]
    exact h0
  have e1 : FlatPairing.pathProduct R 0 l =
      R 0 (basisVector μ) * (R (basisVector μ) v * (R v (basisVector ν) * (R (basisVector ν) 0 * 1))) := by
    simp only [hl, FlatPairing.pathProduct, q1, q2, q3, q4]
  have e2 : endpoint 0 l = 0 := by
    simp only [hl, endpoint, q1, q2, q3, q4]
  have hol := pathHolonomy_eq_pathProduct (ChartBounds.linkValue_eq cf hκ (good := good) (fun a h => h)) hp
  rw [siteOfCoords_zero, add_zero, e1, e2] at hol
  have hv1 : supNorm v ≤ 1 := by
    rw [supNorm_le_iff]
    intro k
    by_cases k1 : k = μ
    · subst k1
      simp [hv, basisVector, hμν]
    · by_cases k2 : k = ν
      · subst k2
        simp [hv, basisVector, k1]
      · simp [hv, basisVector, k1, k2]
  have hv1' : (supNorm v : ℝ) ≤ 1 := by exact_mod_cast hv1
  have hκ0 := zero_le_levelScale (F := F) j
  have dv : levelScale F j * supNorm v ≤ rr :=
    (mul_le_of_le_one_right hκ0 hv1').trans hκ
  have d1 : levelScale F j * supNorm (basisVector μ - (0 : Lattice4)) ≤ rr := by
    rw [sub_zero, supNorm_basisVector]
    simpa using hκ
  have d2 : levelScale F j * supNorm (basisVector ν) ≤ rr := by
    rw [supNorm_basisVector]
    simpa using hκ
  have d3 : levelScale F j * supNorm (v - (0 : Lattice4)) ≤ rr := by
    rw [sub_zero]
    exact dv
  have d4 : levelScale F j * supNorm (- basisVector μ) ≤ rr := by
    rw [supNorm_neg, supNorm_basisVector]
    simpa using hκ
  have t1 := cf.triangle 0 h0 (basisVector μ) h1 (basisVector ν) h3 d1 d2
  have t2 := cf.triangle 0 h0 v h3 (- basisVector μ) (by rw [p3]; exact h2) d3 d4
  rw [p3] at t2
  rw [sub_zero, supNorm_basisVector, supNorm_basisVector] at t1
  rw [sub_zero, supNorm_neg, supNorm_basisVector] at t2
  simp only [Nat.cast_one, mul_one] at t1 t2
  have hI := cf.inv_swap 0 v
  set T1 : UnitQuaternion := R 0 (basisVector μ) * R (basisVector μ) v * R v 0 with hT1
  set T2 : UnitQuaternion := R 0 v * R v (basisVector ν) * R (basisVector ν) 0 with hT2
  have e3 : R 0 (basisVector μ) * (R (basisVector μ) v * (R v (basisVector ν) * (R (basisVector ν) 0 * 1))) =
      T1 * T2 := by
    rw [hT1, hT2, hI]
    group
  rw [e3] at hol
  show ‖((pathHolonomy (referenceGaugeField S V j) w0 l : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ _
  rw [hol, norm_coe_conj_sub_one]
  refine (norm_coe_mul_sub_one_le _ _).trans ?_
  have t3 : ‖(T2 : ℍ[ℝ]) - 1‖ ≤ Cρ * levelScale F j * levelScale F j := by
    refine t2.trans ?_
    have : Cρ * (levelScale F j * supNorm v) ≤ Cρ * levelScale F j :=
      mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hκ0 hv1') hC
    exact mul_le_mul_of_nonneg_right this hκ0
  have t4 : ‖(T1 : ℍ[ℝ]) - 1‖ ≤ Cρ * levelScale F j * levelScale F j := t1
  calc _ ≤ Cρ * levelScale F j * levelScale F j + Cρ * levelScale F j * levelScale F j := add_le_add t4 t3
    _ = _ := by ring
theorem pathHolonomy_bondContour_eq (cf : ChartBounds S V z j w0 D R g Cρ rr) (hκ : levelScale F j ≤ rr)
    {L : ℕ} {i : Fin 4} (hL : 1 ≤ L) (hhull : ∀ x ∈ FlatPairing.twoBlockHull L i, x ∈ D) {h : Lattice4}
    (hh : h ∈ centredCube L) (π : Equiv.Perm (Fin 4)) :
    pathHolonomy (referenceGaugeField S V j) w0 (bondContour L h π i) =
      g 0 * FlatPairing.pathProduct R 0 (bondContour L h π i) * (g ((L : ℤ) • basisVector i))⁻¹ := by
  obtain ⟨c1, c2⟩ := bondContour_spec π i hL hh
  have := pathHolonomy_eq_pathProduct (ChartBounds.linkValue_eq cf hκ
    (good := fun a => a ∈ FlatPairing.twoBlockHull L i) (fun a h => hhull a h)) c1
  rwa [siteOfCoords_zero, add_zero, c2] at this
theorem contourAverage_bounds_below_top (cf : ChartBounds S V z j w0 D R g Cρ rr) (hκ : levelScale F j ≤ rr)
    {y : F.Site (j + 1)} {i : Fin 4}
    (hw0 : w0 = refineSite y) (hodd : Odd F.blockSide) (hL3 : 3 ≤ F.blockSide)
    (hrL : levelScale F j * (3 * F.blockSide) ≤ rr)
    (hhull : ∀ x ∈ FlatPairing.twoBlockHull F.blockSide i, x ∈ D) (hC : 0 ≤ Cρ)
    (he1 : Cρ * (levelScale F j * F.blockSide) ^ 2 ≤ 1 / 2) :
    ∃ w : UnitQuaternion, polarUnit (contourAverage (referenceGaugeField S V j) (y, i)) =
        g 0 * w * R 0 ((F.blockSide : ℤ) • basisVector i) * (g ((F.blockSide : ℤ) • basisVector i))⁻¹ ∧
      ‖(w : ℍ[ℝ]) - 1‖ ≤ 4 * (Cρ * (levelScale F j * F.blockSide) ^ 3) ∧
      (∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
        ‖((pathHolonomy (referenceGaugeField S V j) (refineSite y) (bondContour F.blockSide h π i) *
          (polarUnit (contourAverage (referenceGaugeField S V j) (y, i)))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
            Cρ * (levelScale F j * F.blockSide) ^ 2 + 4 * (Cρ * (levelScale F j * F.blockSide) ^ 3)) ∧
      0 ≤ 1 - ‖contourAverage (referenceGaugeField S V j) (y, i)‖ ∧
      1 - ‖contourAverage (referenceGaugeField S V j) (y, i)‖ ≤
        (Cρ * (levelScale F j * F.blockSide) ^ 2) ^ 2 / 2 := by
  obtain ⟨n1, n2⟩ := cf.contour_bounds F.blockSide i hodd hL3 hrL hhull
  set Le : Lattice4 := (F.blockSide : ℤ) • basisVector i with hLe
  set Q := R 0 Le with hQ
  set Dd : Lattice4 → Equiv.Perm (Fin 4) → UnitQuaternion :=
    fun h π => FlatPairing.closedBlockContour R F.blockSide h π i with hDd
  have hL1 : 1 ≤ F.blockSide := by omega
  have hol : ∀ h ∈ centredCube F.blockSide, ∀ π,
      pathHolonomy (referenceGaugeField S V j) (refineSite y) (bondContour F.blockSide h π (y, i).2) =
      g 0 * Dd h π * Q * (g Le)⁻¹ := by
    intro h hh π
    have h1 := pathHolonomy_bondContour_eq cf hκ hL1 hhull hh π
    rw [hw0] at h1
    show pathHolonomy (referenceGaugeField S V j) (refineSite y) (bondContour F.blockSide h π i) = _
    rw [h1]
    simp only [hDd, FlatPairing.closedBlockContour, hQ, hLe]
    rw [cf.inv_swap 0 ((F.blockSide : ℤ) • basisVector i)]
    generalize FlatPairing.pathProduct R 0 (bondContour F.blockSide h π i) = pp
    generalize R 0 ((F.blockSide : ℤ) • basisVector i) = q
    generalize g ((F.blockSide : ℤ) • basisVector i) = gl
    generalize g 0 = g0
    group
  have e0 : 0 ≤ Cρ * (levelScale F j * F.blockSide) ^ 2 := by positivity
  obtain ⟨w, hu, hw, h6a, h6b⟩ := contourAverage_polarUnit_factor (X := referenceGaugeField S V j) (y, i) hodd
    (g0 := g 0) (g1 := g Le) (Q := Q) (Dd := Dd) e0 he1 n1 n2 hol
  refine ⟨w, hu, hw, fun h hh π => ?_, h6a, h6b⟩
  rw [hu, (show pathHolonomy (referenceGaugeField S V j) (refineSite y) (bondContour F.blockSide h π i) = _
    from hol h hh π)]
  refine (norm_conj_product_sub_one_le _ _ _ _ _).trans (add_le_add (n1 h hh π) hw)
end Estimates
section Assembly
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
theorem patchSite_injOn_small (hamb : IsAdmissibleAmbient F) (hL : 0 < F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {a b : Lattice4} (h : GaugeMap.patchSite S z a = GaugeMap.patchSite S z b)
    (hab : ∀ k, |a k - b k| < 64 * GaugeMap.cellSideLength F) : a = b := by
  funext k
  have h1 := congrFun (add_left_cancel h) k
  simp only [siteOfCoords] at h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  have e : closedOrthant S z k * (b k - (GaugeMap.cellSideLength F - 1) / 2) -
      closedOrthant S z k * (a k - (GaugeMap.cellSideLength F - 1) / 2) =
      closedOrthant S z k * (b k - a k) := by ring
  rw [e] at h1
  have h2 : closedOrthant S z k * (b k - a k) = 0 := by
    rcases period_zero_eq_zero_or hamb hL k with h0 | h0
    · rw [h0] at h1
      exact zero_dvd_iff.1 (by simpa using h1)
    · refine Int.eq_zero_of_abs_lt_dvd h1 ?_
      rw [abs_mul, abs_closedOrthant he, one_mul, abs_sub_comm]
      exact lt_of_lt_of_le (hab k) h0
  rcases he k with h3 | h3 <;> rw [h3] at h2 <;> omega
theorem patchDomain_coord_bounds {x : Lattice4} (hx : x ∈ GaugeMap.patchDomain S z) (i : Fin 4) :
    -(10 * GaugeMap.cellSideLength F) ≤ x i ∧ x i < 21 * GaugeMap.cellSideLength F := by
  classical
  have h1 := (Finset.mem_filter.1 hx).1
  have h2 := (Fintype.mem_piFinset.1 h1) i
  rw [Finset.mem_Icc] at h2
  constructor <;> omega
theorem twoBlockHull_mem_chart (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {j : ℕ} (hj : j + 1 ≤ F.top)
    {y : F.Site (j + 1)} {i : Fin 4} (hy : y ∈ sitesOfCells S (j + 1))
    (hy' : y + unitStep (j + 1) i ∈ sitesOfCells S (j + 1))
    {x0 : Lattice4} (hw : baseSite (refineSite y) = GaugeMap.patchSite S z x0)
    (hx0 : ∀ i, 0 ≤ x0 i ∧ x0 i < GaugeMap.cellSideLength F) {a : Lattice4}
    (ha : a ∈ FlatPairing.twoBlockHull F.blockSide i) :
    a ∈ {a | chartSite S z j x0 a ∈ patchLocalSites S z} := by
  have hL := hodd.pos
  have hL1 : (1 : ℤ) ≤ F.blockSide := by exact_mod_cast hL
  refine mem_chart_of_bounded hodd he (by omega) hw hx0 (fun k => ?_) ?_
  · have hk := ha k
    have hpos : (0 : ℤ) < (F.blockSide : ℤ) ^ j := by positivity
    have hb : |a k| ≤ 2 * (F.blockSide : ℤ) := by
      rw [abs_le]
      have : (if k = i then (F.blockSide : ℤ) else 0) ≤ F.blockSide := by split_ifs <;> omega
      constructor <;> omega
    rw [abs_mul, abs_of_pos hpos]
    have h1 : (F.blockSide : ℤ) ^ j * |a k| ≤ (F.blockSide : ℤ) ^ j * (2 * (F.blockSide : ℤ)) :=
      mul_le_mul_of_nonneg_left hb hpos.le
    have h2 : (F.blockSide : ℤ) ^ (j + 1) ≤ GaugeMap.cellSideLength F := by
      unfold GaugeMap.cellSideLength
      exact pow_le_pow_right₀ hL1 hj
    have h3 : (F.blockSide : ℤ) ^ j * (2 * (F.blockSide : ℤ)) = 2 * (F.blockSide : ℤ) ^ (j + 1) := by ring
    have hN := cellSideLength_pos (F := F) hL
    omega
  · by_cases hc : a i ≤ ((F.blockSide : ℤ) - 1) / 2
    · have hcube : a ∈ centredCube F.blockSide := by
        rw [mem_centredCube_iff]
        intro k
        have hk := ha k
        by_cases hki : k = i
        · subst hki
          exact ⟨hk.1, hc⟩
        · simpa [hki] using hk
      exact refineSite_add_mem_sitesOfCells hodd hj hy hcube
    · set a' : Lattice4 := a - (F.blockSide : ℤ) • basisVector i with ha'
      have hcube : a' ∈ centredCube F.blockSide := by
        rw [mem_centredCube_iff]
        intro k
        have hk := ha k
        by_cases hki : k = i
        · subst hki
          simp only [if_true] at hk
          obtain ⟨q, hq⟩ := hodd
          have hq' : (F.blockSide : ℤ) = 2 * q + 1 := by rw [hq]; push_cast; ring
          have e : a' k = a k - F.blockSide := by simp [ha', basisVector]
          rw [e]
          constructor <;> omega
        · simpa [ha', basisVector, hki] using hk
      have := refineSite_add_mem_sitesOfCells hodd hj hy' hcube
      have e : refineSite (y + unitStep (j + 1) i) + siteOfCoords j a' = refineSite y + siteOfCoords j a := by
        rw [unitStep_eq, refineSite_add j hj, add_assoc, ← siteOfCoords_add]
        congr 2
        funext k
        simp [ha', basisVector, Pi.single_apply]
      rwa [e] at this
theorem levelScale_mul_blockSide (hL : 0 < F.blockSide) {j : ℕ} (hj : j < F.top) :
    levelScale F j * F.blockSide = levelScale F (j + 1) := by
  have hL' : (F.blockSide : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have e : F.top - j = (F.top - (j + 1)) + 1 := by omega
  unfold levelScale
  rw [e, pow_succ]
  field_simp
theorem levelScale_top_eq_one : levelScale F F.top = 1 := by
  simp [levelScale]
theorem levelScale_le_inv_blockSide (hL : 1 ≤ F.blockSide) {j : ℕ} (hj : j < F.top) :
    levelScale F j ≤ 1 / (F.blockSide : ℝ) := by
  have h1 : (0 : ℝ) ≤ 1 / (F.blockSide : ℝ) := by positivity
  have h2 : 1 / (F.blockSide : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hL)]
    exact_mod_cast hL
  unfold levelScale
  calc (1 / (F.blockSide : ℝ)) ^ (F.top - j) ≤ (1 / (F.blockSide : ℝ)) ^ 1 :=
        pow_le_pow_of_le_one h1 h2 (by omega)
    _ = _ := by simp
theorem baseSite_cell (y : F.Cell) : baseSite y = cellCentre 0 y := rfl
theorem baseSite_refineSite_add_blockSide (hodd : Odd F.blockSide) {j : ℕ} (hj : j + 1 ≤ F.top)
    (y : F.Site (j + 1)) (i : Fin 4) :
    baseSite (refineSite y + siteOfCoords j ((F.blockSide : ℤ) • basisVector i)) =
      baseSite (y + unitStep (j + 1) i) := by
  rw [← baseSite_refineSite j hj (y + unitStep (j + 1) i), unitStep_eq, refineSite_add j hj]
  congr 3
variable {V : F.GaugeField F.top} {j : ℕ} {w0 : F.Site j} {D : Set Lattice4}
  {R : Lattice4 → Lattice4 → UnitQuaternion} {g : Lattice4 → UnitQuaternion} {Cρ rr : ℝ}
theorem referenceGaugeField_succ_eq (hodd : Odd F.blockSide) (cf : ChartBounds S V z j w0 D R g Cρ rr)
    (hj : j + 1 ≤ F.top) {y : F.Site (j + 1)}
    {i : Fin 4} (hw0 : w0 = refineSite y) (h0 : (0 : Lattice4) ∈ D)
    (hLe : (F.blockSide : ℤ) • basisVector i ∈ D)
    (d : levelScale F j * supNorm ((F.blockSide : ℤ) • basisVector i - (0 : Lattice4)) ≤ rr) :
    referenceGaugeField S V (j + 1) y i =
      g 0 * R 0 ((F.blockSide : ℤ) • basisVector i) * (g ((F.blockSide : ℤ) • basisVector i))⁻¹ := by
  have lk := cf.transport_eq 0 h0 _ hLe d
  rw [hw0, siteOfCoords_zero, add_zero, baseSite_refineSite j hj,
    baseSite_refineSite_add_blockSide hodd hj] at lk
  exact lk
end Assembly
theorem referenceBoundsStatement_proof (hLoc : patchPairingLocalFormStatement)
    (hNF : FlatPairing.nearlyFlatPairingStatement)
    (hTr : patchTransportStatement) : referenceBoundsStatement := by
  obtain ⟨B, C0, c0, hB, hC0, hc0, hLf⟩ := hLoc
  obtain ⟨C1, r, hC1, hr, hN⟩ := hNF B hB
  have hN' : NearlyFlatBounds B C1 r := hN
  obtain ⟨C2, hC2, hT⟩ := hTr
  have hBpos : 0 < B := by linarith
  set rr : ℝ := min r (1 / (8 * B)) with hrrdef
  have hrr0 : 0 < rr := lt_min hr (by positivity)
  set cc : ℝ := min c0 (min (1 / C0) (1 / (10 * C1 * C0))) with hccdef
  have hcc0 : 0 < cc := lt_min hc0 (lt_min (by positivity) (by positivity))
  set k : ℝ := C1 * C0 with hk
  have hk0 : 0 < k := by positivity
  set Cf : ℝ := 25 * k + C2 + 13 * k ^ 2 + 1 with hCf
  have hCf0 : 0 < Cf := by positivity
  have hkC : ∀ t : ℝ, t ≤ 25 → t * k ≤ Cf := by
    intro t ht
    have : t * k ≤ 25 * k := mul_le_mul_of_nonneg_right ht hk0.le
    have h2 : 0 ≤ 13 * k ^ 2 := by positivity
    rw [hCf]
    linarith
  refine ⟨Cf, cc, ⌈3 / rr⌉₊ + 3, hCf0, hcc0, ?_⟩
  intro F m S hodd hL1 hamb hm hreg s V hs hsc hcold
  have hLpos := hodd.pos
  have hL3 : 3 ≤ F.blockSide := by omega
  have hL1' : 1 ≤ F.blockSide := by omega
  have hLr : (0 : ℝ) < F.blockSide := by exact_mod_cast hLpos
  have hLrr : 3 / (F.blockSide : ℝ) ≤ rr := by
    have h1 : 3 / rr ≤ (⌈3 / rr⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈3 / rr⌉₊ : ℕ) : ℝ) ≤ F.blockSide := by exact_mod_cast (by omega : ⌈3 / rr⌉₊ ≤ F.blockSide)
    have h3 : 3 / rr ≤ F.blockSide := h1.trans h2
    rw [div_le_iff₀ hrr0] at h3
    rw [div_le_iff₀ hLr]
    linarith
  have hes : ∀ (z : F.Cell) (i : Fin 4), closedOrthant S z i = 1 ∨ closedOrthant S z i = -1 :=
    fun z => (closedOrthant_spec hreg (by omega) z).1
  have hsc0 : s ≤ c0 := hsc.trans (min_le_left _ _)
  have hsρ : C0 * s ≤ 1 := by
    have h1 : s ≤ 1 / C0 := hsc.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ hC0] at h1
    linarith
  have hsρ2 : 10 * (C1 * (C0 * s)) ≤ 1 := by
    have h1 : s ≤ 1 / (10 * C1 * C0) := hsc.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  set ρ : ℝ := C0 * s with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set Cρ : ℝ := C1 * ρ with hCρ
  have hCρ0 : 0 ≤ Cρ := by positivity
  have hCρs : Cρ = k * s := by rw [hCρ, hρ, hk]; ring
  have hloc := fun z hz => hLf F m S hodd hamb hm hreg s V hs hsc0 hcold z hz
  have chartAt : ∀ {j : ℕ} (hj : j ≤ F.top) (z : F.Cell) (_ : z ∈ S) (w0 : F.Site j) (x0 : Lattice4),
      baseSite w0 = GaugeMap.patchSite S z x0 → ∃ R, ChartBounds S V z j w0
        {a | chartSite S z j x0 a ∈ patchLocalSites S z} R
        (fun a => GaugeMap.frameChange S V z (baseSite (w0 + siteOfCoords j a))) Cρ rr := by
    intro j hj z hz w0 x0 hw
    obtain ⟨P0, P1, b0, b1, hsym, hlow, hpair, _⟩ := hloc z hz
    exact exists_chartBounds hB hN' hρ0 hsρ (min_le_left _ _) (min_le_right _ _) (hes z) hLpos
      b0 b1 hsym hlow hpair hj hw
  have hlevle : ∀ {j : ℕ}, j < F.top → levelScale F j ≤ rr := by
    intro j hj
    refine (levelScale_le_inv_blockSide hL1' hj).trans (le_trans ?_ hLrr)
    exact div_le_div_of_nonneg_right (by norm_num) hLr.le
  have hlev1 : ∀ {j : ℕ}, j < F.top → levelScale F j ≤ 1 := by
    intro j hj
    refine (levelScale_le_inv_blockSide hL1' hj).trans ?_
    rw [div_le_one hLr]
    exact_mod_cast hL1'
  have bondSites : ∀ {j : ℕ} {y : F.Site j} {i : Fin 4}, (y, i) ∈ innerBonds S j →
      y ∈ sitesOfCells S j ∧ y + unitStep j i ∈ sitesOfCells S j := by
    intro j y i hb
    have := Finset.mem_filter.1 hb
    exact ⟨(Finset.mem_product.1 this.1).1, this.2⟩
  have bondChart : ∀ {j : ℕ}, j < F.top → ∀ {y : F.Site (j + 1)} {i : Fin 4}, (y, i) ∈ innerBonds S (j + 1) →
      ∃ (z : F.Cell) (x0 : Lattice4) (R : Lattice4 → Lattice4 → UnitQuaternion),
        ChartBounds S V z j (refineSite y) {a | chartSite S z j x0 a ∈ patchLocalSites S z} R
          (fun a => GaugeMap.frameChange S V z (baseSite (refineSite y + siteOfCoords j a))) Cρ rr ∧
        ∀ a ∈ FlatPairing.twoBlockHull F.blockSide i, a ∈ {a | chartSite S z j x0 a ∈ patchLocalSites S z} := by
    intro j hj y i hb
    obtain ⟨hy, hy'⟩ := bondSites hb
    have hz0 : (0 : Lattice4) ∈ centredCube F.blockSide := by
      rw [mem_centredCube_iff]
      intro k
      simp only [Pi.zero_apply]
      constructor <;> omega
    have hw0 : refineSite y ∈ sitesOfCells S j := by
      have := refineSite_add_mem_sitesOfCells hodd hj hy hz0
      rwa [siteOfCoords_zero, add_zero] at this
    obtain ⟨z, hz, x0, hw, hx0⟩ := exists_patch_chart hodd hes hj.le hw0
    obtain ⟨R, cf⟩ := chartAt hj.le z hz (refineSite y) x0 hw
    exact ⟨z, x0, R, cf, fun a ha => twoBlockHull_mem_chart hodd (hes z) hj hy hy' hw hx0 ha⟩
  have hLemem : ∀ i : Fin 4, (F.blockSide : ℤ) • basisVector i ∈ FlatPairing.twoBlockHull F.blockSide i := by
    intro i k
    by_cases hk' : k = i
    · subst hk'
      simp [basisVector]
      omega
    · simp [basisVector, hk']
      omega
  have h0mem : ∀ i : Fin 4, (0 : Lattice4) ∈ FlatPairing.twoBlockHull F.blockSide i := by
    intro i k
    have : (0 : ℤ) ≤ if k = i then (F.blockSide : ℤ) else 0 := by split_ifs <;> omega
    simp only [Pi.zero_apply]
    constructor <;> omega
  have hLesup : ∀ i : Fin 4,
      (supNorm ((F.blockSide : ℤ) • basisVector i - (0 : Lattice4)) : ℝ) ≤ F.blockSide := by
    intro i
    have : supNorm ((F.blockSide : ℤ) • basisVector i - (0 : Lattice4)) ≤ F.blockSide := by
      rw [supNorm_le_iff]
      intro k
      by_cases hk' : k = i
      · subst hk'
        simp [basisVector]
      · simp [basisVector, hk']
    exact_mod_cast this
  have topAt : ∀ {y : F.Cell} {i : Fin 4}, (y, i) ∈ innerBonds S F.top →
      ∃ (w g0 g1 : UnitQuaternion),
        polarUnit (contourAverage (referenceGaugeField S V F.depth) (y, i)) = g0 * w * 1 * g1⁻¹ ∧
        ‖(w : ℍ[ℝ]) - 1‖ ≤ 4 * (5 * Cρ) ∧
        (∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
          ‖((pathHolonomy (referenceGaugeField S V F.depth) (refineSite y) (bondContour F.blockSide h π i) *
            (polarUnit (contourAverage (referenceGaugeField S V F.depth) (y, i)))⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
              1‖ ≤ 5 * Cρ + 4 * (5 * Cρ)) ∧
        0 ≤ 1 - ‖contourAverage (referenceGaugeField S V F.depth) (y, i)‖ ∧
        1 - ‖contourAverage (referenceGaugeField S V F.depth) (y, i)‖ ≤ (5 * Cρ) ^ 2 / 2 ∧
        g0 = GaugeMap.cellTransport S V y y ∧ g1 = GaugeMap.cellTransport S V y (y + unitStep F.top i) := by
    intro y i hb
    obtain ⟨hy0, hy0'⟩ := bondSites hb
    have hy : y ∈ S := mem_sitesOfCells_top.1 hy0
    have hy' : y + unitStep F.top i ∈ S := mem_sitesOfCells_top.1 hy0'
    obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
    have hNpos := cellSideLength_pos (F := F) hLpos
    set x0 : Lattice4 := fun _ => (GaugeMap.cellSideLength F - 1) / 2 with hx0def
    have hjt : F.depth + 1 ≤ F.top := le_rfl
    have hw : baseSite (refineSite y) = GaugeMap.patchSite S y x0 := by
      rw [baseSite_refineSite F.depth hjt, baseSite_cell]
      unfold GaugeMap.patchSite
      have : (fun i => closedOrthant S y i * (x0 i - (GaugeMap.cellSideLength F - 1) / 2)) = (0 : Lattice4) := by
        funext k
        simp [hx0def]
      rw [this, siteOfCoords_zero, add_zero]
    have hx0 : ∀ k, 0 ≤ x0 k ∧ x0 k < GaugeMap.cellSideLength F :=
      fun k => ⟨hc0, by simp only [hx0def]; omega⟩
    obtain ⟨R, cf⟩ := chartAt (j := F.depth) (by omega) y hy (refineSite y) x0 hw
    have hhull : ∀ a ∈ FlatPairing.twoBlockHull F.blockSide i,
        a ∈ {a | chartSite S y F.depth x0 a ∈ patchLocalSites S y} :=
      fun a ha => twoBlockHull_mem_chart hodd (hes y) hjt hy0 hy0' hw hx0 ha
    have hjn : F.depth < F.top := Nat.lt_succ_self _
    have hκ := hlevle hjn
    have hκL : levelScale F F.depth * F.blockSide = 1 := by
      rw [levelScale_mul_blockSide hLpos hjn]
      exact levelScale_top_eq_one
    set Le : Lattice4 := (F.blockSide : ℤ) • basisVector i with hLe
    have hnear : ∀ a st, a ∈ FlatPairing.twoBlockHull F.blockSide i →
        a + FlatPairing.stepDisplacement st ∈ FlatPairing.twoBlockHull F.blockSide i →
        ‖((R a (a + FlatPairing.stepDisplacement st) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
          Cρ * levelScale F F.depth := by
      intro a st h1 h2
      have hd : levelScale F F.depth * supNorm (a + FlatPairing.stepDisplacement st - a) ≤ rr := by
        rw [add_sub_cancel_left, supNorm_stepDisplacement]
        simpa using hκ
      have := cf.near_one a (hhull a h1) _ (hhull _ h2) hd
      rw [add_sub_cancel_left, supNorm_stepDisplacement] at this
      simpa using this
    set Dd : Lattice4 → Equiv.Perm (Fin 4) → UnitQuaternion :=
      fun h π => FlatPairing.pathProduct R 0 (bondContour F.blockSide h π i) with hDd
    have hDnear : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖((Dd h π : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 5 * Cρ := by
      intro h hh π
      have h1 := norm_pathProduct_sub_one_le hnear (bondContour_spec π i hL1' hh).1
      refine h1.trans ?_
      have hlen : (((bondContour F.blockSide h π i).length : ℕ) : ℝ) ≤ 5 * F.blockSide := by
        exact_mod_cast length_bondContour_le π i hL1' hh
      have hc : 0 ≤ Cρ * levelScale F F.depth := mul_nonneg hCρ0 (zero_le_levelScale _)
      calc _ ≤ 5 * (F.blockSide : ℝ) * (Cρ * levelScale F F.depth) := mul_le_mul_of_nonneg_right hlen hc
        _ = 5 * Cρ * (levelScale F F.depth * F.blockSide) := by ring
        _ = 5 * Cρ := by rw [hκL, mul_one]
    have he0 : 0 ≤ 5 * Cρ := by positivity
    have he1 : 5 * Cρ ≤ 1 / 2 := by
      rw [hCρ]
      linarith
    have hpure : ‖averagingWeight F.blockSide • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
        pureComponent ((Dd h π : UnitQuaternion) : ℍ[ℝ])‖ ≤ 5 * Cρ := by
      rw [← pureComponent_weightedContourAverage]
      have e1 : pureComponent (weightedContourAverage F.blockSide Dd) =
          pureComponent (weightedContourAverage F.blockSide Dd - 1) := by
        rw [pureComponent_sub, pureComponent_one, sub_zero]
      rw [e1]
      exact (norm_pureComponent_le _).trans (norm_weightedContourAverage_sub_one_le hodd hDnear)
    have hol : ∀ h ∈ centredCube F.blockSide, ∀ π,
        pathHolonomy (referenceGaugeField S V F.depth) (refineSite y) (bondContour F.blockSide h π (y, i).2) =
        (GaugeMap.frameChange S V y (baseSite (refineSite y + siteOfCoords F.depth 0))) * Dd h π * 1 *
          (GaugeMap.frameChange S V y (baseSite (refineSite y + siteOfCoords F.depth Le)))⁻¹ := by
      intro h hh π
      have := pathHolonomy_bondContour_eq cf hκ hL1' hhull hh π
      rw [mul_one]
      exact this
    obtain ⟨w, hu, hw', h6a, h6b⟩ := contourAverage_polarUnit_factor (X := referenceGaugeField S V F.depth)
      (y, i) hodd he0 he1 hDnear hpure hol
    refine ⟨w, _, _, hu, ?_, fun h hh π => ?_, h6a, h6b, ?_, ?_⟩
    · exact hw'.trans (by linarith)
    · rw [hu, (show pathHolonomy (referenceGaugeField S V F.depth) (refineSite y)
        (bondContour F.blockSide h π i) = _ from hol h hh π)]
      refine (norm_conj_product_sub_one_le _ _ _ _ _).trans (add_le_add (hDnear h hh π) ?_)
      exact hw'
    · obtain ⟨_, _, _, _, _, _, _, hcen⟩ := hloc y hy
      have hz0 : (0 : Lattice4) ∈ {a | chartSite S y F.depth x0 a ∈ patchLocalSites S y} := hhull 0 (h0mem i)
      have e1 : baseSite (refineSite y + siteOfCoords F.depth (0 : Lattice4)) =
          GaugeMap.patchSite S y (chartSite S y F.depth x0 0) :=
        baseSite_chartSite (hes y) (by omega) hw 0
      have e2 : GaugeMap.patchSite S y (chartSite S y F.depth x0 0) = cellCentre 0 y := by
        rw [← e1, siteOfCoords_zero, add_zero, baseSite_refineSite F.depth hjt, baseSite_cell]
      rw [e1]
      exact hcen y hy _ hz0 e2
    · obtain ⟨_, _, _, _, _, _, _, hcen⟩ := hloc y hy
      have hzL : Le ∈ {a | chartSite S y F.depth x0 a ∈ patchLocalSites S y} := hhull Le (hLemem i)
      have e1 : baseSite (refineSite y + siteOfCoords F.depth Le) =
          GaugeMap.patchSite S y (chartSite S y F.depth x0 Le) :=
        baseSite_chartSite (hes y) (by omega) hw Le
      have e2 : GaugeMap.patchSite S y (chartSite S y F.depth x0 Le) = cellCentre 0 (y + unitStep F.top i) := by
        rw [← e1, hLe, baseSite_refineSite_add_blockSide hodd hjt y i, baseSite_cell]
      rw [e1]
      exact hcen _ hy' _ hzL e2
  have smallAt : ∀ {j : ℕ}, j + 1 < F.top → ∀ {y : F.Site (j + 1)} {i : Fin 4},
      (y, i) ∈ innerBonds S (j + 1) →
      ∃ (w g0 g1 Q : UnitQuaternion),
        polarUnit (contourAverage (referenceGaugeField S V j) (y, i)) = g0 * w * Q * g1⁻¹ ∧
        referenceGaugeField S V (j + 1) y i = g0 * Q * g1⁻¹ ∧
        ‖(w : ℍ[ℝ]) - 1‖ ≤ 4 * (Cρ * levelScale F (j + 1) ^ 3) ∧
        (∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
          ‖((pathHolonomy (referenceGaugeField S V j) (refineSite y) (bondContour F.blockSide h π i) *
            (polarUnit (contourAverage (referenceGaugeField S V j) (y, i)))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
              Cρ * levelScale F (j + 1) ^ 2 + 4 * (Cρ * levelScale F (j + 1) ^ 3)) ∧
        0 ≤ 1 - ‖contourAverage (referenceGaugeField S V j) (y, i)‖ ∧
        1 - ‖contourAverage (referenceGaugeField S V j) (y, i)‖ ≤ (Cρ * levelScale F (j + 1) ^ 2) ^ 2 / 2 := by
    intro j hj y i hb
    have hjn : j < F.top := by omega
    obtain ⟨z, x0, R, cf, hhull⟩ := bondChart hjn hb
    have hκ := hlevle hjn
    have hmul := levelScale_mul_blockSide (F := F) hLpos hjn
    have hl1 : levelScale F (j + 1) ≤ 1 := hlev1 hj
    have hl0 := zero_le_levelScale (F := F) (j + 1)
    have hlL : levelScale F (j + 1) ≤ 1 / (F.blockSide : ℝ) := levelScale_le_inv_blockSide hL1' hj
    have hrL : levelScale F j * (3 * F.blockSide) ≤ rr := by
      have e : levelScale F j * (3 * F.blockSide) = 3 * levelScale F (j + 1) := by rw [← hmul]; ring
      rw [e]
      have : 3 * (1 / (F.blockSide : ℝ)) = 3 / (F.blockSide : ℝ) := by ring
      linarith
    have he1 : Cρ * (levelScale F j * F.blockSide) ^ 2 ≤ 1 / 2 := by
      rw [hmul]
      have h2 : levelScale F (j + 1) ^ 2 ≤ 1 := pow_le_one₀ hl0 hl1
      have h3 : Cρ ≤ 1 / 2 := by
        rw [hCρ]
        linarith
      nlinarith
    obtain ⟨w, hu, hw', h5, h6a, h6b⟩ :=
      contourAverage_bounds_below_top cf hκ (y := y) (i := i) rfl hodd hL3 hrL hhull hCρ0 he1
    rw [hmul] at hw' h5 h6b
    refine ⟨w, _, _, _, hu, ?_, hw', h5, h6a, h6b⟩
    refine referenceGaugeField_succ_eq hodd cf (by omega) rfl (hhull 0 (h0mem i)) (hhull _ (hLemem i)) ?_
    have h1 : levelScale F j * supNorm ((F.blockSide : ℤ) • basisVector i - (0 : Lattice4)) ≤
        levelScale F j * F.blockSide :=
      mul_le_mul_of_nonneg_left (hLesup i) (zero_le_levelScale _)
    rw [hmul] at h1
    refine h1.trans ?_
    have : 1 / (F.blockSide : ℝ) ≤ 3 / (F.blockSide : ℝ) := div_le_div_of_nonneg_right (by norm_num) hLr.le
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj z hz b hb hx hx'
    obtain ⟨x, hxp, hxe⟩ := Finset.mem_image.1 hx
    obtain ⟨x', hxp', hxe'⟩ := Finset.mem_image.1 hx'
    obtain ⟨b1, i⟩ := b
    obtain ⟨hb1, hb2⟩ := bondSites hb
    simp only at hxe hxe' ⊢
    obtain ⟨R, cf⟩ := chartAt hj.le z hz b1 x hxe.symm
    have hκ := hlevle hj
    have hNpos := cellSideLength_pos (F := F) hLpos
    have hxe3 : GaugeMap.patchSite S z (chartSite S z j x (basisVector i)) = baseSite (b1 + unitStep j i) := by
      rw [unitStep_eq, baseSite_chartSite (hes z) hj.le hxe.symm]
    have hLjN : (F.blockSide : ℤ) ^ j ≤ GaugeMap.cellSideLength F := by
      unfold GaugeMap.cellSideLength
      exact pow_le_pow_right₀ (by exact_mod_cast hL1') hj.le
    have hxx : chartSite S z j x (basisVector i) = x' := by
      refine patchSite_injOn_small hamb hLpos (hes z) (hxe3.trans hxe'.symm) fun k => ?_
      have h1 := patchDomain_coord_bounds hxp k
      have h2 := patchDomain_coord_bounds hxp' k
      have h3 : |(F.blockSide : ℤ) ^ j * (closedOrthant S z k * basisVector i k)| ≤ GaugeMap.cellSideLength F := by
        rw [abs_mul, abs_mul, abs_closedOrthant (hes z), one_mul, abs_of_nonneg (by positivity)]
        have h4 : |basisVector i k| ≤ 1 := by
          by_cases hk' : k = i
          · subst hk'; simp [basisVector]
          · simp [basisVector, hk']
        have hp : (0 : ℤ) ≤ (F.blockSide : ℤ) ^ j := by positivity
        nlinarith
      have h4 := abs_le.1 h3
      simp only [chartSite]
      rw [abs_lt]
      constructor <;> omega
    have hc0 : chartSite S z j x 0 = x := by
      funext k
      simp [chartSite]
    have h0 : (0 : Lattice4) ∈ {a | chartSite S z j x a ∈ patchLocalSites S z} := by
      show chartSite S z j x 0 ∈ patchLocalSites S z
      rw [hc0]
      refine ⟨patchDomain_coord_bounds hxp, ?_⟩
      rw [hxe]
      exact baseSite_mem_sitesOfCells hodd hj.le hb1
    have h1 : basisVector i ∈ {a | chartSite S z j x a ∈ patchLocalSites S z} := by
      show chartSite S z j x (basisVector i) ∈ patchLocalSites S z
      rw [hxx]
      refine ⟨patchDomain_coord_bounds hxp', ?_⟩
      rw [hxe']
      exact baseSite_mem_sitesOfCells hodd hj.le hb2
    have d : levelScale F j * supNorm (basisVector i - (0 : Lattice4)) ≤ rr := by
      rw [sub_zero, supNorm_basisVector]
      simpa using hκ
    have nb := cf.near_one 0 h0 (basisVector i) h1 d
    have lk := cf.transport_eq 0 h0 (basisVector i) h1 d
    rw [sub_zero, supNorm_basisVector] at nb
    simp only [siteOfCoords_zero, add_zero, ← unitStep_eq] at lk
    have e : referenceInPatchFrame S V z j b1 i = R 0 (basisVector i) := by
      unfold referenceInPatchFrame gaugeTransform
      rw [referenceFieldChain_of_lt hj]
      show (GaugeMap.frameChange S V z (baseSite b1))⁻¹ * referenceGaugeField S V j b1 i *
        ((GaugeMap.frameChange S V z (baseSite (b1 + unitStep j i)))⁻¹)⁻¹ = _
      have e2 : referenceGaugeField S V j b1 i = polarUnit (quaternionPairing S (leadingFrame S V (baseSite b1))
        (leadingFrame S V (baseSite (b1 + unitStep j i)))) := rfl
      rw [e2, lk]
      group
    unfold unitDeviation
    rw [e]
    refine nb.trans ?_
    simp only [Nat.cast_one, mul_one]
    rw [hCρs]
    have hl0 := zero_le_levelScale (F := F) j
    have := hkC 1 (by norm_num)
    rw [one_mul] at this
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hs.le) hl0
  · rintro j hj ⟨x, μ, ν⟩ hp
    obtain ⟨hp1, hp2, hp3⟩ := Finset.mem_filter.1 hp
    have hx : x ∈ sitesOfCells S j := (Finset.mem_product.1 hp1).1
    obtain ⟨z, hz, x0, hw, hx0⟩ := exists_patch_chart hodd hes hj.le hx
    obtain ⟨R, cf⟩ := chartAt hj.le z hz x x0 hw
    have hLjN : (F.blockSide : ℤ) ^ j ≤ GaugeMap.cellSideLength F := by
      unfold GaugeMap.cellSideLength
      exact pow_le_pow_right₀ (by exact_mod_cast hL1') hj.le
    have hNpos := cellSideLength_pos (F := F) hLpos
    have hmem : ∀ a : Lattice4, (∀ k, |a k| ≤ 2) → x + siteOfCoords j a ∈ sitesOfCells S j →
        a ∈ {a | chartSite S z j x0 a ∈ patchLocalSites S z} := by
      intro a ha hsa
      refine mem_chart_of_bounded hodd (hes z) hj.le hw hx0 (fun k => ?_) hsa
      rw [abs_mul, abs_of_nonneg (by positivity)]
      have hp0 : (0 : ℤ) ≤ (F.blockSide : ℤ) ^ j := by positivity
      nlinarith [ha k]
    have habs1 : ∀ (l k : Fin 4), |basisVector l k| ≤ 1 := by
      intro l k
      by_cases hk' : k = l
      · subst hk'; simp [basisVector]
      · simp [basisVector, hk']
    have c0 : x ∈ sitesOfCells S j := hx
    have c1 : x + unitStep j μ ∈ sitesOfCells S j := hp3 (by simp [plaquetteCorners])
    have c2 : x + unitStep j ν ∈ sitesOfCells S j := hp3 (by simp [plaquetteCorners])
    have c3 : x + unitStep j μ + unitStep j ν ∈ sitesOfCells S j := hp3 (by simp [plaquetteCorners])
    have m0 := hmem 0 (fun k => by simp) (by rw [siteOfCoords_zero, add_zero]; exact c0)
    have m1 := hmem (basisVector μ) (fun k => (habs1 μ k).trans (by norm_num)) (by rw [← unitStep_eq]; exact c1)
    have m2 := hmem (basisVector ν) (fun k => (habs1 ν k).trans (by norm_num)) (by rw [← unitStep_eq]; exact c2)
    have m3 := hmem (basisVector μ + basisVector ν) (fun k => by
        have a1 := abs_le.1 (habs1 μ k)
        have a2 := abs_le.1 (habs1 ν k)
        rw [abs_le]
        simp only [Pi.add_apply]
        constructor <;> omega)
      (by rw [siteOfCoords_add, ← unitStep_eq, ← unitStep_eq, ← add_assoc]; exact c3)
    have hcl := plaquetteDefect_referenceGaugeField_le cf (hlevle hj) hCρ0 (ne_of_lt hp2) m0 m1 m2 m3
    rw [referenceFieldChain_of_lt hj]
    refine hcl.trans ?_
    rw [hCρs]
    have hl2 : 0 ≤ levelScale F j ^ 2 := by positivity
    have h2 := hkC 2 (by norm_num)
    calc 2 * (k * s) * levelScale F j ^ 2 = (2 * k) * s * levelScale F j ^ 2 := by ring
      _ ≤ Cf * s * levelScale F j ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hs.le) hl2
  · rintro j hj ⟨y, i⟩ hb
    have hjn : j < F.top := by omega
    obtain ⟨w, g0, g1, Q, hu, hup, hw', _, _, _⟩ := smallAt hj hb
    unfold unitDeviation referenceDefect
    rw [referenceFieldChain_of_lt hj, referenceFieldChain_of_lt hjn]
    show ‖((referenceGaugeField S V (j + 1) y i *
      (polarUnit (contourAverage (referenceGaugeField S V j) (y, i)))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ _
    rw [hu, hup, norm_conj_quotient_sub_one_eq]
    refine hw'.trans ?_
    rw [hCρs]
    have hl3 : 0 ≤ levelScale F (j + 1) ^ 3 := pow_nonneg (zero_le_levelScale _) 3
    have h2 := hkC 4 (by norm_num)
    calc 4 * (k * s * levelScale F (j + 1) ^ 3) = (4 * k) * s * levelScale F (j + 1) ^ 3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hs.le) hl3
  · rintro ⟨y, i⟩ hb
    obtain ⟨w, g0, g1, hu, hw', _, _, _, e0, e1⟩ := topAt hb
    obtain ⟨hy0, hy0'⟩ := bondSites hb
    have hy : y ∈ S := mem_sitesOfCells_top.1 hy0
    have hy' : y + unitStep F.top i ∈ S := mem_sitesOfCells_top.1 hy0'
    obtain ⟨_, hbond⟩ := hT F m S hodd hamb hm hreg s V hs.le hcold y hy
    have hb2 := hbond i hy'
    unfold unitDeviation referenceDefect
    have e2 : referenceFieldChain S V (F.depth + 1) = V := referenceFieldChain_top
    rw [e2, referenceFieldChain_of_lt (Nat.lt_succ_self F.depth)]
    show ‖((V y i * (polarUnit (contourAverage (referenceGaugeField S V F.depth) (y, i)))⁻¹ :
      UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ _
    rw [hu]
    refine (norm_mul_inv_factor_sub_one_le _ _ _ _).trans ?_
    rw [e0, e1]
    have hfin : C2 * s + 4 * (5 * (k * s)) ≤ Cf * s := by
      have : C2 + 20 * k ≤ Cf := by
        have h2 : 0 ≤ 13 * k ^ 2 := by positivity
        rw [hCf]
        linarith
      nlinarith
    rw [e0] at *
    rw [hCρs] at hw'
    linarith
  · rintro j hj ⟨y, i⟩ hb h hh π
    rw [referenceFieldChain_of_lt hj]
    unfold unitDeviation
    rcases Nat.lt_or_ge (j + 1) F.top with hj1 | hj1
    · obtain ⟨_, _, _, _, _, _, _, h5, _, _⟩ := smallAt hj1 hb
      refine (h5 h hh π).trans ?_
      rw [hCρs]
      have hl1 : levelScale F (j + 1) ≤ 1 := hlev1 hj1
      have hl0 := zero_le_levelScale (F := F) (j + 1)
      have h3 : levelScale F (j + 1) ^ 3 ≤ levelScale F (j + 1) ^ 2 := by
        rw [pow_succ]
        nlinarith [sq_nonneg (levelScale F (j + 1))]
      have hks : 0 ≤ k * s := by positivity
      have h2 := hkC 5 (by norm_num)
      have hl2 : 0 ≤ levelScale F (j + 1) ^ 2 := by positivity
      calc _ ≤ k * s * levelScale F (j + 1) ^ 2 + 4 * (k * s * levelScale F (j + 1) ^ 2) := by
            have := mul_le_mul_of_nonneg_left h3 hks
            linarith
        _ = (5 * k) * s * levelScale F (j + 1) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hs.le) hl2
    · have hnt : F.top = F.depth + 1 := rfl
      obtain rfl : j = F.depth := by omega
      obtain ⟨_, _, _, _, _, h5, _, _, _, _⟩ := topAt hb
      refine (h5 h hh π).trans ?_
      have e : levelScale F (F.depth + 1) = 1 := levelScale_top_eq_one
      rw [e, hCρs]
      have h2 := hkC 25 (by norm_num)
      have h3 := mul_le_mul_of_nonneg_right h2 hs.le
      calc 5 * (k * s) + 4 * (5 * (k * s)) = 25 * k * s := by ring
        _ ≤ Cf * s := h3
        _ = _ := by ring
  · rintro j hj ⟨y, i⟩ hb
    rw [referenceFieldChain_of_lt hj]
    rcases Nat.lt_or_ge (j + 1) F.top with hj1 | hj1
    · obtain ⟨_, _, _, _, _, _, _, _, h6a, h6b⟩ := smallAt hj1 hb
      refine ⟨h6a, h6b.trans ?_⟩
      rw [hCρs]
      have hl4 : 0 ≤ levelScale F (j + 1) ^ 4 := pow_nonneg (zero_le_levelScale _) 4
      have hcf : k ^ 2 / 2 ≤ Cf := by
        have h1 : 0 ≤ k ^ 2 := by positivity
        rw [hCf]
        linarith [hk0.le, hC2.le]
      calc (k * s * levelScale F (j + 1) ^ 2) ^ 2 / 2 = (k ^ 2 / 2) * s ^ 2 * levelScale F (j + 1) ^ 4 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcf (by positivity)) hl4
    · have hnt : F.top = F.depth + 1 := rfl
      obtain rfl : j = F.depth := by omega
      obtain ⟨_, _, _, _, _, _, h6a, h6b, _, _⟩ := topAt hb
      refine ⟨h6a, h6b.trans ?_⟩
      have e : levelScale F (F.depth + 1) = 1 := levelScale_top_eq_one
      rw [e, hCρs]
      have hcf : 25 * k ^ 2 / 2 ≤ Cf := by
        have h1 : 0 ≤ k ^ 2 := by positivity
        rw [hCf]
        linarith [hk0.le, hC2.le]
      have h3 := mul_le_mul_of_nonneg_right hcf (sq_nonneg s)
      calc (5 * (k * s)) ^ 2 / 2 = 25 * k ^ 2 / 2 * s ^ 2 := by ring
        _ ≤ Cf * s ^ 2 := h3
        _ = _ := by ring
end YangMills.Construction.ReferenceBounds
end
