import YangMills.Construction.ColdChainAtEveryLevel.GaugeCovarianceOfAContour
import YangMills.Construction.ColdChainAtEveryLevel.LeastValuesOfAChain
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
namespace GaugedChains
variable {F : BlockFrame}
theorem norm_unitQuaternion_coe (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem quaternion_re_mul_comm (a b : ℍ[ℝ]) : (a * b).re = (b * a).re := by
  simp only [Quaternion.re_mul]
  ring
theorem unitQuaternion_coe_inv_mul (g : UnitQuaternion) :
    ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_inv_mul_coe <;> assumption
theorem gaugedBlockFit_gaugeTransform {j : ℕ} (γ : F.Site (j + 1) → UnitQuaternion)
    (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion) (X' : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) :
    gaugedBlockFit X (fun y => γ y * k y) (gaugeTransform γ X') c = gaugedBlockFit X k X' c := by
  unfold gaugedBlockFit
  set g0 := γ c.1
  set g1 := γ (c.1 + unitStep (j + 1) c.2)
  have hmean : gaugedContourAverage X (fun y => γ y * k y) c =
      (g0 : ℍ[ℝ]) * gaugedContourAverage X k c * ((g1⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    simp only [gaugedContourAverage, mul_inv_rev, Submonoid.coe_mul]
    simp only [mul_assoc]
    rfl
  have hinv : (gaugeTransform γ X' c.1 c.2)⁻¹ = g1 * (X' c.1 c.2)⁻¹ * g0⁻¹ := by
    simp only [gaugeTransform, mul_inv_rev, inv_inv]
    exact (mul_assoc _ _ _).symm
  rw [hmean, hinv]
  set q := gaugedContourAverage X k c
  have hnorm : ‖(g0 : ℍ[ℝ]) * q * ((g1⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖q‖ := by
    rw [norm_mul, norm_mul, norm_unitQuaternion_coe, norm_unitQuaternion_coe, one_mul, mul_one]
  rw [hnorm]
  congr 1
  simp only [Submonoid.coe_mul]
  calc ((g0 : ℍ[ℝ]) * q * ((g1⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
        ((g1 : ℍ[ℝ]) * (((X' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          ((g0⁻¹ : UnitQuaternion) : ℍ[ℝ]))).re =
      ((g0 : ℍ[ℝ]) * (q * (((g1⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (g1 : ℍ[ℝ])) *
        (((X' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
        ((g0⁻¹ : UnitQuaternion) : ℍ[ℝ]))).re := by
        simp only [mul_assoc]
    _ = ((q * (((X' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          ((g0⁻¹ : UnitQuaternion) : ℍ[ℝ])) * (g0 : ℍ[ℝ])).re := by
        rw [unitQuaternion_coe_inv_mul, mul_one, quaternion_re_mul_comm]
    _ = _ := by
        rw [mul_assoc, unitQuaternion_coe_inv_mul, mul_one]
def partialGaugedAction (a : ℝ) (S : Finset F.Cell) (X : F.FieldChain) (k : F.SiteGauge)
    (j : ℕ) : ℝ :=
  wilsonAction S (X 0) + a * ∑ i ∈ Finset.range j, ∑ c ∈ innerBonds S (i + 1),
    gaugedBlockFit (X i) (k (i + 1)) (X (i + 1)) c
theorem wilsonAction_gaugeTransform (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide)
    (S : Finset F.Cell) (γ : F.Site 0 → UnitQuaternion) (U : F.GaugeField 0) :
    wilsonAction S (gaugeTransform γ U) = wilsonAction S U := by
  unfold wilsonAction
  apply Finset.sum_congr rfl
  intro p _
  obtain ⟨-, -, h, -⟩ := hG F 0 (Nat.succ_pos _) hL
  rw [h γ U p]
  congr 1
  simp only [Submonoid.coe_mul]
  rw [mul_assoc, quaternion_re_mul_comm, mul_assoc, unitQuaternion_coe_inv_mul, mul_one]
theorem blockFit_gaugeTransform_eq (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide)
    {j : ℕ} (hj : j < F.top) (γ : F.Site j → UnitQuaternion)
    (k : F.Site (j + 1) → UnitQuaternion) (hγ : ∀ y, γ (refineSite y) = k y)
    (X : F.GaugeField j) (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    blockFit (gaugeTransform γ X) X' c = gaugedBlockFit X k X' c := by
  obtain ⟨-, h, -, -⟩ := hG F j hj hL
  unfold blockFit gaugedBlockFit gaugedContourAverage
  rw [h γ X c, hγ, hγ]
theorem minimalAction_le_partialGaugedAction (hG : gaugeCovarianceStatement)
    (hV : minimalChainExistenceStatement) (a : ℝ) (ha : 0 ≤ a) (hL : 0 < F.blockSide)
    (S : Finset F.Cell) :
    ∀ j, j ≤ F.top → ∀ (X : F.FieldChain) (k : F.SiteGauge),
      minimalAction a S j (X j) ≤ partialGaugedAction a S X k j := by
  classical
  intro j
  induction j with
  | zero =>
    intro _ X k
    simp [partialGaugedAction, minimalAction]
  | succ j ih =>
    intro hj X k
    have hinj := (hG F j (by omega) hL).1
    set γ : F.Site j → UnitQuaternion :=
      fun z => if h : ∃ y, refineSite y = z then k (j + 1) h.choose else 1 with hγ
    have hγrefine : ∀ y, γ (refineSite y) = k (j + 1) y := by
      intro y
      have hex : ∃ y', refineSite y' = refineSite y := ⟨y, rfl⟩
      simp only [hγ, dif_pos hex]
      rw [hinj hex.choose_spec]
    set W := gaugeTransform γ (X j) with hW
    obtain ⟨-, -, hex, -⟩ := hV F a S ha
    obtain ⟨W0, hW0, hmin⟩ := hex j (X (j + 1))
    set X2 : F.FieldChain := Function.update X j W with hX2
    set k2 : F.SiteGauge := Function.update k j (fun y => γ y * k j y) with hk2
    have hlow := ih (by omega) X2 k2
    have hX2j : X2 j = W := by simp [hX2]
    rw [hX2j] at hlow
    have hfit : ∑ c ∈ innerBonds S (j + 1), blockFit W (X (j + 1)) c =
        ∑ c ∈ innerBonds S (j + 1), gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c :=
      Finset.sum_congr rfl fun c _ =>
        blockFit_gaugeTransform_eq hG hL (by omega) γ _ hγrefine _ _ c
    have hpart : partialGaugedAction a S X2 k2 j = partialGaugedAction a S X k j := by
      cases j with
      | zero =>
        simp only [partialGaugedAction, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero,
          hX2j]
        exact wilsonAction_gaugeTransform hG hL S γ (X 0)
      | succ i =>
        have hlo : ∀ m, m ≤ i → X2 m = X m := fun m hm => Function.update_of_ne (by omega) _ _
        have hkl : ∀ m, m ≤ i → k2 m = k m := fun m hm => Function.update_of_ne (by omega) _ _
        simp only [partialGaugedAction]
        rw [hlo 0 (Nat.zero_le _), Finset.sum_range_succ, Finset.sum_range_succ]
        have hlower : ∑ m ∈ Finset.range i, ∑ c ∈ innerBonds S (m + 1),
            gaugedBlockFit (X2 m) (k2 (m + 1)) (X2 (m + 1)) c =
            ∑ m ∈ Finset.range i, ∑ c ∈ innerBonds S (m + 1),
              gaugedBlockFit (X m) (k (m + 1)) (X (m + 1)) c := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.mem_range] at hm
          rw [hlo m (by omega), hlo (m + 1) (by omega), hkl (m + 1) (by omega)]
        have hlast : ∑ c ∈ innerBonds S (i + 1), gaugedBlockFit (X2 i) (k2 (i + 1)) (X2 (i + 1)) c =
            ∑ c ∈ innerBonds S (i + 1), gaugedBlockFit (X i) (k (i + 1)) (X (i + 1)) c := by
          rw [hlo i le_rfl, hX2j]
          have hk : k2 (i + 1) = fun y => γ y * k (i + 1) y := by simp [hk2]
          rw [hk]
          exact Finset.sum_congr rfl fun c _ => gaugedBlockFit_gaugeTransform γ _ _ _ c
        rw [hlower, hlast]
    calc minimalAction a S (j + 1) (X (j + 1)) = blockEnergy a S j W0 (X (j + 1)) := hW0.symm
      _ ≤ blockEnergy a S j W (X (j + 1)) := hmin W
      _ = minimalAction a S j W + a * ∑ c ∈ innerBonds S (j + 1), blockFit W (X (j + 1)) c := rfl
      _ ≤ partialGaugedAction a S X k j + a * ∑ c ∈ innerBonds S (j + 1),
            gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c := by
          rw [hfit, ← hpart]
          gcongr
      _ = _ := by
          simp only [partialGaugedAction]
          rw [Finset.sum_range_succ]
          ring
end GaugedChains
theorem gaugedChainLowerBound (hG : gaugeCovarianceStatement)
    (hV : minimalChainExistenceStatement) : gaugedChainLowerBoundStatement := by
  intro F a S ha hL
  refine ⟨fun X k =>
    GaugedChains.minimalAction_le_partialGaugedAction hG hV a ha hL S F.top le_rfl X k, ?_⟩
  intro X
  simp only [gaugedChainAction, chainAction]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro c _
  simp [gaugedBlockFit, gaugedContourAverage, blockFit]
end BlockAverages
end YangMills.Construction
end
