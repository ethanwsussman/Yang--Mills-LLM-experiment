import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.FramedChainsOverATopProof
import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace GaugeCovariance
variable {F : BlockFrame}
def pathDisplacement (j : ℕ) (l : List PathStep) : F.Site j := (l.map (stepDisplacement j)).sum
theorem linkValue_gaugeTransform {j : ℕ} (g : F.Site j → UnitQuaternion) (A : F.GaugeField j)
    (x : F.Site j) (e : PathStep) :
    linkValue (gaugeTransform g A) x e = g x * linkValue A x e * (g (x + stepDisplacement j e))⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_gaugeTransform <;> assumption
theorem pathHolonomy_gaugeTransform {j : ℕ} (g : F.Site j → UnitQuaternion) (A : F.GaugeField j)
    (l : List PathStep) :
    ∀ x : F.Site j, pathHolonomy (gaugeTransform g A) x l =
      g x * pathHolonomy A x l * (g (x + pathDisplacement j l))⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_gaugeTransform <;> assumption
theorem pathDisplacement_append (j : ℕ) (l l' : List PathStep) :
    pathDisplacement (F := F) j (l ++ l') = pathDisplacement j l + pathDisplacement j l' := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_append <;> assumption
theorem pathDisplacement_reversePath (j : ℕ) (l : List PathStep) :
    pathDisplacement (F := F) j (reversePath l) = - pathDisplacement j l := by apply _root_.YangMills.Construction.GaugeFixing.pathDisplacement_reversePath <;> assumption
theorem pathDisplacement_replicate (j L : ℕ) (μ : Fin 4) :
    pathDisplacement (F := F) j (List.replicate L (μ, true)) = L • unitStep j μ := by
  simp [pathDisplacement, stepDisplacement, List.map_replicate, List.sum_replicate]
theorem pathDisplacement_bondContour (j L : ℕ) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (μ : Fin 4) :
    pathDisplacement (F := F) j (bondContour L h π μ) = L • unitStep j μ := by
  unfold bondContour
  rw [pathDisplacement_append, pathDisplacement_append, pathDisplacement_reversePath,
    pathDisplacement_replicate]
  abel
theorem period_succ (j : ℕ) (hj : j < F.top) (μ : Fin 4) :
    F.period j μ = F.blockSide * F.period (j + 1) μ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.period_succ <;> assumption
theorem siteCoords_cast {j : ℕ} (x : F.Site j) (μ : Fin 4) :
    ((siteCoords x μ : ℤ) : ZMod (F.period j μ)) = x μ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.siteCoords_cast <;> assumption
theorem refineSite_add_unitStep (j : ℕ) (hj : j < F.top) (y : F.Site (j + 1)) (μ : Fin 4) :
    refineSite (y + unitStep (j + 1) μ) = refineSite y + F.blockSide • unitStep j μ := by
  funext ν
  simp only [refineSite, siteOfCoords, Pi.add_apply, Pi.smul_apply, unitStep]
  set a := siteCoords (y + siteOfCoords (j + 1) (Pi.single μ 1)) ν with ha
  set b := siteCoords y ν with hb
  set d : ℤ := (Pi.single μ 1 : Fin 4 → ℤ) ν with hd
  have h1 : ((a : ℤ) : ZMod (F.period (j + 1) ν)) = ((b + d : ℤ) : ZMod (F.period (j + 1) ν)) := by
    rw [ha, siteCoords_cast, Int.cast_add, hb, siteCoords_cast]
    simp [siteOfCoords, hd]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  have h2 : ((F.blockSide * a : ℤ) : ZMod (F.period j ν)) =
      ((F.blockSide * (b + d) : ℤ) : ZMod (F.period j ν)) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub, period_succ j hj ν]
    push_cast
    rw [← mul_sub]
    exact mul_dvd_mul_left _ h1
  rw [h2]
  push_cast
  rw [mul_add, nsmul_eq_mul]
theorem refineSite_injective (j : ℕ) (hj : j < F.top) (hL : 0 < F.blockSide) :
    Function.Injective (refineSite (F := F) (j := j)) := by
  intro y y' h
  funext ν
  have h1 := congrFun h ν
  simp only [refineSite, siteOfCoords] at h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, period_succ j hj ν] at h1
  push_cast at h1
  rw [← mul_sub] at h1
  have hL' : ((F.blockSide : ℤ)) ≠ 0 := by exact_mod_cast hL.ne'
  have h2 := (mul_dvd_mul_iff_left hL').1 h1
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, siteCoords_cast, siteCoords_cast] at h2
  exact h2
theorem contourAverage_gaugeTransform (j : ℕ) (hj : j < F.top) (g : F.Site j → UnitQuaternion)
    (A : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) :
    contourAverage (gaugeTransform g A) c = (g (refineSite c.1) : ℍ[ℝ]) * contourAverage A c *
      (((g (refineSite (c.1 + unitStep (j + 1) c.2)))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  unfold contourAverage
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro π _
  rw [pathHolonomy_gaugeTransform, pathDisplacement_bondContour, ← refineSite_add_unitStep j hj]
  simp only [Submonoid.coe_mul]
theorem plaquetteHolonomy_gaugeTransform (j : ℕ) (g : F.Site j → UnitQuaternion) (A : F.GaugeField j)
    (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteHolonomy (gaugeTransform g A) p = g p.1 * plaquetteHolonomy A p * (g p.1)⁻¹ := by
  unfold plaquetteHolonomy
  rw [pathHolonomy_gaugeTransform]
  have : pathDisplacement (F := F) j
      [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] = 0 := by
    simp [pathDisplacement, stepDisplacement]
  rw [this, add_zero]
theorem norm_coe_unitQuaternion (u : UnitQuaternion) : ‖(u : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem quaternion_re_mul_comm (a b : ℍ[ℝ]) : (a * b).re = (b * a).re := by apply _root_.YangMills.Construction.BlockAverages.GaugedChains.quaternion_re_mul_comm <;> assumption
theorem coe_inv_mul_coe (u : UnitQuaternion) : ((u⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (u : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_inv_mul_coe <;> assumption
theorem blockFit_gaugeTransform (j : ℕ) (hj : j < F.top) (g : F.Site j → UnitQuaternion)
    (g' : F.Site (j + 1) → UnitQuaternion) (A : F.GaugeField j) (A' : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4)
    (h1 : g (refineSite c.1) = g' c.1)
    (h2 : g (refineSite (c.1 + unitStep (j + 1) c.2)) = g' (c.1 + unitStep (j + 1) c.2)) :
    blockFit (gaugeTransform g A) (gaugeTransform g' A') c = blockFit A A' c := by
  unfold blockFit
  rw [contourAverage_gaugeTransform j hj, h1, h2]
  set u0 := g' c.1
  set u1 := g' (c.1 + unitStep (j + 1) c.2)
  set q := contourAverage A c
  have hn : ‖(u0 : ℍ[ℝ]) * q * ((u1⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖q‖ := by
    rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, mul_one]
  have hinv : (gaugeTransform g' A' c.1 c.2)⁻¹ = u1 * (A' c.1 c.2)⁻¹ * u0⁻¹ := by
    simp only [gaugeTransform, mul_inv_rev, inv_inv]
    exact (mul_assoc _ _ _).symm
  rw [hn, hinv]
  congr 1
  simp only [Submonoid.coe_mul]
  calc ((u0 : ℍ[ℝ]) * q * ((u1⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
        ((u1 : ℍ[ℝ]) * (((A' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          ((u0⁻¹ : UnitQuaternion) : ℍ[ℝ]))).re =
      ((u0 : ℍ[ℝ]) * (q * (((u1⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (u1 : ℍ[ℝ])) *
        (((A' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((u0⁻¹ : UnitQuaternion) : ℍ[ℝ]))).re := by
        simp only [mul_assoc]
    _ = ((q * (((A' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((u0⁻¹ : UnitQuaternion) : ℍ[ℝ])) *
          (u0 : ℍ[ℝ])).re := by
        rw [coe_inv_mul_coe, mul_one, quaternion_re_mul_comm]
    _ = _ := by
        rw [mul_assoc, coe_inv_mul_coe, mul_one]
end GaugeCovariance
theorem gaugeCovarianceStatement_holds : gaugeCovarianceStatement := by
  intro F j hj hL
  exact ⟨GaugeCovariance.refineSite_injective j hj hL,
    fun g A c => GaugeCovariance.contourAverage_gaugeTransform j hj g A c,
    fun g A p => GaugeCovariance.plaquetteHolonomy_gaugeTransform j g A p,
    fun g g' A A' c h1 h2 => GaugeCovariance.blockFit_gaugeTransform j hj g g' A A' c h1 h2⟩
end YangMills.Construction.BlockAverages
end
