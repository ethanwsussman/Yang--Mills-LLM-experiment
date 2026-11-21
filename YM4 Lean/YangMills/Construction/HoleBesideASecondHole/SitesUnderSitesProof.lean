import YangMills.Construction.HoleBesideASecondHole.DistancesBlocksAndLumpsProof
import YangMills.Construction.HoleBesideASecondHole.SitesUnderSites
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LumpContours
open BlockAverages
namespace NestedSites
variable {F : BlockFrame}
theorem siteCoords_cast {j : ℕ} (x : F.Site j) (i : Fin 4) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.siteCoords_cast <;> assumption
theorem period_eq_pow_mul {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) (k : Fin 4) :
    F.period i k = F.blockSide ^ (j - i) * F.period j k := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.period_eq_pow_mul <;> assumption
theorem mem_centredCube_iff {M : ℕ} {o : Fin 4 → ℤ} :
    o ∈ centredCube M ↔ ∀ m, |o m| ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.mem_centredCube_iff <;> assumption
theorem mem_sitesBelow_trans {i j m : ℕ} (hij : i ≤ j) (hjm : j ≤ m) (hm : m ≤ F.top) (hL : Odd F.blockSide)
    (x : F.Site m) {w : F.Site j} (hw : w ∈ sitesBelow j x) {z : F.Site i} (hz : z ∈ sitesBelow i w) :
    z ∈ sitesBelow i x := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.sitesBelow_trans <;> assumption
theorem two_mul_half_add_one {L : ℕ} (hL : Odd L) : 2 * (((L : ℤ) - 1) / 2) + 1 = L := by apply _root_.YangMills.Construction.LumpContours.two_mul_half_pred_add_one_of_odd <;> assumption
theorem sitesBelow_unique (hL : Odd F.blockSide) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.top) {z : F.Site i}
    {x x' : F.Site j} (h : z ∈ sitesBelow i x) (h' : z ∈ sitesBelow i x') : x = x' := by
  unfold sitesBelow at h h'
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
  obtain ⟨b, hb, hab⟩ := Finset.mem_image.1 h'
  have hM : Odd (F.blockSide ^ (j - i)) := hL.pow
  have hMp : (0 : ℤ) < ((F.blockSide ^ (j - i) : ℕ) : ℤ) := by exact_mod_cast hM.pos
  have hM2 := two_mul_half_add_one hM
  have ha' := mem_centredCube_iff.1 ha
  have hb' := mem_centredCube_iff.1 hb
  funext k
  have e1 := congrFun hab k
  simp only [siteOfCoords] at e1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at e1
  obtain ⟨q, hq⟩ := e1
  rw [period_eq_pow_mul hij hj k] at hq
  push_cast at hq hMp hM2 ha' hb'
  set M : ℤ := (F.blockSide : ℤ) ^ (j - i) with hMdef
  have hai := ha' k
  have hbi := hb' k
  rw [abs_le] at hai hbi
  have d1 : M ∣ a k - b k := by
    refine ⟨siteCoords x' k - siteCoords x k + (F.period j k : ℤ) * q, ?_⟩
    linear_combination hq
  have d2 : a k - b k = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd d1 ?_
    rw [abs_lt]
    constructor <;> omega
  have d3 : M * (siteCoords x' k - siteCoords x k + (F.period j k : ℤ) * q) = 0 := by
    linear_combination d2 - hq
  have d4 : siteCoords x' k - siteCoords x k + (F.period j k : ℤ) * q = 0 :=
    (mul_eq_zero.1 d3).resolve_left hMp.ne'
  rw [← siteCoords_cast x k, ← siteCoords_cast x' k, ZMod.intCast_eq_intCast_iff_dvd_sub]
  exact ⟨-q, by linear_combination d4⟩
theorem unitQuaternion_norm (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem re_le_norm (q : ℍ[ℝ]) : q.re ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.quaternion_re_le_norm <;> assumption
end NestedSites
open NestedSites in
theorem nestedSiteFacts_holds : NestedSiteFacts := by
  refine ⟨fun F hL _ => ⟨fun i j m hij hjm hm x w z hw hz => mem_sitesBelow_trans hij hjm hm hL x hw hz,
    fun i j hij hj x x' z h h' => sitesBelow_unique hL hij hj h h', fun U p => ?_⟩, fun q g => ?_⟩
  · unfold plaquetteEnergy
    have := re_le_norm ((plaquetteHolonomy U p : UnitQuaternion) : ℍ[ℝ])
    rw [unitQuaternion_norm] at this
    linarith
  · have := re_le_norm (q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]))
    rw [norm_mul, unitQuaternion_norm, mul_one] at this
    linarith
end YangMills.Construction.LumpContours
end
