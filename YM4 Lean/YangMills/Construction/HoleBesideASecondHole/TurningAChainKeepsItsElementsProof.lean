import YangMills.Construction.ColdChainAtEveryLevel.CriticalForAllVariationsProof
import YangMills.Construction.HoleBesideASecondHole.LinesAndStripsOfALatticeField
import YangMills.Construction.HoleBesideASecondHole.SitesOfBlocksAndCells
import YangMills.Construction.HoleBesideASecondHole.TurningAChainKeepsItsElements
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ChainGauges
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
open YangMills.Construction.LatticeGauge YangMills.Construction.BlockSites
variable {F : BlockFrame}
theorem period_eq_blockSide_mul_succ (j : ℕ) (hj : j < F.top) (i : Fin 4) :
    F.period j i = F.blockSide * F.period (j + 1) i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.period_succ <;> assumption
theorem period_eq_pow_mul_depth (i : ℕ) (hi : i ≤ F.depth) (l : Fin 4) :
    F.period i l = F.blockSide ^ (F.depth - i) * F.period F.depth l := by
  simp only [BlockFrame.period]
  have : F.top - i = (F.depth - i) + (F.top - F.depth) := by
    simp only [BlockFrame.top]
    omega
  rw [this, pow_add]
  ring
theorem pointAtLevel_injective (hL : 0 < F.blockSide) (i : ℕ) (hi : i ≤ F.depth) {x x' : F.Site F.depth}
    (h : (pointAtLevel i x : F.Site i) = pointAtLevel i x') : x = x' := by
  funext l
  have h1 := siteOfCoords_eq_iff.mp h l
  rw [period_eq_pow_mul_depth i hi] at h1
  push_cast at h1
  rw [← mul_sub] at h1
  have hne : ((F.blockSide : ℤ) ^ (F.depth - i)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hL.ne')
  have h2 := (mul_dvd_mul_iff_left hne).mp h1
  have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr h2
  rwa [intCast_siteCoords, intCast_siteCoords] at h3
theorem extendGauge_pointAtLevel (hL : 0 < F.blockSide) (γ : F.Site F.depth → UnitQuaternion) (i : ℕ)
    (hi : i ≤ F.depth) (x : F.Site F.depth) :
    extendGauge γ i (pointAtLevel i x) = γ x := by
  have h : ∃ x', (pointAtLevel i x' : F.Site i) = pointAtLevel i x := ⟨x, rfl⟩
  rw [extendGauge, dif_pos h, pointAtLevel_injective hL i hi h.choose_spec]
theorem pointAtLevel_depth (x : F.Site F.depth) : (pointAtLevel F.depth x : F.Site F.depth) = x := by
  have : (pointAtLevel F.depth x : F.Site F.depth) = siteOfCoords F.depth (siteCoords x) := by
    simp [pointAtLevel]
  rw [this, _root_.YangMills.Construction.BlockSites.siteOfCoords_siteCoords]
theorem extendGauge_depth (hL : 0 < F.blockSide) (γ : F.Site F.depth → UnitQuaternion) :
    extendGauge γ F.depth = γ := by
  funext z
  have := extendGauge_pointAtLevel hL γ F.depth le_rfl z
  rwa [pointAtLevel_depth] at this
theorem refineSite_pointAtLevel (i : ℕ) (hi : i < F.depth) (x : F.Site F.depth) :
    (_root_.YangMills.Construction.BlockAverages.refineSite (pointAtLevel (i + 1) x : F.Site (i + 1)) : F.Site i) = pointAtLevel i x := by
  refine siteOfCoords_eq_iff.mpr fun l => ?_
  have hn : i < F.top := by
    simp only [BlockFrame.top]
    omega
  have h1 : ((((F.blockSide : ℤ) ^ (F.depth - (i + 1)) * siteCoords x l : ℤ)) : ZMod (F.period (i + 1) l)) =
      ((siteCoords (pointAtLevel (i + 1) x : F.Site (i + 1)) l : ℤ) : ZMod (F.period (i + 1) l)) := by
    rw [intCast_siteCoords]
    rfl
  have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
  have e : (F.blockSide : ℤ) ^ (F.depth - i) * siteCoords x l -
        (F.blockSide : ℤ) * siteCoords (pointAtLevel (i + 1) x : F.Site (i + 1)) l =
      -((F.blockSide : ℤ) * (siteCoords (pointAtLevel (i + 1) x : F.Site (i + 1)) l -
        (F.blockSide : ℤ) ^ (F.depth - (i + 1)) * siteCoords x l)) := by
    have : F.depth - i = (F.depth - (i + 1)) + 1 := by omega
    rw [this, pow_succ]
    ring
  rw [e, period_eq_blockSide_mul_succ i hn l]
  push_cast
  exact (dvd_neg).mpr (mul_dvd_mul_left _ h2)
theorem pointAtLevel_succ_of_refineSite (hL : 0 < F.blockSide) (i : ℕ) (hi : i < F.depth)
    (z : F.Site (i + 1)) (x : F.Site F.depth)
    (h : (pointAtLevel i x : F.Site i) = _root_.YangMills.Construction.BlockAverages.refineSite z) : (pointAtLevel (i + 1) x : F.Site (i + 1)) = z := by
  have hn : i < F.top := by
    simp only [BlockFrame.top]
    omega
  rw [← _root_.YangMills.Construction.BlockSites.siteOfCoords_siteCoords z]
  refine siteOfCoords_eq_iff.mpr fun l => ?_
  have h1 := siteOfCoords_eq_iff.mp h l
  rw [period_eq_blockSide_mul_succ i hn l] at h1
  push_cast at h1
  have e : (F.blockSide : ℤ) * siteCoords z l - (F.blockSide : ℤ) ^ (F.depth - i) * siteCoords x l =
      (F.blockSide : ℤ) * (siteCoords z l - (F.blockSide : ℤ) ^ (F.depth - (i + 1)) * siteCoords x l) := by
    have : F.depth - i = (F.depth - (i + 1)) + 1 := by omega
    rw [this, pow_succ]
    ring
  rw [e] at h1
  exact (mul_dvd_mul_iff_left (by exact_mod_cast hL.ne')).mp h1
theorem extendGauge_refineSite (hL : 0 < F.blockSide) (γ : F.Site F.depth → UnitQuaternion) (i : ℕ)
    (hi : i < F.depth) (z : F.Site (i + 1)) :
    extendGauge γ i (_root_.YangMills.Construction.BlockAverages.refineSite z) = extendGauge γ (i + 1) z := by
  by_cases h : ∃ x, (pointAtLevel (i + 1) x : F.Site (i + 1)) = z
  · obtain ⟨x, rfl⟩ := h
    rw [refineSite_pointAtLevel i hi, extendGauge_pointAtLevel hL γ i hi.le,
      extendGauge_pointAtLevel hL γ (i + 1) hi]
  · have h' : ¬ ∃ x, (pointAtLevel i x : F.Site i) = _root_.YangMills.Construction.BlockAverages.refineSite z := fun ⟨x, hx⟩ =>
      h ⟨x, pointAtLevel_succ_of_refineSite hL i hi z x hx⟩
    rw [extendGauge, extendGauge, dif_neg h, dif_neg h']
theorem re_conj_unitQuaternion (a : UnitQuaternion) (q : ℍ[ℝ]) :
    ((a : ℍ[ℝ]) * q * ((a⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = q.re := by apply _root_.YangMills.Construction.GaugedCriticality.re_conj_unit <;> assumption
theorem quatDist_conj_one (a b : UnitQuaternion) : quatDist (a * b * a⁻¹) 1 = quatDist b 1 := by
  rw [quatDist_mul_inv_one (a * b) a]
  have := quatDist_mul_left a b 1
  rwa [mul_one] at this
theorem gaugeChainPreservesEnergy_of_gaugeCovariance (hg : gaugeCovarianceStatement) :
    GaugeChainPreservesEnergy := by
  intro F γ U hL hs
  have hn : F.depth < F.top := by simp [BlockFrame.top]
  have top : gaugeChain γ U F.depth = _root_.YangMills.Construction.BlockAverages.gaugeTransform γ (U F.depth) := by
    simp only [gaugeChain, le_refl, if_true]
    rw [extendGauge_depth hL]
  refine ⟨top, fun p => ?_, fun a Y => ?_⟩
  · rw [top]
    have h1 := (hg F F.depth hn hL).2.2.1 γ (U F.depth) p
    have e1 : plaquetteDefect (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ (U F.depth)) p =
        quatDist (plaquetteHolonomy (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ (U F.depth)) p) 1 := rfl
    have e2 : plaquetteDefect (U F.depth) p = quatDist (plaquetteHolonomy (U F.depth) p) 1 := rfl
    rw [e1, e2, h1, quatDist_conj_one]
  · have hA : ∑ p ∈ cutPlaquettes (cutBelow 0 Y), plaquetteEnergy (gaugeChain γ U 0) p =
        ∑ p ∈ cutPlaquettes (cutBelow 0 Y), plaquetteEnergy (U 0) p := by
      refine Finset.sum_congr rfl fun p _ => ?_
      have e : gaugeChain γ U 0 = _root_.YangMills.Construction.BlockAverages.gaugeTransform (extendGauge γ 0) (U 0) := if_pos (Nat.zero_le _)
      have h0 : 0 < F.top := by simp [BlockFrame.top]
      have h1 := (hg F 0 h0 hL).2.2.1 (extendGauge γ 0) (U 0) p
      simp only [plaquetteEnergy]
      rw [e, h1]
      have e3 : ((extendGauge γ 0 p.1 * plaquetteHolonomy (U 0) p * (extendGauge γ 0 p.1)⁻¹ :
            UnitQuaternion) : ℍ[ℝ]) =
          (extendGauge γ 0 p.1 : ℍ[ℝ]) * (plaquetteHolonomy (U 0) p : ℍ[ℝ]) *
            (((extendGauge γ 0 p.1)⁻¹ : UnitQuaternion) : ℍ[ℝ]) := rfl
      rw [e3, re_conj_unitQuaternion]
    have hB : ∑ i ∈ Finset.range F.depth, ∑ c ∈ cutBonds (cutBelow (i + 1) Y),
          blockFit (gaugeChain γ U i) (gaugeChain γ U (i + 1)) c =
        ∑ i ∈ Finset.range F.depth, ∑ c ∈ cutBonds (cutBelow (i + 1) Y), blockFit (U i) (U (i + 1)) c := by
      refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun c _ => ?_
      have hi' : i < F.depth := Finset.mem_range.mp hi
      have e₁ : gaugeChain γ U i = _root_.YangMills.Construction.BlockAverages.gaugeTransform (extendGauge γ i) (U i) := if_pos hi'.le
      have e₂ : gaugeChain γ U (i + 1) = _root_.YangMills.Construction.BlockAverages.gaugeTransform (extendGauge γ (i + 1)) (U (i + 1)) := if_pos hi'
      have hin : i < F.top := by
        simp only [BlockFrame.top]
        omega
      rw [e₁, e₂]
      exact (hg F i hin hL).2.2.2 _ _ _ _ c (extendGauge_refineSite hL γ i hi' _)
        (extendGauge_refineSite hL γ i hi' _)
    rw [cutChainEnergy, cutChainEnergy, hA, hB]
end YangMills.Construction.ChainGauges
end
