import YangMills.Construction.ColdStepAtMirrorFrames.MirrorFieldIsColdProof
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorImagesOfABondProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace ReflectedField
theorem reflectCoord_eq_ite (m : ℕ) (c : ℤ) : reflectCoord m c =
    if -(m : ℤ) ≤ c ∧ c ≤ m then c else if 0 < c then 2 * (m : ℤ) - c else -(2 * (m : ℤ)) - c := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ReflectionOnBox.reflectCoord_eq <;> assumption
theorem period_reflectedFrame (m : ℕ) (l : Fin 4) :
    (reflectedFrame F m).period (reflectedFrame F m).top l = 4 * m := by
  simp [BlockFrame.period, reflectedFrame]
theorem valMinAbs_bounds {m : ℕ} (hm : 0 < m) (z : (reflectedFrame F m).Cell) (l : Fin 4) :
    -(2 * (m : ℤ)) < (z l).valMinAbs ∧ (z l).valMinAbs ≤ 2 * m := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ReflectedImages.valMinAbs_bounds <;> assumption
theorem reflectCoord_add_one (m : ℕ) (c : ℤ) :
    reflectCoord m (c + 1) = reflectCoord m c + 1 ∨
      reflectCoord m (c + 1) = reflectCoord m c - 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.Reflection.reflectCoord_succ_eq <;> assumption
theorem reflectCoord_mem_Icc {m : ℕ} (hm : 0 < m) (c : ℤ) (h1 : -(2 * (m : ℤ)) < c)
    (h2 : c ≤ 2 * m + 1) :
    -(m : ℤ) ≤ reflectCoord m c ∧ reflectCoord m c ≤ m := by
  rw [reflectCoord_eq_ite]
  split_ifs <;> omega
theorem reflectCoord_add_unitStep_self (m : ℕ) (hm : 0 < m) (z : (reflectedFrame F m).Cell) (i : Fin 4) :
    reflectCoord m ((z + unitStep (reflectedFrame F m).top i : (reflectedFrame F m).Cell) i).valMinAbs =
      reflectCoord m ((z i).valMinAbs + 1) := by
  have hN := period_reflectedFrame (F := F) m i
  have hne : NeZero ((reflectedFrame F m).period (reflectedFrame F m).top i) := ⟨by rw [hN]; omega⟩
  set v := (z i).valMinAbs with hv
  set v' := ((z + unitStep (reflectedFrame F m).top i : (reflectedFrame F m).Cell) i).valMinAbs with hv'
  have r1 := valMinAbs_bounds hm z i
  have r2 := valMinAbs_bounds hm (z + unitStep (reflectedFrame F m).top i) i
  have hc : ((v' : ℤ) : ZMod ((reflectedFrame F m).period (reflectedFrame F m).top i)) =
      ((v + 1 : ℤ) : ZMod ((reflectedFrame F m).period (reflectedFrame F m).top i)) := by
    push_cast
    rw [hv, hv', ZMod.coe_valMinAbs, ZMod.coe_valMinAbs]
    simp [unitStep, siteOfCoords]
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hc
  rw [← hv] at r1
  rw [← hv'] at r2
  have hP : (((reflectedFrame F m).period (reflectedFrame F m).top i : ℕ) : ℤ) = 4 * m := by
    exact_mod_cast hN
  rw [hP] at hk
  have hk01 : k = 0 ∨ k = 1 := by
    by_contra hcon
    push Not at hcon
    rcases lt_or_gt_of_ne hcon.1 with h | h
    · have : k ≤ -1 := by omega
      nlinarith
    · have : 2 ≤ k := by
        have := hcon.2
        omega
      nlinarith
  rcases hk01 with rfl | rfl
  · have : v' = v + 1 := by linarith
    rw [this]
  · have : v' = v + 1 - 4 * m := by linarith
    rw [this, reflectCoord_eq_ite, reflectCoord_eq_ite]
    split_ifs <;> omega
theorem reflectCoord_add_unitStep_of_ne (m : ℕ) (z : (reflectedFrame F m).Cell) (i l : Fin 4)
    (hl : l ≠ i) (hm : 0 < m) :
    reflectCoord m ((z + unitStep (reflectedFrame F m).top i : (reflectedFrame F m).Cell) l).valMinAbs =
      reflectCoord m (z l).valMinAbs := by
  have e : ((z + unitStep (reflectedFrame F m).top i : (reflectedFrame F m).Cell) l) = z l := by
    simp [unitStep, siteOfCoords, Pi.single_eq_of_ne hl]
  rw [e]
theorem siteOfCoords_add {j : ℕ} (a b : Fin 4 → ℤ) :
    (siteOfCoords j (a + b) : F.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
end ReflectedField
open ReflectedField in
theorem reflectedBondReadsBox_holds : ReflectedBondReadsBox := by
  classical
  intro F m z i hm
  refine ⟨?_, fun y V => ?_⟩
  · by_cases hf : IsForwardOriented m z i
    · simp only [sourceOffset, if_pos hf]
      refine ⟨fun l => ?_, fun l => ?_⟩
      · have := valMinAbs_bounds hm z l
        exact abs_le.mpr (reflectCoord_mem_Icc hm _ this.1 (by omega))
      · have hb := valMinAbs_bounds hm z l
        by_cases hl : l = i
        · subst hl
          have h3 := reflectCoord_mem_Icc hm ((z l).valMinAbs + 1) (by omega) (by omega)
          have hf2 : reflectCoord m ((z l).valMinAbs + 1) = reflectCoord m (z l).valMinAbs + 1 := hf
          simp only [Pi.add_apply, Pi.single_eq_same]
          rw [← hf2]
          exact abs_le.mpr h3
        · have := reflectCoord_mem_Icc hm _ hb.1 (by omega)
          simp only [Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
          exact abs_le.mpr this
    · simp only [sourceOffset, if_neg hf]
      refine ⟨fun l => ?_, fun l => ?_⟩
      · have hb := valMinAbs_bounds hm z l
        by_cases hl : l = i
        · subst hl
          simp only [Pi.single_eq_same]
          exact abs_le.mpr (reflectCoord_mem_Icc hm _ (by omega) (by omega))
        · simp only [Pi.single_eq_of_ne hl, add_zero]
          exact abs_le.mpr (reflectCoord_mem_Icc hm _ hb.1 (by omega))
      · have hb := valMinAbs_bounds hm z l
        by_cases hl : l = i
        · subst hl
          simp only [Pi.add_apply, Pi.single_eq_same]
          have hf2 : ¬ reflectCoord m ((z l).valMinAbs + 1) = reflectCoord m (z l).valMinAbs + 1 := hf
          have h4 := reflectCoord_mem_Icc hm _ hb.1 (by omega)
          have h5 : reflectCoord m ((z l).valMinAbs + 1) + 1 = reflectCoord m (z l).valMinAbs := by
            rcases reflectCoord_add_one m (z l).valMinAbs with h | h
            · exact absurd h hf2
            · omega
          rw [h5]
          exact abs_le.mpr h4
        · simp only [Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
          exact abs_le.mpr (reflectCoord_mem_Icc hm _ hb.1 (by omega))
  · by_cases hf : IsForwardOriented m z i
    · have hf' : reflectCoord m ((z i).valMinAbs + (Pi.single i 1 : Fin 4 → ℤ) i) =
          reflectCoord m (z i).valMinAbs + 1 := by simpa [IsForwardOriented] using hf
      simp only [reflectedField, sourceOffset, if_pos hf, if_pos hf']
    · have hf' : ¬ reflectCoord m ((z i).valMinAbs + (Pi.single i 1 : Fin 4 → ℤ) i) =
          reflectCoord m (z i).valMinAbs + 1 := by simpa [IsForwardOriented] using hf
      simp only [reflectedField, sourceOffset, if_neg hf, if_neg hf']
open ReflectedField in
theorem reflectedFieldOfGaugedTop_holds : ReflectedFieldOfGaugedTop := by
  classical
  intro F m y V γ hm
  funext z i
  obtain ⟨e, he⟩ : ∃ e : Fin 4 → ℤ, e = fun l => reflectCoord m (z l).valMinAbs := ⟨_, rfl⟩
  obtain ⟨e', he'⟩ : ∃ e' : Fin 4 → ℤ,
      e' = fun l => reflectCoord m ((z l).valMinAbs + (Pi.single i 1 : Fin 4 → ℤ) l) := ⟨_, rfl⟩
  have hnext : (fun l => reflectCoord m
      ((z + unitStep (reflectedFrame F m).top i : (reflectedFrame F m).Cell) l).valMinAbs) = e' := by
    funext l
    rw [he']
    by_cases hl : l = i
    · subst hl
      simp only [Pi.single_eq_same]
      exact reflectCoord_add_unitStep_self m hm z l
    · simp only [Pi.single_eq_of_ne hl, add_zero]
      exact reflectCoord_add_unitStep_of_ne m z i l hl hm
  have hg1 : reflectedGauge m y γ z = γ (y + siteOfCoords F.top e) := by
    simp only [reflectedGauge, he]
  have hg2 : reflectedGauge m y γ (z + unitStep (reflectedFrame F m).top i) =
      γ (y + siteOfCoords F.top e') := by
    simp only [reflectedGauge, hnext]
  have hf0 : e' i = e i + 1 ∨ e' i = e i - 1 := by
    rw [he, he']
    simp only [Pi.single_eq_same]
    exact reflectCoord_add_one m _
  have hdiff : ∀ l, l ≠ i → e' l = e l := by
    intro l hl
    rw [he, he']
    simp [Pi.single_eq_of_ne hl]
  have hmf : ∀ V' : F.GaugeField F.top, reflectedField m y V' z i =
      if e' i = e i + 1 then V' (y + siteOfCoords F.top e) i
      else (V' (y + siteOfCoords F.top e') i)⁻¹ := by
    intro V'
    rw [he, he']
    rfl
  have hgz : _root_.YangMills.Construction.BlockAverages.gaugeTransform (reflectedGauge m y γ) (reflectedField m y V) z i =
      reflectedGauge m y γ z * reflectedField m y V z i *
        (reflectedGauge m y γ (z + unitStep (reflectedFrame F m).top i))⁻¹ := rfl
  rw [hgz, hmf (_root_.YangMills.Construction.BlockAverages.gaugeTransform γ V), hmf V, hg1, hg2]
  by_cases hc : e' i = e i + 1
  · rw [if_pos hc, if_pos hc]
    have h1 : e' = e + Pi.single i 1 := by
      funext l
      by_cases hl : l = i
      · subst hl
        simp [hc]
      · simp [hdiff l hl, Pi.single_eq_of_ne hl]
    have h2 : (y + siteOfCoords F.top e + unitStep F.top i : F.Cell) = y + siteOfCoords F.top e' := by
      rw [h1, siteOfCoords_add, add_assoc]
      rfl
    simp only [gaugeTransform, h2]
  · rw [if_neg hc, if_neg hc]
    have hc2 : e' i = e i - 1 := hf0.resolve_left hc
    have h1 : e = e' + Pi.single i 1 := by
      funext l
      by_cases hl : l = i
      · subst hl
        simp [hc2]
      · simp [hdiff l hl, Pi.single_eq_of_ne hl]
    have h2 : (y + siteOfCoords F.top e' + unitStep F.top i : F.Cell) = y + siteOfCoords F.top e := by
      rw [h1, siteOfCoords_add, add_assoc]
      rfl
    simp only [gaugeTransform, h2]
    group
theorem reflectedFieldOfTranslatedCentre_holds : ReflectedFieldOfTranslatedCentre := by
  intro F m y h V
  funext z i
  simp only [reflectedField, translateField]
  have e : ∀ u : F.Cell, y + h + u - h = y + u := fun u => by abel
  simp only [e]
theorem reflectedFieldReadsBox_holds : reflectedFieldReadsBox :=
  ⟨reflectedBondReadsBox_holds, reflectedFieldOfGaugedTop_holds, reflectedFieldOfTranslatedCentre_holds⟩
end ColdStepAtMirrorFrames
end YangMills.Construction
end
