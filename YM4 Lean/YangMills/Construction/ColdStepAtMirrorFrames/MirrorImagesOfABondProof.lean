import YangMills.Construction.ColdStepAtMirrorFrames.FramesAreLocalProof
import YangMills.Construction.ColdStepAtMirrorFrames.GaugeOfTheLeastChartProof
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorAgreesOnItsBoxProof
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorImagesOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace ReflectedImages
theorem norm_adjointMap (g : UnitQuaternion) (v : imaginaryQuaternions) : ‖adjointMap g v‖ = ‖v‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimalChart.norm_adjointMap <;> assumption
theorem reflectCoord_eq_ite (m : ℕ) (c : ℤ) : reflectCoord m c =
    if -(m : ℤ) ≤ c ∧ c ≤ m then c else if 0 < c then 2 * (m : ℤ) - c else -(2 * (m : ℤ)) - c := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ReflectionOnBox.reflectCoord_eq <;> assumption
theorem period_reflectedFrame (m : ℕ) (l : Fin 4) :
    (reflectedFrame F m).period (reflectedFrame F m).top l = 4 * m := by
  simp [BlockFrame.period, reflectedFrame]
theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by simp [BlockFrame.period]
theorem valMinAbs_bounds {m : ℕ} (hm : 0 < m) (z : (reflectedFrame F m).Cell) (l : Fin 4) :
    -(2 * (m : ℤ)) < (z l).valMinAbs ∧ (z l).valMinAbs ≤ 2 * m := by
  have hN := period_reflectedFrame (F := F) m l
  have : NeZero ((reflectedFrame F m).period (reflectedFrame F m).top l) := ⟨by rw [hN]; omega⟩
  have h := ZMod.valMinAbs_mem_Ioc (z l)
  simp only [Set.mem_Ioc] at h
  omega
theorem valMinAbs_intCast {m : ℕ} (hm : 0 < m) (u : ℤ) (l : Fin 4) (h1 : -(2 * (m : ℤ)) < u)
    (h2 : u ≤ 2 * m) :
    ((u : ZMod ((reflectedFrame F m).period (reflectedFrame F m).top l))).valMinAbs = u := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ReflectionOnBox.valMinAbs_intCast <;> assumption
theorem intCast_valMinAbs {m : ℕ} (hm : 0 < m) (z : (reflectedFrame F m).Cell) (l : Fin 4) :
    (((z l).valMinAbs : ℤ) : ZMod ((reflectedFrame F m).period (reflectedFrame F m).top l)) = z l := by
  have hN := period_reflectedFrame (F := F) m l
  have : NeZero ((reflectedFrame F m).period (reflectedFrame F m).top l) := ⟨by rw [hN]; omega⟩
  exact ZMod.coe_valMinAbs (z l)
theorem eq_of_siteOfCoords_eq {m : ℕ} (hs : ∀ i, 2 * m + 2 < F.extent i) {u w : Fin 4 → ℤ}
    (hu : WithinRadius m u) (hw : WithinRadius m w)
    (h : (siteOfCoords F.top u : F.Cell) = siteOfCoords F.top w) : u = w := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.LocalFrames.siteOfCoords_inj <;> assumption
theorem exists_sourceBond_within {m : ℕ} (hm : 0 < m) (y : F.Cell) (z : (reflectedFrame F m).Cell)
    (i : Fin 4) :
    ∃ u : (Fin 4 → ℤ) × Fin 4, BondWithinRadius m u ∧ u.2 = i ∧
      sourceBond m y z i = (y + siteOfCoords F.top u.1, u.2) ∧
      ∀ l, (l ≠ i → reflectCoord m (z l).valMinAbs = u.1 l) ∧
        (l = i → (IsForwardOriented m z i ∧ reflectCoord m (z l).valMinAbs = u.1 l) ∨
          (¬ IsForwardOriented m z i ∧ reflectCoord m ((z l).valMinAbs + 1) = u.1 l)) := by
  classical
  have hrange : ∀ c : ℤ, -(2 * (m : ℤ)) < c → c ≤ 2 * m + 1 →
      -(m : ℤ) ≤ reflectCoord m c ∧ reflectCoord m c ≤ m := by
    intro c h1 h2
    rw [reflectCoord_eq_ite]
    split_ifs <;> omega
  by_cases hf : IsForwardOriented m z i
  · refine ⟨(fun l => reflectCoord m (z l).valMinAbs, i), ⟨?_, ?_⟩, rfl, ?_, ?_⟩
    · intro l
      have := valMinAbs_bounds hm z l
      exact abs_le.mpr (hrange _ this.1 (by omega))
    · intro l
      have hb := valMinAbs_bounds hm z l
      by_cases hl : l = i
      · subst hl
        have h3 := hrange _ (by omega : -(2 * (m : ℤ)) < (z l).valMinAbs + 1) (by omega)
        have hf2 : reflectCoord m ((z l).valMinAbs + 1) = reflectCoord m (z l).valMinAbs + 1 := hf
        simp only [Pi.add_apply, Pi.single_eq_same]
        rw [← hf2]
        exact abs_le.mpr h3
      · have := hrange _ hb.1 (by omega)
        simp only [Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
        exact abs_le.mpr this
    · simp only [sourceBond, if_pos hf]
    · intro l
      refine ⟨fun _ => rfl, fun hl => Or.inl ⟨hf, rfl⟩⟩
  · refine ⟨(fun l => reflectCoord m ((z l).valMinAbs + (Pi.single i 1 : Fin 4 → ℤ) l), i), ⟨?_, ?_⟩,
      rfl, ?_, ?_⟩
    · intro l
      have hb := valMinAbs_bounds hm z l
      by_cases hl : l = i
      · subst hl
        simp only [Pi.single_eq_same]
        exact abs_le.mpr (hrange _ (by omega) (by omega))
      · simp only [Pi.single_eq_of_ne hl, add_zero]
        exact abs_le.mpr (hrange _ hb.1 (by omega))
    · intro l
      have hb := valMinAbs_bounds hm z l
      by_cases hl : l = i
      · subst hl
        simp only [Pi.add_apply, Pi.single_eq_same]
        have hf2 : ¬ reflectCoord m ((z l).valMinAbs + 1) = reflectCoord m (z l).valMinAbs + 1 := hf
        have h4 := hrange _ hb.1 (by omega)
        have h5 : reflectCoord m ((z l).valMinAbs + 1) + 1 = reflectCoord m (z l).valMinAbs := by
          revert hf2
          rw [reflectCoord_eq_ite, reflectCoord_eq_ite]
          split_ifs <;> omega
        rw [h5]
        exact abs_le.mpr h4
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
        exact abs_le.mpr (hrange _ hb.1 (by omega))
    · simp only [sourceBond, if_neg hf]
    · intro l
      refine ⟨fun hl => ?_, fun hl => Or.inr ⟨hf, ?_⟩⟩
      · simp only [Pi.single_eq_of_ne hl, add_zero]
      · subst hl
        simp only [Pi.single_eq_same]
theorem far_of_reflectCoord_eq_of_ne {m : ℕ} (c u : ℤ)
    (h : reflectCoord m c = u) (hne : c ≠ u) :
    ((m : ℤ) ≤ c ∨ c ≤ -(m : ℤ)) ∧ (c = 2 * m - u ∨ c = -(2 * m) - u) := by
  rw [reflectCoord_eq_ite] at h
  split_ifs at h <;> omega
theorem far_of_not_forward {m : ℕ} (c u : ℤ) (h2 : c ≤ 2 * m)
    (hf : ¬ reflectCoord m (c + 1) = reflectCoord m c + 1) (h : reflectCoord m (c + 1) = u) :
    ((m : ℤ) ≤ c ∨ c ≤ -(m : ℤ)) ∧ (c = 2 * m - u - 1 ∨ c = -(2 * m) - u - 1) := by
  revert hf h
  rw [reflectCoord_eq_ite, reflectCoord_eq_ite]
  split_ifs <;> intro hf h <;> omega
theorem eq_of_forward {m : ℕ} (c u : ℤ) (h1 : -(2 * (m : ℤ)) < c) (h2 : c ≤ 2 * m)
    (hf : reflectCoord m (c + 1) = reflectCoord m c + 1) (h : reflectCoord m c = u) : c = u := by
  revert hf h
  rw [reflectCoord_eq_ite, reflectCoord_eq_ite]
  split_ifs <;> intro hf h <;> omega
theorem le_cellSupDist_zero {m : ℕ} (z : (reflectedFrame F m).Cell) (l : Fin 4) (c : ℤ)
    (hc : c = (z l).valMinAbs) (k : ℕ)
    (h : (k : ℤ) ≤ c ∨ c ≤ -(k : ℤ)) : k ≤ cellSupDist (0 : (reflectedFrame F m).Cell) z := by
  unfold cellSupDist
  have h1 : ((((0 : (reflectedFrame F m).Cell) - z) l).valMinAbs).natAbs ≤
      Finset.univ.sup fun i => ((((0 : (reflectedFrame F m).Cell) - z) i).valMinAbs).natAbs :=
    Finset.le_sup (f := fun i => ((((0 : (reflectedFrame F m).Cell) - z) i).valMinAbs).natAbs)
      (Finset.mem_univ l)
  refine le_trans ?_ h1
  have e : (((0 : (reflectedFrame F m).Cell) - z) l) = - z l := by simp
  rw [e, ZMod.natAbs_valMinAbs_neg, ← hc]
  omega
end ReflectedImages
open ReflectedImages in
theorem reflectedImagesOfBond_holds : reflectedImagesOfBond := by
  classical
  intro F m y c hm hs
  have hm0 : 0 < m := by omega
  have hne : ∀ l, NeZero ((reflectedFrame F m).period (reflectedFrame F m).top l) := fun l =>
    ⟨by rw [period_reflectedFrame]; omega⟩
  have hfin : Finite ((reflectedFrame F m).Cell × Fin 4) := by
    have : ∀ l, Finite (ZMod ((reflectedFrame F m).period (reflectedFrame F m).top l)) := fun l => by
      have := hne l
      exact inferInstance
    have : Finite (reflectedFrame F m).Cell := Pi.finite
    infer_instance
  let J : Finset ((reflectedFrame F m).Cell × Fin 4) :=
    (Set.toFinite {p : (reflectedFrame F m).Cell × Fin 4 | sourceBond m y p.1 p.2 = c}).toFinset
  have hJ : ∀ p, p ∈ J ↔ sourceBond m y p.1 p.2 = c := by
    intro p
    simp [J]
  have hcoord : ∀ (u : (Fin 4 → ℤ) × Fin 4), BondWithinRadius m u → c = (y + siteOfCoords F.top u.1, u.2) →
      ∀ p ∈ J, p.2 = u.2 ∧ ∀ l, (p.1 l).valMinAbs = u.1 l ∨
        (((m : ℤ) ≤ (p.1 l).valMinAbs ∨ (p.1 l).valMinAbs ≤ -(m : ℤ)) ∧
          p.1 l = ((2 * (m : ℤ) - u.1 l - (Pi.single u.2 1 : Fin 4 → ℤ) l : ℤ) :
            ZMod ((reflectedFrame F m).period (reflectedFrame F m).top l))) := by
    intro u hu hc p hp
    obtain ⟨w, hw, hw2, hr, hl⟩ := exists_sourceBond_within hm0 y p.1 p.2
    have h1 := (hJ p).mp hp
    rw [hr, hc] at h1
    have h2 : w.2 = u.2 := (Prod.ext_iff.mp h1).2
    have h3 : (siteOfCoords F.top w.1 : F.Cell) = siteOfCoords F.top u.1 :=
      add_left_cancel (Prod.ext_iff.mp h1).1
    have h4 : w.1 = u.1 := eq_of_siteOfCoords_eq hs hw.1 hu.1 h3
    have hp2 : p.2 = u.2 := by rw [← hw2, h2]
    refine ⟨hp2, fun l => ?_⟩
    have hb := valMinAbs_bounds hm0 p.1 l
    have hNz : ((4 * (m : ℤ) : ℤ) : ZMod ((reflectedFrame F m).period (reflectedFrame F m).top l)) = 0 := by
      have : ((((reflectedFrame F m).period (reflectedFrame F m).top l : ℕ) : ℤ) :
          ZMod ((reflectedFrame F m).period (reflectedFrame F m).top l)) = 0 := by simp
      have e : (((reflectedFrame F m).period (reflectedFrame F m).top l : ℕ) : ℤ) = 4 * m := by
        exact_mod_cast period_reflectedFrame (F := F) m l
      rwa [e] at this
    have hcast := intCast_valMinAbs hm0 p.1 l
    by_cases hli : l = p.2
    · rcases (hl l).2 hli with ⟨hf, he⟩ | ⟨hf, he⟩
      · left
        have hf' : reflectCoord m ((p.1 l).valMinAbs + 1) = reflectCoord m (p.1 l).valMinAbs + 1 := by
          rw [hli]
          exact hf
        rw [← h4]
        exact eq_of_forward _ _ hb.1 hb.2 hf' he
      · right
        have hf' : ¬ reflectCoord m ((p.1 l).valMinAbs + 1) = reflectCoord m (p.1 l).valMinAbs + 1 := by
          rw [hli]
          exact hf
        obtain ⟨a1, a2⟩ := far_of_not_forward _ _ hb.2 hf' he
        refine ⟨a1, ?_⟩
        have es : (Pi.single u.2 1 : Fin 4 → ℤ) l = 1 := by
          rw [← hp2, ← hli]
          simp
        rw [es, ← h4, ← hcast]
        rcases a2 with a2 | a2
        · rw [a2]
        · rw [a2]
          have : ((2 * (m : ℤ) - w.1 l - 1 : ℤ)) = -(2 * (m : ℤ)) - w.1 l - 1 + 4 * (m : ℤ) := by ring
          rw [this]
          push_cast at hNz ⊢
          rw [hNz, add_zero]
    · have he := (hl l).1 hli
      rw [h4] at he
      by_cases hcu : (p.1 l).valMinAbs = u.1 l
      · exact Or.inl hcu
      · right
        obtain ⟨a1, a2⟩ := far_of_reflectCoord_eq_of_ne _ _ he hcu
        refine ⟨a1, ?_⟩
        have es : (Pi.single u.2 1 : Fin 4 → ℤ) l = 0 := by
          rw [← hp2]
          exact Pi.single_eq_of_ne hli 1
        rw [es, sub_zero, ← hcast]
        rcases a2 with a2 | a2
        · rw [a2]
        · rw [a2]
          have : ((2 * (m : ℤ) - u.1 l : ℤ)) = -(2 * (m : ℤ)) - u.1 l + 4 * (m : ℤ) := by ring
          rw [this]
          push_cast at hNz ⊢
          rw [hNz, add_zero]
  have hempty : (∀ u : (Fin 4 → ℤ) × Fin 4, BondWithinRadius m u →
      c ≠ (y + siteOfCoords F.top u.1, u.2)) → J = ∅ := by
    intro hno
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    obtain ⟨w, hw, _, hr, _⟩ := exists_sourceBond_within hm0 y p.1 p.2
    exact hno w hw (((hJ p).mp hp).symm.trans hr)
  refine ⟨J, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hex : ∀ u : (Fin 4 → ℤ) × Fin 4, BondWithinRadius m u → c ≠ (y + siteOfCoords F.top u.1, u.2)
    · rw [hempty hex]
      simp
    · push Not at hex
      obtain ⟨u, hu, hc⟩ := hex
      let pat : (Fin 4 → Bool) → (reflectedFrame F m).Cell × Fin 4 := fun ε =>
        (fun l => if ε l then
            ((2 * (m : ℤ) - u.1 l - (Pi.single u.2 1 : Fin 4 → ℤ) l : ℤ) :
              ZMod ((reflectedFrame F m).period (reflectedFrame F m).top l))
          else ((u.1 l : ℤ) : ZMod ((reflectedFrame F m).period (reflectedFrame F m).top l)), u.2)
      have hsub : J ⊆ Finset.univ.image pat := by
        intro p hp
        obtain ⟨h2, h3⟩ := hcoord u hu hc p hp
        rw [Finset.mem_image]
        refine ⟨fun l => decide (p.1 l ≠ ((u.1 l : ℤ) :
          ZMod ((reflectedFrame F m).period (reflectedFrame F m).top l))), Finset.mem_univ _, ?_⟩
        refine Prod.ext ?_ h2.symm
        funext l
        by_cases hh : p.1 l = ((u.1 l : ℤ) : ZMod ((reflectedFrame F m).period (reflectedFrame F m).top l))
        · simp [pat, hh]
        · have : (decide (p.1 l ≠ ((u.1 l : ℤ) :
              ZMod ((reflectedFrame F m).period (reflectedFrame F m).top l)))) = true := by
            simpa using hh
          simp only [pat, this, if_true]
          rcases h3 l with h4 | h4
          · exact absurd (by rw [← h4]; exact (intCast_valMinAbs hm0 p.1 l).symm) hh
          · exact h4.2.symm
      calc J.card ≤ (Finset.univ.image pat).card := Finset.card_le_card hsub
        _ ≤ (Finset.univ : Finset (Fin 4 → Bool)).card := Finset.card_image_le
        _ = 16 := by simp
  · intro V X z i hz
    have : sourceBond m y z i ≠ c := fun h => hz ((hJ (z, i)).mpr h)
    simp only [reflectedDirection, if_neg this]
  · intro V X p hp
    have h1 : sourceBond m y p.1 p.2 = c := (hJ p).mp hp
    simp only [reflectedDirection, if_pos h1]
    split_ifs
    · rfl
    · rw [norm_neg, norm_adjointMap]
  · intro u hu hc
    have hv : ∀ l, ((siteOfCoords (reflectedFrame F m).top u.1 : (reflectedFrame F m).Cell) l).valMinAbs
        = u.1 l := by
      intro l
      have a := abs_le.mp (hu.1 l)
      exact valMinAbs_intCast hm0 (u.1 l) l (by omega) (by omega)
    have hfold : ∀ l, reflectCoord m (u.1 l) = u.1 l := by
      intro l
      have a := abs_le.mp (hu.1 l)
      rw [reflectCoord_eq_ite, if_pos ⟨a.1, a.2⟩]
    have hfw : IsForwardOriented m (siteOfCoords (reflectedFrame F m).top u.1) u.2 := by
      have a := abs_le.mp (hu.2 u.2)
      simp only [Pi.add_apply, Pi.single_eq_same] at a
      unfold IsForwardOriented
      rw [hv, hfold, reflectCoord_eq_ite, if_pos ⟨a.1, a.2⟩]
    have hread : sourceBond m y (siteOfCoords (reflectedFrame F m).top u.1) u.2 = c := by
      simp only [sourceBond, if_pos hfw, hv, hfold, hc]
    refine ⟨(hJ _).mpr hread, fun V X => ?_, fun p hp hne => ?_⟩
    · simp only [reflectedDirection, if_pos hread, if_pos hfw]
    · obtain ⟨h2, h3⟩ := hcoord u hu hc p hp
      have hex : ∃ l, (p.1 l).valMinAbs ≠ u.1 l := by
        by_contra hcon
        push Not at hcon
        apply hne
        refine Prod.ext ?_ h2
        funext l
        have := intCast_valMinAbs hm0 p.1 l
        rw [hcon l] at this
        exact this.symm
      obtain ⟨l, hl⟩ := hex
      rcases h3 l with h4 | h4
      · exact absurd h4 hl
      · exact le_cellSupDist_zero p.1 l _ rfl m h4.1
  · intro hno
    refine ⟨hempty hno, ?_⟩
    by_contra hcon
    have hlt : cellSupDist y c.1 < m := by omega
    have hneF : ∀ l, NeZero (F.period F.top l) := fun l => ⟨by
      rw [period_top]
      have := hs l
      omega⟩
    let e : Fin 4 → ℤ := fun l => ((c.1 - y) l).valMinAbs
    have hel : ∀ l, |e l| < m := by
      intro l
      have h1 : ((y - c.1) l).valMinAbs.natAbs ≤ cellSupDist y c.1 :=
        Finset.le_sup (f := fun i => (((y - c.1) i).valMinAbs).natAbs) (Finset.mem_univ l)
      have e1 : (y - c.1) l = -((c.1 - y) l) := by simp
      rw [e1, ZMod.natAbs_valMinAbs_neg] at h1
      have h2 : |e l| = ((((c.1 - y) l).valMinAbs.natAbs : ℕ) : ℤ) := by
        simp only [e]
        rw [Int.natCast_natAbs]
      rw [h2]
      exact_mod_cast lt_of_le_of_lt h1 hlt
    refine hno (e, c.2) ⟨fun l => (hel l).le, fun l => ?_⟩ ?_
    · have := abs_lt.mp (hel l)
      refine abs_le.mpr ?_
      simp only [Pi.add_apply]
      by_cases hl : l = c.2
      · subst hl
        simp only [Pi.single_eq_same]
        omega
      · simp only [Pi.single_eq_of_ne hl]
        omega
    · refine Prod.ext ?_ rfl
      funext l
      have := hneF l
      simp only [siteOfCoords, Pi.add_apply, e]
      rw [ZMod.coe_valMinAbs]
      simp
end ColdStepAtMirrorFrames
end YangMills.Construction
end
