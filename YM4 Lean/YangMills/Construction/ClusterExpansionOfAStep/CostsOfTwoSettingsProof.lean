import YangMills.Construction.ClusterExpansionOfAStep.CostsOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.LocalityOfTheKernel
import YangMills.Construction.ClusterExpansionOfAStep.SharesOfHoledFieldsAtLevelZero
import YangMills.Construction.ClusterExpansionOfAStep.SharesOfHoledFieldsForget
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open scoped Quaternion
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusLumps TorusFields StepSettings StepCosts BlockOffsets
namespace BlockCosts
section Sites
variable {L n : ℕ} [NeZero L] [NeZero n]
omit [NeZero L] [NeZero n] in
theorem zmod_eq_of_intCast_cast_eq (P N : ℕ) (hPN : P = N) [NeZero P] (a b : ZMod P)
    (e : (((ZMod.cast a : ℤ)) : ZMod N) = ((ZMod.cast b : ℤ) : ZMod N)) : a = b := by apply _root_.YangMills.Construction.TorusLumps.castInt_injective <;> assumption
theorem eq_of_toTorusSite_eq {x x' : (stepBlockFrame L n).Site 0}
    (e : (toTorusSite (n * L) x : TorusSite (n * L)) = toTorusSite (n * L) x') : x = x' := by
  funext i
  exact zmod_eq_of_intCast_cast_eq _ (n * L) (period_zero i) _ _ (congrFun e i)
theorem toTorusSite_siteOfCoords (z : Fin 4 → ℤ) :
    (toTorusSite (n * L) (siteOfCoords (F := stepBlockFrame L n) 0 z) : TorusSite (n * L)) = siteOfInt z := by
  funext i
  exact intCast_cast_of_eq _ (n * L) (period_zero i) (z i)
theorem fineSite_shift (Y : TorusSite n) (h o : Fin 4 → ℤ) :
    fineSite L Y h o = fineSite L (Y + siteOfInt h) 0 o := by
  have e : fineSite L Y h o = siteOfInt (blockPoint L (fun i => ((Y i).cast : ℤ) + h i) o) := rfl
  rw [e, siteOfInt_blockPoint (NeZero.ne L), siteOfInt_cast_add]
theorem toTorusSite_siteAtOffset (Y : TorusSite n) (h o : Fin 4 → ℤ) :
    (toTorusSite (n * L) (siteAtOffset (F := stepBlockFrame L n)
      (torusSiteInFrame (stepBlockFrame L n) 1 (Y + siteOfInt h)) o) :
      TorusSite (n * L)) = fineSite L Y h o := by
  set A : Fin 4 → ℤ := fun i => (((Y + siteOfInt h : TorusSite n) i).cast : ℤ) with hA
  have e1 : siteAtOffset (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 1 (Y + siteOfInt h)) o =
      (siteOfCoords (F := stepBlockFrame L n) 0 (blockPoint L A o) : (stepBlockFrame L n).Site 0) := by
    have c1 := cellCentre_siteOfCoords (L := L) (n := n) A
    have c2 := siteOfCoords_add (L := L) (n := n) 0 (fun i => (L : ℤ) * A i) o
    exact (congrArg (· + siteOfCoords (F := stepBlockFrame L n) 0 o) c1).trans c2.symm
  calc (toTorusSite (n * L) (siteAtOffset (F := stepBlockFrame L n)
        (torusSiteInFrame (stepBlockFrame L n) 1 (Y + siteOfInt h)) o) : TorusSite (n * L))
        = toTorusSite (n * L) (siteOfCoords (F := stepBlockFrame L n) 0 (blockPoint L A o)) := congrArg _ e1
    _ = siteOfInt (blockPoint L A o) := toTorusSite_siteOfCoords _
    _ = fineSite L (siteOfInt A) 0 o := siteOfInt_blockPoint (NeZero.ne L) _ _
    _ = fineSite L (Y + siteOfInt h) 0 o := by rw [hA, siteOfInt_cast_self]
    _ = fineSite L Y h o := (fineSite_shift Y h o).symm
theorem cellCentreOnTorus_eq_fineSite (Y : TorusSite n) (h : Fin 4 → ℤ) :
    cellCentreOnTorus L (torusSiteInFrame (stepBlockFrame L n) 1 (Y + siteOfInt h)) = fineSite L Y h 0 := by
  have e := toTorusSite_siteAtOffset (L := L) Y h 0
  have e2 : siteAtOffset (F := stepBlockFrame L n) (torusSiteInFrame (stepBlockFrame L n) 1 (Y + siteOfInt h)) 0 =
      cellCentre (F := stepBlockFrame L n) 0 (torusSiteInFrame (stepBlockFrame L n) 1 (Y + siteOfInt h)) := by
    have z : siteOfCoords (F := stepBlockFrame L n) 0 (0 : Fin 4 → ℤ) = 0 := by
      funext i
      simp [siteOfCoords]
    show cellCentre (F := stepBlockFrame L n) 0 _ + siteOfCoords 0 0 = _
    rw [z]
    exact add_zero _
  rw [e2] at e
  exact e
omit [NeZero L] in
theorem intCast_cast_add_intCast (P N : ℕ) (hPN : P = N) [NeZero N] (a : ZMod N) (b : ℤ) :
    (((ZMod.cast a : ℤ)) : ZMod P) + (b : ZMod P) = ((ZMod.cast (a + (b : ZMod N)) : ℤ) : ZMod P) := by
  subst hPN
  simp
theorem torusSiteInFrame_add_unitStep (Y : TorusSite n) (h : Fin 4 → ℤ) (i : Fin 4) :
    torusSiteInFrame (stepBlockFrame L n) 1 (Y + siteOfInt h) + BlockAverages.unitStep 1 i =
      torusSiteInFrame (stepBlockFrame L n) 1 (Y + siteOfInt (h + Pi.single i 1)) := by
  funext l
  have e : (Y + siteOfInt (h + Pi.single i 1) : TorusSite n) l =
      (Y + siteOfInt h : TorusSite n) l + (((Pi.single i 1 : Fin 4 → ℤ) l : ℤ) : ZMod n) := by
    rw [siteOfInt_add, ← add_assoc]
    rfl
  show ((((Y + siteOfInt h : TorusSite n) l).cast : ℤ) : ZMod ((stepBlockFrame L n).period 1 l)) +
      (((Pi.single i 1 : Fin 4 → ℤ) l : ℤ) : ZMod ((stepBlockFrame L n).period 1 l)) =
    ((((Y + siteOfInt (h + Pi.single i 1) : TorusSite n) l).cast : ℤ) : ZMod ((stepBlockFrame L n).period 1 l))
  rw [e]
  exact intCast_cast_add_intCast _ n (period_one l) _ _
theorem readAtLevel_one (V : TorusField n) (c : TorusSite n) (i : Fin 4) :
    readAtLevel (stepBlockFrame L n) 1 V (torusSiteInFrame (stepBlockFrame L n) 1 c) i = V c i := by
  unfold readAtLevel
  congr 1
  funext k
  show (((ZMod.cast ((((c k).cast : ℤ)) : ZMod ((stepBlockFrame L n).period 1 k)) : ℤ)) : ZMod n) = c k
  rw [intCast_cast_of_eq _ n (period_one k)]
  simp
end Sites
section Settings
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
omit [NeZero n] [NeZero n'] in
theorem offsetInBox_mono {k m : ℕ} (hk : k ≤ m) {h : Fin 4 → ℤ} (hh : OffsetInBox k h) : OffsetInBox m h :=
  fun l => (hh l).trans (by exact_mod_cast hk)
theorem field_eq_of_offsetInBox {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n}
    {Y' : TorusSite n'} {m k : ℕ} {η : FreeCoords s.free} {η' : FreeCoords s'.free}
    (hodd : Odd R.params.side) (hn : 2 ≤ n) (hn' : 2 ≤ n')
    (hf : s.free ⊆ chartBonds R.params.side n) (hag : SettingsAgreeNear s s' Y Y' m) (hk : k ≤ m)
    (hnear : CoordsAgreeNear s s' Y Y' k η η') (kk o : Fin 4 → ℤ) (i : Fin 4)
    (ho : o ∈ centredCube R.params.side) (hin : OffsetInBox k kk)
    (hout : o + Pi.single i 1 ∉ centredCube R.params.side → OffsetInBox k (kk + Pi.single i 1)) :
    s.field η (fineSite R.params.side Y kk o) i = s'.field η' (fineSite R.params.side Y' kk o) i := by
  have hinm : OffsetInBox m kk := offsetInBox_mono hk hin
  have hnr : IsNearIndex R.params.side k (kk, o, i) := ⟨hin, ho⟩
  have hnm : IsNearIndex R.params.side m (kk, o, i) := ⟨hinm, ho⟩
  by_cases hfr : nearBond R.params.side Y (kk, o, i) ∈ s.free
  · have hfr' := (hag.free_iff _ hnm).mp hfr
    have h1 := hnear _ hnr
    simp only [ChartSetting.coordsByIndex] at h1
    rw [dif_pos hfr, dif_pos hfr'] at h1
    have hfm := hag.frame_eq _ hnm hfr
    have e1 : s.field η (fineSite R.params.side Y kk o) i = chartLink s (fineSite R.params.side Y kk o) i
        (s.frame (nearBond R.params.side Y (kk, o, i)) + toImaginary (η ⟨_, hfr⟩)) := dif_pos hfr
    have e2 : s'.field η' (fineSite R.params.side Y' kk o) i = chartLink s' (fineSite R.params.side Y' kk o) i
        (s'.frame (nearBond R.params.side Y' (kk, o, i)) + toImaginary (η' ⟨_, hfr'⟩)) := dif_pos hfr'
    rw [e1, e2, h1, hfm]
    unfold chartLink
    rw [gaugeAt_fineSite_eq hodd hn hf hag kk o hinm ho, fineSite_add_unitStep, fineSite_add_unitStep]
    have hcr : ∀ (N : ℕ) [NeZero N], 2 ≤ N → ∀ (Z : TorusSite N),
        IsCrossingBond (F := stepBlockFrame R.params.side N)
          (torusSiteInFrame (stepBlockFrame R.params.side N) 0 (fineSite R.params.side Z kk o), i) ↔
          o + Pi.single i 1 ∉ centredCube R.params.side := by
      intro N _ hN Z
      show IsCrossingBond (F := stepBlockFrame R.params.side N) (torusSiteInFrame (stepBlockFrame R.params.side N) 0
        (siteOfInt (blockPoint R.params.side (fun i => ((Z i).cast : ℤ) + kk i) o)), i) ↔ _
      rw [torusSiteInFrame_siteOfInt]
      exact isCrossingBond_blockPoint_iff hodd hN _ o ho i
    have hblock : ∀ (N : ℕ) [NeZero N] (Z : TorusSite N),
        parentBlock R.params.side (fineSite R.params.side Z kk o) = Z + siteOfInt kk := by
      intro N _ Z
      show parentBlock R.params.side
        (siteOfInt (blockPoint R.params.side (fun i => ((Z i).cast : ℤ) + kk i) o) : TorusSite (N * R.params.side)) = _
      rw [parentBlock_blockPoint hodd _ o ho, siteOfInt_cast_add]
    by_cases hcube : o + Pi.single i 1 ∈ centredCube R.params.side
    · rw [if_neg (fun h => ((hcr n hn Y).mp h) hcube), if_neg (fun h => ((hcr n' hn' Y').mp h) hcube),
        gaugeAt_fineSite_eq hodd hn hf hag kk _ hinm hcube]
    · have hin1 : OffsetInBox m (kk + Pi.single i 1) := offsetInBox_mono hk (hout hcube)
      have hV : s.coarse (parentBlock R.params.side (fineSite R.params.side Y kk o)) i =
          s'.coarse (parentBlock R.params.side (fineSite R.params.side Y' kk o)) i := by
        rw [hblock, hblock]
        exact hag.coarse_agree (kk, i) ⟨hinm, hin1⟩
      rw [if_pos ((hcr n hn Y).mpr hcube), if_pos ((hcr n' hn' Y').mpr hcube), hV, fineSite_wrap, fineSite_wrap]
      have hwrap : o + Pi.single i 1 - (R.params.side : ℤ) • Pi.single i 1 ∈ centredCube R.params.side := by
        obtain ⟨H, hH⟩ := hodd
        have hL : ((R.params.side : ℤ) - 1) / 2 = (H : ℤ) := by rw [hH]; push_cast; omega
        have hLH : (R.params.side : ℤ) = 2 * H + 1 := by rw [hH]; push_cast; ring
        have hb := (mem_centredCube_iff o).mp ho
        rw [hL] at hb
        have hoi : o i = H := by
          by_contra hne
          apply hcube
          rw [mem_centredCube_iff, hL]
          intro l
          by_cases hl : l = i
          · subst hl
            have := hb l
            simp only [Pi.add_apply, Pi.single_eq_same]
            omega
          · have := hb l
            simpa [Pi.single_apply, hl] using this
        rw [mem_centredCube_iff, hL]
        intro l
        by_cases hl : l = i
        · subst hl
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
          omega
        · have := hb l
          simpa [Pi.single_apply, hl] using this
      rw [gaugeAt_fineSite_eq hodd hn hf hag _ _ hin1 hwrap]
  · have hfr' : nearBond R.params.side Y' (kk, o, i) ∉ s'.free := fun h => hfr ((hag.free_iff _ hnm).mpr h)
    have e1 : s.field η (fineSite R.params.side Y kk o) i = s.fine (fineSite R.params.side Y kk o) i := dif_neg hfr
    have e2 : s'.field η' (fineSite R.params.side Y' kk o) i = s'.fine (fineSite R.params.side Y' kk o) i :=
      dif_neg hfr'
    rw [e1, e2]
    exact hag.fine_eq _ hnm hfr
theorem fieldsAgreeNear_fineSite {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n}
    {Y' : TorusSite n'} {m k : ℕ} {η : FreeCoords s.free} {η' : FreeCoords s'.free}
    (hodd : Odd R.params.side) (hn : 2 ≤ n) (hn' : 2 ≤ n')
    (hf : s.free ⊆ chartBonds R.params.side n) (hag : SettingsAgreeNear s s' Y Y' m) (hk4 : 4 ≤ k) (hk : k ≤ m)
    (hnear : CoordsAgreeNear s s' Y Y' k η η') (h : Fin 4 → ℤ) (hh : OffsetInBox 1 h) :
    FieldsAgreeNear (s.field η) (s'.field η') (fineSite R.params.side Y h 0) (fineSite R.params.side Y' h 0)
      (3 * R.params.side) := by
  intro b hb
  obtain ⟨e, i⟩ := b
  obtain ⟨kk, o, ho, hdec⟩ := exists_block_offset hodd e
  obtain ⟨H, hH⟩ := id hodd
  have hL : ((R.params.side : ℤ) - 1) / 2 = (H : ℤ) := by rw [hH]; push_cast; omega
  have hLH : (R.params.side : ℤ) = 2 * H + 1 := by rw [hH]; push_cast; ring
  have hc := (mem_centredCube_iff o).mp ho
  rw [hL] at hc
  have hLpos : (0 : ℤ) < R.params.side := by omega
  have hcast : ((3 * R.params.side : ℕ) : ℤ) = 3 * (R.params.side : ℤ) := by push_cast; ring
  have hb1 : ∀ l, -(3 * (R.params.side : ℤ)) ≤ e l ∧ e l ≤ 3 * (R.params.side : ℤ) := fun l => by
    have := hb.1 l
    rw [hcast] at this
    exact abs_le.mp this
  have hbound : ∀ l, -3 ≤ kk l ∧ kk l ≤ 3 := by
    intro l
    have h1 := hb1 l
    have h2 := hc l
    have h3 := hdec l
    have a1 : (R.params.side : ℤ) * kk l < (R.params.side : ℤ) * 4 := by linarith [h1.1, h1.2, h2.1, h2.2]
    have a2 : (R.params.side : ℤ) * (-kk l) < (R.params.side : ℤ) * 4 := by
      have : (R.params.side : ℤ) * (-kk l) = -((R.params.side : ℤ) * kk l) := by ring
      rw [this]
      linarith [h1.1, h1.2, h2.1, h2.2]
    have b1 := lt_of_mul_lt_mul_left a1 hLpos.le
    have b2 := lt_of_mul_lt_mul_left a2 hLpos.le
    omega
  have hpt : ∀ (N : ℕ) (Z : TorusSite N),
      fineSite R.params.side Z h 0 + siteOfInt e = fineSite R.params.side Z (h + kk) o := by
    intro N Z
    show siteOfInt _ + siteOfInt _ = siteOfInt _
    rw [← siteOfInt_add]
    congr 1
    funext l
    have h2 := hdec l
    simp only [Pi.add_apply, Pi.zero_apply] at h2 ⊢
    rw [h2]
    ring
  show s.field η (fineSite R.params.side Y h 0 + siteOfInt e) i =
    s'.field η' (fineSite R.params.side Y' h 0 + siteOfInt e) i
  rw [hpt, hpt]
  refine field_eq_of_offsetInBox hodd hn hn' hf hag hk hnear (h + kk) o i ho ?_ ?_
  · intro l
    have h1 := abs_le.mp (hh l)
    have h2 := hbound l
    simp only [Pi.add_apply]
    push_cast at h1
    rw [abs_le]
    constructor <;> omega
  · intro hout
    have hoi : o i = H := by
      by_contra hne
      apply hout
      rw [mem_centredCube_iff, hL]
      intro l
      by_cases hl : l = i
      · subst hl
        have := hc l
        simp only [Pi.add_apply, Pi.single_eq_same]
        omega
      · have := hc l
        simpa [Pi.single_apply, hl] using this
    have h2 : kk i ≤ 2 := by
      have h3 := abs_le.mp (hb.2 i)
      rw [hcast] at h3
      have h4 := hdec i
      simp only [Pi.add_apply, Pi.single_eq_same] at h3
      have a1 : (R.params.side : ℤ) * kk i < (R.params.side : ℤ) * 3 := by linarith [h3.2]
      have b1 := lt_of_mul_lt_mul_left a1 hLpos.le
      omega
    intro l
    have h1 := abs_le.mp (hh l)
    have h3 := hbound l
    push_cast at h1
    simp only [Pi.add_apply]
    rw [abs_le]
    by_cases hl : l = i
    · subst hl
      simp only [Pi.single_eq_same]
      constructor <;> omega
    · simp only [Pi.single_apply, hl, if_false]
      constructor <;> omega
end Settings
section Means
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
omit [NeZero n] [NeZero n'] in
theorem offsetInBox_zero (m : ℕ) : OffsetInBox m (0 : Fin 4 → ℤ) := fun l => by simp
omit [NeZero n] [NeZero n'] in
theorem offsetInBox_single (i : Fin 4) : OffsetInBox 1 (Pi.single i (1 : ℤ) : Fin 4 → ℤ) := by
  intro l
  by_cases hl : l = i
  · subst hl
    simp
  · simp [Pi.single_apply, hl]
omit [NeZero n] [NeZero n'] in
theorem offsetInBox_neg_single (i : Fin 4) : OffsetInBox 1 (-Pi.single i (1 : ℤ) : Fin 4 → ℤ) := by
  intro l
  have := offsetInBox_single i l
  simpa using this
theorem contourMean_eq (hloc : BondKernelLocality) (hfit : R.params.Admissible)
    (hJ : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side) (h16 : 16 ≤ n) (h16' : 16 ≤ n')
    {s : ChartSetting R n} {s' : ChartSetting R n'}
    {Y : TorusSite n} {Y' : TorusSite n'} {m k : ℕ} {η : FreeCoords s.free} {η' : FreeCoords s'.free}
    (hf : s.free ⊆ chartBonds R.params.side n) (hag : SettingsAgreeNear s s' Y Y' m) (hk4 : 4 ≤ k) (hk : k ≤ m)
    (hnear : CoordsAgreeNear s s' Y Y' k η η') (h : Fin 4 → ℤ) (i : Fin 4) (hh : OffsetInBox 1 h)
    (hh' : OffsetInBox 1 (h + Pi.single i 1)) :
    contourMean R.params.baseDepth (stepHotLumps R.params (s.field η)) s.bases
        (readAtLevel (stepBlockFrame R.params.side n) 0 (s.field η))
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h), i) =
      contourMean R.params.baseDepth (stepHotLumps R.params (s'.field η')) s'.bases
        (readAtLevel (stepBlockFrame R.params.side n') 0 (s'.field η'))
        (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h), i) := by
  have hodd := hfit.L_odd
  have hn : 2 ≤ n := by omega
  have hn' : 2 ≤ n' := by omega
  have h1m : 1 ≤ m := by omega
  obtain ⟨z₀, hz₀, e₀, e₀'⟩ := hag.bases_match h (offsetInBox_mono h1m hh)
  obtain ⟨z₁, hz₁, e₁, e₁'⟩ := hag.bases_match (h + Pi.single i 1) (offsetInBox_mono h1m hh')
  have F0 := fieldsAgreeNear_fineSite hodd hn hn' hf hag hk4 hk hnear h hh
  have F1 := fieldsAgreeNear_fineSite hodd hn hn' hf hag hk4 hk hnear _ hh'
  rw [← cellCentreOnTorus_eq_fineSite, ← cellCentreOnTorus_eq_fineSite] at F0 F1
  rw [← torusSiteInFrame_add_unitStep, ← torusSiteInFrame_add_unitStep] at F1
  have S0 := (hloc R.params hfit hJ n n' h16 h16' (s.field η) (s'.field η')
    (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))
    (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h))).2.1 F0
  have S1 := (hloc R.params hfit hJ n n' h16 h16' (s.field η) (s'.field η')
    (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h) + BlockAverages.unitStep 1 i)
    (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h) + BlockAverages.unitStep 1 i)).2.1 F1
  have F2 : FieldsAgreeNear (s.field η) (s'.field η')
      (cellCentreOnTorus R.params.side (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)))
      (cellCentreOnTorus R.params.side (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h)))
      (2 * R.params.side) :=
    fun b hb => F0 b ⟨offsetInBox_mono (by omega) hb.1, offsetInBox_mono (by omega) hb.2⟩
  have b0 : s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) =
      siteAtOffset (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) z₀ :=
    eq_of_toTorusSite_eq (e₀.trans (toTorusSite_siteAtOffset Y h z₀).symm)
  have b0' : s'.bases (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h)) =
      siteAtOffset (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h)) z₀ :=
    eq_of_toTorusSite_eq (e₀'.trans (toTorusSite_siteAtOffset Y' h z₀).symm)
  have hc := torusSiteInFrame_add_unitStep (L := R.params.side) Y h i
  have hc' := torusSiteInFrame_add_unitStep (L := R.params.side) Y' h i
  have b1 : s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h) +
        BlockAverages.unitStep 1 i) =
      siteAtOffset (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h) +
        BlockAverages.unitStep 1 i) z₁ := by
    have e : s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt (h + Pi.single i 1))) =
        siteAtOffset (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt (h + Pi.single i 1))) z₁ :=
      eq_of_toTorusSite_eq (e₁.trans (toTorusSite_siteAtOffset Y _ z₁).symm)
    exact (congrArg s.bases hc).trans
      (e.trans (congrArg (fun c : (stepBlockFrame R.params.side n).Cell => siteAtOffset c z₁) hc.symm))
  have b1' : s'.bases (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h) +
        BlockAverages.unitStep 1 i) =
      siteAtOffset (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h) +
        BlockAverages.unitStep 1 i) z₁ := by
    have e : s'.bases (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt (h + Pi.single i 1))) =
        siteAtOffset (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt (h + Pi.single i 1))) z₁ :=
      eq_of_toTorusSite_eq (e₁'.trans (toTorusSite_siteAtOffset Y' _ z₁).symm)
    exact (congrArg s'.bases hc').trans
      (e.trans (congrArg (fun c : (stepBlockFrame R.params.side n').Cell => siteAtOffset c z₁) hc'.symm))
  exact ((hloc R.params hfit hJ n n' h16 h16' (s.field η) (s'.field η')
    (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h))
    (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h))).2.2.2
    i 0 (readAtLevel (stepBlockFrame R.params.side n) 1 s.coarse)
    (readAtLevel (stepBlockFrame R.params.side n') 1 s'.coarse) s.bases s'.bases z₀ z₁ hz₀ hz₁
    b0 b0' b1 b1' F2 S0 S1).1
theorem bondFit_eq (hloc : BondKernelLocality) (hfit : R.params.Admissible)
    (hJ : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side) (h16 : 16 ≤ n) (h16' : 16 ≤ n')
    {s : ChartSetting R n} {s' : ChartSetting R n'}
    {Y : TorusSite n} {Y' : TorusSite n'} {m k : ℕ} {η : FreeCoords s.free} {η' : FreeCoords s'.free}
    (hf : s.free ⊆ chartBonds R.params.side n) (hag : SettingsAgreeNear s s' Y Y' m) (hk4 : 4 ≤ k) (hk : k ≤ m)
    (hnear : CoordsAgreeNear s s' Y Y' k η η') (h : Fin 4 → ℤ) (i : Fin 4) (hh : OffsetInBox 1 h)
    (hh' : OffsetInBox 1 (h + Pi.single i 1)) :
    bondFit R.params (s.field η) s.coarse s.bases (Y + siteOfInt h, i) =
      bondFit R.params (s'.field η') s'.coarse s'.bases (Y' + siteOfInt h, i) := by
  have hM := contourMean_eq hloc hfit hJ h16 h16' hf hag hk4 hk hnear h i hh hh'
  have h1m : 1 ≤ m := by omega
  have hV : s.coarse (Y + siteOfInt h) i = s'.coarse (Y' + siteOfInt h) i :=
    hag.coarse_agree (h, i) ⟨offsetInBox_mono h1m hh, offsetInBox_mono h1m hh'⟩
  have hr : readAtLevel (stepBlockFrame R.params.side n) 1 s.coarse
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (Y + siteOfInt h)) i =
      readAtLevel (stepBlockFrame R.params.side n') 1 s'.coarse
        (torusSiteInFrame (stepBlockFrame R.params.side n') 1 (Y' + siteOfInt h)) i := by
    rw [readAtLevel_one, readAtLevel_one, hV]
  unfold bondFit contourFit
  dsimp only
  rw [hM, hr]
theorem meanNorm_eq (hloc : BondKernelLocality) (hfit : R.params.Admissible)
    (hJ : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side) (h16 : 16 ≤ n) (h16' : 16 ≤ n')
    {s : ChartSetting R n} {s' : ChartSetting R n'}
    {Y : TorusSite n} {Y' : TorusSite n'} {m k : ℕ} {η : FreeCoords s.free} {η' : FreeCoords s'.free}
    (hf : s.free ⊆ chartBonds R.params.side n) (hag : SettingsAgreeNear s s' Y Y' m) (hk4 : 4 ≤ k) (hk : k ≤ m)
    (hnear : CoordsAgreeNear s s' Y Y' k η η') (h : Fin 4 → ℤ) (i : Fin 4) (hh : OffsetInBox 1 h)
    (hh' : OffsetInBox 1 (h + Pi.single i 1)) :
    meanNorm R.params (s.field η) s.bases (Y + siteOfInt h, i) =
      meanNorm R.params (s'.field η') s'.bases (Y' + siteOfInt h, i) := by
  have hM := contourMean_eq hloc hfit hJ h16 h16' hf hag hk4 hk hnear h i hh hh'
  unfold meanNorm
  dsimp only
  rw [hM]
end Means
section Free
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
theorem sum_ite_bondBlock_eq {M : Type} [AddCommMonoid M] (s : ChartSetting R n) (Y : TorusSite n)
    (g : s.free → M) :
    (open Classical in ∑ b : s.free, if bondBlock (R := R) b.1 = Y then g b else 0) =
      ∑ b ∈ s.freeBondsOf Y, g b := by
  classical
  unfold ChartSetting.freeBondsOf
  rw [Finset.sum_filter]
theorem sum_freeBondsOf_eq_sum_index {M : Type} [AddCommMonoid M] (hodd : Odd R.params.side)
    (s : ChartSetting R n) (Y : TorusSite n) (g : s.free → M) : ∑ b ∈ s.freeBondsOf Y, g b =
      open Classical in ∑ q ∈ centredCube R.params.side ×ˢ (Finset.univ : Finset (Fin 4)),
        if h : nearBond R.params.side Y (0, q.1, q.2) ∈ s.free then g ⟨_, h⟩ else 0 := by
  classical
  symm
  rw [← Finset.sum_filter_of_ne
    (p := fun q : (Fin 4 → ℤ) × Fin 4 => nearBond R.params.side Y (0, q.1, q.2) ∈ s.free)
    (fun q _ hne => by
      by_contra hc
      exact hne (dif_neg hc))]
  refine Finset.sum_bij (fun q hq => ⟨nearBond R.params.side Y (0, q.1, q.2), (Finset.mem_filter.mp hq).2⟩)
    ?_ ?_ ?_ ?_
  · intro q hq
    have hq1 := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    show parentBlock R.params.side (fineSite R.params.side Y 0 q.1) = Y
    rw [parentBlock_fineSite hodd Y 0 q.1 hq1]
    have z : (siteOfInt (0 : Fin 4 → ℤ) : TorusSite n) = 0 := by
      funext i
      simp [siteOfInt]
    rw [z, add_zero]
  · intro q hq q' hq' e
    have h1 := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
    have h2 := (Finset.mem_product.mp (Finset.mem_filter.mp hq').1).1
    have e1 := congrArg Subtype.val e
    simp only [nearBond, Prod.mk.injEq] at e1
    exact Prod.ext (fineSite_injective Y 0 hodd h1 h2 e1.1) e1.2
  · rintro ⟨⟨x, i⟩, hb⟩ hm
    have hY : parentBlock R.params.side x = Y := (Finset.mem_filter.mp hm).2
    obtain ⟨o, ho, e⟩ := exists_fineSite_of_parentBlock hodd Y x hY
    have hfree : nearBond R.params.side Y (0, o, i) ∈ s.free := by
      show (fineSite R.params.side Y 0 o, i) ∈ s.free
      rw [← e]
      exact hb
    refine ⟨(o, i), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ho, Finset.mem_univ _⟩, hfree⟩, ?_⟩
    apply Subtype.ext
    show (fineSite R.params.side Y 0 o, i) = (x, i)
    rw [← e]
  · intro q hq
    exact dif_pos (Finset.mem_filter.mp hq).2
theorem sum_freeBondsOf_eq {M : Type} [AddCommMonoid M] (hodd : Odd R.params.side)
    {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n} {Y' : TorusSite n'} {m : ℕ}
    (hag : SettingsAgreeNear s s' Y Y' m) (g : s.free → M) (g' : s'.free → M)
    (hg : ∀ o ∈ centredCube R.params.side, ∀ (i : Fin 4) (h : nearBond R.params.side Y (0, o, i) ∈ s.free)
      (h' : nearBond R.params.side Y' (0, o, i) ∈ s'.free), g ⟨_, h⟩ = g' ⟨_, h'⟩) :
    ∑ b ∈ s.freeBondsOf Y, g b = ∑ b ∈ s'.freeBondsOf Y', g' b := by
  classical
  rw [sum_freeBondsOf_eq_sum_index hodd, sum_freeBondsOf_eq_sum_index hodd]
  refine Finset.sum_congr rfl fun q hq => ?_
  have ho := (Finset.mem_product.mp hq).1
  have hnm : IsNearIndex R.params.side m (0, q.1, q.2) := ⟨offsetInBox_zero m, ho⟩
  by_cases hfr : nearBond R.params.side Y (0, q.1, q.2) ∈ s.free
  · have hfr' := (hag.free_iff _ hnm).mp hfr
    rw [dif_pos hfr, dif_pos hfr']
    exact hg q.1 ho q.2 hfr hfr'
  · have hfr' : nearBond R.params.side Y' (0, q.1, q.2) ∉ s'.free := fun h => hfr ((hag.free_iff _ hnm).mpr h)
    rw [dif_neg hfr, dif_neg hfr']
end Free
end BlockCosts
open BlockCosts in
theorem blockCostsAgree_holds (hsh : HoledShares.SharesOfHoledFieldsForget)
    (hz : HoledShares.LevelZeroShareIsLocal) (hloc : BondKernelLocality) :
    BlockCostsAgree := by
  intro T hT y R hy hR n n' _ _ hn hn' s s' Y Y' m k η η' hs hs' hag hk4 hkm hnear hb hb'
  have hfit : R.params.Admissible := hR ▸ hT.fits y hy
  have hLT : R.params.side = T.side := by rw [hR]; rfl
  have hσT : R.params.threshold = T.threshold := by rw [hR]; rfl
  have hJT : R.params.baseDepth = T.baseDepth := by rw [hR]; rfl
  have hC : ColdChain.ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam T.ρA T.σA T.cg T.N := by
    rw [hR]
    exact hT.chain
  have hσ : R.params.threshold ≤ T.σA := by
    rw [hσT]
    linarith [hT.σ_le, hT.σ_pos]
  have h4096 := hT.n₀_ge
  have h16 : 16 ≤ n := by omega
  have h16' : 16 ≤ n' := by omega
  have hodd : Odd R.params.side := hfit.L_odd
  have hJ : 11 * 2 ^ 12 * R.params.baseDepth < R.params.side := by
    rw [hLT, hJT]
    exact hT.L_gt
  have hL40 : 2 ^ 40 ≤ R.params.side := by
    rw [hLT]
    exact hT.L_ge
  have hf := hs.subset_chart
  have hside : 2 * m + 2 < n := hag.lt_extent
  have hside' : 2 * m + 2 < n' := hag.lt_extent'
  have hfields : ∀ o ∈ centredCube R.params.side, FieldsAgreeNear (s.field η) (s'.field η')
      (fineSite R.params.side Y 0 o) (fineSite R.params.side Y' 0 o)
      (R.params.side * k - R.params.side) := fun o ho =>
    fieldsAgreeNear_of_settings hodd (by omega) (by omega) hf hag (by omega) hkm hnear ho
  have hLk : R.params.side * 4 ≤ R.params.side * k := Nat.mul_le_mul_left _ hk4
  have hm16 : 2 ^ 16 + 4 ≤ R.params.side * k - R.params.side := by omega
  have hs1 : 2 * (R.params.side * k - R.params.side) + 2 < n * R.params.side := by
    have h1 : (2 * k + 3) * R.params.side ≤ n * R.params.side := Nat.mul_le_mul_right _ (by omega)
    have h2 : (2 * k + 3) * R.params.side = 2 * (R.params.side * k) + 3 * R.params.side := by ring
    omega
  have hs2 : 2 * (R.params.side * k - R.params.side) + 2 < n' * R.params.side := by
    have h1 : (2 * k + 3) * R.params.side ≤ n' * R.params.side := Nat.mul_le_mul_right _ (by omega)
    have h2 : (2 * k + 3) * R.params.side = 2 * (R.params.side * k) + 3 * R.params.side := by ring
    omega
  have hdv : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
  have hdv' : R.params.side ∣ n' * R.params.side := Dvd.intro_left n' rfl
  have hN0 : 0 < T.N 0 := hC.2.2.2.2.2.2.2.1 0
  have hshare : ∀ o ∈ centredCube R.params.side,
      |levelShare R.params.coupling R.params.side R.depth
          (Finset.univ \ thickening lumpRange (torusHotSites R.params (s.field η)))
          (fineSite R.params.side Y 0 o) (s.field η) -
        levelShare R.params.coupling R.params.side R.depth
          (Finset.univ \ thickening lumpRange (torusHotSites R.params (s'.field η')))
          (fineSite R.params.side Y' 0 o) (s'.field η')| ≤
        R.params.threshold ^ 2 * T.N 0 *
          Real.exp (-T.δ₁ * ((R.params.side * k - R.params.side - 2 ^ 16 : ℕ) : ℝ)) := by
    intro o ho
    have hF := hfields o ho
    have hbk := sameBlockPosition_fineSite R.params Y Y' 0 o
    obtain h0 | ⟨t, ht⟩ : R.depth = 0 ∨ ∃ t, R.depth = t + 1 := by
      cases hh : R.depth with
      | zero => exact Or.inl rfl
      | succ t => exact Or.inr ⟨t, rfl⟩
    · rw [h0, hz R.params hfit (n * R.params.side) (n' * R.params.side) (s.field η) (s'.field η') _ _ _
        hdv hdv' hm16 hs1 hs2 hF hbk, sub_self, abs_zero]
      positivity
    · rw [ht]
      exact (hsh T.δ₁ T.lam T.ρA T.σA T.cg T.N R.params hC hfit hσ t (n * R.params.side) (n' * R.params.side)
        (s.field η) (s'.field η') _ _ _ hdv (by omega) hs1 hs2 hF).1 hdv' (Or.inl hbk)
  have hz0 : ∀ (N : ℕ) [NeZero N] (Z : TorusSite N), Z + siteOfInt (0 : Fin 4 → ℤ) = Z := by
    intro N _ Z
    funext i
    simp [siteOfInt]
  have hzn : ∀ (N : ℕ) [NeZero N] (Z : TorusSite N) (i : Fin 4),
      Z + siteOfInt (-Pi.single i (1 : ℤ)) = Z - TorusFields.unitStep N i := by
    intro N _ Z i
    rw [unitStep_eq_siteOfInt, sub_eq_add_neg]
    congr 1
    funext l
    simp [siteOfInt]
  have hplus : ∀ i : Fin 4, OffsetInBox 1 ((0 : Fin 4 → ℤ) + Pi.single i 1) := fun i => by
    rw [zero_add]
    exact offsetInBox_single i
  have hminus : ∀ i : Fin 4, OffsetInBox 1 (-Pi.single i (1 : ℤ) + Pi.single i 1) := fun i => by
    rw [neg_add_cancel]
    exact offsetInBox_zero 1
  have hfits : ∀ i : Fin 4, bondFit R.params (s.field η) s.coarse s.bases (Y, i) =
      bondFit R.params (s'.field η') s'.coarse s'.bases (Y', i) := fun i => by
    have := bondFit_eq hloc hfit hJ h16 h16' hf hag hk4 hkm hnear 0 i (offsetInBox_zero 1) (hplus i)
    rwa [hz0, hz0] at this
  have hfitm : ∀ i : Fin 4, bondFit R.params (s.field η) s.coarse s.bases (Y - TorusFields.unitStep n i, i) =
      bondFit R.params (s'.field η') s'.coarse s'.bases (Y' - TorusFields.unitStep n' i, i) := fun i => by
    have := bondFit_eq hloc hfit hJ h16 h16' hf hag hk4 hkm hnear _ i (offsetInBox_neg_single i) (hminus i)
    rwa [hzn, hzn] at this
  have hsizes : ∀ i : Fin 4, meanNorm R.params (s.field η) s.bases (Y, i) =
      meanNorm R.params (s'.field η') s'.bases (Y', i) := fun i => by
    have := meanNorm_eq hloc hfit hJ h16 h16' hf hag hk4 hkm hnear 0 i (offsetInBox_zero 1) (hplus i)
    rwa [hz0, hz0] at this
  rw [← hLT, ← hσT]
  refine ⟨?_, ?_, ?_⟩
  · have e : s.blockCostAt Y η - s'.blockCostAt Y' η' = ∑ o ∈ centredCube R.params.side,
        (levelShare R.params.coupling R.params.side R.depth
          (Finset.univ \ thickening lumpRange (torusHotSites R.params (s.field η)))
          (fineSite R.params.side Y 0 o) (s.field η) -
        levelShare R.params.coupling R.params.side R.depth
          (Finset.univ \ thickening lumpRange (torusHotSites R.params (s'.field η')))
          (fineSite R.params.side Y' 0 o) (s'.field η')) := by
      unfold ChartSetting.blockCostAt blockCost
      rw [sum_sitesInBlocks hodd, sum_sitesInBlocks hodd, Finset.sum_sub_distrib]
      simp only [hfits, hfitm]
      ring
    rw [e]
    calc _ ≤ ∑ o ∈ centredCube R.params.side, |levelShare R.params.coupling R.params.side R.depth
          (Finset.univ \ thickening lumpRange (torusHotSites R.params (s.field η)))
          (fineSite R.params.side Y 0 o) (s.field η) -
        levelShare R.params.coupling R.params.side R.depth
          (Finset.univ \ thickening lumpRange (torusHotSites R.params (s'.field η')))
          (fineSite R.params.side Y' 0 o) (s'.field η')| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ (centredCube R.params.side).card • (R.params.threshold ^ 2 * T.N 0 *
          Real.exp (-T.δ₁ * ((R.params.side * k - R.params.side - 2 ^ 16 : ℕ) : ℝ))) :=
          Finset.sum_le_card_nsmul _ _ _ hshare
      _ = _ := by
          rw [card_centredCube hodd, nsmul_eq_mul]
          push_cast
          ring
  · unfold ChartSetting.logJacobianAt ChartSetting.logJacobian
    have e1 : ∀ i : Fin 4, logPartitionGap (R.params.coupling * R.coupling *
          meanNorm R.params (s.field η) s.bases (Y, i)) =
        logPartitionGap (R.params.coupling * R.coupling * meanNorm R.params (s'.field η') s'.bases (Y', i)) :=
      fun i => by rw [hsizes]
    simp only [e1]
    congr 1
    rw [sum_ite_bondBlock_eq s Y fun b => Real.log (haarLogDensity (toCoords (s.frame b.1) + η b)),
      sum_ite_bondBlock_eq s' Y' fun b => Real.log (haarLogDensity (toCoords (s'.frame b.1) + η' b))]
    refine sum_freeBondsOf_eq hodd hag _ _ fun o ho i h h' => ?_
    have hnm : IsNearIndex R.params.side m (0, o, i) := ⟨offsetInBox_zero m, ho⟩
    have hnk : IsNearIndex R.params.side k (0, o, i) := ⟨offsetInBox_zero k, ho⟩
    have h1 := hnear _ hnk
    simp only [ChartSetting.coordsByIndex] at h1
    rw [dif_pos h, dif_pos h'] at h1
    show Real.log (haarLogDensity (toCoords (s.frame (nearBond R.params.side Y (0, o, i))) + η ⟨_, h⟩)) =
      Real.log (haarLogDensity (toCoords (s'.frame (nearBond R.params.side Y' (0, o, i))) + η' ⟨_, h'⟩))
    rw [hag.frame_eq _ hnm h, h1]
  · rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]
    exact sum_freeBondsOf_eq hodd hag _ _ fun _ _ _ _ _ => rfl
end ClusterExpansionOfAStep
end YangMills.Construction
end
