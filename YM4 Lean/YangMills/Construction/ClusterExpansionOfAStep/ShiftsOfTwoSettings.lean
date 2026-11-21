import YangMills.Construction.ClusterExpansionOfAStep.AdmissionReadsVOnItsHullProof
import YangMills.Construction.ClusterExpansionOfAStep.CalculusOfASplit
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields StepSettings BlockOffsets TorusLumps StepCosts
namespace SettingShifts
set_option linter.unusedSectionVars false
section Blocks
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n']
theorem fineSite_eq_add_siteOfInt (L : ℕ) [NeZero L] (Z : TorusSite n) (h o : Fin 4 → ℤ) :
    fineSite L Z h o = fineSite L (Z + siteOfInt h) 0 o := by
  show siteOfInt (blockPoint L (fun i => ((Z i).cast : ℤ) + h i) o) = _
  rw [siteOfInt_blockPoint (NeZero.ne L), siteOfInt_cast_add]
theorem fineSite_add_siteOfInt (L : ℕ) [NeZero L] (Z : TorusSite n) (h h₂ o : Fin 4 → ℤ) :
    fineSite L (Z + siteOfInt h) h₂ o = fineSite L Z (h + h₂) o := by
  rw [fineSite_eq_add_siteOfInt L _ h₂, fineSite_eq_add_siteOfInt L Z (h + h₂), siteOfInt_add, add_assoc]
theorem nearBond_add_siteOfInt (L : ℕ) [NeZero L] (Z : TorusSite n) (h h₂ o : Fin 4 → ℤ) (i : Fin 4) :
    nearBond L (Z + siteOfInt h) (h₂, o, i) = nearBond L Z (h + h₂, o, i) := by
  simp only [nearBond, fineSite_add_siteOfInt]
theorem offsetInBox_add {m j : ℕ} {h h₂ : Fin 4 → ℤ} (hh : ∀ l, |h l| + j ≤ m) (h2 : OffsetInBox j h₂) :
    OffsetInBox m (h + h₂) := by
  intro l
  have a := hh l
  have b := h2 l
  have c : |(h + h₂) l| ≤ |h l| + |h₂ l| := abs_add_le _ _
  omega
theorem settingsAgreeNear_shift {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n}
    {Y' : TorusSite n'} {m j : ℕ} {h : Fin 4 → ℤ} (hag : SettingsAgreeNear s s' Y Y' m)
    (hh : ∀ l, |h l| + j ≤ m) :
    SettingsAgreeNear s s' (Y + siteOfInt h) (Y' + siteOfInt h) j := by
  have hjm : j ≤ m := by
    have a := hh 0
    have b := abs_nonneg (h 0)
    omega
  refine ⟨by have := hag.lt_extent; omega, by have := hag.lt_extent'; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    have hb2 : OffsetInBox m ((h + b.1) + Pi.single b.2 1) := by
      rw [add_assoc]
      exact offsetInBox_add hh hb.2
    have := hag.coarse_agree (h + b.1, b.2) ⟨offsetInBox_add hh hb.1, hb2⟩
    simpa only [bondFrom, siteOfInt_add, add_assoc] using this
  · rintro ⟨h₂, o, i⟩ hq
    rw [nearBond_add_siteOfInt, nearBond_add_siteOfInt]
    exact hag.free_iff _ ⟨offsetInBox_add hh hq.1, hq.2⟩
  · rintro ⟨h₂, o, i⟩ hq hf
    rw [nearBond_add_siteOfInt] at hf
    have := hag.fine_eq (h + h₂, o, i) ⟨offsetInBox_add hh hq.1, hq.2⟩ hf
    simpa only [nearBond, fineSite_add_siteOfInt] using this
  · rintro ⟨h₂, o, i⟩ hq hf
    rw [nearBond_add_siteOfInt] at hf
    rw [nearBond_add_siteOfInt, nearBond_add_siteOfInt]
    exact hag.frame_eq _ ⟨offsetInBox_add hh hq.1, hq.2⟩ hf
  · intro h₂ o hb ho
    rw [fineSite_add_siteOfInt, fineSite_add_siteOfInt]
    exact hag.support_iff _ o (offsetInBox_add hh hb) ho
  · intro h₂ o hz hz' hb ho
    have e := fineSite_add_siteOfInt R.params.side Y h h₂ o
    have e' := fineSite_add_siteOfInt R.params.side Y' h h₂ o
    have h1 : fineSite R.params.side Y (h + h₂) o ∈ s.support := e ▸ hz
    have h2 : fineSite R.params.side Y' (h + h₂) o ∈ s'.support := e' ▸ hz'
    have := hag.labelling_eq _ o h1 h2 (offsetInBox_add hh hb) ho
    have c1 : s.labelling ⟨_, hz⟩ = s.labelling ⟨_, h1⟩ := by congr 2
    have c2 : s'.labelling ⟨_, hz'⟩ = s'.labelling ⟨_, h2⟩ := by congr 2
    rw [c1, c2, this]
  · intro h₂ hb
    obtain ⟨o, ho, a, b⟩ := hag.bases_match _ (offsetInBox_add hh hb)
    refine ⟨o, ho, ?_, ?_⟩
    · rw [fineSite_add_siteOfInt, add_assoc, ← siteOfInt_add]
      exact a
    · rw [fineSite_add_siteOfInt, add_assoc, ← siteOfInt_add]
      exact b
theorem coordsByIndex_congr (s : ChartSetting R n) {Y Z : TorusSite n} (η : FreeCoords s.free)
    {q q₂ : NearBondIndex} (h : nearBond R.params.side Y q = nearBond R.params.side Z q₂) :
    s.coordsByIndex Y η q = s.coordsByIndex Z η q₂ := by
  simp only [ChartSetting.coordsByIndex, h]
theorem coordsAgreeNear_shift {s : ChartSetting R n} {s' : ChartSetting R n'} {Y : TorusSite n}
    {Y' : TorusSite n'} {k j : ℕ} {h : Fin 4 → ℤ} {η : FreeCoords s.free} {η' : FreeCoords s'.free}
    (hn : CoordsAgreeNear s s' Y Y' k η η') (hh : ∀ l, |h l| + j ≤ k) :
    CoordsAgreeNear s s' (Y + siteOfInt h) (Y' + siteOfInt h) j η η' := by
  rintro ⟨h₂, o, i⟩ hq
  rw [coordsByIndex_congr s η (nearBond_add_siteOfInt R.params.side Y h h₂ o i),
    coordsByIndex_congr s' η' (nearBond_add_siteOfInt R.params.side Y' h h₂ o i)]
  exact hn _ ⟨offsetInBox_add hh hq.1, hq.2⟩
theorem eq_of_siteOfInt_eq {k : ℕ} {h h₂ : Fin 4 → ℤ} (hk : 2 * k + 2 < n) (a : OffsetInBox k h)
    (b : OffsetInBox k h₂) (e : (siteOfInt h : TorusSite n) = siteOfInt h₂) : h = h₂ := by
  funext i
  have h1 := congrFun e i
  simp only [siteOfInt] at h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  have a' := abs_le.mp (a i)
  have b' := abs_le.mp (b i)
  have h3 : |h₂ i - h i| < (n : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd h1 h3
  omega
theorem eq_of_nearBond_eq (hodd : Odd R.params.side) {Y : TorusSite n} {k : ℕ} {q q₂ : NearBondIndex}
    (hk : 2 * k + 2 < n) (a : IsNearIndex R.params.side k q) (b : IsNearIndex R.params.side k q₂)
    (e : nearBond R.params.side Y q = nearBond R.params.side Y q₂) : q = q₂ := by
  obtain ⟨h, o, i⟩ := q
  obtain ⟨h₂, o₂, i₂⟩ := q₂
  simp only [nearBond, Prod.mk.injEq] at e
  obtain ⟨e1, rfl⟩ := e
  have b1 := parentBlock_fineSite hodd Y h o a.2
  have b2 := parentBlock_fineSite hodd Y h₂ o₂ b.2
  rw [e1, b2] at b1
  have hh : h = h₂ := eq_of_siteOfInt_eq hk a.1 b.1 (add_left_cancel b1).symm
  subst hh
  have h3 : o = o₂ := fineSite_injective Y h hodd a.2 b.2 e1
  rw [h3]
theorem coordsAgreeNear_update (hodd : Odd R.params.side) {s : ChartSetting R n} {s' : ChartSetting R n'}
    {Y : TorusSite n} {Y' : TorusSite n'} {k : ℕ} {η : FreeCoords s.free} {η' : FreeCoords s'.free}
    {q₀ : NearBondIndex} {hb : nearBond R.params.side Y q₀ ∈ s.free}
    {hb' : nearBond R.params.side Y' q₀ ∈ s'.free}
    (hk : 2 * k + 2 < n) (hk' : 2 * k + 2 < n') (hfree : ∀ q, IsNearIndex R.params.side k q →
      (nearBond R.params.side Y q ∈ s.free ↔ nearBond R.params.side Y' q ∈ s'.free))
    (hn : CoordsAgreeNear s s' Y Y' k η η') (h0 : IsNearIndex R.params.side k q₀)
    (v : EuclideanSpace ℝ (Fin 3)) :
    CoordsAgreeNear s s' Y Y' k (Function.update η ⟨_, hb⟩ v) (Function.update η' ⟨_, hb'⟩ v) := by
  intro q hq
  have base := hn q hq
  by_cases hq0 : q = q₀
  · subst hq0
    simp only [ChartSetting.coordsByIndex, dif_pos hb, dif_pos hb', Function.update_self]
  · have ne : nearBond R.params.side Y q ≠ nearBond R.params.side Y q₀ :=
      fun e => hq0 (eq_of_nearBond_eq hodd hk hq h0 e)
    have ne' : nearBond R.params.side Y' q ≠ nearBond R.params.side Y' q₀ :=
      fun e => hq0 (eq_of_nearBond_eq hodd hk' hq h0 e)
    simp only [ChartSetting.coordsByIndex] at base ⊢
    by_cases hf : nearBond R.params.side Y q ∈ s.free
    · have hf' := (hfree q hq).mp hf
      rw [dif_pos hf, dif_pos hf'] at base ⊢
      rw [Function.update_of_ne (fun e => ne (congrArg Subtype.val e)),
        Function.update_of_ne (fun e => ne' (congrArg Subtype.val e))]
      exact base
    · have hf' : nearBond R.params.side Y' q ∉ s'.free := fun e => hf ((hfree q hq).mpr e)
      rw [dif_neg hf, dif_neg hf']
theorem toTorusSite_siteOfCoords (L : ℕ) [NeZero L] (Z : TorusSite n) (o : Fin 4 → ℤ) :
    toTorusSite (n * L) (siteOfCoords (F := stepBlockFrame L n) 0
      (fun k => (L : ℤ) ^ 1 * siteCoords (torusSiteInFrame (stepBlockFrame L n) 1 Z) k + o k)) =
      fineSite L Z 0 o := by
  have e1 : (siteOfInt (fun k => siteCoords (torusSiteInFrame (stepBlockFrame L n) 1 Z) k) : TorusSite n) =
      Z := by
    funext i
    simp only [siteOfInt, torusSiteInFrame]
    have := siteCoords_siteOfCoords_one (L := L) (n := n) (fun i => ((Z i).cast : ℤ)) i
    show (((siteCoords (siteOfCoords (F := stepBlockFrame L n) 1 (fun i => ((Z i).cast : ℤ))) i : ℤ)) :
      ZMod n) = Z i
    rw [this]
    simp
  funext i
  simp only [toTorusSite]
  rw [siteCoords_siteOfCoords_zero]
  rw [ZMod.intCast_mod]
  have h2 := siteOfInt_blockPoint (n := n) (NeZero.ne L)
    (fun k => siteCoords (torusSiteInFrame (stepBlockFrame L n) 1 Z) k) o
  rw [e1] at h2
  have := congrFun h2 i
  simpa [siteOfInt, blockPoint] using this
theorem exists_bases_eq_fineSite (s : ChartSetting R n) (hs : s.IsAdmissible) (Z : TorusSite n) :
    ∃ o ∈ centredCube R.params.side,
      toTorusSite (n * R.params.side) (s.bases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 Z)) =
        fineSite R.params.side Z 0 o := by
  have hb := hs.isBaseChoice (torusSiteInFrame (stepBlockFrame R.params.side n) 1 Z)
  by_cases hc : nearbyLumps (stepHotLumps R.params s.fine)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 Z) = ∅ ∨
      IsCrowded R.params.baseDepth (stepHotLumps R.params s.fine)
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 Z)
  · have e := hb.1 hc
    have h0 : (0 : Fin 4 → ℤ) ∈ centredCube R.params.side := by
      rw [_root_.YangMills.Construction.BlockOffsets.mem_centredCube_iff]
      intro i
      have : (0 : ℤ) ≤ ((R.params.side : ℤ) - 1) / 2 := by
        have : 1 ≤ (R.params.side : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne R.params.side)
        omega
      simpa using this
    refine ⟨0, h0, ?_⟩
    rw [e]
    have := toTorusSite_siteOfCoords (n := n) R.params.side Z 0
    simpa [cellCentre, stepBlockFrame, BlockFrame.top] using this
  · obtain ⟨hu, _⟩ := hb.2 hc
    unfold sitesBelow at hu
    obtain ⟨o, ho, e⟩ := Finset.mem_image.mp hu
    refine ⟨o, by simpa [stepBlockFrame, BlockFrame.top] using ho, ?_⟩
    rw [← e]
    have := toTorusSite_siteOfCoords (n := n) R.params.side Z o
    simpa [stepBlockFrame, BlockFrame.top] using this
theorem settingsAgreeNear_refl (s : ChartSetting R n) (hs : s.IsAdmissible) (Z : TorusSite n) (j : ℕ)
    (hj : 2 * j + 2 < n) : SettingsAgreeNear s s Z Z j := by
  refine ⟨hj, hj, fun _ _ => rfl, fun _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ _ => rfl, ?_⟩
  intro h _
  obtain ⟨o, ho, e⟩ := exists_bases_eq_fineSite s hs (Z + siteOfInt h)
  refine ⟨o, ho, ?_, ?_⟩ <;> rw [e, fineSite_eq_add_siteOfInt R.params.side Z h]
end Blocks
section Small
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem coordNorm_eq_norm (v : EuclideanSpace ℝ (Fin 3)) : coordNorm v = ‖v‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coordNorm_eq_norm <;> assumption
theorem two_mul_supDist_le (x y : TorusSite n) : 2 * supDist x y ≤ n := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.HullLocality.two_mul_supDist_le <;> assumption
theorem inBalls_update (s : ChartSetting R n) {η : FreeCoords s.free} (hη : s.InBalls η) (b : s.free)
    {v : EuclideanSpace ℝ (Fin 3)} (hv : coordNorm v ≤ R.ballRadius) : s.InBalls (Function.update η b v) := by
  intro b'
  by_cases h : b' = b
  · subst h
    simpa using hv
  · rw [Function.update_of_ne h]
    exact hη b'
end Small
end SettingShifts
end YangMills.Construction
end
