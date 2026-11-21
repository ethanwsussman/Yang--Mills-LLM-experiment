import YangMills.Construction.LawByMomentsOfTheFlow.CoordinatesOnACircle
import YangMills.Construction.LawByMomentsOfTheFlow.FarLevelNearTheScale
import YangMills.Construction.LawByMomentsOfTheFlow.PlacesOfTheSitesOfASupport
import YangMills.Construction.LawByMomentsOfTheFlow.SitesAtTheFarLevelOfTheScale
import YangMills.Construction.LawByMomentsOfTheFlow.WeightsAndSitesBelowTheScale
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open TorusLumps RenormalizationStepParameters TorusFields LevelTestFunctions TestFunctions
private theorem forAllParameters_combine {Q₁ Q₂ Q₃ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁)
    (h₂ : ForAllParameters Q₂) (h : ∀ Λ : MomentParameters, Odd Λ.stepParams.side → Q₁ Λ → Q₂ Λ → Q₃ Λ) :
    ForAllParameters Q₃ := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := h₁ a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := h₂ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hL hLge Tb hTa hTL hD hCS hOn hrt hC Kr hKr
  obtain ⟨y₁, G₁⟩ := H₁ L hL ((le_max_left _ _).trans hLge) Tb hTa hTL hD hCS hOn
    (hrt.trans (min_le_left _ _)) ((le_max_left _ _).trans hC) Kr hKr
  obtain ⟨y₂, G₂⟩ := H₂ L hL ((le_max_right _ _).trans hLge) Tb hTa hTL hD hCS hOn
    (hrt.trans (min_le_right _ _)) ((le_max_right _ _).trans hC) Kr hKr
  refine ⟨max y₁ y₂, fun y hy hRet hRow g hg hyg k _ hk2 hk8 R d hd => ?_⟩
  refine h _ ?_ (G₁ y ((le_max_left _ _).trans hy) hRet hRow g hg hyg k hk2 hk8 R d hd)
    (G₂ y ((le_max_right _ _).trans hy) hRet hRow g hg hyg k hk2 hk8 R d hd)
  show Odd Tb.side
  rw [hTL]
  exact hL
private theorem distFromCenter_le_of_mem {k : ℕ}
    (hsh : ∀ (c : ℝ), 0 < c → ∀ v : ℝ, |circleRep c v| ≤ |v|)
    (hsub : ∀ (c : ℝ), 0 < c → ∀ u v : ℝ, |circleRep c (u + v)| ≤ |circleRep c u| + |circleRep c v|)
    (hP : supportSitesLocationStatement) {L : ℕ} [NeZero L] (hL : Odd L) (P : LevelData k) {R d : ℝ}
    (hF : P.SupAdmissible L R d) {u : ℕ} (hu : u ≤ P.windowLevel) (i : Fin k) {y : TorusSite (P.sideAt L u)}
    (hy : y ∈ P.supportSites L u i) :
    P.distFromCenter L u y ≤ 1 / 2 + |R| * ((L : ℝ) ^ P.scaleLevel / (L : ℝ) ^ u) := by
  obtain ⟨z, hz, hzc⟩ := (hP L hL k P u hu i).1 y hy
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hT : (0 : ℝ) < (P.period L : ℝ) := by
    have : 0 < P.period L := Nat.pos_of_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (NeZero.ne L)))
    exact_mod_cast this
  have hzb : ∀ a, |z a| ≤ R := hF.isSupTestFamily.abs_coord_le i z (subset_tsupport _ hz)
  have hM : (0 : ℝ) < (L : ℝ) ^ P.windowLevel := by positivity
  have hU : (0 : ℝ) < (L : ℝ) ^ u := by positivity
  unfold LevelData.distFromCenter
  refine ciSup_le fun a => ?_
  have h1 := hsub _ hT (((y a).val : ℝ) * (L : ℝ) ^ u / (L : ℝ) ^ P.windowLevel - P.center a -
    (L : ℝ) ^ P.scaleLevel / (L : ℝ) ^ P.windowLevel * z a)
    ((L : ℝ) ^ P.scaleLevel / (L : ℝ) ^ P.windowLevel * z a)
  rw [sub_add_cancel] at h1
  have h2 := hzc a
  have h3 : |circleRep (P.period L) ((L : ℝ) ^ P.scaleLevel / (L : ℝ) ^ P.windowLevel * z a)| ≤
      (L : ℝ) ^ P.scaleLevel / (L : ℝ) ^ P.windowLevel * |R| := by
    refine (hsh _ hT _).trans ?_
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left ((hzb a).trans (le_abs_self _)) (by positivity)
  have h4 := h1.trans (add_le_add h2 h3)
  have h5 : |circleRep (P.period L) (((y a).val : ℝ) * (L : ℝ) ^ u / (L : ℝ) ^ P.windowLevel - P.center a)| *
      (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ u ≤
      ((L : ℝ) ^ u / (2 * (L : ℝ) ^ P.windowLevel) +
        (L : ℝ) ^ P.scaleLevel / (L : ℝ) ^ P.windowLevel * |R|) *
      (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ u :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hM.le) hU.le
  refine h5.trans (le_of_eq ?_)
  field_simp
theorem farLevelSupportSites_of_parts (hC : CircleRepProperties)
    (hP : supportSitesLocationStatement) (hF : farLevelNearScaleStatement)
    (hW : weightsSitesBelowScaleStatement) : farLevelSupportSitesStatement := by
  obtain ⟨-, hsh, hsub, -, -, -, -⟩ := hC
  unfold farLevelNearScaleStatement ForAllPoints at hF
  unfold weightsSitesBelowScaleStatement ForAllPoints at hW
  unfold farLevelSupportSitesStatement ForAllPoints
  refine forAllParameters_combine hF hW ?_
  rintro Λ hodd ⟨C₁, c₁, X₁, -, -, H₁⟩ ⟨C₂, c₂, X₂, -, -, H₂⟩
  obtain ⟨A, hAd⟩ : ∃ A : ℝ, A = |C₂ 0| * C₁ 0 ^ 4 := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, B = |Λ.R| * |C₁ 0| := ⟨_, rfl⟩
  have hA : 0 ≤ A := by
    rw [hAd]
    positivity
  have hB : 0 ≤ B := by
    rw [hBd]
    positivity
  refine ⟨fun _ => A + B + 2, 1, Λ.floor, one_pos, le_rfl, fun S => ?_⟩
  obtain ⟨hts, hLs, -⟩ := H₁ S
  have hLpos : (0 : ℝ) < Λ.stepParams.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Λ.stepParams.side)
  have hL1 : (1 : ℝ) ≤ Λ.stepParams.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Λ.stepParams.side)
  have hZ : (0 : ℝ) < (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - S.lastSeparated) := by positivity
  have hr : (1 : ℝ) ≤ (S.range : ℝ) := by
    rcases Nat.eq_zero_or_pos S.range with h0 | h0
    · rw [h0] at hLs
      simp only [Nat.cast_zero, mul_zero] at hLs
      linarith
    · exact_mod_cast h0
  have hZr : (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - S.lastSeparated) ≤ |C₁ 0| * (S.range : ℝ) :=
    hLs.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
  have hfar : ∀ u, S.lastSeparated ≤ u → u ≤ S.data.windowLevel → ∀ (i : Fin Λ.k),
      ∀ y ∈ S.data.supportSites Λ.stepParams.side u i,
      S.data.distFromCenter Λ.stepParams.side u y ≤ 1 / 2 + B * (S.range : ℝ) := by
    intro u htu huK i y hy
    refine (distFromCenter_le_of_mem hsh hsub hP hodd S.data S.supAdmissible huK i hy).trans ?_
    have hU : (0 : ℝ) < (Λ.stepParams.side : ℝ) ^ u := by positivity
    have hsplit : (Λ.stepParams.side : ℝ) ^ S.data.scaleLevel =
        (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - S.lastSeparated) *
          (Λ.stepParams.side : ℝ) ^ S.lastSeparated := by
      rw [← pow_add, Nat.sub_add_cancel hts]
    have hle : (Λ.stepParams.side : ℝ) ^ S.lastSeparated ≤ (Λ.stepParams.side : ℝ) ^ u :=
      pow_le_pow_right₀ hL1 htu
    have hq : (Λ.stepParams.side : ℝ) ^ S.data.scaleLevel / (Λ.stepParams.side : ℝ) ^ u ≤
        (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - S.lastSeparated) := by
      rw [div_le_iff₀ hU, hsplit]
      exact mul_le_mul_of_nonneg_left hle hZ.le
    have h1 : |Λ.R| * ((Λ.stepParams.side : ℝ) ^ S.data.scaleLevel / (Λ.stepParams.side : ℝ) ^ u) ≤
        B * (S.range : ℝ) := by
      rw [hBd, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hq.trans hZr) (abs_nonneg _)
    linarith
  obtain ⟨b, hbd⟩ : ∃ b : ℕ, b = ⌈1 / 2 + B * (S.range : ℝ)⌉₊ := ⟨_, rfl⟩
  have hb1 : 1 / 2 + B * (S.range : ℝ) ≤ (b : ℝ) := by
    rw [hbd]
    exact Nat.le_ceil _
  have hb2 : (b : ℝ) < 1 / 2 + B * (S.range : ℝ) + 1 := by
    rw [hbd]
    exact Nat.ceil_lt_add_one (by positivity)
  have hbmem : b ∈ {b : ℕ | ∀ u, S.lastSeparated ≤ u → u ≤ S.data.windowLevel → ∀ (i : Fin Λ.k),
      ∀ y ∈ S.data.supportSites Λ.stepParams.side u i, S.data.distFromCenter Λ.stepParams.side u y ≤ b} :=
    fun u h1 h2 i y hy => (hfar u h1 h2 i y hy).trans hb1
  have hrdb : S.radius ≤ b := Nat.sInf_le hbmem
  have hrd : S.radius ∈ {b : ℕ | ∀ u, S.lastSeparated ≤ u → u ≤ S.data.windowLevel → ∀ (i : Fin Λ.k),
      ∀ y ∈ S.data.supportSites Λ.stepParams.side u i, S.data.distFromCenter Λ.stepParams.side u y ≤ b} :=
    Nat.sInf_mem ⟨b, hbmem⟩
  refine ⟨fun i => ?_, ?_, hrd⟩
  · have h1 := (H₂ S S.lastSeparated hts i).2
    have h2 : (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - S.lastSeparated)) =
        ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - S.lastSeparated)) ^ 4 := by
      rw [mul_comm, pow_mul]
    have h3 : ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - S.lastSeparated)) ^ 4 ≤
        (C₁ 0 * (S.range : ℝ)) ^ 4 :=
      pow_le_pow_left₀ hZ.le hLs 4
    have h4 : C₂ 0 * (Λ.stepParams.side : ℝ) ^ (4 * (S.data.scaleLevel - S.lastSeparated)) ≤
        A * (S.range : ℝ) ^ 4 := by
      rw [h2, hAd]
      calc C₂ 0 * ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - S.lastSeparated)) ^ 4
          ≤ |C₂ 0| * ((Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - S.lastSeparated)) ^ 4 :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |C₂ 0| * (C₁ 0 * (S.range : ℝ)) ^ 4 := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ = |C₂ 0| * C₁ 0 ^ 4 * (S.range : ℝ) ^ 4 := by ring
    have h5 : 0 ≤ (B + 2) * (S.range : ℝ) ^ 4 := by positivity
    show ((S.data.supportSites Λ.stepParams.side S.lastSeparated i).card : ℝ) ≤ (A + B + 2) * (S.range : ℝ) ^ 4
    linarith [h1.trans h4]
  · have h1 : (S.radius : ℝ) ≤ (b : ℝ) := by exact_mod_cast hrdb
    have h2 : 0 ≤ A * (S.range : ℝ) := by positivity
    show (S.radius : ℝ) ≤ (A + B + 2) * (S.range : ℝ)
    nlinarith
end YangMills.Construction.MomentLaw
end
