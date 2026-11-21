import YangMills.Construction.ClusterExpansionOfAStep.LocalityOfTheDensities
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheDensities
import YangMills.Construction.ClusterExpansionOfAStep.TwoRatiosOfSettings
import YangMills.Construction.ClusterExpansionOfAStep.TwoSumsOnABox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open StepSettings TorusFields RenormalizationStepParameters TorusLumps StepLocality
theorem logMassRatiosClose_of_locality (hLoc : DensityLocality) (hSum : LogIntegralEqSumActivity)
    (hTwo : TwoTorusSumsBound) : LogMassRatiosClose := by
  obtain ⟨r₁, hr₁, h₁⟩ := hLoc
  obtain ⟨r₂, hr₂, h₂⟩ := hSum
  refine ⟨fun c => min (r₁ c) (r₂ c), fun c => lt_min (hr₁ c) (hr₂ c), fun T hT hle => ?_⟩
  obtain ⟨y₁, hy₁⟩ := h₁ T hT (hle.trans (min_le_left _ _))
  obtain ⟨y₂, hy₂⟩ := h₂ T hT (hle.trans (min_le_right _ _))
  refine ⟨max y₁ y₂, fun y hy R hR n n' _ _ hn hn' sa sb sa' sb' H Y Y' d m ha hb ha' hb' hH hd hdr hmr hP => ?_⟩
  have hyy₁ : y₁ ≤ y := (le_max_left _ _).trans hy
  have hyy₂ : y₂ ≤ y := (le_max_right _ _).trans hy
  have hc : 0 < T.rt / 2 ^ 5 := div_pos hT.rt_pos (by norm_num)
  have L := hy₁ y hyy₁ R hR
  have S := hy₂ y hyy₂ R hR
  have ha1 := S n hn sa ha
  have hb1 := S n hn sb hb
  have ha2 := S n' hn' sa' ha'
  have hb2 := S n' hn' sb' hb'
  have hfar : ∀ (p : ℕ) [NeZero p] (s₁ s₂ : ChartSetting R p) (Z : TorusSite p), T.n₀ ≤ p → s₁.IsAdmissible →
      s₂.IsAdmissible →
      (∀ (z : TorusSite p) (k : ℕ), (∀ h ∈ H, k + 2 ≤ supDist z (Z + siteOfInt h)) →
        SettingsAgreeNear s₁ s₂ z z k) →
      ∀ (z : TorusSite p) (D : ℕ), d ≤ D → (∀ h ∈ H, D ≤ supDist z (Z + siteOfInt h)) →
        |s₂.blockActivity T.lam z - s₁.blockActivity T.lam z| ≤ Real.exp (-(T.rt / 2 ^ 5 * ((D : ℝ) - 2))) := by
    intro p _ s₁ s₂ Z hp hs₁ hs₂ hfa z D hD' hall
    have hD2 : 2 ≤ D := hd.trans hD'
    have hcast : ((D - 2 : ℕ) : ℝ) = (D : ℝ) - 2 := by
      rw [Nat.cast_sub hD2]
      norm_num
    have hag : SettingsAgreeNear s₁ s₂ z z (D - 2) := hfa z (D - 2) fun h hh => by
      have := hall h hh
      omega
    have hge : (R.range : ℝ) / (4 * R.params.side) ≤ ((D - 2 : ℕ) : ℝ) := by
      rw [hcast]
      have : (d : ℝ) ≤ D := by exact_mod_cast hD'
      linarith
    have h5 := (L p p hp hp s₁ s₂ z z (D - 2) hs₁ hs₂).1 hge hag
    rw [hcast] at h5
    rw [abs_sub_comm]
    have e : T.rt * ((D : ℝ) - 2) / 2 ^ 5 = T.rt / 2 ^ 5 * ((D : ℝ) - 2) := by ring
    rwa [e] at h5
  have hnear : ∀ h ∈ H, ∀ g, OffsetInBox (d - 1) g →
      |(sb.blockActivity T.lam (Y + siteOfInt (h + g)) - sa.blockActivity T.lam (Y + siteOfInt (h + g))) -
        (sb'.blockActivity T.lam (Y' + siteOfInt (h + g)) - sa'.blockActivity T.lam (Y' + siteOfInt (h + g)))| ≤
      2 * Real.exp (-(T.rt / 2 ^ 5 * m)) := by
    intro h hh g hg
    have e1 := (L n n' hn hn' sa sa' _ _ m ha ha').1 hmr (hP.left_agree_near h hh g hg)
    have e2 := (L n n' hn hn' sb sb' _ _ m hb hb').1 hmr (hP.right_agree_near h hh g hg)
    have e : T.rt * (m : ℝ) / 2 ^ 5 = T.rt / 2 ^ 5 * m := by ring
    rw [e] at e1 e2
    rw [abs_le] at e1 e2 ⊢
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  have key := hTwo n n' (fun z => sb.blockActivity T.lam z - sa.blockActivity T.lam z)
    (fun z => sb'.blockActivity T.lam z - sa'.blockActivity T.lam z) H Y Y' d (T.rt / 2 ^ 5)
    (2 * Real.exp (-(T.rt / 2 ^ 5 * m))) hc (by positivity) (by omega) hH hP.offsets_injective
    hP.offsets_injective'
    (hfar n sa sb Y hn ha hb hP.agree_away) (hfar n' sa' sb' Y' hn' ha' hb' hP.agree_away') hnear
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← ha1, ← hb1, ← ha2, ← hb2] at key
  exact key
end YangMills.Construction.ClusterExpansionOfAStep
end
