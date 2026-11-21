import YangMills.Construction.InequalityOnMirroredCopies.TheRatioIsBounded
import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenCopiesAtEveryDatum
import YangMills.Construction.SixteenPointsOnASmallTorus.TheInequalityAtEveryDatum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SmallTorusCopies
open ReflectedCopies
private theorem copyBound_pow_mono {A A' b b' l ϱ : ℝ} (f : InfiniteLattice.AmbientSpace → ℝ) (hA : 0 ≤ A)
    (hAA : A ≤ A') (hbb : b ≤ b') (n : ℕ) : copyBound A b l ϱ f ^ n ≤ copyBound A' b' l ϱ f ^ n := by
  have hN : 0 ≤ radiusNorm ϱ f :=
    le_max_of_le_left (Real.iSup_nonneg fun _ => norm_nonneg _)
  have hl : 0 ≤ l ^ 4 := by positivity
  have hX : 0 ≤ TorusBound.logPos (1 / ϱ) ^ (1 / 20 : ℝ) :=
    Real.rpow_nonneg (le_max_right _ _) _
  have hs : copySize A b l ϱ ≤ copySize A' b' l ϱ :=
    mul_le_mul hAA
      (Real.exp_le_exp.2 (add_le_add (mul_le_mul_of_nonneg_right hbb hl)
        (mul_le_mul_of_nonneg_right hbb hX)))
      (Real.exp_pos _).le (hA.trans hAA)
  have h0 : 0 ≤ copySize A b l ϱ := mul_nonneg hA (Real.exp_pos _).le
  exact pow_le_pow_left₀ (mul_nonneg h0 hN) (mul_le_mul_of_nonneg_right hs hN) n
private theorem copyInequality_mono {D : ChessboardTori.ChessboardSetup} {A A' b b' : ℝ} (hA : 0 ≤ A)
    (hAA : A ≤ A') (hbb : b ≤ b') (H : CopyInequality D A b) : CopyInequality D A' b' := by
  intro c ϱ f hs
  obtain ⟨κ, hκ⟩ := H c ϱ f hs
  exact ⟨κ, fun j => ⟨(hκ j).1, (hκ j).2.1, (hκ j).2.2.trans (copyBound_pow_mono f hA hAA hbb _)⟩⟩
theorem copyInequalityForAdmissibleFlows_of_bounds (h₁ : sixteenCopyBoundForAdmissibleFlows)
    (h₂ : SixteenCopiesImpliesInequality) (h₃ : TorusRatioBoundedStatement) :
    copyInequalityForAdmissibleFlows := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hpos, hS⟩ := h₁ a ha
  obtain ⟨rt₁, hpos₁, hR⟩ := h₃
  refine ⟨L₀, fun c => min (rt₀ c) (rt₁ c), C₀, fun c => lt_min (hpos c) (hpos₁ c), ?_⟩
  intro L hodd hL T hTa hTL hD hC hOn hrt hCder
  obtain ⟨y₀, hy₀⟩ := hS L hodd hL T hTa hTL hD hC hOn (hrt.trans (min_le_left _ _)) hCder
  obtain ⟨y₁, hy₁⟩ := hR T hD hC (hrt.trans (min_le_right _ _))
  refine ⟨max y₀ y₁, fun y hy hret hrow Ξ hΞ => ?_⟩
  obtain ⟨A₀, b₀, hA₀, hb₀, hSix⟩ := hy₀ y (le_of_max_le_left hy) hret hrow Ξ hΞ
  obtain ⟨b₁, hb₁, hB⟩ := hy₁ y (le_of_max_le_right hy) ⟨hret, hrow⟩ Ξ
  refine ⟨max A₀ 1, max (b₀ + b₁) 1, le_max_right _ _, le_max_right _ _, fun D hDL hd => ?_⟩
  have hd' : ReflectedCopies.IsAdmissibleSetup (T.stepParameters y) Ξ D := ⟨hDL, hd.coupling_ge, hd.coupling_le⟩
  exact copyInequality_mono hA₀ (le_max_left _ _) (le_max_left _ _)
    (h₂ D A₀ b₀ b₁ hA₀ hb₀ hb₁ (hSix D hDL hd) (hB D hd'))
end YangMills.Construction.SmallTorusCopies
end
