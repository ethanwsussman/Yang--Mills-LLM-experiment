import YangMills.Construction.ColdChainAtEveryLevel.ComparisonOfAgreeingPairs
import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsWithTwoRadii
import YangMills.Construction.ColdChainAtEveryLevel.TurnedChainsOfAColdTop
import YangMills.Construction.ColdChainAtEveryLevel.WeightedEstimateOnTheSlice
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
open YangMills.Construction.TwistedTops
section Monotone
variable {F : BlockFrame}
variable {a θ del Ca rL r' s : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top}
theorem IsSliceCriticalPoint.mono_const {C₁ C₂ : ℝ} {U : ChainChart F}
    (h : IsSliceCriticalPoint a θ del Ca rL C₁ s S V U)
    (hC : C₁ ≤ C₂) : IsSliceCriticalPoint a θ del Ca rL C₂ s S V U := by
  obtain ⟨Ul, Ur, h1, h2⟩ := h.split
  exact {
    mem_slice := h.mem_slice
    small := h.small
    critical := h.critical
    unique := h.unique
    split := ⟨Ul, Ur, h1, fun p y0 θ' hθ' => ⟨(h2 p y0 θ' hθ').1, (h2 p y0 θ' hθ').2.trans
      (mul_le_mul_of_nonneg_right hC (sq_nonneg s))⟩⟩
    floor := h.floor }
theorem SliceCriticalPointLocalBounds.mono_const {C₁ C₂ : ℝ} {U : ChainChart F}
    (hb : SliceCriticalPointLocalBounds a θ C₁ s S V U)
    (hL : 0 < F.blockSide) (hC₁ : 0 ≤ C₁) (hC : C₁ ≤ C₂) (hs : 0 ≤ s) :
    SliceCriticalPointLocalBounds a θ C₂ s S V U := by
  have hLr : (0 : ℝ) < (F.blockSide : ℝ) := by exact_mod_cast hL
  have hm : C₁ * s ≤ C₂ * s := mul_le_mul_of_nonneg_right hC hs
  have h0 : 0 ≤ C₁ * s := mul_nonneg hC₁ hs
  have h4 : (C₁ * s) ^ 4 ≤ (C₂ * s) ^ 4 := pow_le_pow_left₀ h0 hm 4
  have h2 : (C₁ * s) ^ 2 ≤ (C₂ * s) ^ 2 := pow_le_pow_left₀ h0 hm 2
  constructor
  · exact hb.colder
  · intro j p x hj h1 h3
    have hx : 0 ≤ x := by linarith
    have q : 0 ≤ (x / (F.blockSide : ℝ) ^ (F.top - j)) ^ (4 * θ) :=
      Real.rpow_nonneg (div_nonneg hx (pow_nonneg hLr.le _)) _
    exact (hb.quartic j p x hj h1 h3).trans (mul_le_mul_of_nonneg_right h4 q)
  · intro p x h1 h3
    have hx : 0 ≤ x := by linarith
    have q : 0 ≤ (x / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) :=
      Real.rpow_nonneg (div_nonneg hx (pow_nonneg hLr.le _)) _
    obtain ⟨e1, e2⟩ := hb.curvature_and_misfits p x h1 h3
    exact ⟨e1.trans (mul_le_mul_of_nonneg_right h2 q), e2.trans (mul_le_mul_of_nonneg_right h2 q)⟩
  · intro j z hj
    obtain ⟨e1, e2⟩ := hb.misfits_on_cells j z hj
    have q1 : 0 ≤ (4 / (F.blockSide : ℝ) ^ 2) ^ (F.top - 1 - j) := pow_nonneg (by positivity) _
    have q2 : 0 ≤ (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j) := pow_nonneg (by positivity) _
    exact ⟨e1.trans (pow_le_pow_left₀ (mul_nonneg h0 q1) (mul_le_mul_of_nonneg_right hm q1) 4),
      e2.trans (pow_le_pow_left₀ (mul_nonneg h0 q2) (mul_le_mul_of_nonneg_right hm q2) 2)⟩
theorem IsCriticalChainOverTop.mono_const {C₁ C₂ s' : ℝ} {V' : F.GaugeField F.top} {U : ChainChart F}
    (hb : IsCriticalChainOverTop a θ del Ca C₁ s' S V V' U) (hL : 0 < F.blockSide) (hC₁ : 0 ≤ C₁) (hC : C₁ ≤ C₂)
    (hs : 0 ≤ s') : IsCriticalChainOverTop a θ del Ca C₂ s' S V V' U := by
  have hLr : (0 : ℝ) < (F.blockSide : ℝ) := by exact_mod_cast hL
  have hm : C₁ * s' ≤ C₂ * s' := mul_le_mul_of_nonneg_right hC hs
  have h0 : 0 ≤ C₁ * s' := mul_nonneg hC₁ hs
  have h4 : (C₁ * s') ^ 4 ≤ (C₂ * s') ^ 4 := pow_le_pow_left₀ h0 hm 4
  have h2 : (C₁ * s') ^ 2 ≤ (C₂ * s') ^ 2 := pow_le_pow_left₀ h0 hm 2
  obtain ⟨Ul, Ur, g1, g2⟩ := hb.split
  constructor
  · exact hb.critical
  · exact ⟨Ul, Ur, g1, fun p y0 θ' hθ' => ⟨(g2 p y0 θ' hθ').1, (g2 p y0 θ' hθ').2.trans
      (mul_le_mul_of_nonneg_right hC (sq_nonneg s'))⟩⟩
  · intro j p x hj h1 h3
    have hx : 0 ≤ x := by linarith
    have q : 0 ≤ (x / (F.blockSide : ℝ) ^ (F.top - j)) ^ (4 * θ) :=
      Real.rpow_nonneg (div_nonneg hx (pow_nonneg hLr.le _)) _
    exact (hb.quartic j p x hj h1 h3).trans (mul_le_mul_of_nonneg_right h4 q)
  · intro p x h1 h3
    have hx : 0 ≤ x := by linarith
    have q : 0 ≤ (x / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ) :=
      Real.rpow_nonneg (div_nonneg hx (pow_nonneg hLr.le _)) _
    obtain ⟨e1, e2⟩ := hb.curvature_and_misfits p x h1 h3
    exact ⟨e1.trans (mul_le_mul_of_nonneg_right h2 q), e2.trans (mul_le_mul_of_nonneg_right h2 q)⟩
  · intro j z hj
    obtain ⟨e1, e2⟩ := hb.misfits_on_cells j z hj
    have q1 : 0 ≤ (4 / (F.blockSide : ℝ) ^ 2) ^ (F.top - 1 - j) := pow_nonneg (by positivity) _
    have q2 : 0 ≤ (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j) := pow_nonneg (by positivity) _
    exact ⟨e1.trans (pow_le_pow_left₀ (mul_nonneg h0 q1) (mul_le_mul_of_nonneg_right hm q1) 4),
      e2.trans (pow_le_pow_left₀ (mul_nonneg h0 q2) (mul_le_mul_of_nonneg_right hm q2) 2)⟩
end Monotone
end BlockAverages
namespace TwistedTops
open YangMills.Construction.BlockAverages
section Monotone
variable {F : BlockFrame}
variable {a θ del Ca rL r' s : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top}
theorem IsTwistedCriticalChain.mono_const {k : ℕ} {c : Fin k → F.Site F.top × Fin 4}
    {X : Fin k → imaginaryQuaternions} {U : ChainChart F} {T : (Fin k → ℝ) → ChainChart F} {C₁ C₂ : ℝ}
    {Ck Ck' : ℕ → ℝ} (h : IsTwistedCriticalChain a θ del Ca rL r' C₁ s Ck S V c X U T)
    (hL : 0 < F.blockSide) (hC₁ : 0 ≤ C₁) (hC : C₁ ≤ C₂) (hs : 0 ≤ s) (hk : ∀ m, Ck m ≤ Ck' m) :
    IsTwistedCriticalChain a θ del Ca rL r' C₂ s Ck' S V c X U T where
  eq_zero := h.eq_zero
  holo_fine := h.holo_fine
  holo_coarse := h.holo_coarse
  analytic_fine := h.analytic_fine
  analytic_coarse := h.analytic_coarse
  mem_gaugeSlice := h.mem_gaugeSlice
  norm_le := h.norm_le
  isCritical ζ σ h1 h2 := by
    have hσ : 0 ≤ (k : ℝ) * σ ∨ k = 0 := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exact Or.inr h0
      · have hl : 0 ≤ |ζ ⟨0, h0⟩| := abs_nonneg _
        have : 0 ≤ σ := hl.trans (h1 _)
        exact Or.inl (by positivity)
    refine IsCriticalChainOverTop.mono_const (h.isCritical ζ σ h1 h2) hL hC₁ hC ?_
    rcases hσ with h3 | h3
    · linarith
    · subst h3
      simpa using hs
  hessian_ge := h.hessian_ge
  mixedDeriv_decay m e z hm := (h.mixedDeriv_decay m e z hm).trans
    (mul_le_mul_of_nonneg_right (hk m) (Real.exp_pos _).le)
theorem IsTwistedCriticalChain.toTwistedFamily {k : ℕ} {c : Fin k → F.Site F.top × Fin 4}
    {X : Fin k → imaginaryQuaternions} {U : ChainChart F} {T : (Fin k → ℝ) → ChainChart F} {C₁ : ℝ}
    {Ck : ℕ → ℝ} (hk : 1 ≤ k) (h : IsTwistedCriticalChain a θ del Ca rL r' C₁ s Ck S V c X U T) :
    IsTwistedCriticalFamily a del rL r' S V c X T where
  mem_gaugeSlice := h.mem_gaugeSlice
  norm_le := h.norm_le
  stationary ζ hζ := by
    have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
    have h1 : ∀ l, |ζ l| ≤ Finset.univ.sup' hne fun l => |ζ l| := fun l =>
      Finset.le_sup' (fun l => |ζ l|) (Finset.mem_univ l)
    have h2 : (Finset.univ.sup' hne fun l => |ζ l|) < r' / k :=
      (Finset.sup'_lt_iff hne).2 fun l _ => hζ l
    exact (h.isCritical ζ _ h1 h2).critical
end Monotone
end TwistedTops
namespace BlockAverages
open YangMills.Construction.TwistedTops
set_option maxHeartbeats 1000000 in
theorem criticalChainsTwoRadii_of_parts (hW : weightedSliceEstimateStatement)
    (hB : splitCriticalPointBoundsStatement) (hC : coldTopTwistedChainsStatement)
    (hD : agreeingPairsComparisonStatement) : criticalChainsTwoRadiiStatement := by
  intro a ha
  obtain ⟨θ, del, Ca₄, hθ, hθ8, hdel, hdel8, hCa₄, hE⟩ := hW a ha
  obtain ⟨Ca, hCa, L₁, hC'⟩ := hC a θ del Ca₄ ha hθ hθ8 hdel hdel8 hCa₄ hE
  obtain ⟨L₂, hD'⟩ := hD a θ del Ca₄ ha hθ hθ8 hdel hdel8 hCa₄ hE
  obtain ⟨L₃, hB'⟩ := hB a θ del Ca ha hθ hθ8 hdel hdel8 hCa
  refine ⟨θ, del, Ca, hθ, hθ8, hdel, hdel8, hCa, max L₁ (max L₂ L₃), fun L hL hLge => ?_⟩
  have hL1 : L₁ ≤ L := le_trans (le_max_left _ _) hLge
  have hL2 : L₂ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLge
  have hL3 : L₃ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLge
  obtain ⟨c₁, hc₁, hCL⟩ := hC' L hL hL1
  obtain ⟨c₂, hc₂, hDL⟩ := hD' L hL hL2
  set r : ℝ := min c₁ c₂ with hr
  have hr0 : 0 < r := lt_min hc₁ hc₂
  obtain ⟨r', sL, CL, Ck, hr'0, hr'r, hsL, hCL0, hCk, hchain⟩ := hCL r hr0 (min_le_left _ _)
  obtain ⟨s₀, C, Ck', hs₀, hC0, hCk', hcomp⟩ := hDL r hr0 (min_le_right _ _)
  obtain ⟨s₂, C₂, hs₂, hC₂, hbounds⟩ := hB' L hL hL3 r CL hr0 hCL0
  have hCLmax : CL ≤ CL + C₂ + C := by linarith
  have hC₂max : C₂ ≤ CL + C₂ + C := by linarith
  have hCmax : C ≤ CL + C₂ + C := by linarith
  refine ⟨r, r', min sL (min s₀ s₂), CL + C₂ + C, fun m => Ck m + Ck' m, hr0, hr'0, hr'r,
    lt_min hsL (lt_min hs₀ hs₂), by positivity, fun m => add_pos (hCk m) (hCk' m), ?_, ?_⟩
  · intro F m S hFL hamb hm hreg s V hs hsle hcold
    have hLpos : 0 < F.blockSide := by
      have : Odd F.blockSide := hFL ▸ hL
      exact this.pos
    obtain ⟨U, hU, hT⟩ := hchain F m S hFL hamb hm hreg s V hs (hsle.trans (min_le_left _ _)) hcold
    refine ⟨U, hU.mono_const hCLmax, ?_, fun k c X hk hX => ?_⟩
    · exact SliceCriticalPointLocalBounds.mono_const (hbounds F m S hFL hamb hm hreg s V hs
        (hsle.trans ((min_le_right _ _).trans (min_le_right _ _))) hcold U hU) hLpos hC₂.le hC₂max hs.le
    · obtain ⟨T, hTc⟩ := hT k c X hk hX
      exact ⟨T, hTc.mono_const hLpos hCL0.le hCLmax hs.le fun m => by linarith [hCk' m]⟩
  · intro F F' m S S' hFL hFL' ht hamb hamb' hm hreg hreg' s V V' Y Y' ρ hs hsle hcold hcold' hρ hagree U U' hU hU'
    obtain ⟨h1, h2⟩ := hcomp F F' m S S' hFL hFL' ht hamb hamb' hm hreg hreg' s V V' Y Y' ρ hs
      (hsle.trans ((min_le_right _ _).trans (min_le_left _ _))) hcold hcold' hρ hagree U U'
      ⟨hU.mem_slice, hU.small, hU.critical⟩ ⟨hU'.mem_slice, hU'.small, hU'.critical⟩
    refine ⟨fun z hz => (h1 z hz).trans ?_, fun k h X hk hb hX T T' hT hT' m' e z hm' hz => ?_⟩
    · have : C * s ≤ (CL + C₂ + C) * s := mul_le_mul_of_nonneg_right hCmax hs.le
      exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    · refine (h2 k h X r' hk hr'0 hb hX T T' (hT.toTwistedFamily hk) (hT'.toTwistedFamily hk) m' e z hm' hz).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith [hCk m']) (Real.exp_pos _).le
end BlockAverages
end YangMills.Construction
end
