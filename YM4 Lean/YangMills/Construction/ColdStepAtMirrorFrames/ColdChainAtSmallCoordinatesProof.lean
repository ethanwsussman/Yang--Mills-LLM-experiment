import YangMills.Construction.ColdChainAtEveryLevel.AnalyticCoordinatesOfAColdTop
import YangMills.Construction.ColdChainAtEveryLevel.AnalyticSharesOfAColdTop
import YangMills.Construction.ColdChainAtEveryLevel.EveryHotPlaquetteCosts
import YangMills.Construction.ColdChainAtEveryLevel.HessianFloorInTheChart
import YangMills.Construction.ColdChainAtEveryLevel.OneLeastFieldOfAColdTop
import YangMills.Construction.ColdStepAtMirrorFrames.ClassicalChainAtGivenNumbersProof
import YangMills.Construction.ColdStepAtMirrorFrames.ColdChainAtSmallCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
namespace SmallCoordinates
variable {F : BlockFrame}
theorem isCold_of_le {S : Finset F.Cell} {j : ℕ} {s s' : ℝ} {X : F.GaugeField j} (hle : s ≤ s')
    (hcold : IsCold S j s X) : IsCold S j s' X :=
  fun p hp => (hcold p hp).trans_le hle
theorem hasColdMinimizer_mono {a ρ N N' s : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top} (hs : 0 ≤ s)
    (hN : N ≤ N') (h : HasColdMinimizer a ρ N s S V) : HasColdMinimizer a ρ N' s S V := by
  obtain ⟨w, ⟨h0, h1, h2⟩, hc, hu⟩ := h
  refine ⟨w, ⟨h0, fun b hb => (h1 b hb).trans ?_, h2⟩, hc, hu⟩
  exact min_le_min le_rfl (mul_le_mul_of_nonneg_right hN hs)
theorem hasCoerciveHessian_anti {a lam ρ ρ' σ σ' : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top}
    (hρ : ρ' ≤ ρ) (hσ : σ' ≤ σ) (h : HasCoerciveHessian a lam ρ σ S V) :
    HasCoerciveHessian a lam ρ' σ' S V :=
  fun w dw h1 h2 h3 hc => h w dw h1 h2 (fun b hb => (h3 b hb).trans hρ) (isCold_of_le hσ hc)
theorem hasHotPlaquettePenalty_anti {a cg σ σ' s : ℝ} {S : Finset F.Cell} {V : F.GaugeField F.top}
    (hσ : σ' ≤ σ) (h : HasHotPlaquettePenalty a cg σ s S V) : HasHotPlaquettePenalty a cg σ' s S V :=
  fun t h1 h2 W => h t h1 (h2.trans hσ) W
theorem hasRegularCellShares_mono {a δ s : ℝ} {N N' : ℕ → ℝ} {S : Finset F.Cell}
    {V : F.GaugeField F.top} (hs : 0 ≤ s) (hN : ∀ k, N k ≤ N' k) (h : HasRegularCellShares a δ s N S V) :
    HasRegularCellShares a δ s N' S V := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_⟩
  · intro k c X hk hX
    exact (h6 k c X hk hX).trans (mul_le_mul_of_nonneg_right (hN k) (Real.exp_pos _).le)
  · intro Y k c X hk hX
    exact (h7 Y k c X hk hX).trans (mul_le_mul_of_nonneg_right (hN k) (Real.exp_pos _).le)
  · intro Y
    exact ⟨(h8 Y).1, (h8 Y).2.trans (mul_le_mul_of_nonneg_right (hN 0) (sq_nonneg s))⟩
  · intro Y c X hX
    refine (h9 Y c X hX).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    exact mul_le_mul_of_nonneg_right (hN 1) hs
theorem hasRegularCoordinates_mono {a δ ρ : ℝ} {N N' : ℕ → ℝ} {S : Finset F.Cell}
    {V : F.GaugeField F.top} (hN : ∀ k, N k ≤ N' k) (h : HasRegularCoordinates a δ ρ N S V) :
    HasRegularCoordinates a δ ρ N' S V := by
  intro b hb
  refine ⟨(h b hb).1, fun k c X hk hX => ?_⟩
  exact ((h b hb).2 k c X hk hX).trans (mul_le_mul_of_nonneg_right (hN k) (Real.exp_pos _).le)
theorem derivativeScale_nonneg (s : ℝ) (hs : 0 ≤ s) (k : ℕ) : 0 ≤ derivativeScale s k := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.AdmissibleParameters.derivativeScale_nonneg <;> assumption
theorem hasComparableCellShares_mono {a δ s : ℝ} {N N' : ℕ → ℝ} {F' : BlockFrame} {S : Finset F.Cell}
    {V : F.GaugeField F.top} {S' : Finset F'.Cell} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    {r : ℕ} (hs : 0 ≤ s) (hN : ∀ k, N k ≤ N' k) (h : HasComparableCellShares a δ s N S V S' V' Y Y' r) :
    HasComparableCellShares a δ s N' S V S' V' Y Y' r := by
  intro k hh X h1 h2
  refine (h k hh X h1 h2).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  exact mul_le_mul_of_nonneg_left (hN k) (derivativeScale_nonneg s hs k)
theorem hasComparableCoordinates_mono {a δ ρ s : ℝ} {N N' : ℕ → ℝ} {F' : BlockFrame}
    {S : Finset F.Cell} {V : F.GaugeField F.top} {S' : Finset F'.Cell} {V' : F'.GaugeField F'.top}
    {Y : F.Cell} {Y' : F'.Cell} {r : ℕ} (hs : 0 ≤ s) (hN : ∀ k, N k ≤ N' k)
    (h : HasComparableCoordinates a δ ρ s N S V S' V' Y Y' r) :
    HasComparableCoordinates a δ ρ s N' S V S' V' Y Y' r := by
  intro hh o i ho hb hbox hd
  obtain ⟨h1, h2⟩ := h hh o i ho hb hbox hd
  refine ⟨h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le), fun k h' X hk hbx hX => ?_⟩
  · exact mul_le_mul_of_nonneg_right (hN 0) hs
  · exact (h2 k h' X hk hbx hX).trans (mul_le_mul_of_nonneg_right (hN k) (Real.exp_pos _).le)
end SmallCoordinates
open SmallCoordinates in
theorem coldChainAtSmallCoordinates_of_uniqueMinimizer (h1 : uniqueMinimizerStatement)
    (h2 : hessianLowerBoundStatement) (h3 : analyticCellSharesStatement)
    (h4 : analyticChartCoordsStatement) (h5 : hotPlaquetteCostStatement) :
    ColdChainAtSmallCoordinates := by
  intro a ha
  obtain ⟨d3, hd3, h3⟩ := h3 a ha
  obtain ⟨d4, hd4, h4⟩ := h4 a ha
  set δ : ℝ := min (1 / 8) (min d3 d4) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (lt_min hd3 hd4)
  have hδ8 : δ ≤ 1 / 8 := min_le_left _ _
  have hδ3 : δ ≤ d3 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ4 : δ ≤ d4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨L1, h1⟩ := h1 a ha
  obtain ⟨L2, h2⟩ := h2 a ha
  obtain ⟨L3, h3⟩ := h3 δ hδ0 hδ3
  obtain ⟨L4, h4⟩ := h4 δ hδ0 hδ4
  obtain ⟨L5, h5⟩ := h5 a ha
  refine ⟨δ, hδ0, max L1 (max L2 (max L3 (max L4 L5))), fun L hL hge => ?_⟩
  have g1 : L1 ≤ L := le_of_max_le_left hge
  have g2 : L2 ≤ L := le_of_max_le_left (le_of_max_le_right hge)
  have g3 : L3 ≤ L := le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hge))
  have g4 : L4 ≤ L := le_of_max_le_left (le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hge)))
  have g5 : L5 ≤ L := le_of_max_le_right (le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hge)))
  obtain ⟨lam, ρ2, σ2, hlam, hρ2, hσ2, h2⟩ := h2 L hL g2
  set ρ : ℝ := min ρ2 1 with hρdef
  have hρ : 0 < ρ := lt_min hρ2 one_pos
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have hρρ : ρ ≤ ρ2 := min_le_left _ _
  obtain ⟨σ1, N1, hσ1, hN1, h1⟩ := h1 L hL g1 ρ hρ
  obtain ⟨σ3, N3, hσ3, hN3, h3⟩ := h3 L hL g3
  obtain ⟨σ4, N4, hσ4, hN4, h4⟩ := h4 L hL g4 ρ hρ hρ1
  obtain ⟨σ5, cg, hσ5, hcg, h5⟩ := h5 L hL g5
  set σA : ℝ := min σ1 (min σ2 (min σ3 (min σ4 σ5))) with hσA
  have hσA0 : 0 < σA := lt_min hσ1 (lt_min hσ2 (lt_min hσ3 (lt_min hσ4 hσ5)))
  have e1 : σA ≤ σ1 := min_le_left _ _
  have e2 : σA ≤ σ2 := (min_le_right _ _).trans (min_le_left _ _)
  have e3 : σA ≤ σ3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have e4 : σA ≤ σ4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have e5 : σA ≤ σ5 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let N : ℕ → ℝ := fun k => N1 + N3 k + N4 k
  have hN : ∀ k, 0 < N k := fun k => by
    have := hN3 k
    have := hN4 k
    simp only [N]
    linarith
  have n1 : N1 ≤ N 0 := by
    have := hN3 0
    have := hN4 0
    simp only [N]
    linarith
  have n3 : ∀ k, N3 k ≤ N k := fun k => by
    have := hN4 k
    simp only [N]
    linarith
  have n4 : ∀ k, N4 k ≤ N k := fun k => by
    have := hN3 k
    simp only [N]
    linarith
  refine ⟨lam, ρ, σA, cg, N, hδ0, hδ8, hlam, hρ, hρ1, hσA0, hcg, hN, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsσ hcold
  have s3 := h3 F m S hFL hamb hm hreg s V hs (hsσ.trans e3) hcold
  have s4 := h4 F m S hFL hamb hm hreg s V hs (hsσ.trans e4) hcold
  refine ⟨hasColdMinimizer_mono hs.le n1 (h1 F m S hFL hamb hm hreg s V hs (hsσ.trans e1) hcold),
    hasCoerciveHessian_anti hρρ e2 (h2 F m S hFL hamb hm hreg s V hs (hsσ.trans e2) hcold),
    hasRegularCellShares_mono hs.le n3 s3.1, hasRegularCoordinates_mono n4 s4.1,
    hasHotPlaquettePenalty_anti e5 (h5 F m S hFL hamb hm hreg s V hs (hsσ.trans e5) hcold), ?_⟩
  intro F' S' V' Y Y' r hF' ht hamb' hreg' hcold' hag
  exact ⟨hasComparableCellShares_mono hs.le n3 (s3.2 F' S' V' Y Y' r hF' ht hamb' hreg' hcold' hag),
    hasComparableCoordinates_mono hs.le n4 (s4.2 F' S' V' Y Y' r hF' ht hamb' hreg' hcold' hag)⟩
end ColdStepAtMirrorFrames
end YangMills.Construction
end
