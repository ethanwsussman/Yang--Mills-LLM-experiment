import YangMills.Construction.RunningCouplingSlope.AverageFamiliesReadNearCells
import YangMills.Construction.RunningCouplingSlope.AveragesAlongTheBackgroundAreLocal
import YangMills.Construction.RunningCouplingSlope.FamiliesThatReadNearCellsAreLocal
import YangMills.Construction.RunningCouplingSlope.LocalFamiliesAreClosed
import YangMills.Construction.RunningCouplingSlope.NoiseFamilyReadsNearCells
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.BackgroundMeansLocality
open Tower PeriodicOperators
open Tower.CriticalBranchResponse
variable {L n k : ℕ}
private lemma twoSourceBackground_eq_remainder (w : Fin 4 → ℤ) (s t : ℝ) :
    twoSourceBackground L n k w s t = remainderGaugeField (twoCellResponseForm L n k w s t) := by
  unfold twoSourceBackground remainderGaugeField IdentityExpChart.expForm
    scaledRemainderForm twoCellResponseForm
  congr 1
  funext b
  simp only [meshScaledResponse, Pi.add_apply, Pi.smul_apply, Submodule.coe_smul, smul_add]
  rw [smul_comm (s : ℂ), smul_comm (t : ℂ)]
private lemma isLocalAlongBackground_weaken (hC : LocalFamiliesClosed)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] {c : ι → Vertex L n k k}
    {c' : ι' → Vertex L n k k} {T : ℝ → ℝ → Matrix ι' ι ℂ} {w : Fin 4 → ℤ} {M M' θ θ' : ℝ}
    (hM : 0 ≤ M) (hMM : M ≤ M') (hθ' : 0 < θ') (hθθ : θ' ≤ θ)
    (h : IsLocalAlongBackground c c' T w M θ) :
    IsLocalAlongBackground c c' T w M' θ' := by
  obtain ⟨S, -, hS⟩ := hC θ (hθ'.trans_le hθθ)
  exact (hS L n k hL hn).mono c c' T w M M' θ' hM hMM hθ' hθθ h
theorem backgroundMeansAreLocal_of_components (hC : LocalFamiliesClosed)
    (hF : NearCellFamiliesAreLocal) (hA : MeanKernelsAreLocalNearCells)
    (hN : NoiseCovarianceIsLocalNearCells) :
    BackgroundMeansAreLocal := by
  intro a ha L hL
  obtain ⟨ρ₁, C₁, r₁, hρ₁, hC₁, hr₁, hA'⟩ := hA L hL
  obtain ⟨ρ₂, C₂, r₂, hρ₂, hC₂, hr₂, hN'⟩ := hN a ha L hL
  obtain ⟨M₁, θ₁, hM₁, hθ₁, hF₁⟩ := hF L hL ρ₁ C₁ r₁ hρ₁ hC₁ hr₁
  obtain ⟨M₂, θ₂, hM₂, hθ₂, hF₂⟩ := hF L hL ρ₂ C₂ r₂ hρ₂ hC₂ hr₂
  refine ⟨M₁ + M₂, min θ₁ θ₂, by positivity, lt_min hθ₁ hθ₂, fun k hk => ?_⟩
  obtain ⟨n₁, h₁⟩ := hA' k hk
  obtain ⟨n₂, h₂⟩ := hN' k hk
  obtain ⟨n₃, h₃⟩ := hF₁ k hk
  obtain ⟨n₄, h₄⟩ := hF₂ k hk
  refine ⟨n₁ + n₂ + n₃ + n₄, fun n hn hn0 => ?_⟩
  intro _ _ _ _ _ _ _ _ w
  obtain ⟨a₁, a₂, a₃, a₄⟩ := h₁ n (by omega) hn0
  have a₅ := h₂ n (by omega) hn0
  have w₁ : M₁ ≤ M₁ + M₂ := by linarith
  have w₂ : M₂ ≤ M₁ + M₂ := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := isLocalAlongBackground_weaken hC hL hn0 hM₁.le w₁ (lt_min hθ₁ hθ₂) (min_le_left _ _) (h₃ n (by omega) hn0 _ _ _ a₁ w)
    refine (congrArg (fun T => IsLocalAlongBackground colouredEdgeCell edgeCell T w (M₁ + M₂) (min θ₁ θ₂)) ?_).mpr this
    funext s t
    simp only [rescaledQAlong, twoSourceBackground_eq_remainder]
  · have := isLocalAlongBackground_weaken hC hL hn0 hM₁.le w₁ (lt_min hθ₁ hθ₂) (min_le_left _ _) (h₃ n (by omega) hn0 _ _ _ a₂ w)
    refine (congrArg (fun T => IsLocalAlongBackground colouredEdgeCell edgeCell T w (M₁ + M₂) (min θ₁ θ₂)) ?_).mpr this
    funext s t
    simp only [meanQAlong, twoSourceBackground_eq_remainder]
  · have := isLocalAlongBackground_weaken hC hL hn0 hM₁.le w₁ (lt_min hθ₁ hθ₂) (min_le_left _ _) (h₃ n (by omega) hn0 _ _ _ a₃ w)
    refine (congrArg (fun T => IsLocalAlongBackground colouredVertexCell vertexCell T w (M₁ + M₂) (min θ₁ θ₂)) ?_).mpr this
    funext s t
    simp only [rescaledRAlong, twoSourceBackground_eq_remainder]
  · have := isLocalAlongBackground_weaken hC hL hn0 hM₁.le w₁ (lt_min hθ₁ hθ₂) (min_le_left _ _) (h₃ n (by omega) hn0 _ _ _ a₄ w)
    refine (congrArg (fun T => IsLocalAlongBackground colouredVertexCell vertexCell T w (M₁ + M₂) (min θ₁ θ₂)) ?_).mpr this
    funext s t
    simp only [meanRAlong, twoSourceBackground_eq_remainder]
  · have := isLocalAlongBackground_weaken hC hL hn0 hM₂.le w₂ (lt_min hθ₁ hθ₂) (min_le_right _ _) (h₄ n (by omega) hn0 _ _ _ a₅ w)
    refine (congrArg (fun T => IsLocalAlongBackground edgeCell edgeCell T w (M₁ + M₂) (min θ₁ θ₂)) ?_).mpr this
    funext s t
    simp only [noiseAlong, twoSourceBackground_eq_remainder]
end YangMills.Construction.RunningCouplingSlope.BackgroundMeansLocality
end
