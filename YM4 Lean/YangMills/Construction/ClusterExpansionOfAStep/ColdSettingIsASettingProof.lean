import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheMarkedIntegralOfAllBlocksProof
import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingIsCold
import YangMills.Construction.ClusterExpansionOfAStep.MeanOfAContourAtAColdTop
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepAtParametersProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings RenormalizationStepParameters StepCosts
namespace ColdChart
variable {H : BlockFrame} {m : ℕ}
section HotLumps
variable {n : ℕ}
theorem hotLumps_eq_empty_of_isCold {H : BlockFrame} {j m : ℕ} {L : ℕ} (g : LumpGrid L)
    (hm : ∀ i, H.period j i = m) (s : ℝ) (X : Finset (H.Site j)) (W : TorusField m) (hW : IsCold s W) :
    hotLumps g s X (readAtLevel H j W) = ∅ := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.hotLumps_eq_empty_of_isCold <;> assumption
theorem stepHotLumps_eq_empty (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (W : TorusField (n * ℓ.side)) (hW : IsCold ℓ.threshold W) :
    stepHotLumps ℓ W = ∅ := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.stepHotLumps_eq_empty <;> assumption
theorem torusHotSites_eq_empty (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (W : TorusField (n * ℓ.side)) (hW : IsCold ℓ.threshold W) :
    torusHotSites ℓ W = ∅ := by apply _root_.YangMills.Construction.MarkedIntegrals.ChartRepresentation.torusHotSites_eq_empty <;> assumption
theorem torusHotLumps_eq_empty (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) [NeZero ℓ.side] (W : TorusField (n * ℓ.side))
    (hW : IsCold ℓ.threshold W) : torusHotLumps ℓ W = ∅ := by
  have hL : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
  have hq : n * ℓ.side / ℓ.side = n := Nat.mul_div_cancel _ hL
  have hm : ∀ i, (stepBlockFrame ℓ.side (n * ℓ.side / ℓ.side)).period 0 i = n * ℓ.side := by
    intro i
    show n * ℓ.side / ℓ.side * ℓ.side ^ (0 + 1 - 0) = n * ℓ.side
    rw [hq]
    simp
  unfold torusHotLumps
  rw [hotLumps_eq_empty_of_isCold _ hm _ _ W hW]
  rfl
theorem thickening_empty [NeZero n] (m : ℕ) : thickening m (∅ : Finset (TorusSite n)) = ∅ := by
  unfold thickening
  simp
theorem trivialField_isCold {s : ℝ} (hs : 0 < s) (m : ℕ) : IsCold s (trivialField m) := by apply _root_.YangMills.SharedProofs.p4747 <;> assumption
end HotLumps
section Hulls
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem isHullState_empty (W : TorusField (n * R.params.side)) (hW : IsCold R.params.threshold W) (r : ℕ) :
    IsHullState R.params r W ∅ := by
  refine ⟨?_, ?_⟩
  · rw [torusHotSites_eq_empty R.params W hW, thickening_empty]
  · intro X hX
    simp [chainComponents] at hX
end Hulls
end ColdChart
open ColdChart in
theorem coldChartSettingIsAdmissible_holds (hcold : ColdChartSettingIsCold)
    (hmean : ContourMeanAtColdField) : ColdChartSettingIsAdmissible := by
  intro T hT
  obtain ⟨y₁, h₁⟩ := hcold T hT
  obtain ⟨y₂, h₂⟩ := hmean T hT
  refine ⟨max y₁ y₂, fun y hy R hR n _ hn V hV => ?_⟩
  have hy1 : y₁ ≤ y := le_trans (le_max_left _ _) hy
  have hy2 : y₂ ≤ y := le_trans (le_max_right _ _) hy
  have hσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hσ0 : 0 < R.params.threshold := by rw [hσ]; exact hT.σ_pos
  have hc4 := h₁ y hy1 R hR n hn V hV
  have hc : ∀ η, (coldChartSetting R V).InBalls η →
      IsCold R.params.threshold ((coldChartSetting R V).field η) := by
    intro η hη x μ ν hμ
    have h1 := hc4 η hη x μ ν hμ
    rw [hσ]
    have h2 : 0 < T.threshold := hT.σ_pos
    linarith
  have hflat : IsCold R.params.threshold (trivialField (n * R.params.side)) := trivialField_isCold hσ0 _
  exact
    { subset_chart := Finset.Subset.refl _
      isHull := fun η hη => isHullState_empty _ (hc η hη) _
      hotLumps_eq := fun η hη => by
        rw [torusHotLumps_eq_empty _ _ (hc η hη)]
        exact (torusHotLumps_eq_empty _ _ hflat).symm
      factor_ne_zero := fun η _ X hX => by
        have : X ∈ chainComponents R.range (∅ : Finset (TorusSite (n * R.params.side))) := hX
        simp [chainComponents] at this
      far_from_support := fun b _ z hz => by
        have : z ∈ (∅ : Finset (TorusSite (n * R.params.side))) ∪
            torusHotSites R.params (trivialField (n * R.params.side)) := hz
        rw [torusHotSites_eq_empty _ _ hflat] at this
        simp at this
      curvature_lt := fun η hη b _ x μ ν hμ _ => by
        rw [hσ]
        exact hc4 η hη x μ ν hμ
      region_spec := Or.inl ⟨rfl, by rw [hσ]; exact hV⟩
      near_frame := fun b _ b' hb' hb'' _ => absurd hb' hb''
      isBaseChoice := by
        have h0 : stepHotLumps R.params (trivialField (n * R.params.side)) = ∅ :=
          stepHotLumps_eq_empty _ _ hflat
        show IsBaseChoice R.params.baseDepth (stepHotLumps R.params (trivialField (n * R.params.side)))
          (fun y => cellCentre 0 y)
        rw [h0]
        intro y
        exact ⟨fun _ => rfl, fun h => absurd (Or.inl (by unfold nearbyLumps; exact Finset.filter_empty _)) h⟩
      cutoff_ne_zero := fun b hb hb' _ => absurd hb hb'
      half_le_meanNorm := fun η hη b _ c _ => h₂ y hy2 R hR n hn V hV η hη c }
end YangMills.Construction.ClusterExpansionOfAStep
end
