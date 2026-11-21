import YangMills.Construction.ParameterData.FirstPassagesAreData
import YangMills.Construction.SixteenPointsOnASmallTorus.TheInequalityAtEveryDatum
import YangMills.Construction.SystemOfAdmissibleConstants.CumulantConditionsFromTheInequality
import YangMills.Construction.SystemOfAdmissibleConstants.OnePointBoundsFromTheInequality
import YangMills.Construction.SystemOfAdmissibleConstants.TheFourBoundsAlongTheTrajectory
import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SystemOfAdmissibleConstants
open YangMills.Construction.AmbientPoints
private theorem familyBoundsHold_of_clusterConditions {L M : ℕ} {S : Set ℝ} {P : ℕ+ → ℝ → Prop} {A v : ℝ}
    (h : AdmissibleConstants.ClusterConditions L (M : ℝ) P A v) :
    CouplingFlow.FamilyBoundsHold L M S P (AdmissibleConstants.constantFamiliesOfBounds L A v) where
  torus := by
    rintro ⟨L', hLs, K, m⟩ hs _ β hd n hn d hd0 f hf hsep
    simp only at hs hd
    subst hs
    exact h.torus K β hd m n hn d hd0 f (fun i => (hf.1 i).1) ⟨hd0, fun i k hik => by
      have h' := hsep.trans (iInf_le_of_le i (iInf_le_of_le k (iInf_le_of_le hik le_rfl)))
      rw [tsupport_eq_of_torus, tsupport_eq_of_torus] at h'
      exact h'⟩
  torusBall := by
    rintro ⟨L', hLs, K, m⟩ hs _ β hd n hn d R hd0 hR0 _ f hf hRs hsep
    simp only at hs hd
    subst hs
    exact h.ballOnTori K β hd m n hn R d hR0 hd0 f (fun i => (hf.1 i).1)
      (fun i => by
        obtain ⟨_, ⟨_, x, rfl⟩, h'⟩ := hRs i
        rw [tsupport_eq_of_torus] at h'
        exact ⟨x, h'⟩)
      ⟨hd0, fun i k hik => by
        have h' := hsep.trans (iInf_le_of_le i (iInf_le_of_le k (iInf_le_of_le hik le_rfl)))
        rw [tsupport_eq_of_torus, tsupport_eq_of_torus] at h'
        exact h'⟩
  stateBall := by
    rintro ⟨L', hLs, K, m⟩ hs β hd n hn d R hd0 hR0 ν hν f hf hRs hsep
    simp only at hs hd hν
    subst hs
    exact h.ballInStates K β hd ν.1 hν n hn R d hR0 hd0 f (fun i => (hf.1 i).1)
      (fun i => by
        obtain ⟨_, ⟨_, x, rfl⟩, h'⟩ := hRs i
        rw [tsupport_eq_of_r4] at h'
        exact ⟨x, h'⟩)
      ⟨hd0, fun i k hik => by
        have h' := hsep.trans (iInf_le_of_le i (iInf_le_of_le k (iInf_le_of_le hik le_rfl)))
        rw [tsupport_eq_of_r4, tsupport_eq_of_r4] at h'
        exact h'⟩
  onePoint := by
    rintro ⟨L', hLs, K, m⟩ hs β hd R hR0 ν hν ν' hν' f hf hb
    simp only at hs hd hν hν'
    subst hs
    exact h.meanGapInStates K β hd ν.1 hν ν'.1 hν' R hR0 f hf (by
      obtain ⟨_, ⟨_, x, rfl⟩, h'⟩ := hb
      rw [tsupport_eq_of_r4] at h'
      exact ⟨x, h'⟩)
theorem familyBoundsAlongPath_of_copyInequality
    (hC : SmallTorusCopies.copyInequalityForAdmissibleFlows)
    (hD : TrajectoryData.windowMembersAreDataStatement)
    (hK : AdmissibleConstants.CumulantConditionsOfInequality)
    (hO : AdmissibleConstants.OnePointBoundsOfInequality) :
    FamilyBoundsAlongFlow := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, hT⟩ := hC a ha
  refine ⟨max L₀ 13, rt₀, C₀, hrt, fun L hodd hL T hTa hTL hDr hCS hOn hrtT hCder => ?_⟩
  obtain ⟨y₀, hy₀⟩ := hT L hodd (le_trans (le_max_left _ _) hL) T hTa hTL hDr hCS hOn hrtT hCder
  refine ⟨y₀, fun y hy hret hrow D hDh g hg hfl => ?_⟩
  subst hTL
  have hLs : Conventions.IsAdmissibleBlockingFactor T.side := ⟨hodd, le_trans (le_max_right _ _) hL⟩
  have hu : 0 < g ^ (-2 : ℤ) := zpow_pos hg _
  have hc : 0 ≤ oneLoopDeviation T := Real.iSup_nonneg fun _ => abs_nonneg _
  have hfl₁ : D.floorStar ≤ g ^ (-2 : ℤ) := le_trans (le_max_left _ _) hfl
  have hfl₂ : y + 2 * oneLoopDeviation T + 1 ≤ g ^ (-2 : ℤ) :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hfl
  have hB : 1 ≤ T.B := hDr.B_ge
  have hBs : 2 * T.B ≤ D.shift := hDh.shift_ge
  have htop : D.threshold g = g ^ (-2 : ℤ) + D.shift := rfl
  obtain ⟨A, v, hA, hv, hAv⟩ := hy₀ y hy hret hrow (D.threshold g) (by rw [htop]; linarith)
  have hpos : ∀ (K : ℕ+) (β : ℝ), β ∈ D.passageWindow K g → 0 < β := fun K β hβ => by
    have h₁ : D.threshold g ≤ β := hβ.1
    rw [htop] at h₁
    linarith
  have hineq : SeparatedMoments.CopyInequalityOnRelation T.side (fun K β => β ∈ D.passageWindow K g) A v :=
    fun E hE hE2 hβ => by
      have hdat := hD T y D hDh g hg hfl₁ E.K E.β hE2 hβ
      exact hAv E hE ⟨hE2, hdat.floor, hdat.le_threshold⟩
  have hcl : ∀ M : ℝ, 1 ≤ M →
      AdmissibleConstants.ClusterConditions T.side M (fun K β => β ∈ D.passageWindow K g) A v := fun M hM => by
    obtain ⟨h₁, h₂, h₃⟩ := hK T.side _ A v M hLs hpos hA hv hM hineq
    obtain ⟨h₄, h₅⟩ := hO T.side _ A v M hLs hpos hA hv hM hineq
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  refine ⟨A, v, hA, hv, hcl, fun S => familyBoundsHold_of_clusterConditions (hcl _ ?_)⟩
  have : 1 ≤ blockCubeSize T S := Nat.one_le_pow _ _ (by have := hLs.2; omega)
  exact_mod_cast this
end YangMills.Construction.SystemOfAdmissibleConstants
end
