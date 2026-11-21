import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.ResponseInTheExpansion.MirrorOfAColdBoxIsCold
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TopLevelSites
private theorem siteOfInt_mem_supBall {n : ℕ} [NeZero n] {m : ℕ} (c : Fin 4 → ℤ) (hc : OffsetInBox m c)
    (o : TorusSite n) : o + siteOfInt c ∈ supBall o (m : ℝ) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have h : supDist (o + siteOfInt c) o ≤ m := by
    unfold supDist
    refine Finset.sup_le fun i _ => ?_
    have e : ((o + siteOfInt c : TorusSite n) i - o i) = ((c i : ℤ) : ZMod n) := by
      simp [siteOfInt]
    rw [e]
    have h1 := ZMod.natAbs_min_of_le_div_two n (((c i : ℤ) : ZMod n).valMinAbs) (c i) (ZMod.coe_valMinAbs _)
      (ZMod.natAbs_valMinAbs_le _)
    have h2 := hc i
    have h3 : (c i).natAbs ≤ m := by
      have := abs_le.mp h2
      omega
    exact h1.trans h3
  exact_mod_cast h
theorem mirrorOfColdBallSmallCurvature : mirrorOfColdBallSmallCurvatureStatement := by
  intro L t m n _ o V g s hs hm _ _ hV
  have : NeZero (4 * m) := ⟨by omega⟩
  have hcold : ∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν →
      (∀ d ∈ TorusLumps.plaquetteOffsets μ ν, OffsetInBox m (a + d)) →
      curvature (TorusFields.gaugeTransform g V) (o + siteOfInt a) μ ν < s := by
    intro a μ ν hlt hbox
    rw [curvature_gaugeTransform]
    refine hV (o + siteOfInt a, μ, ν) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, fun z hz => ?_⟩)
    have e : ∀ d : Fin 4 → ℤ, o + siteOfInt (a + d) = o + siteOfInt a + siteOfInt d := by
      intro d
      funext i
      simp [siteOfInt, add_assoc]
    have ev1 : ∀ i : Fin 4, (siteOfInt (Pi.single i 1 : Fin 4 → ℤ) : TorusSite n) = unitStep n i := by
      intro i
      funext l
      by_cases h : l = i
      · subst h
        simp [siteOfInt, unitStep]
      · simp [siteOfInt, unitStep, h]
    have hlist : ∀ d ∈ TorusLumps.plaquetteOffsets μ ν, o + siteOfInt a + siteOfInt d ∈ supBall o (m : ℝ) := by
      intro d hd
      rw [← e]
      exact siteOfInt_mem_supBall _ (hbox d hd) o
    simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · have := hlist 0 (by simp [TorusLumps.plaquetteOffsets])
      simpa [TorusLumps.siteOfInt_zero_offset] using this
    · have := hlist (Pi.single μ 1) (by simp [TorusLumps.plaquetteOffsets])
      rwa [ev1] at this
    · have := hlist (Pi.single ν 1) (by simp [TorusLumps.plaquetteOffsets])
      rwa [ev1] at this
    · have := hlist (Pi.single μ 1 + Pi.single ν 1) (by simp [TorusLumps.plaquetteOffsets])
      have e2 : (siteOfInt (Pi.single μ 1 + Pi.single ν 1 : Fin 4 → ℤ) : TorusSite n) = unitStep n μ + unitStep n ν := by
        rw [← ev1, ← ev1]
        funext i
        simp [siteOfInt]
      rw [e2, ← add_assoc] at this
      exact this
  have h1 := TorusMirror.isCold_mirrorField hm o (TorusFields.gaugeTransform g V) hs hcold
  rintro ⟨z, μ, ν⟩ hlt
  unfold reflectedTopField
  rw [reflectedField_readAtLevel (F := torusFrame L t n) (n := n) (fun _ => rfl) hm,
    plaquetteDefect_readAtLevel_eq
      (period_top_of_extent (F := ColdStepAtMirrorFrames.reflectedFrame (torusFrame L t n) m) (n := 4 * m) fun _ => rfl)]
  exact h1 _ _ _ hlt
end YangMills.Construction.ResponseInTheExpansion
end
