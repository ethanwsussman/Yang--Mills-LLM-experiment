import YangMills.Construction.ClusterExpansionOfAStep.AttachedClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps StepSettings StepGas StepCosts BlockTrees
  ColdStepAtMirrorFrames
namespace BlockZones
section Sites
variable {n L : ℕ} [NeZero L]
theorem blockSite_parentBlock_siteOffset (x : TorusSite (n * L)) :
    blockSite (parentBlock L x) (siteOffset x) = x := by
  funext i
  set u : ℤ := ((x i).cast : ℤ) with hu
  set m : ℤ := ((L : ℤ) - 1) / 2 with hm
  have hLpos : (0 : ℤ) < L := by exact_mod_cast NeZero.pos L
  set q : ℤ := (u + m) / L with hq
  set ρ' : ℤ := (u + m) % L with hρ
  have h0 : 0 ≤ ρ' := Int.emod_nonneg _ hLpos.ne'
  have h1 : ρ' < L := Int.emod_lt_of_pos _ hLpos
  have hdec : u + m = L * q + ρ' := (Int.mul_ediv_add_emod _ _).symm
  have hb : parentBlock L x i = ((q : ℤ) : ZMod n) := rfl
  have hc : (((parentBlock L x i).cast : ℤ) : ZMod n) = ((q : ℤ) : ZMod n) := by
    rw [ZMod.intCast_zmod_cast, hb]
  obtain ⟨e, he⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hc
  have hp : (((siteOffset (L := L) x i : Fin L) : ℕ) : ℤ) = ρ' := by
    unfold StepSettings.siteOffset
    simp only [Fin.ofNat, Fin.val_mk]
    have hlt : ρ'.toNat < L := by omega
    rw [Nat.mod_eq_of_lt hlt]
    exact Int.toNat_of_nonneg h0
  show (((L : ℤ) * (((parentBlock L x i).cast : ℤ)) +
      ((((siteOffset (L := L) x i : Fin L) : ℕ) : ℤ) - ((L : ℤ) - 1) / 2) : ℤ) : ZMod (n * L)) = x i
  rw [hp, ← hm]
  have hxi : x i = ((u : ℤ) : ZMod (n * L)) := by
    rw [hu]
    exact (ZMod.intCast_zmod_cast (x i)).symm
  rw [hxi]
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2
  refine ⟨e, ?_⟩
  push_cast
  have e2 : (((parentBlock L x i).cast : ℤ)) = q - n * e := by linarith
  rw [e2]
  have : u = L * q + ρ' - m := by linarith
  rw [this]
  ring
end Sites
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem markAt_coarseStateOf (C : Finset (TorusSite n)) (W : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) (y : TorusSite n) :
    (coarseStateOf R C W Yt ωt bad b).markAt y = (open Classical in
      if y ∈ storedBlocks R.params.side R.range bad Yt C then
        some (blockConfigAt R C (storedBlocks R.params.side R.range bad Yt C) W Yt ωt bad b y)
      else none) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.markAt_coarseStateOf <;> assumption
section Anchors
variable {L : ℕ} [NeZero L]
theorem parentBlock_mem_coreBlocks {r : ℕ} {θ : Finset (TorusSite (n * L))} {z : TorusSite (n * L)}
    (hz : z ∈ θ) : parentBlock L z ∈ coreBlocks L r θ := by
  classical
  unfold coreBlocks
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · unfold sitesInBlocks
    simp
  · exact (mem_thickening _ _ _).mpr ⟨z, hz, by rw [supDist_self]; exact Nat.zero_le _⟩
open Classical in
theorem attachedSites_eq_of_subset {r : ℕ} {bad : Finset (TorusBond (n * L))}
    {Yt : Finset (TorusSite (n * L))} {C : Finset (TorusSite n)}
    (h : bad.image Prod.fst ∪ Yt ⊆ attachedSites L r bad Yt C) :
    attachedSites L r bad Yt C = sitesInBlocks L C ∪ bad.image Prod.fst ∪ Yt := by
  apply Finset.Subset.antisymm
  · intro z hz
    unfold attachedSites clusterComponents at hz
    simp only [Finset.mem_biUnion, Finset.mem_filter, id] at hz
    obtain ⟨X, ⟨hX, _⟩, hzX⟩ := hz
    have := subset_of_mem_chainComponents hX hzX
    simp only [Finset.mem_union] at this ⊢
    tauto
  · intro z hz
    simp only [Finset.mem_union] at hz
    rcases hz with (hz | hz) | hz
    · have hzB : z ∈ bad.image Prod.fst ∪ Yt ∪ sitesInBlocks L C := Finset.mem_union_right _ hz
      obtain ⟨X, hX, hzX⟩ := exists_mem_chainComponents (r := 10 * r) hzB
      unfold attachedSites clusterComponents
      simp only [Finset.mem_biUnion, Finset.mem_filter, id]
      exact ⟨X, ⟨hX, ⟨z, Finset.mem_inter.mpr ⟨hzX, hz⟩⟩⟩, hzX⟩
    · exact h (Finset.mem_union_left _ hz)
    · exact h (Finset.mem_union_right _ hz)
end Anchors
structure IsRetainedZone (G : GasGround R n) (Z : Finset (TorusSite n)) : Prop where
  zone_eq : Z = G.cut ∪ coreBlocks R.params.side R.range G.anchorSites
  recorded_iff : ∀ y, (G.state.markAt y).isSome = true ↔ y ∈ Z
  bond_iff : ∀ b, G.IsRecorded b ↔
    parentBlock R.params.side b.1 ∈ Z ∧
      parentBlock R.params.side (b.1 + TorusFields.unitStep (n * R.params.side) b.2) ∈ Z
theorem exists_isAdmissibleZone (G : GasGround R n) (hG : G.IsAdmissibleGround) : ∃ Z, IsRetainedZone G Z := by
  classical
  rcases hG with hc | hh
  · have hrec : ∀ y, G.state.markAt y = none := by
      intro y
      unfold StepSettings.CoarseState.markAt
      rw [dif_neg]
      rw [hc.state_empty]
      simp
    have hbad : G.recordedBad = ∅ := by
      unfold StepGas.GasGround.recordedBad
      simp [hrec]
    have hsites : G.recordedSites = ∅ := by
      unfold StepGas.GasGround.recordedSites StepSettings.CoarseState.labelAt
      simp [hrec]
    have hatt : G.anchorSites = ∅ := by
      unfold StepGas.GasGround.anchorSites
      rw [hbad, hsites, hc.cut_eq]
      simp [sitesInBlocks]
    refine ⟨∅, ?_, fun y => by simp [hrec], fun b => ?_⟩
    · rw [hatt, hc.cut_eq]
      unfold coreBlocks
      simp [thickening]
    · unfold StepGas.GasGround.IsRecorded
      simp [hrec]
  · obtain ⟨W, Yt, ωt, bad, b, hq, _, _, hall, _, _, _⟩ := hh.exists_state
    set Z := storedBlocks R.params.side R.range bad Yt G.cut with hZ
    have hrec : ∀ y, G.state.markAt y =
        if y ∈ Z then some (blockConfigAt R G.cut Z W Yt ωt bad b y) else none := by
      intro y
      rw [← hq, markAt_coarseStateOf]
    have hatt := attachedSites_eq_of_subset hall
    have hcore : ∀ z ∈ bad.image Prod.fst ∪ Yt, parentBlock R.params.side z ∈ Z := fun z hz => by
      rw [hZ]
      unfold storedBlocks
      exact Finset.mem_union_right _ (parentBlock_mem_coreBlocks (hall hz))
    have hbad : G.recordedBad = bad := by
      ext c
      unfold StepGas.GasGround.recordedBad
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrec]
      constructor
      · rintro ⟨s, hs, hb⟩
        by_cases hy : parentBlock R.params.side c.1 ∈ Z
        · rw [if_pos hy] at hs
          have := Option.some.inj hs
          subst this
          unfold blockConfigAt at hb
          simp only [decide_eq_true_eq, blockSite_parentBlock_siteOffset] at hb
          exact hb
        · rw [if_neg hy] at hs
          exact absurd hs (by simp)
      · intro hc
        have hy : parentBlock R.params.side c.1 ∈ Z :=
          hcore _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc))
        refine ⟨_, if_pos hy, ?_⟩
        unfold blockConfigAt
        simp only [decide_eq_true_eq, blockSite_parentBlock_siteOffset]
        exact hc
    have hsites : G.recordedSites = Yt := by
      ext z
      unfold StepGas.GasGround.recordedSites StepSettings.CoarseState.labelAt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrec]
      constructor
      · intro h
        by_cases hy : parentBlock R.params.side z ∈ Z
        · rw [if_pos hy] at h
          simp only [blockConfigAt, blockSite_parentBlock_siteOffset] at h
          by_contra hz
          simp [hz] at h
        · rw [if_neg hy] at h
          simp at h
      · intro hz
        have hy : parentBlock R.params.side z ∈ Z := hcore _ (Finset.mem_union_right _ hz)
        rw [if_pos hy]
        simp only [blockConfigAt, blockSite_parentBlock_siteOffset]
        simp [hz]
    have hattG : G.anchorSites = attachedSites R.params.side R.range bad Yt G.cut := by
      rw [hatt]
      unfold StepGas.GasGround.anchorSites
      rw [hbad, hsites]
    refine ⟨Z, ?_, fun y => ?_, fun c => ?_⟩
    · rw [hattG, hZ]
      rfl
    · rw [hrec]
      by_cases hy : y ∈ Z
      · simp [hy]
      · simp [hy]
    · unfold StepGas.GasGround.IsRecorded
      simp only [hrec]
      constructor
      · rintro ⟨s, hs, hf⟩
        by_cases hy : parentBlock R.params.side c.1 ∈ Z
        · rw [if_pos hy] at hs
          have := Option.some.inj hs
          subst this
          refine ⟨hy, ?_⟩
          by_contra hz
          unfold blockConfigAt at hf
          simp [blockSite_parentBlock_siteOffset, hz] at hf
        · rw [if_neg hy] at hs
          exact absurd hs (by simp)
      · rintro ⟨h1, h2⟩
        refine ⟨_, if_pos h1, ?_⟩
        unfold blockConfigAt
        simp [blockSite_parentBlock_siteOffset, h2]
section Distance
variable {G : GasGround R n} {γ : GasFamily R n} {Z : Finset (TorusSite n)}
theorem parentBlock_mem_coreBlocks_of_near {L : ℕ} [NeZero L] {r : ℕ} {θ : Finset (TorusSite (n * L))}
    {x z : TorusSite (n * L)} (hz : z ∈ θ) (h : supDist x z ≤ 4 * r) :
    parentBlock L x ∈ coreBlocks L r θ := by
  classical
  unfold coreBlocks
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · unfold sitesInBlocks
    simp
  · exact (mem_thickening _ _ _).mpr ⟨z, hz, h⟩
theorem mem_free_settingOf {b : TorusBond (n * R.params.side)} (hb : b ∈ (G.settingOf γ).free) :
    b ∈ markedBonds R G.cut ∧ ¬ G.IsRecorded b ∧ γ.fieldAt b = Sum.inl () := by
  classical
  have h1 : b ∈ (G.freeBonds.filter fun b => γ.fieldAt b = Sum.inl ()) := hb
  obtain ⟨h2, h3⟩ := Finset.mem_filter.mp h1
  unfold StepGas.GasGround.freeBonds at h2
  obtain ⟨h4, h5⟩ := Finset.mem_filter.mp h2
  exact ⟨h4, h5, h3⟩
theorem supDist_bond_ends_le (b : TorusBond (n * R.params.side)) {z : TorusSite (n * R.params.side)}
    (h : supDist b.1 z + R.params.side + 1 < 4 * R.range) (hL : 1 ≤ R.params.side) :
    supDist b.1 z ≤ 4 * R.range ∧
      supDist (b.1 + TorusFields.unitStep (n * R.params.side) b.2) z ≤ 4 * R.range := by
  refine ⟨by omega, ?_⟩
  have h1 := supDist_triangle (b.1 + TorusFields.unitStep (n * R.params.side) b.2) b.1 z
  have h2 := supDist_add_unitStep_le b.1 b.2
  rw [supDist_comm] at h2
  omega
theorem far_of_mem_anchorSites (hZ : IsRetainedZone G Z) {b : TorusBond (n * R.params.side)}
    (hb : b ∈ (G.settingOf γ).free) {z : TorusSite (n * R.params.side)} (hz : z ∈ G.anchorSites) :
    4 * R.range ≤ supDist b.1 z + R.params.side + 1 := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hL : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  obtain ⟨h1, h2⟩ := supDist_bond_ends_le b hlt hL
  apply (mem_free_settingOf hb).2.1
  rw [hZ.bond_iff, hZ.zone_eq]
  exact ⟨Finset.mem_union_right _ (parentBlock_mem_coreBlocks_of_near hz h1),
    Finset.mem_union_right _ (parentBlock_mem_coreBlocks_of_near hz h2)⟩
theorem far_of_mem_supportSites {b : TorusBond (n * R.params.side)} (hb : b ∈ (G.settingOf γ).free)
    {θ : GasSupport R n} (hθ : γ.Occupies θ) {z : TorusSite (n * R.params.side)} (hz : z ∈ θ.sites) :
    4 * R.range ≤ supDist b.1 z + R.params.side + 1 := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hL : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  obtain ⟨h1, h2⟩ := supDist_bond_ends_le b hlt hL
  have hst : b ∈ θ.coreBonds := by
    unfold StepGas.GasSupport.coreBonds
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, parentBlock_mem_coreBlocks_of_near hz h1,
      parentBlock_mem_coreBlocks_of_near hz h2⟩
  have hf := (mem_free_settingOf hb).2.2
  unfold StepGas.GasFamily.fieldAt at hf
  rw [dif_pos ⟨θ, hθ, hst⟩] at hf
  exact absurd hf (by simp)
theorem far_of_mem_support (hZ : IsRetainedZone G Z) {b : TorusBond (n * R.params.side)}
    (hb : b ∈ (G.settingOf γ).free) {z : TorusSite (n * R.params.side)} (hz : z ∈ (G.settingOf γ).support) :
    4 * R.range ≤ supDist b.1 z + R.params.side + 1 := by
  classical
  have h1 : z ∈ G.recordedSites ∪ γ.sites := hz
  rcases Finset.mem_union.mp h1 with h | h
  · refine far_of_mem_anchorSites hZ hb ?_
    unfold StepGas.GasGround.anchorSites
    exact Finset.mem_union_right _ h
  · obtain ⟨θ, hθ, hzθ⟩ := GasFamily.exists_of_mem_sites h
    refine far_of_mem_supportSites hb hθ ?_
    show z ∈ clusterSupportSites R.params.side θ
    unfold clusterSupportSites
    exact Finset.mem_union_right _ hzθ
theorem far_of_mem_bad (hZ : IsRetainedZone G Z) {b c : TorusBond (n * R.params.side)}
    (hb : b ∈ (G.settingOf γ).free) (hc : c ∈ (G.settingOf γ).bad) :
    4 * R.range ≤ supDist b.1 c.1 + R.params.side + 1 := by
  classical
  have h1 : c ∈ G.recordedBad ∪ (Finset.univ.filter fun θ => γ.Occupies θ).biUnion Prod.fst ∪
    (chartBonds R.params.side n).filter fun b => parentBlock R.params.side b.1 ∈ G.cut := hc
  simp only [Finset.mem_union] at h1
  rcases h1 with (h | h) | h
  · refine far_of_mem_anchorSites hZ hb ?_
    unfold StepGas.GasGround.anchorSites
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h))
  · obtain ⟨θ, hθ, hc'⟩ := Finset.mem_biUnion.mp h
    refine far_of_mem_supportSites hb (Finset.mem_filter.mp hθ).2 ?_
    show c.1 ∈ clusterSupportSites R.params.side θ
    unfold clusterSupportSites
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc')
  · refine far_of_mem_anchorSites hZ hb ?_
    unfold StepGas.GasGround.anchorSites
    refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
    unfold sitesInBlocks
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩
theorem far_of_parentBlock_mem_cut (hZ : IsRetainedZone G Z) {b : TorusBond (n * R.params.side)}
    (hb : b ∈ (G.settingOf γ).free) {z : TorusSite (n * R.params.side)}
    (hz : parentBlock R.params.side z ∈ G.cut) : 4 * R.range ≤ supDist b.1 z + R.params.side + 1 := by
  classical
  refine far_of_mem_anchorSites hZ hb ?_
  unfold StepGas.GasGround.anchorSites
  refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
  unfold sitesInBlocks
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
end Distance
section Fields
variable {s : ChartSetting R n}
theorem not_mem_free_of_isAxialTreeBond (hc : s.free ⊆ chartBonds R.params.side n)
    {z : TorusSite (n * R.params.side)} {i : Fin 4}
    (ht : IsAxialTreeBond (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 z, i)) : (z, i) ∉ s.free := fun h => by
  classical
  have := hc h
  unfold chartBonds at this
  exact (Finset.mem_filter.mp this).2 ht
theorem blockGauge_field (hc : s.free ⊆ chartBonds R.params.side n) (hL : Odd R.params.side) (hn : 2 ≤ n)
    (η : FreeCoords s.free) (x : TorusSite (n * R.params.side)) :
    blockGauge R.params.side (s.field η) x = blockGauge R.params.side s.fine x := by
  classical
  apply blockGauge_congr hL hn
  intro z i _ ht
  unfold StepSettings.ChartSetting.field
  rw [dif_neg (not_mem_free_of_isAxialTreeBond hc ht)]
omit [NeZero n] in
theorem field_of_not_mem_free {η : FreeCoords s.free} {b : TorusBond (n * R.params.side)} (hb : b ∉ s.free) :
    s.field η b.1 b.2 = s.fine b.1 b.2 := by
  classical
  unfold StepSettings.ChartSetting.field
  exact dif_neg hb
theorem chartCoord_field_of_not_mem_free (hc : s.free ⊆ chartBonds R.params.side n) (hL : Odd R.params.side)
    (hn : 2 ≤ n) (η : FreeCoords s.free) {b : TorusBond (n * R.params.side)} (hb : b ∉ s.free) :
    chartCoord R.params s.coarse (s.field η) b = chartCoord R.params s.coarse s.fine b := by
  rw [chartCoord_eq, chartCoord_eq, blockGauge_field hc hL hn, blockGauge_field hc hL hn,
    field_of_not_mem_free hb]
theorem chartCoord_field_of_mem_free (hc : s.free ⊆ chartBonds R.params.side n) (hL : Odd R.params.side)
    (hn : 2 ≤ n) (η : FreeCoords s.free) (b : s.free)
    (hw : ‖((s.frame b.1 + toImaginary (η b) : imaginaryQuaternions) : ℍ[ℝ])‖ < Real.pi) :
    chartCoord R.params s.coarse (s.field η) b.1 = s.frame b.1 + toImaginary (η b) := by
  classical
  have hv : s.field η b.1.1 b.1.2 = chartLink s b.1.1 b.1.2 (s.frame b.1 + toImaginary (η b)) := by
    unfold StepSettings.ChartSetting.field
    rw [dif_pos b.2]
  rw [chartCoord_eq_minimalLog R.params s.coarse _ b.1 (expUnit (s.frame b.1 + toImaginary (η b))) ?_]
  · exact minimalLog_expUnit hw
  · rw [blockGauge_field hc hL hn, blockGauge_field hc hL hn, hv]
    unfold chartLink
    rfl
end Fields
end BlockZones
end YangMills.Construction
end
