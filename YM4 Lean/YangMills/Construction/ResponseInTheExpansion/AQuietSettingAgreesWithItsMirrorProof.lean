import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ClusterExpansionOfAStep.DifferencesOfTheDensities
import YangMills.Construction.ResponseInTheExpansion.AQuietSettingAgreesWithItsMirror
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps StepGas StepSettings BoxAgreement BlockOffsets StepCosts TorusMirror
namespace ResponseInTheExpansion
namespace ColdMirrorAgreement
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem add_mem_supBall {m : ℕ} (o : TorusSite n) {h : Fin 4 → ℤ} (hh : TorusFields.OffsetInBox m h) :
    o + siteOfInt h ∈ supBall o m := by
  unfold supBall
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [supDist_comm]
  exact_mod_cast supDist_add_le_of_offsetInBox o hh
private theorem cellOffset_torusFrame {L n : ℕ} [NeZero L] [NeZero n] (t : ℕ) (hodd : Odd L) (A o : Fin 4 → ℤ)
    (ho : o ∈ centredCube L) :
    cellOffset (F := torusFrame L t n)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth (siteOfInt (blockPoint L A o) : TorusSite (n * L))) = o := by apply _root_.YangMills.Construction.InBoxTransfer.cellOffset_torusFrame <;> assumption
end ColdMirrorAgreement
open ColdMirrorAgreement in
theorem coldMirrorSettingAgreement (hfr : FrameLocality.FrameCoordLocal) : coldMirrorSettingAgreementStatement := by
  classical
  intro R n m _ _ V q γ o hfit hn2 hLn hm hm₀ hm₀m hside₀ hside hull hdis hcore
  have hodd := hfit.L_odd
  have h4 : 2 ≤ 4 * m := by omega
  obtain ⟨m', hm'⟩ : ∃ m', m' = m - R.frameReach - 1 := ⟨_, rfl⟩
  have hmm : m' + R.frameReach + 1 ≤ m := by omega
  rw [← hm']
  set G := hotCaseGround R V q with hG
  set V' := mirrorField m o V with hV'
  have hq : ∀ h, TorusFields.OffsetInBox m h → o + siteOfInt h ∉ q.1 := fun h hh hmem =>
    Finset.disjoint_left.mp hdis hmem (add_mem_supBall o hh)
  have hstore : ∀ h, TorusFields.OffsetInBox m h → q.markAt (o + siteOfInt h) = none := by
    intro h hh
    unfold StepSettings.CoarseState.markAt
    rw [dif_neg (hq h hh)]
  have hC : ∀ h, TorusFields.OffsetInBox m h → o + siteOfInt h ∉ hotCoreSites R V := fun h hh hmem => hq h hh (hull.1 hmem)
  have hθ : ∀ θ, γ.Occupies θ → ∀ h, TorusFields.OffsetInBox m h → o + siteOfInt h ∉ θ.core := fun θ hθ h hh hmem =>
    Finset.disjoint_left.mp (hcore θ hθ) hmem (add_mem_supBall o hh)
  have hcold : IsCold (9 / 8 * R.params.threshold) V' := by
    refine isCold_mirrorField (by omega) o V (by have := hfit.σ_pos; positivity) fun a μ ν hlt hc => ?_
    by_contra hge
    push Not at hge
    have hσ : R.params.threshold ≤ curvature V (o + siteOfInt a) μ ν := by
      have := hfit.σ_pos
      linarith
    have hl : torusLumpOf R.params (o + siteOfInt a) ∈ torusHotLumps R.params V :=
      (mem_torusHotLumps_iff R.params hfit hLn V _).mpr ⟨_, μ, ν, hlt, hσ, o + siteOfInt a, by simp [plaquetteVertices], rfl⟩
    have hz : o + siteOfInt a ∈ torusHotSites R.params V := Finset.mem_biUnion.mpr ⟨_, hl, mem_torusLumpOf_self _⟩
    have h0 : TorusFields.OffsetInBox m a := by simpa using hc 0 (by simp [plaquetteOffsets])
    exact hq a h0 (hull.1 ((mem_thickening _ _ _).mpr ⟨_, hz, by simp [supDist_self]⟩))
  have mono : ∀ {h : Fin 4 → ℤ}, TorusFields.OffsetInBox m' h → TorusFields.OffsetInBox m h := fun hh i =>
    (hh i).trans (by exact_mod_cast (by omega : m' ≤ m))
  have hfi : ∀ (h oo : Fin 4 → ℤ) (i : Fin 4), TorusFields.OffsetInBox m h → oo ∈ centredCube R.params.side →
      (((fineSite R.params.side o h oo, i) : TorusBond (n * R.params.side)) ∈ (G.settingOf γ).free ↔
        ((fineSite R.params.side (0 : TorusSite (4 * m)) h oo, i) : TorusBond (4 * m * R.params.side)) ∈
          chartBonds R.params.side (4 * m)) := by
    intro h oo i hh ho
    have hb := parentBlock_fineSite hodd o h oo ho
    rw [mem_settingOf_free_iff]
    constructor
    · rintro ⟨⟨hm1, -⟩, -⟩
      exact (fineSite_mem_chartBonds_iff (R := R) hodd hn2 h4 o 0 h oo ho i).mp (Finset.mem_filter.mp hm1).1
    · intro hc
      refine ⟨⟨Finset.mem_filter.mpr ⟨(fineSite_mem_chartBonds_iff (R := R) hodd hn2 h4 o 0 h oo ho i).mpr hc, ?_⟩, ?_⟩, ?_⟩
      · show parentBlock R.params.side (fineSite R.params.side o h oo) ∉ hotCoreSites R V
        rw [hb]
        exact hC h hh
      · rintro ⟨s, hs, -⟩
        have hs' : q.markAt (parentBlock R.params.side (fineSite R.params.side o h oo)) = some s := hs
        rw [hb, hstore h hh] at hs'
        cases hs'
      · refine fieldAt_eq_inl_of_forall_not_mem fun θ hθ' hst => hθ θ hθ' h hh ?_
        have := GasSupport.parentBlock_mem_core_of_mem_coreBonds hst
        rwa [show parentBlock R.params.side ((fineSite R.params.side o h oo, i) : TorusBond (n * R.params.side)).1 =
          o + siteOfInt h from hb] at this
  have hfieldNone : ∀ (h oo : Fin 4 → ℤ) (i : Fin 4), TorusFields.OffsetInBox m h → oo ∈ centredCube R.params.side →
      γ.fieldAt ((fineSite R.params.side o h oo, i) : TorusBond (n * R.params.side)) = Sum.inl () := by
    intro h oo i hh ho
    refine fieldAt_eq_inl_of_forall_not_mem fun θ hθ' hst => hθ θ hθ' h hh ?_
    have := GasSupport.parentBlock_mem_core_of_mem_coreBonds hst
    rwa [show parentBlock R.params.side ((fineSite R.params.side o h oo, i) : TorusBond (n * R.params.side)).1 =
      o + siteOfInt h from parentBlock_fineSite hodd o h oo ho] at this
  have hbox : ∀ {h : Fin 4 → ℤ} {b : (Fin 4 → ℤ) × Fin 4}, TorusFields.OffsetInBox m' h →
      TorusFields.BondOffsetInBox R.frameReach b → TorusFields.BondOffsetInBox m (h + b.1, b.2) := by
    intro h b hh hb
    constructor
    · intro i
      have h1 : |h i| ≤ (m' : ℤ) := hh i
      have h2 : |b.1 i| ≤ (R.frameReach : ℤ) := hb.1 i
      have : ((m' : ℤ) + R.frameReach) ≤ m := by omega
      show |h i + b.1 i| ≤ (m : ℤ)
      rw [abs_le] at h1 h2 ⊢
      constructor <;> omega
    · intro i
      have h1 : |h i| ≤ (m' : ℤ) := hh i
      have h2 : |(b.1 + Pi.single b.2 1 : Fin 4 → ℤ) i| ≤ (R.frameReach : ℤ) := hb.2 i
      have : ((m' : ℤ) + R.frameReach) ≤ m := by omega
      have e : ((h + b.1) + Pi.single b.2 1 : Fin 4 → ℤ) i = h i + (b.1 + Pi.single b.2 1 : Fin 4 → ℤ) i := by
        simp only [Pi.add_apply]
        ring
      show |((h + b.1) + Pi.single b.2 1 : Fin 4 → ℤ) i| ≤ (m : ℤ)
      rw [e]
      rw [abs_le] at h1 h2 ⊢
      constructor <;> omega
  refine ⟨hcold, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    have hb' : TorusFields.BondOffsetInBox m b := ⟨fun i => (hb.1 i).trans (by exact_mod_cast (by omega : m' ≤ m)),
      fun i => (hb.2 i).trans (by exact_mod_cast (by omega : m' ≤ m))⟩
    have e := mirrorField_siteOfInt (m := m) hm o V b hb'
    show V (bondFrom o b).1 (bondFrom o b).2 = V' (bondFrom 0 b).1 (bondFrom 0 b).2
    simp only [bondFrom, zero_add]
    exact e.symm
  · rintro ⟨h, oo, i⟩ ⟨hh, ho⟩
    exact hfi h oo i (mono hh) ho
  · rintro ⟨h, oo, i⟩ ⟨hh, ho⟩ hf
    refine (settingOf_fine_of_not_mem_free G γ hf).trans ?_
    rw [show γ.fieldAt (nearBond R.params.side o (h, oo, i)) = Sum.inl () from hfieldNone h oo i (mono hh) ho]
    show q.fieldWithStoredLinks (trivialField _) (fineSite R.params.side o h oo) i =
      (coldChartSetting R V').fine (fineSite R.params.side (0 : TorusSite (4 * m)) h oo) i
    unfold StepSettings.CoarseState.fieldWithStoredLinks
    rw [parentBlock_fineSite hodd o h oo ho, hstore h (mono hh)] <;> rfl
  · rintro ⟨h, oo, i⟩ ⟨hh, ho⟩ -
    have hoff₁ := cellOffset_torusFrame (L := R.params.side) (n := n) R.depth hodd
      (fun i => ((o i).cast : ℤ) + h i) oo ho
    have hoff₂ := cellOffset_torusFrame (L := R.params.side) (n := 4 * m) R.depth hodd
      (fun i => (((0 : TorusSite (4 * m)) i).cast : ℤ) + h i) oo ho
    refine hfr R.params R.anchorRadius R.depth R.frameReach n (4 * m) V V' _ _ hfit hm₀ hside₀ (by omega) rfl
      (hoff₁.trans hoff₂.symm) ?_
    show FieldsAgreeNear V V' (parentBlock R.params.side (fineSite R.params.side o h oo))
      (parentBlock R.params.side (fineSite R.params.side (0 : TorusSite (4 * m)) h oo)) R.frameReach
    rw [parentBlock_fineSite hodd o h oo ho, parentBlock_fineSite hodd 0 h oo ho]
    intro b hb
    have e := mirrorField_siteOfInt (m := m) hm o V (h + b.1, b.2) (hbox hh hb)
    have e1 : ∀ (N : ℕ) (Z : TorusSite N), (bondFrom (Z + siteOfInt h) b).1 = (bondFrom Z (h + b.1, b.2)).1 := by
      intro N Z
      simp only [bondFrom]
      rw [add_assoc, ← siteOfInt_add]
    show V (bondFrom (o + siteOfInt h) b).1 b.2 = V' (bondFrom (0 + siteOfInt h) b).1 b.2
    rw [e1, e1]
    simp only [bondFrom, zero_add]
    exact e.symm
  · intro h oo hh ho
    constructor
    · intro hz
      exfalso
      rcases (mem_settingOf_support_iff G γ _).mp hz with h1 | h2
      · unfold StepSettings.CoarseState.labelAt at h1
        have h1' : (match q.markAt (parentBlock R.params.side (fineSite R.params.side o h oo)) with
          | some s => s.siteLabel (siteOffset (fineSite R.params.side o h oo))
          | none => Sum.inl ()).isRight = true := h1
        rw [parentBlock_fineSite hodd o h oo ho, hstore h (mono hh)] at h1'
        simp at h1'
      · obtain ⟨θ, hθ', hz'⟩ := GasFamily.exists_of_mem_sites h2
        have hc := GasSupport.parentBlock_mem_core (R := R) (θ := θ) (z := fineSite R.params.side o h oo)
          (Finset.mem_union_right _ hz')
        rw [parentBlock_fineSite hodd o h oo ho] at hc
        exact hθ θ hθ' h (mono hh) hc
    · intro hz
      exact absurd hz (Finset.notMem_empty _)
  · intro h oo hz hz' hh ho
    exact absurd hz' (Finset.notMem_empty _)
  · intro h hh
    have ec : toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
        (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (o + siteOfInt h)) = o + siteOfInt h :=
      TopLevelSites.toTorusSite_torusSiteInFrame BlockTrees.stepBlockFrame_period_one _
    have h0 : (0 : Fin 4 → ℤ) ∈ centredCube R.params.side := by
      rw [TopLevelSites.mem_centredCube_iff]
      intro i
      have hpos : (1 : ℤ) ≤ R.params.side := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
      have : 0 ≤ TopLevelSites.halfWidth R.params.side := by
        unfold TopLevelSites.halfWidth
        omega
      simpa using this
    refine ⟨0, h0, ?_, toTorusSite_cellCentre (R := R) (0 : TorusSite (4 * m)) h⟩
    rw [settingOf_bases_torusSiteInFrame, baseAt_eq_inl_of_forall_not_mem fun θ hθ' => hθ θ hθ' h (mono hh)]
    show toTorusSite (n * R.params.side) (G.groundBases (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (o + siteOfInt h))) = _
    unfold StepGas.GasGround.groundBases
    show toTorusSite (n * R.params.side) (match q.markAt (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n
      (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (o + siteOfInt h))) with
      | some s => frameBlockSite R.params.side n _ s.basePoint
      | none => cellCentre (F := stepBlockFrame R.params.side n) 0
          (torusSiteInFrame (stepBlockFrame R.params.side n) 1 (o + siteOfInt h))) = _
    rw [ec, hstore h (mono hh)]
    exact toTorusSite_cellCentre (R := R) o h
end ResponseInTheExpansion
end YangMills.Construction
end
