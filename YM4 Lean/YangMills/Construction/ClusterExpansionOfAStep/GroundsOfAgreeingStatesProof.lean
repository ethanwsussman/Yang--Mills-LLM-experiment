import YangMills.Construction.ClusterExpansionOfAStep.GroundsOfAgreeingStates
import YangMills.Construction.ClusterExpansionOfAStep.HullReadOnAClass
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps StepSettings StepGas
namespace ClusterExpansionOfAStep
namespace GroundsAgreeNearProof
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem exists_mem_components {r : ℕ} {Y : Finset (TorusSite n)} {z : TorusSite n} (hz : z ∈ Y) :
    ∃ X ∈ chainComponents r Y, z ∈ X := by apply _root_.YangMills.Construction.TorusLumps.exists_mem_chainComponents <;> assumption
theorem markAt_restrict (q : CoarseState R n) {X : Finset (TorusSite n)} {z : TorusSite n} (hz : z ∈ X) :
    (q.restrict X).markAt z = q.markAt z := by
  classical
  unfold CoarseState.markAt CoarseState.restrict
  by_cases h : z ∈ q.1
  · rw [dif_pos (Finset.mem_inter.mpr ⟨h, hz⟩), dif_pos h]
  · rw [dif_neg (fun h' => h (Finset.mem_inter.mp h').1), dif_neg h]
theorem isAdmissibleOn_of_coarseFactor_ne_zero {V : TorusField n} {q : CoarseState R n}
    {X : Finset (TorusSite n)} (h : coarseFactor V q X ≠ 0) :
    (q.restrict X).IsAdmissibleCoarseState (hotNeighbourhoodOn R X V) X := by
  classical
  by_contra hn
  apply h
  unfold coarseFactor admissibilityIndicator
  rw [if_neg hn]
  ring
theorem isCore_of_mem_hotCoreSites (hRead : HullRestrictedToComponent) (hadm : R.params.Admissible)
    (hr : 2 ^ 16 ≤ R.nextRange) (hside : R.params.side ∣ n)
    {V : TorusField n} {q : CoarseState R n} (hq : IsHullState R.params R.nextRange V q.1)
    (hfac : ∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) {z : TorusSite n}
    (hz : z ∈ hotCoreSites R V) :
    ∃ s, q.markAt z = some s ∧ s.isCore = true := by
  classical
  have hzY : z ∈ q.1 := hq.1 hz
  obtain ⟨X, hX, hzX⟩ := exists_mem_components (r := R.nextRange) hzY
  have hA := isAdmissibleOn_of_coarseFactor_ne_zero (hfac X hX)
  have hon : z ∈ hotNeighbourhoodOn R X V := (hRead R n V q.1 X z hadm hr hside hq hX hzX).mpr hz
  have hzone := hA.subset_dataZone hon
  unfold CoarseState.markedZone at hzone
  have hsome := (Finset.mem_filter.mp hzone).2
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨s, ?_, ?_⟩
  · rw [← markAt_restrict q hzX]
    exact hs
  · rw [hA.isCore_eq z s hs]
    simpa using hon
theorem mem_hotCoreSites_of_isCore (hRead : HullRestrictedToComponent) (hadm : R.params.Admissible)
    (hr : 2 ^ 16 ≤ R.nextRange) (hside : R.params.side ∣ n)
    {V : TorusField n} {q : CoarseState R n} (hq : IsHullState R.params R.nextRange V q.1)
    (hfac : ∀ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X ≠ 0) {z : TorusSite n}
    {s : BlockLabels R.labels.Ω R.params.side}
    (hs : q.markAt z = some s) (hb : s.isCore = true) : z ∈ hotCoreSites R V := by
  classical
  have hzY : z ∈ q.1 := by
    by_contra hn
    unfold CoarseState.markAt at hs
    rw [dif_neg hn] at hs
    exact absurd hs (by simp)
  obtain ⟨X, hX, hzX⟩ := exists_mem_components (r := R.nextRange) hzY
  have hA := isAdmissibleOn_of_coarseFactor_ne_zero (hfac X hX)
  have hs' : (q.restrict X).markAt z = some s := by rw [markAt_restrict q hzX]; exact hs
  have hdec := hA.isCore_eq z s hs'
  rw [hb] at hdec
  have hon : z ∈ hotNeighbourhoodOn R X V := by simpa using hdec.symm
  exact (hRead R n V q.1 X z hadm hr hside hq hX hzX).mp hon
end GroundsAgreeNearProof
open GroundsAgreeNearProof in
theorem groundsAgreeNear_of_statesAgreeNear (hRead : HullRestrictedToComponent) :
    GroundsAgreeNearOfStatesAgreeNear := by
  classical
  intro R n n' _ _ V V' Y ω y y' m hadm hr hside hq hfac
  have hrec : ∀ (Y' : Finset (TorusSite n')) (ω' : Y' → CoarseLabel R.labels.Ω R.params.side),
      StatesAgreeNear R.params V V' Y Y' ω ω' y y' m → ∀ h, OffsetInBox m h →
      CoarseState.markAt (⟨Y, ω⟩ : CoarseState R n) (y + siteOfInt h) =
        CoarseState.markAt (⟨Y', ω'⟩ : CoarseState R n') (y' + siteOfInt h) := by
    intro Y' ω' hag h hh
    obtain ⟨_, _, _, hmem, hlab, _⟩ := hag
    unfold CoarseState.markAt
    by_cases h1 : y + siteOfInt h ∈ Y
    · have h2 : y' + siteOfInt h ∈ Y' := (hmem h hh).mp h1
      simp only [dif_pos h1, dif_pos h2]
      rw [hlab h hh h1 h2 (Finset.mem_univ _)]
    · have h2 : y' + siteOfInt h ∉ Y' := fun h' => h1 ((hmem h hh).mpr h')
      simp only [dif_neg h1, dif_neg h2]
  constructor
  · intro Y' ω' hside' hq' hfac' hag
    have hs := hrec Y' ω' hag
    refine ⟨hag.1, hag.2.1, hag.2.2.1, fun h hh => ?_, hs⟩
    constructor
    · intro hz
      obtain ⟨s, h1, h2⟩ := isCore_of_mem_hotCoreSites hRead hadm hr hside (q := ⟨Y, ω⟩) hq hfac hz
      exact mem_hotCoreSites_of_isCore hRead hadm hr hside' (q := ⟨Y', ω'⟩) hq' hfac'
        (by rw [← hs h hh]; exact h1) h2
    · intro hz
      obtain ⟨s, h1, h2⟩ := isCore_of_mem_hotCoreSites hRead hadm hr hside' (q := ⟨Y', ω'⟩) hq' hfac' hz
      exact mem_hotCoreSites_of_isCore hRead hadm hr hside (q := ⟨Y, ω⟩) hq hfac
        (by rw [hs h hh]; exact h1) h2
  · intro ω' hag
    have hs := hrec ∅ ω' hag
    have hempty : (⟨∅, ω'⟩ : CoarseState R n') = emptyCoarseState R := by
      unfold emptyCoarseState
      congr 1
      funext z
      exact absurd z.2 (Finset.notMem_empty _)
    rw [hempty] at hs
    refine ⟨hag.1, hag.2.1, hag.2.2.1, fun h hh => ?_, hs⟩
    change y + siteOfInt h ∈ hotCoreSites R V ↔ y' + siteOfInt h ∈ (∅ : Finset (TorusSite n'))
    simp only [Finset.notMem_empty, iff_false]
    intro hz
    have := (hag.2.2.2.1 h hh).mp (hq.1 hz)
    exact absurd this (Finset.notMem_empty _)
end ClusterExpansionOfAStep
end YangMills.Construction
end
