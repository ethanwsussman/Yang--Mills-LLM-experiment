import YangMills.Construction.Lattice.BlockFieldsOnTheWholeLattice
import YangMills.Construction.Lattice.LiftingIsConsistentWithTheAverages
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
private theorem blockFieldAtLevel_facts (hL : LiftConsistentWithAverages)
    {L m K : ℕ} (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K) (n : ℕ)
    (hn : n + 1 ≤ K) (V : BondAtLevel L m K (n + 1) → Matrices.ComplexMatrix2)
    (hV : V ∈ gaugeFieldsAtLevel L m K (n + 1)) :
    bareLift V ∈ gaugeFieldsAtLevel L m K 0 ∧
      (∀ j : ℕ, j ≤ n + 1 →
        averagedLift (Averaging.smoothingRadius L) j V =
          blockFieldAtLevel (Averaging.smoothingRadius L) j (bareLift V) ∧
        averagedLift (Averaging.smoothingRadius L) j V ∈ gaugeFieldsAtLevel L m K j ∧
        (∀ b : BondAtLevel L m K j, EndsInOneBlock (n + 1) b →
          averagedLift (Averaging.smoothingRadius L) j V b = 1) ∧
        ∀ (c : BondAtLevel L m K (n + 1)) (b : BondAtLevel L m K j), CoversBond c b →
          averagedLift (Averaging.smoothingRadius L) j V b = V c) ∧
      blockAverageStep (Averaging.smoothingRadius L) n
          (averagedLift (Averaging.smoothingRadius L) n V) =
        blockFieldAtLevel (Averaging.smoothingRadius L) (n + 1) (bareLift V) ∧
      blockFieldAtLevel (Averaging.smoothingRadius L) (n + 1) (bareLift V) = V := by
  have hclosed : IsReversalClosed (univ : Set (BondAtLevel L m K (n + 1))) :=
    fun _ _ => mem_univ _
  have hcompact : IsGaugeField compactGaugeGroup (univ : Set (BondAtLevel L m K (n + 1))) V := hV
  obtain ⟨-, -, -, -, hR, hW, -⟩ := hL L m K hS hm hK (n + 1) hn univ hclosed V (Or.inl hcompact)
  obtain ⟨hcons, -⟩ := hR hcompact
  obtain ⟨hbare, hlev⟩ := hW rfl hV
  obtain ⟨hvals, -, htop, -⟩ := hcons
  have hfield : ∀ j ≤ n + 1,
      (compactLevelLifts (K := K) univ V j).field = averagedLift (Averaging.smoothingRadius L) j V :=
    fun j hj => (hlev j hj).2.2
  have htop' : blockFieldAtLevel (Averaging.smoothingRadius L) (n + 1) (bareLift V) = V := by
    funext b
    have hb : b ∈ (compactLevelLifts (K := K) univ V (n + 1)).support := by
      rw [(hlev (n + 1) le_rfl).1]; exact mem_univ _
    have h := htop.2 b hb
    rw [hfield (n + 1) le_rfl] at h
    exact h
  refine ⟨hbare, fun j hj => ⟨rfl, ?_, ?_, ?_⟩, rfl, htop'⟩
  · rw [← hfield j hj]; exact (hlev j hj).2.1
  · intro b hb
    rw [← hfield j hj]
    exact (((hvals j hj).2.2.2 b).1 hb).2
  · intro c b hb
    rw [← hfield j hj]
    exact (((hvals j hj).2.2.2 b).2.1 c (mem_univ _) hb).2
private theorem bareLift_trivialGaugeField {L m K k : ℕ} :
    bareLift (trivialGaugeField : BondAtLevel L m K k → Matrices.ComplexMatrix2) =
      (trivialGaugeField : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) := by
  funext b
  simp [bareLift, liftToFinerLevel, trivialGaugeField]
theorem BlockFieldLifts.statement_holds (hL : LiftConsistentWithAverages) :
    BlockFieldLifts.Statement := by
  intro L m K hS hm hK
  refine ⟨fun n hn V hV => blockFieldAtLevel_facts hL hS hm hK n hn V hV, fun q hq => ?_⟩
  cases q with
  | zero => rfl
  | succ n =>
    have hid : (trivialGaugeField : BondAtLevel L m K (n + 1) → Matrices.ComplexMatrix2) ∈
        gaugeFieldsAtLevel L m K (n + 1) := by
      refine ⟨fun _ _ => ?_, fun _ _ => ?_⟩
      · exact one_mem _
      · simp [trivialGaugeField]
    have h := (blockFieldAtLevel_facts hL hS hm hK n hq _ hid).2.2.2
    rw [bareLift_trivialGaugeField] at h
    exact h
end YangMills.Construction.PeriodicLattice
