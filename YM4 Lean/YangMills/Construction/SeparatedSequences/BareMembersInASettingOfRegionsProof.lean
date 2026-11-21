import YangMills.Construction.SeparatedSequences.ClassExpansionsInASettingOfRegions
import YangMills.Construction.SeparatedSequences.ClassSiteFunctionsInASettingOfRegions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses.FineMembersPaired
open SingleSequence SingleSequence.SequenceData
variable {α α' : Type} {r : α → α' → Prop}
def equivOfPairsUniquely (h : PairsUniquely r) : α ≃ α' :=
  Equiv.ofBijective (fun p => (h.1 p).choose)
    ⟨fun p q hpq => by
        have hp := (h.1 p).choose_spec.1
        have hq := (h.1 q).choose_spec.1
        simp only at hpq
        rw [← hpq] at hq
        exact (h.2 _).unique hp hq,
      fun p' => by
        obtain ⟨p, hp, -⟩ := h.2 p'
        exact ⟨p, ((h.1 p).choose_spec.2 p' hp).symm⟩⟩
theorem rel_equivOfPairsUniquely (h : PairsUniquely r) (p : α) : r p (equivOfPairsUniquely h p) :=
  (h.1 p).choose_spec.1
end YangMills.Construction.SeparatedClasses.FineMembersPaired
end
