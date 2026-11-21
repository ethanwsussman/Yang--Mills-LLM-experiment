import YangMills.Construction.TorusOrFourSpace.CountableChoicesAndFamiliesOfDenseSets
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicSpace.Kind.CountableDenseFamilies
theorem statement_holds : Statement := by
  intro D E
  refine ⟨fun C => ?_, fun C _ => ?_, fun C _ n φ _ Q => ?_⟩
  · constructor
    · rintro ⟨hC, hc⟩ Q
      exact ⟨hc Q, (hC Q).1, (hC Q).2⟩
    · intro hF
      exact ⟨fun Q => ⟨(hF Q).2.1, (hF Q).2.2⟩, fun Q => (hF Q).1⟩
  · ext x
    constructor
    · rintro ⟨hn, Q, hQ, hd, hm⟩
      exact ⟨hn, fun j => ⟨Q j, hQ j⟩, hd, hm⟩
    · rintro ⟨hn, Q, hd, hm⟩
      exact ⟨hn, fun j => (Q j : Set (E.Pt D)), fun j => (Q j).2, hd, hm⟩
  · constructor
    · rintro ⟨hQ, hd, hm⟩
      exact ⟨hQ, hd, hm⟩
    · rintro ⟨hQ, hd, hm⟩
      exact ⟨hQ, hd, hm⟩
end YangMills.Construction.PeriodicSpace.Kind.CountableDenseFamilies
