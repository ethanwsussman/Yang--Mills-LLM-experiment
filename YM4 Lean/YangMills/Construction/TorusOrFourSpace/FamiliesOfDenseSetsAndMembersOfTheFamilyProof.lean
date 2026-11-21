import YangMills.Construction.TorusOrFourSpace.CountableFamilyOfACountableChoice
import YangMills.Construction.TorusOrFourSpace.FamiliesOfDenseSetsAndMembersOfTheFamily
import YangMills.Construction.TorusOrFourSpace.QuotientMapCompactSetsAndFunctionsOfClassC1
import YangMills.Construction.TorusOrFourSpace.TwoNormsOfClassC1
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.DenseFamilies
open Kind VectorClasses C1NormComparison
theorem claim_holds (hfam : CountableChoiceFamilyFacts)
    (hvec : VectorClasses.Claim)
    (hnorm : C1NormComparison.statement)
    (hquot : Kind.QuotientCompactC1.Claim) :
    DenseFamilies.Claim := by
  intro D E
  obtain ⟨-, hstock, -, -⟩ := hfam D E
  have hlin : ∀ Q : Set (E.Pt D), IsLinearSubspaceSet D E (c1SupportedIn D E Q) :=
    fun Q => ((hvec D E).1 Q).2.1
  obtain ⟨-, -, -, -, hcpt⟩ := hquot D E
  have heq : ∀ Q ∈ supportStock D E, c1VanishingOutside D E Q = c1SupportedIn D E Q :=
    fun Q hQ => (hstock Q hQ).1
  refine ⟨⟨fun Q hQ => ?_, ?_⟩, fun F n _ => ⟨?_, ?_⟩⟩
  · refine ⟨heq Q hQ, ?_, ?_⟩
    · rw [heq Q hQ]
      exact hlin Q
    · obtain ⟨W, hW⟩ := hlin Q
      have hfin : ∀ u ∈ W, u ∈ c1Set D E ∧ euclidC1Norm D E u < ⊤ := by
        intro u hu
        have hu' : u ∈ c1SupportedIn D E Q := hW ▸ hu
        exact ⟨hu'.1, (hcpt u hu'.1 hu'.2.1).2.2.1⟩
      obtain ⟨-, -, -, hdense⟩ := (hnorm D E).2 W hfin
      intro A hA
      rw [heq Q hQ, ← hW]
      exact hdense A (by rw [hW, ← heq Q hQ]; exact hA)
  · have hpick : ∀ Q : supportStock D E, ∃ A : Set (E.Pt D → ℝ),
        A.Countable ∧ A ⊆ c1VanishingOutside D E Q ∧
          IsDenseWrt D E (euclidC1Norm D E) (c1VanishingOutside D E Q) A := by
      intro Q
      obtain ⟨A, hAV, hAc, hAd⟩ := (hstock Q Q.2).2.2.1.2.2
      exact ⟨A, hAc, hAV, hAd⟩
    choose A hA using hpick
    exact ⟨⟨A, hA⟩⟩
  · intro φ hφ
    exact hφ.2
  · intro φ Q _ hform
    have hmem : ∀ i, φ i ∈ c1SupportedIn D E (Q i : Set (E.Pt D)) := by
      intro i
      rw [← heq _ (Q i).2]
      exact (F.isDense (Q i)).2.1 (hform.2 i)
    have hsupp : ∀ i, supportQ D E (φ i) ⊆ (Q i : Set (E.Pt D)) := fun i => (hmem i).2.2
    refine ⟨hmem, hsupp, fun i => (hmem i).1, fun i => (hmem i).2.1, fun i k hik => ?_⟩
    exact (hform.1 hik).mono (hsupp i) (hsupp k)
end YangMills.Construction.PeriodicSpace.DenseFamilies
