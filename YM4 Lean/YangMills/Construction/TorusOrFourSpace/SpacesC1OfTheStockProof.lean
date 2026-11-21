import YangMills.Construction.TorusOrFourSpace.CountableFamilyOfACountableChoice
import YangMills.Construction.TorusOrFourSpace.QuotientMapCompactSetsAndFunctionsOfClassC1
import YangMills.Construction.TorusOrFourSpace.SpacesC1OfTheStock
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.StockC1
open Kind VectorClasses
theorem c1OfStock_holds (hFamily : CountableChoiceFamilyFacts)
    (hSpace : Kind.QuotientCompactC1.Claim)
    (hClasses : VectorClasses.Claim) : C1OfStock.Holds := by
  intro D E Q hQ
  obtain ⟨hMetric, -, -, -, hC1⟩ := hSpace D E
  obtain ⟨-, hStock, -, -⟩ := hFamily D E
  obtain ⟨hEq, hGrad, -, -⟩ := hStock Q hQ
  obtain ⟨-, ⟨-, hNorm⟩, -⟩ := hClasses D E
  have hClass : ∀ f ∈ c1VanishingOutside D E Q, f ∈ c1SupportedIn D E Q := fun f hf => hEq ▸ hf
  have hLip : c1VanishingOutside D E Q ⊆ lipschitzSupportedIn D E Set.univ := by
    intro f hf
    obtain ⟨hfC, hfK, -⟩ := hClass f hf
    exact ⟨(hC1 f hfC hfK).2.2.2.2.1, hfK, Set.subset_univ _⟩
  refine ⟨⟨fun f hfC => ⟨fun hf => (hClass f hf).2.2, fun hs => ⟨hfC, fun y hy => ?_⟩⟩,
    fun f hf => ?_⟩, ⟨fun h hh => hNorm.lt_top h (hLip hh),
      fun h hh => hNorm.eq_zero_iff h (hLip hh), fun h hh α => hNorm.smul h (hLip hh) α,
      fun h hh h' hh' => hNorm.add_le h (hLip hh) h' (hLip hh')⟩, fun f hf => ?_⟩
  · by_contra hne
    refine hy (hs ?_)
    intro r hr
    refine ⟨y, hne, ?_⟩
    rw [(hMetric.2.1 y y).2 rfl]
    exact hr
  · obtain ⟨hfC, hfK, -⟩ := hClass f hf
    exact ⟨hfK, hf.2, hGrad f hf, (hC1 f hfC hfK).2.2.1⟩
  · obtain ⟨hfC, hfK, -⟩ := hClass f hf
    exact (hC1 f hfC hfK).2.2.2.2.2.2.2
end YangMills.Construction.PeriodicSpace.StockC1
