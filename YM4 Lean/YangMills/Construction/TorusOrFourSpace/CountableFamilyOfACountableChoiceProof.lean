import YangMills.Construction.TorusOrFourSpace.CountableFamilyOfACountableChoice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
theorem countableChoiceFamilyFacts_holds (hstock : SupportStockAndCountableFamily) :
    CountableChoiceFamilyFacts := by
  intro D E
  obtain ⟨h1, h2, h3, h4⟩ := (hstock D).2 E
  exact ⟨h1, h2, h3, fun C hC => h4 C fun Q => ⟨hC.2 Q, (hC.1 Q).1, (hC.1 Q).2⟩⟩
end YangMills.Construction.PeriodicSpace
