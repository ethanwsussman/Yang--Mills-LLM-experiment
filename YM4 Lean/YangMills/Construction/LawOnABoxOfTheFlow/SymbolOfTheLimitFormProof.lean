import YangMills.Construction.FormsOnATorus.PropertiesOfTheSymbol
import YangMills.Construction.LawOnABoxOfTheFlow.SymbolOfTheLimitForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitForms
theorem limitFormSymbolStatement_of_symbolProperties
    (hsymb : symbolPropertiesStatement) : limitFormSymbolStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, h0, H⟩ := hsymb a ha
  refine ⟨L₀, rt₀, h0, fun L hL hL₀ T hTa hTL hT hr => ?_⟩
  obtain ⟨y₀, Hy⟩ := H L hL hL₀ T hTa hTL hT hr
  refine ⟨y₀, fun y h1 h2 h3 c₁ C₁ hc => ?_⟩
  obtain ⟨c, C, D, hc', K⟩ := Hy y h1 h2 h3 c₁ C₁ hc
  exact ⟨c, C, hc', fun k Q hQ => (K k Q hQ).1⟩
end YangMills.Construction.LimitForms
end
