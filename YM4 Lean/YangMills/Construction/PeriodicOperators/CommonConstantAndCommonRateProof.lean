import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.PeriodicOperators.CommonConstantAndCommonRate
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.UniformDecay
open TorusMetric (euclidNormVec)
theorem normVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_nonneg <;> assumption
theorem expDecay_mono {I I' : PeriodicData} {T : I'.Carrier → I.Carrier → ℂ} {C δ C' δ' : ℝ}
    (hC : 0 < C) (h : ExpDecay I I' T C δ) (hCC : C ≤ C') (hδ : δ' ≤ δ) :
    ExpDecay I I' T C' δ' := by
  intro j' j
  have hd := normVec_nonneg (I'.pos j' - I.pos j)
  have hexp : Real.exp (-δ * euclidNormVec (I'.pos j' - I.pos j)) ≤
      Real.exp (-δ' * euclidNormVec (I'.pos j' - I.pos j)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc ‖T j' j‖ ≤ C * Real.exp (-δ * euclidNormVec (I'.pos j' - I.pos j)) := h j' j
    _ ≤ C * Real.exp (-δ' * euclidNormVec (I'.pos j' - I.pos j)) :=
        mul_le_mul_of_nonneg_left hexp hC.le
    _ ≤ C' * Real.exp (-δ' * euclidNormVec (I'.pos j' - I.pos j)) :=
        mul_le_mul_of_nonneg_right hCC (Real.exp_pos _).le
theorem claim_holds : Claim := by
  refine ⟨?_, ?_⟩
  · intro I I' _ _ T C δ C' δ' _ hC _ h hCC _ hδ
    exact expDecay_mono hC h hCC hδ
  · intro A _ _ I I' _ _ T C δ _ hC hδ h
    obtain ⟨a, ha⟩ := Finite.exists_max C
    obtain ⟨b, hb⟩ := Finite.exists_min δ
    have hall : ∀ c, ExpDecay (I c) (I' c) (T c) (C a) (δ b) := fun c =>
      expDecay_mono (hC c) (h c) (ha c) (hb c)
    refine ⟨C a, δ b, ⟨⟨a, rfl⟩, ?_⟩, ⟨⟨b, rfl⟩, ?_⟩, hall, fun c => ⟨hδ b, C a, hC a, hall c⟩⟩
    · rintro _ ⟨c, rfl⟩
      exact ha c
    · rintro _ ⟨c, rfl⟩
      exact hb c
end YangMills.Construction.PeriodicOperators.UniformDecay
end
