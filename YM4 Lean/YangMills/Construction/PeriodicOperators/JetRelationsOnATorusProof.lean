import YangMills.Construction.PeriodicOperators.JetRelationsOnATorus
import YangMills.Construction.PeriodicOperators.JetTripleOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.MatricesOfALocalOperatorFunctionOnATorus
import YangMills.Construction.PeriodicOperators.WaveSpacesOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TorusJetRelations
open JetDomains
theorem liftQuotField_eq_of_isLiftOf {D : PeriodicData} {k : ℕ} {u : D.QuotMod k → ℂ}
    {v : D.Carrier → ℂ} (hv : IsLiftOf D k u v) : liftQuotField D k u = v :=
  funext hv
theorem claim_holds (hTrip : LocalOpFunTriple.Claim)
    (hMat : LocalTorusMatrices.LocalTorusMatricesClaim)
    (hBloch : BlochDecomposition.Claim) : Claim := by
  intro F I I' hF hI hI' T hT ρ R hR s hs hsR κ hκ p hp wPlus wMinus φ
  refine ⟨?_, ?_⟩
  · have hNegVec : toComplexVec (-p) = -toComplexVec p := by
      funext μ
      simp [toComplexVec]
    obtain ⟨uPlus, hUPlus⟩ := (hBloch F hF).blochWave_descends s hs p hp wPlus
    obtain ⟨uMinus, hUMinus⟩ :=
      (hBloch F hF).blochWave_descends s hs (-p) (neg_mem hp) wMinus
    obtain ⟨v, hv⟩ := (hBloch I hI).blochWave_descends s hs κ hκ φ
    rw [hNegVec] at hUMinus
    exact ⟨⟨uPlus, hUPlus⟩, ⟨uMinus, hUMinus⟩, ⟨v, hv⟩⟩
  · intro uPlus uMinus v hUPlus hUMinus hv j
    have hChosen : IsActionTriple F I I' T (toComplexVec p) wPlus wMinus
        (Classical.epsilon (IsActionTriple F I I' T (toComplexVec p) wPlus wMinus)) :=
      Classical.epsilon_spec
        ((hTrip F I I' hF hI hI' T hT).1 (toComplexVec p) wPlus wMinus).exists
    obtain ⟨e10, e01, e11⟩ := hChosen (toComplexVec κ) φ j
    have hActs := (hMat F I I' hF hI hI' T ρ R hR s hs hsR).1
    have b10 := ((hActs uPlus uPlus _ (Or.inr (Or.inr (Or.inl rfl)))).2 v).2.2 j
    have b01 := ((hActs uMinus uMinus _ (Or.inr (Or.inr (Or.inl rfl)))).2 v).2.2 j
    have b11 := ((hActs uPlus uMinus _ (Or.inr (Or.inr (Or.inr rfl)))).2 v).2.2 j
    refine ⟨?_, ?_, ?_⟩
    · show applyKernel (descendMatrix I I' s (periodization I I'
          (coeffOne F I I' T (liftQuotField F s uPlus)) s)) v (I'.mkQuot s j) = _
      rw [← b10, liftQuotField_eq_of_isLiftOf hv, liftQuotField_eq_of_isLiftOf hUPlus]
      exact e10
    · show applyKernel (descendMatrix I I' s (periodization I I'
          (coeffOne F I I' T (liftQuotField F s uMinus)) s)) v (I'.mkQuot s j) = _
      rw [← b01, liftQuotField_eq_of_isLiftOf hv, liftQuotField_eq_of_isLiftOf hUMinus]
      exact e01
    · show applyKernel (descendMatrix I I' s (periodization I I'
          (coeffTwo F I I' T (liftQuotField F s uPlus) (liftQuotField F s uMinus)) s))
          v (I'.mkQuot s j) = _
      rw [← b11, liftQuotField_eq_of_isLiftOf hv, liftQuotField_eq_of_isLiftOf hUPlus,
        liftQuotField_eq_of_isLiftOf hUMinus]
      exact e11
end YangMills.Construction.PeriodicOperators.TorusJetRelations
end
