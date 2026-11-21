import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import YangMills.Construction.PeriodicOperators.IdentityOfAPeriodicIndexSet
import YangMills.Construction.PeriodicOperators.JetOfAProductOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.MultiplesOfLocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHom
import YangMills.Construction.PeriodicOperators.PeriodicOperatorsOfFiniteRangeAsLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.ProductOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.SymbolsOfCombinationsAndProductsAtAPoint
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.OpFunMultiples
open ConstantOpFun (constAssign)
open JetQuad (EqAsJet)
def smulIdKernel (I : PeriodicData) (c : ℂ) : I.Carrier → I.Carrier → ℂ :=
  fun i' i => c * idKernel I i' i + 0 * idKernel I i' i
theorem opFunComp_constAssign_smulIdKernel {F I I' : PeriodicData} (c : ℂ)
    (S : (F.Carrier → ℂ) → I.Carrier → I'.Carrier → ℂ) :
    opFunComp (constAssign F (smulIdKernel I c)) S = fun ζ => c • S ζ := by
  classical
  funext ζ i' i
  simp only [opFunComp, compKernel, constAssign, smulIdKernel, idKernel]
  rw [tsum_eq_single i']
  · simp
  · intro b hb
    simp [Ne.symm hb]
theorem mul_eqAsJet_smul {I I' : PeriodicData} {δ : ℝ} {p : Fin 4 → ℂ} (c : ℂ) (A : JetQuad I I)
    (J : JetQuad I' I) (hArg : ProductJetArguments δ p)
    (h00 : ∀ κ ∈ imStrip (2 * δ), A.f00 κ = c • (LinearMap.id : QuotHom I I))
    (h10 : ∀ κ ∈ stripAddShift δ p, A.f10 κ = 0) (h01 : ∀ κ ∈ stripSubShift δ p, A.f01 κ = 0)
    (h11 : ∀ κ ∈ realDualPoints, A.f11 κ = 0) :
    EqAsJet δ p (JetQuad.mul p A J) (JetQuad.smul c J) := by
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_, fun κ hκ => ?_, fun κ hκ => ?_⟩
  · show (A.f00 κ).comp (J.f00 κ) = c • J.f00 κ
    rw [h00 κ hκ, LinearMap.smul_comp, LinearMap.id_comp]
  · obtain ⟨-, -, hp, -⟩ := hArg.comp10 κ hκ
    show (A.f10 κ).comp (J.f00 κ) + (A.f00 (κ + p)).comp (J.f10 κ) = c • J.f10 κ
    rw [h10 κ hκ, h00 _ hp, LinearMap.zero_comp, zero_add, LinearMap.smul_comp, LinearMap.id_comp]
  · obtain ⟨-, -, hp, -⟩ := hArg.comp01 κ hκ
    show (A.f01 κ).comp (J.f00 κ) + (A.f00 (κ - p)).comp (J.f01 κ) = c • J.f01 κ
    rw [h01 κ hκ, h00 _ hp, LinearMap.zero_comp, zero_add, LinearMap.smul_comp, LinearMap.id_comp]
  · obtain ⟨-, -, hs, -, hm, -, hq, -⟩ := hArg.comp11 κ hκ
    show (A.f11 κ).comp (J.f00 κ) + (A.f00 κ).comp (J.f11 κ) + (A.f10 (κ - p)).comp (J.f01 κ) +
      (A.f01 (κ + p)).comp (J.f10 κ) = c • J.f11 κ
    rw [h11 κ hκ, h00 κ hs, h10 _ hm, h01 _ hq, LinearMap.zero_comp, LinearMap.zero_comp,
      LinearMap.zero_comp, zero_add, add_zero, add_zero, LinearMap.smul_comp, LinearMap.id_comp]
theorem claim_holds (hW : ConstantOpFun.Claim)
    (hP : OpFunComp.LocalClosed)
    (hJ : JetComp.Claim)
    (hA : JetArgumentsAndEqualJets)
    (hI : IdKernelFacts.Claim)
    (hD : CovariantFiniteRange.Claim)
    (hC : SymbolAtPoint.Claim)
    (hN : HomNorm.Claim) : Claim := by
  intro F hF δ p hδ hp εPlus εMinus I' I'' hI' hI'' S hS c
  obtain ⟨hper, -, hformed, -, hmat, -⟩ := hI I'' hI''
  obtain ⟨-, -, ⟨ϱ, hϱ⟩, -⟩ := hD.1 I'' hI''
  obtain ⟨-, -, -, -, -, -, -, ⟨hunit, -⟩, -⟩ := hN I'' I'' hI'' hI''
  have hcomb : ∀ κ, IsPeriodicKernel I'' I'' (smulIdKernel I'' c) ∧
      symbolHom I'' I'' (smulIdKernel I'' c) κ = c • (LinearMap.id : QuotHom I'' I'') := by
    intro κ
    obtain ⟨h1, -, h3⟩ := hC.1 I'' I'' hI'' hI'' (idKernel I'') (idKernel I'') κ c 0
      hper (hformed κ (mem_univ κ)) hper (hformed κ (mem_univ κ))
    have hid : symbolHom I'' I'' (idKernel I'') κ = LinearMap.id := by
      show linearMapOfEntries (quotSymbol I'' I'' (idKernel I'') κ) = LinearMap.id
      rw [hmat κ]
      exact hunit
    refine ⟨h1, ?_⟩
    have h3' : symbolHom I'' I'' (smulIdKernel I'' c) κ = _ := h3
    rw [h3', hid, zero_smul, add_zero]
  have hfin : IsFiniteRange I'' I'' (smulIdKernel I'' c) :=
    ⟨ϱ, fun i' i h => by simp [smulIdKernel, hϱ i' i h]⟩
  obtain ⟨⟨hloc, -, -, -, -, j00, j10, j01, j11⟩, -⟩ := hW F I'' I'' hF hI'' hI''
    (smulIdKernel I'' c) (hcomb 0).1 hfin δ p hδ hp εPlus εMinus
  have hl := hP F I'' I'' I' hF hI'' hI'' hI' (constAssign F (smulIdKernel I'' c)) S hloc hS
  have hj := hJ δ p hδ hp F I'' I'' I' hF hI'' hI'' hI' εPlus εMinus
    (constAssign F (smulIdKernel I'' c)) S hloc hS
  rw [opFunComp_constAssign_smulIdKernel] at hl hj
  refine ⟨hl, ?_⟩
  have hm := mul_eqAsJet_smul c (jetAlong F I'' I'' (constAssign F (smulIdKernel I'' c)) p εPlus εMinus)
    (jetAlong F I' I'' S p εPlus εMinus) (hA.1 δ p hδ hp).2.1
    (fun κ h => (j00 h).trans (hcomb κ).2) (fun κ h => j10 h) (fun κ h => j01 h)
    (fun κ h => j11 h)
  exact ⟨hj.1.trans hm.1, hj.2.1.trans hm.2.1, hj.2.2.1.trans hm.2.2.1, hj.2.2.2.trans hm.2.2.2⟩
end YangMills.Construction.PeriodicOperators.OpFunMultiples
end
