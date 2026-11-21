import YangMills.Construction.PeriodicOperators.JetOfALocalOperatorFunctionIsEntire
import YangMills.Construction.PeriodicOperators.JetRelationsOnATorus
import YangMills.Construction.PeriodicOperators.JetTripleOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.JetsOfPeriodicOperatorsAndConstantParts
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.ProductOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.ProductsOfJets
import YangMills.Construction.PeriodicOperators.QuasiPeriodicityOfTheJetOfAFunction
import YangMills.Construction.PeriodicOperators.StripsAndFiniteNormsOfJets
import YangMills.Construction.PeriodicOperators.SumOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.SumsAndMultiplesOfJets
import YangMills.Construction.PeriodicOperators.TransposeOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.TransposesOfJets
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetDomains
open JetQuad (IsJet EqAsJet)
theorem opFunJetTheory_holds
    (hAdd : OpFunAdd.LocalClosed)
    (hComp : OpFunComp.LocalClosed)
    (hTransp : OpFunTransposeLocal.Claim)
    (hTriple : LocalOpFunTriple.Claim)
    (hQuasi : JetQuasiPeriodic.Claim)
    (hEntire : LocalJetEntire.Claim)
    (hTorus : TorusJetRelations.Claim)
    (hStrip : StripJetNorms.Claim)
    (hAddSMul : JetAddSMul.Claim)
    (hMul : JetProducts.Claim)
    (hTr : JetTransposition.Holds)
    (hZero : ZeroPartJets.Claim) :
    OpFunJetTheory := by
  refine ⟨?_, ?_, ?_⟩
  · intro F P Q R hF hP hQ hR
    exact ⟨hAdd F P Q hF hP hQ, hComp F P Q R hF hP hQ hR, hTransp F P Q hF hP hQ⟩
  · intro F P Q hF hP hQ T hT
    obtain ⟨triple, e10, e01, e11⟩ := hTriple F P Q hF hP hQ T hT
    obtain ⟨n10, n01, n11, jet⟩ := hEntire F P Q hF hP hQ T hT
    exact
      { triple_unique := triple
        entries_f10 := e10
        entries_f01 := e01
        entries_f11 := e11
        entire_f10 := n10
        entire_f01 := n01
        entire_f11 := n11
        quasiPeriodic := hQuasi F P Q hF hP hQ T hT
        isJet := jet
        descends := hTorus F P Q hF hP hQ T hT }
  · intro P Q R hP hQ hR δ p hδ hp
    obtain ⟨strips, sups⟩ := hStrip P Q hP hQ δ p hδ hp
    obtain ⟨addDef, addJet, smulDef, smulJet⟩ := hAddSMul P Q hP hQ δ p hδ hp
    obtain ⟨mulDef, mulJet⟩ := hMul P Q R hP hQ hR δ p hδ hp
    obtain ⟨trDef, trJet⟩ := hTr P Q hP hQ δ p hδ hp
    obtain ⟨kernelJet, oneJet, zeroParts⟩ := hZero P Q hP hQ δ p hδ hp
    obtain ⟨-, addJet', -, smulJet'⟩ := hAddSMul P P hP hP δ p hδ hp
    obtain ⟨-, mulJet'⟩ := hMul P P P hP hP hP δ p hδ hp
    have derived : ∀ T : JetQuad P P, JetQuad.IsInvertibleJet δ p T →
        IsJet δ p (JetQuad.mul p (JetQuad.zeroPartInv T) T) ∧
          IsJet δ p (JetQuad.normalize p T) ∧
          IsJet δ p (JetQuad.mul p (JetQuad.normalize p T) (JetQuad.normalize p T)) ∧
          IsJet δ p (JetQuad.logSeries p T) := by
      intro T hT
      have lead : IsJet δ p (JetQuad.mul p (JetQuad.zeroPartInv T) T) :=
        mulJet' _ _ (zeroParts T hT).2.1 hT.isJet
      have norm : IsJet δ p (JetQuad.normalize p T) :=
        addJet' _ _ lead (smulJet' (-1) _ oneJet)
      have sq : IsJet δ p (JetQuad.mul p (JetQuad.normalize p T) (JetQuad.normalize p T)) :=
        mulJet' _ _ norm norm
      exact ⟨lead, norm, sq, addJet' _ _ norm (smulJet' (-(1 / 2)) _ sq)⟩
    exact
      { imStrip_subset := strips
        sups_finite := sups
        add_defined := addDef
        add_isJet := addJet
        smul_defined := smulDef
        smul_isJet := smulJet
        mul_defined := mulDef
        mul_isJet := mulJet
        transpose_defined := trDef
        transpose_isJet := trJet
        ofKernel_isJet := kernelJet
        one_isJet := oneJet
        zeroPart_isJet := fun T hT => ⟨(zeroParts T hT).1, (zeroParts T hT).2.1⟩
        zeroPart_inv := fun T hT => (zeroParts T hT).2.2
        invertible_derived_isJet := derived
        normalize_logNumber_wellFormed := fun T hT =>
          have q := derived T hT
          have wf : JetQuad.NormalizeWellFormed δ p T :=
            ⟨(zeroParts T hT).2.1, q.1, oneJet⟩
          ⟨wf, ⟨wf, q.2.1, q.2.2.1, q.2.2.2⟩⟩ }
end YangMills.Construction.PeriodicOperators.JetDomains
end
