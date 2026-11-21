import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import YangMills.Construction.PeriodicOperators.CopiesAndUnionsOfPeriodicIndexSets
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.OperatorFunctionsThatAgreeOnSmallFields
import YangMills.Construction.PeriodicOperators.WidthsAtWhichJetsAreInvertible
import YangMills.Construction.Towers.IndexSetsArePeriodic
import YangMills.Construction.Towers.OuterFactorsKeepTheNumberOfAJet
import YangMills.Construction.Towers.TheJetOfTheScaledSaddleOfTheBonds
import YangMills.Construction.Towers.TheJetOfTheScaledSaddleOfTheSites
import YangMills.Construction.Towers.TheOperatorFunctionsAtTheBackgroundFields
import YangMills.Construction.Towers.TheOperatorJetsAreSaddleJets
import YangMills.Construction.Towers.TheTwoOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.OperatorJetsSaddle
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad
open YangMills.Construction.Tower.RescaledConditions (sumDiagScale)
theorem invertible_and_logNumber_of_saddleRelation
    (hDis : YangMills.Construction.PeriodicOperators.DisjSumJets.Claim)
    (hExt : YangMills.Construction.PeriodicOperators.ExtendByZeroJets.Claim)
    (hAgr : YangMills.Construction.PeriodicOperators.LocalAgreement.Claim)
    (hOut : YangMills.Construction.PeriodicOperators.DiagonalScaling.PreservesJetIndex)
    (hEq : YangMills.Construction.PeriodicOperators.JetArgumentsAndEqualJets)
    (hJet : YangMills.Construction.PeriodicOperators.JetDomains.OpFunJetTheory)
    (hUn : YangMills.Construction.PeriodicOperators.CopiesUnions.Claim)
    {G F I₁ I₂ : PeriodicData} (hG : IsPeriodic G) (hF : IsPeriodic F)
    (h₁ : IsPeriodic I₁) (h₂ : IsPeriodic I₂)
    {e : G.Carrier → F.Carrier} (he : IsIndexEmbedding e)
    {T : (F.Carrier → ℂ) → (I₁.disjSum I₂).Carrier → (I₁.disjSum I₂).Carrier → ℂ}
    {S : (G.Carrier → ℂ) → (I₁.disjSum I₂).Carrier → (I₁.disjSum I₂).Carrier → ℂ}
    (hT : IsLocalOpFun F (I₁.disjSum I₂) (I₁.disjSum I₂) T)
    (hS : IsLocalOpFun G (PeriodicData.sigma (pairData I₁ I₂))
      (PeriodicData.sigma (pairData I₁ I₂)) (readOnSigma S))
    {x y x' y' : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (hx' : x' ≠ 0) (hy' : y' ≠ 0)
    (hrel : ∃ ρ : ℝ, 0 < ρ ∧ ∀ f, IsSupBelow G f ρ → T (PeriodicOperators.extendByZero e f) =
      sumDiagScale (S := I₁.Carrier) (B := I₂.Carrier) x y x' y' (S f))
    {δ : ℝ} {p : Fin 4 → ℂ} (hδ : 0 < δ) (hp : p ∈ imStrip δ) (εPlus εMinus : G.UnitQuot → ℂ)
    {B : JetQuad (PeriodicData.sigma (pairData I₁ I₂)) (PeriodicData.sigma (pairData I₁ I₂))}
    (hB : IsInvertibleJet δ p B)
    (hBeq : EqAsJet δ p (jetAlong G _ _ (readOnSigma S) p εPlus εMinus) B) :
    IsInvertibleJet δ p (jetAlong F (I₁.disjSum I₂) (I₁.disjSum I₂) T p
        (extendQuotByZero e εPlus) (extendQuotByZero e εMinus)) ∧
      logNumber p (jetAlong F (I₁.disjSum I₂) (I₁.disjSum I₂) T p
        (extendQuotByZero e εPlus) (extendQuotByZero e εMinus)) =
        logNumber p B := by
  have hU : IsPeriodic (PeriodicData.sigma (pairData I₁ I₂)) :=
    hUn.2.2 _ (fun b => by fin_cases b <;> assumption)
  obtain ⟨hSum, hDisT⟩ := hDis G I₁ I₂ hG h₁ h₂
  obtain ⟨hSloc, hSjet⟩ := hDisT S hS
  obtain ⟨-, hTjet⟩ := hExt G F _ _ hG hF hSum hSum e he T hT
  obtain ⟨hScaled, hOutJ⟩ := hOut G I₁ I₂ hG h₁ h₂ x y x' y' hx hy hx' hy' S hSloc
  obtain ⟨ρ, hρ, hrel'⟩ := hrel
  obtain ⟨-, hAgrJ⟩ := hAgr G _ _ hG hSum hSum
    (fun ζ => sumDiagScale (S := I₁.Carrier) (B := I₂.Carrier) x y x' y' (S ζ))
    (fun f => T (PeriodicOperators.extendByZero e f)) hScaled ⟨ρ, hρ, hrel'⟩
  have hjS : JetQuad.IsJet δ p (jetAlong G _ _ (readOnSigma S) p εPlus εMinus) :=
    (hJet.2.1 G _ _ hG hU hU _ hS).isJet δ hδ p hp εPlus εMinus
  have hsym : EqAsJet δ p B (jetAlong G _ _ (readOnSigma S) p εPlus εMinus) :=
    ⟨hBeq.1.symm, hBeq.2.1.symm, hBeq.2.2.1.symm, hBeq.2.2.2.symm⟩
  obtain ⟨hinv, -, -, hℓ⟩ := (hEq.2.2 δ p _ hU B _ hB.isJet hjS hsym).2 hB
  obtain ⟨hinvS, hℓS⟩ := hSjet δ p εPlus εMinus hδ hp hinv
  obtain ⟨hinvO, hℓO⟩ := hOutJ δ p εPlus εMinus hδ hp hinvS
  rw [← hTjet p εPlus εMinus, hAgrJ p εPlus εMinus]
  exact ⟨hinvO, hℓO.trans (hℓS.trans hℓ.symm)⟩
theorem operatorJetsSaddle_holds
    (hDis : YangMills.Construction.PeriodicOperators.DisjSumJets.Claim)
    (hExt : YangMills.Construction.PeriodicOperators.ExtendByZeroJets.Claim)
    (hAgr : YangMills.Construction.PeriodicOperators.LocalAgreement.Claim)
    (hOut : YangMills.Construction.PeriodicOperators.DiagonalScaling.PreservesJetIndex)
    (hEq : YangMills.Construction.PeriodicOperators.JetArgumentsAndEqualJets)
    (hJet : YangMills.Construction.PeriodicOperators.JetDomains.OpFunJetTheory)
    (hUn : YangMills.Construction.PeriodicOperators.CopiesUnions.Claim)
    (hTrip : YangMills.Construction.Tower.FullSpace.BackgroundJets.BackgroundTriple.ExtendsByZero)
    (hRel : YangMills.Construction.Tower.FullSpace.BackgroundJets.OpFunsAtBackground.SaddleRelations)
    (hBond : YangMills.Construction.Tower.FullSpace.BackgroundJets.RescaledEdgeSaddleJet)
    (hSite : YangMills.Construction.Tower.FullSpace.BackgroundJets.VertexSaddleJet.LocalWithBlockJet)
    (hTwo : YangMills.Construction.Tower.FullSpace.OperatorFunctions.OperatorFunctionsTheorem)
    (hWid : YangMills.Construction.PeriodicOperators.InvertibleJetWidths.Claim)
    (hPer : YangMills.Construction.LocalKernels.IndexSetPeriodicity.Statement)
    (hIdx : YangMills.Construction.PeriodicOperators.TowerIndexSets.Claim) : Claim := by
  intro L hL hs k hk p hp μPlus μMinus hBinv hSinv
  obtain ⟨⟨_, _, _, hv, hg⟩, -⟩ := hTwo L hL hs k hk
  have hF : IsPeriodic (fieldPeriodicData L k hL) :=
    ((hPer L hs k).2 (YangMills.Construction.LocalKernels.fieldIndices L k hL)).1
  have hb₀ := (hIdx L hs k 0 (Nat.zero_le k)).2.1
  have hbk := (hIdx L hs k k le_rfl).2.1
  have hs₀ := (hIdx L hs k 0 (Nat.zero_le k)).1
  have hsk := (hIdx L hs k k le_rfl).1
  have hV : IsPeriodic (vectorIndices L k) := (hDis _ _ _ hb₀ hb₀ hbk).1
  have hG : IsPeriodic (ghostIndices L k) := (hDis _ _ _ hb₀ hs₀ hsk).1
  have hδ : 0 < stripHalfWidth := hBinv.isJet.pos_width
  have hpS : p ∈ imStrip stripHalfWidth := hBinv.isJet.mem_imStrip
  have hm : -p ∈ momentumPolydisc stripHalfWidth := fun μ => by simpa using hp μ
  obtain ⟨he, hamp⟩ := hTrip L hL hs k hk
  obtain ⟨ρ, hρ, hrel⟩ := hRel L hL hs k hk
  have hη : ((YangMills.Construction.Tower.finestMesh L k : ℝ) : ℂ) ≠ 0 := by
    have hL' : (0 : ℝ) < L := by exact_mod_cast hL
    exact Complex.ofReal_ne_zero.2 (zpow_pos hL' _).ne'
  obtain ⟨hSb, hJb⟩ := hBond L hs k hk
  obtain ⟨hSs, hJs⟩ := hSite L hs k hk
  have hv' := invertible_and_logNumber_of_saddleRelation hDis hExt hAgr hOut hEq hJet hUn
    hb₀ hF hb₀ hbk he hv hSb
    (pow_ne_zero 2 hη) (inv_ne_zero hη) one_ne_zero hη
    ⟨ρ, hρ, fun f hf => (hrel f hf).1⟩ hδ hpS (scaledResponseField L k p μPlus)
    (scaledResponseField L k (-p) μMinus) hBinv (hJb stripHalfWidth p μPlus μMinus hδ hpS)
  have hg' := invertible_and_logNumber_of_saddleRelation hDis hExt hAgr hOut hEq hJet hUn
    hb₀ hF hs₀ hsk he hg hSs
    (pow_ne_zero 2 hη) one_ne_zero one_ne_zero (pow_ne_zero 2 hη)
    ⟨ρ, hρ, fun f hf => (hrel f hf).2⟩ hδ hpS (scaledResponseField L k p μPlus)
    (scaledResponseField L k (-p) μMinus) hSinv (hJs stripHalfWidth p μPlus μMinus hδ hpS)
  rw [← hamp p hp μPlus, ← hamp (-p) hm μMinus] at hv' hg'
  have width : ∀ {I : PeriodicData} (hI : IsPeriodic I)
      (T : ((fieldPeriodicData L k hL).Carrier → ℂ) → I.Carrier → I.Carrier → ℂ),
      IsLocalOpFun (fieldPeriodicData L k hL) I I T →
      ∀ a b : (fieldPeriodicData L k hL).UnitQuot → ℂ,
      JetQuad.IsInvertibleJet stripHalfWidth p (jetAlong (fieldPeriodicData L k hL) I I T p a b) →
      HasInvertibleJetsAtWidth (fieldPeriodicData L k hL) I T stripHalfWidth := by
    intro I hI T hT a b hinv
    refine ⟨hδ, ?_⟩
    rcases ((hWid _ I hF hI T hT).1 stripHalfWidth hδ).1 with h | h
    · exact h
    · exact absurd hinv (h p hpS a b)
  exact ⟨⟨width hV _ hv _ _ hv'.1, width hG _ hg _ _ hg'.1⟩, hv'.2, hg'.2⟩
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.OperatorJetsSaddle
end
