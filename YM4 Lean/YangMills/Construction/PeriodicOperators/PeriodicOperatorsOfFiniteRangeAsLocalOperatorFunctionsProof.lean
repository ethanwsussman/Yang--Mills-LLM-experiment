import YangMills.Construction.PeriodicOperators.CalculusOfJets
import YangMills.Construction.PeriodicOperators.CalculusOfSymbols
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.NumbersOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.PeriodicOperatorsOfFiniteRangeAsLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.SymbolsOnStrips
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.ConstantOpFun
open JetDomains
open JetQuad (EqAsJet)
open YangMills.Construction.Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
open YangMills.Construction.TorusMetric (euclidNormVec)
theorem euclidNormVec_sub_comm (x y : Fin 4 → ℝ) : euclidNormVec (x - y) = euclidNormVec (y - x) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
theorem isHolomorphicIn_const (l : ℕ) (ρ : ℝ) (w : ℂ) :
    YangMills.Construction.Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1)
      (YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk
        (0 : YangMills.Construction.Coordinates.ComplexCoordinates l) ρ)
      (fun z _ => (fun _ : YangMills.Construction.Coordinates.ComplexCoordinates l => w) z) := by
  refine ⟨?_, continuousOn_const, fun a _ j => Filter.Eventually.of_forall fun ζ => ?_⟩
  · simp only [YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk,
      ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
  · exact differentiableAt_const _
section Assignment
variable {F I I' : PeriodicData}
theorem isLocalWith_constAssign (hFin : ∀ y ς, (nearIndices F y ς).Finite)
    {T : I'.Carrier → I.Carrier → ℂ} (hcov : IsShiftInvariant I I' T) {ϱ : ℝ}
    (hϱ : ∀ ι' ι, ¬ euclidNormVec (I'.pos ι' - I.pos ι) ≤ ϱ → T ι' ι = 0) {ρ : ℝ}
    (hρ : 0 < ρ) : IsLocalWith F I I' (constAssign F T) ρ ϱ where
  radius_pos := hρ
  vanish_far := fun _ _ ι' ι h => hϱ ι' ι (by rwa [euclidNormVec_sub_comm])
  holo_entry := fun ι' ι => by
    have := (hFin (I'.pos ι') ϱ).to_subtype
    exact ⟨_, (Finite.equivFin (nearIndices F (I'.pos ι') ϱ)).symm,
      fun _ => T ι' ι, isHolomorphicIn_const _ ρ _, fun _ _ => rfl⟩
  shift_covariant := fun _ _ n ι' ι => hcov n ι' ι
theorem isSecondOrderExpansion_entryFun_constAssign (T : I'.Carrier → I.Carrier → ℂ)
    (ι' : I'.Carrier) (ι : I.Carrier) {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S) :
    IsSecondOrderExpansion (entryFun (constAssign F T) ι' ι e) 0 0 := by
  refine ⟨fun _ _ => rfl, (Asymptotics.isBigO_zero _ _).congr_left fun z => ?_⟩
  simp [entryFun, constAssign]
theorem coeffOne_coeffTwo_constAssign (hN : ParameterIndependence.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ} {ρ R : ℝ}
    (hm : IsLocalWith F I I' (constAssign F T) ρ R) :
    (∀ ζ, coeffOne F I I' (constAssign F T) ζ = 0) ∧
      ∀ ζ ζ', coeffTwo F I I' (constAssign F T) ζ ζ' = 0 := by
  have key := (hN F I I' hF hI hI' _ ρ R ρ R hm hm).2.1.1
  constructor
  · intro ζ
    funext ι' ι
    obtain ⟨l, e, -, -, -⟩ := hm.holo_entry ι' ι
    exact (((key ζ ζ ι' ι).1.1 0).1
      ⟨hm, l, e, 0, 0, isSecondOrderExpansion_entryFun_constAssign T ι' ι e, rfl⟩).symm
  · intro ζ ζ'
    funext ι' ι
    obtain ⟨l, e, -, -, -⟩ := hm.holo_entry ι' ι
    exact (((key ζ ζ' ι' ι).2.1 0).1
      ⟨hm, l, e, 0, 0, isSecondOrderExpansion_entryFun_constAssign T ι' ι e, rfl⟩).symm
theorem jetAlong_constAssign (hJ : JetDomains.OpFunJetTheory)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : I'.Carrier → I.Carrier → ℂ}
    (hloc : IsLocalOpFun F I I' (constAssign F T))
    (h₁ : ∀ ζ, coeffOne F I I' (constAssign F T) ζ = 0)
    (h₂ : ∀ ζ ζ', coeffTwo F I I' (constAssign F T) ζ ζ' = 0)
    (p : Fin 4 → ℂ) (εPlus εMinus : F.UnitQuot → ℂ) :
    jetAlong F I I' (constAssign F T) p εPlus εMinus = JetQuad.ofKernel I I' T := by
  obtain ⟨A, hA, huniq⟩ := (hJ.2.1 F I I' hF hI hI' _ hloc).triple_unique p εPlus εMinus
  have hzero : IsActionTriple F I I' (constAssign F T) p εPlus εMinus (0, 0, 0) := by
    intro κ φ ι'
    simp [h₁, h₂, applyKernel, blochWave]
  have hε := huniq _ (Classical.epsilon_spec (⟨A, hA⟩ :
    ∃ B, IsActionTriple F I I' (constAssign F T) p εPlus εMinus B))
  have hε₀ : Classical.epsilon (IsActionTriple F I I' (constAssign F T) p εPlus εMinus) =
      (0, 0, 0) := hε.trans (huniq _ hzero).symm
  simp only [jetAlong, JetQuad.ofKernel, hε₀]
  rfl
end Assignment
section Symbols
variable {I I' : PeriodicData}
theorem symbolHom_entries_entire (hQ : StripSymbols.Claim) (hC : SymbolCalculus.Claim)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ}
    (hp : IsPeriodicKernel I I' T) (hr : IsFiniteRange I I' T) :
    StripSymbols.SymbolSummability I I' ∧ EntriesHolomorphicOn univ (symbolHom I I' T) := by
  have hs := (hQ.2.1 I I' hI hI').1
  refine ⟨hs, fun c' c => ?_⟩
  obtain ⟨ι', rfl⟩ : ∃ ι', I'.mkQuot 1 ι' = c' := Quot.exists_rep c'
  obtain ⟨ι, rfl⟩ : ∃ ι, I.mkQuot 1 ι = c := Quot.exists_rep c
  have hE := (hC I I' hI hI').1 T hp hr
  have e : (fun (κ : Fin 4 → ℂ) (_ : Fin 1) =>
        linearMapEntry (symbolHom I I' T κ) (I'.mkQuot 1 ι') (I.mkQuot 1 ι)) =
      fun κ _ => fourierSymbol I I' T κ ι' ι := by
    funext κ _
    exact ((hQ.2.1 I I' hI hI').2.1 T κ hp (hE.1 κ (mem_univ κ))).carrierEntry_symbolHom ι' ι
  rw [e]
  exact (hE.2 ι' ι).2
theorem linCombKernel_zero_right (c : ℂ) (T : I'.Carrier → I.Carrier → ℂ) :
    StripSymbols.linCombKernel c 0 T T = c • T := by
  funext ι' ι
  simp [StripSymbols.linCombKernel]
end Symbols
theorem constAssign_isLocalOpFun_and_jet (hD : CovariantFiniteRange.Claim)
    (hN : ParameterIndependence.Claim)
    (hJ : JetDomains.OpFunJetTheory)
    {F I I' : PeriodicData} (hF : IsPeriodic F) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ}
    (hp : IsPeriodicKernel I I' T) (hr : IsFiniteRange I I' T) :
    IsLocalOpFun F I I' (constAssign F T) ∧
      (∀ ζ, coeffOne F I I' (constAssign F T) ζ = 0) ∧
      (∀ ζ ζ', coeffTwo F I I' (constAssign F T) ζ ζ' = 0) ∧
      ∀ (q : Fin 4 → ℂ) (εPlus εMinus : F.UnitQuot → ℂ),
        jetAlong F I I' (constAssign F T) q εPlus εMinus = JetQuad.ofKernel I I' T := by
  obtain ⟨ϱ, hϱ⟩ := hr
  have hm : IsLocalWith F I I' (constAssign F T) 1 ϱ :=
    isLocalWith_constAssign ((hD.1 F hF).1) hp.1 hϱ one_pos
  have hloc : IsLocalOpFun F I I' (constAssign F T) := ⟨1, ϱ, hm⟩
  obtain ⟨h₁, h₂⟩ := coeffOne_coeffTwo_constAssign hN hF hI hI' hm
  exact ⟨hloc, h₁, h₂, jetAlong_constAssign hJ hF hI hI' hloc h₁ h₂⟩
theorem claim_holds (hD : CovariantFiniteRange.Claim)
    (hN : ParameterIndependence.Claim)
    (hJ : JetDomains.OpFunJetTheory)
    (hQ : StripSymbols.Claim) (hC : SymbolCalculus.Claim)
    (hK : JetCalculus.Claim) : Claim := by
  intro F I I' hF hI hI' T hp hr δ q hδ hq εPlus εMinus
  obtain ⟨hloc, h₁, h₂, hjet⟩ := constAssign_isLocalOpFun_and_jet hD hN hJ hF hI hI' hp hr
  obtain ⟨hs, hent⟩ := symbolHom_entries_entire hQ hC hI hI' hp hr
  have hform : SymbolSummableOn I I' T univ := hs.finiteRange T hp hr
  refine ⟨⟨hloc, rfl, h₁, h₂, ⟨univ, isOpen_univ, subset_univ _, hform, hent⟩, ?_⟩, ?_⟩
  · rw [hjet]
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  intro S c hS
  have hfacts := fun κ : Fin 4 → ℂ =>
    ((hQ.2.1 I I' hI hI').2.1 T κ hp (hform κ (mem_univ κ))).linComb T hp
      (hform κ (mem_univ κ)) c 0
  have hpc : IsPeriodicKernel I I' (c • T) :=
    linCombKernel_zero_right c T ▸ (hfacts 0).1
  have hrc : IsFiniteRange I I' (c • T) := by
    obtain ⟨ϱ, hϱ⟩ := hr
    exact ⟨ϱ, fun ι' ι h => by simp [hϱ ι' ι h]⟩
  obtain ⟨hlocc, -, -, hjetc⟩ := constAssign_isLocalOpFun_and_jet (F := F) hD hN hJ hF hI hI' hpc hrc
  have hsum : IsLocalOpFun F I I' (opFunAdd S (constAssign F (c • T))) :=
    (hJ.1 F I I' I hF hI hI' hI).1 S _ hS hlocc
  have hadd : EqAsJet δ q (jetAlong F I I' (opFunAdd S (constAssign F (c • T))) q εPlus εMinus)
      (JetQuad.add (jetAlong F I I' S q εPlus εMinus)
        (jetAlong F I I' (constAssign F (c • T)) q εPlus εMinus)) :=
    ((hK δ q hδ hq).2.2.1 F I' I I hF hI' hI hI εPlus εMinus).1 S _ hS hlocc
  rw [hjetc] at hadd
  refine ⟨hsum, ?_, ?_, ?_, ?_⟩
  · intro κ hκ
    refine (hadd.1 hκ).trans ?_
    have h := (hfacts κ).2.2
    rw [linCombKernel_zero_right c T, zero_smul, add_zero] at h
    simp only [JetQuad.add, JetQuad.ofKernel, JetQuad.smul, Pi.add_apply, Pi.smul_apply, h]
  · intro κ hκ
    refine (hadd.2.1 hκ).trans ?_
    simp [JetQuad.add, JetQuad.ofKernel, JetQuad.smul]
  · intro κ hκ
    refine (hadd.2.2.1 hκ).trans ?_
    simp [JetQuad.add, JetQuad.ofKernel, JetQuad.smul]
  · intro κ hκ
    refine (hadd.2.2.2 hκ).trans ?_
    simp [JetQuad.add, JetQuad.ofKernel, JetQuad.smul]
end YangMills.Construction.PeriodicOperators.ConstantOpFun
end
