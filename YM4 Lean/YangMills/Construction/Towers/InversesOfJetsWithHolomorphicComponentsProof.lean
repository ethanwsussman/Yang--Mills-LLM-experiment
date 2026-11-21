import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.JetsOfPeriodicOperatorsAndConstantParts
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.Towers.InversesOfJetsWithHolomorphicComponents
import YangMills.Construction.Towers.SumsProductsAndTransposesOfJetsWithHolomorphicComponents
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.InverseJetHolomorphy
open Coordinates
open PeriodicOperators
open ScaledOperatorFunctions
open StripSymbols (openStripInterior)
open EntriesDets
theorem appendSet_eq_preimage_splitCoords (S : Set (ComplexCoordinates 4 × ComplexCoordinates 4)) :
    appendSet (n := 4) (n' := 4) S = splitCoords ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : splitCoords (n := 4) (n' := 4) (appendCoords w.1 w.2) = w := by
      refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
      · exact Fin.append_left w.1 w.2 j
      · exact Fin.append_right w.1 w.2 j
    simpa [hw'] using hw
  · intro hx
    exact ⟨_, hx, Fin.append_castAdd_natAdd⟩
theorem continuous_splitCoords : Continuous (splitCoords (n := 4) (n' := 4)) :=
  Continuous.prodMk (continuous_pi fun _ => continuous_apply _)
    (continuous_pi fun _ => continuous_apply _)
theorem isOpen_appendSet {S : Set (ComplexCoordinates 4 × ComplexCoordinates 4)} (hS : IsOpen S) :
    IsOpen (appendSet (n := 4) (n' := 4) S) := by
  rw [appendSet_eq_preimage_splitCoords]
  exact hS.preimage continuous_splitCoords
section ComponentDomains
variable {I I' : PeriodicData}
theorem isHolomorphicInMomentumPair_iff {W : Set (ComplexCoordinates 4 × ComplexCoordinates 4)}
    {A : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I I'} :
    IsHolomorphicInMomentumPair W A ↔ IsOpen (appendSet (n := 4) (n' := 4) W) ∧
      ∀ e, ComplexCoordinates.IsHolomorphicIn (N' := 1) (appendSet (n := 4) (n' := 4) W) fun x _ =>
        quotHomEntries (A (splitCoords (n := 4) (n' := 4) x).2 (splitCoords (n := 4) (n' := 4) x).1) e := by
  constructor
  · intro h
    have h' : 1 ≤ 4 + 4 ∧ IsOpen (appendSet (n := 4) (n' := 4) W) ∧ ∀ e,
        ComplexCoordinates.IsHolomorphicIn (N' := 1) (appendSet (n := 4) (n' := 4) W) fun x _ =>
          quotHomEntries (A (splitCoords (n := 4) (n' := 4) x).2
            (splitCoords (n := 4) (n' := 4) x).1) e := h
    exact h'.2
  · intro h
    exact show 1 ≤ 4 + 4 ∧ IsOpen (appendSet (n := 4) (n' := 4) W) ∧ ∀ e,
        ComplexCoordinates.IsHolomorphicIn (N' := 1) (appendSet (n := 4) (n' := 4) W) fun x _ =>
          quotHomEntries (A (splitCoords (n := 4) (n' := 4) x).2
            (splitCoords (n := 4) (n' := 4) x).1) e from ⟨by norm_num, h⟩
theorem componentOpenDomain_const {P : Set (ComplexCoordinates 4)} (hP : IsOpen P)
    (D : ComplexCoordinates 4 → Set (Fin 4 → ℂ)) (B : QuotHom I I') :
    ComponentOpenDomain P D fun _ _ => B := by
  have hU : IsOpen ((univ : Set (ComplexCoordinates 4)) ×ˢ P) := isOpen_univ.prod hP
  refine ⟨univ ×ˢ P, fun w hw => hw.2, fun p hp k _ => ⟨mem_univ _, hp⟩, ?_⟩
  refine isHolomorphicInMomentumPair_iff.2 ⟨isOpen_appendSet hU, fun e => ?_⟩
  exact ⟨isOpen_appendSet hU, continuousOn_const,
    fun _ _ _ => Filter.Eventually.of_forall fun _ => differentiableAt_const _⟩
theorem componentOpenDomain_smul
    (hSmul : ∀ (O : Set (ComplexCoordinates (4 + 4))), IsOpen O → ∀ (c : ℂ)
      (u : ComplexCoordinates (4 + 4) → ℂ), HolomorphicFnOn O u →
        HolomorphicFnOn O fun x => c * u x)
    {P : Set (ComplexCoordinates 4)} {D : ComplexCoordinates 4 → Set (Fin 4 → ℂ)}
    {A : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I I'} (c : ℂ)
    (h : ComponentOpenDomain P D A) : ComponentOpenDomain P D fun p k => c • A p k := by
  obtain ⟨W, h₁, h₂, h₃⟩ := h
  refine ⟨W, h₁, h₂, ?_⟩
  obtain ⟨hO, hE⟩ := isHolomorphicInMomentumPair_iff.1 h₃
  refine isHolomorphicInMomentumPair_iff.2 ⟨hO, fun e => ?_⟩
  have hc := hSmul _ hO c
    (fun x => quotHomEntries (A (splitCoords (n := 4) (n' := 4) x).2
      (splitCoords (n := 4) (n' := 4) x).1) e) (hE e)
  have he : ∀ B : QuotHom I I', quotHomEntries (c • B) e = c * quotHomEntries B e := fun B => by
    simp [quotHomEntries, linearMapEntry]
  have hf : (fun (x : ComplexCoordinates (4 + 4)) (_ : Fin 1) =>
      quotHomEntries (c • A (splitCoords (n := 4) (n' := 4) x).2
        (splitCoords (n := 4) (n' := 4) x).1) e) =
      fun x _ => c * quotHomEntries (A (splitCoords (n := 4) (n' := 4) x).2
        (splitCoords (n := 4) (n' := 4) x).1) e := by
    funext x _
    exact he _
  rw [hf]
  exact hc
theorem jetFamilyHolomorphic_smul
    (hSmul : ∀ (O : Set (ComplexCoordinates (4 + 4))), IsOpen O → ∀ (c : ℂ)
      (u : ComplexCoordinates (4 + 4) → ℂ), HolomorphicFnOn O u →
        HolomorphicFnOn O fun x => c * u x)
    {δ : ℝ} {P : Set (ComplexCoordinates 4)} {T : ComplexCoordinates 4 → JetQuad I I'} (c : ℂ)
    (h : JetFamilyHolomorphic δ P T)
    (hj : ∀ p ∈ P, JetQuad.IsJet δ p (JetQuad.smul c (T p))) :
    JetFamilyHolomorphic δ P fun p => JetQuad.smul c (T p) :=
  ⟨hj, componentOpenDomain_smul hSmul c h.open00, componentOpenDomain_smul hSmul c h.open10,
    componentOpenDomain_smul hSmul c h.open01, componentOpenDomain_smul hSmul c h.open11⟩
end ComponentDomains
theorem jetFamilyHolomorphic_one {δ : ℝ} {P : Set (ComplexCoordinates 4)} (hP : IsOpen P)
    (I : PeriodicData) (hj : ∀ p ∈ P, JetQuad.IsJet δ p (JetQuad.one I)) :
    JetFamilyHolomorphic δ P fun _ => JetQuad.one I :=
  ⟨hj, componentOpenDomain_const hP _ LinearMap.id, componentOpenDomain_const hP _ 0,
    componentOpenDomain_const hP _ 0, componentOpenDomain_const hP _ 0⟩
theorem isInvertibleQuotHom_of_isUnit {I : PeriodicData} {B : QuotHom I I}
    (h : IsUnit (B : Module.End ℂ (I.UnitQuot → ℂ))) : IsInvertibleQuotHom B := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.isInvertibleQuotHom_of_isUnit <;> assumption
theorem componentOpenDomain_inverse {I : PeriodicData} (hI : IsPeriodic I)
    (hDet : QuotHomDetFacts I)
    (hInv : QuotHomFamilyDetInv (4 + 4) I)
    {P : Set (ComplexCoordinates 4)} {D : Set (Fin 4 → ℂ)}
    {A : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I I}
    (h : ComponentOpenDomain P (fun _ => D) A)
    (hU : ∀ p ∈ P, ∀ k ∈ D, IsInvertibleQuotHom (A p k)) :
    ComponentOpenDomain P (fun _ => D) fun p k => quotHomInverse (A p k) := by
  obtain ⟨W, hWP, hWD, hWH⟩ := h
  obtain ⟨hO, hE⟩ := isHolomorphicInMomentumPair_iff.1 hWH
  have := hI.finite_quot
  let e : Fin (Nat.card I.UnitQuot) ≃ I.UnitQuot := (Finite.equivFin I.UnitQuot).symm
  let B : ComplexCoordinates (4 + 4) → QuotHom I I := fun x =>
    A (splitCoords (n := 4) (n' := 4) x).2 (splitCoords (n := 4) (n' := 4) x).1
  have hMatrix : ContinuousOn (fun x => matrixOfEnum (B x) e)
      (appendSet (n := 4) (n' := 4) W) := by
    refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_
    have hc := (hE (e a, e b)).2.1
    exact ((continuous_apply (0 : Fin 1)).comp_continuousOn hc)
  have hDetCont : ContinuousOn (fun x => (matrixOfEnum (B x) e).det)
      (appendSet (n := 4) (n' := 4) W) :=
    (continuous_id.matrix_det).comp_continuousOn hMatrix
  have hS : IsOpen (appendSet (n := 4) (n' := 4) W ∩
      (fun x => (matrixOfEnum (B x) e).det) ⁻¹' {0}ᶜ) :=
    hDetCont.isOpen_inter_preimage hO isOpen_compl_singleton
  have hIff : ∀ C : QuotHom I I, IsInvertibleQuotHom C ↔ (matrixOfEnum C e).det ≠ 0 := by
    intro C
    rw [(hDet C).1 e]
    exact (hDet C).2.2.2
  let W' : Set (ComplexCoordinates 4 × ComplexCoordinates 4) :=
    {w | w ∈ W ∧ IsInvertibleQuotHom (A w.2 w.1)}
  have hSet : appendSet (n := 4) (n' := 4) W' = appendSet (n := 4) (n' := 4) W ∩
      (fun x => (matrixOfEnum (B x) e).det) ⁻¹' {0}ᶜ := by
    rw [appendSet_eq_preimage_splitCoords, appendSet_eq_preimage_splitCoords]
    ext x
    exact and_congr_right fun _ => hIff (B x)
  have hSub : appendSet (n := 4) (n' := 4) W' ⊆ appendSet (n := 4) (n' := 4) W := by
    rw [hSet]
    exact inter_subset_left
  have hOpen : IsOpen (appendSet (n := 4) (n' := 4) W') := hSet ▸ hS
  have hInvertible : ∀ x ∈ appendSet (n := 4) (n' := 4) W', IsInvertibleQuotHom (B x) := by
    intro x hx
    rw [appendSet_eq_preimage_splitCoords] at hx
    exact hx.2
  have hHol : QuotHomFamilyHolomorphicOn (appendSet (n := 4) (n' := 4) W') B := by
    refine ⟨by norm_num, hOpen, fun c => ?_⟩
    have hc := hE c
    exact ⟨hOpen, hc.2.1.mono hSub, fun a ha => hc.2.2 a (hSub ha)⟩
  have hRes := ((hInv _ B hInvertible).2 hOpen hHol).2
  exact ⟨W', fun w hw => hWP w hw.1, fun p hp k hk => ⟨hWD p hp k hk, hU p hp k hk⟩, hRes⟩
theorem invertibleJetInverseHolomorphic_holds (hAlgebra : JetClosure.JetOpsClosed)
    (hZero : ZeroPartJets.Claim)
    (hLocal : JetDomains.OpFunJetTheory)
    (hEntries : EntriesDets.Claim)
    (hSymbols : StripSymbols.Claim) : InvertibleJetInverseHolomorphic := by
  intro δ hδ P hP hPs I hI T hT hInvT
  have hStrip : ∀ p ∈ P, p ∈ imStrip δ := by
    intro p hp
    obtain ⟨e, -, hsub, -⟩ := hSymbols.1 δ hδ
    exact hsub (e ▸ hPs hp)
  have hSmul : ∀ (O : Set (ComplexCoordinates (4 + 4))), IsOpen O → ∀ (c : ℂ)
      (u : ComplexCoordinates (4 + 4) → ℂ), HolomorphicFnOn O u →
        HolomorphicFnOn O fun x => c * u x := fun O hO =>
    ((hEntries.2.2.2.2.2.2.1 (4 + 4) O (by norm_num) hO).2.2.2.2.2.1).2.2.2
  have hFacts : ∀ p ∈ P, JetDomains.JetAlgebra I I I δ p := fun p hp =>
    hLocal.2.2 I I I hI hI hI δ p hδ (hStrip p hp)
  have hZ := fun p (hp : p ∈ P) => hZero I I hI hI δ p hδ (hStrip p hp)
  have hOne : JetFamilyHolomorphic δ P fun _ => JetQuad.one I :=
    jetFamilyHolomorphic_one hP I fun p hp => (hZ p hp).2.1
  have hI3 := hEntries.2.2.1 I hI
  have hA : JetFamilyHolomorphic δ P fun p => JetQuad.zeroPartInv (T p) := by
    refine ⟨fun p hp => ((hZ p hp).2.2 (T p) (hInvT p hp)).2.1, ?_,
      componentOpenDomain_const hP _ 0, componentOpenDomain_const hP _ 0,
      componentOpenDomain_const hP _ 0⟩
    exact componentOpenDomain_inverse hI hI3.2.1 (hI3.2.2.2 (4 + 4) (by norm_num)) hT.open00
      fun p hp k hk => isInvertibleQuotHom_of_isUnit ((hInvT p hp).isUnit_f00 k hk)
  obtain ⟨hAdd, hMul, -⟩ := hAlgebra δ hδ P hP hPs I I I hI hI hI
  have hNegOne : JetFamilyHolomorphic δ P fun _ => JetQuad.smul (-1) (JetQuad.one I) :=
    jetFamilyHolomorphic_smul hSmul (-1) hOne fun p hp =>
      (hFacts p hp).smul_isJet _ _ (hOne.is_jet p hp)
  have hN : JetFamilyHolomorphic δ P fun p => JetQuad.normalize p (T p) :=
    hAdd _ _ (hMul _ _ hA hT) hNegOne
  have hNegN : JetFamilyHolomorphic δ P fun p =>
      JetQuad.smul (-1) (JetQuad.normalize p (T p)) :=
    jetFamilyHolomorphic_smul hSmul (-1) hN fun p hp =>
      (hFacts p hp).smul_isJet _ _ (hN.is_jet p hp)
  exact hMul _ _ (hAdd _ _ (hAdd _ _ hOne hNegN) (hMul _ _ hN hN)) hA
end YangMills.Construction.Tower.FullSpace.InverseJetHolomorphy
end
