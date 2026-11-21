import YangMills.Construction.ClusterExpansion.PolymerSystemOfARegion
import YangMills.Construction.OneLoopLaw.GaugeColourMomentaAndDifferencesOfFunctionalsProof
import YangMills.Construction.Towers.ClosedFormsUnderTheLinearAverageProof
import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import YangMills.Construction.Towers.PolarisationAtTheResponseField
import YangMills.Construction.Towers.PolarisationOfTheTotalNormaliserAlongTheFirstOrderField
import YangMills.Construction.Towers.PolarisationOfTheTotalNormaliserFamilyInTheTower
import YangMills.Construction.Towers.SecondDifferentialOfTheFunctionalAndItsComplexExtension
import YangMills.Construction.Towers.SecondDifferentialOfTheFunctionalOnGaugeDirections
import YangMills.Construction.Towers.TheResponseOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.HessianAtResponseField
open Matrices
open TorusResponseField (complexify complexResponse linearizedField topForm responseField)
open CriticalBranchResponse (CompositeDerivativeEquation)
open PeriodicOperators.Tempered (EventuallyForSides UnitEdge imagComponent complexHessian
  realComponent hessianAtIdentity)
variable {L n k : ℕ}
private theorem eventuallyForSides_and {P Q : ℕ → Prop} (hP : EventuallyForSides L P)
    (hQ : EventuallyForSides L Q) : EventuallyForSides L fun m => P m ∧ Q m := by apply _root_.YangMills.SharedProofs.p21504 <;> assumption
private theorem finite_positiveEdge (hL : 0 < L) (j : ℕ) : Finite (PositiveEdge L n k j) := by
  have : Finite (Vertex L n k j) :=
    (ClusterExpansion.RegionPolymers.sublattice_finite hL n
      (PeriodicLattice.levelDepth k j)).to_subtype
  exact Finite.of_injective (fun e : PositiveEdge L n k j => (e.1.source, e.1.target))
    fun _ _ h => Subtype.ext (PeriodicLattice.Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
abbrev _root_.YangMills.SharedProofs.p11983 := @finite_positiveEdge
private theorem vertexCoboundary_mem {j : ℕ} {f : Vertex L n k j → ComplexMatrix2}
    (hf : f ∈ vertexFunctionSpace L n k j) : vertexCoboundary f ∈ edgeFormSpace L n k j := by apply _root_.YangMills.Construction.Tower.ClosedFormsSmoothing.vertexCoboundary_mem <;> assumption
private theorem realComponent_mem {A : UnitEdge L n → ComplexMatrix2}
    (hA : A ∈ complexEdgeForms L n 0 0) : realComponent A ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p16359 <;> assumption
private theorem imagComponent_mem {A : UnitEdge L n → ComplexMatrix2}
    (hA : A ∈ complexEdgeForms L n 0 0) : imagComponent A ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p9724 <;> assumption
private theorem mem_complexEdgeForms {j : ℕ} {R : Edge L n k j → ComplexMatrix2}
    (hR : R ∈ edgeFormSpace L n k j) : R ∈ complexEdgeForms L n k j := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_complexEdgeForms_of_mem <;> assumption
private theorem complexify_realizedBy (r : RealPeriodicField L n k) :
    (complexify r).RealizedBy r :=
  Classical.epsilon_spec (p := fun ζ : PeriodicField L n k => ζ.RealizedBy r)
    ⟨(⟨r.1, mem_complexEdgeForms r.1.2⟩, ⟨r.2.1, mem_complexEdgeForms r.2.1.2⟩,
      ⟨r.2.2, mem_complexEdgeForms r.2.2.2⟩), rfl, rfl, rfl⟩
abbrev _root_.YangMills.SharedProofs.p20583 := @complexify_realizedBy
private theorem linearizedField_eq {A : Edge L n k k → ComplexMatrix2}
    (h : CompositeDerivativeEquation L n k A) :
    ∃ f ∈ vertexFunctionSpace L n k 0, ∃ g : edgeFormSpace L n k 0,
      (g : Edge L n k 0 → ComplexMatrix2) = vertexCoboundary f ∧
        linearizedField L n k A = responseField L n k A + (g, 0, 0) := by
  obtain ⟨f, hf, he⟩ := h
  have hf' : f ∈ vertexFunctionSpace L n k 0 := hf
  refine ⟨f, hf', ⟨vertexCoboundary f, vertexCoboundary_mem hf'⟩, rfl, ?_⟩
  set g : edgeFormSpace L n k 0 := ⟨vertexCoboundary f, vertexCoboundary_mem hf'⟩ with hg
  have hfst : ((responseField L n k A + (g, 0, 0)).1 : Edge L n k 0 → ComplexMatrix2) =
      leftDifferential (chosenProlongComp L n k k) (trivialField L n k k) A := by
    change ((CriticalBranchResponse.meshScaledResponse L n k A : Edge L n k 0 → ComplexMatrix2) +
      vertexCoboundary f) = _
    rw [he]
    abel
  have hsnd : (responseField L n k A + (g, 0, 0)).2 = (responseField L n k A).2 := by
    simp
  have hspec := Classical.epsilon_spec (p := fun r : RealPeriodicField L n k =>
    (r.1 : Edge L n k 0 → ComplexMatrix2) =
        leftDifferential (chosenProlongComp L n k k) (trivialField L n k k) A ∧
      r.2 = (responseField L n k A).2) ⟨_, hfst, hsnd⟩
  refine Prod.ext (Subtype.ext ?_) ?_
  · exact hspec.1.trans hfst.symm
  · exact hspec.2.trans hsnd.symm
private theorem secondDeriv_linearizedField [Fintype (PositiveEdge L n k 0)]
    [Fintype (PositiveEdge L n k k)] (hExt : HessianAndComplexExtension L n k)
    (hGauge : ∀ f ∈ vertexFunctionSpace L n k 0, ∀ g : edgeFormSpace L n k 0,
      (g : Edge L n k 0 → ComplexMatrix2) = vertexCoboundary f → ∀ ζ : RealPeriodicField L n k,
        fieldFunctionalSecondDeriv L n k (g, 0, 0) ζ = 0)
    {A A' : Edge L n k k → ComplexMatrix2} (h : CompositeDerivativeEquation L n k A)
    (h' : CompositeDerivativeEquation L n k A') :
    fieldFunctionalSecondDeriv L n k (linearizedField L n k A) (linearizedField L n k A') =
      fieldFunctionalSecondDeriv L n k (responseField L n k A) (responseField L n k A') := by
  obtain ⟨β, hβ, hsym⟩ := hExt.exists_symm_bilinForm
  obtain ⟨f, hf, g, hg, e⟩ := linearizedField_eq h
  obtain ⟨f', hf', g', hg', e'⟩ := linearizedField_eq h'
  have h₁ : ∀ ζ, β (g, 0, 0) ζ = 0 := fun ζ => (hβ _ _).trans (hGauge f hf g hg ζ)
  have h₂ : ∀ ζ, β ζ (g', 0, 0) = 0 := fun ζ =>
    (hsym _ _).trans ((hβ _ _).trans (hGauge f' hf' g' hg' ζ))
  rw [e, e', ← hβ, ← hβ]
  simp only [map_add, LinearMap.add_apply, h₁, h₂, add_zero]
private theorem hessian_at_side (hS : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hk : 1 ≤ k) (hT : NormaliserFamilyHessianOnTop) (hG : HessianVanishesOnGaugeDirections)
    (hC : HessianAndComplexExtensionHolds)
    (hF : ∀ A ∈ edgeFormSpace L n k k, ∀ A' ∈ edgeFormSpace L n k k,
      leftSecondDeriv (logTotalNormaliserRatio L n k) (trivialField L n k k) A A' =
        fieldFunctionalSecondDeriv L n k (linearizedField L n k A) (linearizedField L n k A'))
    (hA : ∀ A ∈ edgeFormSpace L n k k, CompositeDerivativeEquation L n k A) :
    ∀ A ∈ complexEdgeForms L n 0 0, ∀ A' ∈ complexEdgeForms L n 0 0,
      complexHessian (logNormaliserFamily L k) n A A' =
        complexSecondDeriv L n k (complexResponse L n k A) (complexResponse L n k A') := by
  have hL : 0 < L := by
    have := hS.2
    omega
  have h₀ : Finite (PositiveEdge L n k 0) := finite_positiveEdge hL 0
  have hₖ : Finite (PositiveEdge L n k k) := finite_positiveEdge hL k
  let _ : Fintype (PositiveEdge L n k 0) := Fintype.ofFinite _
  let _ : Fintype (PositiveEdge L n k k) := Fintype.ofFinite _
  have hExt := hC L n k hS hn hk
  obtain ⟨hbij, hpol⟩ := hT L n k hS hn hk
  have hre : ∀ R ∈ edgeFormSpace L n 0 0, ∀ R' ∈ edgeFormSpace L n 0 0,
      hessianAtIdentity (logNormaliserFamily L k) n R R' =
        fieldFunctionalSecondDeriv L n k (responseField L n k (topForm L n k R))
          (responseField L n k (topForm L n k R')) := by
    intro R hR R' hR'
    have hm := hbij.mapsTo hR
    have hm' := hbij.mapsTo hR'
    rw [hpol R hR R' hR', hF _ hm _ hm']
    exact secondDeriv_linearizedField hExt (hG L n k hS hn hk) (hA _ hm) (hA _ hm')
  have hcx : ∀ r r' : RealPeriodicField L n k,
      complexSecondDeriv L n k (complexify r) (complexify r') =
        (fieldFunctionalSecondDeriv L n k r r' : ℂ) := fun r r' =>
    hExt.isComplexSecondDeriv _ _ r r' (complexify_realizedBy r) (complexify_realizedBy r')
  intro A hA₀ A' hA₀'
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [complexHessian, complexResponse, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hcx]
  rw [hre _ (realComponent_mem hA₀) _ (realComponent_mem hA₀'),
    hre _ (imagComponent_mem hA₀) _ (imagComponent_mem hA₀'),
    hre _ (realComponent_mem hA₀) _ (imagComponent_mem hA₀'),
    hre _ (imagComponent_mem hA₀) _ (realComponent_mem hA₀')]
  push_cast
  linear_combination (-(fieldFunctionalSecondDeriv L n k
    (responseField L n k (topForm L n k (imagComponent A)))
    (responseField L n k (topForm L n k (imagComponent A'))) : ℂ)) * hI
theorem claim_holds (hT : NormaliserFamilyHessianOnTop)
    (hF : NormaliserHessianAlongLinearizedField.Claim)
    (hG : HessianVanishesOnGaugeDirections)
    (hC : HessianAndComplexExtensionHolds)
    (hA : CriticalBranchResponse.ResponseConditions) : Claim := by
  intro L hS k hk
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  obtain ⟨s, hs, h⟩ := eventuallyForSides_and (hF L hS (i + 1) hk) (hA L hS i)
  refine ⟨s, hs, fun t ht hst m hm e => ?_⟩
  obtain ⟨hFm, hAm⟩ := h t ht hst m hm e
  exact hessian_at_side hS hm hk hT hG hC hFm fun A hA' => (hAm A hA').1
end YangMills.Construction.Tower.HessianAtResponseField
end
