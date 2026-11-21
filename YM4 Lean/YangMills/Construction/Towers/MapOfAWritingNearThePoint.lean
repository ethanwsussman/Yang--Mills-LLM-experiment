import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.FunctionsOfFiniteBondSets
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace LocalPresentations
open Tower.FullSpace
variable {L k j : ℕ}
def positiveEdgeValue (F : Finset (Edge L k j)) (U : Edge L k j → Matrices.ComplexMatrix2)
    (w : F → Matrices.ComplexMatrix2) (e : Edge L k j) : Matrices.ComplexMatrix2 :=
  open Classical in if he : e ∈ F then w ⟨e, he⟩ else U e
def replaceOn (F : Finset (Edge L k j)) (U : Edge L k j → Matrices.ComplexMatrix2)
    (w : F → Matrices.ComplexMatrix2) : Edge L k j → Matrices.ComplexMatrix2 :=
  open Classical in
  fun e => if e.IsPositivelyOriented then positiveEdgeValue F U w e
    else (positiveEdgeValue F U w e.opposite)⁻¹
def restrictTuple {F' F : Finset (Edge L k j)} (hF : F' ⊆ F) (w : F → Matrices.ComplexMatrix2) :
    F' → Matrices.ComplexMatrix2 :=
  fun e => w ⟨e, hF e.2⟩
def realLine : Set ℂ := {z | z.im = 0}
def realEntryMatrices : Set Matrices.ComplexMatrix2 := {M | ∀ r s : Fin 2, (M r s).im = 0}
def PresentationsAgree {E : Type} (𝒢 : Set Matrices.ComplexMatrix2)
    (𝔇 : Set (Edge L k j → Matrices.ComplexMatrix2))
    (h : (Edge L k j → Matrices.ComplexMatrix2) → E) (U : Edge L k j → Matrices.ComplexMatrix2) :
    Prop :=
  ∀ (F₁ F₂ F : Finset (Edge L k j)) (O₁ : Set (F₁ → Matrices.ComplexMatrix2))
    (O₂ : Set (F₂ → Matrices.ComplexMatrix2))
    (f₁ : (F₁ → Matrices.ComplexMatrix2) → E) (f₂ : (F₂ → Matrices.ComplexMatrix2) → E)
    (h₁ : F₁ ⊆ F) (h₂ : F₂ ⊆ F),
    IsFinitePositiveEdgeSet F → IsLocalPresentation 𝒢 𝔇 h U F₁ O₁ f₁ →
      IsLocalPresentation 𝒢 𝔇 h U F₂ O₂ f₂ →
      ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ edgeProduct 𝒢 F,
        (∀ e : F, Matrices.ComplexMatrix2.operatorNorm (w e - U e) < ε) →
        replaceOn F U w ∈ 𝔇 ∧ restrictTuple h₁ w ∈ O₁ ∧ restrictTuple h₂ w ∈ O₂ ∧
          f₁ (restrictTuple h₁ w) = h (replaceOn F U w) ∧
          f₂ (restrictTuple h₂ w) = h (replaceOn F U w)
def PresentationShrinks {E : Type} (𝒢 : Set Matrices.ComplexMatrix2) (kept : Set (Set E))
    (𝔇 : Set (Edge L k j → Matrices.ComplexMatrix2))
    (h : (Edge L k j → Matrices.ComplexMatrix2) → E)
    (U : Edge L k j → Matrices.ComplexMatrix2) : Prop :=
  ∀ (F : Finset (Edge L k j)) (O : Set (F → Matrices.ComplexMatrix2))
    (f : (F → Matrices.ComplexMatrix2) → E),
    IsLocalPresentation 𝒢 𝔇 h U F O f →
      (∃ O' : Set (F → Matrices.ComplexMatrix2),
        Matrices.ComplexMatrix2.IsRelativelyOpen (edgeProduct 𝒢 F) O' ∧ O' ⊆ O ∧
        restrictToEdges F U ∈ O' ∧
        (∀ w ∈ O', ∃ U' ∈ 𝔇, f w = h U') ∧
        ∀ S ∈ kept, (∀ U' ∈ 𝔇, h U' ∈ S) → ∀ w ∈ O', f w ∈ S) ∧
      ∀ O'' : Set (F → Matrices.ComplexMatrix2),
        Matrices.ComplexMatrix2.IsRelativelyOpen (edgeProduct 𝒢 F) O'' → O'' ⊆ O →
        restrictToEdges F U ∈ O'' → ∀ f'' : (F → Matrices.ComplexMatrix2) → E, EqOn f'' f O'' →
          IsLocalPresentation 𝒢 𝔇 h U F O'' f''
def NearPointProperties (L k j : ℕ) (𝒢 : Set Matrices.ComplexMatrix2) {E : Type}
    (kept : Set (Set E)) : Prop :=
  ∀ (𝔇 : Set (Edge L k j → Matrices.ComplexMatrix2))
    (h : (Edge L k j → Matrices.ComplexMatrix2) → E)
    (U : Edge L k j → Matrices.ComplexMatrix2), IsFinitelyOpen 𝒢 𝔇 → U ∈ 𝔇 →
    (∀ (F : Finset (Edge L k j)) (w : F → Matrices.ComplexMatrix2), IsFinitePositiveEdgeSet F →
      w ∈ edgeProduct 𝒢 F → replaceOn F U w ∈ fieldsValuedIn L k j 𝒢) ∧
    PresentationsAgree 𝒢 𝔇 h U ∧ PresentationShrinks 𝒢 kept 𝔇 h U
def LocalPresentationNearPoint : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j ≤ k →
    NearPointProperties L k j PeriodicLattice.compactGaugeGroup {realLine} ∧
    NearPointProperties L k j PeriodicLattice.compactGaugeGroup
      {realEntryMatrices, PeriodicLattice.compactGaugeGroup} ∧
    NearPointProperties L k j PeriodicLattice.complexGaugeGroup {realLine} ∧
    NearPointProperties L k j PeriodicLattice.complexGaugeGroup
      {realEntryMatrices, PeriodicLattice.complexGaugeGroup}
end LocalPresentations
end YangMills.Construction
end
