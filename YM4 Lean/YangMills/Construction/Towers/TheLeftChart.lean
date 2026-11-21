import YangMills.Construction.Towers.FormsOnTowers
import YangMills.Construction.Towers.FunctionsOfFiniteBondSets
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower
section Formulas
variable {α : Type*} (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
def directionalDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (φ : (α → ComplexMatrix2) → E) (B : α → ComplexMatrix2) : E :=
  deriv (fun t : 𝕜 => φ (algebraMap 𝕜 ℂ t • B)) 0
def mixedDirectionalDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (φ : (α → ComplexMatrix2) → E) (B B' : α → ComplexMatrix2) : E :=
  deriv (fun s : 𝕜 => deriv (fun t : 𝕜 => φ (algebraMap 𝕜 ℂ s • B + algebraMap 𝕜 ℂ t • B')) 0) 0
def logDirectionalDeriv [NormedSpace 𝕜 ComplexMatrix2] (φ : (α → ComplexMatrix2) → ComplexMatrix2)
    (W : ComplexMatrix2) (B : α → ComplexMatrix2) : ComplexMatrix2 :=
  Complex.I⁻¹ • deriv (fun t : 𝕜 => ComplexMatrix2.logSeries (φ (algebraMap 𝕜 ℂ t • B) * W⁻¹)) 0
end Formulas
def IsOpenIntervalAroundZero (I : Set ℝ) : Prop := IsOpen I ∧ I.OrdConnected ∧ (0 : ℝ) ∈ I
structure PairedFunctionSpace where
  index : Type
  realSubmodule : Submodule ℝ (index → ComplexMatrix2)
  complexSubmodule : Submodule ℂ (index → ComplexMatrix2)
  pair : (index → ComplexMatrix2) → (index → ComplexMatrix2) → ℂ
  IsFinitelySupported : (index → ComplexMatrix2) → Prop
def pairedFunctions (ι : Type) : PairedFunctionSpace where
  index := ι
  realSubmodule := GroupLieProduct.hermitianTracelessFunctions ι
  complexSubmodule := GroupLieProduct.tracelessFunctions ι
  pair := traceFinsumPairing
  IsFinitelySupported := HasFiniteSupp
namespace PairedFunctionSpace
variable {S S' : PairedFunctionSpace}
def PreservesFiniteSupport (T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule) : Prop :=
  ∀ f : S.complexSubmodule, S.IsFinitelySupported f → S'.IsFinitelySupported (T f)
def IsTransposeMap (T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule)
    (T' : S'.complexSubmodule →ₗ[ℂ] S.complexSubmodule) : Prop :=
  ∀ (g : S'.complexSubmodule) (f : S.complexSubmodule), S.IsFinitelySupported f →
    S.pair (T' g) f = S'.pair g (T f)
def transposeMap (T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule) :
    S'.complexSubmodule →ₗ[ℂ] S.complexSubmodule :=
  Classical.epsilon (IsTransposeMap T)
def IsComplexification (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule)
    (T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule) : Prop :=
  ∀ (f f' : S.realSubmodule) (h : S.complexSubmodule),
    (h : S.index → ComplexMatrix2) = f + Complex.I • (f' : S.index → ComplexMatrix2) →
    (T h : S'.index → ComplexMatrix2) = T₀ f + Complex.I • (T₀ f' : S'.index → ComplexMatrix2)
def complexification (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) :
    S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule :=
  Classical.epsilon (IsComplexification T₀)
def IsRealTransposeMap (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule)
    (T₀' : S'.realSubmodule →ₗ[ℝ] S.realSubmodule) : Prop :=
  ∀ (g : S'.realSubmodule) (h : S'.complexSubmodule), (h : S'.index → ComplexMatrix2) = g →
    (T₀' g : S.index → ComplexMatrix2) = transposeMap (complexification T₀) h
def realTransposeMap (T₀ : S.realSubmodule →ₗ[ℝ] S'.realSubmodule) :
    S'.realSubmodule →ₗ[ℝ] S.realSubmodule :=
  Classical.epsilon (IsRealTransposeMap T₀)
end PairedFunctionSpace
section FiniteSide
variable {L n k j j' : ℕ}
def extendOddly (f : Edge L n k j → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  open Classical in fun b => if b.IsPositivelyOriented then f b else -f b.opposite
def fieldsIn (L n k j : ℕ) (𝒢 : Set ComplexMatrix2) : Set (Edge L n k j → ComplexMatrix2) :=
  {U | PeriodicLattice.IsGaugeField 𝒢 univ U}
def edgePower (L n k j : ℕ) (𝒢 : Set ComplexMatrix2) : Set (PositiveEdge L n k j → ComplexMatrix2) :=
  {w | ∀ b, w b ∈ 𝒢}
theorem edgePower_compactGaugeGroup :
    edgePower L n k j PeriodicLattice.compactGaugeGroup = specialUnitaryPower (PositiveEdge L n k j) :=
  rfl
def fieldOfPositiveValues (w : PositiveEdge L n k j → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  open Classical in fun b =>
    if h : b.IsPositivelyOriented then w ⟨b, h⟩
    else if h' : b.opposite.IsPositivelyOriented then (w ⟨b.opposite, h'⟩)⁻¹
    else 1
def IsOpenFieldSet (𝒢 : Set ComplexMatrix2) (𝔇 : Set (Edge L n k j → ComplexMatrix2)) : Prop :=
  𝔇 ⊆ fieldsIn L n k j 𝒢 ∧
    ComplexMatrix2.IsRelativelyOpen (edgePower L n k j 𝒢) (restrictToPositiveEdges '' 𝔇)
def IsDifferentiableFn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝔇 : Set (Edge L n k j → ComplexMatrix2)) (F : (Edge L n k j → ComplexMatrix2) → E) : Prop :=
  IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝔇 ∧ ∃ _ : Fintype (PositiveEdge L n k j),
    EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower (PositiveEdge L n k j))
      (restrictToPositiveEdges '' 𝔇) fun w => F (fieldOfPositiveValues w)
def IsTwiceDifferentiableFn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝔇 : Set (Edge L n k j → ComplexMatrix2)) (F : (Edge L n k j → ComplexMatrix2) → E) : Prop :=
  IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝔇 ∧ ∃ _ : Fintype (PositiveEdge L n k j),
    EmbeddedSubmanifold.HasDifferentiablePartialsOn (specialUnitaryPower (PositiveEdge L n k j))
      (restrictToPositiveEdges '' 𝔇) fun w => F (fieldOfPositiveValues w)
def IsDifferentiableFieldMap (𝔇 : Set (Edge L n k j → ComplexMatrix2))
    (Φ : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2) : Prop :=
  IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝔇 ∧ MapsTo Φ 𝔇 (fieldSpace L n k j') ∧
    ∃ (_ : Fintype (PositiveEdge L n k j)) (_ : Fintype (PositiveEdge L n k j')),
      specialUnitaryPower.IsDifferentiableInto (restrictToPositiveEdges '' 𝔇)
        fun w => restrictToPositiveEdges (Φ (fieldOfPositiveValues w))
def tangentAt [Fintype (PositiveEdge L n k j)] (U : Edge L n k j → ComplexMatrix2) :
    Submodule ℝ (PositiveEdge L n k j → ComplexMatrix2) :=
  EmbeddedSubmanifold.tangentSpace (specialUnitaryPower (PositiveEdge L n k j))
    (restrictToPositiveEdges U)
def leftChartTangent (U B : Edge L n k j → ComplexMatrix2) : PositiveEdge L n k j → ComplexMatrix2 :=
  fun b => deriv (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B) U b) 0
def IsDifferentiableFieldCurve (𝒢 : Set ComplexMatrix2) (I : Set ℝ)
    (γ : ℝ → Edge L n k j → ComplexMatrix2) : Prop :=
  IsOpenIntervalAroundZero I ∧ MapsTo γ I (fieldsIn L n k j 𝒢) ∧
    ∀ b : Edge L n k j, b.IsPositivelyOriented → DifferentiableOn ℝ (fun t => γ t b) I
def curveTangent (γ : ℝ → Edge L n k j → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  extendOddly fun b => Complex.I⁻¹ • (deriv (fun t => γ t b) 0 * (γ 0 b)⁻¹)
def leftDifferential (Φ : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2)
    (U B : Edge L n k j → ComplexMatrix2) : Edge L n k j' → ComplexMatrix2 :=
  extendOddly fun c =>
    logDirectionalDeriv ℝ (fun X => Φ (PeriodicLattice.expTwist X U) c) (Φ U c) B
def leftDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (Edge L n k j → ComplexMatrix2) → E) (U B : Edge L n k j → ComplexMatrix2) : E :=
  directionalDeriv ℝ (fun X => F (PeriodicLattice.expTwist X U)) B
def leftSecondDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (Edge L n k j → ComplexMatrix2) → E) (U B B' : Edge L n k j → ComplexMatrix2) : E :=
  mixedDirectionalDeriv ℝ (fun X => F (PeriodicLattice.expTwist X U)) B B'
def IsLeftGradient (𝔇 : Set (Edge L n k j → ComplexMatrix2)) (F : (Edge L n k j → ComplexMatrix2) → ℂ)
    (U X : Edge L n k j → ComplexMatrix2) : Prop :=
  PeriodicLattice.IsBondForm PeriodicLattice.complexLieAlgebra X ∧
    ((∀ V ∈ 𝔇, (F V).im = 0) → PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra X) ∧
    ∀ B ∈ edgeFormSpace L n k j, HasFiniteSupp (restrictToPositiveEdges B) →
      edgeFormPairing X B = leftDeriv F U B
def leftGradient (𝔇 : Set (Edge L n k j → ComplexMatrix2)) (F : (Edge L n k j → ComplexMatrix2) → ℂ)
    (U : Edge L n k j → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  Classical.epsilon (IsLeftGradient 𝔇 F U)
def covDiff (U : Edge L n k j → ComplexMatrix2) (l : Vertex L n k j → ComplexMatrix2) :
    Edge L n k j → ComplexMatrix2 :=
  extendOddly fun b => ComplexMatrix2.conjugateBy (U b) (l b.target) - l b.source
def adjointForm (u : Vertex L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2) :
    Edge L n k j → ComplexMatrix2 :=
  extendOddly fun b => ComplexMatrix2.conjugateBy (u b.source) (B b)
def adjointVertexFn (u : Vertex L n k j → ComplexMatrix2) (l : Vertex L n k j → ComplexMatrix2) :
    Vertex L n k j → ComplexMatrix2 :=
  fun x => ComplexMatrix2.conjugateBy (u x) (l x)
def tangentEdgeValue (U B : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) : ComplexMatrix2 :=
  open Classical in
  if b.IsPositivelyOriented then B b
  else -ComplexMatrix2.conjugateBy (U b.opposite)⁻¹ (B b.opposite)
def isometryOnTangent (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (U B : Edge L n k j → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  extendOddly fun b => tangentEdgeValue U B (edgePreimage f b)
def complexEdgeForms (L n k j : ℕ) : Submodule ℂ (Edge L n k j → ComplexMatrix2) where
  carrier := {B | PeriodicLattice.IsBondForm PeriodicLattice.complexLieAlgebra B}
  add_mem' := by
    rintro B B' ⟨h, r⟩ ⟨h', r'⟩
    refine ⟨fun b hb => ComplexMatrix2.traceless.add_mem (h b hb) (h' b hb), fun b => ?_⟩
    simp only [Pi.add_apply, r, r']
    abel
  zero_mem' := ⟨fun b _ => ComplexMatrix2.traceless.zero_mem, fun b => by simp⟩
  smul_mem' := by
    rintro c B ⟨h, r⟩
    refine ⟨fun b hb => ComplexMatrix2.traceless.smul_mem c (h b hb), fun b => ?_⟩
    simp only [Pi.smul_apply, r, smul_neg]
def edgePairedSpace (L n k j : ℕ) : PairedFunctionSpace where
  index := Edge L n k j
  realSubmodule := edgeFormSpace L n k j
  complexSubmodule := complexEdgeForms L n k j
  pair := edgeFormPairing
  IsFinitelySupported := fun B => HasFiniteSupp (restrictToPositiveEdges B)
def IsHolomorphicFn {E : Type} {l : ℕ} (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : E ≃ Coordinates.ComplexCoordinates l) (𝔇 : Set (Edge L n k j → ComplexMatrix2))
    (F : (Edge L n k j → ComplexMatrix2) → E) : Prop :=
  IsOpenFieldSet PeriodicLattice.complexGaugeGroup 𝔇 ∧ ∃ _ : Fintype (PositiveEdge L n k j),
    GroupLieProduct.IsHolomorphicToCoords β e
      (GroupLieProduct.asGroupFactors '' (restrictToPositiveEdges '' 𝔇))
      fun p => F (fieldOfPositiveValues fun b => p (.inl b))
def IsHolomorphicFieldMap (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (𝔇 : Set (Edge L n k j → ComplexMatrix2))
    (Φ : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2) : Prop :=
  IsOpenFieldSet PeriodicLattice.complexGaugeGroup 𝔇 ∧
    MapsTo Φ 𝔇 (fieldsIn L n k j' PeriodicLattice.complexGaugeGroup) ∧
    ∃ (_ : Fintype (PositiveEdge L n k j)) (_ : Fintype (PositiveEdge L n k j')),
      GroupLieProduct.IsHolomorphicToProduct β
        (GroupLieProduct.asGroupFactors '' (restrictToPositiveEdges '' 𝔇))
        fun p => GroupLieProduct.asGroupFactors
          (restrictToPositiveEdges (Φ (fieldOfPositiveValues fun b => p (.inl b))))
def holLeftDifferential (Φ : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2)
    (U B : Edge L n k j → ComplexMatrix2) : Edge L n k j' → ComplexMatrix2 :=
  extendOddly fun c =>
    logDirectionalDeriv ℂ (fun X => Φ (PeriodicLattice.expTwist X U) c) (Φ U c) B
def holLeftDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : (Edge L n k j → ComplexMatrix2) → E) (U B : Edge L n k j → ComplexMatrix2) : E :=
  directionalDeriv ℂ (fun X => F (PeriodicLattice.expTwist X U)) B
def holLeftSecondDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : (Edge L n k j → ComplexMatrix2) → E) (U B B' : Edge L n k j → ComplexMatrix2) : E :=
  mixedDirectionalDeriv ℂ (fun X => F (PeriodicLattice.expTwist X U)) B B'
end FiniteSide
namespace FullSpace
section OneLattice
variable {a : ℝ}
def expTwist (A U : InfiniteLattice.Link a → ComplexMatrix2) : InfiniteLattice.Link a → ComplexMatrix2 :=
  open Classical in
  fun b => if b.IsPositivelyOriented then ComplexMatrix2.matExp (Complex.I • A b) * U b
    else (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹
def extendOddly (f : InfiniteLattice.Link a → ComplexMatrix2) : InfiniteLattice.Link a → ComplexMatrix2 :=
  open Classical in fun b => if b.IsPositivelyOriented then f b else -f b.opposite
def IsEdgeFormIn (𝔥 : Set ComplexMatrix2) (B : InfiniteLattice.Link a → ComplexMatrix2) : Prop :=
  (∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → B b ∈ 𝔥) ∧
    ∀ b : InfiniteLattice.Link a, B b.opposite = -B b
def IsDifferentiableFieldCurve (𝒢 : Set ComplexMatrix2) (I : Set ℝ)
    (γ : ℝ → InfiniteLattice.Link a → ComplexMatrix2) : Prop :=
  IsOpenIntervalAroundZero I ∧ MapsTo γ I {U | IsFieldIn 𝒢 U} ∧
    ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → DifferentiableOn ℝ (fun t => γ t b) I
def curveTangent (γ : ℝ → InfiniteLattice.Link a → ComplexMatrix2) :
    InfiniteLattice.Link a → ComplexMatrix2 :=
  extendOddly fun b => Complex.I⁻¹ • (deriv (fun t => γ t b) 0 * (γ 0 b)⁻¹)
def covDiff (U : InfiniteLattice.Link a → ComplexMatrix2)
    (l : InfiniteLattice.LatticePoint a → ComplexMatrix2) : InfiniteLattice.Link a → ComplexMatrix2 :=
  extendOddly fun b => ComplexMatrix2.conjugateBy (U b) (l b.terminal) - l b.initial
def adjointForm (u : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B : InfiniteLattice.Link a → ComplexMatrix2) : InfiniteLattice.Link a → ComplexMatrix2 :=
  extendOddly fun b => ComplexMatrix2.conjugateBy (u b.initial) (B b)
def adjointVertexFn (u l : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    InfiniteLattice.LatticePoint a → ComplexMatrix2 :=
  fun x => ComplexMatrix2.conjugateBy (u x) (l x)
def tangentEdgeValue (U B : InfiniteLattice.Link a → ComplexMatrix2) (b : InfiniteLattice.Link a) :
    ComplexMatrix2 :=
  open Classical in
  if b.IsPositivelyOriented then B b
  else -ComplexMatrix2.conjugateBy (U b.opposite)⁻¹ (B b.opposite)
def isometryOnTangent (f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace)
    (U B : InfiniteLattice.Link a → ComplexMatrix2) : InfiniteLattice.Link a → ComplexMatrix2 :=
  extendOddly fun b => tangentEdgeValue U B (edgePreimage f b)
def complexEdgeForms (a : ℝ) : Submodule ℂ (InfiniteLattice.Link a → ComplexMatrix2) where
  carrier := {B | IsEdgeFormIn PeriodicLattice.complexLieAlgebra B}
  add_mem' := by
    rintro B B' ⟨h, r⟩ ⟨h', r'⟩
    refine ⟨fun b hb => ComplexMatrix2.traceless.add_mem (h b hb) (h' b hb), fun b => ?_⟩
    simp only [Pi.add_apply, r, r']
    abel
  zero_mem' := ⟨fun b _ => ComplexMatrix2.traceless.zero_mem, fun b => by simp⟩
  smul_mem' := by
    rintro c B ⟨h, r⟩
    refine ⟨fun b hb => ComplexMatrix2.traceless.smul_mem c (h b hb), fun b => ?_⟩
    simp only [Pi.smul_apply, r, smul_neg]
def edgePairedSpace (a : ℝ) : PairedFunctionSpace where
  index := InfiniteLattice.Link a
  realSubmodule := edgeFormSpace a
  complexSubmodule := complexEdgeForms a
  pair := finiteEdgePairing
  IsFinitelySupported := fun B => HasFiniteSupp (restrictToPositiveEdges B)
end OneLattice
section Presentations
variable {L k j j' : ℕ}
structure LocalData (L k j : ℕ) (E : Type) where
  support : Finset (Edge L k j)
  region : Set (support → ComplexMatrix2)
  fn : (support → ComplexMatrix2) → E
instance instNonemptyLocalData {E : Type} [Nonempty E] : Nonempty (LocalData L k j E) :=
  ⟨⟨∅, ∅, fun _ => Classical.arbitrary E⟩⟩
abbrev PresentationClass (L k j : ℕ) (E : Type) : Type :=
  ∀ F : Finset (Edge L k j), Set (F → ComplexMatrix2) → ((F → ComplexMatrix2) → E) → Prop
def differentiablePresentations (L k j : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    PresentationClass L k j E :=
  fun F O f => EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower F) O f
def holomorphicPresentations (L k j : ℕ) {E : Type} {l : ℕ}
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : E ≃ Coordinates.ComplexCoordinates l) : PresentationClass L k j E :=
  fun _ O f => GroupLieProduct.IsHolomorphicToCoords β e
    (GroupLieProduct.asGroupFactors '' O) fun p => f fun b => p (.inl b)
def chosenPresentation {E : Type} [Nonempty E] (𝒢 : Set ComplexMatrix2)
    (𝔇 : Set (Edge L k j → ComplexMatrix2)) (K : PresentationClass L k j E)
    (h : (Edge L k j → ComplexMatrix2) → E) (U : Edge L k j → ComplexMatrix2) : LocalData L k j E :=
  Classical.epsilon fun w =>
    IsLocalPresentation 𝒢 𝔇 h U w.support w.region w.fn ∧ K w.support w.region w.fn
def valueViaPresentation {E : Type} [Nonempty E] (𝒢 : Set ComplexMatrix2)
    (𝔇 : Set (Edge L k j → ComplexMatrix2)) (K : PresentationClass L k j E)
    (h : (Edge L k j → ComplexMatrix2) → E) (U X : Edge L k j → ComplexMatrix2) : E :=
  (chosenPresentation 𝒢 𝔇 K h U).fn fun b => ComplexMatrix2.matExp (Complex.I • X b) * U b
def IsDifferentiableFn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝔇 : Set (Edge L k j → ComplexMatrix2)) (F : (Edge L k j → ComplexMatrix2) → E) : Prop :=
  IsFinitelyOpen PeriodicLattice.compactGaugeGroup 𝔇 ∧ IsFinitelyDifferentiable 𝔇 F
def IsDifferentiableFieldMap (𝔇 : Set (Edge L k j → ComplexMatrix2))
    (Φ : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2) : Prop :=
  IsFinitelyOpen PeriodicLattice.compactGaugeGroup 𝔇 ∧ MapsTo Φ 𝔇 (fieldSpace L k j') ∧
    ∀ c : Edge L k j', c.IsPositivelyOriented → IsFinitelyDifferentiable 𝔇 fun U => Φ U c
def leftDifferential (𝔇 : Set (Edge L k j → ComplexMatrix2))
    (Φ : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2)
    (U B : Edge L k j → ComplexMatrix2) : Edge L k j' → ComplexMatrix2 :=
  extendOddly fun c => logDirectionalDeriv ℝ
    (valueViaPresentation PeriodicLattice.compactGaugeGroup 𝔇
      (differentiablePresentations L k j ComplexMatrix2) (fun U' => Φ U' c) U) (Φ U c) B
def leftDeriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nonempty E]
    (𝔇 : Set (Edge L k j → ComplexMatrix2)) (F : (Edge L k j → ComplexMatrix2) → E)
    (U B : Edge L k j → ComplexMatrix2) : E :=
  directionalDeriv ℝ
    (valueViaPresentation PeriodicLattice.compactGaugeGroup 𝔇
      (differentiablePresentations L k j E) F U) B
def IsHolomorphicFn {E : Type} {l : ℕ} (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : E ≃ Coordinates.ComplexCoordinates l) (𝔇 : Set (Edge L k j → ComplexMatrix2))
    (F : (Edge L k j → ComplexMatrix2) → E) : Prop :=
  IsFinitelyOpen PeriodicLattice.complexGaugeGroup 𝔇 ∧ IsFinitelyHolomorphic β e 𝔇 F
def IsHolomorphicFieldMap (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (𝔇 : Set (Edge L k j → ComplexMatrix2))
    (Φ : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2) : Prop :=
  IsFinitelyOpen PeriodicLattice.complexGaugeGroup 𝔇 ∧
    MapsTo Φ 𝔇 (fieldsValuedIn L k j' PeriodicLattice.complexGaugeGroup) ∧
    ∀ c : Edge L k j', c.IsPositivelyOriented →
      IsFinitelyHolomorphic β Coordinates.ComplexCoordinates.matrixEquiv 𝔇 fun U => Φ U c
def holLeftDifferential (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (𝔇 : Set (Edge L k j → ComplexMatrix2))
    (Φ : (Edge L k j → ComplexMatrix2) → Edge L k j' → ComplexMatrix2)
    (U B : Edge L k j → ComplexMatrix2) : Edge L k j' → ComplexMatrix2 :=
  extendOddly fun c => logDirectionalDeriv ℂ
    (valueViaPresentation PeriodicLattice.complexGaugeGroup 𝔇
      (holomorphicPresentations L k j β Coordinates.ComplexCoordinates.matrixEquiv)
      (fun U' => Φ U' c) U)
    (Φ U c) B
def holLeftDeriv {E : Type} {l : ℕ} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Nonempty E] (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : E ≃ Coordinates.ComplexCoordinates l)
    (𝔇 : Set (Edge L k j → ComplexMatrix2)) (F : (Edge L k j → ComplexMatrix2) → E)
    (U B : Edge L k j → ComplexMatrix2) : E :=
  directionalDeriv ℂ
    (valueViaPresentation PeriodicLattice.complexGaugeGroup 𝔇 (holomorphicPresentations L k j β e) F U) B
def holLeftSecondDeriv {E : Type} {l : ℕ} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Nonempty E] (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : E ≃ Coordinates.ComplexCoordinates l)
    (𝔇 : Set (Edge L k j → ComplexMatrix2)) (F : (Edge L k j → ComplexMatrix2) → E)
    (U B B' : Edge L k j → ComplexMatrix2) : E :=
  mixedDirectionalDeriv ℂ
    (valueViaPresentation PeriodicLattice.complexGaugeGroup 𝔇 (holomorphicPresentations L k j β e) F U)
    B B'
end Presentations
end FullSpace
end Tower
end YangMills.Construction
end
