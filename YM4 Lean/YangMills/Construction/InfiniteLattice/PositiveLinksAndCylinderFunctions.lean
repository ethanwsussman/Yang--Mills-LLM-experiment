import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
abbrev GaugeFieldAtScale (L K : ℕ) : Type := GaugeField (PeriodicLattice.meshSize L (K : ℤ))
theorem Link.opposite_opposite (b : Link a) : b.opposite.opposite = b := rfl
def positiveLinkSet (a : ℝ) : Set (Link a) :=
  {b | ∃ (x : LatticePoint a) (κ : Fin 4), b = Link.forwardFrom x κ}
theorem mem_positiveLinks_iff {b : Link a} :
    b ∈ positiveLinkSet a ↔ b.IsPositivelyOriented := by
  constructor
  · rintro ⟨x, κ, rfl⟩
    exact ⟨κ, by simp [Link.forwardFrom]⟩
  · rintro ⟨κ, h⟩
    exact ⟨b.initial, κ, Link.ext rfl (by
      change b.terminal = b.initial + axisStep a κ
      rw [← h]
      abel)⟩
theorem mem_positiveLinks_or_opposite_mem (b : Link a) :
    b ∈ positiveLinkSet a ∨ b.opposite ∈ positiveLinkSet a := by
  simp only [mem_positiveLinks_iff]
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · exact Or.inl ⟨μ, h⟩
  · refine Or.inr ⟨μ, ?_⟩
    change b.initial - b.terminal = axisStep a μ
    rw [← neg_sub, h, neg_neg]
theorem opposite_notMem_positiveLinks (ha : 0 < a) {b : Link a}
    (hb : b ∈ positiveLinkSet a) : b.opposite ∉ positiveLinkSet a := by
  rw [mem_positiveLinks_iff] at hb ⊢
  obtain ⟨μ, h₁⟩ := hb
  rintro ⟨ν, h₂⟩
  have h₂' : b.initial - b.terminal = axisStep a ν := h₂
  have hs : axisStep a μ + axisStep a ν = 0 := by
    rw [← h₁, ← h₂']
    abel
  have hμ := congrFun (congrArg Subtype.val hs) μ
  by_cases hν : μ = ν
  · subst hν
    simp [axisStep] at hμ
    linarith
  · simp [axisStep, Pi.single_eq_of_ne hν] at hμ
    linarith
theorem xor_mem_positiveLinks (ha : 0 < a) (b : Link a) :
    Xor (b ∈ positiveLinkSet a) (b.opposite ∈ positiveLinkSet a) := by
  rcases mem_positiveLinks_or_opposite_mem b with h | h
  · exact Or.inl ⟨h, opposite_notMem_positiveLinks ha h⟩
  · exact Or.inr ⟨h, fun h' => opposite_notMem_positiveLinks ha h' h⟩
abbrev LinkVariables (ι : Type) : Type := ι → Matrices.ComplexMatrix2.specialUnitary
def LinkVariables.haarMeasure (ι : Type) [Countable ι] : Measure (LinkVariables ι) :=
  Matrices.ComplexMatrix2.haarPi ι
def restrictField (U : GaugeField a) (S : Set (Link a)) : LinkVariables S := fun b => U b
def trivialField (a : ℝ) : GaugeField a := ⟨fun _ => 1, fun _ => by simp⟩
def gluedField (ha : 0 < a) {S : Set (Link a)} (hS : S ⊆ positiveLinkSet a)
    (V : LinkVariables S) (ω : GaugeField a) : GaugeField a :=
  open Classical in
  ⟨fun b => if h : b ∈ S then V ⟨b, h⟩ else
      if h' : b.opposite ∈ S then (V ⟨b.opposite, h'⟩)⁻¹ else ω b, fun b => by
    by_cases h : b ∈ S
    · have h' : b.opposite ∉ S := fun h' =>
        opposite_notMem_positiveLinks ha (hS h) (hS h')
      simp only [h, h', dite_true, dite_false]
      exact dif_pos h
    · by_cases h' : b.opposite ∈ S
      · simp only [h, h', dite_true, dite_false, inv_inv]
      · have h'' : b.opposite.opposite ∉ S := h
        simp only [h, h', h'', dite_false]
        exact ω.2 b⟩
theorem gluedField_apply_of_mem (ha : 0 < a) {S : Set (Link a)}
    (hS : S ⊆ positiveLinkSet a) (V : LinkVariables S) (ω : GaugeField a) (b : S) :
    gluedField ha hS V ω b = V b :=
  dif_pos b.2
theorem gluedField_apply_of_notMem (ha : 0 < a) {S : Set (Link a)}
    (hS : S ⊆ positiveLinkSet a) (V : LinkVariables S) (ω : GaugeField a) {b : Link a}
    (hb : b ∈ positiveLinkSet a \ S) : gluedField ha hS V ω b = ω b := by
  have h' : b.opposite ∉ S := fun h' =>
    opposite_notMem_positiveLinks ha hb.1 (hS h')
  classical
  change (if h : b ∈ S then V ⟨b, h⟩ else
    if h' : b.opposite ∈ S then (V ⟨b.opposite, h'⟩)⁻¹ else ω b) = ω b
  rw [dif_neg hb.2, dif_neg h']
theorem eq_gluedField (ha : 0 < a) {S : Set (Link a)}
    (hS : S ⊆ positiveLinkSet a) (V : LinkVariables S) (ω U : GaugeField a)
    (h₁ : ∀ b : S, U b = V b) (h₂ : ∀ b ∈ positiveLinkSet a \ S, U b = ω b) :
    U = gluedField ha hS V ω := by
  have key : ∀ b ∈ positiveLinkSet a, U b = gluedField ha hS V ω b := fun b hb => by
    by_cases h : b ∈ S
    · rw [h₁ ⟨b, h⟩]
      exact (gluedField_apply_of_mem ha hS V ω ⟨b, h⟩).symm
    · rw [h₂ b ⟨hb, h⟩, gluedField_apply_of_notMem ha hS V ω ⟨hb, h⟩]
  refine Subtype.ext (funext fun b => ?_)
  rcases mem_positiveLinks_or_opposite_mem b with h | h
  · exact key b h
  · have hU := U.2 b.opposite
    have hW := (gluedField ha hS V ω).2 b.opposite
    rw [Link.opposite_opposite] at hU hW
    change U b = (gluedField ha hS V ω) b
    rw [hU, hW, key _ h]
def DependsOnlyOnLinks {E : Type*} (S : Set (Link a)) (F : GaugeField a → E) : Prop :=
  ∀ U U' : GaugeField a, restrictField U S = restrictField U' S → F U = F U'
def DependsOnCoords {ι : Type} {E : Type*} (I : Set ι) (Φ : LinkVariables ι → E) : Prop :=
  ∀ V V' : LinkVariables ι, (∀ b ∈ I, V b = V' b) → Φ V = Φ V'
def DependsOnFinitelyManyCoords {ι : Type} {E : Type*} (Φ : LinkVariables ι → E) : Prop :=
  ∃ I : Set ι, I.Finite ∧ DependsOnCoords I Φ
def positiveLinksWithin (a : ℝ) (S : Set AmbientSpace) : Set (Link a) :=
  positiveLinkSet a ∩ linksWithin S
def localizedBoundedObservables (a : ℝ) (S : Set AmbientSpace) : Set (GaugeField a → ℂ) :=
  {F | IsBoundedObservable F ∧ DependsOnlyOnLinks (positiveLinksWithin a S) F}
def IsCylinderFunction {E : Type*} (F : GaugeField a → E) : Prop :=
  ∃ W : Set (Link a), W.Finite ∧ W ⊆ positiveLinkSet a ∧ DependsOnlyOnLinks W F
def continuousCylinderFunctions (a : ℝ) : Set (GaugeField a → ℂ) :=
  {F | Continuous F ∧ IsCylinderFunction F}
def GaugeFieldProbability (a : ℝ) : Type :=
  {ν : Measure (GaugeField a) // IsProbabilityMeasure ν}
def GaugeFieldProbability.expect (ν : GaugeFieldProbability a)
    (F : GaugeField a → ℂ) : ℂ :=
  ∫ U, F U ∂ν.1
instance weakTopology : TopologicalSpace (GaugeFieldProbability a) :=
  ⨅ F : GaugeField a →ᵇ ℂ, TopologicalSpace.induced (fun ν => ν.expect F) inferInstance
end InfiniteLattice
end YangMills.Construction
