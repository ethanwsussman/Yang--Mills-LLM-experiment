import YangMills.Construction.Lattice.ActionOfLatticeIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def minimalPeriodRatio : ℝ := 3
structure PeriodSublattice (a : ℝ) where
  periods : AddSubgroup (LatticePoint a)
  exists_linearIndependent : ∃ v : Fin 4 → LatticePoint a, (∀ i, v i ∈ periods) ∧
    LinearIndependent ℝ fun i => (v i : AmbientSpace)
  le_norm_of_ne_zero : ∀ γ ∈ periods, γ ≠ 0 → minimalPeriodRatio * a ≤ ‖(γ : AmbientSpace)‖
abbrev PositiveLink (a : ℝ) : Type := {b : Link a // b.IsPositivelyOriented}
def PositiveLink.translate (b : PositiveLink a) (γ : LatticePoint a) : PositiveLink a :=
  ⟨⟨b.1.initial + γ, b.1.terminal + γ, by simpa only [add_sub_add_right_eq_sub] using b.1.isAdjacent⟩,
    by simpa only [Link.IsPositivelyOriented, add_sub_add_right_eq_sub] using b.2⟩
instance : Countable (LatticePoint a) :=
  Function.Surjective.countable (f := fun n : Fin 4 → ℤ =>
      (⟨fun μ => (n μ : ℝ) * a, n, fun _ => rfl⟩ : LatticePoint a))
    fun x => by
      obtain ⟨n, hn⟩ := x.2
      exact ⟨n, Subtype.ext (funext fun μ => (hn μ).symm)⟩
instance : Countable (Link a) :=
  Function.Injective.countable (f := fun b : Link a => (b.initial, b.terminal)) fun _ _ h =>
    Link.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
namespace PeriodSublattice
variable (Γ : PeriodSublattice a)
theorem spacing_ne_zero (Γ : PeriodSublattice a) : a ≠ 0 := by
  obtain ⟨v, -, hv⟩ := Γ.exists_linearIndependent
  rintro rfl
  refine hv.ne_zero 0 (funext fun μ => ?_)
  obtain ⟨n, hn⟩ := (v 0).2
  simpa using hn μ
def linkOrbit (b : PositiveLink a) : Set (PositiveLink a) :=
  {b' | ∃ γ ∈ Γ.periods, b' = b.translate γ}
def plaquetteOrbit (p : ElementaryPlaquette a) : Set (ElementaryPlaquette a) :=
  {q | ∃ γ ∈ Γ.periods, q = (shift γ).plaquetteMap p}
abbrev QuotientLink : Type := Set.range Γ.linkOrbit
abbrev QuotientPlaquette : Type := Set.range Γ.plaquetteOrbit
def linkClass (b : PositiveLink a) : Γ.QuotientLink := ⟨Γ.linkOrbit b, b, rfl⟩
instance : Countable Γ.QuotientLink := (Set.countable_range Γ.linkOrbit).to_subtype
abbrev QuotientField : Type := Γ.QuotientLink → Matrices.ComplexMatrix2.specialUnitary
def quotientHaar : Measure Γ.QuotientField := Matrices.ComplexMatrix2.haarPi Γ.QuotientLink
def liftValue (U : Γ.QuotientField) (b : Link a) : Matrices.ComplexMatrix2.specialUnitary :=
  open Classical in
  if h : b.IsPositivelyOriented then U (Γ.linkClass ⟨b, h⟩)
  else if h' : b.opposite.IsPositivelyOriented then (U (Γ.linkClass ⟨b.opposite, h'⟩))⁻¹ else 1
theorem isPositivelyOriented_opposite_of_not {b : Link a} (h : ¬b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h₁ | h₁⟩ := b.isAdjacent
  · exact absurd ⟨μ, h₁⟩ h
  · exact ⟨μ, by
      change b.initial - b.terminal = axisStep a μ
      rw [← neg_sub, h₁, neg_neg]⟩
theorem not_isPositivelyOriented_opposite (Γ : PeriodSublattice a) {b : Link a}
    (h : b.IsPositivelyOriented) : ¬b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h₁⟩ := h
  rintro ⟨ν, h₂⟩
  have h₂' : b.initial - b.terminal = axisStep a ν := h₂
  have hs : axisStep a μ + axisStep a ν = 0 := by
    rw [← h₁, ← h₂']
    abel
  have hμ := congrFun (congrArg Subtype.val hs) μ
  have ha := Γ.spacing_ne_zero
  by_cases hν : μ = ν
  · subst hν
    simp [axisStep] at hμ
    exact ha (by linarith)
  · simp [axisStep, Pi.single_eq_of_ne hν] at hμ
    exact ha hμ
theorem liftValue_opposite (U : Γ.QuotientField) (b : Link a) :
    Γ.liftValue U b.opposite = (Γ.liftValue U b)⁻¹ := by
  unfold liftValue
  by_cases h : b.IsPositivelyOriented
  · have hh : b.opposite.opposite.IsPositivelyOriented := h
    rw [dif_neg (Γ.not_isPositivelyOriented_opposite h), dif_pos hh, dif_pos h]
    rfl
  · have hr := isPositivelyOriented_opposite_of_not h
    rw [dif_pos hr, dif_neg h, dif_pos hr, inv_inv]
def lift (U : Γ.QuotientField) : GaugeField a :=
  ⟨Γ.liftValue U, Γ.liftValue_opposite U⟩
def periodize {E : Type*} (F : GaugeField a → E) (U : Γ.QuotientField) : E :=
  F (Γ.lift U)
theorem quotientPlaquette_nonempty (p : Γ.QuotientPlaquette) :
    (p : Set (ElementaryPlaquette a)).Nonempty := by
  obtain ⟨_, q, rfl⟩ := p
  exact ⟨_, 0, zero_mem _, rfl⟩
def quotientFaceEnergy (U : Γ.QuotientField) (p : Γ.QuotientPlaquette) : ℝ :=
  faceEnergy (Γ.lift U) (Γ.quotientPlaquette_nonempty p).some
def boltzmannWeight (β : ℝ) (U : Γ.QuotientField) : ℝ :=
  Real.exp (-β * ∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p)
def partitionFunction (β : ℝ) : ℝ := ∫ U, Γ.boltzmannWeight β U ∂Γ.quotientHaar
def gibbsMeasure (β : ℝ) : Measure Γ.QuotientField :=
  (ENNReal.ofReal (Γ.partitionFunction β))⁻¹ •
    Γ.quotientHaar.withDensity fun U => ENNReal.ofReal (Γ.boltzmannWeight β U)
def liftedGibbsMeasure (β : ℝ) : Measure (GaugeField a) :=
  (Γ.gibbsMeasure β).map Γ.lift
end PeriodSublattice
end InfiniteLattice
end YangMills.Construction
