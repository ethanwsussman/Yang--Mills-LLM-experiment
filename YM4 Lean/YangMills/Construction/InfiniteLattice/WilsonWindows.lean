import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
theorem Link.opposite_not_isPositivelyOriented (ha : 0 < a) {b : Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := hb
  rintro ⟨ν, hν⟩
  have hsum : axisStep a μ + axisStep a ν = 0 := by
    rw [← hμ, ← hν]
    change b.terminal - b.initial + (b.initial - b.terminal) = 0
    abel
  have hcoord := congrFun (congrArg Subtype.val hsum) μ
  have hstep : ∀ κ, ((axisStep a κ : LatticePoint a) : AmbientSpace) μ = if μ = κ then a else 0 :=
    fun κ => by
      by_cases h : μ = κ
      · subst h; simp [axisStep]
      · simp [axisStep, h]
  have hcoord' : ((axisStep a μ : LatticePoint a) : AmbientSpace) μ +
      ((axisStep a ν : LatticePoint a) : AmbientSpace) μ = 0 := hcoord
  rw [hstep μ, hstep ν] at hcoord'
  by_cases h : μ = ν
  · simp only [if_true, h] at hcoord'
    linarith
  · simp only [if_true, if_neg h] at hcoord'
    linarith
structure LinkWindow (a : ℝ) where
  links : Finset (Link a)
  isPositive : ∀ b ∈ links, b.IsPositivelyOriented
namespace LinkWindow
variable (W : LinkWindow a)
def faces : Set (ElementaryPlaquette a) := facesTouching W.links
def faceCount : ℕ := W.faces.ncard
def rim : Set (Link a) := {b | (∃ p ∈ W.faces, b ∈ p.edges) ∧ b ∉ W.links}
abbrev Assignments : Type := W.links → Matrices.ComplexMatrix2.specialUnitary
def haarProd : Measure W.Assignments := Matrices.ComplexMatrix2.haarPi W.links
def restrictInside (U : GaugeField a) : W.Assignments := restrictTo W.links U
def restrictRim (U : GaugeField a) : W.rim → Matrices.ComplexMatrix2.specialUnitary :=
  fun b => U b
def glue (ha : 0 < a) (V : W.Assignments) (U : GaugeField a) : GaugeField a :=
  open Classical in
  ⟨fun b => if h : b ∈ W.links then V ⟨b, h⟩ else
      if h' : b.opposite ∈ W.links then (V ⟨b.opposite, h'⟩)⁻¹ else U b, fun b => by
    by_cases h : b ∈ W.links
    · have h' : b.opposite ∉ W.links := fun h' =>
        Link.opposite_not_isPositivelyOriented ha (W.isPositive b h) (W.isPositive _ h')
      simp only [h, h', dite_true, dite_false]
      exact dif_pos h
    · by_cases h' : b.opposite ∈ W.links
      · simp only [h, h', dite_true, dite_false, inv_inv]
      · have h'' : b.opposite.opposite ∉ W.links := h
        simp only [h, h', h'', dite_false]
        exact U.2 b⟩
def boltzmannWeight (ha : 0 < a) (β : ℝ) (V : W.Assignments) (U : GaugeField a) : ℝ :=
  Real.exp (-β * ∑ᶠ p ∈ W.faces, faceEnergy (W.glue ha V U) p)
def densityKernel (ha : 0 < a) (β : ℝ) (V : W.Assignments) (U : GaugeField a) : ℝ :=
  W.boltzmannWeight ha β V U / ∫ V', W.boltzmannWeight ha β V' U ∂W.haarProd
def wilsonKernel (ha : 0 < a) (β : ℝ) (F : GaugeField a → ℂ) (U : GaugeField a) : ℂ :=
  ∫ V, F (W.glue ha V U) * (W.densityKernel ha β V U : ℂ) ∂W.haarProd
@[reducible] def exteriorSigma : MeasurableSpace (GaugeField a) :=
  linkSigma {b | b.IsPositivelyOriented ∧ b ∉ W.links}
end LinkWindow
end InfiniteLattice
end YangMills.Construction
end
