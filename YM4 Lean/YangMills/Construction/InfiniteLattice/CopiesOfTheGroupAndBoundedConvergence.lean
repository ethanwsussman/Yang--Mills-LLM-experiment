import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def groupDist (g h : Matrices.ComplexMatrix2.specialUnitary) : ℝ :=
  Matrices.ComplexMatrix2.operatorNorm ((g : Matrices.ComplexMatrix2) - (h : Matrices.ComplexMatrix2))
theorem nhds_basis_groupDist (g : Matrices.ComplexMatrix2.specialUnitary) :
    (𝓝 g).HasBasis (fun ε : ℝ => 0 < ε) fun ε => {h | groupDist g h < ε} := by
  open scoped Matrix.Norms.L2Operator in
  have hb := Metric.nhds_basis_ball (x := g)
  convert hb using 2 with ε
  ext k
  simp only [mem_ofPred_eq, Metric.mem_ball, groupDist, Matrices.ComplexMatrix2.operatorNorm,
    Subtype.dist_eq, dist_eq_norm]
  rw [norm_sub_rev]
def setIndicator {X : Type*} (E : Set X) : X → ℂ := E.indicator 1
def IsAtMostCountable (J : Type) : Prop := Finite J ∨ Nonempty (J ≃ ℕ)
theorem isAtMostCountable_iff_countable (J : Type) : IsAtMostCountable J ↔ Countable J := by
  constructor
  · rintro (hJ | hJ)
    · exact Finite.to_countable
    · obtain ⟨e⟩ := hJ
      exact e.injective.countable
  · intro hJ
    rcases finite_or_infinite J with hf | hi
    · exact Or.inl hf
    · obtain ⟨d⟩ := nonempty_denumerable J
      exact Or.inr ⟨Denumerable.eqv J⟩
def restrictFamily {J : Type} (J' : Set J) (g : LinkVariables J) : LinkVariables J' := fun j => g j
def DependsOnlyOnCoords {J : Type} {Y : Type*} (J' : Set J) (F : LinkVariables J → Y) : Prop :=
  ∀ g h : LinkVariables J, restrictFamily J' g = restrictFamily J' h → F g = F h
theorem haarMeasure_eq_pi (J : Type) [Fintype J] :
    LinkVariables.haarMeasure J = Measure.pi fun _ : J => Matrices.ComplexMatrix2.haarProb :=
  Measure.infinitePi_eq_pi _
section BoundedConvergence
variable (X : Type*) [TopologicalSpace X]
def boundedBorelSpace : Submodule ℂ (X → ℂ) where
  carrier := {F | Measurable[borel X] F ∧ ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C}
  add_mem' := by
    rintro F F' ⟨hF, C, hC⟩ ⟨hF', C', hC'⟩
    let _ : MeasurableSpace X := borel X
    exact ⟨hF.add hF', C + C', fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hC' x))⟩
  zero_mem' := by
    let _ : MeasurableSpace X := borel X
    exact ⟨measurable_const, 0, fun x => by simp⟩
  smul_mem' := by
    rintro c F ⟨hF, C, hC⟩
    let _ : MeasurableSpace X := borel X
    refine ⟨hF.const_smul c, ‖c‖ * C, fun x => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)
variable {X}
def boundedSupValue (F : X → ℂ) : ℝ := ⨆ x, ‖F x‖
theorem setIndicator_mem_boundedBorelSpace {E : Set X} (hE : MeasurableSet[borel X] E) :
    setIndicator E ∈ boundedBorelSpace X := by
  let _ : MeasurableSpace X := borel X
  refine ⟨measurable_one.indicator hE, 1, fun x => ?_⟩
  by_cases hx : x ∈ E <;> simp [setIndicator, hx]
end BoundedConvergence
def IsInterClosed {X : Type*} (𝓔 : Set (Set X)) : Prop :=
  ∀ A ∈ 𝓔, ∀ B ∈ 𝓔, A ∩ B ∈ 𝓔
end InfiniteLattice
end YangMills.Construction
