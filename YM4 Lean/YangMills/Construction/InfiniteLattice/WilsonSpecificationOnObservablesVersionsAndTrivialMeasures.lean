import YangMills.Construction.InfiniteLattice.CopiesOfTheGroupAndBoundedConvergence
import YangMills.Construction.InfiniteLattice.LinksAndTheReplacementOfAConfigurationOnAFiniteSet
import YangMills.Construction.InfiniteLattice.WilsonKernelOnObservables
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open GibbsAtFixedSpacing
namespace InfiniteLattice
variable {a : ℝ}
theorem hasNoOppositePairs_of_subset_positiveLinks (ha : 0 < a) {𝓛 : Finset (Link a)}
    (h𝓛 : (𝓛 : Set (Link a)) ⊆ positiveLinkSet a) :
    HasNoOppositePairs (𝓛 : Set (Link a)) :=
  fun _ hl hr => opposite_notMem_positiveLinks ha (h𝓛 hl) (h𝓛 hr)
def observableOfLinks (𝓛 : Finset (Link a)) (φ : LinkVariables (𝓛 : Set (Link a)) → ℂ) :
    GaugeField a → ℂ :=
  fun U => φ (restrictField U (𝓛 : Set (Link a)))
def observableOfComplement (𝓛 : Finset (Link a)) (f : ComplementVariables 𝓛 → ℂ) :
    GaugeField a → ℂ :=
  fun U => f (complementValues 𝓛 U)
theorem continuous_restrictField (S : Set (Link a)) :
    Continuous fun U : GaugeField a => restrictField U S :=
  continuous_pi fun l => (continuous_apply (l : Link a)).comp
    (continuous_subtype_val (p := fun U : Link a → Matrices.ComplexMatrix2.specialUnitary =>
      ∀ l, U l.opposite = (U l)⁻¹))
theorem isBoundedObservable_comp {Y : Type*} [TopologicalSpace Y] {f : GaugeField a → Y}
    (hf : Continuous f) {φ : Y → ℂ} (hφ : φ ∈ boundedBorelSpace Y) :
    IsBoundedObservable fun U => φ (f U) := by
  obtain ⟨hm, C, hC⟩ := hφ
  let _ : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  exact ⟨hm.comp hf.measurable, C, fun U => hC _⟩
theorem isBoundedObservable_observableOfLinks (𝓛 : Finset (Link a))
    {φ : LinkVariables (𝓛 : Set (Link a)) → ℂ}
    (hφ : φ ∈ boundedBorelSpace (LinkVariables (𝓛 : Set (Link a)))) :
    IsBoundedObservable (observableOfLinks 𝓛 φ) :=
  isBoundedObservable_comp (continuous_restrictField _) hφ
theorem isBoundedObservable_observableOfComplement (𝓛 : Finset (Link a))
    {f : ComplementVariables 𝓛 → ℂ}
    (hf : f ∈ boundedBorelSpace (ComplementVariables 𝓛)) :
    IsBoundedObservable (observableOfComplement 𝓛 f) :=
  isBoundedObservable_comp (continuous_restrictField _) hf
def IsCondExpRepresentative (ν : Measure (GaugeField a))
    (𝓕 : MeasurableSpace (GaugeField a)) (F F' : GaugeField a → ℂ) : Prop :=
  IsBoundedObservable F' ∧ Measurable[𝓕] F' ∧
    ∀ H : GaugeField a → ℂ, IsBoundedObservable H → Measurable[𝓕] H →
      ∫ U, F' U * H U ∂ν = ∫ U, F U * H U ∂ν
theorem wilsonSpecification_eq_of_complementValues_eq (β : ℝ) {𝓛 : Finset (Link a)}
    {U U' : GaugeField a} (h : complementValues 𝓛 U = complementValues 𝓛 U') :
    wilsonSpecification β 𝓛 U = wilsonSpecification β 𝓛 U' := by
  have hw : boltzmannWeight β 𝓛 U = boltzmannWeight β 𝓛 U' := by
    funext v
    have hp : ∀ p : ElementaryPlaquette a, faceEnergy (patch 𝓛 v U) p =
        faceEnergy (patch 𝓛 v U') p := fun p =>
      WilsonOperator.faceEnergy_congr p fun l hl => by
        classical
        by_cases hl' : l ∈ 𝓛
        · simp only [patch, dif_pos hl']
        · simp only [patch, dif_neg hl']
          exact congrFun h ⟨l, WilsonOperator.mem_positiveLinks_of_mem_edgeList p hl, hl'⟩
    simp only [boltzmannWeight, hp]
  unfold wilsonSpecification partitionFunction
  rw [hw]
def wilsonSpecificationAt (ha : 0 < a) (β : ℝ) (𝓛 : Finset (Link a)) (Y : ComplementVariables 𝓛) :
    Measure (𝓛 → Matrices.ComplexMatrix2.specialUnitary) :=
  wilsonSpecification β 𝓛 (gluedField ha sdiff_subset Y (trivialField a))
theorem wilsonSpecificationAt_complementValues (ha : 0 < a) (β : ℝ) (𝓛 : Finset (Link a))
    (U : GaugeField a) :
    wilsonSpecificationAt ha β 𝓛 (complementValues 𝓛 U) = wilsonSpecification β 𝓛 U :=
  wilsonSpecification_eq_of_complementValues_eq β (funext fun l =>
    gluedField_apply_of_mem ha sdiff_subset (complementValues 𝓛 U) (trivialField a) l)
end InfiniteLattice
end YangMills.Construction
