import YangMills.Construction.SpectralTheory.EuclideanBorelProjectionValuedMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanSpectral
def IsBoundedMeasurable {Y : Type*} [MeasurableSpace Y] (f : Y → ℂ) : Prop :=
  Measurable f ∧ ∃ c : ℝ, ∀ y, ‖f y‖ ≤ c
def normLeSet {Y : Type*} (f : Y → ℂ) (n : ℕ) : Set Y :=
  {y | ‖f y‖ ≤ n}
def truncate {Y : Type*} (f : Y → ℂ) (n : ℕ) : Y → ℂ :=
  (normLeSet f n).indicator f
namespace SpectralMeasure
variable {Y Y' H : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [TopologicalSpace Y'] [MeasurableSpace Y'] [BorelSpace Y']
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def IsBoundedCalculus (E : SpectralMeasure Y H) (f : Y → ℂ) (T : H →L[ℂ] H) : Prop :=
  ∀ x : H, ⟪x, T x⟫_ℂ = ∫ y, f y ∂E.diagMeasure x
def boundedCalculus (E : SpectralMeasure Y H) (f : Y → ℂ) : H →L[ℂ] H :=
  Classical.epsilon (E.IsBoundedCalculus f)
def pushforward (E : SpectralMeasure Y H) (hY' : IsEuclideanBorel Y') (g : Y → Y')
    (hg : Measurable g) : SpectralMeasure Y' H where
  borelSubset := hY'
  toFun s := E ⟨g ⁻¹' s.1, hg s.2⟩
  selfAdjoint _ := E.selfAdjoint _
  map_univ := E.map_univ
  map_inter s t := E.map_inter ⟨g ⁻¹' s.1, hg s.2⟩ ⟨g ⁻¹' t.1, hg t.2⟩
  countablyAdditive x s hd := by
    have h := E.countablyAdditive x (fun k => ⟨g ⁻¹' (s k).1, hg (s k).2⟩)
      (fun k l hkl => (hd hkl).preimage g)
    have hu : (⟨g ⁻¹' ⋃ k, (s k).1, hg (MeasurableSet.iUnion fun k => (s k).2)⟩ : BorelSubsets Y) =
        ⟨⋃ k, g ⁻¹' (s k).1, MeasurableSet.iUnion fun k => hg (s k).2⟩ :=
      Subtype.ext preimage_iUnion
    simpa only [hu] using h
def calculusDomain (E : SpectralMeasure Y H) (f : Y → ℂ) : Set H :=
  {x | ∫⁻ y, ‖f y‖ₑ ^ 2 ∂E.diagMeasure x < ∞}
def calculusLimit (E : SpectralMeasure Y H) (f : Y → ℂ) (x : H) : H :=
  limUnder atTop fun n : ℕ => E.boundedCalculus (truncate f n) x
def IsCalculusOperator (E : SpectralMeasure Y H) (f : Y → ℂ)
    (T : H →ₗ.[ℂ] H) : Prop :=
  (T.domain : Set H) = E.calculusDomain f ∧ ∀ x : T.domain, T x = E.calculusLimit f x
def calculusOperator (E : SpectralMeasure Y H) (f : Y → ℂ) : H →ₗ.[ℂ] H :=
  Classical.epsilon (E.IsCalculusOperator f)
end SpectralMeasure
namespace FunctionalCalculus
open SpectralMeasure
variable {Y H : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
structure ValuesAndDiagMeasures (E : SpectralMeasure Y H) : Prop where
  isOrthProjection : ∀ s, IsOrthProjection (E s)
  diagMass_eq : ∀ (x : H) (s : BorelSubsets Y), E.diagMass x s = ((‖E s x‖ ^ 2 : ℝ) : ℂ)
  isFiniteMeasure : ∀ x : H, IsFiniteMeasure (E.diagMeasure x)
  real_apply : ∀ (x : H) (s : BorelSubsets Y), (((E.diagMeasure x).real s.1 : ℝ) : ℂ) = E.diagMass x s
  real_univ : ∀ x : H, (E.diagMeasure x).real univ = ‖x‖ ^ 2
  apply_empty : E ⟨∅, MeasurableSet.empty⟩ = 0
  apply_union : ∀ s t : BorelSubsets Y, Disjoint s.1 t.1 →
    E ⟨s.1 ∪ t.1, s.2.union t.2⟩ = E s + E t
  apply_iUnion : ∀ s : ℕ → BorelSubsets Y, (∀ n, E (s n) = 0) →
    E ⟨⋃ n, (s n).1, MeasurableSet.iUnion fun n => (s n).2⟩ = 0
structure BoundedCalculusLaws (E : SpectralMeasure Y H) : Prop where
  existsUnique : ∀ f : Y → ℂ, IsBoundedMeasurable f → ∃! T : H →L[ℂ] H, E.IsBoundedCalculus f T
  isBoundedCalculus : ∀ f : Y → ℂ, IsBoundedMeasurable f →
    E.IsBoundedCalculus f (E.boundedCalculus f)
  add : ∀ f g : Y → ℂ, IsBoundedMeasurable f → IsBoundedMeasurable g →
    E.boundedCalculus (f + g) = E.boundedCalculus f + E.boundedCalculus g
  smul : ∀ (a : ℂ) (f : Y → ℂ), IsBoundedMeasurable f →
    E.boundedCalculus (a • f) = a • E.boundedCalculus f
  mul : ∀ f g : Y → ℂ, IsBoundedMeasurable f → IsBoundedMeasurable g →
    E.boundedCalculus (f * g) = E.boundedCalculus f * E.boundedCalculus g
  isAdjointPair : ∀ f : Y → ℂ, IsBoundedMeasurable f →
    IsAdjointPair (E.boundedCalculus f) (E.boundedCalculus fun y => (starRingEnd ℂ) (f y))
  indicator : ∀ s : BorelSubsets Y, E.boundedCalculus (s.1.indicator 1) = E s
  norm_sq : ∀ f : Y → ℂ, IsBoundedMeasurable f → ∀ x : H,
    ‖E.boundedCalculus f x‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 ∂E.diagMeasure x
  integral_le : ∀ f : Y → ℂ, IsBoundedMeasurable f → ∀ x : H,
    ∫ y, ‖f y‖ ^ 2 ∂E.diagMeasure x ≤ (⨆ y, ‖f y‖) ^ 2 * ‖x‖ ^ 2
  diagMeasure_real_apply : ∀ f : Y → ℂ, IsBoundedMeasurable f → ∀ (x : H) (s : BorelSubsets Y),
    (E.diagMeasure (E.boundedCalculus f x)).real s.1 =
      ∫ y in s.1, ‖f y‖ ^ 2 ∂E.diagMeasure x
def DominatedStrongConvergence (E : SpectralMeasure Y H) : Prop :=
  ∀ (f : ℕ → Y → ℂ) (g : Y → ℂ) (c : ℝ), (∀ n, Measurable (f n)) → (∀ n y, ‖f n y‖ ≤ c) →
    (∀ y, Tendsto (fun n => f n y) atTop (𝓝 (g y))) →
      TendstoStrongly atTop (fun n => E.boundedCalculus (f n)) (E.boundedCalculus g)
structure RealBoundedCalculus (E : SpectralMeasure Y H) : Prop where
  isSelfAdjoint : ∀ f : Y → ℝ, Measurable f → (∃ c : ℝ, ∀ y, |f y| ≤ c) →
    IsSelfAdjointOp (E.boundedCalculus fun y => (f y : ℂ))
  apply_neg_eq_zero : ∀ (f : Y → ℝ) (hf : Measurable f), (∃ c : ℝ, ∀ y, |f y| ≤ c) →
    OpGe (E.boundedCalculus fun y => (f y : ℂ)) (scalarOp 0) →
      E ⟨{y | f y < 0}, measurableSet_lt hf measurable_const⟩ = 0
def PushforwardDiagMeasures (E : SpectralMeasure Y H) : Prop :=
  ∀ (Y' : Type) [TopologicalSpace Y'] [MeasurableSpace Y'] [BorelSpace Y']
    (hY' : IsEuclideanBorel Y') (g : Y → Y') (hg : Measurable g) (x : H),
    (E.pushforward hY' g hg).diagMeasure x = (E.diagMeasure x).map g
structure UnboundedCalculusLaws (E : SpectralMeasure Y H) : Prop where
  dense : ∀ f : Y → ℂ, Measurable f → Dense (E.calculusDomain f)
  isCalculusOperator : ∀ f : Y → ℂ, Measurable f →
    E.IsCalculusOperator f (E.calculusOperator f)
  tendsto : ∀ f : Y → ℂ, Measurable f → ∀ x ∈ E.calculusDomain f,
    Tendsto (fun n : ℕ => E.boundedCalculus (truncate f n) x) atTop (𝓝 (E.calculusLimit f x))
  norm_sq : ∀ f : Y → ℂ, Measurable f → ∀ x ∈ E.calculusDomain f,
    ‖E.calculusLimit f x‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 ∂E.diagMeasure x
  inner_eq : ∀ f : Y → ℂ, Measurable f → ∀ x ∈ E.calculusDomain f,
    ⟪x, E.calculusLimit f x⟫_ℂ = ∫ y, f y ∂E.diagMeasure x
  of_bounded : ∀ f : Y → ℂ, IsBoundedMeasurable f →
    (E.calculusOperator f).domain = ⊤ ∧
      ∀ x : (E.calculusOperator f).domain, E.calculusOperator f x = E.boundedCalculus f x
  mem_calculusDomain_add : ∀ f g : Y → ℂ, Measurable f → Measurable g → ∀ (a b : ℂ),
    ∀ x ∈ E.calculusDomain f ∩ E.calculusDomain g, x ∈ E.calculusDomain (a • f + b • g)
  calculusLimit_add : ∀ f g : Y → ℂ, Measurable f → Measurable g → ∀ (a b : ℂ),
    ∀ x ∈ E.calculusDomain f ∩ E.calculusDomain g,
      E.calculusLimit (a • f + b • g) x = a • E.calculusLimit f x + b • E.calculusLimit g x
  isSelfAdjoint : ∀ f : Y → ℝ, Measurable f →
    IsSelfAdjointPartial (E.calculusOperator fun y => (f y : ℂ))
  pushforward : ∀ (Y' : Type) [TopologicalSpace Y'] [MeasurableSpace Y'] [BorelSpace Y']
    (hY' : IsEuclideanBorel Y') (g : Y → Y') (hg : Measurable g) (f : Y' → ℂ),
    Measurable f → (E.pushforward hY' g hg).calculusOperator f = E.calculusOperator (f ∘ g)
structure SupportLaws (E : SpectralMeasure Y H) : Prop where
  isCarriedBy_supp : E.IsCarriedBy ⟨E.supp, E.isClosed_supp.measurableSet⟩
  supp_subset_iff : ∀ (C : Set Y) (hC : IsClosed C),
    E.supp ⊆ C ↔ E.IsCarriedBy ⟨C, hC.measurableSet⟩
def FunctionalCalculusHolds : Prop :=
  ∀ (Y H : Type) [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : SpectralMeasure Y H),
    ValuesAndDiagMeasures E ∧ BoundedCalculusLaws E ∧ DominatedStrongConvergence E ∧
      RealBoundedCalculus E ∧ PushforwardDiagMeasures E ∧ UnboundedCalculusLaws E ∧ SupportLaws E
end FunctionalCalculus
end YangMills.Construction.EuclideanSpectral
