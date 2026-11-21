import YangMills.Construction.InfiniteLattice.WilsonWindows
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
def positiveLinks (a : ℝ) : Set (Link a) := {b | b.IsPositivelyOriented}
def Link.orientedRepresentative (b : Link a) : Link a :=
  open Classical in if b.IsPositivelyOriented then b else b.opposite
instance instCountablePositiveLinks : Countable (positiveLinks a) := by
  have hs : Countable (LatticePoint a) :=
    Function.Surjective.countable
      (f := fun n : Fin 4 → ℤ => (⟨fun μ => (n μ : ℝ) * a, n, fun _ => rfl⟩ : LatticePoint a)) fun x => by
        obtain ⟨n, hn⟩ := x.2
        exact ⟨n, Subtype.ext (funext fun μ => (hn μ).symm)⟩
  exact Function.Injective.countable (f := fun b : positiveLinks a => (b.1.initial, b.1.terminal))
    fun b b' h => Subtype.ext (Link.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
def restrictToPositive (U : GaugeField a) : positiveLinks a → Matrices.ComplexMatrix2.specialUnitary :=
  fun b => U b.1
def extendFromPositive (g : positiveLinks a → Matrices.ComplexMatrix2.specialUnitary) (b : Link a) :
    Matrices.ComplexMatrix2.specialUnitary :=
  open Classical in
  if h : b ∈ positiveLinks a then g ⟨b, h⟩ else
    if h' : b.opposite ∈ positiveLinks a then (g ⟨b.opposite, h'⟩)⁻¹ else 1
def gaugeFieldOfPositive (ha : 0 < a) (g : positiveLinks a → Matrices.ComplexMatrix2.specialUnitary) :
    GaugeField a :=
  ⟨extendFromPositive g, fun b => by
    simp only [extendFromPositive]
    by_cases h : b ∈ positiveLinks a
    · have h' : b.opposite ∉ positiveLinks a := Link.opposite_not_isPositivelyOriented ha h
      have h'' : b.opposite.opposite ∈ positiveLinks a := h
      rw [dif_neg h', dif_pos h'', dif_pos h]
      rfl
    · by_cases h' : b.opposite ∈ positiveLinks a
      · rw [dif_pos h', dif_neg h, dif_pos h', inv_inv]
      · have h'' : b.opposite.opposite ∉ positiveLinks a := h
        rw [dif_neg h', dif_neg h'', dif_neg h, dif_neg h', inv_one]⟩
def gaugeFieldHaarMeasure (ha : 0 < a) : Measure (GaugeField a) :=
  (Matrices.ComplexMatrix2.haarPi (positiveLinks a)).map (gaugeFieldOfPositive ha)
def IsLinkSet (𝓜 : Set (Link a)) : Prop := 𝓜 ⊆ positiveLinks a
def LinksLieIn (𝓜 : Set (Link a)) (S : Set AmbientSpace) : Prop :=
  ∀ b ∈ 𝓜, (b.initial : AmbientSpace) ∈ S ∧ (b.terminal : AmbientSpace) ∈ S
def LatticeSymmetry.linkImage (s : LatticeSymmetry a) (𝓜 : Set (Link a)) : Set (Link a) :=
  (fun b => (s.linkMap b).orientedRepresentative) '' 𝓜
def shiftLinks (𝓜 : Set (Link a)) (v : LatticePoint a) : Set (Link a) :=
  (shift v).linkImage 𝓜
def ElementaryPlaquette.linkSet (p : ElementaryPlaquette a) : Set (Link a) := {b | b ∈ p.edges}
def facesMeeting (𝓛 : Set (Link a)) : Set (ElementaryPlaquette a) :=
  {p | ∃ b ∈ p.linkSet, b ∈ 𝓛}
namespace LinkWindow
variable (W : LinkWindow a)
def localWeight (β : ℝ) (U : GaugeField a) : ℝ :=
  Real.exp (-β * ∑ᶠ p ∈ facesMeeting (W.links : Set (Link a)), faceEnergy U p)
def conditionalExpectation (ha : 0 < a) (β : ℝ) (F : GaugeField a → ℂ) (U : GaugeField a) : ℂ :=
  (∫ V, F (W.glue ha V U) * (W.localWeight β (W.glue ha V U) : ℂ) ∂W.haarProd) /
    ((∫ V, W.localWeight β (W.glue ha V U) ∂W.haarProd : ℝ) : ℂ)
end LinkWindow
def continuousLocalFunctions (a : ℝ) : Set (GaugeField a → ℂ) :=
  {F | IsBoundedObservable F ∧ IsLocalObservable F ∧ Continuous F}
def DependsOnlyOn (𝓜 : Set (Link a)) (F : GaugeField a → ℂ) : Prop :=
  ∀ U U' : GaugeField a, (∀ b ∈ 𝓜, U b = U' b) → F U = F U'
def observableSupport (F : GaugeField a → ℂ) : Set (Link a) :=
  ⋂₀ {𝓜 | IsLinkSet 𝓜 ∧ 𝓜.Finite ∧ DependsOnlyOn 𝓜 F}
structure GaugeTransform (a : ℝ) where
  toFun : LatticePoint a → Matrices.ComplexMatrix2.specialUnitary
  finite_ne_one : {x | toFun x ≠ 1}.Finite
namespace GaugeTransform
def act (h : GaugeTransform a) (U : GaugeField a) : GaugeField a :=
  ⟨fun b => h.toFun b.initial * U b * (h.toFun b.terminal)⁻¹, fun b => by
    change h.toFun b.terminal * U b.opposite * (h.toFun b.initial)⁻¹ =
      (h.toFun b.initial * U b * (h.toFun b.terminal)⁻¹)⁻¹
    rw [U.2 b]
    simp only [mul_inv_rev, inv_inv, mul_assoc]⟩
def pullback {E : Type*} (h : GaugeTransform a) (F : GaugeField a → E) : GaugeField a → E :=
  fun U => F (h.act U)
instance : Mul (GaugeTransform a) where
  mul h h' :=
    ⟨fun x => h.toFun x * h'.toFun x, (h.finite_ne_one.union h'.finite_ne_one).subset fun x hx => by
      have hx' : h.toFun x * h'.toFun x ≠ 1 := hx
      by_cases h₁ : h.toFun x = 1
      · by_cases h₂ : h'.toFun x = 1
        · exact (hx' (by rw [h₁, h₂, one_mul])).elim
        · exact Set.mem_union_right _ (show x ∈ {x | h'.toFun x ≠ 1} from h₂)
      · exact Set.mem_union_left _ (show x ∈ {x | h.toFun x ≠ 1} from h₁)⟩
end GaugeTransform
def IsGaugeInvariantFunction (F : GaugeField a → ℂ) : Prop :=
  ∀ h : GaugeTransform a, h.pullback F = F
def gibbsClass (ha : 0 < a) (β : ℝ) : Set (Measure (GaugeField a)) :=
  {ν | IsProbabilityMeasure ν ∧ ∀ W : LinkWindow a, ∀ F ∈ continuousLocalFunctions a,
    ∫ U, W.conditionalExpectation ha β F U ∂ν = ∫ U, F U ∂ν}
def subgroupInvariantGibbsClass (ha : 0 < a) (β : ℝ) (Q : AddSubgroup (LatticePoint a)) :
    Set (Measure (GaugeField a)) :=
  {ν | ν ∈ gibbsClass ha β ∧ ∀ v ∈ Q, IsSymmetricUnder ν (shift v)}
def periodicGibbsClass (ha : 0 < a) (β : ℝ) : Set (Measure (GaugeField a)) :=
  ⋃ (Q : AddSubgroup (LatticePoint a)) (_ : Q.FiniteIndex), subgroupInvariantGibbsClass ha β Q
@[reducible] def probabilityMeasuresWeakTopology (a : ℝ) :
    TopologicalSpace (ProbabilityMeasure (GaugeField a)) :=
  ⨅ F : C(GaugeField a, ℂ), TopologicalSpace.induced
    (fun ν : ProbabilityMeasure (GaugeField a) => ∫ U, F U ∂(ν : Measure (GaugeField a)))
    inferInstance
end InfiniteLattice
end YangMills.Construction
