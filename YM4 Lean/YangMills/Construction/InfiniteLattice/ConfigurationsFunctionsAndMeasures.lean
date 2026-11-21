import YangMills.Construction.InfiniteLattice.PositiveLinksAndCylinderFunctions
import YangMills.Construction.Lattice.ImagesOfBondsAndPlaquettesUnderLatticeIsometries
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter YangMills.Construction.InfiniteLattice
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction
namespace GibbsAtFixedSpacing
variable {a : ℝ}
def linfNorm (x : AmbientSpace) : ℝ := Finset.univ.sup' Finset.univ_nonempty fun μ => |x μ|
def HasNoOppositePairs (S : Set (Link a)) : Prop := ∀ e ∈ S, e.opposite ∉ S
instance instCountableLatticePoint : Countable (LatticePoint a) :=
  Function.Surjective.countable (f := fun n : Fin 4 → ℤ =>
    (⟨fun μ => (n μ : ℝ) * a, n, fun _ => rfl⟩ : LatticePoint a))
    (by
      rintro ⟨x, n, hn⟩
      exact ⟨n, Subtype.ext (funext fun μ => (hn μ).symm)⟩)
instance instCountableLink : Countable (Link a) :=
  Function.Injective.countable (f := fun e : Link a => (e.initial, e.terminal))
    (fun _ _ h => Link.ext (Prod.ext_iff.mp h).1 (Prod.ext_iff.mp h).2)
open Classical in
def overwriteLinks {S : Set (Link a)} (hS : HasNoOppositePairs S)
    (V : LinkVariables S) (U : GaugeField a) : GaugeField a :=
  ⟨fun e => if he : e ∈ S then V ⟨e, he⟩
    else if ho : e.opposite ∈ S then (V ⟨e.opposite, ho⟩)⁻¹ else U e, by
    intro e
    by_cases he : e ∈ S
    · have ho : e.opposite.opposite ∈ S := he
      simp only [dif_pos he, dif_neg (hS e he), dif_pos ho]
      rfl
    · by_cases ho : e.opposite ∈ S
      · simp only [dif_neg he, dif_pos ho, inv_inv]
      · have hoo : e.opposite.opposite ∉ S := he
        simp only [dif_neg he, dif_neg ho, dif_neg hoo]
        exact U.2 e⟩
def boundedMeasurableIn (a : ℝ) (R : Set AmbientSpace) : Set (GaugeField a → ℂ) :=
  {F | Measurable[regionSigma R] F ∧ ∃ C : ℝ, ∀ U, ‖F U‖ ≤ C}
def locallyMeasurableIn (a : ℝ) (R : Set AmbientSpace) : Set (GaugeField a → ℂ) :=
  ⋃ Q ∈ {Q : Set AmbientSpace | Bornology.IsBounded Q}, boundedMeasurableIn a (R ∩ Q)
def continuousFns (a : ℝ) : Set (GaugeField a → ℂ) := {F | Continuous F}
def continuousLocal (a : ℝ) : Set (GaugeField a → ℂ) :=
  {F | Continuous F ∧ IsBoundedObservable F ∧ IsLocalObservable F}
section Dependence
variable {E : Type*}
def IsIndependentOfLinks {S : Set (Link a)} (hS : HasNoOppositePairs S)
    (F : GaugeField a → E) : Prop :=
  ∀ (V : LinkVariables S) (U : GaugeField a), F (overwriteLinks hS V U) = F U
theorem opposite_ne_self (ha : 0 < a) (e : Link a) : e.opposite ≠ e := by
  intro h
  have hend : e.terminal = e.initial := congrArg Link.initial h
  obtain ⟨μ, hμ | hμ⟩ := e.isAdjacent
  all_goals
    rw [hend, sub_self] at hμ
    have hv := congrFun (congrArg Subtype.val hμ) μ
    simp [axisStep] at hv
    linarith
theorem hasNoOppositePairs_singleton (ha : 0 < a) (e : Link a) :
    HasNoOppositePairs ({e} : Set (Link a)) := by
  intro f hf ho
  rw [mem_singleton_iff] at hf ho
  subst hf
  exact opposite_ne_self ha f ho
def DependsOnLink (ha : 0 < a) (F : GaugeField a → E) (e : Link a) : Prop :=
  ¬ IsIndependentOfLinks (hasNoOppositePairs_singleton ha e) F
def linkSupport (ha : 0 < a) (F : GaugeField a → E) : Set (Link a) :=
  {e | e ∈ positiveLinkSet a ∧ DependsOnLink ha F e}
theorem overwriteLinks_opposite (ha : 0 < a) (e : Link a)
    (V : LinkVariables ({e.opposite} : Set (Link a))) (U : GaugeField a) :
    overwriteLinks (hasNoOppositePairs_singleton ha e.opposite) V U =
      overwriteLinks (hasNoOppositePairs_singleton ha e) (fun _ => (V ⟨e.opposite, rfl⟩)⁻¹) U := by
  apply Subtype.ext
  funext f
  have hne : e.opposite ≠ e := opposite_ne_self ha e
  by_cases hfe : f = e
  · subst hfe
    have h1 : f ∉ ({f.opposite} : Set (Link a)) := fun h => hne h.symm
    have h2 : f.opposite ∈ ({f.opposite} : Set (Link a)) := rfl
    have h3 : f ∈ ({f} : Set (Link a)) := rfl
    simp only [overwriteLinks, dif_neg h1, dif_pos h2, dif_pos h3]
  · by_cases hfo : f = e.opposite
    · subst hfo
      have h1 : e.opposite ∈ ({e.opposite} : Set (Link a)) := rfl
      have h2 : e.opposite ∉ ({e} : Set (Link a)) := hne
      have h3 : e.opposite.opposite ∈ ({e} : Set (Link a)) := rfl
      simp only [overwriteLinks, dif_pos h1, dif_neg h2, dif_pos h3, inv_inv]
    · have h1 : f ∉ ({e.opposite} : Set (Link a)) := hfo
      have h2 : f ∉ ({e} : Set (Link a)) := hfe
      have h3 : f.opposite ∉ ({e.opposite} : Set (Link a)) :=
        fun h => hfe (congrArg Link.opposite h)
      have h4 : f.opposite ∉ ({e} : Set (Link a)) := fun h => hfo (congrArg Link.opposite h)
      simp only [overwriteLinks, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4]
theorem DependsOnLink.opposite (ha : 0 < a) {F : GaugeField a → E} {e : Link a}
    (h : DependsOnLink ha F e) : DependsOnLink ha F e.opposite := by
  intro hn
  exact h fun V U =>
    (congrArg F (overwriteLinks_opposite ha e.opposite V U)).trans (hn _ U)
end Dependence
def BorelProb (a : ℝ) : Type := GaugeFieldProbability a
namespace BorelProb
def integral (ν : BorelProb a) (F : GaugeField a → ℂ) : ℂ := GaugeFieldProbability.expect ν F
instance instTopologicalSpace : TopologicalSpace (BorelProb a) :=
  ⨅ F : continuousFns a,
    TopologicalSpace.induced (fun ν : BorelProb a => ν.integral F.1) inferInstance
def TendstoWeak (ν : ℕ → BorelProb a) (μ : BorelProb a) : Prop :=
  ∀ F : GaugeField a → ℂ, Continuous F →
    Tendsto (fun i => (ν i).integral F) atTop (𝓝 (μ.integral F))
def IsSubseqWeakLimit (ν : ℕ → BorelProb a) (μ : BorelProb a) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, 1 ≤ φ k) ∧ TendstoWeak (ν ∘ φ) μ
end BorelProb
section MeanSquare
variable {Ω : Type*} [MeasurableSpace Ω]
def IsSqIntegrable (ν : Measure Ω) [IsProbabilityMeasure ν] (H : Ω → ℂ) : Prop :=
  Measurable H ∧ ∫⁻ ω, ‖H ω‖ₑ ^ 2 ∂ν < ∞
def TendstoInL2 (ν : Measure Ω) [IsProbabilityMeasure ν] (H : ℕ → Ω → ℂ)
    (H' : Ω → ℂ) : Prop :=
  Measurable H' ∧ (∀ k, 1 ≤ k → Measurable (H k)) ∧
    Tendsto (fun k => ∫⁻ ω, ‖H' ω - H k ω‖ₑ ^ 2 ∂ν) atTop (𝓝 0)
end MeanSquare
def edgesOf (p : ElementaryPlaquette a) : Set (Link a) :=
  {e | e ∈ positiveLinkSet a ∧ e.initial ∈ p.cornerSet ∧ e.terminal ∈ p.cornerSet}
structure BoundaryCycle (p : ElementaryPlaquette a) where
  v₁ : LatticePoint a
  v₂ : LatticePoint a
  v₃ : LatticePoint a
  v₄ : LatticePoint a
  corners_eq : ({v₁, v₂, v₃, v₄} : Set (LatticePoint a)) = p.cornerSet
  adj₁₂ : ∃ μ : Fin 4, v₂ - v₁ = axisStep a μ ∨ v₂ - v₁ = -axisStep a μ
  adj₂₃ : ∃ μ : Fin 4, v₃ - v₂ = axisStep a μ ∨ v₃ - v₂ = -axisStep a μ
  adj₃₄ : ∃ μ : Fin 4, v₄ - v₃ = axisStep a μ ∨ v₄ - v₃ = -axisStep a μ
  adj₄₁ : ∃ μ : Fin 4, v₁ - v₄ = axisStep a μ ∨ v₁ - v₄ = -axisStep a μ
def BoundaryCycle.holonomy {p : ElementaryPlaquette a} (c : BoundaryCycle p) (U : GaugeField a) :
    Matrices.ComplexMatrix2.specialUnitary :=
  U ⟨c.v₁, c.v₂, c.adj₁₂⟩ * U ⟨c.v₂, c.v₃, c.adj₂₃⟩ * U ⟨c.v₃, c.v₄, c.adj₃₄⟩ *
    U ⟨c.v₄, c.v₁, c.adj₄₁⟩
end GibbsAtFixedSpacing
end YangMills.Construction
end
