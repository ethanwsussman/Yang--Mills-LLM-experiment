import YangMills.Construction.InfiniteLattice.PeriodicExtensionsAndTheirWeakLimitPoints
import YangMills.Construction.InfiniteLattice.WindowDensitiesAndStandardWindows
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
open PeriodicExtensions
namespace LinkWindow
section Kernel
variable {a : ℝ} (W : LinkWindow a)
theorem rim_subset_positiveLinks : W.rim ⊆ positiveLinkSet a := by
  rintro e ⟨⟨q, -, he⟩, -⟩
  simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
def fieldOfRimValues (ha : 0 < a) (ξ : LinkVariables W.rim) : GaugeField a :=
  gluedField ha W.rim_subset_positiveLinks ξ (trivialField a)
def rimKernel (ha : 0 < a) (β : ℝ) (V : W.Assignments) (ξ : LinkVariables W.rim) : ℝ :=
  W.densityKernel ha β V (W.fieldOfRimValues ha ξ)
theorem glue_congr_of_mem_edges (ha : 0 < a) (V : W.Assignments) {U U' : GaugeField a}
    (h : W.restrictRim U = W.restrictRim U') {q : ElementaryPlaquette a} (hq : q ∈ W.faces)
    {e : Link a} (he : e ∈ q.edges) : W.glue ha V U e = W.glue ha V U' e := by
  classical
  by_cases hW : e ∈ W.links
  · simp [LinkWindow.glue, hW]
  · have hpos : e.IsPositivelyOriented := by
      have he' : e ∈ W.rim := ⟨⟨q, hq, he⟩, hW⟩
      exact mem_positiveLinks_iff.mp (W.rim_subset_positiveLinks he')
    have hopp : e.opposite ∉ W.links := fun h' =>
      Link.opposite_not_isPositivelyOriented ha hpos (W.isPositive _ h')
    have hU : U e = U' e := congrFun h ⟨e, ⟨q, hq, he⟩, hW⟩
    simpa [LinkWindow.glue, hW, hopp] using hU
theorem boltzmannWeight_congr (ha : 0 < a) (β : ℝ) (V : W.Assignments) {U U' : GaugeField a}
    (h : W.restrictRim U = W.restrictRim U') :
    W.boltzmannWeight ha β V U = W.boltzmannWeight ha β V U' := by
  have hsum : ∑ᶠ q ∈ W.faces, faceEnergy (W.glue ha V U) q =
      ∑ᶠ q ∈ W.faces, faceEnergy (W.glue ha V U') q := by
    refine finsum_mem_congr rfl fun q hq => ?_
    have key : ∀ e ∈ q.edges, W.glue ha V U e = W.glue ha V U' e :=
      fun e he => W.glue_congr_of_mem_edges ha V h hq he
    simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at key
    obtain ⟨h1, h2, h3, h4⟩ := key
    simp only [faceEnergy, faceHolonomy, h1, h2, h3, h4]
  simp only [LinkWindow.boltzmannWeight, hsum]
theorem rimKernel_restrictRim (ha : 0 < a) (β : ℝ) (V : W.Assignments)
    (U : GaugeField a) :
    W.rimKernel ha β V (W.restrictRim U) = W.densityKernel ha β V U := by
  have hU : W.restrictRim (W.fieldOfRimValues ha (W.restrictRim U)) =
      W.restrictRim U := by
    funext e
    exact gluedField_apply_of_mem ha W.rim_subset_positiveLinks _ _ e
  have hw : ∀ V' : W.Assignments,
      W.boltzmannWeight ha β V' (W.fieldOfRimValues ha (W.restrictRim U)) =
        W.boltzmannWeight ha β V' U := fun V' => W.boltzmannWeight_congr ha β V' hU
  simp only [rimKernel, LinkWindow.densityKernel, hw]
def realOperator (ha : 0 < a) (β : ℝ) (F : GaugeField a → ℝ) (U : GaugeField a) :
    ℝ :=
  ∫ V, F (W.glue ha V U) * W.rimKernel ha β V (W.restrictRim U) ∂W.haarProd
def stateDensity (ha : 0 < a) (β : ℝ) (ν : RealWeakState a) (V : W.Assignments) : ℝ :=
  ∫ U, W.rimKernel ha β V (W.restrictRim U) ∂ν.measure
theorem stateDensity_eq_marginalDensity (ha : 0 < a) (β : ℝ) (ν : RealWeakState a)
    (V : W.Assignments) :
    W.stateDensity ha β ν V = W.marginalDensity ha β ν.measure V := by
  simp only [stateDensity, marginalDensity, rimKernel_restrictRim]
def stateDistance (ha : 0 < a) (β : ℝ) (μ ν : RealWeakState a) : ℝ≥0∞ :=
  ⨆ V : W.Assignments, ENNReal.ofReal |W.stateDensity ha β ν V / W.stateDensity ha β μ V - 1|
def infStateDistance (ha : 0 < a) (β : ℝ) (μ : RealWeakState a)
    (𝒜 : Set (RealWeakState a)) : ℝ≥0∞ :=
  ⨅ ν ∈ 𝒜, W.stateDistance ha β μ ν
end Kernel
section LeastSide
variable {L K : ℕ} (W : LinkWindow (PeriodicLattice.meshSize L (K : ℤ)))
def torusSidesOfInjection : Set ℝ :=
  {s | ∃ m : ℕ, 0 < m ∧ PeriodicLattice.torusSide L m = s ∧ W.InjectsIntoTorus m}
open Classical in
def leastTorusSide : EReal :=
  if W.torusSidesOfInjection.Nonempty then ((sInf W.torusSidesOfInjection : ℝ) : EReal) else ⊤
end LeastSide
end LinkWindow
end InfiniteLattice
end YangMills.Construction
