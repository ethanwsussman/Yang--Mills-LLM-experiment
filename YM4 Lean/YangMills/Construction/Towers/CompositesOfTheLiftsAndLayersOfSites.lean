import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace GaussianConstraint
def IntegrableGaussianOnKernel {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (M : E →ₗ[ℝ] F) (Q : QuadraticForm ℝ (LinearMap.ker M)) : Prop :=
  letI : MeasurableSpace (LinearMap.ker M) := borel _
  haveI : BorelSpace (LinearMap.ker M) := ⟨rfl⟩
  Integrable fun v : LinearMap.ker M => Real.exp (-(1 / 2) * Q v)
end GaussianConstraint
namespace Tower
variable {L n k : ℕ}
def CriticalBranchData.prolongIter (b : CriticalBranchData L n k) {j t : ℕ} (h : j ≤ t) :
    (Edge L n k t → Matrices.ComplexMatrix2) → Edge L n k j → Matrices.ComplexMatrix2 :=
  Nat.leRec (motive := fun t _ => (Edge L n k t → Matrices.ComplexMatrix2) → Edge L n k j → Matrices.ComplexMatrix2)
    id (fun i _ f => f ∘ b.prolong i) h
def chosenProlongIter (L n k : ℕ) {j : ℕ} (h : j ≤ k) :
    (Edge L n k k → Matrices.ComplexMatrix2) → Edge L n k j → Matrices.ComplexMatrix2 :=
  (chosenCriticalBranch L n k).prolongIter h
def IsInVertexLayer (L n k i : ℕ) (x : PeriodicLattice.FourTorus L n) : Prop :=
  x ∈ PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) ∧
    x ∉ PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1))
def vertexFunctionsVanishingOnTop (L n k : ℕ) : Submodule ℝ (Vertex L n k 0 → Matrices.ComplexMatrix2) where
  carrier := {f | f ∈ vertexFunctionSpace L n k 0 ∧ ∀ x : Vertex L n k 0,
    (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k k) → f x = 0}
  add_mem' := by
    rintro f g ⟨hf, vf⟩ ⟨hg, vg⟩
    exact ⟨(vertexFunctionSpace L n k 0).add_mem hf hg, fun x hx => by simp [vf x hx, vg x hx]⟩
  zero_mem' := ⟨(vertexFunctionSpace L n k 0).zero_mem, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨hf, vf⟩
    exact ⟨(vertexFunctionSpace L n k 0).smul_mem c hf, fun x hx => by simp [vf x hx]⟩
def restrictToLayer (i : ℕ) (f : Vertex L n k 0 → Matrices.ComplexMatrix2) : FineOnlyVertex L n k i → Matrices.ComplexMatrix2 :=
  fun x => restrictVertexFunction i f x.1
structure ProlongItersNearIdentity (L n k : ℕ) : Prop where
  tendsto : ∀ (j : ℕ) (h : j ≤ k), Tendsto (chosenProlongIter L n k h)
    (𝓝[fieldSpace L n k k] trivialField L n k k)
    (𝓝[fieldSpace L n k j] trivialField L n k j)
  comp_eq : ∀ (j : ℕ) (h : j ≤ k), EventuallyNearIdentity (fieldSpace L n k k) fun W =>
    chosenProlongComp L n k j (chosenProlongIter L n k h W) = chosenProlongComp L n k k W
  comp_zero_eq : EventuallyNearIdentity (fieldSpace L n k k) fun W =>
    chosenProlongIter L n k (Nat.zero_le k) W = chosenProlongComp L n k k W
structure SmoothingStepWellDefined (L n k : ℕ) : Prop where
  mem_smallPlaquetteFields : ∀ i < k, EventuallyNearIdentity (fieldSpace L n k i) fun V =>
    ∀ e : Edge L n k (i + 1), V ∈ PeriodicLattice.smallPlaquetteFields (Averaging.smoothingRadius L) e
  contourMean_mem : ∀ i < k, EventuallyNearIdentity (fieldSpace L n k i) fun V =>
    ∀ y : Vertex L n k (i + 1), ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
      PeriodicLattice.HasContourMean V y x ∧
        PeriodicLattice.meanContourHolonomy V y x ∈ PeriodicLattice.compactGaugeGroup
  smoothingStep_mem : ∀ i < k, EventuallyNearIdentity (fieldSpace L n k i) fun V =>
    ∀ e : Edge L n k (i + 1), smoothingStep L n k i V e ∈ PeriodicLattice.compactGaugeGroup
  contourLogDeriv_linear : ∀ i < k, EventuallyNearIdentity (fieldSpace L n k i) fun V =>
    ∃ T : edgeFormSpace L n k i →ₗ[ℝ] fineOnlyFunctions L n k i, ∀ A : edgeFormSpace L n k i,
      (T A : FineOnlyVertex L n k i → Matrices.ComplexMatrix2) =
        contourLogDeriv L n k i V (A : Edge L n k i → Matrices.ComplexMatrix2)
  iterDifferential_linear : ∀ j ≤ k, EventuallyNearIdentity (fieldSpace L n k 0) fun U =>
    ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k j, ∀ A : edgeFormSpace L n k 0,
      (T A : Edge L n k j → Matrices.ComplexMatrix2) =
        leftDifferential (smoothingIter L n k j) U (A : Edge L n k 0 → Matrices.ComplexMatrix2)
structure VertexLayerDecomposition (L n k : ℕ) : Prop where
  existsUnique_layer : ∀ x : Vertex L n k 0,
    (x : PeriodicLattice.FourTorus L n) ∉ PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k k) →
      ∃! i : Fin k, IsInVertexLayer L n k i (x : PeriodicLattice.FourTorus L n)
  restrict_bijective : ∃ T : vertexFunctionsVanishingOnTop L n k ≃ₗ[ℝ]
      ∀ i : Fin k, fineOnlyFunctions L n k i, ∀ (f : vertexFunctionsVanishingOnTop L n k) (i : Fin k),
    (T f i : FineOnlyVertex L n k i → Matrices.ComplexMatrix2) = restrictToLayer i (f : Vertex L n k 0 → Matrices.ComplexMatrix2)
  pairing_eq_sum : ∀ f ∈ vertexFunctionsVanishingOnTop L n k, ∀ g ∈ vertexFunctionsVanishingOnTop L n k,
    traceFinsumPairing f g = ∑ i : Fin k,
      fineOnlyPairing (restrictToLayer (L := L) (n := n) (k := k) i f) (restrictToLayer i g)
end Tower
def ProlongCompositesAndVertexLayers.Statement : Prop :=
  (∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    Tower.ProlongItersNearIdentity L n k ∧ Tower.SmoothingStepWellDefined L n k ∧
      Tower.VertexLayerDecomposition L n k) ∧
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (M : E →ₗ[ℝ] F)
    (Q : QuadraticForm ℝ (LinearMap.ker M)), Function.Surjective M → Q.PosDef →
      GaussianConstraint.IntegrableGaussianOnKernel M Q ∧ 0 < GaussianConstraint.constrainedGaussianNumber M Q
end YangMills.Construction
end
