import YangMills.Construction.Continuum.SeparatingFamilyAndTheCoordinateMap
import YangMills.Construction.ReflectionPositivity.LipschitzTuplesIsometriesOnFunctionsTensorsAndPartitions
import Mathlib
set_option autoImplicit false
open Set Filter
noncomputable section
namespace YangMills.Construction.SeparatingFamily
open TestFunctions ReflectionPositivity.AxisMirror
theorem isSpaceIsometry_of_mem_adicHyperoctahedralMotions {L : ℕ} {r : Equiv.Perm (Fin 4 → ℝ)}
    (hr : r ∈ adicHyperoctahedralMotions L) : InfiniteLattice.IsSpaceIsometry r := by
  obtain ⟨w, hw, v, -, h⟩ := hr
  obtain ⟨σ, ε, hε⟩ := (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff w).1 hw
  intro x y
  unfold InfiniteLattice.euclidDist TorusMetric.euclidNormVec
  congr 1
  have hcoord : ∀ i, (r x - r y) i ^ 2 = (x - y) (σ i) ^ 2 := fun i => by
    have hsign : ((ε i : ℤ) : ℝ) ^ 2 = 1 := by
      rcases Int.units_eq_one_or (ε i) with h1 | h1 <;> simp [h1]
    simp only [Pi.sub_apply, h, Pi.add_apply, hε]
    calc _ = ((ε i : ℤ) : ℝ) ^ 2 * (x (σ i) - y (σ i)) ^ 2 := by ring
      _ = _ := by rw [hsign, one_mul]
  simp only [hcoord]
  exact Equiv.sum_comp σ fun i => (x - y) i ^ 2
def motionToIsometryEquiv (D : MirrorData) (r : adicHyperoctahedralMotions D.L) :
    Ambient.IsometryEquiv D .euclidean :=
  ⟨r.1, isSpaceIsometry_of_mem_adicHyperoctahedralMotions r.2⟩
def MotionGroupCountableAndPreservesBoxUnions (L : ℕ) : Prop :=
  (adicHyperoctahedralMotions L : Set (Equiv.Perm (Fin 4 → ℝ))).Countable ∧
    ∀ r ∈ adicHyperoctahedralMotions L, ∀ Q ∈ ratBoxUnions, ⇑r '' Q ∈ ratBoxUnions
def MotionSpanCountableAndDense (L : ℕ) : Prop :=
  (ratMotionSpan L).Countable ∧
    ∀ Q : ratBoxUnions, (motionDenseSets L Q).Countable ∧ fixedDenseSets Q ⊆ motionDenseSets L Q ∧
      IsDenseInC1ZeroOff Q (motionDenseSets L Q)
def DisjointTupleFamilyEqSpanTuples (D : MirrorData) : Prop :=
  disjointTupleFamily (motionDenseSets D.L) =
    {X | X ≠ [] ∧ (∀ φ ∈ X, φ ∈ ratMotionSpan D.L) ∧
      X.Pairwise fun f g =>
        Disjoint (Ambient.closedSupport D .euclidean f) (Ambient.closedSupport D .euclidean g)}
def SeparatingTuplesCountableAndStable (D : MirrorData) : Prop :=
  (separatingTuples D.L).Countable ∧
    (∀ r : adicHyperoctahedralMotions D.L, ∀ X ∈ separatingTuples D.L,
      (motionToIsometryEquiv D r).mapList X ∈ separatingTuples D.L) ∧
    ∀ X ∈ separatingTuples D.L, ∀ Y ∈ separatingTuples D.L,
      Ambient.HaveDisjointSupports (D := D) (E := .euclidean) X Y →
        Ambient.append (D := D) (E := .euclidean) X Y ∈ separatingTuples D.L
def SeparatingTuplesApproximate (D : MirrorData) (M : ℝ) : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ f : Fin k → ScalarField,
    List.ofFn f ∈ Ambient.separatedN D .euclidean k →
    ∀ O : Fin k → Set (Fin 4 → ℝ), (∀ i, IsOpen (O i)) →
      (∀ i, Ambient.closedSupport D .euclidean (f i) ⊆ O i) →
      ∃ φ : ℕ → Fin k → ScalarField,
        (∀ l, List.ofFn (φ l) ∈ separatingTuples D.L) ∧
        (∀ l i, Ambient.closedSupport D .euclidean (φ l i) ⊆ O i) ∧
        ∀ i, Tendsto (fun l => sharpNormR4 M (φ l i - f i)) atTop (nhds 0)
def SeparatingTuplesFacts : Prop :=
  ∀ D : MirrorData, MotionGroupCountableAndPreservesBoxUnions D.L ∧
    MotionSpanCountableAndDense D.L ∧ DisjointTupleFamilyEqSpanTuples D ∧
    SeparatingTuplesCountableAndStable D ∧
    ∀ M : ℝ, 1 ≤ M → SeparatingTuplesApproximate D M
end YangMills.Construction.SeparatingFamily
end
