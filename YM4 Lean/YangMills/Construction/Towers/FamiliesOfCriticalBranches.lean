import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Tower
variable {L n k : ℕ}
structure CriticalBranchData (L n k : ℕ) where
  energy : ∀ j : ℕ, (Edge L n k j → Matrices.ComplexMatrix2) → ℝ
  prolong : ∀ i : ℕ, (Edge L n k (i + 1) → Matrices.ComplexMatrix2) → Edge L n k i →
    Matrices.ComplexMatrix2
instance : Nonempty (CriticalBranchData L n k) := ⟨⟨fun _ _ => 0, fun _ _ _ => 1⟩⟩
def blockGaugeLift {i : ℕ} (v : Vertex L n k (i + 1) → Matrices.ComplexMatrix2) :
    Vertex L n k i → Matrices.ComplexMatrix2 :=
  fun x => v (Classical.epsilon fun y : Vertex L n k (i + 1) =>
    x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y)
def ForGaugesNearOneOrConstant {j : ℕ}
    (P : (Vertex L n k j → Matrices.ComplexMatrix2) → (Edge L n k j → Matrices.ComplexMatrix2) →
      Prop) : Prop :=
  (∀ᶠ q in 𝓝[gaugeGroupAt L n k j] (fun _ => (1 : Matrices.ComplexMatrix2)) ×ˢ
      𝓝[fieldSpace L n k j] (fun _ => (1 : Matrices.ComplexMatrix2)), P q.1 q.2) ∧
    EventuallyNearIdentity (fieldSpace L n k j) fun W => ∀ v ∈ gaugeGroupAt L n k j,
      (∀ x x', v x = v x') → P v W
def IsLevelSymmetry (k j : ℕ)
    (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n) : Prop :=
  IsDistancePreserving f ∧ MapsSublatticeOnto k j f
def TangentSpacesAreKernels (i : ℕ) (N : Set (Edge L n k i → Matrices.ComplexMatrix2)) : Prop :=
  ∀ V ∈ N, ∀ B : Edge L n k i → Matrices.ComplexMatrix2,
    B ∈ (fieldCurveData L n k i).tangentSpan N V ↔
      B ∈ edgeFormSpace L n k i ∧ leftDifferential (smoothingStep L n k i) V B = 0
def IsUniqueCriticalPointIn {j : ℕ} (O N : Set (Edge L n k j → Matrices.ComplexMatrix2))
    (F : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ) (x : Edge L n k j → Matrices.ComplexMatrix2) :
    Prop :=
  x ∈ O ∧ (fieldCurveData L n k j).IsCriticalOn N F x ∧
    ∀ V ∈ O, (fieldCurveData L n k j).IsCriticalOn N F V → V = x
def HasPosDefHessian {j : ℕ} (N : Set (Edge L n k j → Matrices.ComplexMatrix2))
    (F : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ) (x : Edge L n k j → Matrices.ComplexMatrix2) :
    Prop :=
  ((fieldCurveData L n k j).hessianForm (S := (fieldCurveData L n k j).tangentSpan N x)
    Subtype.val N F x).PosDef
namespace CriticalBranchData
variable (b : CriticalBranchData L n k)
def gaugeFixedEnergy (i : ℕ) (V : Edge L n k i → Matrices.ComplexMatrix2) : ℝ :=
  b.energy i V + axialFunction L n k i V
def levelFibre {i : ℕ} (U : Set (Edge L n k i → Matrices.ComplexMatrix2))
    (W : Edge L n k (i + 1) → Matrices.ComplexMatrix2) :
    Set (Edge L n k i → Matrices.ComplexMatrix2) :=
  {V | V ∈ U ∧ smoothingStep L n k i V = W}
def prolongComp : ∀ j : ℕ, (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k 0 →
    Matrices.ComplexMatrix2
  | 0 => id
  | i + 1 => prolongComp i ∘ b.prolong i
def hessianAtOne (j : ℕ) (B B' : Edge L n k j → Matrices.ComplexMatrix2) : ℝ :=
  leftSecondDeriv (b.energy j) (trivialField L n k j) B B'
def stepQuadratic (i : ℕ) (ξ : Edge L n k i → Matrices.ComplexMatrix2) : ℝ :=
  b.hessianAtOne i ξ ξ + traceFinsumNorm (fineOnlyContourAverage L n k i ξ) ^ 2
def energyGradient (j : ℕ) (W : Edge L n k j → Matrices.ComplexMatrix2) :
    Edge L n k j → Matrices.ComplexMatrix2 :=
  leftGradient (fieldSpace L n k j) (fun V => (b.energy j V : ℂ)) W
def SatisfiesMultiplierIdentity (j : ℕ) (W : Edge L n k j → Matrices.ComplexMatrix2) : Prop :=
  ∃ g : edgeFormSpace L n k j, (g : Edge L n k j → Matrices.ComplexMatrix2) = b.energyGradient j W ∧
    (PairedFunctionSpace.realTransposeMap (S := edgePairedSpace L n k 0)
        (S' := edgePairedSpace L n k j)
        (leftDifferentialLinear (smoothingIter L n k j) (b.prolongComp j W)) g).1 =
      leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ))
        (b.prolongComp j W)
structure IsCriticalUpTo (m : ℕ) : Prop where
  analytic_energy : ∀ j ≤ m, ∃ U : Set (Edge L n k j → Matrices.ComplexMatrix2),
    IsOpenNhdOfOne U ∧ IsAnalyticFieldFunction U (b.energy j)
  energy_nonneg : ∀ j ≤ m, EventuallyNearIdentity (fieldSpace L n k j) fun V => 0 ≤ b.energy j V
  energy_bottom : EventuallyNearIdentity (fieldSpace L n k 0) fun V =>
    b.energy 0 V = plaquetteAction L n k V
  analytic_prolong : ∀ i < m, ∃ U : Set (Edge L n k (i + 1) → Matrices.ComplexMatrix2),
    IsOpenNhdOfOne U ∧ IsAnalyticFieldMap U (b.prolong i)
  prolong_trivial : ∀ i < m, b.prolong i (trivialField L n k (i + 1)) = trivialField L n k i
  prolong_section : ∀ i < m, EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
    smoothingStep L n k i (b.prolong i W) = W ∧ IsAxialGaugeAt L n k i (b.prolong i W) ∧
      b.energy (i + 1) W = b.energy i (b.prolong i W) ∧
      b.energy (i + 1) W = b.gaugeFixedEnergy i (b.prolong i W)
  fibre_structure : ∀ i < m, ∃ U : Set (Edge L n k i → Matrices.ComplexMatrix2), IsOpenNhdOfOne U ∧
    EventuallyNearIdentity (fieldSpace L n k (i + 1))
      (fun W => IsAnalyticFieldSubmanifold (levelFibre U W) ∧
        TangentSpacesAreKernels i (levelFibre U W)) ∧
    ∃ O ∈ 𝓝[fieldSpace L n k i] (trivialField L n k i),
      EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
        IsUniqueCriticalPointIn O (levelFibre U W) (b.gaugeFixedEnergy i) (b.prolong i W) ∧
          HasPosDefHessian (levelFibre U W) (b.gaugeFixedEnergy i) (b.prolong i W)
  energy_gauge_invariant : ∀ j ≤ m, ForGaugesNearOneOrConstant fun v W =>
    b.energy j (PeriodicLattice.gaugeTransform v W) = b.energy j W
  prolong_gauge_equivariant : ∀ i < m, ForGaugesNearOneOrConstant fun v W =>
    b.prolong i (PeriodicLattice.gaugeTransform v W) =
      PeriodicLattice.gaugeTransform (blockGaugeLift v) (b.prolong i W)
  energy_symmetry_invariant : ∀ j ≤ m, EventuallyNearIdentity (fieldSpace L n k j) fun W =>
    ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n, IsLevelSymmetry k j f →
      b.energy j (pushField f W) = b.energy j W
  prolong_symmetry_equivariant : ∀ i < m, EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
    ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
      IsLevelSymmetry k (i + 1) f →
      b.prolong i (pushField f W) = pushField f (b.prolong i W)
  energy_trivial : ∀ j ≤ m, b.energy j (trivialField L n k j) = 0
  gradient_trivial : ∀ j ≤ m, b.energyGradient j (trivialField L n k j) = 0
  hessianAtOne_nonneg : ∀ j ≤ m, ∀ B ∈ edgeFormSpace L n k j, 0 ≤ b.hessianAtOne j B B
  hessianAtOne_null_iff : ∀ j ≤ m, ∀ B ∈ edgeFormSpace L n k j,
    (∀ B' ∈ edgeFormSpace L n k j, b.hessianAtOne j B B' = 0) ↔ IsClosedEdgeForm B
  hessianAtOne_bottom : ∀ B ∈ edgeFormSpace L n k 0,
    b.hessianAtOne 0 B B = traceFinsumNorm (edgeCoboundary B) ^ 2
  hessianAtOne_isLeast : ∀ i < m, ∀ B ∈ edgeFormSpace L n k (i + 1),
    IsLeast {r | ∃ ξ ∈ edgeFormSpace L n k i, linearSmoothing L n k i ξ = B ∧
        r = b.stepQuadratic i ξ}
      (b.hessianAtOne (i + 1) B B)
  hessianAtOne_minimizer_iff : ∀ i < m, ∀ B ∈ edgeFormSpace L n k (i + 1),
    ∀ ξ : Edge L n k i → Matrices.ComplexMatrix2,
    (ξ ∈ edgeFormSpace L n k i ∧ linearSmoothing L n k i ξ = B ∧
        b.stepQuadratic i ξ = b.hessianAtOne (i + 1) B B) ↔
      ξ = leftDifferential (b.prolong i) (trivialField L n k (i + 1)) B
  prolongComp_section : ∀ j ≤ m, EventuallyNearIdentity (fieldSpace L n k j) fun W =>
    smoothingIter L n k j (b.prolongComp j W) = W ∧
      b.energy j W = plaquetteAction L n k (b.prolongComp j W) ∧
      b.SatisfiesMultiplierIdentity j W
  prolongComp_lift : ∀ i < m, EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
    smoothingIter L n k i (b.prolongComp (i + 1) W) = b.prolong i W
  prolongComp_critical : ∀ j ≤ m, ∃ U : Set (Edge L n k 0 → Matrices.ComplexMatrix2),
    IsOpenNhdOfOne U ∧
    EventuallyNearIdentity (fieldSpace L n k j) fun W =>
      (fieldCurveData L n k 0).IsCriticalOn {V | V ∈ U ∧ smoothingIter L n k j V = W}
        (plaquetteAction L n k) (b.prolongComp j W)
abbrev IsCritical : Prop := b.IsCriticalUpTo k
end CriticalBranchData
end Tower
end YangMills.Construction
end
