import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.EuclideanIsometries
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
def IsBlockScale (P : Conventions.StandingParameters) (M : ℕ) : Prop := ∃ k : ℕ, M = P.L ^ k
theorem IsBlockScale.one_le {P : Conventions.StandingParameters} {M : ℕ}
    (hM : IsBlockScale P M) : 1 ≤ M := by
  obtain ⟨k, rfl⟩ := hM
  have hL : 13 ≤ P.L := P.isAdmissible.2
  exact Nat.one_le_pow _ _ (by omega)
inductive ModelSpace where
  | euclidean
  | torus
namespace ModelSpace
variable (P : Conventions.StandingParameters)
def Carrier : ModelSpace → Type
  | euclidean => Fin 4 → ℝ
  | torus => P.Torus
instance (X : ModelSpace) : AddCommGroup (X.Carrier P) :=
  match X with
  | euclidean => inferInstanceAs (AddCommGroup (Fin 4 → ℝ))
  | torus => inferInstanceAs (AddCommGroup P.Torus)
def torusCover : (Fin 4 → ℝ) → P.Torus :=
  TorusMetric.torusProj (PeriodicLattice.torusSide P.L P.m)
def proj : (X : ModelSpace) → (Fin 4 → ℝ) → X.Carrier P
  | euclidean => id
  | torus => torusCover P
variable (X : ModelSpace)
def basePoint : X.Carrier P := 0
def norm : (X : ModelSpace) → X.Carrier P → ℝ
  | euclidean, z => TorusMetric.euclidNormVec z
  | torus, z => TorusMetric.torusEuclidNorm (S := PeriodicLattice.torusSide P.L P.m) z
def dist (a b : X.Carrier P) : ℝ := norm P X (a - b)
def infDist (A B : Set (X.Carrier P)) : ℝ≥0∞ :=
  ⨅ a ∈ A, ⨅ b ∈ B, ENNReal.ofReal (dist P X a b)
def closureIn (A : Set (X.Carrier P)) : Set (X.Carrier P) :=
  MetricNotions.closureWrt (dist P X) A
def IsCompactIn (A : Set (X.Carrier P)) : Prop := MetricNotions.IsCompactWrt (dist P X) A
def closedBall (c : X.Carrier P) (r : ℝ) : Set (X.Carrier P) := {z | norm P X (z - c) ≤ r}
def ballAtBase (r : ℝ≥0∞) : Set (X.Carrier P) := {z | ENNReal.ofReal (norm P X z) < r}
theorem ballAtBase_top : ballAtBase P X ⊤ = univ := by
  ext z
  simp [ballAtBase]
theorem ballAtBase_ofReal {r : ℝ} (hr : 0 < r) :
    ballAtBase P X (ENNReal.ofReal r) = {z | norm P X z < r} := by
  ext z
  simp [ballAtBase, ENNReal.ofReal_lt_ofReal_iff hr]
def gradR4 (F : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => TestFunctions.partialDerivR4 i F x
def IsC1 : (X : ModelSpace) → (X.Carrier P → ℝ) → Prop
  | euclidean, f => TestFunctions.IsC1R4 f
  | torus, f => TestFunctions.IsC1R4 (f ∘ torusCover P)
def IsGradOnTorus (f : P.Torus → ℝ) (G : P.Torus → Fin 4 → ℝ) : Prop :=
  G ∘ torusCover P = gradR4 (f ∘ torusCover P)
def grad : (X : ModelSpace) → (X.Carrier P → ℝ) → X.Carrier P → Fin 4 → ℝ
  | euclidean, f => gradR4 f
  | torus, f => Classical.epsilon (IsGradOnTorus P f)
def IsLiftOf (z : X.Carrier P) (v : Fin 4 → ℝ) : Prop := proj P X v = z
def IsMinimalLiftOf (z : X.Carrier P) (v : Fin 4 → ℝ) : Prop :=
  IsLiftOf P X z v ∧ TorusMetric.euclidNormVec v = norm P X z
end ModelSpace
end YangMills.Construction.LatticeLimits
end
