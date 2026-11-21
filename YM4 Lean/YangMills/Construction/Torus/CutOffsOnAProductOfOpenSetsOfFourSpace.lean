import YangMills.Construction.Torus.ChartsOfSmallOpenSetsAndTransportOfFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.AmbientPoints
open TorusMetric
def bumpScale (ρ : ℝ) : ℝ := 2 * ρ / Real.pi
def bumpNumber (n : ℕ) (ρ : ℝ) : ℝ :=
  1 + 16 * (n : ℝ) * 3 ^ (4 * n - 1) * bumpScale ρ ^ (4 * n + 1) * (bumpScale ρ + 2) ^ n
variable {s : Conventions.StandingParameters} {n : ℕ}
def IsOpenTupleInBall (ρ : ℝ) (O : Fin n → Set (Pt s .euclidean)) : Prop :=
  1 ≤ n ∧ 0 < ρ ∧ ∀ i, IsOpen (O i) ∧ O i ⊆ {u : Fin 4 → ℝ | euclidNormVec u ≤ ρ}
def entrySpace (O : Fin n → Set (Pt s .euclidean)) (i : Fin n) :
    Set (Pt s .euclidean → ℝ) :=
  c1CompactSupportIn (O i)
def singletonTuples (A : Set (Pt s .euclidean)) : Set (Tuple s .euclidean 1) := {y | y 0 ∈ A}
def IsCutoff (O : Fin n → Set (Pt s .euclidean)) (χ : Fin n → Pt s .euclidean → ℝ) : Prop :=
  ∀ i, asFunctionOnOnePoint (χ i) ∈ testFns (singletonTuples (O i))
def cutoffTensor (χ : Fin n → Pt s .euclidean → ℝ) : Tuple s .euclidean n → ℂ :=
  tensorProd fun i y => (χ i y : ℂ)
def IsCutoffFor {O : Fin n → Set (Pt s .euclidean)} (χ : Fin n → Pt s .euclidean → ℝ)
    (F : testFns (boxSet O)) : Prop :=
  IsCutoff O χ ∧ cutoffTensor χ * F.1 = F.1
end YangMills.Construction.AmbientPoints
