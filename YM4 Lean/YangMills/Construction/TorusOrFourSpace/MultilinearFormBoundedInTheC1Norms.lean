import YangMills.Construction.TorusOrFourSpace.ClassesOfFunctionsWithSupportInASet
import YangMills.Construction.TorusOrFourSpace.CutOffsOnAProductOfOpenSets
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind.Tuple
section Defs
variable (D : Params) (E : Kind) {n : ℕ+}
def coordProj (i : Fin (n : ℕ)) (S : Set (E.Tuple D n)) : Set (E.Pt D) :=
  (fun y => y i) '' S
def OneOnCoordProjs (F : E.Tuple D n → ℂ) (χ : Fin (n : ℕ) → E.Pt D → ℝ) : Prop :=
  ∀ i, ∀ y ∈ coordProj D E i (supportT D E F), χ i y = 1
def IsTensorSumWithin (O : Fin (n : ℕ) → Set (E.Pt D))
    (χ : Fin (n : ℕ) → E.Pt D → ℝ) (G : E.Tuple D n → ℂ) : Prop :=
  ∃ (m : ℕ) (φ : Fin m → Fin (n : ℕ) → E.Pt D → ℂ),
    (∀ l i, φ l i ∈ singleTestFns D E (O i) ∧
      Kind.supportQ D E (φ l i) ⊆ Kind.supportQ D E (χ i)) ∧
    G = ∑ l, tensorProd D E (φ l)
abbrev C1Components (O : Fin (n : ℕ) → Set (E.Pt D)) : Type :=
  ∀ i, Kind.c1SupportedIn D E (O i)
variable {D E} {O : Fin (n : ℕ) → Set (E.Pt D)}
def IsMultilinearReal (B : C1Components D E O → ℝ) : Prop :=
  ∀ (g : C1Components D E O) (i : Fin (n : ℕ)) (u v w : Kind.c1SupportedIn D E (O i)) (a b : ℝ),
    w.1 = a • u.1 + b • v.1 →
      B (Function.update g i w) = a * B (Function.update g i u) + b * B (Function.update g i v)
def C1Bounded (c : ℝ) (B : C1Components D E O → ℝ) : Prop :=
  ∀ g : C1Components D E O,
    ENNReal.ofReal |B g| ≤ ENNReal.ofReal c * ∏ i, c1NormSingleReal D E (g i).1
def IsDistribExtending (B : C1Components D E O → ℝ)
    (T : testFns D E (boxSet D E O) → ℂ) : Prop :=
  IsDistrib T ∧ ∀ φ : Fin (n : ℕ) → E.Pt D → ℝ,
    (∀ i, (fun y => (φ i y : ℂ)) ∈ singleTestFns D E (O i)) →
      ∃ (hφ : ∀ i, φ i ∈ Kind.c1SupportedIn D E (O i))
        (hF : tensorProd D E (fun i y => (φ i y : ℂ)) ∈ testFns D E (boxSet D E O)),
        T ⟨_, hF⟩ = ((B fun i => ⟨φ i, hφ i⟩ : ℝ) : ℂ)
end Defs
def C1BoundedFormDistribution : Prop :=
  ∀ (D : Params) (n : ℕ+) (ρ c : ℝ), 0 < ρ → 0 ≤ c →
    ∀ O : Fin (n : ℕ) → Set (Kind.euclidean.Pt D),
      (∀ i, Kind.IsOpenQ D Kind.euclidean (O i)) →
      (∀ i, ∀ u ∈ O i, TorusMetric.euclidNormVec u ≤ ρ) →
    ∀ B : C1Components D Kind.euclidean O → ℝ,
      IsMultilinearReal B → C1Bounded c B →
      (∀ F : testFns D Kind.euclidean (boxSet D Kind.euclidean O),
        (∀ χ, IsCutoffFamily D Kind.euclidean O χ → OneOnCoordProjs D Kind.euclidean F.1 χ →
          IsCutoffOf D Kind.euclidean χ F) ∧
        (∃ χ, IsCutoffFamily D Kind.euclidean O χ ∧ OneOnCoordProjs D Kind.euclidean F.1 χ) ∧
        ∀ χ, IsCutoffOf D Kind.euclidean χ F →
          ∃ Fs : ℕ+ → testFns D Kind.euclidean (boxSet D Kind.euclidean O),
            (∀ t, IsTensorSumWithin D Kind.euclidean O χ (Fs t).1) ∧
              TendstoInTestFns Fs F) ∧
      (∃! T, IsDistribExtending B T) ∧
      ∀ T, IsDistribExtending B T →
        (∀ (F : testFns D Kind.euclidean (boxSet D Kind.euclidean O)) (χ),
          IsCutoffOf D Kind.euclidean χ F →
            ENNReal.ofReal ‖T F‖ ≤
              ENNReal.ofReal (2 ^ (n : ℕ) * c * cutoffBound n ρ) *
                (∏ i, c1NormSingleReal D Kind.euclidean (χ i)) *
                  cNorm D Kind.euclidean (5 * (n : ℕ) + 1) F.1) ∧
        IsDistribOfOrderLE (5 * (n : ℕ) + 1) T
end YangMills.Construction.PeriodicSpace.Kind.Tuple
