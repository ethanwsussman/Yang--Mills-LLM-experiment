import YangMills.Construction.Torus.CutOffsOnAProductOfOpenSetsOfFourSpace
import YangMills.Construction.Torus.GradientNormOfAFunctionOfOnePoint
import YangMills.Construction.Torus.PeriodBoxModesCoefficientsAndPartialSums
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open ReflectionPositivity.AxisMirror (Ambient)
namespace AmbientPoints
variable {s : Conventions.StandingParameters} {n : ℕ}
def factorProjection (i : Fin n) (S : Set (Tuple s .euclidean n)) : Set (Pt s .euclidean) :=
  (fun y => y i) '' S
def CutOffIsOneOnProjections (F : Tuple s .euclidean n → ℂ)
    (χ : Fin n → Pt s .euclidean → ℝ) : Prop :=
  ∀ i, ∀ y ∈ factorProjection i (closedSupport F), χ i y = 1
def IsFiniteTensorSumWithin (O : Fin n → Set (Pt s .euclidean))
    (χ : Fin n → Pt s .euclidean → ℝ) (G : Tuple s .euclidean n → ℂ) : Prop :=
  ∃ (m : ℕ) (φ : Fin m → Fin n → Pt s .euclidean → ℂ),
    (∀ l i, ofSinglePoint (φ l i) ∈ testFns (singletonTuples (O i)) ∧
      closedSupport (ofSinglePoint (φ l i)) ⊆ closedSupport (asFunctionOnOnePoint (χ i))) ∧
    G = ∑ l, tensorProd (φ l)
abbrev EntryTuple (O : Fin n → Set (Pt s .euclidean)) : Type :=
  ∀ i, entrySpace O i
variable {O : Fin n → Set (Pt s .euclidean)}
def IsMultilinearOnComponents (B : EntryTuple O → ℝ) : Prop :=
  ∀ (g : EntryTuple O) (i : Fin n) (u v w : entrySpace O i) (a b : ℝ),
    w.1 = a • u.1 + b • v.1 →
      B (Function.update g i w) = a * B (Function.update g i u) + b * B (Function.update g i v)
def IsGradNormBounded (c : ℝ) (B : EntryTuple O → ℝ) : Prop :=
  ∀ g : EntryTuple O,
    ENNReal.ofReal |B g| ≤ ENNReal.ofReal c * ∏ i, c1GradNorm fun x => ((g i).1 x : ℂ)
def IsDistribExtending (B : EntryTuple O → ℝ) (T : testFns (boxSet O) → ℂ) :
    Prop :=
  IsDistrib T ∧ ∀ φ : Fin n → Pt s .euclidean → ℝ,
    (∀ i, asFunctionOnOnePoint (φ i) ∈ testFns (singletonTuples (O i))) →
      ∃ (hφ : ∀ i, φ i ∈ entrySpace O i)
        (hF : tensorProd (fun i y => (φ i y : ℂ)) ∈ testFns (boxSet O)),
        T ⟨_, hF⟩ = ((B fun i => ⟨φ i, hφ i⟩ : ℝ) : ℂ)
def complexEntrySpace (O : Fin n → Set (Pt s .euclidean)) (i : Fin n) :
    Set (Pt s .euclidean → ℂ) :=
  {h | IsCnAtPoint 1 h ∧ IsCompact (tsupport h) ∧ tsupport h ⊆ O i}
def IsComplexComponentTuple (O : Fin n → Set (Pt s .euclidean))
    (h : Fin n → Pt s .euclidean → ℂ) : Prop :=
  ∀ i, h i ∈ complexEntrySpace O i
def IsComplexMultilinearOnComponents (O : Fin n → Set (Pt s .euclidean))
    (B : (Fin n → Pt s .euclidean → ℂ) → ℂ) : Prop :=
  ∀ h, IsComplexComponentTuple O h → ∀ (i : Fin n) (u v : Pt s .euclidean → ℂ),
    u ∈ complexEntrySpace O i → v ∈ complexEntrySpace O i → ∀ a b : ℂ,
      B (Function.update h i (a • u + b • v)) =
        a * B (Function.update h i u) + b * B (Function.update h i v)
def IsComplexGradNormBounded (O : Fin n → Set (Pt s .euclidean)) (C : ℝ)
    (B : (Fin n → Pt s .euclidean → ℂ) → ℂ) : Prop :=
  ∀ h, IsComplexComponentTuple O h →
    ENNReal.ofReal ‖B h‖ ≤ ENNReal.ofReal C * ∏ i, c1GradNorm (h i)
def AgreesWithFormOnRealTensors (B : (Fin n → Pt s .euclidean → ℂ) → ℂ)
    (T : testFns (boxSet O) → ℂ) : Prop :=
  ∀ φ : Fin n → Pt s .euclidean → ℝ,
    (∀ i, asFunctionOnOnePoint (φ i) ∈ testFns (singletonTuples (O i))) →
      ∃ hF : tensorProd (fun i y => (φ i y : ℂ)) ∈ testFns (boxSet O),
        T ⟨_, hF⟩ = B fun i y => (φ i y : ℂ)
def cutoffModeTuple (P : ℝ) (χ : Fin n → Pt s .euclidean → ℝ) (k : Fin (4 * n) → ℤ) :
    Fin n → Pt s .euclidean → ℂ :=
  fun i x => (χ i x : ℂ) * Torus.FourierBox.fourierMode P (Torus.FourierBox.blockOf k i) x
def cutoffSeries (P : ℝ) (B : (Fin n → Pt s .euclidean → ℂ) → ℂ)
    (χ : Fin n → Pt s .euclidean → ℝ) (F : Tuple s .euclidean n → ℂ) : ℂ :=
  ∑' k : Fin (4 * n) → ℤ, Torus.FourierBox.fourierCoeff P F k * B (cutoffModeTuple P χ k)
def cutoffPartialSum (P : ℝ) (χ : Fin n → Pt s .euclidean → ℝ)
    (F : Tuple s .euclidean n → ℂ) (t : ℕ+) : Tuple s .euclidean n → ℂ :=
  fun y => ∑ k ∈ Torus.FourierBox.modesWithin (t : ℕ),
    Torus.FourierBox.fourierCoeff P F k * tensorProd (cutoffModeTuple P χ k) y
end AmbientPoints
end YangMills.Construction
