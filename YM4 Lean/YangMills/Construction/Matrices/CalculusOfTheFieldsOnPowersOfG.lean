import YangMills.Construction.InfiniteLattice.SingleBondWeight
import YangMills.Construction.Matrices.FunctionsAndOperatorsOfSeveralVariablesOnG
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def smoothOfENatOrder {J : Type} (q : ℕ∞) : Set ((J → specialUnitary) → ℂ) :=
  ENat.recTopCoe smoothSet (fun n => smoothOrder n) q
def supNorm {J : Type} (F : (J → specialUnitary) → ℂ) : ℝ := ⨆ u, ‖F u‖
def IsStarClosedSubalgebraSet {J : Type} (S : Set ((J → specialUnitary) → ℂ)) : Prop :=
  (∃ A : Subalgebra ℂ ((J → specialUnitary) → ℂ), (A : Set ((J → specialUnitary) → ℂ)) = S) ∧
    ∀ F : (J → specialUnitary) → ℂ, F ∈ S → (fun u => star (F u)) ∈ S
namespace FieldCalculus
def OneParameterSubgroups : Prop :=
  ∀ (i : Fin 3) (t s : ℝ),
    matExp ((t : ℂ) • lieGenerator i) =
        ((Real.cos (t / 2) : ℝ) : ℂ) • (1 : Matrices.ComplexMatrix2) +
          (Complex.I * ((Real.sin (t / 2) : ℝ) : ℂ)) • pauli i ∧
      matExp ((t : ℂ) • lieGenerator i) ∈ specialUnitary ∧
      matExp (((t + s : ℝ) : ℂ) • lieGenerator i) =
        matExp ((t : ℂ) • lieGenerator i) * matExp ((s : ℂ) • lieGenerator i)
def HasDerivAlongField (J : Type) : Prop :=
  ∀ (b : J) (i : Fin 3) (F : (J → specialUnitary) → ℂ), F ∈ smoothOrder 1 →
    ∀ u : J → specialUnitary,
    ContDiff ℝ 1 (fun t : ℝ => F (shiftAt u b i t)) ∧
      ∀ t : ℝ, HasDerivAt (fun s : ℝ => F (shiftAt u b i s))
        (rightField b i F (shiftAt u b i t)) t
def LeibnizRules (J : Type) : Prop :=
  ∀ (b : J) (i : Fin 3) (F H : (J → specialUnitary) → ℂ), F ∈ smoothOrder 1 →
    H ∈ smoothOrder 1 →
    rightField b i (fun u => F u * H u) =
        (fun u => rightField b i F u * H u + F u * rightField b i H u) ∧
      rightField b i (fun u => star (F u)) = fun u => star (rightField b i F u)
def ChainRuleHolds (J : Type) : Prop :=
  ∀ (q : ℕ∞) (F : (J → specialUnitary) → ℂ) (I : Set ℝ) (φ : ℝ → ℝ),
    F ∈ smoothOfENatOrder q → (∀ u, (F u).im = 0) →
    IsOpen I → I.OrdConnected → (∀ u, (F u).re ∈ I) → ContDiffOn ℝ ∞ φ I →
    (fun u => ((φ (F u).re : ℝ) : ℂ)) ∈ smoothOfENatOrder q ∧
      (1 ≤ q → ∀ (b : J) (i : Fin 3) (u : J → specialUnitary),
        rightField b i (fun v => ((φ (F v).re : ℝ) : ℂ)) u =
          ((deriv φ (F u).re : ℝ) : ℂ) * rightField b i F u)
def ExpAndInvSmooth (J : Type) : Prop :=
  (∀ F : (J → specialUnitary) → ℂ, F ∈ smoothSet → (∀ u, (F u).im = 0) →
      (fun u => Complex.exp (F u)) ∈ smoothSet) ∧
    ∀ F : (J → specialUnitary) → ℂ, F ∈ smoothSet → (∀ u, (F u).im = 0 ∧ 0 < (F u).re) →
      (fun u => (F u)⁻¹) ∈ smoothSet
def PolynomialAndBondWeightSmooth (J : Type) : Prop :=
  (∀ F : (J → specialUnitary) → ℂ, IsEntryPolynomial F → F ∈ smoothSet) ∧
    ∀ β : ℝ, 0 < β → ∀ b c : J, b ≠ c →
      (fun u : J → specialUnitary =>
        YangMills.Construction.InfiniteLattice.singleBondWeight β (u b * (u c)⁻¹)) ∈ smoothSet ∧
        ∀ u : J → specialUnitary,
          (YangMills.Construction.InfiniteLattice.singleBondWeight β (u b * (u c)⁻¹)).im = 0 ∧
          0 < (YangMills.Construction.InfiniteLattice.singleBondWeight β (u b * (u c)⁻¹)).re
def SingleWeightSmooth : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (K : Type) [Unique K],
    (fun v : K → specialUnitary =>
      YangMills.Construction.InfiniteLattice.singleBondWeight β (v default)) ∈ smoothSet
def FieldsSkewAdjoint (J : Type) [Finite J] : Prop :=
  ∀ (b : J) (i : Fin 3) (F H : (J → specialUnitary) → ℂ), F ∈ smoothOrder 1 →
    H ∈ smoothOrder 1 →
    ∫ u, rightField b i F u * H u ∂haarPi J = -∫ u, F u * rightField b i H u ∂haarPi J ∧
      ∫ u, star (rightField b i F u) * H u ∂haarPi J =
        -∫ u, star (F u) * rightField b i H u ∂haarPi J
def SeriesSmooth (J : Type) : Prop :=
  ∀ (A : Type) [Countable A] (F : A → (J → specialUnitary) → ℂ),
    (∀ a, F a ∈ smoothSet) →
    (∀ w : List (J × Fin 3), Summable fun a => supNorm (fieldWord w (F a))) →
    (fun u => ∑' a, F a u) ∈ smoothSet ∧
      ∀ (w : List (J × Fin 3)) (u : J → specialUnitary),
        HasSum (fun a => fieldWord w (F a) u)
          (fieldWord w (fun v => ∑' a, F a v) u)
def PartialVariablesSmooth (J : Type) [Finite J] : Prop :=
  ∀ B : Set J, B.Nonempty → B ≠ Set.univ →
    (∀ (F : (J → specialUnitary) → ℂ), F ∈ smoothSet → ∀ z : ↥Bᶜ → specialUnitary,
      (fun v : ↥B → specialUnitary => F (glue B v z)) ∈ smoothSet) ∧
    (∀ φ : (↥B → specialUnitary) → ℂ, φ ∈ smoothSet →
      pullFromPart B φ ∈ smoothSet) ∧
    ∀ (F : (J → specialUnitary) → ℂ) (A : (↥B → specialUnitary) → (↥B → specialUnitary) → ℂ),
      F ∈ smoothSet →
      IsEntryPolynomial (fun x : ↥B ⊕ ↥B → specialUnitary => A (x ∘ Sum.inl) (x ∘ Sum.inr)) →
      (fun u : J → specialUnitary => ∫ v', A (restrictTo B u) v' *
        F (glue B v' (restrictTo Bᶜ u)) ∂haarPi ↥B) ∈ smoothSet
def AllRules : Prop :=
  OneParameterSubgroups ∧ SingleWeightSmooth ∧
    ∀ (J : Type) [Finite J] [Nonempty J],
      HasDerivAlongField J ∧
      (∀ q : ℕ∞, IsStarClosedSubalgebraSet (smoothOfENatOrder (J := J) q)) ∧
      LeibnizRules J ∧ ChainRuleHolds J ∧ ExpAndInvSmooth J ∧
      PolynomialAndBondWeightSmooth J ∧ FieldsSkewAdjoint J ∧
      SeriesSmooth J ∧ PartialVariablesSmooth J
end FieldCalculus
end YangMills.Construction.SpinHarmonics
end
