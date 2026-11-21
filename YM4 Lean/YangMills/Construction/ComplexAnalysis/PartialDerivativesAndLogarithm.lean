import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.PowerSeries.MultiIndexNotation
import Mathlib
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace ComplexVariables
variable {n : ℕ}
def IsHolomorphicScalar (U : Set (Coordinates.ComplexCoordinates n))
    (F : Coordinates.ComplexCoordinates n → ℂ) : Prop :=
  Coordinates.ComplexCoordinates.IsHolomorphicIn U ((Equiv.funUnique (Fin 1) ℂ).symm ∘ F)
def IsEntireFun (F : Coordinates.ComplexCoordinates n → ℂ) : Prop := IsHolomorphicScalar univ F
def diffQuot (F : Coordinates.ComplexCoordinates n → ℂ) (z : Coordinates.ComplexCoordinates n)
    (j : Fin n) (ζ : ℂ) : ℂ :=
  ζ⁻¹ * (F (z + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) - F z)
def HasPartialDeriv (U : Set (Coordinates.ComplexCoordinates n))
    (F : Coordinates.ComplexCoordinates n → ℂ) (j : Fin n) : Prop :=
  IsOpen U ∧ ∀ z ∈ U, ∃ l : ℂ, Tendsto (diffQuot F z j) (𝓝[≠] 0) (𝓝 l)
def partialDeriv (j : Fin n) (F : Coordinates.ComplexCoordinates n → ℂ) :
    Coordinates.ComplexCoordinates n → ℂ :=
  fun z => limUnder (𝓝[≠] (0 : ℂ)) (diffQuot F z j)
def iteratedPartials (l : List (Fin n)) (F : Coordinates.ComplexCoordinates n → ℂ) :
    Coordinates.ComplexCoordinates n → ℂ :=
  l.foldr partialDeriv F
def HasIteratedPartials (U : Set (Coordinates.ComplexCoordinates n)) :
    List (Fin n) → (Coordinates.ComplexCoordinates n → ℂ) → Prop
  | [], _ => IsOpen U
  | j :: l, F => HasIteratedPartials U l F ∧ HasPartialDeriv U (iteratedPartials l F) j
def partialOverFinset (J : Finset (Fin n)) (F : Coordinates.ComplexCoordinates n → ℂ) :
    Coordinates.ComplexCoordinates n → ℂ :=
  iteratedPartials (J.sort) F
def HasPartialOverFinset (U : Set (Coordinates.ComplexCoordinates n)) (J : Finset (Fin n))
    (F : Coordinates.ComplexCoordinates n → ℂ) : Prop :=
  HasIteratedPartials U (J.sort) F
def multiIndexSteps (α : PowerSeries.MultiIndex n) : List (Fin n) :=
  (List.finRange n).flatMap fun i => List.replicate (α i) i
def partialOfIndex (α : PowerSeries.MultiIndex n) (F : Coordinates.ComplexCoordinates n → ℂ) :
    Coordinates.ComplexCoordinates n → ℂ :=
  iteratedPartials (multiIndexSteps α) F
def HasPartialOfIndex (U : Set (Coordinates.ComplexCoordinates n)) (α : PowerSeries.MultiIndex n)
    (F : Coordinates.ComplexCoordinates n → ℂ) : Prop :=
  HasIteratedPartials U (multiIndexSteps α) F
def mixedPartialAtOrigin (F : Coordinates.ComplexCoordinates n → ℂ) : ℂ :=
  partialOverFinset Finset.univ F 0
def HasRealPartialDeriv (U' : Set (Coordinates.ComplexCoordinates n))
    (φ : Coordinates.ComplexCoordinates n → ℂ) (j : Fin n) : Prop :=
  Matrices.ComplexMatrix2.IsRelativelyOpen (Coordinates.ComplexCoordinates.realLocus n) U' ∧
    ∀ t ∈ U', ∃ l : ℂ, Tendsto (fun ζ : ℝ => diffQuot φ t j ζ) (𝓝[≠] 0) (𝓝 l)
def realPartialDeriv (j : Fin n) (φ : Coordinates.ComplexCoordinates n → ℂ) :
    Coordinates.ComplexCoordinates n → ℂ :=
  fun t => limUnder (𝓝[≠] (0 : ℝ)) fun ζ : ℝ => diffQuot φ t j ζ
def expComp {Ω : Type*} (u : Ω → ℂ) : Ω → ℂ := fun ω => Complex.exp (u ω)
def twoPiIMultiples : Set ℂ := {w | ∃ k : ℤ, w = k * (2 * Real.pi * Complex.I)}
def nonpositiveRayComplement : Set ℂ := {w | ∀ x : ℝ, x ≤ 0 → w ≠ x}
def logPrincipal (w : ℂ) : ℂ := Complex.log w
def absMonomial (z : Coordinates.ComplexCoordinates n) (α : PowerSeries.MultiIndex n) : ℝ :=
  PowerSeries.MultiIndex.monomial (fun i => ‖z i‖) α
def indicatorIndex (J : Finset (Fin n)) : PowerSeries.MultiIndex n :=
  fun i => if i ∈ J then 1 else 0
def singleIndex (j : Fin n) : PowerSeries.MultiIndex n := indicatorIndex {j}
def IsAbsSummable (c : PowerSeries.MultiIndex n → ℂ) : Prop := Summable fun α => ‖c α‖
def indexSum (c : PowerSeries.MultiIndex n → ℂ) : ℂ := ∑' α, c α
end ComplexVariables
end YangMills.Construction
