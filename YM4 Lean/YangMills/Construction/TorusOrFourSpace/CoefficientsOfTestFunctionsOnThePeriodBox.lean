import YangMills.Construction.TorusOrFourSpace.CutOffsOnAProductOfOpenSets
import YangMills.Construction.TorusOrFourSpace.PeriodBoxCharactersAndCoefficients
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PeriodCell
def fourierMultiplier {p : ℕ+} (P : ℝ) (k : IntCoords p) (α : CoordIndex p) : ℂ :=
  ∏ j, (2 * Real.pi * Complex.I * (k j : ℂ) / (P : ℂ)) ^ α j
def FourierCoeffBounds : Prop :=
  ∀ (D : Params) (p : ℕ+) (P : ℝ), 0 < P →
    (∀ k : IntCoords p,
      Kind.Tuple.IsComplexLinearForm
        (fun F : cellTestFns D p P => fourierCoeff D P F.1 k)) ∧
    (∀ F ∈ cellTestFns D p P, ∀ k : IntCoords p,
      ENNReal.ofReal ‖fourierCoeff D P F k‖ ≤
        Kind.Tuple.cNorm D Kind.euclidean 0 F) ∧
    (∀ (α : CoordIndex p) (k : IntCoords p),
      Coords.iterPartial α (fourierChar P k) =
        fun u => fourierMultiplier P k α * fourierChar P k u) ∧
    (∀ F ∈ cellTestFns D p P, ∀ (α : CoordIndex p) (k : IntCoords p),
      fourierCoeff D P (Kind.Tuple.partialDeriv D Kind.euclidean α F) k =
        fourierMultiplier P k α * fourierCoeff D P F k) ∧
    (∀ F ∈ cellTestFns D p P, ∀ (α : CoordIndex p) (t : ℕ+),
      Coords.iterPartial α (fourierPartialSum D P F t) =
        fourierPartialSum D P (Kind.Tuple.partialDeriv D Kind.euclidean α F) t) ∧
    (∀ F ∈ cellTestFns D p P, ∀ k : IntCoords p, k ≠ 0 → ∀ ν : ℕ,
      ENNReal.ofReal ‖fourierCoeff D P F k‖ ≤
        ENNReal.ofReal ((P / (2 * Real.pi * (k.maxAbs : ℝ))) ^ ν) *
          Kind.Tuple.cNorm D Kind.euclidean ν F) ∧
    (∀ s : ℕ+, Set.encard {k' : IntCoords p | k'.maxAbs = (s : ℕ)} ≤
      ((2 * (4 * (p : ℕ)) * (3 * (s : ℕ)) ^ (4 * (p : ℕ) - 1) : ℕ) : ℕ∞)) ∧
    (Summable (fun s : ℕ+ => (((s : ℕ) : ℝ) ^ 2)⁻¹) ∧
      ∑' s : ℕ+, (((s : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2) ∧
    (Summable (fun k' : {k' : IntCoords p // k' ≠ 0} =>
        ((k'.1.maxAbs : ℝ) ^ (4 * (p : ℕ) + 1))⁻¹) ∧
      ∑' k' : {k' : IntCoords p // k' ≠ 0}, ((k'.1.maxAbs : ℝ) ^ (4 * (p : ℕ) + 1))⁻¹ ≤
        4 * (4 * ((p : ℕ) : ℝ)) * 3 ^ (4 * (p : ℕ) - 1)) ∧
    (∀ F ∈ cellTestFns D p P, Summable fun k' : IntCoords p => ‖fourierCoeff D P F k'‖) ∧
    (∀ h : Fin (p : ℕ) → Kind.euclidean.Pt D → ℂ,
      (∀ i, h i ∈ Kind.Tuple.singleTestFns D Kind.euclidean (cell P)) →
        Kind.Tuple.tensorProd D Kind.euclidean h ∈ cellTestFns D p P ∧
        ∀ k : IntCoords p,
          fourierCoeff D P (Kind.Tuple.tensorProd D Kind.euclidean h) k =
            ∏ i, fourierCoeff (p := 1) D P
              (Kind.Tuple.ofSingle D Kind.euclidean (h i)) (k.block i))
end YangMills.Construction.PeriodicSpace.PeriodCell
