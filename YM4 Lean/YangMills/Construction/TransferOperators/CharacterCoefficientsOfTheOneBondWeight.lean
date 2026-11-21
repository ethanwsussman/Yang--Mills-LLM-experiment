import YangMills.Construction.InfiniteLattice.ModifiedBesselFunctionsAndCharacterCoefficients
import YangMills.Construction.TransferOperators.BondKernelAndLayerEnergy
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def besselRatioBound (β : ℝ) : ℝ := 4 / β + β
def bondWeightCharTerm (β : ℝ) (l : HalfNatural) (g : Matrices.ComplexMatrix2.specialUnitary) : ℂ :=
  ((2 * l.toReal + 1 : ℝ) : ℂ) * weightCharCoeff β l * spinCharacter l g
def ModBesselSeriesFacts : Prop :=
  ∀ (n : ℕ) (x : ℝ), 0 < x →
    HasSum (fun k : ℕ => (x / 2) ^ (n + 2 * k) / ((k.factorial : ℝ) * ((n + k).factorial : ℝ)))
        (modBesselI n x) ∧
      0 < modBesselI n x ∧
      (1 ≤ n → modBesselI (n - 1) x - modBesselI (n + 1) x =
        2 * (n : ℝ) / x * modBesselI n x) ∧
      modBesselI (n + 1) x ≤ x / (2 * ((n : ℝ) + 1)) * modBesselI n x ∧
      modBesselI n x ≤ (x / 2) ^ n / (n.factorial : ℝ) * Real.exp (x ^ 2 / 4)
def SingleLinkOpDiagonal (β : ℝ) : Prop :=
  (∀ (l : HalfNatural), ∀ ψ ∈ coeffSpanL2 l,
    TransferOperators.singleLinkOperator β ψ = weightCharCoeff β l • ψ) ∧
  ∀ F : Lp ℂ 2 Matrices.ComplexMatrix2.haarProb,
    HasSum (fun l : HalfNatural => weightCharCoeff β l • coeffProjection l F)
      (TransferOperators.singleLinkOperator β F)
def WeightCharCoeffBounds (β : ℝ) (l : HalfNatural) : Prop :=
  weightCharCoeff β l =
      ((2 * Real.exp (-β) / β * modBesselI (l.doubled + 1) β : ℝ) : ℂ) ∧
    0 < (weightCharCoeff β l).re ∧
    (weightCharCoeff β l).re ≤ 1 ∧
    (weightCharCoeff β l).re ≤
      (β / 2) ^ l.doubled * Real.exp (β ^ 2 / 4) / ((l.doubled + 1).factorial : ℝ) ∧
    max ((weightCharCoeff β ⟨l.doubled + 1⟩).re / (weightCharCoeff β l).re)
        ((weightCharCoeff β l).re / (weightCharCoeff β ⟨l.doubled + 1⟩).re) ≤
      4 * (l.toReal + 1) / β + β ∧
    4 * (l.toReal + 1) / β + β ≤ besselRatioBound β * (1 + l.toReal)
def WeightCharCoeffSummable (β : ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → 0 < b →
    Summable fun l : HalfNatural => (2 * l.toReal + 1) ^ a * (weightCharCoeff β l).re ^ b
def BondWeightCharExpansion (β : ℝ) : Prop :=
  (∀ g : Matrices.ComplexMatrix2.specialUnitary,
    Summable fun l : HalfNatural => ‖bondWeightCharTerm β l g‖) ∧
  TendstoUniformly
    (fun (s : Finset HalfNatural) (g : Matrices.ComplexMatrix2.specialUnitary) =>
      ∑ l ∈ s, bondWeightCharTerm β l g)
    (InfiniteLattice.singleBondWeight β) atTop
def BondWeightCharCoeffStatement : Prop :=
  ModBesselSeriesFacts ∧
  ∀ β : ℝ, 0 < β →
    SingleLinkOpDiagonal β ∧
    (∀ l : HalfNatural, WeightCharCoeffBounds β l) ∧
    4 ≤ besselRatioBound β ∧
    WeightCharCoeffSummable β ∧
    BondWeightCharExpansion β
end YangMills.Construction.SpinHarmonics
end
