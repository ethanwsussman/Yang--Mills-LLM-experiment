import YangMills.Construction.Functions.SmearingFilterWeight
import Mathlib
set_option autoImplicit false
open YangMills.Construction.TriangleKernel (smearingSeq tentFourierCoeff)
open YangMills.Construction.SmearingFilter (absCoeffSum filterSeries weightSeries)
noncomputable section
namespace YangMills.Construction.SmearingFilter.SeriesConvergence
def AbsCoeffSumFacts : Prop :=
  (Summable fun j : ℤ => ‖|(smearingSeq j : ℝ)| * (tentFourierCoeff j).re‖) ∧
  HasSum (fun j : ℤ => ((|(smearingSeq j : ℝ)| : ℝ) : ℂ) * tentFourierCoeff j)
    (absCoeffSum : ℂ)
def FilterSeriesFacts : Prop :=
  (∀ (j : ℤ) (u : ℝ),
    ‖(smearingSeq j : ℂ) * tentFourierCoeff j * Complex.exp (Complex.I * j * u)‖ ≤
      |(smearingSeq j : ℝ)| * (tentFourierCoeff j).re) ∧
  (∀ u : ℝ, Summable fun j : ℤ =>
    ‖(smearingSeq j : ℂ) * tentFourierCoeff j * Complex.exp (Complex.I * j * u)‖) ∧
  (∀ u : ℝ, HasSum
    (fun j : ℤ =>
      (smearingSeq j : ℂ) * tentFourierCoeff j * Complex.exp (Complex.I * j * u))
    (filterSeries u)) ∧
  TendstoUniformly
    (fun (s : Finset ℤ) (u : ℝ) => ∑ j ∈ s,
      (smearingSeq j : ℂ) * tentFourierCoeff j * Complex.exp (Complex.I * j * u))
    filterSeries Filter.atTop
def WeightSeriesFacts : Prop :=
  (∀ j : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(smearingSeq ((j : ℤ) + 1) : ℂ) * tentFourierCoeff ((j : ℤ) + 1) * (t : ℂ) ^ j‖ ≤
      |(smearingSeq ((j : ℤ) + 1) : ℝ)| * (tentFourierCoeff ((j : ℤ) + 1)).re) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) 1, Summable fun j : ℕ =>
    ‖(smearingSeq ((j : ℤ) + 1) : ℂ) * tentFourierCoeff ((j : ℤ) + 1) * (t : ℂ) ^ j‖) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) 1, HasSum
    (fun j : ℕ => 2 *
      ((smearingSeq ((j : ℤ) + 1) : ℂ) * tentFourierCoeff ((j : ℤ) + 1) * (t : ℂ) ^ j))
    (weightSeries t)) ∧
  TendstoUniformlyOn
    (fun (s : Finset ℕ) (t : ℝ) => 2 * ∑ j ∈ s,
      (smearingSeq ((j : ℤ) + 1) : ℂ) * tentFourierCoeff ((j : ℤ) + 1) * (t : ℂ) ^ j)
    weightSeries Filter.atTop (Set.Icc 0 1)
def SeriesConverge : Prop :=
  AbsCoeffSumFacts ∧ FilterSeriesFacts ∧ WeightSeriesFacts
end YangMills.Construction.SmearingFilter.SeriesConvergence
