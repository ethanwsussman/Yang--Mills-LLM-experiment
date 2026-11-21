import YangMills.Construction.Lattice.WilsonGibbsMeasure
import YangMills.Construction.Probability.BoundedRealRandomVariable
import Mathlib
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def WilsonCumulantWellPosedness.statement : Prop :=
  (∀ (L m K : ℕ) (β : ℝ), 1 < L → 0 < m → 0 < K →
    (∀ U : Bond L m (K : ℤ) → Matrices.ComplexMatrix2,
      (Function.support fun p : Plaquette L m (K : ℤ) => plaquetteCost U p).Finite) ∧
    Integrable (boltzmannWeight β) (productHaarMeasure L m (K : ℤ)) ∧
    0 < partitionFunction L m K β ∧
    IsProbabilityMeasure (wilsonGibbsMeasure L m K β)) ∧
  (∀ (L m K : ℕ), 1 < L → 0 < m → 0 < K →
    ∀ σ : FourTorus L m ≃ FourTorus L m, IsSublatticeIsometry (K : ℤ) σ →
      ∀ b : Bond L m (K : ℤ), ∃ b' : Bond L m (K : ℤ),
        (b'.source : FourTorus L m) = σ.symm b.source ∧
          (b'.target : FourTorus L m) = σ.symm b.target) ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ)
    (X : Fin n → Ω → ℝ), 1 ≤ n → (∀ i, Probability.IsBoundedRealRV (X i)) →
    (∀ t : Fin n → ℂ, Integrable (fun ω => Complex.exp (∑ i, t i * (X i ω : ℂ))) ν) ∧
    Cumulants.momentGeneratingFunction ν X 0 = 1 ∧
    ContDiffAt ℂ (n : WithTop ℕ∞)
      (fun t : Fin n → ℂ => Complex.log (Cumulants.momentGeneratingFunction ν X t)) 0
end PeriodicLattice
end YangMills.Construction
