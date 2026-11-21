import YangMills.Construction.Lattice.MinimalOrbitsOfTheConstantSequenceAtARadius
import YangMills.Construction.Lattice.RegularSetsOfTheWholeLattice
import YangMills.Construction.Lattice.SequencesAtACubeSizeAndAGap
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
structure CriticalFieldConstants where
  radiusMul : ℝ
  minPower : ℕ
  uniqueRadius : ℝ
  existRadius : ℕ → ℝ
instance : Nonempty CriticalFieldConstants := ⟨⟨0, 0, 0, fun _ => 0⟩⟩
def CriticalFieldExists (B a : ℝ) {L m : ℕ} (K k : ℕ) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    Prop :=
  ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ a →
    (∀ p : PlaquetteAtLevel L m K k,
        Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy V p - 1) < ε₁) →
      constantConstrainedFields K k V =
          {U | U ∈ gaugeFieldsAtLevel L m K 0 ∧
            blockFieldAtLevel (Averaging.smoothingRadius L) k U = V} ∧
        ∃ U, IsConstantCritical (Averaging.smoothingRadius L) K k (datumOnLevel K k V) U ∧
          U ∈ smallCurvatureConfigs L m K k (B * ε₁)
def CriticalFieldsOneOrbit (a : ℝ) {L m : ℕ} (K k : ℕ)
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) : Prop :=
  ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ a → ∀ U U' : BondAtLevel L m K 0 → Matrices.ComplexMatrix2,
    IsConstantCritical (Averaging.smoothingRadius L) K k (datumOnLevel K k V) U →
    IsConstantCritical (Averaging.smoothingRadius L) K k (datumOnLevel K k V) U' →
    U ∈ smallCurvatureConfigs L m K k ε₀ → U' ∈ smallCurvatureConfigs L m K k ε₀ →
      U' ∈ residualGaugeOrbit K k constantWholeTorus U
def CriticalFieldConstants.Valid (L : ℕ) (N : CriticalFieldConstants) : Prop :=
  6 ≤ N.radiusMul ∧ (∃ a : ℕ, N.minPower = L ^ a) ∧
    0 < N.uniqueRadius ∧ N.uniqueRadius ≤ 1 ∧
    ∀ ρ : ℕ, (∃ a : ℕ, ρ = L ^ a) → N.minPower ≤ ρ →
      0 < N.existRadius ρ ∧ N.radiusMul * N.existRadius ρ ≤ N.uniqueRadius ∧
      ∀ K m k : ℕ, 0 < K → 0 < m → 1 ≤ k → k ≤ K →
        6 * (ρ : ℝ) ≤ RegionChains.sitesPerAxis L m K k →
        ∀ V : BondAtLevel L m K k → Matrices.ComplexMatrix2, V ∈ gaugeFieldsAtLevel L m K k →
          CriticalFieldExists N.radiusMul (N.existRadius ρ) K k V ∧
            CriticalFieldsOneOrbit N.uniqueRadius K k V
def criticalFieldConstants (L : ℕ) : CriticalFieldConstants :=
  Classical.epsilon (CriticalFieldConstants.Valid L)
def criticalRadiusMul (L : ℕ) : ℝ := (criticalFieldConstants L).radiusMul
def criticalMinPower (L : ℕ) : ℕ := (criticalFieldConstants L).minPower
def criticalUniqueRadius (L : ℕ) : ℝ := (criticalFieldConstants L).uniqueRadius
def criticalExistRadius (L ρ : ℕ) : ℝ := (criticalFieldConstants L).existRadius ρ
end YangMills.Construction.PeriodicLattice
