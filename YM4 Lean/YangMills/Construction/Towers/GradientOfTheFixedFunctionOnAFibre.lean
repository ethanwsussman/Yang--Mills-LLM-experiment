import YangMills.Construction.Towers.GaussianIntegralsAndTheNormalisers
import Mathlib
noncomputable section
namespace YangMills.Construction.Tower
def GaugeFixedGradientOnFibre : Prop :=
  ∀ L m k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ i : ℕ, i + 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L m k (i + 1)) fun W =>
      ∃ g : edgeFormSpace L m k (i + 1),
        (g : Edge L m k (i + 1) → Matrices.ComplexMatrix2) =
            (chosenCriticalBranch L m k).energyGradient (i + 1) W ∧
          (PairedFunctionSpace.realTransposeMap (S := edgePairedSpace L m k i)
              (S' := edgePairedSpace L m k (i + 1))
              (constraintDifferential L m k i W) g).1 =
            leftGradient (fieldSpace L m k i) (fun V => (chosenGaugeFixedEnergy L m k i V : ℂ))
              (chosenProlong L m k i W)
end YangMills.Construction.Tower
end
