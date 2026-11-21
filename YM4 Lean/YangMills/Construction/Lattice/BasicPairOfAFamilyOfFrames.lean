import YangMills.Construction.Lattice.BasicBackgroundInTheMixedAxialAndLandauGauge
import YangMills.Construction.Lattice.ObjectsOfTheCentralBox
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CentralBlock
open CubesOfStep
variable (c : ParameterChoice.ChoiceUpToDegreeConstants) {m K : ℕ} {x : ℕ → ℝ} {k : ℕ}
  (S : LabelAtLevel c m K x k) (Q : Set (Set (FourTorus c.L m)))
def IsFramedBasePair (α : ℝ) (ρ : ↥Q → SignedFrame)
    (V W : BondAtLevel c.L m K k → Matrices.ComplexMatrix2)
    (U : BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  IsBoxMinimizer c S Q (⋃₀ Q) V W ∧
    ∀ Y : ↥Q, IsMixedAxialLandauBackground c.εv α (ρ Y) K k (Nat.log c.L c.M₁) (⋃₀ Q)
      (S.innerBoxIn c.r x Q Y.1) W U
end YangMills.Construction.PeriodicLattice.CentralBlock
