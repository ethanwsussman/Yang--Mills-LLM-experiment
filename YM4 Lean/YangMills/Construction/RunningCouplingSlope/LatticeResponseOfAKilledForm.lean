import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.OperatorsOfAStepAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
open Conventions FlatLinearization TorusFields TorusLumps
def latticeResponseOfAnnihilatedStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, IsAdmissibleBlockingFactor L →
    ∀ (h : BondKernel) (hl : LatticeBond → LatticeBond → ℝ)
    (G : (n : ℕ) → TorusBond (n * L) → TorusBond (n * L) → ℝ) (Gl : LatticeBond → LatticeBond → ℝ),
    IsFlowKernel h → TendstoLatticeKernel h hl → IsGreenFamily a L h hl G Gl →
    ∀ w : LatticeOneForm, FlatLinearization.HasPolynomialGrowth w → VanishesOnLatticeTrees L w →
      (∀ b, HasSum (fun c => hl b c * w c) 0) →
      ∀ b, HasSum (fun c => latticeResponseOfInverse a L Gl b c * latticeContourAverage L w c) (w b)
end YangMills.Construction.RunningCouplingSlope
end
