import YangMills.Construction.Towers.TheFamiliesOfTheTotalNormaliser
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices YangMills.Construction.PeriodicOperators.Tempered
def NormaliserFamilyHessianOnTop : Prop :=
  ∀ L m k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 1 ≤ k →
    Set.BijOn (fun B : UnitEdge L m → ComplexMatrix2 => B ∘ topEdgeEquivUnit L m k)
        (edgeFormSpace L m 0 0 : Set (UnitEdge L m → ComplexMatrix2))
        (edgeFormSpace L m k k : Set (Edge L m k k → ComplexMatrix2)) ∧
      ∀ B ∈ edgeFormSpace L m 0 0, ∀ B' ∈ edgeFormSpace L m 0 0,
        PeriodicOperators.Tempered.hessianAtIdentity (logNormaliserFamily L k) m B B' =
          Tower.leftSecondDeriv (k := k) (j := k) (logTotalNormaliserRatio L m k)
            (Tower.trivialField L m k k)
            (B ∘ topEdgeEquivUnit L m k) (B' ∘ topEdgeEquivUnit L m k)
end YangMills.Construction.Tower
end
