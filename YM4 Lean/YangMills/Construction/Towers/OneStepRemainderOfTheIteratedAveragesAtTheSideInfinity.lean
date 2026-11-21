import YangMills.Construction.Towers.OneStepRemainderOfTheIteratedAveragesOnASide
import YangMills.Construction.Towers.SignsOfTheLeftChartAndOfTheDifferentialsOfTheAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def StepRemainderAtInfiniteSide : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k →
    ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
      ∀ A ∈ complexEdgeForms (meshAt L k j),
        maxOperatorNorm A ≤ ENNReal.ofReal (stepRemainderRadius L / 2) →
          expForm A ∈ nearIdentityPolydisc L k j (polydiscRadius L) c ∧
            Matrices.ComplexMatrix2.operatorNorm
                (Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries (smoothingMap L k j (expForm A) c) -
                  linearSmoothing L A c) ≤
              stepRemainderConstant L * (maxOperatorNorm A).toReal ^ 2
end YangMills.Construction.Tower.FullSpace
end
