import YangMills.Construction.Towers.CovarianceOfTheDerivativesOfTheActionOnTheSides
import YangMills.Construction.Towers.ExpansionOfTheMoveOnASide
import YangMills.Construction.Towers.GaugeConditionsOfTheAlgebraOfTheLeftChartOnASide
import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LeftChartAlgebra.DerivativeCovariance
variable {L n k j : ℕ}
theorem conjugateBy_add (V X Y : Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2.conjugateBy V (X + Y) =
      Matrices.ComplexMatrix2.conjugateBy V X + Matrices.ComplexMatrix2.conjugateBy V Y := by
  simp only [Matrices.ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (V X : Matrices.ComplexMatrix2) (c : ℂ) :
    Matrices.ComplexMatrix2.conjugateBy V (c • X) = c • Matrices.ComplexMatrix2.conjugateBy V X := by
  simp only [Matrices.ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
theorem adjointForm_linear_combination (u : Tower.Vertex L n k j → Matrices.ComplexMatrix2)
    (B B' : Tower.Edge L n k j → Matrices.ComplexMatrix2) (s t : ℂ) :
    Tower.adjointForm u (s • B + t • B') = s • Tower.adjointForm u B + t • Tower.adjointForm u B' := by
  funext e
  by_cases he : PeriodicLattice.Bond.IsPositivelyOriented e
  · simp [Tower.adjointForm, Tower.extendOddly, he, conjugateBy_add, conjugateBy_smul]
  · simp [Tower.adjointForm, Tower.extendOddly, he, conjugateBy_add, conjugateBy_smul, add_comm]
theorem adjointForm_smul (u : Tower.Vertex L n k j → Matrices.ComplexMatrix2)
    (B : Tower.Edge L n k j → Matrices.ComplexMatrix2) (t : ℂ) :
    Tower.adjointForm u (t • B) = t • Tower.adjointForm u B := by
  funext e
  by_cases he : PeriodicLattice.Bond.IsPositivelyOriented e
  · simp [Tower.adjointForm, Tower.extendOddly, he, conjugateBy_smul]
  · simp [Tower.adjointForm, Tower.extendOddly, he, conjugateBy_smul]
theorem complexAction_expTwist_gaugeTransform
    (hCovar : Tower.LeftChartAlgebra.GaugeCovariance L n k j)
    (hEquiv : Tower.LeftChartFacts.GaugeEquivarianceForms L n k j)
    (hTwist : Tower.LeftChartAlgebra.TwistExpansion L n k j)
    {U : Tower.Edge L n k j → Matrices.ComplexMatrix2}
    {u : Tower.Vertex L n k j → Matrices.ComplexMatrix2}
    (hU : U ∈ Tower.fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hu : PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup u)
    {C : Tower.Edge L n k j → Matrices.ComplexMatrix2} (hC : C ∈ Tower.complexEdgeForms L n k j) :
    Tower.complexAction
        (PeriodicLattice.expTwist (Tower.adjointForm u C) (PeriodicLattice.gaugeTransform u U)) =
      Tower.complexAction (PeriodicLattice.expTwist C U) := by
  rw [(hEquiv u hu).1 U hU C hC]
  have hW : PeriodicLattice.expTwist C U ∈
      Tower.fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
    have h := (hTwist U 0 C hU (fun _ => Matrices.ComplexMatrix2.traceless.zero_mem) hC).1 1
    simpa using h
  unfold Tower.complexAction
  exact finsum_congr fun p => ((hCovar _ u hW hu).2 p).2
theorem derivativeCovarianceOnPeriodic_holds
    (hGauge : Tower.LeftChartAlgebra.GaugeConditionsFiniteSide)
    (hEquiv : Tower.GaugeEquivarianceFormsAllSides)
    (hTwist : Tower.TwistExpansionOnTorus.Claim) :
    Tower.LeftChartAlgebra.DerivativeCovarianceOnPeriodic := by
  intro L n k j hL hn hj U u B B' hU hu hB hB'
  have key : ∀ C ∈ Tower.complexEdgeForms L n k j,
      Tower.complexAction
          (PeriodicLattice.expTwist (Tower.adjointForm u C) (PeriodicLattice.gaugeTransform u U)) =
        Tower.complexAction (PeriodicLattice.expTwist C U) := fun C hC =>
    complexAction_expTwist_gaugeTransform (hGauge L n k j hL hn hj).1
      ((hEquiv L k j hL hj).1 n hn) (hTwist L n k j hL hn hj) hU hu hC
  have hs : ∀ t : ℂ, t • B ∈ Tower.complexEdgeForms L n k j := fun t =>
    (Tower.complexEdgeForms L n k j).smul_mem t hB
  constructor
  · show deriv (fun t : ℂ => Tower.complexAction (PeriodicLattice.expTwist
        (algebraMap ℂ ℂ t • Tower.adjointForm u B) (PeriodicLattice.gaugeTransform u U))) 0 =
      deriv (fun t : ℂ => Tower.complexAction
        (PeriodicLattice.expTwist (algebraMap ℂ ℂ t • B) U)) 0
    refine congrArg (fun f : ℂ → ℂ => deriv f 0) (funext fun t => ?_)
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [← adjointForm_smul, key _ (hs t)]
  · show deriv (fun s : ℂ => deriv (fun t : ℂ => Tower.complexAction (PeriodicLattice.expTwist
        (algebraMap ℂ ℂ s • Tower.adjointForm u B + algebraMap ℂ ℂ t • Tower.adjointForm u B')
        (PeriodicLattice.gaugeTransform u U))) 0) 0 =
      deriv (fun s : ℂ => deriv (fun t : ℂ => Tower.complexAction (PeriodicLattice.expTwist
        (algebraMap ℂ ℂ s • B + algebraMap ℂ ℂ t • B') U)) 0) 0
    refine congrArg (fun f : ℂ → ℂ => deriv f 0) (funext fun s => ?_)
    refine congrArg (fun f : ℂ → ℂ => deriv f 0) (funext fun t => ?_)
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [← adjointForm_linear_combination,
      key _ ((Tower.complexEdgeForms L n k j).add_mem (hs s)
        ((Tower.complexEdgeForms L n k j).smul_mem t hB'))]
end YangMills.Construction.Tower.LeftChartAlgebra.DerivativeCovariance
end
