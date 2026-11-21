import YangMills.Construction.Lattice.LieValuedBondFunctions
import YangMills.Construction.Lattice.LinearisedConstraint
import YangMills.Construction.Lattice.SettingOfTheFibresOfTheAverage
import YangMills.Construction.Matrices.HaarExpChartDensity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set PeriodicLattice
namespace AverageFibres
variable {L m K j : ℕ}
def realFormValues (a : RealLieForm L m K j) : BondAtLevel L m K j → Matrices.ComplexMatrix2 :=
  fun b => (LieBondFunction.onBond (complexify a) b : Matrices.ComplexMatrix2)
def formsInPiBall (L m K j : ℕ) : Set (RealLieForm L m K j) :=
  {ν | ∀ c, ν c ∈ Matrices.ComplexMatrix2.lieBallPi}
def expMul (ν : RealLieForm L m K j) (W : PositiveBondField L m K j) :
    PositiveBondField L m K j :=
  fun c => Matrices.ComplexMatrix2.expChart (ν c) * W c
def haarDensityOf (ν : RealLieForm L m K j) : ℝ :=
  ∏ᶠ c, Matrices.ComplexMatrix2.haarExpDensity (ν c).toMatrix
def submersionSet (L m K k : ℕ) : Set (PositiveBondField L m K k) :=
  {v | (∀ c : PositivelyOrientedBond L m (levelDepth K (k + 1)),
      (gaugeFieldOfPositive v : BondAtLevel L m K k → Matrices.ComplexMatrix2) ∈
        smallPlaquetteFields (Averaging.smoothingRadius L) c.1) ∧
    ∀ ν : RealLieForm L m K (k + 1), ∃ X : RealLieForm L m K k,
      ∀ c : PositivelyOrientedBond L m (levelDepth K (k + 1)),
        linearizedConstraint (gaugeFieldOfPositive v) (realFormValues X) c.1 = (ν c).toMatrix}
structure FibreChart (k : ℕ) (W : PositiveBondField L m K (k + 1)) where
  Param : Type
  [instNormedAddCommGroup : NormedAddCommGroup Param]
  [instInnerProductSpace : InnerProductSpace ℝ Param]
  [instFiniteDimensional : FiniteDimensional ℝ Param]
  [instMeasurableSpace : MeasurableSpace Param]
  [instBorelSpace : BorelSpace Param]
  source : Set (Param × RealLieForm L m K (k + 1))
  isOpen_source : IsOpen source
  source_subset : source ⊆ univ ×ˢ formsInPiBall L m K (k + 1)
  toFun : Param × RealLieForm L m K (k + 1) → PositiveBondField L m K k
  isOpenEmbedding_toFun : Topology.IsOpenEmbedding (source.domRestrict toFun)
  toFun_mem : ∀ p ∈ source, toFun p ∈ submersionSet L m K k
  weight : Param × RealLieForm L m K (k + 1) → ℝ
  continuousOn_weight : ContinuousOn weight source
  weight_nonneg : ∀ p ∈ source, 0 ≤ weight p
  blockAverageMap_toFun : ∀ p ∈ source, blockAverageMap k (toFun p) = expMul p.2 W
  integral_eq : ∀ f : PositiveBondField L m K k → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) →
    (∀ x, x ∉ toFun '' source → f x = 0) →
      Integrable (fun p => f (toFun p) * weight p)
          ((volume.prod (realLieFormMeasure L m K (k + 1))).restrict source) ∧
        ∫ x, f x ∂gaugeFieldHaar L m (levelDepth K k) =
          ∫ p in source, f (toFun p) * weight p ∂volume.prod (realLieFormMeasure L m K (k + 1))
attribute [instance] FibreChart.instNormedAddCommGroup FibreChart.instInnerProductSpace
  FibreChart.instFiniteDimensional FibreChart.instMeasurableSpace
  FibreChart.instBorelSpace
namespace FibreChart
variable {k : ℕ} {W : PositiveBondField L m K (k + 1)} (u : FibreChart k W)
def range : Set (PositiveBondField L m K k) := u.toFun '' u.source
def sliceMeasure (ν : RealLieForm L m K (k + 1)) : Measure (PositiveBondField L m K k) :=
  (((volume : Measure u.Param).restrict {α | (α, ν) ∈ u.source}).withDensity
      fun α => ENNReal.ofReal (u.weight (α, ν))).map fun α => u.toFun (α, ν)
def fibreMeasure (W' : PositiveBondField L m K (k + 1)) : Measure (PositiveBondField L m K k) :=
  open Classical in
  if h : ∃ ν ∈ formsInPiBall L m K (k + 1), W' = expMul ν W then
    ENNReal.ofReal (haarDensityOf h.choose)⁻¹ • u.sliceMeasure h.choose
  else 0
end FibreChart
end AverageFibres
end YangMills.Construction
end
