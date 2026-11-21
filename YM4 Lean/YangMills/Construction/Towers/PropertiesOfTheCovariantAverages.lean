import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace PairedFunctionSpace
def HasTransposeProduct (S S' : Tower.PairedFunctionSpace)
    (f : (S.index → Matrices.ComplexMatrix2) → S'.index → Matrices.ComplexMatrix2) (c : ℂ) :
    Prop :=
  ∃ T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule,
    (∀ v : S.complexSubmodule, (T v : S'.index → Matrices.ComplexMatrix2) = f v) ∧
    Tower.PairedFunctionSpace.PreservesFiniteSupport T ∧
    ∀ w : S'.complexSubmodule,
      (T (Tower.PairedFunctionSpace.transposeMap T w) : S'.index → Matrices.ComplexMatrix2) =
        c • (w : S'.index → Matrices.ComplexMatrix2)
end PairedFunctionSpace
namespace CovariantSmoothingProperties
def OneStepRelations (L n k j : ℕ) : Prop :=
  ∀ V ∈ Tower.smallComplexFields L n k j,
    (∀ φ : Tower.Vertex L n k j → Matrices.ComplexMatrix2,
      (∀ x, φ x ∈ Matrices.ComplexMatrix2.traceless) →
      Tower.complexSmoothingDeriv V (Tower.covDiff V φ) =
        Tower.covDiff (PeriodicLattice.complexBlockAverageStep j V)
          (Tower.restrictVertexFunction (j + 1) φ) ∧
      Tower.contourLogDrift V (Tower.covDiff V φ) =
        Tower.adjointCubeAverage V φ - Tower.restrictVertexFunction (j + 1) φ ∧
      Tower.covariantSmoothingDeriv V (Tower.covDiff V φ) =
        Tower.covDiff (PeriodicLattice.complexBlockAverageStep j V)
          (Tower.adjointCubeAverage V φ)) ∧
    Tower.PairedFunctionSpace.HasTransposeProduct (Tower.pairedFunctions (Tower.Vertex L n k j))
      (Tower.pairedFunctions (Tower.Vertex L n k (j + 1))) (Tower.adjointCubeAverage V)
      (PeriodicLattice.inverseFourthPowerWeight L)
def IterateRelations (L n k j : ℕ) : Prop :=
  ∀ U ∈ Tower.smallIterateFields L n k,
    (∀ A ∈ Tower.complexEdgeForms L n k 0,
      Tower.iterCovariantDeriv L n k U j A =
        Tower.complexIterDeriv L n k j U A +
          Tower.covDiff (PeriodicLattice.complexBlockFieldAtLevel j U)
            (Tower.iterContourLogDrift L n k U j A)) ∧
    (∀ φ : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2,
      (∀ x, φ x ∈ Matrices.ComplexMatrix2.traceless) →
      Tower.iterAdjointCubeAverage L n k U j φ =
        Tower.restrictVertexFunction j φ +
          Tower.iterContourLogDrift L n k U j (Tower.covDiff U φ) ∧
      Tower.iterCovariantDeriv L n k U j (Tower.covDiff U φ) =
        Tower.covDiff (PeriodicLattice.complexBlockFieldAtLevel j U)
          (Tower.iterAdjointCubeAverage L n k U j φ)) ∧
    Tower.PairedFunctionSpace.HasTransposeProduct (Tower.pairedFunctions (Tower.Vertex L n k 0))
      (Tower.pairedFunctions (Tower.Vertex L n k j)) (Tower.iterAdjointCubeAverage L n k U j)
      (PeriodicLattice.inverseFourthPowerWeight L ^ j)
def GaugeEquivariance (L n k j : ℕ) : Prop :=
  ∀ U ∈ Tower.smallIterateFields L n k, ∀ g ∈ Tower.gaugeGroupAt L n k 0,
    PeriodicLattice.gaugeTransform g U ∈ Tower.smallIterateFields L n k →
    (∀ φ : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2,
      (∀ x, φ x ∈ Matrices.ComplexMatrix2.traceless) →
      Tower.covDiff (PeriodicLattice.gaugeTransform g U) (Tower.adjointVertexFn g φ) =
        Tower.adjointForm g (Tower.covDiff U φ) ∧
      Tower.iterAdjointCubeAverage L n k (PeriodicLattice.gaugeTransform g U) j
          (Tower.adjointVertexFn g φ) =
        Tower.adjointVertexFn (Tower.restrictVertexFunction j g)
          (Tower.iterAdjointCubeAverage L n k U j φ)) ∧
    ∀ A ∈ Tower.complexEdgeForms L n k 0,
      Tower.complexIterDeriv L n k j (PeriodicLattice.gaugeTransform g U) (Tower.adjointForm g A) =
        Tower.adjointForm (Tower.restrictVertexFunction j g)
          (Tower.complexIterDeriv L n k j U A) ∧
      Tower.iterCovariantDeriv L n k (PeriodicLattice.gaugeTransform g U) j
          (Tower.adjointForm g A) =
        Tower.adjointForm (Tower.restrictVertexFunction j g)
          (Tower.iterCovariantDeriv L n k U j A) ∧
      Tower.iterContourLogDrift L n k (PeriodicLattice.gaugeTransform g U) j
          (Tower.adjointForm g A) =
        Tower.adjointVertexFn (Tower.restrictVertexFunction j g)
          (Tower.iterContourLogDrift L n k U j A)
def IsometryEquivariance (L n k j : ℕ) : Prop :=
  ∀ s : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
    Tower.IsDistancePreserving s → Tower.MapsSublatticeOnto k k s →
    ∀ U ∈ Tower.smallIterateFields L n k,
      (∀ φ : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2,
        (∀ x, φ x ∈ Matrices.ComplexMatrix2.traceless) →
        Tower.covDiff (Tower.pushField s U) (Tower.pushSiteFunction s φ) =
          Tower.isometryOnTangent s U (Tower.covDiff U φ) ∧
        Tower.iterAdjointCubeAverage L n k (Tower.pushField s U) j (Tower.pushSiteFunction s φ) =
          Tower.pushSiteFunction s (Tower.iterAdjointCubeAverage L n k U j φ)) ∧
      ∀ A ∈ Tower.complexEdgeForms L n k 0,
        Tower.complexIterDeriv L n k j (Tower.pushField s U) (Tower.isometryOnTangent s U A) =
          Tower.isometryOnTangent s (PeriodicLattice.complexBlockFieldAtLevel j U)
            (Tower.complexIterDeriv L n k j U A) ∧
        Tower.iterCovariantDeriv L n k (Tower.pushField s U) j (Tower.isometryOnTangent s U A) =
          Tower.isometryOnTangent s (PeriodicLattice.complexBlockFieldAtLevel j U)
            (Tower.iterCovariantDeriv L n k U j A) ∧
        Tower.iterContourLogDrift L n k (Tower.pushField s U) j (Tower.isometryOnTangent s U A) =
          Tower.pushSiteFunction s (Tower.iterContourLogDrift L n k U j A)
end CovariantSmoothingProperties
namespace FullSpace.CovariantSmoothingProperties
def OneStepRelations (L k j : ℕ) : Prop :=
  ∀ V ∈ Tower.FullSpace.smallComplexFields L k j,
    (∀ φ : Tower.FullSpace.Vertex L k j → Matrices.ComplexMatrix2,
      (∀ x, φ x ∈ Matrices.ComplexMatrix2.traceless) →
      Tower.FullSpace.complexSmoothingDeriv V (Tower.FullSpace.covDiff V φ) =
        Tower.FullSpace.covDiff (Tower.FullSpace.smoothingMap L k j V)
          (Tower.FullSpace.restrictVertexFunction (Tower.meshAt L k (j + 1)) φ) ∧
      Tower.FullSpace.contourLogDrift V (Tower.FullSpace.covDiff V φ) =
        Tower.FullSpace.adjointCubeAverage V φ -
          Tower.FullSpace.restrictVertexFunction (Tower.meshAt L k (j + 1)) φ ∧
      Tower.FullSpace.covariantSmoothingDeriv V (Tower.FullSpace.covDiff V φ) =
        Tower.FullSpace.covDiff (Tower.FullSpace.smoothingMap L k j V)
          (Tower.FullSpace.adjointCubeAverage V φ)) ∧
    Tower.PairedFunctionSpace.HasTransposeProduct
      (Tower.pairedFunctions (Tower.FullSpace.Vertex L k j))
      (Tower.pairedFunctions (Tower.FullSpace.Vertex L k (j + 1)))
      (Tower.FullSpace.adjointCubeAverage V) (PeriodicLattice.inverseFourthPowerWeight L)
def IterateRelations (L k j : ℕ) : Prop :=
  ∀ U ∈ Tower.FullSpace.smallIterateFields L k,
    (∀ A ∈ Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0),
      Tower.FullSpace.iterCovariantDeriv L k U j A =
        Tower.FullSpace.complexIterDeriv L k j U A +
          Tower.FullSpace.covDiff (Tower.FullSpace.complexIter L k j U)
            (Tower.FullSpace.iterContourLogDrift L k U j A)) ∧
    (∀ φ : Tower.FullSpace.Vertex L k 0 → Matrices.ComplexMatrix2,
      (∀ x, φ x ∈ Matrices.ComplexMatrix2.traceless) →
      Tower.FullSpace.iterAdjointCubeAverage L k U j φ =
        Tower.FullSpace.restrictVertexFunction (Tower.meshAt L k j) φ +
          Tower.FullSpace.iterContourLogDrift L k U j (Tower.FullSpace.covDiff U φ) ∧
      Tower.FullSpace.iterCovariantDeriv L k U j (Tower.FullSpace.covDiff U φ) =
        Tower.FullSpace.covDiff (Tower.FullSpace.complexIter L k j U)
          (Tower.FullSpace.iterAdjointCubeAverage L k U j φ)) ∧
    Tower.PairedFunctionSpace.HasTransposeProduct
      (Tower.pairedFunctions (Tower.FullSpace.Vertex L k 0))
      (Tower.pairedFunctions (Tower.FullSpace.Vertex L k j))
      (Tower.FullSpace.iterAdjointCubeAverage L k U j)
      (PeriodicLattice.inverseFourthPowerWeight L ^ j)
def GaugeEquivariance (L k j : ℕ) : Prop :=
  ∀ U ∈ Tower.FullSpace.smallIterateFields L k, ∀ g ∈ Tower.FullSpace.gaugeGroupAt L k 0,
    Tower.FullSpace.gaugeAct g U ∈ Tower.FullSpace.smallIterateFields L k →
    (∀ φ : Tower.FullSpace.Vertex L k 0 → Matrices.ComplexMatrix2,
      (∀ x, φ x ∈ Matrices.ComplexMatrix2.traceless) →
      Tower.FullSpace.covDiff (Tower.FullSpace.gaugeAct g U) (Tower.FullSpace.adjointVertexFn g φ) =
        Tower.FullSpace.adjointForm g (Tower.FullSpace.covDiff U φ) ∧
      Tower.FullSpace.iterAdjointCubeAverage L k (Tower.FullSpace.gaugeAct g U) j
          (Tower.FullSpace.adjointVertexFn g φ) =
        Tower.FullSpace.adjointVertexFn
          (Tower.FullSpace.restrictVertexFunction (Tower.meshAt L k j) g)
          (Tower.FullSpace.iterAdjointCubeAverage L k U j φ)) ∧
    ∀ A ∈ Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0),
      Tower.FullSpace.complexIterDeriv L k j (Tower.FullSpace.gaugeAct g U)
          (Tower.FullSpace.adjointForm g A) =
        Tower.FullSpace.adjointForm
          (Tower.FullSpace.restrictVertexFunction (Tower.meshAt L k j) g)
          (Tower.FullSpace.complexIterDeriv L k j U A) ∧
      Tower.FullSpace.iterCovariantDeriv L k (Tower.FullSpace.gaugeAct g U) j
          (Tower.FullSpace.adjointForm g A) =
        Tower.FullSpace.adjointForm
          (Tower.FullSpace.restrictVertexFunction (Tower.meshAt L k j) g)
          (Tower.FullSpace.iterCovariantDeriv L k U j A) ∧
      Tower.FullSpace.iterContourLogDrift L k (Tower.FullSpace.gaugeAct g U) j
          (Tower.FullSpace.adjointForm g A) =
        Tower.FullSpace.adjointVertexFn
          (Tower.FullSpace.restrictVertexFunction (Tower.meshAt L k j) g)
          (Tower.FullSpace.iterContourLogDrift L k U j A)
def IsometryEquivariance (L k j : ℕ) : Prop :=
  ∀ s : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace,
    Tower.FullSpace.IsDistancePreserving s →
    Tower.FullSpace.MapsSublatticeOnto (Tower.meshAt L k k) s →
    ∀ U ∈ Tower.FullSpace.smallIterateFields L k,
      (∀ φ : Tower.FullSpace.Vertex L k 0 → Matrices.ComplexMatrix2,
        (∀ x, φ x ∈ Matrices.ComplexMatrix2.traceless) →
        Tower.FullSpace.covDiff (Tower.FullSpace.pushField s U)
            (Tower.FullSpace.pushSiteFunction s φ) =
          Tower.FullSpace.isometryOnTangent s U (Tower.FullSpace.covDiff U φ) ∧
        Tower.FullSpace.iterAdjointCubeAverage L k (Tower.FullSpace.pushField s U) j
            (Tower.FullSpace.pushSiteFunction s φ) =
          Tower.FullSpace.pushSiteFunction s (Tower.FullSpace.iterAdjointCubeAverage L k U j φ)) ∧
      ∀ A ∈ Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0),
        Tower.FullSpace.complexIterDeriv L k j (Tower.FullSpace.pushField s U)
            (Tower.FullSpace.isometryOnTangent s U A) =
          Tower.FullSpace.isometryOnTangent s (Tower.FullSpace.complexIter L k j U)
            (Tower.FullSpace.complexIterDeriv L k j U A) ∧
        Tower.FullSpace.iterCovariantDeriv L k (Tower.FullSpace.pushField s U) j
            (Tower.FullSpace.isometryOnTangent s U A) =
          Tower.FullSpace.isometryOnTangent s (Tower.FullSpace.complexIter L k j U)
            (Tower.FullSpace.iterCovariantDeriv L k U j A) ∧
        Tower.FullSpace.iterContourLogDrift L k (Tower.FullSpace.pushField s U) j
            (Tower.FullSpace.isometryOnTangent s U A) =
          Tower.FullSpace.pushSiteFunction s (Tower.FullSpace.iterContourLogDrift L k U j A)
end FullSpace.CovariantSmoothingProperties
def CovariantSmoothingProperties.Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ n k : ℕ, 0 < n →
      (∀ j < k, Tower.CovariantSmoothingProperties.OneStepRelations L n k j) ∧
      ∀ j ≤ k, Tower.CovariantSmoothingProperties.IterateRelations L n k j ∧
        Tower.CovariantSmoothingProperties.GaugeEquivariance L n k j ∧
        Tower.CovariantSmoothingProperties.IsometryEquivariance L n k j) ∧
    ∀ k : ℕ,
      (∀ j < k, Tower.FullSpace.CovariantSmoothingProperties.OneStepRelations L k j) ∧
      ∀ j ≤ k, Tower.FullSpace.CovariantSmoothingProperties.IterateRelations L k j ∧
        Tower.FullSpace.CovariantSmoothingProperties.GaugeEquivariance L k j ∧
        Tower.FullSpace.CovariantSmoothingProperties.IsometryEquivariance L k j
end Tower
end YangMills.Construction
end
