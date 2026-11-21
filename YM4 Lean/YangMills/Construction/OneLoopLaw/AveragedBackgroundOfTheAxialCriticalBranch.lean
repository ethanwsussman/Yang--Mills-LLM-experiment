import YangMills.Construction.Lattice.FluctuationFormOfAStepAtAPoint
import YangMills.Construction.Lattice.SettingOfThePureSmallFieldStep
import YangMills.Construction.OneLoopLaw.GaussianNormaliserInTheExponentialChart
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def axialGaugeFibre {L m : ℕ} (K i : ℕ) (W : BondAtLevel L m K (i + 1) → Matrices.ComplexMatrix2) :
    Set (BondAtLevel L m K i → Matrices.ComplexMatrix2) :=
  {V | V ∈ gaugeFieldsAtLevel L m K i ∧ IsBlockAxialGauge K i univ V ∧
    blockAverageStep (Averaging.smoothingRadius L) i V = W}
def transportAlongEq {L L' : ℕ} (F : ℕ → Type) (h : L' = L) (x : F L) : F L' :=
  cast (congrArg F h.symm) x
namespace CubesOfStep
structure SmallFieldStepData (c : ParameterChoice.ChoiceUpToDegreeConstants) {m : ℕ} (K i : ℕ)
    (V : BondAtLevel c.L m K i → Matrices.ComplexMatrix2)
    (W : BondAtLevel c.L m K (i + 1) → Matrices.ComplexMatrix2)
    (branch : (BondAtLevel c.L m K (i + 1) → Matrices.ComplexMatrix2) →
      BondAtLevel c.L m K i → Matrices.ComplexMatrix2) : Prop where
  data : IsSmallFieldStepData c K i V W
  touchingBonds_eq : touchingBonds c (smallFieldStepData V W) = univ
  determiningBondSet_eq :
    determiningBondSet K i (smallFieldStepData V W).domains = constantDeterminingBondSet K i
  backgroundFibre_eq : backgroundFibre c (smallFieldStepData V W) = axialGaugeFibre K i W
  regularFibre_eq : regularFibre c (smallFieldStepData V W) =
    {V' | V' ∈ axialGaugeFibre K i W ∧ HasConstantMinimalOrbit c.εv K i V'}
  backgroundOf_mem : ∀ V' ∈ regularFibre c (smallFieldStepData V W),
    SmallFieldCriticalOrbitExists c K i V' ∧ HasConstantMinimalOrbit c.εv K i V' ∧
      smallFieldRegularCritical c K i V' = constantRegularCriticalFields c.εv K i V' ∧
      backgroundOf c (smallFieldStepData V W) V' ∈ constantRegularCriticalFields c.εv K i V'
  branch_mem : branch W ∈ backgroundFibre c (smallFieldStepData V W)
  branch_mem_regular_of_zero : i = 0 → branch W ∈ regularFibre c (smallFieldStepData V W)
  branch_mem_regular_of_eq :
    regularFibre c (smallFieldStepData V W) = backgroundFibre c (smallFieldStepData V W) →
      branch W ∈ regularFibre c (smallFieldStepData V W)
  wilsonAction_const_on_orbit : branch W ∈ regularFibre c (smallFieldStepData V W) →
    ∀ V' ∈ regularFibre c (smallFieldStepData V W),
      ∀ U ∈ constantRegularCriticalFields c.εv K i V',
        ∀ U' ∈ constantRegularCriticalFields c.εv K i V', wilsonAction U = wilsonAction U'
  isBackgroundMinimizer_iff : branch W ∈ regularFibre c (smallFieldStepData V W) →
    ∀ V', IsBackgroundMinimizer c (smallFieldStepData V W) V' ↔ V' = branch W
  backgroundField_eq : branch W ∈ regularFibre c (smallFieldStepData V W) →
    HasUniqueBackgroundMinimizer c (smallFieldStepData V W) ∧
      backgroundField c (smallFieldStepData V W) = branch W
  backgroundPoint_eq : branch W ∈ regularFibre c (smallFieldStepData V W) →
    ∀ N : Set (BondAtLevel c.L m K (i + 1) → Matrices.ComplexMatrix2),
      IsBranchCase c (smallFieldStepData V W) N →
        backgroundPoint c (smallFieldStepData V W) N branch =
          backgroundField c (smallFieldStepData V W)
end CubesOfStep
end PeriodicLattice
namespace OneLoopLaw
namespace AxialBranchSetting
open PeriodicLattice PeriodicLattice.CubesOfStep
variable (D : AxialBranchSetting) (i : ℕ) (ε : ℝ)
structure FibreMinimumProperties (W : D.Edge (i + 1) → Matrices.ComplexMatrix2)
    (p : D.Edge i → Matrices.ComplexMatrix2) (u : D.Edge 0 → Matrices.ComplexMatrix2) : Prop where
  lift_mem : p ∈ axialGaugeFibre D.K i W
  composite_mem : u ∈ constantRegularCriticalFields ε D.K i p
  wilsonAction_le : ∀ V' ∈ axialGaugeFibre D.K i W, ∀ U ∈ constantConstrainedFields D.K i V',
    D.wilsonAction u ≤ D.wilsonAction U ∧
      (D.wilsonAction U = D.wilsonAction u ↔ V' = p ∧ U ∈ D.residualGaugeOrbit i u)
  minimizer_iff : ∀ V' ∈ axialGaugeFibre D.K i W,
    (∃ U ∈ constantConstrainedFields D.K i V',
      (U ∈ D.fieldSpace 0 ∧ D.blockingIter (i + 1) U = W) ∧
        ∀ U' ∈ D.fieldSpace 0, D.blockingIter (i + 1) U' = W →
          D.wilsonAction U ≤ D.wilsonAction U') ↔ V' = p
structure BackgroundMinimumProperties (W : D.Edge (i + 1) → Matrices.ComplexMatrix2)
    (p : D.Edge i → Matrices.ComplexMatrix2) (u : D.Edge 0 → Matrices.ComplexMatrix2) : Prop where
  background_wilsonAction_le : ∀ V' ∈ axialGaugeFibre D.K i W,
    HasConstantMinimalOrbit ε D.K i V' →
      HoldsOnConstantMinimalOrbit ε D.K i V' fun U =>
        D.wilsonAction u ≤ D.wilsonAction U ∧ (D.wilsonAction U = D.wilsonAction u ↔ V' = p)
  minimalOrbit_eq : HasConstantMinimalOrbit ε D.K i p →
    constantRegularCriticalFields ε D.K i p = D.residualGaugeOrbit i u
  minimalOrbit_exists : i = 0 → HasConstantMinimalOrbit ε D.K i p
structure BackgroundProperties (W : D.Edge (i + 1) → Matrices.ComplexMatrix2) : Prop extends
    D.FibreMinimumProperties i ε W (D.branchLift i W) (D.branchComp (i + 1) W),
    D.BackgroundMinimumProperties i ε W (D.branchLift i W) (D.branchComp (i + 1) W) where
  smallFieldStep : ∀ (c : ParameterChoice.ChoiceUpToDegreeConstants) (hL : c.L = D.L), c.εv = ε →
    ∀ V ∈ D.fieldSpace i,
      SmallFieldStepData c (m := D.m) D.K i
        (transportAlongEq (fun L => BondAtLevel L D.m D.K i → Matrices.ComplexMatrix2) hL V)
        (transportAlongEq (fun L => BondAtLevel L D.m D.K (i + 1) → Matrices.ComplexMatrix2) hL W)
        (transportAlongEq (fun L => (BondAtLevel L D.m D.K (i + 1) → Matrices.ComplexMatrix2) →
          BondAtLevel L D.m D.K i → Matrices.ComplexMatrix2) hL (D.branchLift i))
  chartBase_eq : D.chartBase i W = D.branchLift i W
  chosenProlong_eq : toTower (D.branchLift i W) =
    Tower.chosenProlong D.L D.towerExponent D.level i (toTower W)
structure IsBackgroundNhd (N : Set (D.Edge (i + 1) → Matrices.ComplexMatrix2)) : Prop where
  isOpenNhd : Tower.IsOpenNhdOfOne N
  subset_branchNhd : N ⊆ D.branchNhd (i + 1)
  properties : ∀ W ∈ N, D.BackgroundProperties i ε W
  properties_of_subset : ∀ N' ⊆ N,
    (∃ O : Set (D.Edge (i + 1) → Matrices.ComplexMatrix2), Tower.IsOpenNhdOfOne O ∧ O ⊆ N') →
      ∀ W ∈ N', D.BackgroundProperties i ε W
  image_isometry : ∀ (h : i < D.level), ∀ s ∈ D.levelIsometries (i + 1) h,
    isometryField (D := D) s '' N = N
def backgroundNhd : Set (D.Edge (i + 1) → Matrices.ComplexMatrix2) :=
  Classical.epsilon (D.IsBackgroundNhd i ε)
end AxialBranchSetting
end OneLoopLaw
end YangMills.Construction
end
