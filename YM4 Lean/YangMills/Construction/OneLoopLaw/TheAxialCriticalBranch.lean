import YangMills.Construction.OneLoopLaw.SettingOfTheAxialCriticalBranch
import YangMills.Construction.Towers.DilationOfATower
import YangMills.Construction.Towers.TheSignsOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace OneLoopLaw
namespace AxialBranchSetting
variable (D : AxialBranchSetting)
theorem L_pos : 0 < D.L := by
  have h := D.params.isAdmissible.2
  show 0 < D.params.L
  omega
def blockStep (i : ℕ) : (D.Edge i → Matrices.ComplexMatrix2) → D.Edge (i + 1) → Matrices.ComplexMatrix2 :=
  Tower.smoothingStep D.L D.m D.K i
abbrev unitField (i : ℕ) : D.Edge i → Matrices.ComplexMatrix2 := Tower.trivialField D.L D.m D.K i
abbrev gaugeGroupOn (i : ℕ) : Set (D.Vertex i → Matrices.ComplexMatrix2) :=
  Tower.gaugeGroupAt D.L D.m D.K i
abbrev towerExponent : ℕ := Tower.scaledExponent D.m D.K D.level
def edgeEquivTower (i : ℕ) : D.Edge i ≃ Tower.Edge D.L D.towerExponent D.level i :=
  Tower.scaleEdge D.L_pos D.level_le_cutoff i
variable {D}
def toTower {i : ℕ} (V : D.Edge i → Matrices.ComplexMatrix2) :
    Tower.Edge D.L D.towerExponent D.level i → Matrices.ComplexMatrix2 :=
  Tower.transportTotal (D.edgeEquivTower i) V
def liftComp
    (p : ∀ i : ℕ, (D.Edge (i + 1) → Matrices.ComplexMatrix2) → D.Edge i → Matrices.ComplexMatrix2) :
    ∀ j : ℕ, (D.Edge j → Matrices.ComplexMatrix2) → D.Edge 0 → Matrices.ComplexMatrix2
  | 0 => id
  | i + 1 => liftComp p i ∘ p i
def liftDescent
    (p : ∀ i : ℕ, (D.Edge (i + 1) → Matrices.ComplexMatrix2) → D.Edge i → Matrices.ComplexMatrix2)
    (m : ℕ) : ∀ d : ℕ, (D.Edge (m + d) → Matrices.ComplexMatrix2) → D.Edge m → Matrices.ComplexMatrix2
  | 0 => id
  | d + 1 => liftDescent p m d ∘ p (m + d)
variable (D)
structure AxialLiftSystem where
  nhdAt : ∀ i : ℕ, Set (D.Edge i → Matrices.ComplexMatrix2)
  stepDomain : ∀ i : ℕ, Set (D.Edge i → Matrices.ComplexMatrix2)
  bareDomain : ℕ → Set (D.Edge 0 → Matrices.ComplexMatrix2)
  gaugeDomain : ∀ i : ℕ, Set (D.Vertex i → Matrices.ComplexMatrix2)
  lift : ∀ i : ℕ, (D.Edge (i + 1) → Matrices.ComplexMatrix2) → D.Edge i → Matrices.ComplexMatrix2
instance instNonemptyAxialLiftSystem : Nonempty D.AxialLiftSystem :=
  ⟨⟨fun _ => ∅, fun _ => ∅, fun _ => ∅, fun _ => ∅, fun _ _ _ => 1⟩⟩
variable {D}
namespace AxialLiftSystem
variable (S : D.AxialLiftSystem)
def comp (j : ℕ) : (D.Edge j → Matrices.ComplexMatrix2) → D.Edge 0 → Matrices.ComplexMatrix2 :=
  liftComp S.lift j
def energy (j : ℕ) (W : D.Edge j → Matrices.ComplexMatrix2) : ℝ := D.wilsonAction (S.comp j W)
def fixedEnergy (i : ℕ) (V : D.Edge i → Matrices.ComplexMatrix2) : ℝ :=
  D.axialGaugeFixing i V + S.energy i V
def bareEnergy (D : AxialBranchSetting) (i : ℕ) (U : D.Edge 0 → Matrices.ComplexMatrix2) : ℝ :=
  D.wilsonAction U + D.axialGaugeFixingSum i U
def stepFiber (i : ℕ) (W : D.Edge (i + 1) → Matrices.ComplexMatrix2) :
    Set (D.Edge i → Matrices.ComplexMatrix2) :=
  {V | V ∈ S.stepDomain i ∧ D.blockStep i V = W}
def bareFiber (i : ℕ) (W : D.Edge i → Matrices.ComplexMatrix2) :
    Set (D.Edge 0 → Matrices.ComplexMatrix2) :=
  {U | U ∈ S.bareDomain i ∧ D.blockingIter i U = W}
def IsSoleCriticalPosDef {j : ℕ} (N : Set (D.Edge j → Matrices.ComplexMatrix2))
    (F : (D.Edge j → Matrices.ComplexMatrix2) → ℝ) (x : D.Edge j → Matrices.ComplexMatrix2) : Prop :=
  IsCriticalPointOn (D := D) N F x ∧ (hessianOn (D := D) N F x).PosDef ∧
    ∀ y, IsCriticalPointOn (D := D) N F y → y = x
structure IsAxialLiftSystem : Prop where
  nhdAt_zero : S.nhdAt 0 = D.fieldSpace 0
  isOpen_nhdAt : ∀ i < D.level, Tower.IsOpenNhdOfOne (S.nhdAt (i + 1))
  isOpen_stepDomain : ∀ i < D.level, Tower.IsOpenNhdOfOne (S.stepDomain i)
  isOpen_bareDomain : ∀ i < D.level, Tower.IsOpenNhdOfOne (S.bareDomain (i + 1))
  gaugeDomain_mem : ∀ i < D.level, S.gaugeDomain (i + 1) ⊆ D.gaugeGroupOn (i + 1) ∧
    S.gaugeDomain (i + 1) ∈ 𝓝[D.gaugeGroupOn (i + 1)] (fun _ => (1 : Matrices.ComplexMatrix2))
  analytic_lift : ∀ i < D.level, Tower.IsAnalyticFieldMap (S.nhdAt (i + 1)) (S.lift i)
  lift_eq_chosen : ∀ i < D.level, ∀ W ∈ S.nhdAt (i + 1),
    toTower (S.lift i W) = Tower.chosenProlong D.L D.towerExponent D.level i (toTower W)
  image_constGauge_eq : ∀ i < D.level, ∀ v ∈ D.gaugeGroupOn (i + 1),
    IsConstantGaugeTransform (D := D) v →
      PeriodicLattice.gaugeTransform v '' S.nhdAt (i + 1) = S.nhdAt (i + 1)
  image_isometry_eq : ∀ (i : ℕ) (h : i < D.level), ∀ s ∈ D.levelIsometries (i + 1) h,
    isometryField (D := D) s '' S.nhdAt (i + 1) = S.nhdAt (i + 1)
  stepDomain_subset : ∀ i < D.level, S.stepDomain i ⊆ D.smallFaceDomain i ∩ S.nhdAt i
  bareDomain_subset : ∀ i < D.level, S.bareDomain (i + 1) ⊆ D.iteratedSmallDomain (i + 1)
  mapsTo_lift : ∀ i < D.level, MapsTo (S.lift i) (S.nhdAt (i + 1)) (S.stepDomain i)
  analytic_comp : ∀ i < D.level, Tower.IsAnalyticFieldMap (S.nhdAt (i + 1)) (S.comp (i + 1))
  analytic_energy : ∀ i < D.level,
    Tower.IsAnalyticFieldFunction (S.nhdAt (i + 1)) (S.energy (i + 1))
  fixing_defined : ∀ i < D.level, ∀ V ∈ S.stepDomain i, D.AxialGaugeFixingDefined i V
  analytic_fixedEnergy : ∀ i < D.level,
    Tower.IsAnalyticFieldFunction (S.stepDomain i) (S.fixedEnergy i)
  fixingSum_defined : ∀ i < D.level, ∀ U ∈ S.bareDomain (i + 1),
    D.AxialGaugeFixingSumDefined (i + 1) U
  analytic_bareEnergy : ∀ i < D.level,
    Tower.IsAnalyticFieldFunction (S.bareDomain (i + 1)) (bareEnergy D (i + 1))
  energy_eq_chosen : ∀ i < D.level, ∀ W ∈ S.nhdAt (i + 1),
    S.energy (i + 1) W = Tower.chosenEnergy D.L D.towerExponent D.level (i + 1) (toTower W)
  mapsTo_comp : ∀ i < D.level, MapsTo (S.comp (i + 1)) (S.nhdAt (i + 1)) (S.bareDomain (i + 1))
  fibers_submanifold : ∀ i < D.level, ∀ W ∈ S.nhdAt (i + 1),
    IsAnalyticSubmanifold (D := D) (S.stepDomain i) (S.stepFiber i W) ∧
      IsAnalyticSubmanifold (D := D) (S.bareDomain (i + 1)) (S.bareFiber (i + 1) W)
  blockStep_lift : ∀ i < D.level, ∀ W ∈ S.nhdAt (i + 1), D.blockStep i (S.lift i W) = W
  lift_unitField : ∀ i < D.level, S.lift i (D.unitField (i + 1)) = D.unitField i
  blockingIter_comp : ∀ i < D.level, ∀ W ∈ S.nhdAt (i + 1),
    D.blockingIter (i + 1) (S.comp (i + 1) W) = W
  blockingIter_comp_descent : ∀ m d : ℕ, m + d < D.level → ∀ W ∈ S.nhdAt (m + (d + 1)),
    D.blockingIter m (S.comp (m + (d + 1)) W) = liftDescent S.lift m (d + 1) W
  contDiffTwo : ∀ i < D.level,
    IsContDiffTwo (D := D) (S.stepDomain i) (S.fixedEnergy i) ∧
      IsContDiffTwo (D := D) (S.stepDomain i) (S.energy i) ∧
      IsContDiffTwo (D := D) (S.bareDomain (i + 1)) (bareEnergy D (i + 1)) ∧
      IsContDiffTwo (D := D) (S.bareDomain (i + 1)) D.wilsonAction
  lift_soleCritical : ∀ i < D.level, ∀ W ∈ S.nhdAt (i + 1),
    IsSoleCriticalPosDef (S.stepFiber i W) (S.fixedEnergy i) (S.lift i W)
  fixing_lift_eq_zero : ∀ i < D.level, ∀ W ∈ S.nhdAt (i + 1),
    D.axialGaugeFixing i (S.lift i W) = 0
  lift_axial : ∀ i < D.level, ∀ W ∈ S.nhdAt (i + 1), Tower.IsAxialGaugeAt D.L D.m D.K i (S.lift i W)
  lift_critical_energy : ∀ i < D.level, ∀ W ∈ S.nhdAt (i + 1),
    IsCriticalPointOn (D := D) (S.stepFiber i W) (S.energy i) (S.lift i W)
  fixingSum_comp_eq_zero : ∀ i < D.level, ∀ W ∈ S.nhdAt (i + 1),
    D.axialGaugeFixingSum (i + 1) (S.comp (i + 1) W) = 0
  comp_soleCritical : ∀ i < D.level, ∀ W ∈ S.nhdAt (i + 1),
    IsSoleCriticalPosDef (S.bareFiber (i + 1) W) (bareEnergy D (i + 1)) (S.comp (i + 1) W)
  comp_critical_action : ∀ i < D.level, ∀ W ∈ S.nhdAt (i + 1),
    IsCriticalPointOn (D := D) (S.bareFiber (i + 1) W) D.wilsonAction (S.comp (i + 1) W)
  isometry_covariant : ∀ (i : ℕ) (h : i < D.level), ∀ W ∈ S.nhdAt (i + 1),
    ∀ s ∈ D.levelIsometries (i + 1) h,
      S.energy (i + 1) (isometryField (D := D) s W) = S.energy (i + 1) W ∧
        S.lift i (isometryField (D := D) s W) = isometryField (D := D) s (S.lift i W) ∧
        S.comp (i + 1) (isometryField (D := D) s W) = isometryField (D := D) s (S.comp (i + 1) W)
  gauge_covariant : ∀ i < D.level, ∀ W ∈ S.nhdAt (i + 1), ∀ v ∈ D.gaugeGroupOn (i + 1),
    (IsConstantGaugeTransform (D := D) v ∨ (v ∈ S.gaugeDomain (i + 1) ∧
      PeriodicLattice.gaugeTransform v W ∈ S.nhdAt (i + 1))) →
      S.energy (i + 1) (PeriodicLattice.gaugeTransform v W) = S.energy (i + 1) W ∧
        S.lift i (PeriodicLattice.gaugeTransform v W) =
          PeriodicLattice.gaugeTransform (blockLift (D := D) i v) (S.lift i W) ∧
        S.comp (i + 1) (PeriodicLattice.gaugeTransform v W) =
          PeriodicLattice.gaugeTransform (blockLift (D := D) 0 v) (S.comp (i + 1) W)
structure IsCriticalAxialSystem : Prop extends S.IsAxialLiftSystem where
  eventually_eq_of_critical : ∀ (N' U' : ∀ i : ℕ, Set (D.Edge i → Matrices.ComplexMatrix2))
    (p' : ∀ i : ℕ, (D.Edge (i + 1) → Matrices.ComplexMatrix2) → D.Edge i → Matrices.ComplexMatrix2),
    N' 0 = D.fieldSpace 0 →
    (∀ i < D.level, Tower.IsOpenNhdOfOne (N' (i + 1)) ∧ Tower.IsOpenNhdOfOne (U' i) ∧
      ContinuousOn (p' i) (N' (i + 1)) ∧ MapsTo (p' i) (N' (i + 1)) (U' i) ∧
      U' i ⊆ D.smallFaceDomain i ∩ N' i ∧ p' i (D.unitField (i + 1)) = D.unitField i) →
    (∀ i < D.level, ∀ W ∈ N' (i + 1), ∀ (I : Set ℝ) (γ : ℝ → D.Edge i → Matrices.ComplexMatrix2),
      IsCurveInto (D := D) {V | V ∈ U' i ∧ D.blockStep i V = W} I γ → γ 0 = p' i W →
        HasDerivAt
          (fun t => D.axialGaugeFixing i (γ t) + D.wilsonAction (liftComp p' i (γ t))) 0 0) →
    (∀ i < D.level, ∀ W ∈ N' (i + 1), D.blockStep i (p' i W) = W) →
    ∀ i < D.level, Tower.EventuallyNearIdentity (D.fieldSpace (i + 1)) fun W => p' i W = S.lift i W
end AxialLiftSystem
def chosenBranch (D : AxialBranchSetting) : D.AxialLiftSystem :=
  Classical.epsilon AxialLiftSystem.IsCriticalAxialSystem
end AxialBranchSetting
end OneLoopLaw
end YangMills.Construction
end
