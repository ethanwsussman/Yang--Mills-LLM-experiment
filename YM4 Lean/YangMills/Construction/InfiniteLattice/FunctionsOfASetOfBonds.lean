import YangMills.Construction.InfiniteLattice.UnitSpacingLatticeData
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
namespace LinkSetFunctions
open FixedSpacing (Params IsBorelMeasurableFn)
theorem mesh_pos (D : Params) : 0 < D.mesh := by
  have hL : (0 : ℝ) < (D.L : ℝ) := by
    have h := D.isAdmissible.2
    exact_mod_cast (by omega : 0 < D.L)
  unfold ReflectionPositivity.AxisMirror.MirrorData.mesh PeriodicLattice.meshSize
  exact zpow_pos hL _
theorem two_le_L (D : Params) : 2 ≤ D.L := by
  have h := D.isAdmissible.2
  omega
theorem neg_m_lt_K (D : Params) : -((D.m : ℕ) : ℤ) < ((D.K : ℕ) : ℤ) := by
  have hm := D.m.pos
  have hK := D.K.pos
  omega
def IsBoundedBorel {X : Type*} [TopologicalSpace X] (F : X → ℂ) : Prop :=
  IsBorelMeasurableFn F ∧ ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C
def factorThrough (D : Params) {S : Set (Link D.mesh)} (hS : S ⊆ positiveLinkSet D.mesh)
    (F : GaugeField D.mesh → ℂ) : LinkVariables S → ℂ :=
  fun V => F (gluedField (mesh_pos D) hS V (trivialField D.mesh))
def InfiniteCase (D : Params) : Prop :=
  ∀ (S : Set (Link D.mesh)) (hS : S ⊆ positiveLinkSet D.mesh) (F : GaugeField D.mesh → ℂ),
    IsBoundedObservable F →
      (Measurable[linkSigma S] F ↔ DependsOnlyOnLinks S F) ∧
        (DependsOnlyOnLinks S F →
          (∀ U, F U = factorThrough D hS F (restrictField U S)) ∧
            IsBoundedBorel (factorThrough D hS F) ∧
              (Continuous F → Continuous (factorThrough D hS F)))
@[reducible] def periodicSigma (D : Params) (S : Set (PeriodicLattice.Bond D.L D.m (D.K : ℕ))) :
    MeasurableSpace (PeriodicLattice.CompactGaugeField D.L D.m (D.K : ℕ)) :=
  ⨆ b ∈ S, MeasurableSpace.comap
    (fun U : PeriodicLattice.CompactGaugeField D.L D.m (D.K : ℕ) => U.linkValue b) inferInstance
def periodicFactor (D : Params) {S : Set (PeriodicLattice.Bond D.L D.m (D.K : ℕ))}
    (hS : S ⊆ PeriodicLattice.forwardBonds D.L D.m (D.K : ℕ))
    (F : PeriodicLattice.CompactGaugeField D.L D.m (D.K : ℕ) → ℂ) : LinkVariables S → ℂ :=
  fun V => F (PeriodicLattice.CompactGaugeField.glue (two_le_L D)
    (neg_m_lt_K D) hS V (PeriodicLattice.CompactGaugeField.identity D.L D.m (D.K : ℕ)))
def PeriodicCase (D : Params) : Prop :=
  ∀ (S : Set (PeriodicLattice.Bond D.L D.m (D.K : ℕ)))
    (hS : S ⊆ PeriodicLattice.forwardBonds D.L D.m (D.K : ℕ))
    (F : PeriodicLattice.CompactGaugeField D.L D.m (D.K : ℕ) → ℂ),
    IsBoundedBorel F →
      (Measurable[periodicSigma D S] F ↔ PeriodicLattice.DependsOnlyOn S F) ∧
        (PeriodicLattice.DependsOnlyOn S F →
          (∀ U, F U = periodicFactor D hS F (U.restrictTo S)) ∧
            IsBoundedBorel (periodicFactor D hS F) ∧
              (Continuous F → Continuous (periodicFactor D hS F)))
def Claim : Prop :=
  ∀ D : FixedSpacing.Params, InfiniteCase D ∧ PeriodicCase D
end LinkSetFunctions
end InfiniteLattice
end YangMills.Construction
