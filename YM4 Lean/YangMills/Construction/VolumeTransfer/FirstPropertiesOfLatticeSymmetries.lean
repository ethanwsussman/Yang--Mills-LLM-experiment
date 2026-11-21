import YangMills.Construction.VolumeTransfer.LatticeSymmetriesAndInvariantMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Function
noncomputable section
namespace YangMills.Construction.VolumeTransfer
open InfiniteLattice (AmbientSpace refinedLattice refinedSpacing RefinedGaugeField)
open LatticeGeometry (diagSign)
namespace LatticeSymmetries
def periodLattice (ℓ : ℝ) : Set AmbientSpace :=
  {u | ∃ k : Fin 4 → ℤ, ∀ μ, u μ = ℓ * (k μ : ℝ)}
def TorusInducedMapUnique (L m K : ℕ) : Prop :=
  ∀ (ε : Fin 4 → ℤˣ), ∀ t ∈ refinedLattice L K,
    (∃! r : PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m,
      (LatticeGeometry.periodic L m K).IsInducedBy r fun x => diagSign ε x + t) ∧
    (∀ x, ∀ u ∈ periodLattice (PeriodicLattice.torusSide L m),
      diagSign ε (x + u) + t = (diagSign ε x + t) + diagSign ε u) ∧
    BijOn (diagSign ε) (periodLattice (PeriodicLattice.torusSide L m))
      (periodLattice (PeriodicLattice.torusSide L m))
def SymmetryInvertible {L K : ℕ} (Y : LatticeGeometry L K) : Prop :=
  ∀ (ε : Fin 4 → ℤˣ), ∀ t ∈ refinedLattice L K, ∀ r : Y.Point → Y.Point,
    Y.IsInducedBy r (fun x => diagSign ε x + t) →
      r '' (Y.sites : Set Y.Point) = Y.sites ∧ Y.MapsLinks r ∧ Bijective r ∧
        ∃ s : Y.Point → Y.Point, Y.IsReflectionTranslation s ∧
          Y.IsInducedBy s (fun x => diagSign ε⁻¹ x - diagSign ε⁻¹ t) ∧
            LeftInverse s r ∧ RightInverse s r
def SymmetryComp {L K : ℕ} (Y : LatticeGeometry L K) : Prop :=
  ∀ (ε ε' : Fin 4 → ℤˣ), ∀ t ∈ refinedLattice L K, ∀ t' ∈ refinedLattice L K,
    ∀ r r' : Y.Point → Y.Point,
      Y.IsInducedBy r (fun x => diagSign ε x + t) →
        Y.IsInducedBy r' (fun x => diagSign ε' x + t') →
          Y.IsReflectionTranslation (r ∘ r') ∧
            Y.IsInducedBy (r ∘ r') fun x => diagSign (ε * ε') x + (diagSign ε t' + t)
def EuclideanSymmetryIsometry (L K : ℕ) : Prop :=
  ∀ r : AmbientSpace → AmbientSpace, (LatticeGeometry.euclidean L K).IsReflectionTranslation r →
    ∀ x y : AmbientSpace,
      TorusMetric.supNormVec (r x - r y) = TorusMetric.supNormVec (x - y) ∧
        TorusMetric.l1NormVec (r x - r y) = TorusMetric.l1NormVec (x - y) ∧
          TorusMetric.euclidNormVec (r x - r y) = TorusMetric.euclidNormVec (x - y)
def TorusSymmetryIsometry (L m K : ℕ) : Prop :=
  ∀ (ε : Fin 4 → ℤˣ), ∀ t ∈ refinedLattice L K,
    ∀ r : PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m,
      (LatticeGeometry.periodic L m K).IsInducedBy r (fun x => diagSign ε x + t) →
        ∀ x y : PeriodicLattice.FourTorus L m,
          TorusMetric.torusSupNorm (r x - r y) = TorusMetric.torusSupNorm (x - y) ∧
            TorusMetric.torusL1Norm (r x - r y) = TorusMetric.torusL1Norm (x - y) ∧
              TorusMetric.torusEuclidNorm (r x - r y) = TorusMetric.torusEuclidNorm (x - y) ∧
                TorusMetric.torusProj (PeriodicLattice.torusSide L m) ⁻¹' {r x - r y} =
                  diagSign ε '' (TorusMetric.torusProj (PeriodicLattice.torusSide L m) ⁻¹' {x - y})
def EuclideanShiftsAreSymmetries (L K : ℕ) : Prop :=
  ∀ v : InfiniteLattice.LatticePoint (refinedSpacing L K),
    (LatticeGeometry.euclidean L K).IsReflectionTranslation (InfiniteLattice.shift v).toFun
def TorusShiftsAreSymmetries (L m K : ℕ) : Prop :=
  ∀ w ∈ (LatticeGeometry.periodic L m K).sites,
    (LatticeGeometry.periodic L m K).IsReflectionTranslation fun y => y + w
def MeasureDeterminedByCylinderFunctions (L K : ℕ) : Prop :=
  ∀ (ν ν' : Measure (RefinedGaugeField L K)) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'],
    (∀ F : RefinedGaugeField L K → ℂ,
      IsBoundedBorelInFinitelyManyLinks (refinedLinkValue L K) F →
        ∫ U, F U ∂ν = ∫ U, F U ∂ν') → ν = ν'
def InvarianceNotionsAgree (L K : ℕ) : Prop :=
  ∀ r : AmbientSpace → AmbientSpace, (LatticeGeometry.euclidean L K).IsReflectionTranslation r →
    ∃ (hr : (LatticeGeometry.euclidean L K).MapsLinks r)
      (s : InfiniteLattice.LatticeSymmetry (refinedSpacing L K)), s.toFun = r ∧
        ∀ (ν : Measure (RefinedGaugeField L K)) [IsProbabilityMeasure ν],
          IsInvariantUnderLinkMap ν hr ↔ InfiniteLattice.IsSymmetricUnder ν s
def BasicProperties : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ K : ℕ,
    (SymmetryInvertible (LatticeGeometry.euclidean L K) ∧
      SymmetryComp (LatticeGeometry.euclidean L K) ∧
      EuclideanSymmetryIsometry L K ∧
      EuclideanShiftsAreSymmetries L K ∧
      MeasureDeterminedByCylinderFunctions L K ∧
      InvarianceNotionsAgree L K) ∧
    ∀ m : ℕ,
      TorusInducedMapUnique L m K ∧
      SymmetryInvertible (LatticeGeometry.periodic L m K) ∧
      SymmetryComp (LatticeGeometry.periodic L m K) ∧
      TorusSymmetryIsometry L m K ∧
      TorusShiftsAreSymmetries L m K
end LatticeSymmetries
end YangMills.Construction.VolumeTransfer
end
