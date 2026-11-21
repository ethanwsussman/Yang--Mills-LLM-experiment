import YangMills.Construction.ReflectionPositivity.CellsInducedMapsAndCellAlgebrasOfATorus
import YangMills.Construction.ReflectionPositivity.LatticesAndBondVariablesOfACellSide
import YangMills.Construction.VolumeTransfer.LatticeSymmetriesCarryBondsAndInvariance
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.VolumeTransfer
open InfiniteLattice (AmbientSpace refinedLattice refinedSpacing RefinedGaugeField LatticePoint
  LatticeSymmetry)
namespace LatticeGeometry
variable {L K : ℕ}
def IsInducedReflectionTranslation (Y : LatticeGeometry L K) (r : Y.Point → Y.Point)
    (ε : Fin 4 → ℤˣ) (t : AmbientSpace) : Prop :=
  t ∈ refinedLattice L K ∧ Y.IsInducedBy r fun x => diagSign ε x + t
def AffineMapDescendsUniquely (L m K : ℕ) : Prop :=
  ∀ (ε : Fin 4 → ℤˣ), ∀ t ∈ refinedLattice L K,
    (∀ (x : AmbientSpace), ∀ u ∈ InfiniteLattice.latticeSubgroup (PeriodicLattice.torusSide L m),
      diagSign ε (x + u) + t = (diagSign ε x + t) + diagSign ε u ∧
        diagSign ε u ∈ InfiniteLattice.latticeSubgroup (PeriodicLattice.torusSide L m)) ∧
    ∃! r : (periodic L m K).Point → (periodic L m K).Point,
      (periodic L m K).IsInducedBy r fun x => diagSign ε x + t
def SymmetriesFormGroup (Y : LatticeGeometry L K) : Prop :=
  ∀ (r : Y.Point → Y.Point) (ε : Fin 4 → ℤˣ) (t : AmbientSpace),
    Y.IsInducedReflectionTranslation r ε t →
    r '' (Y.sites : Set Y.Point) = Y.sites ∧ Function.Bijective r ∧
    (∃ s : Y.Point → Y.Point, Y.IsInducedReflectionTranslation s ε⁻¹ (-diagSign ε⁻¹ t) ∧
      Function.LeftInverse s r ∧ Function.RightInverse s r) ∧
    ∀ (s : Y.Point → Y.Point) (δ : Fin 4 → ℤˣ) (w : AmbientSpace),
      Y.IsInducedReflectionTranslation s δ w →
        Y.IsInducedReflectionTranslation (r ∘ s) (ε * δ) (diagSign ε w + t) ∧
        ∀ (hr : Y.MapsLinks r) (hs : Y.MapsLinks s)
          (hrs : Y.MapsLinks (r ∘ s)) (G : Y.Field → ℂ),
          precompose hr (precompose hs G) = precompose hrs G
def SymmetriesPreserveDistances (L K : ℕ) : Prop :=
  ∀ r : AmbientSpace → AmbientSpace, (euclidean L K).IsReflectionTranslation r →
    ∀ x y : AmbientSpace,
    TorusMetric.euclidNormVec (r x - r y) = TorusMetric.euclidNormVec (x - y) ∧
      TorusMetric.supNormVec (r x - r y) = TorusMetric.supNormVec (x - y) ∧
      TorusMetric.l1NormVec (r x - r y) = TorusMetric.l1NormVec (x - y)
def SymmetriesPreserveTorusDistances (L m K : ℕ) : Prop :=
  ∀ r : PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m,
    (periodic L m K).IsReflectionTranslation r →
    ∀ x y : PeriodicLattice.FourTorus L m,
      TorusMetric.torusEuclidNorm (r x - r y) = TorusMetric.torusEuclidNorm (x - y) ∧
        TorusMetric.torusSupNorm (r x - r y) = TorusMetric.torusSupNorm (x - y) ∧
        TorusMetric.torusL1Norm (r x - r y) = TorusMetric.torusL1Norm (x - y)
def ShiftsAreSymmetries (L K : ℕ) : Prop :=
  ∀ v : LatticePoint (refinedSpacing L K),
    (euclidean L K).IsReflectionTranslation (InfiniteLattice.shift v).toFun
def ReflectionGroupActsOnEuclidean (L K : ℕ) (lc : ℝ) : Prop :=
  (∃ n : ℤ, lc / refinedSpacing L K = n) ∧
  (∀ (μ : Fin 4) (ι : ℤ), ∃ q : ℝ, q = ι * lc - 1 / 2 * refinedSpacing L K ∧
    (∀ x : AmbientSpace, FaceReflections.reflect L K lc μ ι x =
      x - (2 * (x μ - q)) • BoxTorus.basisVector μ) ∧
    2 * q = 2 * ι * lc - refinedSpacing L K ∧
    (∃ n : ℤ, 2 * q = n * refinedSpacing L K) ∧
    (euclidean L K).IsReflectionTranslation (FaceReflections.reflect L K lc μ ι)) ∧
  ∀ r ∈ FaceReflections.reflectionGroup L K lc,
    (∃ l : List (Fin 4 × ℤ),
      r = (l.map fun p => FaceReflections.reflectEquiv L K lc p.1 p.2).prod) ∧
    (euclidean L K).IsReflectionTranslation (r : AmbientSpace → AmbientSpace)
def ReflectionGroupActsOnPeriodic (L m K : ℕ) (lc : ℝ) : Prop :=
  (∀ g ∈ ReflectionPositivity.PeriodicCubes.inducedReflections L m K lc,
    (periodic L m K).IsReflectionTranslation g) ∧
  ∀ τ ∈ (periodic L m K).sites, (periodic L m K).IsReflectionTranslation fun x => x + τ
def ProbabilityMeasuresDeterminedByLocalFunctions (L K : ℕ) : Prop :=
  ∀ (ν ν' : Measure (RefinedGaugeField L K)) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'],
    (∀ G : RefinedGaugeField L K → ℂ,
      IsBoundedBorelInFinitelyManyLinks (refinedLinkValue L K) G →
        ∫ U, G U ∂ν = ∫ U, G U ∂ν') → ν = ν'
def InvarianceNotionsAgree (L K : ℕ) : Prop :=
  (∀ (ν : Measure (RefinedGaugeField L K)) [IsProbabilityMeasure ν] (r : AmbientSpace → AmbientSpace)
    (hr : (euclidean L K).IsReflectionTranslation r),
    (∃ s : LatticeSymmetry (refinedSpacing L K), s.toFun = r) ∧
    ∀ s : LatticeSymmetry (refinedSpacing L K), s.toFun = r →
      (IsInvariantUnderReflectionTranslation ν hr ↔ InfiniteLattice.IsSymmetricUnder ν s)) ∧
  ∀ (ν : Measure (RefinedGaugeField L K)) [IsProbabilityMeasure ν]
    (v : LatticePoint (refinedSpacing L K))
    (hv : (euclidean L K).IsReflectionTranslation (InfiniteLattice.shift v).toFun),
    IsInvariantUnderReflectionTranslation ν hv ↔
      InfiniteLattice.IsSymmetricUnder ν (InfiniteLattice.shift v)
end LatticeGeometry
open LatticeGeometry in
def ReflectionTranslationFacts : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ K : ℕ,
    (∀ m : ℕ, AffineMapDescendsUniquely L m K) ∧
    (SymmetriesFormGroup (euclidean L K) ∧ ∀ m : ℕ, SymmetriesFormGroup (periodic L m K)) ∧
    (SymmetriesPreserveDistances L K ∧ ∀ m : ℕ, SymmetriesPreserveTorusDistances L m K) ∧
    ShiftsAreSymmetries L K ∧
    (∀ lc : ℝ, ReflectionPositivity.Chessboard.IsCellSideOf L lc →
      ReflectionGroupActsOnEuclidean L K lc ∧
        ∀ m : ℕ, 2 * lc ≤ PeriodicLattice.torusSide L m → ReflectionGroupActsOnPeriodic L m K lc) ∧
    ProbabilityMeasuresDeterminedByLocalFunctions L K ∧
    InvarianceNotionsAgree L K
end YangMills.Construction.VolumeTransfer
end
