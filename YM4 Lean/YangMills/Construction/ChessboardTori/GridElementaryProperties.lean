import YangMills.Construction.ChessboardTori.PeriodisationAndInducedMaps
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
def invMap (r : AmbientSpace → AmbientSpace) : AmbientSpace → AmbientSpace := Function.invFun r
def euclidInfDist (y : AmbientSpace) (A : Set AmbientSpace) : ℝ :=
  sInf ((fun w => TorusMetric.euclidNormVec (y - w)) '' A)
namespace ChessboardSetup
variable (D : ChessboardSetup)
def periodTranslations : Subgroup (Equiv.Perm AmbientSpace) where
  carrier := {r | ∃ k : Fin 4 → ℤ, (r : AmbientSpace → AmbientSpace) =
    translate (TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k)}
  mul_mem' := by
    rintro r s ⟨k, hk⟩ ⟨k', hk'⟩
    refine ⟨k + k', funext fun x => funext fun μ => ?_⟩
    simp only [Equiv.Perm.coe_mul, Function.comp, hk, hk', translate,
      TestFunctions.latticeTranslate, Pi.add_apply, Int.cast_add]
    ring
  one_mem' := ⟨0, funext fun x => funext fun μ => by
    simp [translate, TestFunctions.latticeTranslate]⟩
  inv_mem' := by
    rintro r ⟨k, hk⟩
    refine ⟨-k, funext fun x => r.injective ?_⟩
    rw [show r (r⁻¹ x) = x by simp, hk]
    funext μ
    simp [translate, TestFunctions.latticeTranslate]
def IsTorusDistPreserving (f : D.Torus → D.Torus) : Prop :=
  ∀ u v, TorusMetric.torusEuclidNorm (f u - f v) = TorusMetric.torusEuclidNorm (u - v)
def LatticeSymMapsLinksFaces : Prop :=
  ∀ r : D.LatticeSym,
    Function.Surjective r.linkMap ∧ Function.Surjective (D.imageFace r) ∧
    (∀ p, D.faceCorners (D.imageFace r p) = r.pointMap '' D.faceCorners p) ∧
    (∀ p : D.Plaquette, (D.imageFace r p).center = r.toFun p.center) ∧
    ∀ (p : D.Plaquette) (U : D.GaugeField),
      InfiniteLattice.faceEnergy (r.pullbackField U) p =
        InfiniteLattice.faceEnergy U (D.imageFace r p)
def ExpSmearedRules : Prop :=
  ∀ (r : D.LatticeSym) (v w : AmbientSpace → ℂ),
    (∃ C : ℝ, ∀ x, ‖v x‖ ≤ C) → HasBoundedSupport v →
    (∃ C : ℝ, ∀ x, ‖w x‖ ≤ C) → HasBoundedSupport w →
    r.actOn (fun U => Complex.exp (D.smeared v U)) =
        (fun U => Complex.exp (D.smeared (v ∘ invMap r.toFun) U)) ∧
      (fun U => starRingEnd ℂ (Complex.exp (D.smeared v U))) =
        (fun U => Complex.exp (D.smeared (fun x => starRingEnd ℂ (v x)) U)) ∧
      (fun U => Complex.exp (D.smeared v U) * Complex.exp (D.smeared w U)) =
        (fun U => Complex.exp (D.smeared (v + w) U))
end ChessboardSetup
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def PointsOffWallsAndSyms : Prop :=
  (∀ x ∈ D.gridPoints, x ∉ g.walls) ∧
    (∀ r ∈ g.reflectionGroup, PreservesDist r ∧
      r '' (D.gridPoints : Set AmbientSpace) = D.gridPoints) ∧
    ∀ v ∈ D.gridPoints, PreservesDist (translate v) ∧
      translate v '' (D.gridPoints : Set AmbientSpace) = D.gridPoints
def coordShift (t : ℤ) (y : ℝ) : ℝ := y + 2 * t * g.cellSide
def coordReflect (k : ℤ) (y : ℝ) : ℝ := 2 * k * g.cellSide - y
def ActsOnCoord (r : AmbientSpace → AmbientSpace) (μ : Fin 4) (f : ℝ → ℝ) : Prop :=
  ∀ x, r x μ - g.origin μ = f (x μ - g.origin μ)
def ReflectsCoord (r : AmbientSpace → AmbientSpace) (μ : Fin 4) : Prop :=
  ∃ k : ℤ, g.ActsOnCoord r μ (g.coordReflect k)
def IsProductOfCoordMaps (r : AmbientSpace → AmbientSpace) : Prop :=
  ∀ μ, (∃ t : ℤ, g.ActsOnCoord r μ (g.coordShift t)) ∨ g.ReflectsCoord r μ
open Classical in
def numReflectedCoords (r : AmbientSpace → AmbientSpace) : ℕ :=
  (Finset.univ.filter (g.ReflectsCoord r)).card
def ReflectionGroupCoordForm : Prop :=
  (∀ r ∈ g.reflectionGroup, g.IsProductOfCoordMaps r) ∧
    (∀ r : AmbientSpace → AmbientSpace, g.IsProductOfCoordMaps r →
      ∃ s ∈ g.reflectionGroup, (s : AmbientSpace → AmbientSpace) = r) ∧
    (∀ r ∈ g.reflectionGroup, orientationSign r = (-1) ^ g.numReflectedCoords r) ∧
    (∀ r ∈ g.reflectionGroup, ∀ s ∈ g.reflectionGroup,
      orientationSign (r * s : Equiv.Perm AmbientSpace) = orientationSign r * orientationSign s) ∧
    (∀ r ∈ g.reflectionGroup, r '' g.walls = g.walls) ∧
    (∀ r ∈ g.reflectionGroup, ∀ S ∈ g.cellSet, r '' S ∈ g.cellSet) ∧
    (∀ S ∈ g.cellSet, ∀ S' ∈ g.cellSet, ∃! r : g.reflectionGroup, r.1 '' S = S') ∧
    ∀ t : Fin 4 → ℤ, ∃ r ∈ g.reflectionGroup,
      (r : AmbientSpace → AmbientSpace) = translate (fun μ => 2 * g.cellSide * t μ) ∧
        orientationSign r = 1
def TransportRules : Prop :=
  ∀ S ∈ g.cellSet, ∀ S' ∈ g.cellSet, ∀ S'' ∈ g.cellSet, ∀ r : g.reflectionGroup, r.1 '' S = S' →
    ∀ F ∈ cellObservables (D := D) S, ∀ G ∈ cellObservables (D := D) S, ∀ c : ℂ,
      g.transportTo S S' F ∈ cellObservables (D := D) S' ∧
      g.transportTo S S F = F ∧
      g.transportTo S' S'' (g.transportTo S S' F) = g.transportTo S S'' F ∧
      g.transportTo S S' (fun U => starRingEnd ℂ (F U)) =
        (fun U => starRingEnd ℂ (g.transportTo S S' F U)) ∧
      g.transportTo S S' (F * G) = g.transportTo S S' F * g.transportTo S S' G ∧
      g.transportTo S S' (F + G) = g.transportTo S S' F + g.transportTo S S' G ∧
      g.transportTo S S' (fun U => c * F U) =
        (fun U => Conventions.signedConj (orientationSign r.1) c * g.transportTo S S' F U) ∧
      g.transportTo S S' 1 = 1
def DistToWalls : Prop :=
  (∀ y : AmbientSpace, euclidInfDist y g.walls =
      Finset.univ.inf' Finset.univ_nonempty fun μ : Fin 4 =>
        Metric.infDist (y μ - g.origin μ) (range fun k : ℤ => (k : ℝ) * g.cellSide)) ∧
    (∀ y, y ∉ g.walls → ∃! S, S ∈ g.cellSet ∧ y ∈ interior S) ∧
    (∀ S ∈ g.cellSet, ∀ S' ∈ g.cellSet, S ≠ S' → ∀ u ∈ interior S, ∀ v ∈ interior S',
      (segment ℝ u v ∩ g.walls).Nonempty ∧
        euclidInfDist u g.walls + euclidInfDist v g.walls ≤
          TorusMetric.euclidNormVec (u - v)) ∧
    ∀ C : Set AmbientSpace, Convex ℝ C → Disjoint C g.walls → ∃ S ∈ g.cellSet, C ⊆ interior S
def DescendsToTorus : Prop :=
  D.periodTranslations ≤ g.reflectionGroup ∧
    (D.periodTranslations.subgroupOf g.reflectionGroup).Normal ∧
    (∀ r ∈ g.reflectionGroup, ∃ f : D.Torus → D.Torus,
      D.proj ∘ r = f ∘ D.proj ∧ D.IsTorusDistPreserving f) ∧
    ∀ r ∈ g.reflectionGroup, ∀ s ∈ g.reflectionGroup, ∀ f h : D.Torus → D.Torus,
      D.proj ∘ r = f ∘ D.proj → D.proj ∘ s = h ∘ D.proj →
        (f = h ↔ s⁻¹ * r ∈ D.periodTranslations)
def TorusGroupQuotient : Prop :=
  (∃ φ : g.reflectionGroup →* Equiv.Perm D.Torus,
      (∀ r : g.reflectionGroup, D.proj ∘ r.1 = φ r ∘ D.proj) ∧
      φ.ker = D.periodTranslations.subgroupOf g.reflectionGroup ∧
      (fun e : Equiv.Perm D.Torus => (e : D.Torus → D.Torus)) '' (φ.range : Set _) =
        g.inducedTorusMaps) ∧
    (Nat.card g.inducedTorusMaps : ℝ) = g.cellsAcross ^ 4 ∧
    (∀ f ∈ g.inducedTorusMaps, D.IsTorusDistPreserving f) ∧
    (∀ r ∈ g.reflectionGroup, ∀ s ∈ g.reflectionGroup, ∀ f : D.Torus → D.Torus,
      D.proj ∘ r = f ∘ D.proj → D.proj ∘ s = f ∘ D.proj →
        orientationSign r = orientationSign s) ∧
    (∀ f ∈ g.inducedTorusMaps,
      f '' (PeriodicLattice.sublattice D.L D.m ((D.K : ℕ) : ℤ) : Set D.Torus) =
        PeriodicLattice.sublattice D.L D.m ((D.K : ℕ) : ℤ) ∧
      f '' (D.proj '' g.walls) = D.proj '' g.walls) ∧
    (∀ f ∈ g.inducedTorusMaps, ∀ C ∈ g.torusCellSet, f '' C ∈ g.torusCellSet) ∧
    (∀ C ∈ g.torusCellSet, ∀ C' ∈ g.torusCellSet, ∃! f, f ∈ g.inducedTorusMaps ∧ f '' C = C') ∧
    (Nat.card g.torusCellSet : ℝ) = g.cellsAcross ^ 4
def ProjOnCellsAndBlocks : Prop :=
  (∀ B ∈ g.blocks, InjOn D.proj (interior B)) ∧
    (∀ S ∈ g.cellSet, ∀ u ∈ S, ∀ v ∈ S,
      TorusMetric.torusEuclidNorm (D.proj u - D.proj v) =
        TorusMetric.euclidNormVec (u - v)) ∧
    (∀ u : AmbientSpace, TorusMetric.setEuclidDist {D.proj u} (D.proj '' g.walls) =
      ENNReal.ofReal (euclidInfDist u g.walls)) ∧
    ∀ S ∈ g.cellSet, ∀ S' ∈ g.cellSet, D.proj '' S ≠ D.proj '' S' →
      ∀ u ∈ D.proj '' interior S, ∀ v ∈ D.proj '' interior S',
        TorusMetric.setEuclidDist {u} (D.proj '' g.walls) +
            TorusMetric.setEuclidDist {v} (D.proj '' g.walls) ≤
          ENNReal.ofReal (TorusMetric.torusEuclidNorm (u - v))
end ReflectionGrid
end ChessboardTori
end YangMills.Construction
end
