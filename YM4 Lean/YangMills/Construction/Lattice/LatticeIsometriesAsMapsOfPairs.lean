import YangMills.Construction.Conventions.TorusPeriodsAndIsometries
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import YangMills.Construction.Lattice.LevelCoordinates
import YangMills.Construction.Lattice.PlaquetteFramesAndCircuits
import YangMills.Construction.Torus.MapOfATorusInducedByAHypercubicMotion
import YangMills.Construction.Torus.PeriodisationRotationsAndReflections
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.PlaquetteCircuits TorusMetric
open InfiniteLattice (AmbientSpace hypercubicGroup frameLinearMap latticeSubgroup torusAffineMap
  InducesTorusMap)
namespace Conventions.StandingParameters
variable (s : StandingParameters)
abbrev cutoffIndex : ℤ := ((s.K : ℕ) : ℤ)
abbrev LatticeSite : Type := PeriodicLattice.Site s.L s.m s.cutoffIndex
abbrev LatticeBond : Type := PeriodicLattice.Bond s.L s.m s.cutoffIndex
abbrev LatticePlaquette : Type := PeriodicLattice.Plaquette s.L s.m s.cutoffIndex
abbrev meshSteps : Set (Fin 4 → ℝ) := PeriodicLattice.PlaquetteCircuits.meshVectors s.L s.cutoffIndex
def IsAffineTorusMap (f : s.Torus → s.Torus) : Prop :=
  ∃ w ∈ hypercubicGroup, ∃ v ∈ latticeSubgroup s.cutoffMesh, f = torusAffineMap s.L s.m w v
def InducedByAffine (r : s.Torus ≃ s.Torus) (w : AmbientSpace →ₗ[ℝ] AmbientSpace)
    (v : AmbientSpace) : Prop :=
  InducesTorusMap s.L s.m (fun x => w x + v) r
def linearOf (r : s.Torus ≃ s.Torus) : AmbientSpace →ₗ[ℝ] AmbientSpace :=
  frameLinearMap (PeriodicLattice.linearComponent r)
def mapQuadruple (r : s.Torus ≃ s.Torus) (γ : Fin 4 → s.LatticeBond) : Fin 4 → s.LatticeBond :=
  fun i => bondImage r (γ i)
def AffineMapsAreIsometries : Prop :=
  (∀ w ∈ hypercubicGroup, ∀ v ∈ latticeSubgroup s.cutoffMesh,
    ∃ r ∈ s.cutoffLatticeIsometries, (r : s.Torus → s.Torus) = torusAffineMap s.L s.m w v) ∧
  (∀ v ∈ latticeSubgroup s.cutoffMesh, ∀ u : s.LatticeSite,
    (u : s.Torus) = torusProj (PeriodicLattice.torusSide s.L s.m) v →
      s.IsAffineTorusMap (translateBy u)) ∧
  (∀ f : SignedFrame, (SignedFrame.torusEquiv s.L s.m f : s.Torus → s.Torus) =
    torusAffineMap s.L s.m (frameLinearMap f) 0) ∧
  ∀ (μ : Fin 4) (c : ℝ) (hc : ∃ q : ℤ, 2 * c = (q : ℝ) * meshSize s.L s.cutoffIndex),
    s.IsAffineTorusMap (PeriodicFunctions.axisReflection s.L s.m s.K μ c hc)
def IsometriesAreAffine : Prop :=
  (∀ r : s.Torus ≃ s.Torus, IsFlatIsometry r →
    ∃ w ∈ hypercubicGroup, ∃ v : AmbientSpace, s.InducedByAffine r w v ∧
      ∀ w' ∈ hypercubicGroup, ∀ v' : AmbientSpace, s.InducedByAffine r w' v' →
        w' = w ∧ v' - v ∈ s.periodLattice) ∧
  (∀ r ∈ s.cutoffLatticeIsometries, ∀ w ∈ hypercubicGroup, ∀ v : AmbientSpace,
    s.InducedByAffine r w v → v ∈ latticeSubgroup s.cutoffMesh) ∧
  (∀ r ∈ s.cutoffLatticeIsometries, s.IsAffineTorusMap r) ∧
  s.cutoffLatticeIsometries = {r : s.Torus ≃ s.Torus | s.IsAffineTorusMap r} ∧
  s.cutoffLatticeIsometries = PeriodicLattice.latticeIsometries s.L s.m s.cutoffIndex ∧
  ∀ r ∈ s.cutoffLatticeIsometries, ∀ w ∈ hypercubicGroup, ∀ v ∈ latticeSubgroup s.cutoffMesh,
    (r : s.Torus → s.Torus) = torusAffineMap s.L s.m w v → s.linearOf r = w
def LinearPartHom : Prop :=
  ∀ r ∈ s.cutoffLatticeIsometries, ∀ r' ∈ s.cutoffLatticeIsometries,
    (∀ (y : s.Torus) (ζ : AmbientSpace),
      r (s.addVector y ζ) = s.addVector (r y) (s.linearOf r ζ)) ∧
    s.linearOf (r'.trans r) = s.linearOf r ∘ₗ s.linearOf r' ∧
    s.linearOf r.symm ∘ₗ s.linearOf r = LinearMap.id ∧
    s.linearOf r ∘ₗ s.linearOf r.symm = LinearMap.id
def BondFromFormula (r : s.Torus ≃ s.Torus) : Prop :=
  ∀ (y y' : s.LatticeSite) (e e' : s.meshSteps),
    (y' : s.Torus) = r y → e'.1 = s.linearOf r e.1 →
      bondImage r (bondFrom y e) = bondFrom y' e' ∧
      bondFromSegment y' e' = r '' bondFromSegment y e ∧
      ((bondFrom y' e').source : s.Torus) = r y ∧
      ((bondFrom y' e').target : s.Torus) = r (s.addVector y e.1)
def ActionOnBonds : Prop :=
  ∀ r ∈ s.cutoffLatticeIsometries, ∀ r' ∈ s.cutoffLatticeIsometries,
    s.linearOf r '' s.meshSteps = s.meshSteps ∧
    s.BondFromFormula r ∧
    (∀ b : s.LatticeBond, bondImage r b.opposite = (bondImage r b).opposite) ∧
    (∀ b : s.LatticeBond, bondImage (r'.trans r) b = bondImage r (bondImage r' b)) ∧
    Function.Bijective (bondImage r : s.LatticeBond → s.LatticeBond) ∧
    Function.LeftInverse (bondImage r.symm) (bondImage r : s.LatticeBond → s.LatticeBond) ∧
    Function.RightInverse (bondImage r.symm) (bondImage r : s.LatticeBond → s.LatticeBond) ∧
    ∀ b : s.LatticeBond, ((bondImage r b).source : s.Torus) = r b.source ∧
      ((bondImage r b).target : s.Torus) = r b.target
def PlaquetteImageByBarycenter (r : s.Torus ≃ s.Torus) (p : s.LatticePlaquette) : Prop :=
  (plaquetteImage r p).barycenter = r p.barycenter ∧
  (∀ p' : s.LatticePlaquette, p'.barycenter = r p.barycenter → p' = plaquetteImage r p) ∧
  (plaquetteImage r p).face = r '' p.face ∧
  faceSpannedBy (plaquetteImage r p).origin (plaquetteImage r p).firstAxis
      (plaquetteImage r p).secondAxis =
    r '' faceSpannedBy p.origin p.firstAxis p.secondAxis
def CircuitsMapToCircuits (r : s.Torus ≃ s.Torus) (p : s.LatticePlaquette) : Prop :=
  (∀ γ : Fin 4 → s.LatticeBond, IsCircuit p γ →
    IsCircuit (plaquetteImage r p) (s.mapQuadruple r γ)) ∧
  ∀ (e e₁ f f₁ : s.meshSteps) (c c₁ : s.LatticeSite), IsFrame p e e₁ →
    (c : s.Torus) = frameVertex p e e₁ → (c₁ : s.Torus) = r c →
    f.1 = s.linearOf r e.1 → f₁.1 = s.linearOf r e₁.1 →
      s.mapQuadruple r (circuitFrom c e e₁) = circuitFrom c₁ f f₁
def ImageOrigin (r : s.Torus ≃ s.Torus) : Prop :=
  ∀ (x : s.LatticeSite) (μ ν μ' ν' : Fin 4) (h : μ ≠ ν) (u u' : ℝ), (u = 1 ∨ u = -1) →
    (u' = 1 ∨ u' = -1) →
    s.linearOf r (coordVec μ) = u • coordVec μ' →
    s.linearOf r (coordVec ν) = u' • coordVec ν' →
    ∃ h' : μ' ≠ ν', ∃ x' : s.LatticeSite,
      plaquetteImage r (plaquetteSpannedBy x μ ν h) = plaquetteSpannedBy x' μ' ν' h' ∧
      (x' : s.Torus) =
        s.subVector
          (s.subVector (r (plaquetteSpannedBy x μ ν h).barycenter)
            ((s.cutoffMesh / 2) • coordVec μ'))
          ((s.cutoffMesh / 2) • coordVec ν') ∧
      (x' : s.Torus) =
        s.addVector
          (s.addVector (r x)
            (((u - 1) / 2 * s.cutoffMesh) • coordVec μ'))
          (((u' - 1) / 2 * s.cutoffMesh) • coordVec ν')
def ActionOnPlaquettes : Prop :=
  Function.Injective (PeriodicLattice.Plaquette.barycenter : s.LatticePlaquette → s.Torus) ∧
  ∀ r ∈ s.cutoffLatticeIsometries, ∀ r' ∈ s.cutoffLatticeIsometries,
    (∀ p : s.LatticePlaquette, s.PlaquetteImageByBarycenter r p) ∧
    (∀ p : s.LatticePlaquette, plaquetteImage (r'.trans r) p =
      plaquetteImage r (plaquetteImage r' p)) ∧
    Function.Bijective (plaquetteImage r : s.LatticePlaquette → s.LatticePlaquette) ∧
    Function.LeftInverse (plaquetteImage r.symm)
      (plaquetteImage r : s.LatticePlaquette → s.LatticePlaquette) ∧
    Function.RightInverse (plaquetteImage r.symm)
      (plaquetteImage r : s.LatticePlaquette → s.LatticePlaquette) ∧
    (∀ p : s.LatticePlaquette, s.CircuitsMapToCircuits r p) ∧
    s.ImageOrigin r
def AffineDescriptionOfIsometries : Prop :=
  ∀ s : StandingParameters, s.AffineMapsAreIsometries ∧ s.IsometriesAreAffine ∧
    s.LinearPartHom ∧ s.ActionOnBonds ∧ s.ActionOnPlaquettes
end Conventions.StandingParameters
end YangMills.Construction
end
