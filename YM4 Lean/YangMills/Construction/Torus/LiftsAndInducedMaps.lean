import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Torus.TransportRadiusAndMotionsOfFourSpace
import Mathlib
set_option autoImplicit false
open Set Function
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace TorusLifts
open InfiniteLattice (AmbientSpace)
def signedCoordinateEquiv (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) : Equiv.Perm AmbientSpace where
  toFun := PeriodicLattice.CutoffTorus.signedPermEuclidean π s
  invFun := PeriodicLattice.CutoffTorus.signedPermEuclidean π⁻¹ fun ν => s (π.symm ν)
  left_inv x := by
    funext ν
    have hsq : (((s (π.symm ν) : ℤˣ) : ℤ) : ℝ) * (((s (π.symm ν) : ℤˣ) : ℤ) : ℝ) = 1 := by
      rcases Int.units_eq_one_or (s (π.symm ν)) with hs | hs <;> simp [hs]
    simp [PeriodicLattice.CutoffTorus.signedPermEuclidean, ← mul_assoc, hsq]
  right_inv := TorusPeriodization.signedPermEuclidean_inv π s
def hyperoctahedralGroupEuclidean : Subgroup (Equiv.Perm AmbientSpace) where
  carrier := {S | ∃ (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ), S = signedCoordinateEquiv π s}
  mul_mem' := by
    rintro _ _ ⟨π, s, rfl⟩ ⟨π', s', rfl⟩
    refine ⟨π' * π, fun μ => s μ * s' (π μ), Equiv.ext fun x => ?_⟩
    exact TorusPeriodization.signedPermEuclidean_comp π π' s s' x
  one_mem' := ⟨1, fun _ => 1, Equiv.ext fun x => by
    funext μ
    simp [signedCoordinateEquiv, PeriodicLattice.CutoffTorus.signedPermEuclidean]⟩
  inv_mem' := by
    rintro _ ⟨π, s, rfl⟩
    exact ⟨π⁻¹, fun ν => s (π.symm ν), Equiv.ext fun x => rfl⟩
theorem exists_hyperoctahedralEuclidean_torusProj (L m : ℕ)
    {τ : Equiv.Perm (PeriodicLattice.FourTorus L m)}
    (hτ : τ ∈ PeriodicLattice.hyperoctahedralGroup L m) :
    ∃ S ∈ hyperoctahedralGroupEuclidean, ∀ x,
      TorusMetric.torusProj (PeriodicLattice.torusSide L m) (S x) =
        τ (TorusMetric.torusProj (PeriodicLattice.torusSide L m) x) := by
  obtain ⟨π, s, rfl⟩ := hτ
  exact ⟨signedCoordinateEquiv π s, ⟨π, s, rfl⟩,
    fun x => PeriodicLattice.CutoffTorus.torusProj_signedPermEuclidean m π s x⟩
def IsSignedPermOn (S : AmbientSpace → AmbientSpace) (σ : Equiv.Perm (Fin 4))
    (ε : Fin 4 → ℤˣ) : Prop :=
  ∀ μ, S (Pi.single μ 1) = (((ε μ : ℤˣ) : ℤ) : ℝ) • (Pi.single (σ μ) 1 : AmbientSpace)
def axisPerm (S : AmbientSpace → AmbientSpace) : Equiv.Perm (Fin 4) :=
  Classical.epsilon fun σ => ∃ ε, IsSignedPermOn S σ ε
def axisSigns (S : AmbientSpace → AmbientSpace) : Fin 4 → ℤˣ :=
  Classical.epsilon fun ε => IsSignedPermOn S (axisPerm S) ε
def integerLattice : Set AmbientSpace := range fun (k : Fin 4 → ℤ) (μ : Fin 4) => (k μ : ℝ)
def Descends (ℓ ℓ' : ℝ) (f : AmbientSpace → AmbientSpace)
    (Φ : TorusMetric.Torus4 ℓ → TorusMetric.Torus4 ℓ') : Prop :=
  Φ ∘ TorusMetric.torusProj ℓ = TorusMetric.torusProj ℓ' ∘ f
def descendedMap (ℓ ℓ' : ℝ) (f : AmbientSpace → AmbientSpace) (u : TorusMetric.Torus4 ℓ) :
    TorusMetric.Torus4 ℓ' :=
  TorusMetric.torusProj ℓ' (f (TestFunctions.liftPoint u))
def scaledMotion (L : ℕ) (b : ℤ) (S : AmbientSpace → AmbientSpace) (w z : AmbientSpace) :
    AmbientSpace :=
  (L : ℝ) ^ b • S z + w
def straightPath (ℓ : ℝ) (x y' : AmbientSpace) (t : ℝ) : TorusMetric.Torus4 ℓ :=
  TorusMetric.torusProj ℓ (x + t • (y' - x))
def plaquetteVertexSet {a : ℝ} (p : InfiniteLattice.ElementaryPlaquette a) :
    Set (InfiniteLattice.LatticePoint a) :=
  {p.corner, p.corner + InfiniteLattice.axisStep a p.lowAxis,
    p.corner + InfiniteLattice.axisStep a p.lowAxis + InfiniteLattice.axisStep a p.highAxis,
    p.corner + InfiniteLattice.axisStep a p.highAxis}
def projectPlaquette (L m : ℕ) (j : ℤ)
    (p : InfiniteLattice.ElementaryPlaquette (PeriodicLattice.meshSize L j)) :
    PeriodicLattice.Plaquette L m j :=
  ⟨InfiniteLattice.projectPoint L m j p.corner, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
def TorusDistEqMinOverLifts (ℓ : ℝ) : Prop :=
  ∀ (u v : TorusMetric.Torus4 ℓ) (x y : AmbientSpace),
    TorusMetric.torusProj ℓ x = u → TorusMetric.torusProj ℓ y = v →
    IsLeast (range fun k : Fin 4 → ℤ =>
        TorusMetric.euclidNormVec (x - y - TestFunctions.latticeTranslate ℓ k))
        (TorusMetric.torusEuclidNorm (u - v)) ∧
      {k : Fin 4 → ℤ |
        TorusMetric.euclidNormVec (x - y - TestFunctions.latticeTranslate ℓ k) ≤
          TorusMetric.euclidNormVec (x - y)}.Finite ∧
      TorusMetric.torusEuclidNorm (TorusMetric.torusProj ℓ x - TorusMetric.torusProj ℓ y) ≤
        TorusMetric.euclidNormVec (x - y) ∧
      ∃ y' : AmbientSpace, TorusMetric.torusProj ℓ y' = v ∧
        TorusMetric.euclidNormVec (x - y') = TorusMetric.torusEuclidNorm (u - v)
def TorusDistIsMetric (ℓ : ℝ) : Prop :=
  ∃ M : MetricSpace (TorusMetric.Torus4 ℓ),
    (∀ u v, @dist _ M.toPseudoMetricSpace.toDist u v = TorusMetric.torusEuclidNorm (u - v)) ∧
    Continuous[inferInstance, M.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace]
      (TorusMetric.torusProj ℓ) ∧
    @CompactSpace _ M.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
def StraightPathsLipschitz (ℓ : ℝ) : Prop :=
  ∀ (u v : TorusMetric.Torus4 ℓ) (x y' : AmbientSpace),
    TorusMetric.torusProj ℓ x = u → TorusMetric.torusProj ℓ y' = v →
    TorusMetric.euclidNormVec (x - y') = TorusMetric.torusEuclidNorm (u - v) →
    straightPath ℓ x y' 0 = u ∧ straightPath ℓ x y' 1 = v ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1,
        TorusMetric.torusEuclidNorm (straightPath ℓ x y' t - straightPath ℓ x y' t') ≤
          |t - t'| * TorusMetric.torusEuclidNorm (u - v)
def HyperoctahedralEuclideanProperties : Prop :=
  ∀ S ∈ hyperoctahedralGroupEuclidean,
    IsSignedPermOn S (axisPerm S) (axisSigns S) ∧
      (∃ O ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∀ x, S x = Matrix.mulVec O x) ∧
      S '' integerLattice = integerLattice
def ScaledMotionDescends (L m : ℕ) (b : ℤ) (S : AmbientSpace → AmbientSpace)
    (w : AmbientSpace) : Prop :=
  (L : ℝ) ^ b * PeriodicLattice.torusSide L m ∈ PeriodicLattice.torusSides L ∧
    Descends (PeriodicLattice.torusSide L m) ((L : ℝ) ^ b * PeriodicLattice.torusSide L m)
      (scaledMotion L b S w)
      (descendedMap (PeriodicLattice.torusSide L m)
        ((L : ℝ) ^ b * PeriodicLattice.torusSide L m) (scaledMotion L b S w)) ∧
    (∀ Φ, Descends (PeriodicLattice.torusSide L m)
        ((L : ℝ) ^ b * PeriodicLattice.torusSide L m) (scaledMotion L b S w) Φ →
      Φ = descendedMap (PeriodicLattice.torusSide L m)
        ((L : ℝ) ^ b * PeriodicLattice.torusSide L m) (scaledMotion L b S w)) ∧
    Bijective (descendedMap (PeriodicLattice.torusSide L m)
      ((L : ℝ) ^ b * PeriodicLattice.torusSide L m) (scaledMotion L b S w)) ∧
    Bijective (scaledMotion L b S w) ∧
    (∀ Ψ : AmbientSpace → AmbientSpace, LeftInverse Ψ (scaledMotion L b S w) →
      RightInverse Ψ (scaledMotion L b S w) →
      Descends ((L : ℝ) ^ b * PeriodicLattice.torusSide L m) (PeriodicLattice.torusSide L m) Ψ
          (descendedMap ((L : ℝ) ^ b * PeriodicLattice.torusSide L m)
            (PeriodicLattice.torusSide L m) Ψ) ∧
        LeftInverse (descendedMap ((L : ℝ) ^ b * PeriodicLattice.torusSide L m)
            (PeriodicLattice.torusSide L m) Ψ)
          (descendedMap (PeriodicLattice.torusSide L m)
            ((L : ℝ) ^ b * PeriodicLattice.torusSide L m) (scaledMotion L b S w)) ∧
        RightInverse (descendedMap ((L : ℝ) ^ b * PeriodicLattice.torusSide L m)
            (PeriodicLattice.torusSide L m) Ψ)
          (descendedMap (PeriodicLattice.torusSide L m)
            ((L : ℝ) ^ b * PeriodicLattice.torusSide L m) (scaledMotion L b S w))) ∧
    (∀ u v : TorusMetric.Torus4 (PeriodicLattice.torusSide L m),
      TorusMetric.torusEuclidNorm
          (descendedMap (PeriodicLattice.torusSide L m)
              ((L : ℝ) ^ b * PeriodicLattice.torusSide L m) (scaledMotion L b S w) u -
            descendedMap (PeriodicLattice.torusSide L m)
              ((L : ℝ) ^ b * PeriodicLattice.torusSide L m) (scaledMotion L b S w) v) =
        (L : ℝ) ^ b * TorusMetric.torusEuclidNorm (u - v)) ∧
    ∀ (u : TorusMetric.Torus4 (PeriodicLattice.torusSide L m)) (z : AmbientSpace),
      descendedMap (PeriodicLattice.torusSide L m)
          ((L : ℝ) ^ b * PeriodicLattice.torusSide L m) (scaledMotion L b S w)
          (u + TorusMetric.torusProj (PeriodicLattice.torusSide L m) z) =
        descendedMap (PeriodicLattice.torusSide L m)
            ((L : ℝ) ^ b * PeriodicLattice.torusSide L m) (scaledMotion L b S w) u +
          TorusMetric.torusProj ((L : ℝ) ^ b * PeriodicLattice.torusSide L m) ((L : ℝ) ^ b • S z)
def ProjectionOfLattice (L m K : ℕ) : Prop :=
  TorusMetric.torusProj (PeriodicLattice.torusSide L m) ''
        (InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L (K : ℤ)) : Set AmbientSpace) =
      (PeriodicLattice.sublattice L m (K : ℤ) : Set (PeriodicLattice.FourTorus L m)) ∧
    (∀ e : InfiniteLattice.Link (PeriodicLattice.meshSize L (K : ℤ)),
      ((InfiniteLattice.projectLink L m (K : ℤ) e).source : PeriodicLattice.FourTorus L m) =
          TorusMetric.torusProj (PeriodicLattice.torusSide L m) (e.initial : AmbientSpace) ∧
        ((InfiniteLattice.projectLink L m (K : ℤ) e).target : PeriodicLattice.FourTorus L m) =
          TorusMetric.torusProj (PeriodicLattice.torusSide L m) (e.terminal : AmbientSpace) ∧
        (e.IsPositivelyOriented →
          (InfiniteLattice.projectLink L m (K : ℤ) e).IsPositivelyOriented) ∧
        (InfiniteLattice.projectLink L m (K : ℤ) e).opposite =
          InfiniteLattice.projectLink L m (K : ℤ) e.opposite) ∧
    Surjective (InfiniteLattice.projectLink L m (K : ℤ)) ∧
    (∀ p : InfiniteLattice.ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)),
      InfiniteLattice.projectPoint L m (K : ℤ) '' plaquetteVertexSet p =
        (projectPlaquette L m (K : ℤ) p).vertices) ∧
    Surjective (projectPlaquette L m (K : ℤ)) ∧
    ∀ p : InfiniteLattice.ElementaryPlaquette (PeriodicLattice.meshSize L (K : ℤ)),
      (projectPlaquette L m (K : ℤ) p).barycenter =
        TorusMetric.torusProj (PeriodicLattice.torusSide L m) p.center
def LiftsAndDescendedMaps.Statement : Prop :=
  ∀ s : Conventions.StandingParameters,
    TorusDistEqMinOverLifts (PeriodicLattice.torusSide s.L s.m) ∧
      TorusDistIsMetric (PeriodicLattice.torusSide s.L s.m) ∧
      StraightPathsLipschitz (PeriodicLattice.torusSide s.L s.m) ∧
      HyperoctahedralEuclideanProperties ∧
      (∀ (b : ℤ) (S : Equiv.Perm AmbientSpace) (w : AmbientSpace), 1 ≤ ((s.m : ℕ) : ℤ) + b →
        S ∈ hyperoctahedralGroupEuclidean → ScaledMotionDescends s.L s.m b S w) ∧
      ProjectionOfLattice s.L s.m s.K
end TorusLifts
end YangMills.Construction
end
