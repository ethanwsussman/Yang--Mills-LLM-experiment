import YangMills.Construction.InfiniteLattice.BondsIsometriesAndStatesOfTheLatticeOfACutoff
import YangMills.Construction.Lattice.ActionOfLatticeIsometries
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import Mathlib
set_option autoImplicit false
open Function Set
noncomputable section
namespace YangMills.Construction
namespace RefinedLatticeSymmetries
open InfiniteLattice CutoffLatticeStates
abbrev MeshStep (L K : ℕ) : Type := ↥(PeriodicLattice.PlaquetteCircuits.meshVectors L (K : ℤ))
def axisStep (L K : ℕ) (μ : Fin 4) : MeshStep L K :=
  ⟨PeriodicLattice.PlaquetteCircuits.meshVector L (K : ℤ) μ, μ, Or.inl rfl⟩
abbrev RefinedMotion (L K : ℕ) : Type := ↥(refinedLatticeMotions L K)
section Actions
variable {L K : ℕ}
abbrev pointImage (r : RefinedMotion L K) :
    LatticePoint (refinedSpacing L K) → LatticePoint (refinedSpacing L K) :=
  (latticeMotionSymmetry r).pointMap
abbrev linkImage (r : RefinedMotion L K) :
    Link (refinedSpacing L K) → Link (refinedSpacing L K) :=
  (latticeMotionSymmetry r).linkMap
def realTraceLoop (U : GaugeField (refinedSpacing L K))
    (γ : Fin 4 → Link (refinedSpacing L K)) : ℝ :=
  (Matrices.ComplexMatrix2.fullTrace (loopHolonomy U γ : Matrices.ComplexMatrix2)).re
end Actions
def MotionsActOnSpace (L m K : ℕ) : Prop :=
  (id ∈ refinedLatticeMotions L K) ∧
    (∀ t ∈ refinedLatticeMotions L K, ∀ t' ∈ refinedLatticeMotions L K,
      t ∘ t' ∈ refinedLatticeMotions L K) ∧
    ∀ r : RefinedMotion L K,
      (∃! q, IsAffineDecomposition (refinedSpacing L K) r.1 q) ∧
      Bijective r.1 ∧
      (∀ x y, TorusMetric.euclidNormVec (r.1 x - r.1 y) = TorusMetric.euclidNormVec (x - y)) ∧
      r.1 '' (refinedLattice L K : Set AmbientSpace) = refinedLattice L K ∧
      motionInverse r ∈ refinedLatticeMotions L K ∧
      LeftInverse (motionInverse r) r.1 ∧ RightInverse (motionInverse r) r.1 ∧
      (∀ x, TorusMetric.torusProj (PeriodicLattice.torusSide L m) (r.1 x) =
        inducedTorusMap L m r (TorusMetric.torusProj (PeriodicLattice.torusSide L m) x)) ∧
      ∀ (w : AmbientSpace →ₗ[ℝ] AmbientSpace) (v : AmbientSpace),
        IsAffineDecomposition (refinedSpacing L K) r.1 (w, v) →
        (∀ y ζ, r.1 (y + ζ) = r.1 y + w ζ) ∧
        (∀ (r' : RefinedMotion L K) (w' : AmbientSpace →ₗ[ℝ] AmbientSpace) (v' : AmbientSpace),
          IsAffineDecomposition (refinedSpacing L K) r'.1 (w', v') →
            IsAffineDecomposition (refinedSpacing L K) (r.1 ∘ r'.1) (w ∘ₗ w', w v' + v)) ∧
        ∃ w₁ : AmbientSpace →ₗ[ℝ] AmbientSpace, w₁ ∘ₗ w = LinearMap.id ∧ w ∘ₗ w₁ = LinearMap.id ∧
          IsAffineDecomposition (refinedSpacing L K) (motionInverse r) (w₁, -w₁ v)
def LinksUnderMotions (L K : ℕ) : Prop :=
  (∀ b : Link (refinedSpacing L K), ∃! q : LatticePoint (refinedSpacing L K) × MeshStep L K,
    linkAlong q.1 q.2 = b) ∧
    (∀ (y : LatticePoint (refinedSpacing L K)) (e : MeshStep L K),
      (linkAlong y e).IsPositivelyOriented ↔ ∃ μ, e = axisStep L K μ) ∧
    (∀ (y : LatticePoint (refinedSpacing L K)) (e : MeshStep L K),
      (linkAlong y e).opposite = linkAlong (y + meshSite e) (-e)) ∧
    ∀ r : RefinedMotion L K,
      (∀ b, linkImage r b.opposite = (linkImage r b).opposite) ∧
      (∀ r' t : RefinedMotion L K, t.1 = r.1 ∘ r'.1 →
        ∀ b, linkImage t b = linkImage r (linkImage r' b)) ∧
      Bijective (linkImage r) ∧
      (∀ t : RefinedMotion L K, t.1 = motionInverse r →
        LeftInverse (linkImage t) (linkImage r) ∧
          RightInverse (linkImage t) (linkImage r)) ∧
      ∀ (w : AmbientSpace →ₗ[ℝ] AmbientSpace) (v : AmbientSpace),
        IsAffineDecomposition (refinedSpacing L K) r.1 (w, v) →
        w '' PeriodicLattice.PlaquetteCircuits.meshVectors L (K : ℤ) =
            PeriodicLattice.PlaquetteCircuits.meshVectors L (K : ℤ) ∧
          ∀ (y : LatticePoint (refinedSpacing L K)) (e f : MeshStep L K), f.1 = w e.1 →
            linkImage r (linkAlong y e) = linkAlong (pointImage r y) f
def PlaquetteFrames (L K : ℕ) : Prop :=
  (∀ (x x' : LatticePoint (refinedSpacing L K)) (μ ν μ' ν' : Fin 4) (h : μ ≠ ν) (h' : μ' ≠ ν'),
    (plaquetteOfAxes x μ ν h).closedSquare = (plaquetteOfAxes x' μ' ν' h').closedSquare →
      x = x' ∧ s(μ, ν) = s(μ', ν')) ∧
    (∀ (x x' : LatticePoint (refinedSpacing L K)) (μ ν μ' ν' : Fin 4) (h : μ ≠ ν) (h' : μ' ≠ ν'),
      (plaquetteOfAxes x μ ν h).center = (plaquetteOfAxes x' μ' ν' h').center →
        x = x' ∧ s(μ, ν) = s(μ', ν')) ∧
    (∀ (p : ElementaryPlaquette (refinedSpacing L K)) (e e' : MeshStep L K), IsFrame p e e' →
      frameBase p e e' ∈ refinedLattice L K ∧
        frameBase p e e' + e.1 ∈ refinedLattice L K ∧
        frameBase p e e' + e.1 + e'.1 ∈ refinedLattice L K ∧
        frameBase p e e' + e'.1 ∈ refinedLattice L K) ∧
    ∀ (x : LatticePoint (refinedSpacing L K)) (μ ν : Fin 4) (h : μ < ν)
      (U : GaugeField (refinedSpacing L K)),
      faceHolonomy U ⟨x, μ, ν, h⟩ =
        loopHolonomy U (circuitFrom x (axisStep L K μ) (axisStep L K ν))
def PlaquettesUnderMotions (L K : ℕ) : Prop :=
  ∀ r : RefinedMotion L K,
    (∀ p : ElementaryPlaquette (refinedSpacing L K), ∃! q : ElementaryPlaquette (refinedSpacing L K),
      q.closedSquare = p.squareImage r.1) ∧
    (∀ p : ElementaryPlaquette (refinedSpacing L K),
      (mapPlaquette r p).closedSquare = p.squareImage r.1) ∧
    (∀ p : ElementaryPlaquette (refinedSpacing L K),
      (mapPlaquette r p).center = r.1 p.center) ∧
    (∀ r' t : RefinedMotion L K, t.1 = r.1 ∘ r'.1 →
      ∀ p, mapPlaquette t p = mapPlaquette r (mapPlaquette r' p)) ∧
    Bijective (mapPlaquette r) ∧
    (∀ t : RefinedMotion L K, t.1 = motionInverse r →
      LeftInverse (mapPlaquette t) (mapPlaquette r) ∧
        RightInverse (mapPlaquette t) (mapPlaquette r)) ∧
    ∀ (w : AmbientSpace →ₗ[ℝ] AmbientSpace) (v : AmbientSpace),
      IsAffineDecomposition (refinedSpacing L K) r.1 (w, v) →
      (∀ (x : LatticePoint (refinedSpacing L K)) (μ ν μ' ν' : Fin 4) (h : μ ≠ ν) (u u' : ℤˣ),
        w (basisVector μ) = (((u : ℤ) : ℝ)) • basisVector μ' →
        w (basisVector ν) = (((u' : ℤ) : ℝ)) • basisVector ν' →
          ∃ (h' : μ' ≠ ν') (x' : LatticePoint (refinedSpacing L K)),
            (x' : AmbientSpace) = r.1 x +
              (((((u : ℤ) : ℝ) - 1) / 2) • PeriodicLattice.PlaquetteCircuits.meshVector L (K : ℤ) μ') +
              (((((u' : ℤ) : ℝ) - 1) / 2) • PeriodicLattice.PlaquetteCircuits.meshVector L (K : ℤ) ν') ∧
            mapPlaquette r (plaquetteOfAxes x μ ν h) = plaquetteOfAxes x' μ' ν' h') ∧
      ∀ (p : ElementaryPlaquette (refinedSpacing L K)) (e e' f f' : MeshStep L K)
        (c : LatticePoint (refinedSpacing L K)),
        IsFrame p e e' → (c : AmbientSpace) = frameBase p e e' → f.1 = w e.1 → f'.1 = w e'.1 →
          IsFrame (mapPlaquette r p) f f' ∧
            frameBase (mapPlaquette r p) f f' = r.1 c ∧
            mapLoop r (circuitFrom c e e') = circuitFrom (pointImage r c) f f'
def CircuitsOfPlaquette (L K : ℕ) : Prop :=
  ∀ p : ElementaryPlaquette (refinedSpacing L K),
    (∀ (e e' : MeshStep L K) (c : LatticePoint (refinedSpacing L K)),
      IsFrame p e e' → (c : AmbientSpace) = frameBase p e e' →
        ![circuitFrom c e e' 1, circuitFrom c e e' 2, circuitFrom c e e' 3, circuitFrom c e e' 0] =
            circuitFrom (c + meshSite e) e' (-e) ∧
          ![(circuitFrom c e e' 3).opposite, (circuitFrom c e e' 2).opposite,
              (circuitFrom c e e' 1).opposite, (circuitFrom c e e' 0).opposite] =
            circuitFrom c e' e ∧
          IsCircuit p (circuitFrom (c + meshSite e) e' (-e)) ∧
          IsCircuit p (circuitFrom c e' e)) ∧
    {γ | IsCircuit p γ}.ncard = 8 ∧
    (∀ (U : GaugeField (refinedSpacing L K)) (γ γ' : Fin 4 → Link (refinedSpacing L K)),
      IsCircuit p γ → IsCircuit p γ' → realTraceLoop U γ = realTraceLoop U γ') ∧
    (∀ (U : GaugeField (refinedSpacing L K)) (γ : Fin 4 → Link (refinedSpacing L K)),
      IsCircuit p γ → faceEnergy U p = 1 - (1 / 2) * realTraceLoop U γ) ∧
    Continuous (fun U : GaugeField (refinedSpacing L K) => faceEnergy U p) ∧
    ∀ U : GaugeField (refinedSpacing L K), faceEnergy U p ∈ Icc (0 : ℝ) 2
def FieldsUnderMotions (L K : ℕ) : Prop :=
  ∀ r : RefinedMotion L K,
    (∀ r' t : RefinedMotion L K, t.1 = r.1 ∘ r'.1 →
      latticeMotionField t = latticeMotionField r' ∘ latticeMotionField r) ∧
    (∀ t : RefinedMotion L K, t.1 = motionInverse r →
      ∃ h : GaugeField (refinedSpacing L K) ≃ₜ GaugeField (refinedSpacing L K),
        ⇑h = latticeMotionField r ∧ ⇑h.symm = latticeMotionField t) ∧
    ∀ (U : GaugeField (refinedSpacing L K)) (γ : Fin 4 → Link (refinedSpacing L K)),
      loopHolonomy (latticeMotionField r U) γ =
        loopHolonomy U (mapLoop r γ)
def ProjectionOfLinksAndFields (L m K : ℕ) : Prop :=
  (∀ (y : LatticePoint (refinedSpacing L K)) (e : MeshStep L K),
    projectLink L m (K : ℤ) (linkAlong y e) =
      PeriodicLattice.PlaquetteCircuits.bondFrom (projectPoint L m (K : ℤ) y) e) ∧
    (∀ b : Link (refinedSpacing L K),
      projectLink L m (K : ℤ) b.opposite = (projectLink L m (K : ℤ) b).opposite) ∧
    Continuous (liftCompactField : PeriodicLattice.CompactGaugeField L m (K : ℤ) → _) ∧
    ∀ r : RefinedMotion L K,
      (∃ s : PeriodicLattice.TorusLatticeSymmetry L m K, s.toFun = inducedTorusMap L m r) ∧
      ∀ s : PeriodicLattice.TorusLatticeSymmetry L m K, s.toFun = inducedTorusMap L m r →
        (∀ b, projectLink L m (K : ℤ) (linkImage r b) = s.bondMap (projectLink L m (K : ℤ) b)) ∧
        ∀ V : PeriodicLattice.CompactGaugeField L m (K : ℤ),
          latticeMotionField r (liftCompactField V) =
            liftCompactField (s.pullback V)
def RefinedLatticeSymmetryTheorem : Prop :=
  ∀ s : Conventions.StandingParameters,
    MotionsActOnSpace s.L s.m s.K ∧
      LinksUnderMotions s.L s.K ∧
      PlaquetteFrames s.L s.K ∧
      PlaquettesUnderMotions s.L s.K ∧
      CircuitsOfPlaquette s.L s.K ∧
      FieldsUnderMotions s.L s.K ∧
      ProjectionOfLinksAndFields s.L s.m s.K
end RefinedLatticeSymmetries
end YangMills.Construction
end
