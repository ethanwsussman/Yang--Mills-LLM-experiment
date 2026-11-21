import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLattice
import YangMills.Construction.Lattice.ConfigurationsAreAProduct
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Function
noncomputable section
namespace YangMills.Construction
namespace InducedPullback
open LatticeCovering (descend spacingIndex period mesh)
open FixedSpacing (Params)
open InfiniteLattice (AmbientSpace hypercubicGroup latticeMotions basisVector)
open PeriodicLattice (Bond CompactGaugeField TorusLatticeSymmetry Site FourTorus translateByVector
  unitStep forwardBonds)
def IsSignedPermutationData (w : AmbientSpace →ₗ[ℝ] AmbientSpace) (σ : Fin 4 → ℤˣ)
    (π : Fin 4 → Fin 4) : Prop :=
  ∀ μ, w (basisVector μ) = (((σ μ : ℤˣ) : ℤ) : ℝ) • basisVector (π μ)
section Bonds
variable {L m : ℕ} {j : ℤ}
def bondEnds (e : Bond L m j) : Set (FourTorus L m) :=
  {(e.source : FourTorus L m), (e.target : FourTorus L m)}
def imageBond (σ : Fin 4 → ℤˣ) (π : Fin 4 → Fin 4) (y : Site L m j) (μ : Fin 4) : Bond L m j :=
  if σ μ = 1 then Bond.forwardFrom y (π μ) else Bond.forwardFrom (y - unitStep L m j (π μ)) (π μ)
def bondSign (σ : Fin 4 → ℤˣ) (e : Bond L m j) : ℤˣ := σ e.axis
end Bonds
section Configurations
variable {L m K : ℕ}
def bondPermutation (g : TorusLatticeSymmetry L m K) (σ : Fin 4 → ℤˣ) (π : Fin 4 → Fin 4)
    (e : Bond L m (K : ℤ)) : Bond L m (K : ℤ) :=
  imageBond σ π (g.pointMap e.source) e.axis
def pullbackConfig (g : TorusLatticeSymmetry L m K) (U : CompactGaugeField L m (K : ℤ)) :
    CompactGaugeField L m (K : ℤ) :=
  g.pullback U
def productHaarOnFields (L m : ℕ) (j : ℤ) : Measure (CompactGaugeField L m j) :=
  (PeriodicLattice.productHaarMeasure L m j).comap fun U : CompactGaugeField L m j => U.1
def PreservesIntegrals (g : TorusLatticeSymmetry L m K)
    (ν : Measure (CompactGaugeField L m (K : ℤ))) : Prop :=
  ∀ Ξ : CompactGaugeField L m (K : ℤ) → ℂ, Measurable Ξ → TestFunctions.IsBoundedFun Ξ →
    ∫ U, Ξ (pullbackConfig g U) ∂ν = ∫ U, Ξ U ∂ν
end Configurations
variable (P : Params)
def MapsPointsAndBonds (r : latticeMotions (mesh P)) (σ : Fin 4 → ℤˣ)
    (π : Fin 4 → Fin 4) : Prop :=
  (∀ (x : FourTorus P.L P.m) (μ : Fin 4),
    descend P r.1 (translateByVector x (mesh P • basisVector μ)) =
      translateByVector (descend P r.1 x)
        ((((σ μ : ℤˣ) : ℤ) : ℝ) • mesh P • basisVector (π μ))) ∧
    (∀ e : Bond P.L P.m (spacingIndex P), ∃ e' : Bond P.L P.m (spacingIndex P),
      (e'.source : FourTorus P.L P.m) = descend P r.1 e.source ∧
        (e'.target : FourTorus P.L P.m) = descend P r.1 e.target) ∧
    ∃ t ∈ latticeMotions (mesh P), LeftInverse t r.1 ∧ RightInverse t r.1 ∧
      LeftInverse (descend P t) (descend P r.1) ∧
      RightInverse (descend P t) (descend P r.1)
def PullbackIsGaugeField (g : TorusLatticeSymmetry P.L P.m (P.K : ℕ)) : Prop :=
  ∀ U : CompactGaugeField P.L P.m (spacingIndex P),
    (fun e => U.1 (g.bondMap e)) ∈ PeriodicLattice.compactGaugeFields P.L P.m (spacingIndex P) ∧
      ∀ e e' : Bond P.L P.m (spacingIndex P), g.IsBondImage e e' →
        (pullbackConfig g U).linkValue e = U.linkValue e'
def PullbackOnPositiveBonds (g : TorusLatticeSymmetry P.L P.m (P.K : ℕ)) (σ : Fin 4 → ℤˣ)
    (π : Fin 4 → Fin 4) : Prop :=
  (∀ (x : Site P.L P.m (spacingIndex P)) (μ : Fin 4),
    bondSign σ (Bond.forwardFrom x μ) = σ μ ∧
      bondPermutation g σ π (Bond.forwardFrom x μ) = imageBond σ π (g.pointMap x) μ ∧
      bondPermutation g σ π (Bond.forwardFrom x μ) ∈ forwardBonds P.L P.m (spacingIndex P) ∧
      bondEnds (bondPermutation g σ π (Bond.forwardFrom x μ)) =
        {g.toFun x, g.toFun (Bond.forwardFrom x μ).target} ∧
      ∀ e' ∈ forwardBonds P.L P.m (spacingIndex P),
        bondEnds e' = {g.toFun x, g.toFun (Bond.forwardFrom x μ).target} →
          e' = bondPermutation g σ π (Bond.forwardFrom x μ)) ∧
    BijOn (bondPermutation g σ π) (forwardBonds P.L P.m (spacingIndex P))
      (forwardBonds P.L P.m (spacingIndex P)) ∧
    ∀ (U : CompactGaugeField P.L P.m (spacingIndex P)) (e : Bond P.L P.m (spacingIndex P)),
      e ∈ forwardBonds P.L P.m (spacingIndex P) →
        (pullbackConfig g U).linkValue e =
          U.linkValue (bondPermutation g σ π e) ^ ((bondSign σ e : ℤˣ) : ℤ)
def PullbackMeasurePreserving (g : TorusLatticeSymmetry P.L P.m (P.K : ℕ)) : Prop :=
  IsHomeomorph (pullbackConfig g) ∧
    PreservesIntegrals g (PeriodicLattice.gaugeFieldMeasure P.L P.m (spacingIndex P)) ∧
    PreservesIntegrals g (productHaarOnFields P.L P.m (spacingIndex P))
def Statement : Prop :=
  ∀ (P : Params) (r : latticeMotions (mesh P)), ∀ w ∈ hypercubicGroup,
    ∀ v ∈ InfiniteLattice.latticeSubgroup (mesh P), (∀ x, r.1 x = w x + v) →
      (∃! q : (Fin 4 → ℤˣ) × (Fin 4 → Fin 4), IsSignedPermutationData w q.1 q.2) ∧
        (∃ g : TorusLatticeSymmetry P.L P.m (P.K : ℕ), g.toFun = descend P r.1) ∧
        ∀ (σ : Fin 4 → ℤˣ) (π : Fin 4 → Fin 4), IsSignedPermutationData w σ π →
          Bijective π ∧ MapsPointsAndBonds P r σ π ∧
            ∀ g : TorusLatticeSymmetry P.L P.m (P.K : ℕ), g.toFun = descend P r.1 →
              PullbackIsGaugeField P g ∧ PullbackOnPositiveBonds P g σ π ∧
                PullbackMeasurePreserving P g
end InducedPullback
end YangMills.Construction
end
