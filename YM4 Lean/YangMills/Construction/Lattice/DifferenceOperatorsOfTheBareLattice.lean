import YangMills.Construction.Lattice.DirichletDifferenceOperators
import YangMills.Construction.Lattice.SeparatedSequenceData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace DirichletOperators
variable {L m K : ℕ}
def forwardDifferenceAdjoint (t : ℕ) (μ : Fin 4) (u : ZeroForms L m K) : ZeroForms L m K :=
  fun x => (finestMeshInLevelUnits L t)⁻¹ * (u (x - unitStep L m (levelDepth K 0) μ) - u x)
def normSq (L t : ℕ) {ι : Type} (u : ι → ℝ) : ℝ := latticeInner L t u u
def oppositeEnd (e : BareBond L m K) (x : BareSite L m K) : BareSite L m K :=
  open Classical in if e.1.source = x then e.1.target else e.1.source
def frontierBondsAt (K : ℕ) (U : Set (FourTorus L m)) (x : BareSite L m K) : Set (BareBond L m K) :=
  {e | e ∈ frontierBonds K U ∧ (e.1.source = x ∨ e.1.target = x)}
namespace BareLatticeOperators
def DifferenceAdjointsCommute (L m K t : ℕ) : Prop :=
  (∀ (μ : Fin 4) (u v : ZeroForms L m K),
    latticeInner L t v (forwardDifference t μ u) = latticeInner L t (forwardDifferenceAdjoint t μ v) u) ∧
  (∀ (μ ν : Fin 4) (u : ZeroForms L m K),
    forwardDifference t μ (forwardDifference t ν u) = forwardDifference t ν (forwardDifference t μ u)) ∧
  (∀ (μ ν : Fin 4) (u : ZeroForms L m K),
    forwardDifference t μ (forwardDifferenceAdjoint t ν u) =
      forwardDifferenceAdjoint t ν (forwardDifference t μ u)) ∧
  (∀ (μ ν : Fin 4) (u : ZeroForms L m K),
    forwardDifferenceAdjoint t μ (forwardDifferenceAdjoint t ν u) =
      forwardDifferenceAdjoint t ν (forwardDifferenceAdjoint t μ u))
def WholeLatticeFormulas (L m K t : ℕ) : Prop :=
  (∀ A : OneForms L m K, gradAdjoint L m K t A = ∑ μ, forwardDifferenceAdjoint t μ (axisComponent A μ)) ∧
  (∀ (A : OneForms L m K) (x : BareSite L m K), gradAdjoint L m K t A x =
    ∑ μ, (finestMeshInLevelUnits L t)⁻¹ *
      (axisComponent A μ (x - unitStep L m (levelDepth K 0) μ) - axisComponent A μ x)) ∧
  (∀ u : ZeroForms L m K, scalarLaplacian L m K t u =
    ∑ μ, forwardDifferenceAdjoint t μ (forwardDifference t μ u)) ∧
  (∀ (u : ZeroForms L m K) (x : BareSite L m K), scalarLaplacian L m K t u x =
    (finestMeshInLevelUnits L t ^ 2)⁻¹ * ∑ μ,
      ((u x - u (x + unitStep L m (levelDepth K 0) μ)) + (u x - u (x - unitStep L m (levelDepth K 0) μ)))) ∧
  (∀ u : ZeroForms L m K, curl t (grad t u) = 0) ∧
  (∀ u : ZeroForms L m K, grad t u = 0 → ∀ x y, u x = u y)
def SummationByParts (L m K t : ℕ) : Prop :=
  ∀ A : OneForms L m K,
    normSq L t (curl t A) = (1 / 2 : ℝ) * ∑ μ, ∑ ν,
      normSq L t (forwardDifference t μ (axisComponent A ν) - forwardDifference t ν (axisComponent A μ)) ∧
    (1 / 2 : ℝ) * ∑ μ, ∑ ν,
        normSq L t (forwardDifference t μ (axisComponent A ν) - forwardDifference t ν (axisComponent A μ)) =
      ∑ μ, ∑ ν, normSq L t (forwardDifference t μ (axisComponent A ν)) -
        normSq L t (gradAdjoint L m K t A) ∧
    latticeInner L t A (hodgeLaplacian L m K t A) =
      ∑ μ, ∑ ν, normSq L t (forwardDifference t μ (axisComponent A ν)) ∧
    ∑ μ, ∑ ν, normSq L t (forwardDifference t μ (axisComponent A ν)) =
      ∑ ν, latticeInner L t (axisComponent A ν) (scalarLaplacian L m K t (axisComponent A ν))
def FrameProjections (K : ℕ) (U : Set (FourTorus L m)) : Prop :=
  (∀ φ : BondFrame, bondProjection K U φ + frontierProjection K U φ = indicatorMul (starBonds K U)) ∧
  frontierProjection K U BondFrame.star = 0 ∧
  frontierProjection K U BondFrame.interior = indicatorMul (frontierBonds K U) ∧
  ∀ e ∈ frontierBonds K U, Xor (e.1.source ∈ sitesOfRegion K U) (e.1.target ∈ sitesOfRegion K U)
def WholeTorusFrames (L m K : ℕ) : Prop :=
  sitesOfRegion K (Set.univ : Set (FourTorus L m)) = Set.univ ∧
  (∀ φ : BondFrame, framedBonds K (Set.univ : Set (FourTorus L m)) φ = Set.univ) ∧
  (∀ φ : BondFrame, framedPlaquettes K (Set.univ : Set (FourTorus L m)) φ = Set.univ) ∧
  frontierBonds K (Set.univ : Set (FourTorus L m)) = ∅ ∧
  frontierSites K (Set.univ : Set (FourTorus L m)) = ∅
def DirichletGradAdjointIdentity (K t : ℕ) (U : Set (FourTorus L m)) : Prop :=
  ∀ (φ : BondFrame) (u : zeroFormsOn K U) (A : oneFormsOn K U φ),
    latticeInner L t (A : OneForms L m K) (dirichletGrad K t U φ u : OneForms L m K) =
      latticeInner L t (dirichletGradAdjoint K t U φ A : ZeroForms L m K) (u : ZeroForms L m K)
def DirichletZeroFormFacts (K t : ℕ) (U : Set (FourTorus L m)) : Prop :=
  ∀ u : zeroFormsOn K U,
    (∀ e, e ∉ starBonds K U → grad t (u : ZeroForms L m K) e = 0) ∧
    (∀ e ∈ frontierBonds K U, ∀ x ∈ sitesOfRegion K U, (e.1.source = x ∨ e.1.target = x) →
      grad t (u : ZeroForms L m K) e = (finestMeshInLevelUnits L t)⁻¹ * (u : ZeroForms L m K) x ∨
        grad t (u : ZeroForms L m K) e = -((finestMeshInLevelUnits L t)⁻¹ * (u : ZeroForms L m K) x)) ∧
    latticeInner L t (u : ZeroForms L m K) (dirichletLaplacian K t U u : ZeroForms L m K) =
      normSq L t (grad t (u : ZeroForms L m K)) ∧
    normSq L t (grad t (u : ZeroForms L m K)) =
      finestMeshInLevelUnits L t ^ 4 * ∑ᶠ e ∈ starBonds K U, |grad t (u : ZeroForms L m K) e| ^ 2
def DirichletOneFormFacts (K t : ℕ) (U : Set (FourTorus L m)) : Prop :=
  ∀ (φ : BondFrame) (A : oneFormsOn K U φ),
    (∀ p, p ∉ framedPlaquettes K U φ → curl t (A : OneForms L m K) p = 0) ∧
    latticeInner L t (A : OneForms L m K) (dirichletCurlCurl K t U φ A : OneForms L m K) =
      normSq L t (curl t (A : OneForms L m K)) ∧
    normSq L t (curl t (A : OneForms L m K)) =
      finestMeshInLevelUnits L t ^ 4 * ∑ᶠ p ∈ framedPlaquettes K U φ, |curl t (A : OneForms L m K) p| ^ 2
def LaplacianRowsOutside (K t : ℕ) (U : Set (FourTorus L m)) : Prop :=
  ∀ (u : zeroFormsOn K U) (x : BareSite L m K), x ∉ sitesOfRegion K U →
    (∀ e ∈ frontierBondsAt K U x, oppositeEnd e x ∈ frontierSites K U) ∧
    scalarLaplacian L m K t (u : ZeroForms L m K) x =
      -((finestMeshInLevelUnits L t ^ 2)⁻¹ *
        ∑ᶠ e ∈ frontierBondsAt K U x, (u : ZeroForms L m K) (oppositeEnd e x))
def Statement : Prop :=
  ∀ P : SeparatedSequences.BaseParameters,
    DifferenceAdjointsCommute P.L P.m P.K P.t ∧
    WholeLatticeFormulas P.L P.m P.K P.t ∧
    SummationByParts P.L P.m P.K P.t ∧
    WholeTorusFrames P.L P.m P.K ∧
    ∀ U : Set (FourTorus P.L P.m),
      FrameProjections P.K U ∧
      DirichletGradAdjointIdentity P.K P.t U ∧
      DirichletZeroFormFacts P.K P.t U ∧
      DirichletOneFormFacts P.K P.t U ∧
      LaplacianRowsOutside P.K P.t U
end BareLatticeOperators
end DirichletOperators
end PeriodicLattice
end YangMills.Construction
