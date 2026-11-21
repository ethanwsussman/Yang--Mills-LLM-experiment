import YangMills.Construction.Lattice.BlocksAndCorridors
import YangMills.Construction.Lattice.ContourPaths
import Mathlib
namespace YangMills.Construction
open Set Filter Asymptotics Matrices PeriodicLattice
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace BackgroundField
section Operators
variable {E F : Type}
def IsAdditiveHomogeneousOn [Add E] [SMul ℝ E] [Add F] [SMul ℝ F] (V : Set E) (T : E → F) :
    Prop :=
  (∀ u ∈ V, ∀ v ∈ V, T (u + v) = T u + T v) ∧ ∀ r : ℝ, ∀ u ∈ V, T (r • u) = r • T u
def IsAdjointBetween (V : Set E) (W : Set F) (innerV : E → E → ℂ) (innerW : F → F → ℂ)
    (T : E → F) (S : F → E) : Prop :=
  MapsTo S W V ∧ ∀ v ∈ V, ∀ w ∈ W, innerW w (T v) = innerV (S w) v
def adjointBetween [Nonempty E] (V : Set E) (W : Set F) (innerV : E → E → ℂ)
    (innerW : F → F → ℂ) (T : E → F) : F → E :=
  Classical.epsilon (IsAdjointBetween V W innerV innerW T)
def IsSymmetricWithQuadraticForm [Add E] [SMul ℝ E] (V : Set E) (inner : E → E → ℂ)
    (q : E → ℂ) (T : E → E) : Prop :=
  MapsTo T V V ∧ IsAdditiveHomogeneousOn V T ∧
    (∀ u ∈ V, ∀ v ∈ V, inner u (T v) = inner (T u) v) ∧ ∀ u ∈ V, inner u (T u) = q u
def symmetricOfQuadraticForm [Nonempty E] [Add E] [SMul ℝ E] (V : Set E) (inner : E → E → ℂ)
    (q : E → ℂ) : E → E :=
  Classical.epsilon (IsSymmetricWithQuadraticForm V inner q)
def IsInverseWithin (V : Set E) (T S : E → E) : Prop :=
  MapsTo S V V ∧ ∀ u ∈ V, T (S u) = u ∧ S (T u) = u
def inverseWithin [Nonempty E] (V : Set E) (T : E → E) : E → E :=
  Classical.epsilon (IsInverseWithin V T)
def IsOrthogonalProjectionOnto [Sub E] (V W : Set E) (inner : E → E → ℂ) (P : E → E) : Prop :=
  MapsTo P V W ∧ ∀ u ∈ V, ∀ w ∈ W, inner (u - P u) w = 0
def orthogonalProjectionOnto [Nonempty E] [Sub E] (V W : Set E) (inner : E → E → ℂ) :
    E → E :=
  Classical.epsilon (IsOrthogonalProjectionOnto V W inner)
end Operators
def halfTraceNormSq (X : ComplexMatrix2) : ℝ :=
  (ComplexMatrix2.halfTrace (X.conjTranspose * X)).re
def IsSpectralAngleMatrix (X A : ComplexMatrix2) : Prop :=
  ∃ (r : ℕ) (θ : Fin r → ℝ) (P : Fin r → ComplexMatrix2), Function.Injective θ ∧
    (∀ i, θ i ∈ Ioc (-Real.pi) Real.pi) ∧ (∀ i, (P i).conjTranspose = P i) ∧
    (∀ i k, P i * P k = if i = k then P i else 0) ∧ ∑ i, P i = 1 ∧
    X = ∑ i, Complex.exp (Complex.I * (θ i : ℂ)) • P i ∧ A = ∑ i, (θ i : ℂ) • P i
open Classical in
def unitaryLog (X : ComplexMatrix2) : ComplexMatrix2 :=
  if ComplexMatrix2.operatorNorm (X - 1) < 1 then ComplexMatrix2.logSeries X
  else Complex.I • Classical.epsilon (IsSpectralAngleMatrix X)
def angleMatrix (X : ComplexMatrix2) : ComplexMatrix2 := (Complex.I)⁻¹ • unitaryLog X
section Geometry
variable {L m K : ℕ}
abbrev FineSite (L m K : ℕ) : Type := SiteAtLevel L m K 0
abbrev FineBond (L m K : ℕ) : Type := BondAtLevel L m K 0
abbrev FinePlaquette (L m K : ℕ) : Type := PlaquetteAtLevel L m K 0
def meshAtLevel (L t j : ℕ) : ℝ := (L : ℝ) ^ j * finestMeshInLevelUnits L t
def cornerLattice (L m K j : ℕ) : Set (FourTorus L m) :=
  {x | x ∈ sublattice L m (levelDepth K 0) ∧ ∃ n : Fin 4 → ℤ, ∀ μ,
    x μ = (((n μ : ℝ) * ((L : ℝ) ^ j * meshSize L K) : ℝ) : AddCircle (torusSide L m))}
def diagonalShift (L m K j : ℕ) : FourTorus L m :=
  fun _ => (((((L : ℝ) ^ j - 1) / 2 * meshSize L K : ℝ)) : AddCircle (torusSide L m))
def centeringShift (L m K : ℕ) (x : FourTorus L m) : FourTorus L m :=
  x - diagonalShift L m K (K + m)
def blockFromCorner (L m K l j : ℕ) (y : FourTorus L m) : Set (FourTorus L m) :=
  {x | x ∈ cornerLattice L m K l ∧ ∃ n : Fin 4 → ℕ, (∀ μ, n μ < L ^ (j - l)) ∧
    x = y + ∑ μ, pointOnAxis L m μ ((n μ : ℝ) * ((L : ℝ) ^ l * meshSize L K))}
def centeredBlock (L m K l j : ℕ) (z : FourTorus L m) : Set (FourTorus L m) :=
  centeringShift L m K '' blockFromCorner L m K l j (z + diagonalShift L m K (K + m))
def centeredPoint {j : ℕ} (y : SiteAtLevel L m K j) : FourTorus L m :=
  (y : FourTorus L m) - diagonalShift L m K j
def siteOfCenteredPoint (j : ℕ) (p : FourTorus L m) : SiteAtLevel L m K j :=
  Classical.epsilon fun z : SiteAtLevel L m K j => centeredPoint z = p
def blockSites (l : ℕ) {j : ℕ} (y : SiteAtLevel L m K j) : Set (SiteAtLevel L m K l) :=
  {x | centeredPoint x ∈ centeredBlock L m K l j (centeredPoint y)}
abbrev fineBlock {j : ℕ} (y : SiteAtLevel L m K j) : Set (FineSite L m K) := blockSites 0 y
abbrev childBlock {j : ℕ} (y : SiteAtLevel L m K (j + 1)) : Set (SiteAtLevel L m K j) :=
  blockSites j y
def fineBlockUnion {j : ℕ} (Λ : Set (SiteAtLevel L m K j)) : Set (FineSite L m K) :=
  ⋃ y ∈ Λ, fineBlock y
def levelSitesOf (j : ℕ) (Ω : Set (FineSite L m K)) : Set (SiteAtLevel L m K j) :=
  {y | ∃ x ∈ Ω, (x : FourTorus L m) = centeredPoint y}
def bondsTouching {j : ℤ} (S : Set (Site L m j)) : Set (Bond L m j) :=
  {b | b.source ∈ S ∨ b.target ∈ S}
end Geometry
section Derivatives
variable {L m K : ℕ}
def algebraFunctionsSupportedIn (S : Set (FineSite L m K)) :
    Set (FineSite L m K → ComplexMatrix2) :=
  {f | (∀ x, f x ∈ ComplexMatrix2.hermitianTraceless) ∧ ∀ x, x ∉ S → f x = 0}
def algebraBondForms (L m K j : ℕ) : Set (BondAtLevel L m K j → ComplexMatrix2) :=
  {A | IsBondForm compactLieAlgebra A}
def bondFormsSupportedNear (S : Set (FineSite L m K)) : Set (FineBond L m K → ComplexMatrix2) :=
  {A | A ∈ algebraBondForms L m K 0 ∧ ∀ b, b ∉ bondsTouching S → A b = 0}
def algebraPlaquetteFunctions (L m K : ℕ) : Set (FinePlaquette L m K → ComplexMatrix2) :=
  {F | ∀ p, F p ∈ ComplexMatrix2.hermitianTraceless}
def siteL2Inner (t : ℕ) (f g : FineSite L m K → ComplexMatrix2) : ℂ :=
  siteInner (finestMeshInLevelUnits L t) f g
def bondL2Inner (t : ℕ) (A B : FineBond L m K → ComplexMatrix2) : ℂ :=
  bondFormInner (finestMeshInLevelUnits L t) A B
def plaquetteL2Inner (t : ℕ) (F G : FinePlaquette L m K → ComplexMatrix2) : ℂ :=
  ((finestMeshInLevelUnits L t ^ 4 : ℝ) : ℂ) * ∑ᶠ p, ComplexMatrix2.halfTrace (F p * G p)
open Classical in
def antisymmetricExtension {j : ℤ} (f : Bond L m j → ComplexMatrix2) :
    Bond L m j → ComplexMatrix2 :=
  fun b => if b.IsPositivelyOriented then f b else -f b.opposite
def covariantSiteDerivative (t : ℕ) (U : FineBond L m K → ComplexMatrix2)
    (f : FineSite L m K → ComplexMatrix2) : FineBond L m K → ComplexMatrix2 :=
  antisymmetricExtension fun b =>
    ((finestMeshInLevelUnits L t : ℂ))⁻¹ •
      (ComplexMatrix2.conjugateBy (U b) (f b.target) - f b.source)
namespace PlaquetteEdges
variable {j : ℤ}
def secondCorner (p : Plaquette L m j) : Site L m j := p.origin + unitStep L m j p.firstAxis
def fourthCorner (p : Plaquette L m j) : Site L m j := p.origin + unitStep L m j p.secondAxis
def firstEdge (p : Plaquette L m j) : Bond L m j := Bond.forwardFrom p.origin p.firstAxis
def secondEdge (p : Plaquette L m j) : Bond L m j :=
  Bond.forwardFrom (secondCorner p) p.secondAxis
def sideEdge (p : Plaquette L m j) : Bond L m j := Bond.forwardFrom p.origin p.secondAxis
def thirdEdge (p : Plaquette L m j) : Bond L m j :=
  (Bond.forwardFrom (fourthCorner p) p.firstAxis).opposite
def fourthEdge (p : Plaquette L m j) : Bond L m j := (sideEdge p).opposite
end PlaquetteEdges
open PlaquetteEdges in
def parallelTransportedEdges (U A : FineBond L m K → ComplexMatrix2) (p : FinePlaquette L m K) :
    Fin 4 → ComplexMatrix2 :=
  ![ComplexMatrix2.conjugateBy (U (sideEdge p)) (A (thirdEdge p)), A (fourthEdge p),
    A (firstEdge p), ComplexMatrix2.conjugateBy (U (firstEdge p)) (A (secondEdge p))]
open PlaquetteEdges in
def unscaledPlaquetteDerivative (U A : FineBond L m K → ComplexMatrix2)
    (p : FinePlaquette L m K) : ComplexMatrix2 :=
  A (firstEdge p) + ComplexMatrix2.conjugateBy (U (firstEdge p)) (A (secondEdge p)) +
    ComplexMatrix2.conjugateBy (U (sideEdge p)) (A (thirdEdge p)) + A (fourthEdge p)
def covariantPlaquetteDerivative (t : ℕ) (U A : FineBond L m K → ComplexMatrix2) :
    FinePlaquette L m K → ComplexMatrix2 :=
  fun p => ((finestMeshInLevelUnits L t : ℂ))⁻¹ • unscaledPlaquetteDerivative U A p
def covariantSiteDerivativeAdjoint (t : ℕ) (U : FineBond L m K → ComplexMatrix2) :
    (FineBond L m K → ComplexMatrix2) → FineSite L m K → ComplexMatrix2 :=
  adjointBetween (algebraFunctionsSupportedIn univ) (algebraBondForms L m K 0) (siteL2Inner t)
    (bondL2Inner t) (covariantSiteDerivative t U)
def covariantPlaquetteDerivativeAdjoint (t : ℕ) (U : FineBond L m K → ComplexMatrix2) :
    (FinePlaquette L m K → ComplexMatrix2) → FineBond L m K → ComplexMatrix2 :=
  adjointBetween (algebraBondForms L m K 0) (algebraPlaquetteFunctions L m K) (bondL2Inner t)
    (plaquetteL2Inner t) (covariantPlaquetteDerivative t U)
def covariantSiteLaplacian (t : ℕ) (U : FineBond L m K → ComplexMatrix2)
    (f : FineSite L m K → ComplexMatrix2) : FineSite L m K → ComplexMatrix2 :=
  covariantSiteDerivativeAdjoint t U (covariantSiteDerivative t U f)
def hermitianRealPart (W : ComplexMatrix2) : ComplexMatrix2 := (1 / 2 : ℂ) • (W + W⁻¹)
def hermitianImaginaryPart (W : ComplexMatrix2) : ComplexMatrix2 :=
  (2 * Complex.I)⁻¹ • (W - W⁻¹)
def orderedCommutatorSum (U A : FineBond L m K → ComplexMatrix2) (p : FinePlaquette L m K) :
    ComplexMatrix2 :=
  ∑ i : Fin 4, ∑ k ∈ Finset.Ioi i, Complex.I •
    (parallelTransportedEdges U A p i * parallelTransportedEdges U A p k -
      parallelTransportedEdges U A p k * parallelTransportedEdges U A p i)
def curvatureQuadraticForm (t : ℕ) (U A : FineBond L m K → ComplexMatrix2) : ℂ :=
  ∑ᶠ p : FinePlaquette L m K, ((finestMeshInLevelUnits L t ^ 4 : ℝ) : ℂ) *
    (ComplexMatrix2.halfTrace (unscaledPlaquetteDerivative U A p ^ 2 *
        (((finestMeshInLevelUnits L t ^ 2 : ℝ) : ℂ)⁻¹ •
          (hermitianRealPart (plaquetteHolonomy U p) - 1))) +
      ComplexMatrix2.halfTrace (orderedCommutatorSum U A p *
        (((finestMeshInLevelUnits L t ^ 2 : ℝ) : ℂ)⁻¹ •
          hermitianImaginaryPart (plaquetteHolonomy U p))))
def backgroundBondLaplacian (t : ℕ) (U : FineBond L m K → ComplexMatrix2) :
    (FineBond L m K → ComplexMatrix2) → FineBond L m K → ComplexMatrix2 :=
  symmetricOfQuadraticForm (algebraBondForms L m K 0) (bondL2Inner t) fun A =>
    bondL2Inner t A
        (covariantPlaquetteDerivativeAdjoint t U (covariantPlaquetteDerivative t U A)) +
      curvatureQuadraticForm t U A
end Derivatives
section Sequence
variable {L m K : ℕ}
def IsCubeUnion (X : Set (FourTorus L m)) : Prop :=
  ∃ i : ℤ, -(m : ℤ) ≤ i ∧ ∃ S : Set (Site L m i), X = ⋃ y ∈ S, cubeAround y
structure NestedRegions (L m t : ℕ) where
  set : Fin (t + 1) → Set (FourTorus L m)
  isCubeUnion : ∀ n, IsCubeUnion (set n)
  antitone : Antitone set
variable {t : ℕ}
namespace NestedRegions
variable (𝔰 : NestedRegions L m t)
open Classical in
def regionAt (n : ℕ) : Set (FourTorus L m) := if h : n < t + 1 then 𝔰.set ⟨n, h⟩ else ∅
def fineSitesOf (K n : ℕ) : Set (FineSite L m K) := sitesIn (𝔰.regionAt n)
def shellSites (K j : ℕ) : Set (SiteAtLevel L m K j) :=
  levelSitesOf j (𝔰.fineSitesOf K j) \ levelSitesOf j (𝔰.fineSitesOf K (j + 1))
def shellBonds (K j : ℕ) : Set (BondAtLevel L m K j) :=
  bondsTouching (levelSitesOf j (𝔰.fineSitesOf K j)) \
    bondsTouching (levelSitesOf j (𝔰.fineSitesOf K (j + 1)))
def shellPoints (K : ℕ) : Set (FourTorus L m) :=
  ⋃ j ∈ Finset.range (t + 1), centeredPoint '' 𝔰.shellSites K j
abbrev ShellSite (K : ℕ) : Type :=
  {q : Σ j : ℕ, SiteAtLevel L m K j // q.1 ≤ t ∧ q.2 ∈ 𝔰.shellSites K q.1}
end NestedRegions
open Classical in
def restrictSites (S : Set (FineSite L m K)) (f : FineSite L m K → ComplexMatrix2) :
    FineSite L m K → ComplexMatrix2 :=
  fun x => if x ∈ S then f x else 0
open Classical in
def restrictBonds (S : Set (FineSite L m K)) (A : FineBond L m K → ComplexMatrix2) :
    FineBond L m K → ComplexMatrix2 :=
  fun b => if b ∈ bondsTouching S then A b else 0
end Sequence
section Averages
variable {L m K : ℕ}
def inverseBlockVolume (L : ℕ) : ℂ := ((L : ℂ) ^ 4)⁻¹
def cornerOfBlock {j : ℕ} (y : SiteAtLevel L m K (j + 1)) : SiteAtLevel L m K j :=
  siteOfCenteredPoint j (centeredPoint y)
def stepsFromCorner {j : ℕ} (y : SiteAtLevel L m K (j + 1)) (x : SiteAtLevel L m K j) :
    Fin 4 → ℕ :=
  Classical.epsilon fun n => (∀ μ, n μ < L) ∧
    centeredPoint x =
      centeredPoint y + ∑ μ, pointOnAxis L m μ ((n μ : ℝ) * meshSize L (levelDepth K j))
def blockPath {j : ℕ} (y : SiteAtLevel L m K (j + 1)) (x : SiteAtLevel L m K j) :
    List (BondAtLevel L m K j) :=
  stepsThroughAxes (fun μ => (stepsFromCorner y x μ : ℤ)) (cornerOfBlock y) [3, 2, 1, 0]
def bondPath {j : ℕ} (c : BondAtLevel L m K (j + 1)) (x : SiteAtLevel L m K j) :
    List (BondAtLevel L m K j) :=
  blockPath c.source x ++ crossingPath c x ++
    reversePath (blockPath c.target (shiftAcross c x))
def axialHolonomy {j : ℕ} (U : BondAtLevel L m K j → ComplexMatrix2)
    (c : BondAtLevel L m K (j + 1)) : ComplexMatrix2 :=
  pathHolonomy U (axialPath (cornerOfBlock c.source) (cornerOfBlock c.target))
def averagedField {j : ℕ} (U : BondAtLevel L m K j → ComplexMatrix2)
    (c : BondAtLevel L m K (j + 1)) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (Complex.I • ∑ᶠ (x) (_ : x ∈ childBlock c.source), inverseBlockVolume L •
      angleMatrix (pathHolonomy U (bondPath c x) * (axialHolonomy U c)⁻¹)) *
    axialHolonomy U c
def iteratedAveragedField (U : FineBond L m K → ComplexMatrix2) :
    (j : ℕ) → BondAtLevel L m K j → ComplexMatrix2
  | 0 => U
  | j + 1 => averagedField (iteratedAveragedField U j)
def ancestorSite (i : ℕ) (x : FineSite L m K) : SiteAtLevel L m K i :=
  Classical.epsilon fun z => x ∈ fineBlock z
def siteAverageStep {j : ℕ} (V : BondAtLevel L m K j → ComplexMatrix2)
    (f : SiteAtLevel L m K j → ComplexMatrix2) : SiteAtLevel L m K (j + 1) → ComplexMatrix2 :=
  fun y => ∑ᶠ (x) (_ : x ∈ childBlock y),
    inverseBlockVolume L • ComplexMatrix2.conjugateBy (pathHolonomy V (blockPath y x)) (f x)
def iteratedSiteAverage (U : FineBond L m K → ComplexMatrix2) :
    (j : ℕ) → (FineSite L m K → ComplexMatrix2) → SiteAtLevel L m K j → ComplexMatrix2
  | 0 => fun f => f
  | j + 1 => fun f => siteAverageStep (iteratedAveragedField U j) (iteratedSiteAverage U j f)
def averagingCoefficient (L : ℕ) (a : ℝ) : ℕ → ℝ
  | 0 => a
  | 1 => a
  | j + 2 => a * averagingCoefficient L a (j + 1) /
      (a * ((L : ℝ) ^ 2)⁻¹ + averagingCoefficient L a (j + 1))
variable {t : ℕ} (𝔰 : NestedRegions L m t)
def shellAverage (K : ℕ) (U : FineBond L m K → ComplexMatrix2)
    (f : FineSite L m K → ComplexMatrix2) : 𝔰.ShellSite K → ComplexMatrix2 :=
  fun q => iteratedSiteAverage U q.1.1 f q.1.2
abbrev regionL2 (K : ℕ) : Set (FineSite L m K → ComplexMatrix2) :=
  algebraFunctionsSupportedIn (𝔰.fineSitesOf K 0)
def siteAverageQuadraticForm (K : ℕ) (a : ℝ) (U : FineBond L m K → ComplexMatrix2)
    (f : FineSite L m K → ComplexMatrix2) : ℂ :=
  ∑ j ∈ Finset.range (t + 1), ((averagingCoefficient L a j : ℝ) : ℂ) *
    ∑ᶠ (y) (_ : y ∈ 𝔰.shellSites K j),
      ((meshAtLevel L t j ^ 2 * halfTraceNormSq (iteratedSiteAverage U j f y) : ℝ) : ℂ)
def siteAveragePenalty (K : ℕ) (a : ℝ) (U : FineBond L m K → ComplexMatrix2) :
    (FineSite L m K → ComplexMatrix2) → FineSite L m K → ComplexMatrix2 :=
  symmetricOfQuadraticForm (regionL2 𝔰 K) (siteL2Inner t) (siteAverageQuadraticForm 𝔰 K a U)
end Averages
section BondAverages
variable {L m K : ℕ}
open Classical in
def fieldOfPositiveValues {j : ℤ} (f : Bond L m j → ComplexMatrix2) :
    Bond L m j → ComplexMatrix2 :=
  fun b => if b.IsPositivelyOriented then f b else (f b.opposite)⁻¹
def transportedProductAfter {j : ℤ} (V₀ V₁ : Bond L m j → ComplexMatrix2)
    (before : List (Bond L m j)) : List (Bond L m j) → ComplexMatrix2
  | [] => 1
  | b :: γ => ComplexMatrix2.conjugateBy (pathHolonomy V₀ before) (V₁ b) *
      transportedProductAfter V₀ V₁ (before ++ [b]) γ
def transportedPathProduct {j : ℤ} (V₀ V₁ : Bond L m j → ComplexMatrix2)
    (γ : List (Bond L m j)) : ComplexMatrix2 :=
  transportedProductAfter V₀ V₁ [] γ
def siteDressingMatrix {j : ℕ} (V₀ V₁ : BondAtLevel L m K j → ComplexMatrix2)
    (y : SiteAtLevel L m K (j + 1)) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (Complex.I • ∑ᶠ (x) (_ : x ∈ childBlock y), inverseBlockVolume L •
    angleMatrix (transportedPathProduct V₀ V₁ (blockPath y x)))
def fieldProduct {j : ℤ} (V₁ V₀ : Bond L m j → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  fieldOfPositiveValues fun b => V₁ b * V₀ b
def relativeAverageStep {j : ℕ} (V₀ V₁ : BondAtLevel L m K j → ComplexMatrix2) :
    BondAtLevel L m K (j + 1) → ComplexMatrix2 :=
  fieldOfPositiveValues fun c =>
    (siteDressingMatrix V₀ V₁ c.source)⁻¹ * averagedField (fieldProduct V₁ V₀) c *
      (averagedField V₀ c)⁻¹ *
      ComplexMatrix2.conjugateBy (averagedField V₀ c) (siteDressingMatrix V₀ V₁ c.target)
def iteratedRelativeAveragedField (U₀ U₁ : FineBond L m K → ComplexMatrix2) :
    (j : ℕ) → BondAtLevel L m K j → ComplexMatrix2
  | 0 => U₁
  | j + 1 => relativeAverageStep (iteratedAveragedField U₀ j)
      (iteratedRelativeAveragedField U₀ U₁ j)
def relativeAverageAngle (U B : FineBond L m K → ComplexMatrix2) (j : ℕ)
    (c : BondAtLevel L m K j) : ComplexMatrix2 :=
  angleMatrix (iteratedRelativeAveragedField U (expGaugeField B) j c)
def IsLinearizedAverageAt (t : ℕ) (U : FineBond L m K → ComplexMatrix2) {j : ℕ}
    (c : BondAtLevel L m K j) (T : (FineBond L m K → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  IsAdditiveHomogeneousOn (algebraBondForms L m K 0) T ∧
    MapsTo T (algebraBondForms L m K 0) compactLieAlgebra ∧
    ∀ A ∈ algebraBondForms L m K 0,
    (fun s : ℝ => relativeAverageAngle U (((s * finestMeshInLevelUnits L t : ℝ) : ℂ) • A) j c -
        ((s * meshAtLevel L t j : ℝ) : ℂ) • T A) =O[𝓝 0] fun s => s ^ 2
def linearizedAverage (t : ℕ) (U : FineBond L m K → ComplexMatrix2) :
    (j : ℕ) → (FineBond L m K → ComplexMatrix2) → BondAtLevel L m K j → ComplexMatrix2
  | 0 => fun A => A
  | j + 1 => fun A =>
    antisymmetricExtension fun c =>
      Classical.epsilon (IsLinearizedAverageAt t U (j := j + 1) c) A
variable {t : ℕ} (𝔰 : NestedRegions L m t)
open Classical in
def bondAverageQuadraticForm (K : ℕ) (a : ℝ) (U A : FineBond L m K → ComplexMatrix2) : ℂ :=
  ∑ j ∈ Finset.range (t + 1), (a : ℂ) *
    ∑ᶠ (b) (_ : b ∈ 𝔰.shellBonds K j ∩ {b | b.IsPositivelyOriented}),
      ((meshAtLevel L t j ^ 2 * halfTraceNormSq (linearizedAverage t U j A b) : ℝ) : ℂ)
def bondAveragePenalty (K : ℕ) (a : ℝ) (U : FineBond L m K → ComplexMatrix2) :
    (FineBond L m K → ComplexMatrix2) → FineBond L m K → ComplexMatrix2 :=
  symmetricOfQuadraticForm (algebraBondForms L m K 0) (bondL2Inner t)
    (bondAverageQuadraticForm 𝔰 K a U)
end BondAverages
section GreenOperators
variable {L m K t : ℕ} (𝔰 : NestedRegions L m t) (a : ℝ) (U : FineBond L m K → ComplexMatrix2)
def shellAverageKernel : Set (FineSite L m K → ComplexMatrix2) :=
  {f | f ∈ regionL2 𝔰 K ∧ shellAverage 𝔰 K U f = 0}
def laplacianKernelProjection :
    (FineSite L m K → ComplexMatrix2) → FineSite L m K → ComplexMatrix2 :=
  orthogonalProjectionOnto (regionL2 𝔰 K) (covariantSiteLaplacian t U '' shellAverageKernel 𝔰 U)
    (siteL2Inner t)
def regionSiteOperator (f : FineSite L m K → ComplexMatrix2) : FineSite L m K → ComplexMatrix2 :=
  restrictSites (𝔰.fineSitesOf K 0)
    (covariantSiteLaplacian t U (restrictSites (𝔰.fineSitesOf K 0) f) +
      siteAveragePenalty 𝔰 K a U (restrictSites (𝔰.fineSitesOf K 0) f))
def siteGreen : (FineSite L m K → ComplexMatrix2) → FineSite L m K → ComplexMatrix2 :=
  inverseWithin (regionL2 𝔰 K) (regionSiteOperator 𝔰 a U)
end GreenOperators
end BackgroundField
end
end YangMills.Construction
