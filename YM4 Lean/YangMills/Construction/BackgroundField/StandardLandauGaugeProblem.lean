import YangMills.Construction.BackgroundField.SecondOrderOfTheAverages
import YangMills.Construction.BackgroundField.SitePropagatorBounds
import YangMills.Construction.Lattice.SmallLandauPairsOnAnAxialTowerDefs
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.BackgroundField
section Averages
variable {L m K : ℕ}
def blockGaugeAverage {j : ℕ} (V₀ : BondAtLevel L m K j → ComplexMatrix2)
    (v : SiteAtLevel L m K j → ComplexMatrix2) (y : SiteAtLevel L m K (j + 1)) : ComplexMatrix2 :=
  v (cornerOfBlock y) * ComplexMatrix2.matExp (Complex.I • ∑ᶠ (x) (_ : x ∈ childBlock y),
    inverseBlockVolume L • angleMatrix ((v (cornerOfBlock y))⁻¹ *
      ComplexMatrix2.conjugateBy (pathHolonomy V₀ (blockPath y x)) (v x)))
def levelGaugeAverage (U₀ : FineBond L m K → ComplexMatrix2) (g : FineSite L m K → ComplexMatrix2) :
    (j : ℕ) → SiteAtLevel L m K j → ComplexMatrix2
  | 0 => g
  | j + 1 => blockGaugeAverage (iteratedAveragedField U₀ j) (levelGaugeAverage U₀ g j)
def relativeGaugeTransform (U₀ : FineBond L m K → ComplexMatrix2) (g : FineSite L m K → ComplexMatrix2)
    (V : FineBond L m K → ComplexMatrix2) : FineBond L m K → ComplexMatrix2 :=
  fieldOfPositiveValues fun e => g e.source * V e * ComplexMatrix2.conjugateBy (U₀ e) (g e.target)⁻¹
def relativeAveragedField (U₀ V : FineBond L m K → ComplexMatrix2) (n : ℕ) :
    BondAtLevel L m K n → ComplexMatrix2 :=
  fieldOfPositiveValues fun e =>
    iteratedAveragedField (fieldProduct V U₀) n e * (iteratedAveragedField U₀ n e)⁻¹
def crossingBondValue (U₀ V : FineBond L m K → ComplexMatrix2) {j : ℕ}
    (c : BondAtLevel L m K (j + 1)) : ComplexMatrix2 :=
  (siteDressingMatrix (iteratedAveragedField U₀ j) (relativeAveragedField U₀ V j) c.source)⁻¹ *
    relativeAveragedField U₀ V (j + 1) c
end Averages
section Problem
variable {L m K t : ℕ} (Ω : NestedRegions L m t)
def IsInAxialGauge (K : ℕ) (U₀ V : FineBond L m K → ComplexMatrix2) : Prop :=
  ∀ j, 1 ≤ j → j ≤ t → ∀ y ∈ Ω.shellSites K j, ∀ x ∈ fineBlock y, ∀ n < j,
    transportedPathProduct (iteratedAveragedField U₀ n) (relativeAveragedField U₀ V n)
      (blockPath (ancestorSite (n + 1) x) (ancestorSite n x)) = 1
open Classical in
def prescribedAverageForm (K : ℕ) (U₀ V : FineBond L m K → ComplexMatrix2) :
    (j : ℕ) → BondAtLevel L m K j → ComplexMatrix2
  | 0 => fun e => angleMatrix (relativeAveragedField U₀ V 0 e)
  | j + 1 => antisymmetricExtension fun e =>
    if e.source ∈ Ω.shellSites K (j + 1) then
      if e.target ∈ Ω.shellSites K (j + 1) then angleMatrix (relativeAveragedField U₀ V (j + 1) e)
      else angleMatrix (relativeAveragedField U₀ V (j + 1) e *
        ComplexMatrix2.conjugateBy (iteratedAveragedField U₀ (j + 1) e)
          (siteDressingMatrix (iteratedAveragedField U₀ j) (relativeAveragedField U₀ V j) e.target))
    else angleMatrix (crossingBondValue U₀ V e)
def IsRegionGaugeTransformation (K : ℕ) (g : FineSite L m K → ComplexMatrix2) : Prop :=
  (∀ x ∈ Ω.fineSitesOf K 0, g x ∈ compactGaugeGroup) ∧ ∀ x, x ∉ Ω.fineSitesOf K 0 → g x = 1
def HasTrivialAverages (K : ℕ) (U₀ : FineBond L m K → ComplexMatrix2)
    (g : FineSite L m K → ComplexMatrix2) : Prop :=
  ∀ j ≤ t, ∀ y ∈ Ω.shellSites K j, levelGaugeAverage U₀ g j y = 1
def IsExpOfBondForm (K : ℕ) (U₁ A : FineBond L m K → ComplexMatrix2) : Prop :=
  A ∈ bondFormsSupportedNear (Ω.fineSitesOf K 0) ∧ ∀ e ∈ bondsTouching (Ω.fineSitesOf K 0),
    U₁ e = ComplexMatrix2.matExp (Complex.I • (((finestMeshInLevelUnits L t : ℝ) : ℂ) • A e))
def LandauGaugeCondition (K : ℕ) (U₀ A : FineBond L m K → ComplexMatrix2) : Prop :=
  laplacianKernelProjection Ω U₀
    (restrictSites (Ω.fineSitesOf K 0) (covariantSiteDerivativeAdjoint t U₀ A)) = 0
def HasAveragesEqual (K : ℕ) (U₀ A : FineBond L m K → ComplexMatrix2)
    (B : (j : ℕ) → BondAtLevel L m K j → ComplexMatrix2) : Prop :=
  ∀ j ≤ t, ∀ e ∈ Ω.shellBonds K j,
    relativeAverageAngle U₀ (((finestMeshInLevelUnits L t : ℝ) : ℂ) • A) j e = B j e
def IsSmallOnShells (K : ℕ) (α₁ : ℝ) (B : (j : ℕ) → BondAtLevel L m K j → ComplexMatrix2) : Prop :=
  ∀ j ≤ t, ∀ e ∈ Ω.shellBonds K j, ComplexMatrix2.operatorNorm (B j e) < 2 * 4 * (L : ℝ) * α₁
def IsGeodesicPath {j : ℤ} (γ : List (Bond L m j)) (x x' : Site L m j) : Prop :=
  IsBondPathFromTo γ x x' ∧ ∀ γ', IsBondPathFromTo γ' x x' → γ.length ≤ γ'.length
def formCovGradient (t : ℕ) (U₀ A : FineBond L m K → ComplexMatrix2) (μ ν : Fin 4)
    (x : FineSite L m K) : ComplexMatrix2 :=
  covDeriv (finestMeshInLevelUnits L t) U₀ μ (bondFormComponent A ν) x
structure FirstOrderFormBounds (K : ℕ) (U₀ A : FineBond L m K → ComplexMatrix2) (C : ℝ)
    (Cβ : ℝ → ℝ) : Prop where
  sup : ∀ j ≤ t, ∀ e ∈ bondsTouching (Ω.fineSitesOf K j),
    ComplexMatrix2.operatorNorm (A e) < C * (meshAtLevel L t j)⁻¹
  grad : ∀ j ≤ t, ∀ x ∈ Ω.fineSitesOf K j, ∀ μ ν : Fin 4,
    ComplexMatrix2.operatorNorm (formCovGradient t U₀ A μ ν x) < C * (meshAtLevel L t j ^ 2)⁻¹
  holder : ∀ β₀ β : ℝ, 0 ≤ β → β ≤ β₀ → β₀ < 1 → ∀ j ≤ t, ∀ x ∈ Ω.fineSitesOf K j,
    ∀ x' ∈ Ω.fineSitesOf K j, x ≠ x' →
      scaledTorusDistance L K t (x : FourTorus L m) (x' : FourTorus L m) ≤ 1 →
      ∀ γ, IsGeodesicPath γ x x' → ∀ μ ν : Fin 4,
        ComplexMatrix2.operatorNorm (ComplexMatrix2.conjugateBy (pathHolonomy U₀ γ)
            (formCovGradient t U₀ A μ ν x') - formCovGradient t U₀ A μ ν x) /
          scaledTorusDistance L K t (x : FourTorus L m) (x' : FourTorus L m) ^ β <
        Cβ β₀ * meshAtLevel L t j ^ (-2 - β)
structure GreenFormBounds (K : ℕ) (U₀ A : FineBond L m K → ComplexMatrix2) (C : ℝ)
    (Cβ : ℝ → ℝ) : Prop
    extends FirstOrderFormBounds Ω K U₀ A C Cβ where
  lap : ∀ j ≤ t, ∀ x ∈ Ω.fineSitesOf K j, ∀ μ : Fin 4,
    ComplexMatrix2.operatorNorm (covariantSiteLaplacian t U₀ (bondFormComponent A μ) x) <
      C * (meshAtLevel L t j ^ 3)⁻¹
structure LandauFormBounds (K : ℕ) (U₀ A : FineBond L m K → ComplexMatrix2) (C : ℝ)
    (Cβ : ℝ → ℝ) : Prop
    extends GreenFormBounds Ω K U₀ A C Cβ where
  curvature : ∀ j ≤ t, ∀ e ∈ bondsTouching (Ω.fineSitesOf K j),
    ComplexMatrix2.operatorNorm
        (covariantPlaquetteDerivativeAdjoint t U₀ (covariantPlaquetteDerivative t U₀ A) e) <
      C * (meshAtLevel L t j ^ 3)⁻¹
structure AxialGaugeData (e K : ℕ) (c α₀ α₁ : ℝ) (U₀ V : FineBond L m K → ComplexMatrix2) : Prop where
  background : U₀ ∈ smallFieldConfigurations Ω K α₀
  cubes : RegularOnShellCubes Ω e K c α₀ U₀
  gaugeField : IsGaugeField compactGaugeGroup univ V
  regular : fieldProduct V U₀ ∈ smallFieldConfigurations Ω K α₀
  axial : IsInAxialGauge Ω K U₀ V
  averages : ∀ j ≤ t, ∀ f ∈ Ω.shellBonds K j,
    ComplexMatrix2.operatorNorm
      (iteratedAveragedField (fieldProduct V U₀) j f - iteratedAveragedField U₀ j f) < α₁
def IsLandauGaugeImage (K : ℕ) (α₁ C : ℝ) (Cβ : ℝ → ℝ) (U₀ V U₁ : FineBond L m K → ComplexMatrix2) :
    Prop :=
  ∃ A, IsExpOfBondForm Ω K U₁ A ∧ LandauFormBounds Ω K U₀ A C Cβ ∧
    HasAveragesEqual Ω K U₀ A (prescribedAverageForm Ω K U₀ V) ∧
    IsSmallOnShells Ω K α₁ (prescribedAverageForm Ω K U₀ V) ∧ LandauGaugeCondition Ω K U₀ A
def landauOp (U A : FineBond L m K → ComplexMatrix2) : FineBond L m K → ComplexMatrix2 :=
  covariantPlaquetteDerivativeAdjoint t U (covariantPlaquetteDerivative t U A) +
    covariantSiteDerivative t U
      (laplacianKernelProjection Ω U
        (restrictSites (Ω.fineSitesOf K 0) (covariantSiteDerivativeAdjoint t U A))) +
    bondAveragePenalty Ω K 1 U A
def landauOpRestricted (U A : FineBond L m K → ComplexMatrix2) : FineBond L m K → ComplexMatrix2 :=
  restrictBonds (Ω.fineSitesOf K 0) (landauOp Ω U (restrictBonds (Ω.fineSitesOf K 0) A))
def landauGreen (U : FineBond L m K → ComplexMatrix2) :
    (FineBond L m K → ComplexMatrix2) → FineBond L m K → ComplexMatrix2 :=
  inverseWithin (bondFormsSupportedNear (Ω.fineSitesOf K 0)) (landauOpRestricted Ω U)
def OnLandauHyperplane (K : ℕ) (U : FineBond L m K → ComplexMatrix2)
    (B : (j : ℕ) → BondAtLevel L m K j → ComplexMatrix2) (A : FineBond L m K → ComplexMatrix2) : Prop :=
  A ∈ bondFormsSupportedNear (Ω.fineSitesOf K 0) ∧
    (∀ j ≤ t, ∀ f ∈ Ω.shellBonds K j,
      ((meshAtLevel L t j : ℝ) : ℂ) • linearizedAverage t U j A f = B j f) ∧
    LandauGaugeCondition Ω K U A
def IsLandauMinimizer (K : ℕ) (U : FineBond L m K → ComplexMatrix2)
    (B : (j : ℕ) → BondAtLevel L m K j → ComplexMatrix2) (A : FineBond L m K → ComplexMatrix2) : Prop :=
  OnLandauHyperplane Ω K U B A ∧ ∀ A', OnLandauHyperplane Ω K U B A' →
    (1 / 2 : ℝ) * (bondL2Inner t A (backgroundBondLaplacian t U A)).re ≤
      (1 / 2 : ℝ) * (bondL2Inner t A' (backgroundBondLaplacian t U A')).re
def landauMinimizer (K : ℕ) (U : FineBond L m K → ComplexMatrix2)
    (B : (j : ℕ) → BondAtLevel L m K j → ComplexMatrix2) : FineBond L m K → ComplexMatrix2 :=
  Classical.epsilon (IsLandauMinimizer Ω K U B)
end Problem
structure GaugeFixingConstants where
  cubeConst : ℝ
  B₀ : ℝ
  B₀β : ℝ → ℝ
  upper : ℝ
  c₁ : ℝ
instance instNonemptyGaugeFixingConstants : Nonempty GaugeFixingConstants :=
  ⟨⟨0, 0, fun _ => 0, 0, 0⟩⟩
def GaugeFixingConstants.B₁ (N : GaugeFixingConstants) (L : ℕ) : ℝ := 5 * 4 * (L : ℝ) * N.B₀
def GaugeFixingConstants.B₂ (N : GaugeFixingConstants) (L : ℕ) (β₀ : ℝ) : ℝ :=
  5 * 4 * (L : ℝ) * N.B₀β β₀
def BoundsGreenOperators (L e r : ℕ) (N : GaugeFixingConstants) : Prop :=
  ∀ (m K t : ℕ) (Ω : NestedRegions L m t), 0 < m → IsDomainSequence e r K Ω →
    ShellCubesCoverPlaquettes Ω e K N.cubeConst → ∀ (α₀ : ℝ) (U₀ : FineBond L m K → ComplexMatrix2),
      0 < α₀ → α₀ ≤ N.upper →
      U₀ ∈ smallFieldConfigurations Ω K α₀ →
      RegularOnShellCubes Ω e K N.cubeConst α₀ U₀ → ∀ n : ℝ, 0 < n →
      (∀ J ∈ bondFormsSupportedNear (Ω.fineSitesOf K 0),
        (∀ j ≤ t, ∀ f ∈ bondsTouching (Ω.fineSitesOf K j),
          ComplexMatrix2.operatorNorm (J f) < n * (meshAtLevel L t j ^ 3)⁻¹) →
        GreenFormBounds Ω K U₀ (landauGreen Ω U₀ J) (N.B₀ * n)
          fun β₀ => N.B₀β β₀ * n) ∧
      ∀ B : (j : ℕ) → BondAtLevel L m K j → ComplexMatrix2, (∀ j, B j ∈ algebraBondForms L m K j) →
        (∀ j ≤ t, ∀ f ∈ Ω.shellBonds K j, ComplexMatrix2.operatorNorm (B j f) < n) →
        FirstOrderFormBounds Ω K U₀ (landauMinimizer Ω K U₀ B) (N.B₀ * n)
          fun β₀ => N.B₀β β₀ * n
def ImprovesFormBounds (L e r : ℕ) (N : GaugeFixingConstants) : Prop :=
  ∀ (m K t : ℕ) (Ω : NestedRegions L m t), 0 < m → IsDomainSequence e r K Ω →
    ShellCubesCoverPlaquettes Ω e K N.cubeConst → ∀ (α₀ α₁ α₂ : ℝ)
      (U₀ U₁ A : FineBond L m K → ComplexMatrix2) (B : (j : ℕ) → BondAtLevel L m K j → ComplexMatrix2),
      0 < α₀ → 0 < α₁ → 0 < α₂ → α₀ ≤ N.upper → α₁ ≤ N.upper → α₂ ≤ N.upper →
      2 * α₂ ^ 2 + 20 * 4 * α₀ * α₂ + 2 * (averageExpansionConstants L).remainderBound * α₂ ^ 2 ≤
        α₀ + α₁ →
      U₀ ∈ smallFieldConfigurations Ω K α₀ →
      RegularOnShellCubes Ω e K N.cubeConst α₀ U₀ →
      IsGaugeField compactGaugeGroup univ U₁ →
      fieldProduct U₁ U₀ ∈ smallFieldConfigurations Ω K α₀ →
      IsExpOfBondForm Ω K U₁ A →
      (∀ j ≤ t, ∀ f ∈ bondsTouching (Ω.fineSitesOf K j),
        ComplexMatrix2.operatorNorm (A f) < α₂ * (meshAtLevel L t j)⁻¹) →
      LandauGaugeCondition Ω K U₀ A → HasAveragesEqual Ω K U₀ A B →
      IsSmallOnShells Ω K α₁ B →
      LandauFormBounds Ω K U₀ A (N.B₁ L * (α₀ + α₁)) fun β₀ => N.B₂ L β₀ * (α₀ + α₁)
def LandauGaugeFixing (L e r : ℕ) (N : GaugeFixingConstants) : Prop :=
  ∀ (m K t : ℕ) (Ω : NestedRegions L m t), 0 < m → IsDomainSequence e r K Ω →
    ShellCubesCoverPlaquettes Ω e K N.cubeConst → ∀ (α₀ α₁ : ℝ) (U₀ V : FineBond L m K → ComplexMatrix2),
      0 < α₀ → 0 < α₁ → α₀ + α₁ ≤ N.c₁ →
      AxialGaugeData Ω e K N.cubeConst α₀ α₁ U₀ V →
      ∃! g : FineSite L m K → ComplexMatrix2, IsRegionGaugeTransformation Ω K g ∧
        HasTrivialAverages Ω K U₀ g ∧
        IsLandauGaugeImage Ω K α₁ (N.B₁ L * (α₀ + α₁)) (fun β₀ => N.B₂ L β₀ * (α₀ + α₁)) U₀ V
          (relativeGaugeTransform U₀ (fun x => (g x)⁻¹) V)
structure AreGaugeFixingConstants (L e r : ℕ) (N : GaugeFixingConstants) : Prop where
  cubeConst_ge : 10 ≤ N.cubeConst
  B₀_pos : 0 < N.B₀
  B₀β_pos : ∀ β₀, 0 ≤ β₀ → β₀ < 1 → 0 < N.B₀β β₀
  upper_pos : 0 < N.upper
  c₁_pos : 0 < N.c₁
  greenBounds : BoundsGreenOperators L e r N
  improvement : ImprovesFormBounds L e r N
  gaugeFixing : LandauGaugeFixing L e r N
structure AreUniqueGaugeFixingConstants (L e r : ℕ) (N : GaugeFixingConstants) : Prop
    extends AreGaugeFixingConstants L e r N where
  exponents_ge : 2 ≤ e + r
  below_threshold : Conventions.IsAdmissibleBlockingFactor L → ∃ c : ℝ, 0 < c ∧
    AxialTowerUniqueness.IsUniquenessThreshold L c ∧ N.c₁ ≤ c ∧ N.B₁ L * N.c₁ ≤ c
end YangMills.Construction.BackgroundField
