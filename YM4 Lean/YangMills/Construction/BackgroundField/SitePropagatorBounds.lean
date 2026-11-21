import YangMills.Construction.BackgroundField.NormsAndCubesOfADecreasingSequence
import YangMills.Construction.BackgroundField.RegularConfigurations
import YangMills.Construction.BackgroundField.RegularityOnCubes
import YangMills.Construction.BackgroundField.WeightedDistanceOfADecreasingSequence
import Mathlib
open Set Filter
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.BackgroundField
section Operators
variable {L m K : ℕ}
def covariantPartial (t : ℕ) (U : FineBond L m K → Matrices.ComplexMatrix2) (μ : Fin 4)
    (f : FineSite L m K → Matrices.ComplexMatrix2) : FineSite L m K → Matrices.ComplexMatrix2 :=
  PeriodicLattice.bondFormComponent (covariantSiteDerivative t U f) μ
def covariantPartialAdjoint (t : ℕ) (U : FineBond L m K → Matrices.ComplexMatrix2) (μ : Fin 4) :
    (FineSite L m K → Matrices.ComplexMatrix2) → FineSite L m K → Matrices.ComplexMatrix2 :=
  adjointBetween (algebraFunctionsSupportedIn univ) (algebraFunctionsSupportedIn univ)
    (siteL2Inner t) (siteL2Inner t) (covariantPartial t U μ)
def covariantGradientNorm (t : ℕ) (U : FineBond L m K → Matrices.ComplexMatrix2)
    (f : FineSite L m K → Matrices.ComplexMatrix2) (x : FineSite L m K) : ℝ≥0∞ :=
  ⨆ μ : Fin 4, ENNReal.ofReal (halfTraceNorm (covariantPartial t U μ f x))
def scalarMulSites (h : FineSite L m K → ℂ) (f : FineSite L m K → Matrices.ComplexMatrix2) :
    FineSite L m K → Matrices.ComplexMatrix2 := fun x => h x • f x
def scalarMulBonds (h : FineSite L m K → ℂ) (A : FineBond L m K → Matrices.ComplexMatrix2) :
    FineBond L m K → Matrices.ComplexMatrix2 := antisymmetricExtension fun b => h b.source • A b
def latticeSiteL2Norm (t : ℕ) (f : FineSite L m K → Matrices.ComplexMatrix2) : ℝ :=
  Real.sqrt (∑ᶠ x, PeriodicLattice.finestMeshInLevelUnits L t ^ 4 * halfTraceNormSq (f x))
def latticeBondL2Norm (t : ℕ) (A : FineBond L m K → Matrices.ComplexMatrix2) : ℝ :=
  Real.sqrt (∑ᶠ b : {b : FineBond L m K // b.IsPositivelyOriented},
    PeriodicLattice.finestMeshInLevelUnits L t ^ 4 * halfTraceNormSq (A b))
def scalarSupNorm (h : FineSite L m K → ℂ) : ℝ≥0∞ := ⨆ x, ENNReal.ofReal ‖h x‖
def gaugeActSites (v f : FineSite L m K → Matrices.ComplexMatrix2) :
    FineSite L m K → Matrices.ComplexMatrix2 :=
  fun x => Matrices.ComplexMatrix2.conjugateBy (v x) (f x)
end Operators
structure SiteGreenConstants where
  M₁ : ℝ
  r₀ : ℕ
  δ₀ : ℝ
  B₀ : ℝ
  Bβ : ℝ → ℝ
  Bε : ℝ → ℝ
  Bεβ : ℝ → ℝ → ℝ
  a₀ : ℝ → ℝ
instance : Nonempty SiteGreenConstants :=
  ⟨⟨0, 0, 0, 0, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ => 0⟩⟩
namespace SiteGreenConstants
variable {L m : ℕ} (C : SiteGreenConstants) (S : SeparatedSequences.ScaleData)
  (𝔰 : NestedRegions L m S.top) (U : FineBond L m S.levels → Matrices.ComplexMatrix2)
abbrev greenAtUnit : (FineSite L m S.levels → Matrices.ComplexMatrix2) →
    FineSite L m S.levels → Matrices.ComplexMatrix2 := siteGreen 𝔰 1 U
def greenAdjointDerivative (A : FineBond L m S.levels → Matrices.ComplexMatrix2) :
    FineSite L m S.levels → Matrices.ComplexMatrix2 :=
  greenAtUnit S 𝔰 U (restrictSites (𝔰.fineSitesOf S.levels 0)
    (covariantSiteDerivativeAdjoint S.top U A))
def decayFactor (y y' : 𝔰.ShellSite S.levels) : ℝ :=
  Real.exp (-C.δ₀ * 𝔰.scaleWeightedDistance y y')
def PointwiseEstimates : Prop :=
  ∀ (y y' : 𝔰.ShellSite S.levels), ∀ x ∈ 𝔰.shellCube y,
    (∀ f ∈ algebraFunctionsSupportedIn (𝔰.shellCube y'),
      ENNReal.ofReal (halfTraceNorm (greenAtUnit S 𝔰 U f x)) ≤
          ENNReal.ofReal (C.B₀ * 𝔰.shellMesh y ^ 2 * C.decayFactor S 𝔰 y y') * siteSupNorm f ∧
        covariantGradientNorm S.top U (greenAtUnit S 𝔰 U f) x ≤
          ENNReal.ofReal (C.B₀ * 𝔰.shellMesh y * C.decayFactor S 𝔰 y y') * siteSupNorm f ∧
        ENNReal.ofReal (halfTraceNorm (covariantSiteLaplacian S.top U (greenAtUnit S 𝔰 U f) x)) ≤
          ENNReal.ofReal (C.B₀ * C.decayFactor S 𝔰 y y') * siteSupNorm f) ∧
    ∀ A ∈ bondFormsSupportedNear (𝔰.shellCube y'),
      ENNReal.ofReal (halfTraceNorm (greenAdjointDerivative S 𝔰 U A x)) ≤
        ENNReal.ofReal (C.B₀ * 𝔰.shellMesh y * C.decayFactor S 𝔰 y y') * bondSupNorm A
def HolderEstimates : Prop :=
  ∀ path : FineSite L m S.levels → FineSite L m S.levels → List (FineBond L m S.levels),
    SeparatedSequences.IsGeodesicChoice S path →
  ∀ (y y' : 𝔰.ShellSite S.levels) (β₀ β : ℝ), 0 ≤ β → β ≤ β₀ → β₀ < 1 →
  ∀ ζ : PeriodicLattice.FourTorus L m → ℂ, 𝔰.IsSmoothSupportedInDoubledCube y ζ →
    (∀ f ∈ algebraFunctionsSupportedIn (𝔰.shellCube y'),
      bondHolderNorm S 1 β U path (scalarMulBonds (fun x => ζ (x : PeriodicLattice.FourTorus L m))
          (covariantSiteDerivative S.top U (greenAtUnit S 𝔰 U f))) ≤
        ENNReal.ofReal (C.Bβ β₀ * 𝔰.shellMesh y ^ (1 - β) * C.decayFactor S 𝔰 y y') *
          (complexHolderNorm S (𝔰.shellMesh y) β ζ + complexSupNorm S.levels ζ) * siteSupNorm f) ∧
    ∀ A ∈ bondFormsSupportedNear (𝔰.shellCube y'),
      siteHolderNorm S 1 β U path (scalarMulSites (fun x => ζ (x : PeriodicLattice.FourTorus L m))
          (greenAdjointDerivative S 𝔰 U A)) ≤
        ENNReal.ofReal (C.Bβ β₀ * 𝔰.shellMesh y ^ (1 - β) * C.decayFactor S 𝔰 y y') *
          (complexHolderNorm S (𝔰.shellMesh y) β ζ + complexSupNorm S.levels ζ) * bondSupNorm A
def SecondDerivativeEstimates : Prop :=
  ∀ path : FineSite L m S.levels → FineSite L m S.levels → List (FineBond L m S.levels),
    SeparatedSequences.IsGeodesicChoice S path →
  ∀ (y y' : 𝔰.ShellSite S.levels) (ε : ℝ), 0 < ε → ε ≤ 1 →
  ∀ A ∈ bondFormsSupportedNear
      (PeriodicLattice.sitesIn (𝔰.doubledCube y') : Set (FineSite L m S.levels)),
    (∀ x ∈ 𝔰.shellCube y,
      covariantGradientNorm S.top U (greenAdjointDerivative S 𝔰 U A) x ≤
        ENNReal.ofReal (C.Bε ε * C.decayFactor S 𝔰 y y') *
          (bondHolderNorm S (𝔰.shellMesh y') ε U path A + bondSupNorm A)) ∧
    ∀ β₀ β : ℝ, 0 ≤ β → β ≤ β₀ → β₀ < 1 →
    ∀ ζ : PeriodicLattice.FourTorus L m → ℂ, 𝔰.IsSmoothSupportedInDoubledCube y ζ →
      bondHolderNorm S 1 β U path (scalarMulBonds (fun x => ζ (x : PeriodicLattice.FourTorus L m))
          (covariantSiteDerivative S.top U (greenAdjointDerivative S 𝔰 U A))) ≤
        ENNReal.ofReal (C.Bεβ ε β₀ * 𝔰.shellMesh y ^ (-β) * C.decayFactor S 𝔰 y y') *
          (complexHolderNorm S (𝔰.shellMesh y) β ζ + complexSupNorm S.levels ζ) *
          (bondHolderNorm S (𝔰.shellMesh y') (β + ε) U path A + bondSupNorm A)
def L2Estimates : Prop :=
  ∀ (y y' : 𝔰.ShellSite S.levels) (h : FineSite L m S.levels → ℂ),
    (∀ x, x ∉ 𝔰.shellCube y → h x = 0) →
    (∀ f ∈ algebraFunctionsSupportedIn (𝔰.shellCube y'),
      ENNReal.ofReal (latticeSiteL2Norm S.top (scalarMulSites h (greenAtUnit S 𝔰 U f))) ≤
          ENNReal.ofReal (C.B₀ * 𝔰.shellMesh y ^ 2 * C.decayFactor S 𝔰 y y' *
            latticeSiteL2Norm S.top f) * scalarSupNorm h ∧
        ENNReal.ofReal (latticeBondL2Norm S.top
            (scalarMulBonds h (covariantSiteDerivative S.top U (greenAtUnit S 𝔰 U f)))) ≤
          ENNReal.ofReal (C.B₀ * 𝔰.shellMesh y * C.decayFactor S 𝔰 y y' *
            latticeSiteL2Norm S.top f) * scalarSupNorm h ∧
        (∀ μ ν : Fin 4,
          ENNReal.ofReal (latticeSiteL2Norm S.top (scalarMulSites h (covariantPartial S.top U μ
              (covariantPartial S.top U ν (greenAtUnit S 𝔰 U f))))) ≤
            ENNReal.ofReal (C.B₀ * C.decayFactor S 𝔰 y y' * latticeSiteL2Norm S.top f) *
              scalarSupNorm h) ∧
        ∀ μ ν : Fin 4,
          ENNReal.ofReal (latticeSiteL2Norm S.top (scalarMulSites h (greenAtUnit S 𝔰 U
              (restrictSites (𝔰.fineSitesOf S.levels 0) (covariantPartialAdjoint S.top U μ
                (covariantPartialAdjoint S.top U ν f)))))) ≤
            ENNReal.ofReal (C.B₀ * C.decayFactor S 𝔰 y y' * latticeSiteL2Norm S.top f) *
              scalarSupNorm h) ∧
    ∀ A ∈ bondFormsSupportedNear (𝔰.shellCube y'),
      ENNReal.ofReal (latticeSiteL2Norm S.top (scalarMulSites h (greenAdjointDerivative S 𝔰 U A))) ≤
          ENNReal.ofReal (C.B₀ * 𝔰.shellMesh y * C.decayFactor S 𝔰 y y' *
            latticeBondL2Norm S.top A) * scalarSupNorm h ∧
        ENNReal.ofReal (latticeBondL2Norm S.top (scalarMulBonds h
            (covariantSiteDerivative S.top U (greenAdjointDerivative S 𝔰 U A)))) ≤
          ENNReal.ofReal (C.B₀ * C.decayFactor S 𝔰 y y' * latticeBondL2Norm S.top A) *
            scalarSupNorm h
def WeightedEstimates : Prop :=
  ∀ γ ∈ Icc (-4 : ℝ) 4,
    (∀ f ∈ regionL2 𝔰 S.levels,
      𝔰.siteWeightedNorm (2 + γ) (greenAtUnit S 𝔰 U f) ≤
          ENNReal.ofReal C.B₀ * 𝔰.siteWeightedNorm γ f ∧
        𝔰.bondWeightedNorm (1 + γ) (covariantSiteDerivative S.top U (greenAtUnit S 𝔰 U f)) ≤
          ENNReal.ofReal C.B₀ * 𝔰.siteWeightedNorm γ f ∧
        𝔰.bondWeightedNorm γ (covariantSiteDerivative S.top U (greenAtUnit S 𝔰 U f)) ≤
          ENNReal.ofReal C.B₀ * 𝔰.siteWeightedNorm γ f) ∧
    ∀ A ∈ bondFormsSupportedNear (𝔰.fineSitesOf S.levels 0),
      𝔰.siteWeightedNorm (1 + γ) (greenAdjointDerivative S 𝔰 U A) ≤
        ENNReal.ofReal C.B₀ * 𝔰.bondWeightedNorm γ A
def GaugeCovariant : Prop :=
  ∀ v : FineSite L m S.levels → Matrices.ComplexMatrix2,
    (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) → ∀ f ∈ regionL2 𝔰 S.levels,
    greenAtUnit S 𝔰 (PeriodicLattice.gaugeTransform v U) (gaugeActSites v f) =
      gaugeActSites v (greenAtUnit S 𝔰 U f)
structure Hold : Prop where
  exists_inverse : ∃ T, IsInverseWithin (regionL2 𝔰 S.levels) (regionSiteOperator 𝔰 1 U) T
  pointwise : C.PointwiseEstimates S 𝔰 U
  holder : C.HolderEstimates S 𝔰 U
  secondDerivative : C.SecondDerivativeEstimates S 𝔰 U
  l2 : C.L2Estimates S 𝔰 U
  weighted : C.WeightedEstimates S 𝔰 U
  gauge : GaugeCovariant S 𝔰 U
end SiteGreenConstants
def ShellCubesCoverPlaquettes {L m t : ℕ} (𝔰 : NestedRegions L m t) (e K : ℕ) (c : ℝ) : Prop :=
  ∀ p ∈ (PeriodicLattice.plaquettesInside (𝔰.regionAt 0) : Set (FinePlaquette L m K)),
    ∃ j ≤ t, ∃ Q, IsShellCube 𝔰 e K c j Q ∧
      p ∈ (PeriodicLattice.plaquettesInside Q : Set (FinePlaquette L m K))
structure AreSiteGreenConstants (L : ℕ) (C : SiteGreenConstants) : Prop where
  M₁_pos : 0 < C.M₁
  δ₀_pos : 0 < C.δ₀
  B₀_pos : 0 < C.B₀
  Bβ_pos : ∀ β ∈ Ico (0 : ℝ) 1, 0 < C.Bβ β
  Bε_pos : ∀ ε ∈ Ioc (0 : ℝ) 1, 0 < C.Bε ε
  Bεβ_pos : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ β ∈ Ico (0 : ℝ) 1, 0 < C.Bεβ ε β
  Bβ_tendsto : Tendsto C.Bβ (𝓝[<] 1) atTop
  Bε_tendsto : Tendsto C.Bε (𝓝[>] 0) atTop
  Bεβ_tendsto_ε : ∀ β ∈ Ico (0 : ℝ) 1, Tendsto (fun ε => C.Bεβ ε β) (𝓝[>] 0) atTop
  Bεβ_tendsto_β : ∀ ε ∈ Ioc (0 : ℝ) 1, Tendsto (C.Bεβ ε) (𝓝[<] 1) atTop
  a₀_pos : ∀ c : ℝ, 10 ≤ c → 0 < C.a₀ c
  bounds : ∀ (m : ℕ) (S : SeparatedSequences.ScaleData), S.unitLevel = S.top →
    C.M₁ ≤ (L : ℝ) ^ S.blockExp →
    ∀ (r : ℕ), C.r₀ ≤ r → ∀ 𝔰 : NestedRegions L m S.top,
      IsDomainSequence S.blockExp r S.levels 𝔰 →
    ∀ c α₀ : ℝ, 10 ≤ c → 0 < α₀ → (L : ℝ) ^ S.blockExp * α₀ ≤ C.a₀ c →
    ShellCubesCoverPlaquettes 𝔰 S.blockExp S.levels c →
    ∀ U : FineBond L m S.levels → Matrices.ComplexMatrix2,
      PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ U →
      RegularOnShellCubes 𝔰 S.blockExp S.levels c α₀ U → C.Hold S 𝔰 U
end YangMills.Construction.BackgroundField
