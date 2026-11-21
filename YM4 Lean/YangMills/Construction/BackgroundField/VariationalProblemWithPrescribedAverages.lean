import YangMills.Construction.BackgroundField.RegularConfigurations
import YangMills.Construction.Lattice.ClassesOfRegularConfigurations
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.Matrices
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.BackgroundField.PrescribedAverageProblem
variable {L m k : ℕ}
def fieldsOnRegion (K : ℕ) (S : NestedRegions L m k) : Set (FineBond L m K → ComplexMatrix2) :=
  {U | IsGaugeField compactGaugeGroup (bondsTouching (S.fineSitesOf K 0)) U ∧
    ∀ e, e ∉ bondsTouching (S.fineSitesOf K 0) → U e = 1}
def regularFields (K : ℕ) (S : NestedRegions L m k) (ε : ℝ) :
    Set (FineBond L m K → ComplexMatrix2) :=
  {U | U ∈ fieldsOnRegion K S ∧
    extendByOne (bondsInside (S.regionAt 0)) U ∈ transposeRegularSetConst K k S.regionAt ε}
def IsShellDatum (K : ℕ) (S : NestedRegions L m k)
    (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) : Prop :=
  ∀ j ≤ k, IsGaugeField compactGaugeGroup (S.shellBonds K j) (V j)
def fieldsWithAverages (K : ℕ) (S : NestedRegions L m k)
    (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) : Set (FineBond L m K → ComplexMatrix2) :=
  {U | U ∈ fieldsOnRegion K S ∧
    ∀ j ≤ k, ∀ e ∈ S.shellBonds K j, e.IsPositivelyOriented → iteratedAveragedField U j e = V j e}
def admissibleFields (K : ℕ) (S : NestedRegions L m k) (ε : ℝ)
    (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) : Set (FineBond L m K → ComplexMatrix2) :=
  regularFields K S ε ∩ fieldsWithAverages K S V
def regionActionFunctional (K : ℕ) (S : NestedRegions L m k)
    (U : FineBond L m K → ComplexMatrix2) : ℝ :=
  actionInside K (S.regionAt 0) U
def pinnedGaugeTransforms (K : ℕ) (S : NestedRegions L m k) :
    Set (FineSite L m K → ComplexMatrix2) :=
  {g | (∀ x, g x ∈ compactGaugeGroup) ∧ (∀ x, x ∉ S.fineSitesOf K 0 → g x = 1) ∧
    ∀ x : FineSite L m K, (x : FourTorus L m) ∈ S.shellPoints K → g x = 1}
def pinnedOrbit (K : ℕ) (S : NestedRegions L m k) (U : FineBond L m K → ComplexMatrix2) :
    Set (FineBond L m K → ComplexMatrix2) :=
  (fun g => gaugeTransform g U) '' pinnedGaugeTransforms K S
def IsOrbitWithin (K : ℕ) (S : NestedRegions L m k)
    (X O : Set (FineBond L m K → ComplexMatrix2)) : Prop :=
  (∃ U ∈ X, O = pinnedOrbit K S U) ∧ O ⊆ X
def IsCriticalPoint (K : ℕ) (S : NestedRegions L m k) (X : Set (FineBond L m K → ComplexMatrix2))
    (U : FineBond L m K → ComplexMatrix2) : Prop :=
  U ∈ X ∧ ∀ (δ : ℝ) (c : ℝ → FineBond L m K → ComplexMatrix2), 0 < δ →
    (∀ t ∈ Ioo (-δ) δ, c t ∈ X) →
    (∀ e p q, DifferentiableOn ℝ (fun t => c t e p q) (Ioo (-δ) δ)) → c 0 = U →
    deriv (fun t => regionActionFunctional K S (c t)) 0 = 0
def IsCriticalOrbitIn (K : ℕ) (S : NestedRegions L m k)
    (X O : Set (FineBond L m K → ComplexMatrix2)) : Prop :=
  IsOrbitWithin K S X O ∧ ∀ U ∈ O, IsCriticalPoint K S X U
def IsMinimizingOrbit (K : ℕ) (S : NestedRegions L m k)
    (X O : Set (FineBond L m K → ComplexMatrix2)) : Prop :=
  IsOrbitWithin K S X O ∧
    ∀ U ∈ O, ∀ W ∈ X, regionActionFunctional K S U ≤ regionActionFunctional K S W
open Classical in
def shellField (K : ℕ) (S : NestedRegions L m k)
    (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) :
    (j : ℕ) → BondAtLevel L m K j → ComplexMatrix2
  | 0 => V 0
  | j + 1 => fun e => if e ∈ S.shellBonds K (j + 1) then V (j + 1) e else averagedField (V j) e
def LiesInLowerShell (K : ℕ) (S : NestedRegions L m k) (j : ℕ)
    (e : BondAtLevel L m K j) : Prop :=
  e.source ∈ levelSitesOf j (S.fineSitesOf K (j - 1)) \ levelSitesOf j (S.fineSitesOf K j) ∧
    e.target ∈ levelSitesOf j (S.fineSitesOf K (j - 1)) \ levelSitesOf j (S.fineSitesOf K j)
def IsShellPlaquette (K : ℕ) (S : NestedRegions L m k) (j : ℕ)
    (p : PlaquetteAtLevel L m K j) : Prop :=
  (∃ e ∈ p.boundaryBonds, e ∈ S.shellBonds K j) ∧
    ∀ e ∈ p.boundaryBonds, e ∈ S.shellBonds K j ∨ LiesInLowerShell K S j e
def IsSmallCurvatureDatum (K : ℕ) (S : NestedRegions L m k) (ε₁ : ℝ)
    (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) : Prop :=
  ∀ j ≤ k, ∀ p : PlaquetteAtLevel L m K j, IsShellPlaquette K S j p →
    ComplexMatrix2.operatorNorm (plaquetteHolonomy (shellField K S V j) p - 1) < ε₁
def supCube (w : FourTorus L m) (h : ℝ) : Set (FourTorus L m) :=
  {x | TorusMetric.torusSupNorm (x - w) ≤ h}
def IsAdmissibleCube (K n r : ℕ) (S : NestedRegions L m k) (j M : ℕ)
    (Q : Set (FourTorus L m)) : Prop :=
  ∃ w : FourTorus L m, Q = supCube w ((M : ℝ) * meshSize L (levelDepth K j)) ∧
    IsUnionOfPartitionCubes (scaledCubeIndex K j n) Q ∧
    2 * ((M : ℝ) + 2 * ((L : ℝ) ^ r * (L : ℝ) ^ n)) * meshSize L (levelDepth K j) < torusSide L m ∧
    (sitesIn (supCube w (((M : ℝ) + 2 * ((L : ℝ) ^ r * (L : ℝ) ^ n)) *
        meshSize L (levelDepth K j))) : Set (FineSite L m K)) ⊆
      S.fineSitesOf K j \ S.fineSitesOf K (j + 2) ∧
    ¬ (sitesIn (supCube w (((M : ℝ) + 2 * ((L : ℝ) ^ r * (L : ℝ) ^ n)) *
        meshSize L (levelDepth K j))) : Set (FineSite L m K)) ⊆
      S.fineSitesOf K (j + 1) \ S.fineSitesOf K (j + 2)
section Free
variable {K : ℕ}
def freeDeriv (k : ℕ) (A : FineBond L m K → ComplexMatrix2) (μ ν : Fin 4) (x : FineSite L m K) :
    ComplexMatrix2 :=
  covDeriv (finestMeshInLevelUnits L k) (fun _ => 1) μ (bondFormComponent A ν) x
def freeCurlAdjoint (k : ℕ) (A : FineBond L m K → ComplexMatrix2) (x : FineSite L m K) (μ : Fin 4) :
    ComplexMatrix2 :=
  transposeDerivAt (finestMeshInLevelUnits L k) (fun _ => 1)
    (covariantPlaquetteDerivative k (fun _ => 1) A) x μ
def freeLaplacian (k : ℕ) (A : FineBond L m K → ComplexMatrix2) (ν : Fin 4) (x : FineSite L m K) :
    ComplexMatrix2 :=
  ∑ μ : Fin 4, (((finestMeshInLevelUnits L k ^ 2 : ℝ) : ℂ))⁻¹ •
    ((2 : ℂ) • bondFormComponent A ν x -
      bondFormComponent A ν (x + unitStep L m (levelDepth K 0) μ) -
      bondFormComponent A ν (x - unitStep L m (levelDepth K 0) μ))
def DerivReadsInside (Q : Set (FourTorus L m)) (x : FineSite L m K) (μ ν : Fin 4) : Prop :=
  Bond.forwardFrom x ν ∈ (bondsInside Q : Set (FineBond L m K)) ∧
    Bond.forwardFrom (x + unitStep L m (levelDepth K 0) μ) ν ∈ (bondsInside Q : Set (FineBond L m K))
def LaplacianReadsInside (Q : Set (FourTorus L m)) (x : FineSite L m K) (ν : Fin 4) : Prop :=
  Bond.forwardFrom x ν ∈ (bondsInside Q : Set (FineBond L m K)) ∧
    ∀ μ : Fin 4,
      Bond.forwardFrom (x + unitStep L m (levelDepth K 0) μ) ν ∈
        (bondsInside Q : Set (FineBond L m K)) ∧
      Bond.forwardFrom (x - unitStep L m (levelDepth K 0) μ) ν ∈
        (bondsInside Q : Set (FineBond L m K))
def freeGradHolderSeminorm (k : ℕ) (Q : Set (FourTorus L m)) (β : ℝ)
    (A : FineBond L m K → ComplexMatrix2) : ℝ≥0∞ :=
  ⨆ (μ : Fin 4) (ν : Fin 4) (x : FineSite L m K) (y : FineSite L m K)
    (_ : DerivReadsInside Q x μ ν ∧ DerivReadsInside Q y μ ν ∧ x ≠ y ∧
      scaledTorusDistance L K k (x : FourTorus L m) (y : FourTorus L m) ≤ 1),
    ENNReal.ofReal (ComplexMatrix2.operatorNorm (freeDeriv k A μ ν y - freeDeriv k A μ ν x) /
      scaledTorusDistance L K k (x : FourTorus L m) (y : FourTorus L m) ^ β)
end Free
def IsSmoothOnCube (E : ℝ → Prop) (B₃ : ℝ) (B₄ : ℝ → ℝ) (ε₁ : ℝ) (K k j M : ℕ)
    (Q : Set (FourTorus L m)) (U : FineBond L m K → ComplexMatrix2) : Prop :=
  ∃ (g : FineSite L m K → ComplexMatrix2) (A : FineBond L m K → ComplexMatrix2),
    (∀ x, g x ∈ compactGaugeGroup) ∧ A ∈ algebraBondForms L m K 0 ∧
    (∀ e ∈ (bondsInside Q : Set (FineBond L m K)),
      gaugeTransform (fun x => (g x)⁻¹) U e =
        expGaugeField (((finestMeshInLevelUnits L k : ℝ) : ℂ) • A) e ∧
      ComplexMatrix2.operatorNorm (A e) < B₃ * M * ε₁ * (meshAtLevel L k j)⁻¹) ∧
    (∀ (x : FineSite L m K) (μ ν : Fin 4), DerivReadsInside Q x μ ν →
      ComplexMatrix2.operatorNorm (freeDeriv k A μ ν x) < B₃ * M * ε₁ * (meshAtLevel L k j ^ 2)⁻¹) ∧
    (∀ β₀, E β₀ → ∀ β, 0 ≤ β → β ≤ β₀ →
      freeGradHolderSeminorm k Q β A <
        ENNReal.ofReal (B₄ β₀ * M * ε₁ * meshAtLevel L k j ^ (-2 - β))) ∧
    (∀ (x : FineSite L m K) (μ : Fin 4), HasCurrentAt K Q (Bond.forwardFrom x μ) →
      ComplexMatrix2.operatorNorm (freeCurlAdjoint k A x μ) <
        B₃ * M * ε₁ * (meshAtLevel L k j ^ 3)⁻¹) ∧
    ∀ (x : FineSite L m K) (ν : Fin 4), LaplacianReadsInside Q x ν →
      ComplexMatrix2.operatorNorm (freeLaplacian k A ν x) < B₃ * M * ε₁ * (meshAtLevel L k j ^ 3)⁻¹
def MinimizerTheoremHolds (E : ℝ → Prop) (L n r : ℕ) (a₀ a₁ B₃ : ℝ) (B₄ : ℝ → ℝ) : Prop :=
  ∀ (m K k : ℕ), 1 ≤ k → ∀ S : NestedRegions L m k, IsDomainSequence n r K S →
    ∀ (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) (ε₁ : ℝ), 0 < ε₁ → ε₁ ≤ a₁ →
      IsShellDatum K S V → IsSmallCurvatureDatum K S ε₁ V →
      ∃ O : Set (FineBond L m K → ComplexMatrix2),
        IsMinimizingOrbit K S (admissibleFields K S (B₃ * ε₁) V) O ∧
        (∀ ε₀, B₃ * ε₁ ≤ ε₀ → ε₀ ≤ a₀ →
          IsCriticalOrbitIn K S (admissibleFields K S ε₀ V) O ∧
          ∀ O', IsCriticalOrbitIn K S (admissibleFields K S ε₀ V) O' → O' = O) ∧
        ∀ U ∈ O, ∀ j ≤ k, ∀ N : ℕ, 0 < N →
          (N : ℝ) * ((L : ℝ) ^ r * (L : ℝ) ^ n) ≤ (L : ℝ) ^ r * (L : ℝ) ^ n * (a₁ / ε₁) →
          ∀ Q : Set (FourTorus L m), IsAdmissibleCube K n r S j (N * (L ^ r * L ^ n)) Q →
            IsSmoothOnCube E B₃ B₄ ε₁ K k j (N * (L ^ r * L ^ n)) Q U
structure MinimizerConstants where
  a₀ : ℝ
  a₁ : ℝ
  B₄ : ℝ → ℝ
instance : Nonempty MinimizerConstants := ⟨⟨0, 0, fun _ => 0⟩⟩
def AreMinimizerConstants (E : ℝ → Prop) (L n r : ℕ) (B₃ : ℝ) (c : MinimizerConstants) : Prop :=
  0 < c.a₀ ∧ 0 < c.a₁ ∧ B₃ * c.a₁ ≤ c.a₀ ∧ (∀ β₀, 0 < c.B₄ β₀) ∧
    MinimizerTheoremHolds E L n r c.a₀ c.a₁ B₃ c.B₄
def IsRegularityConstant (E : ℝ → Prop) (L : ℕ) (B₃ f g : ℝ) : Prop :=
  0 < B₃ ∧ ∀ n r : ℕ, 1 ≤ r → f ≤ (L : ℝ) ^ n → g ≤ (L : ℝ) ^ r * (L : ℝ) ^ n →
    ∃ c, AreMinimizerConstants E L n r B₃ c
end YangMills.Construction.BackgroundField.PrescribedAverageProblem
