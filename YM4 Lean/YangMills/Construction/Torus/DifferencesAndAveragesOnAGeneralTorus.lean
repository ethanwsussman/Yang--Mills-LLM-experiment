import YangMills.Construction.Torus.FormsAveragesAndOperatorsOnAGeneralTorus
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.GeneralTorus.DiffAndMeans
def SumSquaresDiffIdentity (D : ScaleData) : Prop :=
  ∀ A : D.BondField,
    D.plaquetteL2Norm (D.plaquetteCurl A) ^ 2 + D.siteL2Norm (D.gradAdjoint A) ^ 2 =
      ∑ μ : Fin 4, ∑ ν : Fin 4, D.siteL2Norm (D.forwardDiff ν (D.formComponent μ A)) ^ 2
def TentMultiplicityFormula : Prop :=
  ∀ N : ℕ, Odd N →
    (∀ s : ℤ, |(s : ℝ)| ≤ halfSpan N →
      (tentMultiplicity N s : ℝ) = (s : ℝ) + ((N : ℝ) + 1) / 2 ∧
        (tentMultiplicity N (s + (N : ℤ)) : ℝ) = ((N : ℝ) - 1) / 2 - (s : ℝ)) ∧
    (∀ s : ℤ, (s : ℝ) < -halfSpan N ∨ 3 * halfSpan N + 1 < (s : ℝ) →
      tentMultiplicity N s = 0) ∧
    ∀ s : ℤ, tentMultiplicity N s ≤ N
def windowSite {D : ScaleData} {n : ℕ} (c : D.PosBond n) (k : Fin 4 → ℤ) : D.Space :=
  (c.1.src : D.Space) + torusProj D.torusSide fun ν => D.levelSpacing 0 * (k ν : ℝ)
def BondMeanSitesWeights (D : ScaleData) : Prop :=
  ∀ n, n ≤ D.lastLevel → ∀ c : D.PosBond n,
    (∀ k k' : Fin 4 → ℤ, MemBondWindow (D.blockSize n) (ScaleData.posBondDir c) k →
      MemBondWindow (D.blockSize n) (ScaleData.posBondDir c) k' →
        windowSite c k = windowSite c k' → k = k') ∧
    (∀ x : D.Space, (x ∈ D.baseLattice ∧ x ∈ ScaleData.bondSupport c) ↔
      ∃ k : Fin 4 → ℤ, MemBondWindow (D.blockSize n) (ScaleData.posBondDir c) k ∧
        x = windowSite c k) ∧
    (∀ A : D.BondField, D.blockBondMean n A c =
      ∑ᶠ x : D.BaseSite, D.meanWeight c (x : D.Space) *
        D.formComponent (ScaleData.posBondDir c) A x) ∧
    (∀ x : D.BaseSite, 0 ≤ D.meanWeight c (x : D.Space) ∧
      D.meanWeight c (x : D.Space) ≤ ((D.blockSize n : ℝ) ^ 4)⁻¹) ∧
    (∑ᶠ x : D.BaseSite, D.meanWeight c (x : D.Space)) = 1 ∧
    ∀ x : D.BaseSite, D.meanWeight c (x : D.Space) ≠ 0 →
      (x : D.Space) ∈ ScaleData.bondSupport c ∧
        ((x + unitStep D.torusSide (D.levelSpacing 0) (ScaleData.posBondDir c) : D.BaseSite) :
          D.Space) ∈ ScaleData.bondSupport c
def MeanCommutesGrad (D : ScaleData) : Prop :=
  ∀ n, n ≤ D.lastLevel → ∀ (f : D.SiteField) (c : D.PosBond n),
    D.blockBondMean n (D.grad f) c =
      (D.levelSpacing n)⁻¹ * (D.blockSiteMean n f (c.1.tgt : D.Space) -
        D.blockSiteMean n f (c.1.src : D.Space))
def MeanComposition (D : ScaleData) : Prop :=
  ∀ n, n < D.lastLevel →
    (∀ (f : D.SiteField) (y : D.SiteAt (n + 1)),
      D.blockSiteMean (n + 1) f (y : D.Space) =
        ((D.L : ℝ) ^ 4)⁻¹ * ∑ᶠ z ∈ D.coarseBlock n (y : D.Space), D.blockSiteMean n f z) ∧
    ∀ c' : D.PosBond (n + 1),
      (∀ A : D.BondField, D.blockBondMean (n + 1) A c' =
        ∑ᶠ c'' : D.PosBond n, D.oneStepWeight c' c'' * D.blockBondMean n A c'') ∧
      (∀ c'' : D.PosBond n,
        0 ≤ D.oneStepWeight c' c'' ∧ D.oneStepWeight c' c'' ≤ ((D.L : ℝ) ^ 4)⁻¹) ∧
      (∑ᶠ c'' : D.PosBond n, D.oneStepWeight c' c'') = 1 ∧
      ∀ c'' : D.PosBond n, D.oneStepWeight c' c'' ≠ 0 →
        ScaleData.posBondDir c'' = ScaleData.posBondDir c' ∧
        (c''.1.src : D.Space) ∈
          D.coarseBlock n (c'.1.src : D.Space) ∪ D.coarseBlock n (c'.1.tgt : D.Space) ∧
        (c''.1.tgt : D.Space) ∈
          D.coarseBlock n (c'.1.src : D.Space) ∪ D.coarseBlock n (c'.1.tgt : D.Space)
def DiffAndMeanFacts : Prop :=
  ∀ W : GaugeSetting, SumSquaresDiffIdentity W.data ∧ TentMultiplicityFormula ∧
    BondMeanSitesWeights W.data ∧ MeanCommutesGrad W.data ∧
    MeanComposition W.data
end YangMills.Construction.GeneralTorus.DiffAndMeans
