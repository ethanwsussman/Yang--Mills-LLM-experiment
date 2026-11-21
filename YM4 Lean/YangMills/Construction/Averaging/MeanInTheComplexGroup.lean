import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.InvertibleContourVariables
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Averaging
open Matrices PeriodicLattice
def smallComplexFamilies (n : ℕ) : Set (Fin n → ComplexMatrix2) :=
  {V | (∀ i, V i ∈ complexGaugeGroup) ∧ ComplexMatrix2.familyDiameter V < centreOfMassDiameter}
def IsNearComplexLogMean {n : ℕ} (V : Fin n → ComplexMatrix2) (W : ComplexMatrix2) : Prop :=
  ComplexMatrix2.IsLogMean complexGaugeGroup V W ∧
    ∃ i, ComplexMatrix2.operatorNorm (V i * W⁻¹ - 1) ≤ complexMeanTolerance
structure ComplexLogMeanProperties (n : ℕ) : Prop where
  existsUnique : ∀ V ∈ smallComplexFamilies n, ∃! W, IsNearComplexLogMean V W
  spread : ∀ V ∈ smallComplexFamilies n, ∀ i,
    ComplexMatrix2.operatorNorm (V i * (complexLogMean V)⁻¹ - 1) ≤
      4 * ComplexMatrix2.familyDiameter V
  numbering : ∀ V ∈ smallComplexFamilies n, ∀ π : Equiv.Perm (Fin n),
    complexLogMean (V ∘ π) = complexLogMean V
  constantFamily : ∀ W ∈ complexGaugeGroup, complexLogMean (fun _ : Fin n => W) = W
  isOpen : ComplexMatrix2.IsRelativelyOpen
    (ComplexMatrix2.complexifiedProduct fun _ : Fin n => ComplexMatrix2.FactorKind.group)
    (smallComplexFamilies n)
  holomorphic : ∀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
    Coordinates.ComplexCoordinates.IsHolomorphicOnSL2Power b (smallComplexFamilies n)
      complexLogMean
  holomorphicInEntries : ComplexMatrix2.IsHolomorphicBetween
    (fun _ : Fin n => ComplexMatrix2.FactorKind.group)
    (fun _ : Unit => ComplexMatrix2.FactorKind.group) (smallComplexFamilies n)
    fun V _ => complexLogMean V
  memRealGroup : ∀ V : Fin n → ComplexMatrix2, (∀ i, V i ∈ compactGaugeGroup) →
    ComplexMatrix2.familyDiameter V < centreOfMassDiameter →
      complexLogMean V ∈ compactGaugeGroup
  onlyMean : ∀ V : Fin n → ComplexMatrix2, (∀ i, V i ∈ compactGaugeGroup) →
    ComplexMatrix2.familyDiameter V < centreOfMassDiameter →
      ∀ W, ComplexMatrix2.IsLogMean compactGaugeGroup V W ↔ W = complexLogMean V
  exactlyOneMean : ∀ V : Fin n → ComplexMatrix2, (∀ i, V i ∈ compactGaugeGroup) →
    ComplexMatrix2.familyDiameter V < centreOfMassDiameter →
      ComplexMatrix2.HasUniqueLogMean compactGaugeGroup V
  meanEqualsAverage : ∀ V : Fin n → ComplexMatrix2, (∀ i, V i ∈ compactGaugeGroup) →
    ComplexMatrix2.familyDiameter V < centreOfMassDiameter →
      ComplexMatrix2.logMean compactGaugeGroup V = complexLogMean V
  covariant : ∀ V ∈ smallComplexFamilies n, ∀ W ∈ compactGaugeGroup, ∀ W' ∈ compactGaugeGroup,
    complexLogMean (fun i => W * V i * W') = W * complexLogMean V * W'
def ContourHolonomiesAreSmall (L m K : ℕ) (ω₁ : ℝ) : Prop :=
  ∀ ω ∈ Ioc (0 : ℝ) ω₁, ∀ k, k < K → ∀ c : BondAtLevel L m K (k + 1),
    ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
      ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
        ∀ x ∈ sitesInBlock (levelDepth K k) y,
          ComplexMatrix2.familyDiameter (contourHolonomies U y x) < centreOfMassDiameter
def ComplexLogMeanOfSmallFamilies : Prop :=
  0 < 4 * centreOfMassDiameter ∧ 4 * centreOfMassDiameter ≤ complexMeanTolerance ∧
  complexMeanTolerance < 1 ∧
  (∀ n : ℕ, 1 ≤ n → ComplexLogMeanProperties n) ∧
  ∀ s : Conventions.StandingParameters, averagingRadiusCap s.L ∈ Ioc (0 : ℝ) 1 ∧
    ContourHolonomiesAreSmall s.L s.m s.K (averagingRadiusCap s.L)
end YangMills.Construction.Averaging
end
