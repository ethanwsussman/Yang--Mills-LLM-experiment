import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BlocksAndCorridors
import YangMills.Construction.Lattice.SmallFieldStepSpaces
import Mathlib
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
def LieSquareExpFormula : Prop :=
  ∀ A ∈ ComplexMatrix2.hermitianTraceless,
    A ^ 2 = ((ComplexMatrix2.operatorNorm A : ℂ) ^ 2) • (1 : ComplexMatrix2) ∧
    (ComplexMatrix2.operatorNorm A : ℂ) ^ 2 = ComplexMatrix2.halfTrace (A ^ 2) ∧
    ComplexMatrix2.halfTrace (A ^ 2) = halfTracePairing A A ∧
    spectrum ℂ A = {(ComplexMatrix2.operatorNorm A : ℂ), -(ComplexMatrix2.operatorNorm A : ℂ)} ∧
    ComplexMatrix2.matExp (Complex.I • A) =
      (Real.cos (ComplexMatrix2.operatorNorm A) : ℂ) • (1 : ComplexMatrix2) +
        (Complex.I * (Real.sinc (ComplexMatrix2.operatorNorm A) : ℂ)) • A ∧
    ComplexMatrix2.halfTrace (ComplexMatrix2.matExp (Complex.I • A)) =
      (Real.cos (ComplexMatrix2.operatorNorm A) : ℂ) ∧
    ComplexMatrix2.matExp (Complex.I • A) ∈ ComplexMatrix2.specialUnitary
def IsPosDefComplexPairing {V : Type*} [AddCommGroup V] [Module ℝ V] (p : V → V → ℂ) : Prop :=
  ∃ B : LinearMap.BilinForm ℝ V, (∀ v w, B v w = B w v) ∧ (∀ v w, p v w = (B v w : ℂ)) ∧
    ∀ v, v ≠ 0 → 0 < B v v
def StepSpacesPosDefFinDim (L m K k : ℕ) : Prop :=
  IsPosDefComplexPairing (bareBondFormSpaceInner (L := L) (m := m) (K := K) k) ∧
  IsPosDefComplexPairing (bareSiteFieldSpaceInner (L := L) (m := m) (K := K) k) ∧
  IsPosDefComplexPairing (lieBondSpaceInner (L := L) (m := m) (K := K) (k := k)) ∧
  FiniteDimensional ℝ (bareBondFormSpace L m K) ∧
  FiniteDimensional ℝ (bareSiteFieldSpace L m K) ∧
  FiniteDimensional ℝ (lieBondSpaceAtLevel L m K k) ∧
  FiniteDimensional ℝ (siteFieldSpaceAtLevel L m K k) ∧
  FiniteDimensional ℝ (lieBondSpaceAtNextLevel L m K k)
def ExpInjOnBallPi : Prop :=
  ∀ A ∈ ComplexMatrix2.hermitianTraceless, ∀ A' ∈ ComplexMatrix2.hermitianTraceless,
    ComplexMatrix2.operatorNorm A < Real.pi → ComplexMatrix2.operatorNorm A' < Real.pi →
    ComplexMatrix2.matExp (Complex.I • A) = ComplexMatrix2.matExp (Complex.I • A') → A = A'
def LogSeriesNearOne : Prop :=
  AnalyticOnNhd ℂ ComplexMatrix2.logSeries ComplexMatrix2.logBall ∧
  ComplexMatrix2.logSeries 1 = 0 ∧
  HasFDerivAt ComplexMatrix2.logSeries (ContinuousLinearMap.id ℂ ComplexMatrix2) 1 ∧
  ∀ X ∈ ComplexMatrix2.logBall, ComplexMatrix2.matExp (ComplexMatrix2.logSeries X) = X
def LogSeriesOnSpecialUnitary : Prop :=
  (∀ g ∈ ComplexMatrix2.specialUnitary, ComplexMatrix2.operatorNorm (g - 1) < 1 →
    Complex.I⁻¹ • ComplexMatrix2.logSeries g ∈ ComplexMatrix2.hermitianTraceless ∧
    ComplexMatrix2.operatorNorm (Complex.I⁻¹ • ComplexMatrix2.logSeries g) < Real.pi / 3 ∧
    g ∈ ComplexMatrix2.unitaryLogDomain ∧
    ComplexMatrix2.logSeries g = ComplexMatrix2.unitaryLog g) ∧
  ∀ A ∈ ComplexMatrix2.hermitianTraceless, ComplexMatrix2.operatorNorm A < Real.pi / 3 →
    ComplexMatrix2.operatorNorm (ComplexMatrix2.matExp (Complex.I • A) - 1) < 1 ∧
    Complex.I⁻¹ • ComplexMatrix2.logSeries (ComplexMatrix2.matExp (Complex.I • A)) = A
def ConjugateBySpecialUnitary : Prop :=
  ∀ g ∈ ComplexMatrix2.specialUnitary,
    (∀ X : ComplexMatrix2,
      g * ComplexMatrix2.matExp X * g⁻¹ = ComplexMatrix2.matExp (ComplexMatrix2.conjugateBy g X)) ∧
    (∀ X : ComplexMatrix2,
      ComplexMatrix2.operatorNorm (ComplexMatrix2.conjugateBy g X) = ComplexMatrix2.operatorNorm X) ∧
    ComplexMatrix2.conjugateBy g '' (ComplexMatrix2.hermitianTraceless : Set ComplexMatrix2) =
      (ComplexMatrix2.hermitianTraceless : Set ComplexMatrix2) ∧
    ∀ X X' : ComplexMatrix2,
      ComplexMatrix2.fullTrace (ComplexMatrix2.conjugateBy g X * ComplexMatrix2.conjugateBy g X') =
        ComplexMatrix2.fullTrace (X * X')
def IsPivotCharacterized {L m K n : ℕ} (e : BondAtLevel L m K (n + 1)) : Prop :=
  (∀ b : BondAtLevel L m K n,
    (b ∈ axialPath (e.source.toSublattice (levelDepth K n)) (e.target.toSublattice (levelDepth K n)) ∧
      (b.source : FourTorus L m) ∈ unitBlock e.source ∧ (b.target : FourTorus L m) ∈ unitBlock e.target) ↔
      b = pivot e) ∧
  (pivot e : BondAtLevel L m K n).IsPositivelyOriented
def BlockPartitionAndPivots (L m K : ℕ) : Prop :=
  3 ≤ L ∧ ∀ n : ℕ, n < K →
    Pairwise (Function.onFun Disjoint fun y : SiteAtLevel L m K (n + 1) => unitBlock y) ∧
    (⋃ y : SiteAtLevel L m K (n + 1), unitBlock y) =
      (sublattice L m (levelDepth K n) : Set (FourTorus L m)) ∧
    (∀ y : SiteAtLevel L m K (n + 1), (unitBlock y).ncard = L ^ 4) ∧
    (∀ y : SiteAtLevel L m K (n + 1),
      unitBlock y ∩ (sublattice L m (levelDepth K (n + 1)) : Set (FourTorus L m)) =
        {(y : FourTorus L m)}) ∧
    (∀ e : BondAtLevel L m K (n + 1), e.IsPositivelyOriented → IsPivotCharacterized e) ∧
    (∀ e e' : BondAtLevel L m K (n + 1), e.IsPositivelyOriented → e'.IsPositivelyOriented →
      ({e'.source, e'.target} : Set (SiteAtLevel L m K (n + 1))) = {e.source, e.target} → e' = e) ∧
    (∀ b : BondAtLevel L m K n, ∃ e : BondAtLevel L m K (n + 1), e.IsPositivelyOriented ∧
      (b.source : FourTorus L m) ∈ bondDoubleBlock e ∧ (b.target : FourTorus L m) ∈ bondDoubleBlock e) ∧
    ∀ y : SiteAtLevel L m K (n + 1), ∃ e : BondAtLevel L m K (n + 1), e.IsPositivelyOriented ∧ e.source = y
def GaugeTransformComp (L m : ℕ) : Prop :=
  ∀ j : ℤ, -(m : ℤ) ≤ j → ∀ S : Set (Bond L m j), IsReversalClosed S →
  ∀ U V : Bond L m j → ComplexMatrix2, IsGaugeField compactGaugeGroup S U →
    IsGaugeField compactGaugeGroup S V →
  ∀ g h : Site L m j → ComplexMatrix2, IsGaugeMap compactGaugeGroup g →
    IsGaugeMap compactGaugeGroup h →
    (∀ e ∈ S, gaugeTransform h (gaugeTransform g U) e = gaugeTransform (h * g) U e) ∧
    ((∀ e ∈ S, gaugeTransform g U e = gaugeTransform h V e) →
      ∀ e ∈ S, U e = gaugeTransform (fun x => (g x)⁻¹ * h x) V e)
def SecondDerivCompCurve : Prop :=
  ∀ (E F : Type) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [T2Space F] [FiniteDimensional ℝ F]
    (D : Set E) (D' : Set F) (f : E → F) (I : Set ℝ) (γ : ℝ → E),
    IsC2Between D D' f → IsTwiceDiffCurve I γ → MapsTo γ I D →
    IsTwiceDiffCurve I (f ∘ γ) ∧
    deriv (deriv (f ∘ γ)) 0 =
      secondFDeriv f (γ 0) (deriv γ 0) (deriv γ 0) +
        firstFDeriv f (γ 0) (deriv (deriv γ) 0)
def ElementaryStepFacts : Prop :=
  ∀ L m K k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → k < K →
    (LieSquareExpFormula ∧ StepSpacesPosDefFinDim L m K k) ∧
    ExpInjOnBallPi ∧
    LogSeriesNearOne ∧
    LogSeriesOnSpecialUnitary ∧
    ConjugateBySpecialUnitary ∧
    BlockPartitionAndPivots L m K ∧
    GaugeTransformComp L m ∧
    SecondDerivCompCurve
end YangMills.Construction.PeriodicLattice
