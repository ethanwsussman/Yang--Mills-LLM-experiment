import YangMills.Construction.Conventions.BoundNumber
import YangMills.Construction.Lattice.CriticalConfigurationsOverABlockField
import YangMills.Construction.OneLoopLaw.BranchesOverAStepAndFirstCaseSets
import YangMills.Construction.PolymerActivities.GaussianNormaliserFunctionalOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Filter Set ParameterChoice PeriodicLattice PeriodicLattice.CubesOfStep
namespace OneLoopLaw
structure LawParameters where
  blockSize : ℕ
  gapSize : ℕ
  B₃ : ℝ
  aV : ℝ
  a₁ : ℝ
  εv : ℝ
  εBar : ℝ
structure LawParameters.Admissible (A : LawParameters) (L : ℕ) : Prop where
  blockSize_eq_pow : ∃ n : ℕ, A.blockSize = L ^ n
  gapSize_eq_pow : ∃ n : ℕ, A.gapSize = L ^ n
  le_gapSize : L ≤ A.gapSize
  minPower_le : criticalMinPower L ≤ A.gapSize * A.blockSize
  radiusMul_le : max (criticalRadiusMul L) 1 ≤ A.B₃
  aV_pos : 0 < A.aV
  aV_le : A.aV ≤ min (criticalUniqueRadius L) 1
  a₁_pos : 0 < A.a₁
  a₁_le : A.a₁ ≤ min (criticalExistRadius L (A.gapSize * A.blockSize))
    (min (A.aV / A.B₃) (Averaging.smoothingRadius L / A.B₃))
  εv_pos : 0 < A.εv
  εv_add_sq_le : A.εv + 3 / 2 * A.εv ^ 2 ≤ A.aV
  εBar_pos : 0 < A.εBar
  εBar_le : A.εBar ≤ A.a₁
  B₃_mul_εBar_le : A.B₃ * A.εBar ≤ A.εv
section FirstCase
variable (c : ChoiceUpToDegreeConstants) {m K k : ℕ}
  (N : Set (BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2))
  (p : (BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) →
    BondAtLevel c.L m K k → Matrices.ComplexMatrix2)
def smallFieldBackground (W : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) :
    BondAtLevel c.L m K k → Matrices.ComplexMatrix2 :=
  backgroundPoint c (pureStepData c 1 W) N p
def smallFieldNormalizer (W : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) : ℝ :=
  gaussianNormalizer c (pureStepData c 1 W) (smallFieldBackground c N p W)
def SmallFieldNormalizerDefined (W : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) :
    Prop :=
  (k < K ∧ HasBackgroundPoint c (pureStepData c 1 W) N ∧
      HasUniqueCriticalOrbit (Averaging.smoothingRadius c.L) c.εv K k
        (pureStepData c 1 W).domains
        (activeBondSet K k (pureStepData c 1 W).domains)
        (fieldDatum c (pureStepData c 1 W) (smallFieldBackground c N p W))) ∧
    RealConstraintDefined (Averaging.smoothingRadius c.L) (smallFieldBackground c N p W)
      {e : BondAtLevel c.L m K (k + 1) | e.IsPositivelyOriented} ∧
    HessianFormDefined c (pureStepData c 1 W) (smallFieldBackground c N p W) ∧
    IsHessianPosDef c (pureStepData c 1 W) (smallFieldBackground c N p W) ∧
    0 < smallFieldNormalizer c N p W
def logNormalizerRatio (W : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) : ℝ :=
  Real.log (smallFieldNormalizer c N p W) -
    Real.log (smallFieldNormalizer c N p
      (1 : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2))
def LogNormalizerRatioDefined (W : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) :
    Prop :=
  SmallFieldNormalizerDefined c N p W ∧
    SmallFieldNormalizerDefined c N p
      (1 : BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2)
def IsBranchFirstCase : Prop :=
  ∃ (h : HasAxialBranchSetting c m K k) (B : StepBranch (axialBranchSetting h).params k) (ρ : ℝ),
    0 < ρ ∧ B.IsFirstCaseSet ρ N ∧
      (∃ O : Set (BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2),
        Tower.IsOpenNhdOfOne O ∧ O ⊆ N) ∧ p = B.lift
end FirstCase
def choiceFunctional (c : ChoiceUpToDegreeConstants) {K k : ℕ}
    (N : ∀ m : ℕ, Set (BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2))
    (p : ∀ m : ℕ, (BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) →
      BondAtLevel c.L m K k → Matrices.ComplexMatrix2) :
    EffectiveAction.TorusFunctional c.L K (k + 1) :=
  fun m W => logNormalizerRatio c (N m) (p m) W
def KernelDecaysExp (P : Fin 4 → Fin 4 → EffectiveAction.IntPoint → ℝ) : Prop :=
  ∃ C δ : ℝ, 0 < δ ∧ ∀ μ ν u, |P μ ν u| ≤ C * Real.exp (-δ * ∑ μ, |(u μ : ℝ)|)
structure ChoiceHasShift (A : LawParameters) (c : ChoiceUpToDegreeConstants) {K k : ℕ}
    (N : ∀ m : ℕ, Set (BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2))
    (p : ∀ m : ℕ, (BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) →
      BondAtLevel c.L m K k → Matrices.ComplexMatrix2) (b : ℝ) :
    Prop where
  analytic : ∀ m : ℕ, 0 < m →
    6 * ((A.gapSize * A.blockSize : ℕ) : ℝ) ≤ RegionChains.sitesPerAxis c.L m K (k + 1) →
    ∃ O : Set (BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2), Tower.IsOpenNhdOfOne O ∧
      (∀ W ∈ O, LogNormalizerRatioDefined c (N m) (p m) W) ∧
      Tower.IsAnalyticFieldFunction O (logNormalizerRatio c (N m) (p m))
  torus : EffectiveAction.IsTorusFunctional c.L K (k + 1) (choiceFunctional c N p)
  stiffness : ∀ t : Fin 3 → Matrices.ComplexMatrix2.LieElement, Orthonormal ℝ t →
    EffectiveAction.IsTorusStiffnessWith t (choiceFunctional c N p) b
  decay : ∀ t : Fin 3 → Matrices.ComplexMatrix2.LieElement, Orthonormal ℝ t →
    ∀ P, EffectiveAction.HasKernelLimit t (choiceFunctional c N p) P → KernelDecaysExp P
def IsOneLoopShiftSequence (L : ℕ) (b : ℕ → ℝ) : Prop :=
  ∀ (A : LawParameters), A.Admissible L →
    ∀ c : ChoiceUpToDegreeConstants, c.L = L → c.εv = A.εv →
      ∀ K k : ℕ, k < K →
        (∀ (N : ∀ m : ℕ, Set (BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2))
          (p : ∀ m : ℕ, (BondAtLevel c.L m K (k + 1) → Matrices.ComplexMatrix2) →
            BondAtLevel c.L m K k → Matrices.ComplexMatrix2),
          (∀ m : ℕ, 0 < m → IsBranchFirstCase c (N m) (p m)) →
            ChoiceHasShift A c N p (b (k + 1))) ∧
        oneLoopShift c K k = b (k + 1)
def oneLoopShifts (L : ℕ) : ℕ → ℝ := Conventions.boundNumber (IsOneLoopShiftSequence L)
def shiftSum (L i n : ℕ) : ℝ := ∑ l ∈ Finset.Icc (i + 1) n, oneLoopShifts L l
def IsShiftSumBound (L : ℕ) (c₂ : ℝ) : Prop :=
  0 ≤ c₂ ∧ ∀ k : ℕ, |shiftSum L 0 k - k * oneLoopCoefficient L| ≤ c₂
def shiftSumBound (L : ℕ) : ℝ := Conventions.boundNumber (IsShiftSumBound L)
end OneLoopLaw
end YangMills.Construction
end
