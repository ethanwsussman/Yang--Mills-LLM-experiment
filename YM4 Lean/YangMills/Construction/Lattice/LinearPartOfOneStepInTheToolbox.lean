import YangMills.Construction.Lattice.KernelsOnPositiveBondFamilies
import YangMills.Construction.Lattice.ObjectsOfTheLinearPartOfOneStep
import YangMills.Construction.Lattice.OneStepCovarianceAndDomainsInTheToolbox
import Mathlib
open scoped Matrix.Norms.L2Operator Topology
open Asymptotics
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
def doubleBlockUnion (C : PositiveBondFamily L m K (n + 1)) : SymmetricBondSet L m K n where
  bonds := {v | ∃ c ∈ C.bonds, v ∈ (doubleBlockSymmetricSet c).bonds}
  opposite_mem := fun v ⟨c, hc, hv⟩ => ⟨c, hc, (doubleBlockSymmetricSet c).opposite_mem v hv⟩
def IsPositivePartOfDoubleBlockUnion (P : PositiveBondFamily L m K n)
    (C : PositiveBondFamily L m K (n + 1)) : Prop :=
  ∀ v, v ∈ P.bonds ↔ v ∈ (doubleBlockUnion C).bonds ∧ v.IsPositivelyOriented
def maxDoubleBlockCurvature (C : PositiveBondFamily L m K (n + 1))
    (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2) : ℝ :=
  ⨆ c : ↥C.bonds, doubleBlockCurvature W₀ c.1
def restrictToBondFamily (P : PositiveBondFamily L m K n) (c : BondAtLevel L m K (n + 1))
    (a : P.LieField) : LieBondField (doubleBlockSymmetricSet c) :=
  fun v => a.eval v.1
theorem restrictToDoubleBlock_add (P : PositiveBondFamily L m K n)
    (c : BondAtLevel L m K (n + 1)) (a a' : P.LieField) :
    restrictToBondFamily P c (a + a') =
      restrictToBondFamily P c a + restrictToBondFamily P c a' := by
  funext v
  exact LieBondField.eval_add a a' v.1
theorem restrictToDoubleBlock_smul (P : PositiveBondFamily L m K n)
    (c : BondAtLevel L m K (n + 1)) (z : ℂ) (a : P.LieField) :
    restrictToBondFamily P c (z • a) = z • restrictToBondFamily P c a := by
  funext v
  exact LieBondField.eval_smul z a v.1
def stepBondMap (s : AveragingScheme) (C : PositiveBondFamily L m K (n + 1))
    (P : PositiveBondFamily L m K n) (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (a : P.LieField) : C.LieField :=
  fun c => projectTraceless (stepVariableAt s c.1 (restrictToBondFamily P c.1 a) W₀)
def straightenedFamilyMap [Finite (PositiveBondAtLevel L m K n)] (s : AveragingScheme)
    (C : PositiveBondFamily L m K (n + 1)) (P : PositiveBondFamily L m K n)
    (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2) : FamilyLinearMap P C where
  toFun a c := ⟨straightenedMap s c.1 W₀ (restrictToBondFamily P c.1 a),
    straightenedMap_mem s c.1 W₀ _⟩
  map_add' a a' := by
    have := finite_siteAtLevel (L := L) (m := m) (K := K) (n := n)
    funext c
    refine Subtype.ext ?_
    have hf := Set.toFinite (sitesInBlock (levelDepth K n) c.1.source : Set (SiteAtLevel L m K n))
    change inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.1.source,
        straightenedSummand s c.1 W₀ (restrictToBondFamily P c.1 (a + a')) x =
      inverseFourthPowerWeight L • (∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.1.source,
        straightenedSummand s c.1 W₀ (restrictToBondFamily P c.1 a) x) +
      inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.1.source,
        straightenedSummand s c.1 W₀ (restrictToBondFamily P c.1 a') x
    rw [← smul_add, ← finsum_mem_add_distrib hf]
    simp only [restrictToDoubleBlock_add, straightenedSummand_add]
  map_smul' z a := by
    have := finite_siteAtLevel (L := L) (m := m) (K := K) (n := n)
    funext c
    refine Subtype.ext ?_
    have hf := Set.toFinite (sitesInBlock (levelDepth K n) c.1.source : Set (SiteAtLevel L m K n))
    change inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.1.source,
        straightenedSummand s c.1 W₀ (restrictToBondFamily P c.1 (z • a)) x =
      z • inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.1.source,
        straightenedSummand s c.1 W₀ (restrictToBondFamily P c.1 a) x
    simp only [restrictToDoubleBlock_smul, straightenedSummand_smul]
    rw [finsum_mem_eq_finite_toFinset_sum _ hf, finsum_mem_eq_finite_toFinset_sum _ hf,
      ← Finset.smul_sum, smul_comm z]
def blockCrossingAverage (P : PositiveBondFamily L m K n) (c : BondAtLevel L m K (n + 1))
    (a : P.LieField) : Matrices.ComplexMatrix2 :=
  inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
    ((restrictToBondFamily P c a).pathSum (crossingPath c x) : Matrices.ComplexMatrix2)
section Derivatives
variable (C : PositiveBondFamily L m K (n + 1)) (P : PositiveBondFamily L m K n)
  [Fintype (PositiveBondsOf P.symmetrization)] [Fintype (PositiveBondsOf C.symmetrization)]
def stepLinearPart (s : AveragingScheme) (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2) :
    FamilyLinearMap P C :=
  (fderiv ℂ (stepBondMap s C P W₀) 0).toLinearMap
def stepRemainder (s : AveragingScheme) (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (a : P.LieField) : C.LieField :=
  stepBondMap s C P W₀ a - stepLinearPart C P s W₀ a
structure StepRemainderBound (κ₅ : ℝ) (s : AveragingScheme)
    (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2) (c : ↥C.bonds) (a : P.LieField) :
    Prop where
  differentiable :
    DifferentiableAt ℂ (fun a' => stepRemainder C P s W₀ a' (C.toPositiveBond c)) a
  value_le : Matrices.ComplexMatrix2.operatorNorm
      (stepRemainder C P s W₀ a (C.toPositiveBond c) : Matrices.ComplexMatrix2) ≤
    κ₅ * supOperatorNorm (restrictToBondFamily P c.1 a) ^ 2
  partial_le : ∀ v : ↥P.bonds, partialAlongBondNorm
      (fun a' => stepRemainder C P s W₀ a' (C.toPositiveBond c)) a (P.toPositiveBond v) ≤
    κ₅ * supOperatorNorm (restrictToBondFamily P c.1 a)
  partial_eq_zero : ∀ v : ↥P.bonds, v.1 ∉ (doubleBlockSymmetricSet c.1).bonds →
    partialAlongBond (fun a' => stepRemainder C P s W₀ a' (C.toPositiveBond c)) a
      (P.toPositiveBond v) = 0
variable [Finite (PositiveBondAtLevel L m K n)]
structure StepLinearBounds (κ₅ κ₉ : ℝ) (s : AveragingScheme)
    (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2) : Prop where
  differentiable : DifferentiableAt ℂ (stepBondMap s C P W₀) 0
  value_mem : ∀ (c : ↥C.bonds) (a : P.LieField),
    supOperatorNorm (restrictToBondFamily P c.1 a) < bondFieldRadius L →
      stepVariableAt s c.1 (restrictToBondFamily P c.1 a) W₀ ∈ Matrices.ComplexMatrix2.traceless
  straightened_rowSumNorm_le :
    FamilyLinearMap.rowSumNorm (straightenedFamilyMap s C P W₀) ≤ L
  straightened_columnSumNorm_le :
    FamilyLinearMap.columnSumNorm (straightenedFamilyMap s C P W₀) ≤ ((L : ℝ) ^ 3)⁻¹
  sub_rowSumNorm_le :
    FamilyLinearMap.rowSumNorm (stepLinearPart C P s W₀ - straightenedFamilyMap s C P W₀) ≤
      κ₉ * maxDoubleBlockCurvature C W₀
  sub_columnSumNorm_le :
    FamilyLinearMap.columnSumNorm (stepLinearPart C P s W₀ - straightenedFamilyMap s C P W₀) ≤
      κ₉ * maxDoubleBlockCurvature C W₀
  sub_kernelNorm_le : ∀ (c : ↥C.bonds) (v : ↥P.bonds),
    FamilyLinearMap.kernelNorm (stepLinearPart C P s W₀ - straightenedFamilyMap s C P W₀) c v ≤
      1 / 8 * ((L : ℝ) ^ 4)⁻¹ * κ₉ * doubleBlockCurvature W₀ c.1
  remainder : ∀ (c : ↥C.bonds) (a : P.LieField),
    supOperatorNorm (restrictToBondFamily P c.1 a) ≤ bondFieldRadius L / 2 →
      StepRemainderBound C P κ₅ s W₀ c a
  kernel_eq_zero : ∀ (c : ↥C.bonds) (v : ↥P.bonds), v.1 ∉ (doubleBlockSymmetricSet c.1).bonds →
    FamilyLinearMap.kernel (stepLinearPart C P s W₀) c v = 0 ∧
      FamilyLinearMap.kernel (straightenedFamilyMap s C P W₀) c v = 0
end Derivatives
def StepLinearAssertions (L : ℕ) (κ₅ κ₉ : ℝ) : Prop :=
  0 < κ₅ ∧ 0 < κ₉ ∧
  ∀ m K n : ℕ, 0 < m → n < K →
    (∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
      {v : BondAtLevel L m K n |
          v ∈ (doubleBlockSymmetricSet c).bonds ∧ v.IsPositivelyOriented}.encard ≤
        ((8 * L ^ 4 : ℕ) : ℕ∞)) ∧
    (∀ v : BondAtLevel L m K n,
      {c : BondAtLevel L m K (n + 1) |
          c.IsPositivelyOriented ∧ v ∈ (doubleBlockSymmetricSet c).bonds}.encard ≤ 8) ∧
    ∀ (C : PositiveBondFamily L m K (n + 1)) (P : PositiveBondFamily L m K n),
      C.bonds.Nonempty → IsPositivePartOfDoubleBlockUnion P C →
      ∀ (_ : Fintype (PositiveBondAtLevel L m K n)) (_ : Fintype (PositiveBondsOf P.symmetrization))
        (_ : Fintype (PositiveBondsOf C.symmetrization)) (s : AveragingScheme),
        stepLinearPart C P s (trivialGaugeField : BondAtLevel L m K n → Matrices.ComplexMatrix2) =
            straightenedFamilyMap s C P trivialGaugeField ∧
        (∀ (a : P.LieField) (c : ↥C.bonds),
          (straightenedFamilyMap s C P
              (trivialGaugeField : BondAtLevel L m K n → Matrices.ComplexMatrix2) a
            (C.toPositiveBond c) : Matrices.ComplexMatrix2) = blockCrossingAverage P c.1 a) ∧
        ∀ W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2,
          IsGaugeField compactGaugeGroup (doubleBlockUnion C).bonds W₀ →
          maxDoubleBlockCurvature C W₀ ≤ plaquetteSmallness L →
            StepLinearBounds C P κ₅ κ₉ s W₀
def stepRemainderConstant (L : ℕ) : ℝ := 11 / bondFieldRadius L ^ 2
def stepDeviationConstant (L : ℕ) : ℝ :=
  8 * (L : ℝ) ^ 4 *
    ((1 / admissibleStepRadius L + 2) * (3 * Real.pi * L) / admissibleStepRadius L)
end YangMills.Construction.PeriodicLattice
end
