import YangMills.Construction.DirichletOperator.ChangeOfTheDomainInTheGaugeTerm
import YangMills.Construction.DirichletOperator.RegularityOfTheLocalOperators
import YangMills.Construction.RegionSequence.BlockOperatorNorms
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet RegionSequence RegionSequence.NestedRegions PartitionCubes
open CubeTorus (TensorAnchorSupported)
open CubeOperators (cutoffSize sourceSize)
namespace RemainderEstimates
def remainderRate (L : ℕ) : ℝ :=
  min (min ((CubeOperators.chosenConstants L).δ / (2 * (L : ℝ)))
      ((CubeTorus.chosenConstants L).δ / (2 * (L : ℝ))))
    (min ((RegionSequence.OperatorEstimates.chosenConstants L).δ / 4)
      (GaugeDomainChange.decayRate L / (4 * 4 * (L : ℝ))))
abbrev FormEndo (R : NestedRegions) : Type :=
  (formCutSpace R).space →ₗ[ℝ] (formCutSpace R).space
variable {R : NestedRegions} {M : ℕ}
def ActsAs (T : FormEndo R) (O : (R.FineBond → ℝ) → R.FineBond → ℝ) : Prop :=
  ∀ f : (formCutSpace R).space, (T f).1 = O f.1
def kernelGreenCutoff (P' P : LevelCube R M) (A : R.FineBond → ℝ) : R.FineBond → ℝ :=
  P'.kernel P (P.system.inv (P.system.pullBonds P.partitionFn A))
def defectAdj (P : LevelCube R M) (A : R.FineBond → ℝ) : P.system.setting.FineBond → ℝ :=
  adjointValue (P.system.forms : Set (P.system.setting.FineBond → ℝ)) bondInner bondInner
    P.defectOp A
def cutoffGreenDefectAdj (P : LevelCube R M) (A : R.FineBond → ℝ) : R.FineBond → ℝ :=
  P.system.pushBonds P.partitionFn (P.system.inv (defectAdj P A))
variable (R M) in
def remainderAdj (A : R.FineBond → ℝ) : R.FineBond → ℝ :=
  adjointValue (R.oneForms : Set (R.FineBond → ℝ)) bondInner bondInner (remainderOp R M) A
def expWeight (L : ℕ) (x x' : R.Point) : ℝ := Real.exp (-remainderRate L * R.weightedDist x x')
def doubledCube (x : R.Point) : Set R.Point := cubeHalfSide x (R.levelScale x)
variable (R M) in
def KernelGreenCutoffBound (L : ℕ) (C : ℝ) : Prop :=
  ∃ T : LevelCube R M → LevelCube R M → FormEndo R,
    (∀ P' ∈ active R M, ∀ P ∈ active R M, ActsAs (T P' P) (kernelGreenCutoff P' P)) ∧
    ∀ (p : NormExponent) (x x' : R.allCentres),
      ∑ᶠ q ∈ active R M ×ˢ active R M, cellNorm p (T q.1 q.2) x x' ≤
        C * (M : ℝ)⁻¹ * expWeight L (x : R.Point) x'
variable (R M) in
def CutoffGreenAdjBound (L : ℕ) (C : ℝ) : Prop :=
  ∃ T : LevelCube R M → FormEndo R,
    (∀ P ∈ active R M, ActsAs (T P) (cutoffGreenDefectAdj P)) ∧
    ∀ x x' : R.allCentres,
      ∑ᶠ P ∈ active R M, cellNorm .sup (T P) x x' ≤
        C * (M : ℝ)⁻¹ * expWeight L (x : R.Point) x'
variable (R M) in
def RemainderAdjHolderBound (L : ℕ) (α C : ℝ) : Prop :=
  ∀ x : R.allCentres, ∀ ζ : R.FineSite → ℝ,
    VanishesOff (doubledCube (x : R.Point)) ζ → ∀ A ∈ R.oneForms,
      holderBond α (R.levelScale x) (smulSiteBond ζ (remainderAdj R M A)) ≤
        C * (M : ℝ)⁻¹ * cutoffSize α (R.levelScale x) ζ *
          ∑ᶠ x'' : R.allCentres, expWeight L (x : R.Point) x'' * supBond (cellCutBond (x'' : R.Point) A)
variable (R M) in
def DivergenceSourceBound (L : ℕ) (ε C : ℝ) : Prop :=
  ∀ x x' : R.allCentres, ∀ J : R.Tensor 1,
    TensorAnchorSupported (doubledCube (x' : R.Point)) J →
      ∑ᶠ q ∈ active R M ×ˢ active R M,
          supBond (cellCutBond (x : R.Point) (kernelGreenCutoff q.1 q.2 (divOne J))) ≤
        C * (M : ℝ)⁻¹ * (R.levelScale x')⁻¹ * expWeight L (x : R.Point) x' *
          sourceSize ε (R.levelScale x') J
variable (R M) in
def DivergenceSourceL2Bound (L : ℕ) (C : ℝ) : Prop :=
  ∀ x x' : R.allCentres, ∀ J : R.Tensor 1,
    TensorAnchorSupported (doubledCube (x' : R.Point)) J →
      ∑ᶠ q ∈ active R M ×ˢ active R M,
          ltwoBond (cellCutBond (x : R.Point) (kernelGreenCutoff q.1 q.2 (divOne J))) ≤
        C * (M : ℝ)⁻¹ * (R.levelScale x')⁻¹ * expWeight L (x : R.Point) x' * ltwoTensor J
def ForChainsAbove (L : ℕ) (minBlock minProduct : ℝ) (Φ : NestedRegions → ℕ → Prop) : Prop :=
  ∀ (K m M R₁ : ℕ) (R : NestedRegions), R.L = L → R.IsLevelUnitChain K m M R₁ →
    minBlock ≤ (M : ℝ) → minProduct ≤ (R₁ : ℝ) * (M : ℝ) → Φ R M
end RemainderEstimates
end YangMills.Construction
