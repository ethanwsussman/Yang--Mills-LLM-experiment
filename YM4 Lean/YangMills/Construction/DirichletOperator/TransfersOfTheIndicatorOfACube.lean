import YangMills.Construction.DirichletOperator.FactsOfALocalOperatorOfACube
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes
variable {R : NestedRegions} {M : ℕ}
def LevelCube.pushIndicator (P : LevelCube R M) (f : P.system.setting.FineBond → ℝ) : R.FineBond → ℝ :=
  P.system.pushBonds (indicator (P.thicken (5 / 6)) fun _ => 1) f
structure LevelCube.IndicatorTransfers (P : LevelCube R M) : Prop where
  localForm_pushIndicator : ∀ f : P.system.setting.FineBond → ℝ,
    AnchorSupported (P.system.embed '' P.thicken (5 / 6)) f → P.localForm (P.pushIndicator f) = f
  bondInner_pushIndicator : ∀ (f : P.system.setting.FineBond → ℝ) (A : R.FineBond → ℝ),
    bondInner (P.pushIndicator f) A = bondInner f (P.localForm A)
  pNorm_pushIndicator_le : ∀ (p : NormExponent) (X : Set R.Point) (f : P.system.setting.FineBond → ℝ),
    (formCutSpace R).pNorm p (restrictBonds X (P.pushIndicator f)) ≤
      (formCutSpace P.system.setting).pNorm p (restrictBonds (P.localSet X) f)
  pNorm_localForm_le : ∀ (p : NormExponent) (X : Set R.Point) (A : R.FineBond → ℝ),
    (formCutSpace P.system.setting).pNorm p (restrictBonds (P.localSet X) (P.localForm A)) ≤
      (formCutSpace R).pNorm p (restrictBonds X A)
namespace IndicatorTransfer
end IndicatorTransfer
end PartitionCubes
end YangMills.Construction
