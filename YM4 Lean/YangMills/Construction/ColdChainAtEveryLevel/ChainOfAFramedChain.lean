import YangMills.Construction.ColdChainAtEveryLevel.FramedChainsOverATop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
def chainOfGaugedChainStatement : Prop :=
  ∀ (F : BlockFrame), 0 < F.blockSide → ∀ (X : F.FieldChain) (k : F.SiteGauge), ∃ X' : F.FieldChain,
    X' F.top = X F.top ∧
    (∀ p, ((plaquetteHolonomy (X' 0) p : UnitQuaternion) : ℍ[ℝ]).re =
      ((plaquetteHolonomy (X 0) p : UnitQuaternion) : ℍ[ℝ]).re) ∧
    ∀ j, j < F.top → ∀ c, blockFit (X' j) (X' (j + 1)) c = gaugedBlockFit (X j) (k (j + 1)) (X (j + 1)) c
end YangMills.Construction.BlockAverages
end
