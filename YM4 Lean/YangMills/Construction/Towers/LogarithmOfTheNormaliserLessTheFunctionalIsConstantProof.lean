import YangMills.Construction.Towers.DataOfAChangeOfTheGaugeFixingAtAChain
import YangMills.Construction.Towers.GaussianNumberThroughTwoSaddlesOnATower
import YangMills.Construction.Towers.LogarithmOfTheNormaliserLessTheFunctionalIsConstant
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
theorem logNormaliserSubBackgroundConst_holds (hG : GaussianLogViaTwoSaddleDets)
    (hT : GaugeFixingTransferDataAlongChain) : LogNormaliserSubBackgroundConst := by
  intro L n k hL hn hk
  obtain ⟨C, hC⟩ := hG L n k hL hn hk
  refine ⟨C, ?_⟩
  have hev := hT L n k hL hn hk
  unfold EventuallyNearIdentity at hev ⊢
  filter_upwards [hev] with W hW hinj J μ hJ hμ
  obtain ⟨-, -, h⟩ := hC _ _ _ _ _ _ (hW hinj J μ hJ hμ)
  unfold totalGaussianNormaliser backgroundFunctional hessianSaddleDet ghostSaddleDet
  rw [h]
  ring
end YangMills.Construction.Tower
end
