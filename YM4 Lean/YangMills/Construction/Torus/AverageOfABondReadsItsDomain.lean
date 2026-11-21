import YangMills.Construction.Torus.FormsAveragesAndOperatorsOnAGeneralTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus
def BlockBondMeanIsLocal : Prop :=
  ∀ (S : ScaleData) (n : ℕ), n ≤ S.lastLevel → ∀ (c : S.PosBond n) (A A' : S.BondField),
    (∀ e : S.BaseBond, (e.1.src : S.Space) ∈ ScaleData.bondSupport c → A e = A' e) →
    S.blockBondMean n A c = S.blockBondMean n A' c
end YangMills.Construction.GeneralTorus
end
