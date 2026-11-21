import YangMills.Construction.Torus.ColumnsOfTheGreenOperatorOnTheTori
import YangMills.Construction.Torus.SettingOfTheExpansionOnThePhysicalTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.GeneralTorus
namespace GaugeSetting
open SeparatedSequences GreenBounds
variable (W : GaugeSetting)
structure ColumnEstimatesHold : Prop where
  coarseForms : W.CoarseFormsCellwise
  bond_le : ∀ (c : W.CoarseBond), ∀ y ∈ W.chain.shellSitesUnion, ∀ b ∈ W.bondSet,
    W.chain.LiesInCell b y →
    |(W.greenColumn c).1 b| ≤
      greenColumnConstant 4 W.data.L (chosen W.data.L).rate (chosen W.data.L).bound *
        W.chain.localSpacing y ^ 2 *
        Real.exp (-(chosen W.data.L).rate * siteCoarseDist y c)
  plaquetteBond_le : ∀ (c : W.CoarseBond) (p : W.data.BasePlaquette),
    ∀ y ∈ W.chain.shellSitesUnion,
    (∃ x ∈ p.cornerSet, (x : W.data.Space) ∈ W.chain.localCube y) →
      ∀ b : W.data.BaseBond, ScaleData.IsPlaquetteBond p b →
        |(W.greenColumn c).1 b| ≤
          plaquetteColumnConstant 4 W.data.L (chosen W.data.L).rate
              (chosen W.data.L).bound *
            W.chain.localSpacing y ^ 2 *
            Real.exp (-(chosen W.data.L).rate * siteCoarseDist y c)
  curl_le : ∀ (c : W.CoarseBond) (p : W.data.BasePlaquette), ∀ y ∈ W.chain.shellSitesUnion,
    (∃ x ∈ p.cornerSet, (x : W.data.Space) ∈ W.chain.localCube y) →
      |W.data.plaquetteCurl (W.greenColumn c).1 p| ≤
        plaquetteColumnConstant 4 W.data.L (chosen W.data.L).rate
            (chosen W.data.L).bound *
          W.chain.localSpacing y *
          Real.exp (-(chosen W.data.L).rate * siteCoarseDist y c)
  kernel_le : ∀ c c' : W.CoarseBond,
    |W.kernelEntry W.coarseGreen c c'| ≤
      compressedEntryConstant 4 W.data.L (chosen W.data.L).rate
          (chosen W.data.L).bound *
        coarseSpacing c ^ 2 * Real.exp (-(chosen W.data.L).rate * coarseDist c c')
end GaugeSetting
def GreenColumnEstimatesOnSetting : Prop :=
  ∀ (W : GaugeSetting) (m K t : ℕ), W.IsExpansionSetting m K t →
    W.data.L ≤ W.data.blockCount →
    (GreenBounds.chosen W.data.L).blockLower ≤ (W.data.blockCount : ℝ) →
    (GreenBounds.chosen W.data.L).gapLower ≤
      (W.data.gapCount : ℝ) * (W.data.blockCount : ℝ) →
    W.ColumnEstimatesHold
end YangMills.Construction.GeneralTorus
