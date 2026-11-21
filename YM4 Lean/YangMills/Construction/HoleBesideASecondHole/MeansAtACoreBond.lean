import YangMills.Construction.HoleBesideASecondHole.BoxesAreFilled
import YangMills.Construction.HoleBesideASecondHole.MeansAtABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace CoreBondMeans
open BlockAverages LumpContours HoleSavings BondMeans ChainGauges
def excludedBoxSide (J₀ : ℕ) : ℕ := 11 * 2 ^ 12 * J₀
def coreCurvatureBound (C C₀ CJ s : ℝ) : ℝ := Real.sqrt (CJ + C₀ * C) * s
def coreOscillation (L J₀ : ℕ) (C C₀ CJ s : ℝ) : ℝ :=
  72 * (L : ℝ) * coreCurvatureBound C C₀ CJ s + 16 * ((J₀ * Nat.sqrt L : ℕ) : ℝ) * (CJ * Real.sqrt L * s)
def CoreBondMeanEstimate : Prop :=
  ∀ (F : BlockFrame) (g : LumpGrid F.blockSide) (a s θ C C₀ CJ : ℝ) (J₀ : ℕ) (D : HoleData F g a s θ J₀)
    (idx : Finset (Finset (F.Site F.depth)) → ℕ) (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth)
    (U2 : F.FieldChain) (Wt : F.GaugeField F.depth) (γ : F.Site F.depth → UnitQuaternion) (c : F.Cell × Fin 4),
    Odd F.blockSide → HoleBounds.IsCubicTorus F 4096 → 1 ≤ J₀ → 0 < s → 0 < C → 0 < C₀ → 0 < CJ →
    excludedBoxSide J₀ < F.blockSide → 8 * (2 * excludedBoxSide J₀) ^ 3 < F.blockSide ^ 3 →
    D.IsHoleFamily C idx o → D.IsHoleFillingChain C C₀ idx o U2 → D.IsBoxFilling C CJ idx o U2 Wt γ →
    c.1 ∈ D.coreCells C 5 → c.1 + unitStep F.top c.2 ∈ D.coreCells C 5 →
    coreOscillation F.blockSide J₀ C C₀ CJ s ≤ 1 / 8 →
    ‖(((cellRotation Wt (gaugeChain γ U2 F.depth) D.base c.1)⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          LumpContours.contourMean J₀ D.hotFineLumps D.base D.fineField c *
          ((cellRotation Wt (gaugeChain γ U2 F.depth) D.base (c.1 + unitStep F.top c.2) : UnitQuaternion) : ℍ[ℝ]) -
          contourAverage (gaugeChain γ U2 F.depth) c‖ ≤
        2 * ((J₀ * Nat.sqrt F.blockSide : ℕ) : ℝ) ^ 4 * (CJ * Real.sqrt F.blockSide * s) / (F.blockSide : ℝ) ^ 3 +
          12 * coreOscillation F.blockSide J₀ C C₀ CJ s ^ 2 +
          14 * coreOscillation F.blockSide J₀ C C₀ CJ s *
            (8 * (2 * excludedBoxSide J₀ : ℝ) ^ 3 / (F.blockSide : ℝ) ^ 3) ∧
      1 - ‖contourAverage (gaugeChain γ U2 F.depth) c‖ ≤ coreOscillation F.blockSide J₀ C C₀ CJ s ^ 2 ∧
      ‖LumpContours.contourMean J₀ D.hotFineLumps D.base D.fineField c‖ ≤ 1
end CoreBondMeans
end YangMills.Construction
end
