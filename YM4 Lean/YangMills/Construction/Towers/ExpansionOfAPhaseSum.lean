import YangMills.Construction.Towers.ChargedFormOfTheConstantFieldDefs
import YangMills.Construction.Towers.SymbolsOfTheConstantField
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (toComplexVec)
open YangMills.Construction.Tower.UnitLatticeL2
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
open MagneticWeyl Massive AbelianFieldDensity AbelianFieldDensity.SectorDecomposition
def TrigMatrixSumExpansion : Prop :=
  ∀ (ι : Type) [Fintype ι] (c : ι → ℝ) (n : ι → Fin 4 → ℤ) (M : ι → Matrix (Fin 4) (Fin 4) ℂ),
    (∀ φ, IsFiniteFourierSymbol (trigMatrixSum c n M φ)) ∧
    ((∀ q, trigMatrixSum c n M 0 q = latticeSymbol (toComplexVec q) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) →
      (∀ φ : ℝ, |φ| ≤ Real.pi → ∀ q, pointwiseAdjoint (trigMatrixSum c n M φ) q = trigMatrixSum c n M φ q) →
      (∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ f : ℝ, |f| ≤ Real.pi / 2 →
        ∀ v : VectorL2 L 4,
          AbelianFieldDensity.massiveOp (scaledLinearAngle L f)
              (edgeTensor v raisingPauli) =
            edgeTensor (weylQuant L (2 * f) (trigMatrixSum c n M (2 * f)) v) raisingPauli) →
      ∃ (D C : ℝ) (σ₁ σ₂ : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ)
        (σr : ℝ → AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ),
        ChargedSymbolExpansion D C σ₁ σ₂ (trigMatrixSum c n M) σr)
end YangMills.Construction.Tower.ConstantFieldSymbols
end
