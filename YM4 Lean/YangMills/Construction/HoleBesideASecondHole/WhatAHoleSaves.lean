import YangMills.Construction.HoleBesideASecondHole.TheInequalityOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.HoleBounds
open BlockAverages LumpContours
def holeSavingStatement : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 8 ∧ ∀ Θ : ℝ, 1 ≤ Θ → ∃ Jf : ℕ, ∀ J₀ : ℕ, Jf ≤ J₀ → ∃ L₀ : ℕ,
    ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ g : LumpGrid L, ∃ s₀ : ℝ, 0 < s₀ ∧
      ∀ s : ℝ, 0 < s → s ≤ s₀ → ∃ cE : ℝ, 0 < cE ∧ ∀ F : BlockFrame, F.blockSide = L → IsCubicTorus F 4096 →
        (L ∣ F.extent 0 → ∀ (H : Finset (Finset (F.Site F.top))), (∀ l ∈ H, IsLump g l) →
          ∀ (V : F.GaugeField F.top) (W : F.GaugeField F.depth) (b : F.Cell → F.Site F.depth)
            (Wl : F.GaugeField F.depth),
            HasLumpWall (cellsOffLumps F H) (hotLumps g s (cutBelow F.depth (cellsOffLumps F H)) W) →
            IsBaseChoice J₀ (hotLumps g s (cutBelow F.depth (cellsOffLumps F H)) W) b →
            IsMinimizingField a
              (cellsOffLumps F H \ lumpsNeighbourhood (hotLumps g (Θ * s) (cellsOffLumps F H) V)) V Wl →
            HoleSavingInequality g a κ s cE J₀ (cellsOffLumps F H)
              (cellsOffLumps F H \ lumpsNeighbourhood (hotLumps g (Θ * s) (cellsOffLumps F H) V))
              (hotLumps g (Θ * s) (cellsOffLumps F H) V) V W b Wl) ∧
        ∀ (V : F.GaugeField F.top) (W : F.GaugeField F.depth) (b : F.Cell → F.Site F.depth)
          (Wl : F.GaugeField F.depth),
          IsCold (torusCells F) F.top (Θ * s) V →
          IsBaseChoice J₀ (hotLumps g s (cutBelow F.depth (torusCells F)) W) b →
          IsMinimizingField a (torusCells F) V Wl →
          HoleSavingInequality g a κ s cE J₀ (torusCells F) (torusCells F) ∅ V W b Wl
end YangMills.Construction.HoleBounds
end
