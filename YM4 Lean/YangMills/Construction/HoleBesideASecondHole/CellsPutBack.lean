import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LumpContours
open YangMills.Construction.BlockAverages
variable {F : BlockFrame}
open Classical in
def cellsNear (S D : Finset F.Cell) (m : ℕ) : Finset F.Cell :=
  S.filter fun z => ∃ y ∈ D, cellSupDist z y ≤ m
open Classical in
def reinsertionBound (a C r : ℝ) (S S₁ : Finset F.Cell) (V : F.GaugeField F.top) : ℝ :=
  cutEffectiveAction a F.top S₁ V + C * r ^ 2 * (cellsNear S (S \ S₁) 330).card
open Classical in
def IsReinsertionWitness (a Ca CL r : ℝ) (S S₁ : Finset F.Cell) (V : F.GaugeField F.top)
    (W : F.GaugeField F.depth) : Prop :=
  plainBlockEnergy a S W V ≤ reinsertionBound a Ca r S S₁ V ∧
    (∀ b ∈ cutBonds (cutBelow F.depth S), ‖(bondCoordinate 1 V W b : ℍ[ℝ])‖ ≤ CL * r) ∧
    (∀ p ∈ cutPlaquettes (cutBelow F.depth S), plaquetteDefect W p ≤ CL * r) ∧
    ∀ Wl : F.GaugeField F.depth, IsMinimizingField a S₁ V Wl → ∀ b ∈ cutBonds (cutBelow F.depth S),
      (∀ y ∈ S \ S₁, 320 < cellSupDist (enclosingCell b.1) y) →
        bondCoordinate 1 V W b = bondCoordinate 1 V Wl b
def ReinsertionCostEstimate : Prop :=
  ∀ a : ℝ, 0 < a → ∃ Ca : ℝ, 0 < Ca ∧ ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∃ CL r₀ : ℝ, 0 < CL ∧ 0 < r₀ ∧
      ∀ (F : BlockFrame) (S S₁ : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → S₁ ⊆ S →
        IsOrthantRegular S 1024 → IsOrthantRegular S₁ 1024 →
        ∀ (r : ℝ) (V : F.GaugeField F.top), 0 < r → r ≤ r₀ → IsCold S F.top r V →
          cutEffectiveAction a F.top S V ≤ reinsertionBound a Ca r S S₁ V ∧
            ∃ W : F.GaugeField F.depth, IsReinsertionWitness a Ca CL r S S₁ V W
end YangMills.Construction.LumpContours
end
