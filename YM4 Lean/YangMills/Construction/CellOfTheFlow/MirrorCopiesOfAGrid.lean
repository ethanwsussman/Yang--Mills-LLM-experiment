import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusFields WeightedResponses
namespace CellGrid
variable (G : CellGrid)
def reflectionTo (κ κ' : Fin 4 → ℤ) : TorusIsometry where
  axisPerm := 1
  axisSign i := open Classical in if Even (κ' i - κ i) then 1 else -1
  offset i := open Classical in
    if Even (κ' i - κ i) then (G.side : ℤ) * (κ' i - κ i)
    else 2 * G.offset i + (G.side : ℤ) * (κ i + κ' i) + (G.side : ℤ) - 1
  axisSign_unit i := by
    by_cases h : Even (κ' i - κ i) <;> simp [h]
end CellGrid
section Copies
variable {m : ℕ} [NeZero m]
open Classical in
def pullbackBy (g : TorusIsometry) (W' : TorusField m) : TorusField m := fun x k =>
  if g.axisSign (g.axisPerm.symm k) = 1 then W' (g.mapSite x) (g.axisPerm.symm k)
  else (W' (g.mapSite x - unitStep m (g.axisPerm.symm k)) (g.axisPerm.symm k))⁻¹
def cellCopy (G : CellGrid) (κ κ' : Fin 4 → ℤ) (F : TorusField m → ℝ) : TorusField m → ℝ :=
  fun W' => F (pullbackBy (G.reflectionTo κ κ') W')
def DependsOnlyOn (c : Finset (TorusSite m)) (F : TorusField m → ℝ) : Prop :=
  ∀ W W' : TorusField m, (∀ b : TorusBond m, b.1 ∈ c → b.1 + unitStep m b.2 ∈ c → W b.1 b.2 = W' b.1 b.2) →
    F W = F W'
def copyProductMean (G : CellGrid) (β : ℝ) (κ : Fin 4 → ℤ) (A : Finset (Fin 4 → ℤ)) (F : TorusField m → ℝ) : ℝ :=
  ∫ W, ∏ κ' ∈ A, cellCopy G κ κ' F W ∂(wilsonLaw β m)
def chessboardNorm (G : CellGrid) (β : ℝ) (κ : Fin 4 → ℤ) (F : TorusField m → ℝ) : ℝ :=
  copyProductMean G β κ (G.indices m) F ^ (1 / ((G.indices m).card : ℝ))
end Copies
end YangMills.Construction.CellWindows
end
