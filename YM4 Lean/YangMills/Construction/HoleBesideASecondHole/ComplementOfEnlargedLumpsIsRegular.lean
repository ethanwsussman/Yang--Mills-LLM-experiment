import YangMills.Construction.HoleBesideASecondHole.TheInequalityOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace LumpContours
open BlockAverages
variable {F : BlockFrame}
structure PeriodicLineGrid (p : ℕ) where
  left : ℤ → ℤ
  right : ℤ → ℤ
  left_le : ∀ c, left c ≤ c
  le_right : ∀ c, c ≤ right c
  interval_eq : ∀ c c', left c ≤ c' → c' ≤ right c → left c' = left c ∧ right c' = right c
  interval_length : ∀ c, 2 ^ 14 ≤ right c - left c + 1 ∧ right c - left c + 1 < 2 ^ 15
  periodic : ∀ c, left (c + p) = left c + p ∧ right (c + p) = right c + p
def gridBox (G : (i : Fin 4) → PeriodicLineGrid (F.extent i)) (c : Fin 4 → ℤ) : Finset F.Cell :=
  boxSites F.top (fun i => (G i).left (c i)) (fun i => (G i).right (c i))
def ComplementOfThickenedLumpsRegular : Prop :=
  (∀ (F : BlockFrame) (G : (i : Fin 4) → PeriodicLineGrid (F.extent i)) (H : Finset (Finset F.Cell)),
    (∀ i, 0 < F.extent i) → (∀ l ∈ H, ∃ c, l = gridBox G c) →
      IsOrthantRegular (HoleBounds.cellsOffLumps F H) 2047) ∧
  ∀ (L : ℕ) (g : LumpGrid L) (F : BlockFrame) (H : Finset (Finset F.Cell)), Odd L → (∀ i, 0 < F.extent i) →
    (∀ i, L ∣ F.extent i) → (∀ l ∈ H, IsLump g l) → IsOrthantRegular (HoleBounds.cellsOffLumps F H) 2047
end LumpContours
end YangMills.Construction
end
