import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import YangMills.Construction.Towers.TheSettingOfTheRemainder
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.EntireDependence
open PeriodicOperators
def IsEntireOn (F : PeriodicData) (S : Finset F.Carrier) (g : (F.Carrier → ℂ) → ℂ) : Prop :=
  ∃ h : (S → ℂ) → ℂ, Differentiable ℂ h ∧ ∀ ζ, g ζ = h fun κ => ζ κ
open Classical in
def edgeIndices (L k : ℕ) (b : PeriodicOperators.PosEdge L k 0) :
    Finset (remainderIndex L k).Carrier :=
  Finset.univ.image fun a : Fin 3 => ((a, b) : Fin 3 × PeriodicOperators.PosEdge L k 0)
def IsLocalAllRadii (L k : ℕ) (I I' : PeriodicData)
    (T : ((remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) : Prop :=
  (∀ ρ : ℝ, 0 < ρ →
      IsLocalWith (remainderIndex L k) I I' T ρ (2 * finestMesh L k)) ∧
    HasEntireKernelEntries (remainderIndex L k) I I' T
end YangMills.Construction.Tower.FullSpace.EntireDependence
end
