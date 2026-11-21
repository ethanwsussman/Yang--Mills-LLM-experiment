import YangMills.Construction.Lattice.SettingOfTheTorusBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusBound
def SourceDiskAndClass.Statement : Prop :=
  ∀ (D : Setup) {n : ℕ} (f : Fin n → D.Torus → ℝ) (ϱ : ℝ), D.IsRealFamily f → 0 < ϱ →
    (∀ i, TestFunctions.IsBoundedFun (f i) ∧
      BddAbove (Set.range fun x => ‖f i x‖) ∧
      {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f i x - f i y‖ ≤ C * TestFunctions.euclidDistTorus x y}.Nonempty ∧
      0 ≤ D.sharpNorm (f i) ∧
      (D.sharpNorm (f i) = 0 → ∀ x, f i x = 0)) ∧
    (∀ z : Fin n → ℂ, D.IsWeight (D.smear z f)) ∧
    IsOpen (D.disc ϱ f) ∧
    Convex ℝ (D.disc ϱ f) ∧
    (fun (z : Fin n → ℂ) i => starRingEnd ℂ (z i)) '' D.disc ϱ f = D.disc ϱ f ∧
    (0 : Fin n → ℂ) ∈ D.disc ϱ f ∧
    (∀ w ∈ D.sources ϱ, D.IsWeight w) ∧
    (0 : D.Torus → ℂ) ∈ D.sources ϱ
end YangMills.Construction.TorusBound
