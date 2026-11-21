import YangMills.Construction.InequalityOnMirroredCopies.TheInequalityAtEveryDatum
import YangMills.Construction.Lattice.SettingOfTheTorusBound
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ReflectedCopies
open ChessboardTori
def levelMesh (D : ChessboardSetup) (t : ℕ) : ℝ := (D.L : ℝ) ^ ((t : ℤ) - ((D.K : ℕ) : ℤ))
def RadiusCoversScale (ℓ : TorusLumps.StepParameters) (D : ChessboardSetup) (c ϱ : ℝ) (t : ℕ) :
    Prop :=
  c * (TorusLumps.clusterRange (TorusLumps.couplingFlow ℓ D.β t).1 : ℝ) ≤ ϱ / levelMesh D t
def IsRadiusScale (ℓ : TorusLumps.StepParameters) (D : ChessboardSetup) (c ϱ : ℝ) (s : ℕ) :
    Prop :=
  s ≤ (D.K : ℕ) ∧ RadiusCoversScale ℓ D c ϱ s ∧
    ∀ t : ℕ, s < t → t ≤ (D.K : ℕ) → ¬ RadiusCoversScale ℓ D c ϱ t
def CouplingBoundAtRadiusScale : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (Ξ c : ℝ), ℓ.Admissible → 1 ≤ c → ∃ C : ℝ, 0 ≤ C ∧
    ∀ D : ChessboardSetup, IsAdmissibleSetup ℓ Ξ D →
      (∀ t : ℕ, t < (D.K : ℕ) →
        |(TorusLumps.couplingFlow ℓ D.β (t + 1)).1 - (TorusLumps.couplingFlow ℓ D.β t).1| ≤
          2 * ℓ.B) →
      ∀ ϱ : ℝ, 0 < ϱ →
        (∀ s : ℕ, IsRadiusScale ℓ D c ϱ s →
          (TorusLumps.couplingFlow ℓ D.β s).1 ≤ C * (1 + TorusBound.logPos (1 / ϱ))) ∧
        ((∀ t : ℕ, t ≤ (D.K : ℕ) → ¬ RadiusCoversScale ℓ D c ϱ t) →
          D.β ≤ C * (1 + TorusBound.logPos (1 / ϱ)))
end ReflectedCopies
end YangMills.Construction
end
