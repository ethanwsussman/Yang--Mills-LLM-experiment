import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.UnitaryCombinations
open YangMills.Construction.OneLoopNotation
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (torusAverage castVec)
namespace Tower
namespace MagneticWeyl
def latticePoint (L : ℕ) (n : Fin 4 → ℤ) : FullSpace.Vertex L 0 0 :=
  ⟨fun μ => (n μ : ℝ) * meshAt L 0 0, n, fun _ => rfl⟩
end MagneticWeyl
open MagneticWeyl in
def WeylExplicitFormulas : Prop :=
  ∀ (L : ℕ) (φ : ℝ),
    (∀ (w : FullSpace.Vertex L 0 0 → ℂ) (x : FullSpace.Vertex L 0 0),
      FullSpace.chargedShift (halfFluxAngle L φ) 1 w x =
          Complex.exp (Complex.I * (φ : ℂ) * (((x : AmbientSpace) 0 : ℝ) : ℂ)) *
            w (x + InfiniteLattice.axisStep _ 1) ∧
        ∀ μ : Fin 4, μ ≠ 1 →
          FullSpace.chargedShift (halfFluxAngle L φ) μ w x = w (x + InfiniteLattice.axisStep _ μ)) ∧
    (∀ μ : Fin 4,
      IsUnitaryOp
          ((magneticTranslation L φ μ).toLinearEquiv : ScalarL2 L →ₗ[ℂ] ScalarL2 L) ∧
        ∀ (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0),
          magneticTranslation L φ μ w x 0 =
            FullSpace.chargedShift (halfFluxAngle L φ) μ (fun y => w y 0) x) ∧
    (∀ w : ScalarL2 L,
      magneticTranslation L φ 0 (magneticTranslation L φ 1 w) =
        Complex.exp (Complex.I * (φ : ℂ)) • magneticTranslation L φ 1 (magneticTranslation L φ 0 w)) ∧
    (∀ μ ν : Fin 4, μ ≠ ν → ¬(μ = 0 ∧ ν = 1) → ¬(μ = 1 ∧ ν = 0) → ∀ w : ScalarL2 L,
      magneticTranslation L φ μ (magneticTranslation L φ ν w) =
        magneticTranslation L φ ν (magneticTranslation L φ μ w)) ∧
    ∀ (n : Fin 4 → ℤ) (w : ScalarL2 L) (x : FullSpace.Vertex L 0 0),
      magneticWeyl L φ n w x =
        Complex.exp (Complex.I * (φ : ℂ) *
          ((n 1 : ℂ) * (((x : AmbientSpace) 0 : ℝ) : ℂ) + (n 0 : ℂ) * (n 1 : ℂ) / 2)) •
          w (x + latticePoint L n)
end Tower
end YangMills.Construction
end
