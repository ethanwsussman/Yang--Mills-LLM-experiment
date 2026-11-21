import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
set_option autoImplicit false

section
open Set
noncomputable section
namespace YangMills.Construction
open Coordinates
namespace ComplexManifolds
def coordinatesProdHomeomorph (n m : ℕ) :
    ComplexCoordinates n × ComplexCoordinates m ≃ₜ ComplexCoordinates (n + m) :=
  Homeomorph.sumArrowHomeomorphProdArrow.symm.trans
    (Homeomorph.piCongrLeft (Y := fun _ => ℂ) finSumFinEquiv)
end ComplexManifolds
end YangMills.Construction
end
end

open Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.ComplexAnalysis
open YangMills.Construction.Coordinates
def HolomorphicOnCoordinatesProd {a a' : ℕ} (𝔘 : Set (ComplexCoordinates a × ComplexCoordinates a'))
    (u : ComplexCoordinates a × ComplexCoordinates a' → ℂ) : Prop :=
  ComplexCoordinates.IsHolomorphicIn (N' := 1) (ComplexManifolds.coordinatesProdHomeomorph a a' '' 𝔘)
    (fun z _ => u ((ComplexManifolds.coordinatesProdHomeomorph a a').symm z))
def upperHalfPlaneCoords : Set (ComplexCoordinates 1) := {z | 0 < (z 0).im}
def IdentityTheoremsProdAndUpperHalfPlane : Prop :=
  (∀ (a a' : ℕ), 1 ≤ a + a' →
    ∀ (𝔘 : Set (ComplexCoordinates a × ComplexCoordinates a'))
      (u : ComplexCoordinates a × ComplexCoordinates a' → ℂ)
      (𝔵₀ : ComplexCoordinates a) (ω₀ : ComplexCoordinates a'),
      IsOpen 𝔘 → IsConnected 𝔘 → HolomorphicOnCoordinatesProd 𝔘 u →
      (𝔵₀, ω₀) ∈ 𝔘 → 𝔵₀ ∈ ComplexCoordinates.realLocus a →
      (∀ᶠ p in 𝓝 (𝔵₀, ω₀), p.1 ∈ ComplexCoordinates.realLocus a → u p = 0) →
      ∀ p ∈ 𝔘, u p = 0) ∧
  (∀ u : ℂ → ℂ, ContinuousOn u {z | 0 ≤ z.im} →
    ComplexCoordinates.IsHolomorphicIn (N' := 1) upperHalfPlaneCoords (fun z _ => u (z 0)) →
    (∀ z : ℂ, z.im = 0 → u z = 0) →
    ∀ z : ℂ, 0 ≤ z.im → u z = 0)
end YangMills.Construction.ComplexAnalysis
