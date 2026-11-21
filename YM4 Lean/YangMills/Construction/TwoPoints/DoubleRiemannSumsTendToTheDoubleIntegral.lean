import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def pairedGridSum (δ : ℝ) (f g W : AmbientSpace → ℂ) : ℂ :=
  ∑ᶠ q : (Fin 4 → ℤ) × (Fin 4 → ℤ),
    setIntegralOf (gridCube δ q.1) f * setIntegralOf (gridCube δ q.2) g *
      W (gridCenter δ q.2 - gridCenter δ q.1)
def PairedGridSumLimit.Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ W : AmbientSpace → ℂ, ContinuousOn W {z | 2 * ε < euclidNorm z} →
    ∀ f ∈ ccIn (univ : Set AmbientSpace),
      ∀ g ∈ ccIn (univ : Set AmbientSpace),
        (∀ x ∈ tsupport f, ∀ y ∈ tsupport g, 2 * ε < euclidNorm (y - x)) →
          Tendsto (fun δ => pairedGridSum δ f g W) (𝓝[>] 0)
            (𝓝 (lebesgueIntegral fun y : AmbientSpace => lebesgueIntegral fun x : AmbientSpace =>
              f x * g y * W (y - x)))
end YangMills.Construction.TwoPoints
end
