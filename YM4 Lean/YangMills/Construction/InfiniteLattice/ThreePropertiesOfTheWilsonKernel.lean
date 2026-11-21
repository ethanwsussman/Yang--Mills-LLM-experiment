import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import YangMills.Construction.InfiniteLattice.WilsonKernelOfBondsWithOneOrientation
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.LatticePhases.WilsonKernelProperties
variable {a : ℝ}
def IsProbDensity (W : OrientedLinkSet a) (g : W.Resample → ℝ) : Prop :=
  Measurable g ∧ (∀ V, 0 ≤ g V) ∧ ∫ V, g V ∂W.resampleHaar = 1
def IsLinearOnContinuousLocal (W : OrientedLinkSet a) (β' : ℝ) : Prop :=
  ∀ (c₁ c₂ : ℂ) (F₁ F₂ : GaugeField a → ℂ),
    F₁ ∈ continuousLocalFunctions a → F₂ ∈ continuousLocalFunctions a →
      W.heatBath β' (fun U => c₁ * F₁ U + c₂ * F₂ U) =
        fun U => c₁ * W.heatBath β' F₁ U + c₂ * W.heatBath β' F₂ U
def AvoidsLinkEndpoints (W : OrientedLinkSet a) (S : Set AmbientSpace) : Prop :=
  ∀ b ∈ W.links, (b.initial : AmbientSpace) ∉ S ∧ (b.terminal : AmbientSpace) ∉ S
def Statement : Prop :=
  ∀ (D : Setup) (W : OrientedLinkSet D.mesh) (β' β'' : ℝ), 0 < β' → 0 < β'' →
    ∀ F ∈ continuousLocalFunctions D.mesh,
      ((∀ U, 0 ≤ W.energy U ∧ W.energy U ≤ 2 * (W.faceCount : ℝ)) ∧
        ∀ U, IsProbDensity W (W.boltzmannDensity β' U)) ∧
      (IsLinearOnContinuousLocal W β' ∧
        observableSupNorm (W.heatBath β' F) ≤ observableSupNorm F ∧
        W.heatBath β' F ∈ continuousLocalFunctions D.mesh) ∧
      (∀ (S : Set AmbientSpace) (H : GaugeField D.mesh → ℂ),
        H ∈ continuousLocalFunctions D.mesh → H ∈ regionObservables D.mesh S →
          AvoidsLinkEndpoints W S →
          W.heatBath β' (fun U => H U * F U) = fun U => H U * W.heatBath β' F U) ∧
      observableSupNorm (fun U => W.heatBath β' F U - W.heatBath β'' F U) ≤
        observableSupNorm F * (Real.exp (2 * |β' - β''| * (W.faceCount : ℝ)) - 1)
end YangMills.Construction.LatticePhases.WilsonKernelProperties
