import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def gaugeGeneratorAtLevel (R : F.FieldChain) (U : ChainChart F) (ξ : F.Site 0 → imaginaryQuaternions) :
    (j : ℕ) → F.Site j → ℍ[ℝ]
  | 0 => fun x => ξ x
  | j + 1 => fun y => ‖relativePathAverage (chartField R U j) (R j) y‖⁻¹ • pureComponent
      (((balancingGauge (chartField R U j) (R j) y : UnitQuaternion) : ℍ[ℝ]) *
        ((1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
          ((pathHolonomy (chartField R U j) (refineSite y) (axisPath h π) : UnitQuaternion) : ℍ[ℝ]) *
            gaugeGeneratorAtLevel R U ξ j (refineSite y + siteOfCoords j h) *
            (((pathHolonomy (R j) (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ])))
def plaquetteBondSum (f : F.Site 0 → Fin 4 → ℝ) (p : F.Site 0 × Fin 4 × Fin 4) : ℝ :=
  f p.1 p.2.1 + f (p.1 + unitStep 0 p.2.1) p.2.2 + f (p.1 + unitStep 0 p.2.2) p.2.1 + f p.1 p.2.2
def plaquetteCornerSum (f : F.Site 0 → ℝ) (p : F.Site 0 × Fin 4 × Fin 4) : ℝ :=
  f p.1 + f (p.1 + unitStep 0 p.2.1) + f (p.1 + unitStep 0 p.2.2) +
    f (p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2)
def regularChainGaugeDirectionsStatement : Prop :=
  ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧ ∀ (F : BlockFrame) (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain)
    (U : ChainChart F) (W : F.GaugeField F.top), Odd F.blockSide → ChartIsRegular S R U →
    (∀ b ∈ innerBonds S 0, ‖U.fine b.1 b.2‖ ≤ c₀) →
    (∀ j, j + 1 < F.top → ∀ b ∈ innerBonds S (j + 1), ‖U.coarse j b.1 b.2‖ ≤ c₀) →
    ∃ H : (F.Site 0 → imaginaryQuaternions) →ₗ[ℝ] (F.Site 0 → Fin 4 → imaginaryQuaternions),
      (∀ ξ : F.Site 0 → imaginaryQuaternions, (∀ y ∈ S, gaugeGeneratorAtLevel R U ξ F.top y = 0) →
        ∃ A : ChainChart F, (∀ b ∈ innerBonds S 0, ((A.fine b.1 b.2 : imaginaryQuaternions) : ℍ[ℝ]) =
            - covariantDiff (R 0) (fun x => ξ x) b.1 b.2 + H ξ b.1 b.2) ∧
          IsStationaryAlong a S R W U A) ∧
      (∀ (ξ : F.Site 0 → imaginaryQuaternions), ∀ b ∈ innerBonds S 0, ‖H ξ b.1 b.2‖ ≤
        C₀ * ‖U.fine b.1 b.2‖ * (‖ξ b.1‖ + ‖ξ (b.1 + unitStep 0 b.2)‖)) ∧
      ∀ (ξ : F.Site 0 → imaginaryQuaternions), ∀ p ∈ innerPlaquettes S 0, ‖linearizedCurl (R 0) (H ξ) p‖ ≤
        C₀ * ((‖linearizedCurl (R 0) U.fine p‖ + plaquetteBondSum (fun x i => ‖U.fine x i‖) p ^ 2) *
            plaquetteCornerSum (fun x => ‖ξ x‖) p +
          plaquetteBondSum (fun x i => ‖U.fine x i‖) p *
            plaquetteBondSum (fun x i => ‖covariantDiff (R 0) (fun x => ξ x) x i‖) p)
end YangMills.Construction.BlockAverages
end
