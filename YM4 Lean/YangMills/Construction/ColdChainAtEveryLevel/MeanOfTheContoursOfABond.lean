import YangMills.Construction.ColdChainAtEveryLevel.NearlyFlatPairing
import YangMills.Construction.ColdChainAtEveryLevel.NormsOfCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
variable {F : BlockFrame}
def pureGap {j : ℕ} (X R : F.GaugeField j) : F.Site j → Fin 4 → ℍ[ℝ] :=
  fun x i => pureComponent ((X x i * (R x i)⁻¹ : UnitQuaternion) : ℍ[ℝ])
def relativeContourMean {j : ℕ} (X R : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) : UnitQuaternion :=
  polarUnit (gaugedContourAverage X (balancingGauge X R) c) * (polarUnit (contourAverage R c))⁻¹
def contourMeanFirstOrderStatement : Prop :=
  ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (F : BlockFrame) (j : ℕ) (X R : F.GaugeField j) (b : F.Site (j + 1) × Fin 4) (t ε : ℝ),
    Odd F.blockSide → j + 1 ≤ F.top → 0 ≤ t → 0 ≤ ε → (F.blockSide : ℝ) * t ≤ c₀ → ε ≤ c₀ →
    (∀ a ∈ FlatPairing.twoBlockHull F.blockSide b.2, ∀ k, a + LatticeFractionalIntegration.basisVector k ∈ FlatPairing.twoBlockHull F.blockSide b.2 →
      ‖((X (refineSite b.1 + siteOfCoords j a) k * (R (refineSite b.1 + siteOfCoords j a) k)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ t) →
    (∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2) * (polarUnit (contourAverage R b))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ε) →
    ‖parallelAverage R (pureGap X R) b‖ ≤ (F.blockSide : ℝ) * t ∧
      ‖pureComponent ((relativeContourMean X R b : UnitQuaternion) : ℍ[ℝ]) - parallelAverage R (pureGap X R) b‖ ≤
        C * ((F.blockSide : ℝ) * t) * ((F.blockSide : ℝ) * t + ε) ∧
      ‖((relativeContourMean X R b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        4 * ‖parallelAverage R (pureGap X R) b‖ + C * ((F.blockSide : ℝ) * t) * ((F.blockSide : ℝ) * t + ε)
end BlockAverages
end YangMills.Construction
end
