import YangMills.Construction.ColdChainAtEveryLevel.PatchesAndTheGaugeMap
import YangMills.Construction.ColdChainAtEveryLevel.WeightsAndCellNormsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
section Plain
variable {E : Type} [AddCommMonoid E] [Module ℝ E]
def bondLineAverage {j : ℕ} (f : F.Site j → Fin 4 → E) (c : F.Site (j + 1) × Fin 4) : E :=
  (1 / (F.blockSide : ℝ) ^ 4) • ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
    f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2
def nestedAverage (f : F.Site 0 → Fin 4 → E) : (j : ℕ) → F.Site j → Fin 4 → E
  | 0 => f
  | j + 1 => fun y i => bondLineAverage (nestedAverage f j) (y, i)
end Plain
def patchFrameForm (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) {j : ℕ}
    (f : F.Site j → Fin 4 → ℍ[ℝ]) : F.Site j → Fin 4 → ℍ[ℝ] :=
  fun x i => adjointAction (YangMills.Construction.GaugeMap.frameChange S V z (baseSite x))⁻¹ (f x i)
def patchNestedAverageStatement : Prop :=
  ∃ (C c : ℝ) (L1 : ℕ), 0 < C ∧ 0 < c ∧ ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), Odd F.blockSide →
    L1 ≤ F.blockSide → IsAdmissibleAmbient F →
    1024 ≤ m → IsOrthantRegular S m → ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
      ∀ z ∈ S, ∀ u : F.Site 0 → Fin 4 → imaginaryQuaternions, ∀ k, k ≤ F.top → ∀ b ∈ innerBonds S k,
        enclosingCell b.1 ∈ cellBall S z 10 →
        enclosingCell (b.1 + unitStep k b.2) ∈ cellBall S z 10 →
        ‖patchFrameForm S V z (linearPart (referenceFieldChain S V) (baseOnlyChart u) k) b.1 b.2 -
            nestedAverage (patchFrameForm S V z (fun x i => ((u x i : imaginaryQuaternions) : ℍ[ℝ]))) k b.1 b.2‖ ≤
          C * s * (1 / (F.blockSide : ℝ)) ^ (F.top - k) *
            nestedAverage (fun x i => ‖((u x i : imaginaryQuaternions) : ℍ[ℝ])‖) k b.1 b.2
end YangMills.Construction.BlockAverages
end
