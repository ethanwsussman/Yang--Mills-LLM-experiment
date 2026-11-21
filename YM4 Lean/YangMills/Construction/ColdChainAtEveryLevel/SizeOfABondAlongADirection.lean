import YangMills.Construction.ColdChainAtEveryLevel.FactsOfTheLogarithm
import YangMills.Construction.ColdChainAtEveryLevel.LevelRecursionNearACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BondAverageNorms
open BlockAverages
variable {F : BlockFrame}
def expTwistedField {j : ℕ} (R : F.GaugeField j) (f : F.Site j → Fin 4 → imaginaryQuaternions) : F.GaugeField j :=
  fun x i => expUnit (f x i) * R x i
def bondAverageNorm {j : ℕ} (R : F.GaugeField j) (f : F.Site j → Fin 4 → imaginaryQuaternions)
    (c : F.Site (j + 1) × Fin 4) : ℝ :=
  ‖contourAverage (expTwistedField R f) c‖
def levelCoordinateImaginary (R : F.FieldChain) (U : ChainChart F) (j : ℕ) : F.Site j → Fin 4 → imaginaryQuaternions :=
  fun x i => ⟨levelCoordinate R U j x i, re_unitQuaternionLog _⟩
def bondAverageNormDerivStatement : Prop :=
  ∃ L0 : ℕ, ∀ L : ℕ, Odd L → L0 ≤ L → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (F : BlockFrame) (m : ℕ) (S : Finset F.Cell), F.blockSide = L → IsAdmissibleAmbient F → 1024 ≤ m →
      IsOrthantRegular S m →
      ∀ (s : ℝ) (V : F.GaugeField F.top), 0 < s → s ≤ c → IsCold S F.top s V →
        ∀ (j : ℕ) (b : F.Site (j + 1) × Fin 4), j < F.top → b ∈ innerBonds S (j + 1) →
          (∀ U : ChainChart F, ‖gaugedBondAverage (referenceFieldChain S V) U j b‖ =
            bondAverageNorm (referenceFieldChain S V j) (levelCoordinateImaginary (referenceFieldChain S V) U j) b) ∧
          ∀ (f : F.Site j → Fin 4 → imaginaryQuaternions) (t : ℝ), 0 ≤ t → t ≤ c →
            BoundedOnAdjacentBlocks (fun x i => ‖(f x i : ℍ[ℝ])‖) b t →
            (∀ (k : ℕ) (g : Fin k → F.Site j → Fin 4 → imaginaryQuaternions), AnalyticAt ℝ (fun σ : Fin k → ℝ =>
              bondAverageNorm (referenceFieldChain S V j) (fun x i => f x i + ∑ l, σ l • g l x i) b) 0) ∧
            ∀ (g : F.Site j → Fin 4 → imaginaryQuaternions) (ρ : ℝ), 0 ≤ ρ →
              BoundedOnAdjacentBlocks (fun x i => ‖(g x i : ℍ[ℝ])‖) b ρ →
              |deriv (fun τ : ℝ =>
                  bondAverageNorm (referenceFieldChain S V j) (fun x i => f x i + τ • g x i) b) 0| ≤
                C * (t + s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1))) ^ 2) * ρ
end YangMills.Construction.BondAverageNorms
end
