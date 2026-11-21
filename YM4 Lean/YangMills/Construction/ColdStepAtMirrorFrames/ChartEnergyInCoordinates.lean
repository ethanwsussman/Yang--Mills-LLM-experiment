import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def imaginaryUnit (α : Fin 3) : imaginaryQuaternions :=
  ⟨![(⟨0, 1, 0, 0⟩ : ℍ[ℝ]), ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] α, by fin_cases α <;> rfl⟩
def imaginaryCoord (α : Fin 3) : imaginaryQuaternions →ₗ[ℝ] ℝ where
  toFun u := ![(u : ℍ[ℝ]).imI, (u : ℍ[ℝ]).imJ, (u : ℍ[ℝ]).imK] α
  map_add' u v := by fin_cases α <;> simp
  map_smul' c v := by fin_cases α <;> simp
abbrev ChartCoordinateIndex (F : BlockFrame) : Type :=
  (↥(chordBonds (finiteCells F)) × Fin 3) ⊕ (↥(innerBonds (finiteCells F) F.top) × Fin 3)
def chartDimension (F : BlockFrame) : ℕ := Fintype.card (ChartCoordinateIndex F)
def chartCoordinateEquiv (F : BlockFrame) : ChartCoordinateIndex F ≃ Fin (chartDimension F) :=
  Fintype.equivFin _
def directionOfIndex : ChartCoordinateIndex F → ChartDirection F
  | .inl p => .inl (p.1.1.1, p.1.1.2, imaginaryUnit p.2)
  | .inr p => .inr (p.1.1.1, p.1.1.2, imaginaryUnit p.2)
def chartDirections (F : BlockFrame) : Fin (chartDimension F) → ChartDirection F :=
  fun k => directionOfIndex ((chartCoordinateEquiv F).symm k)
def coordinateOfIndex (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (dv : F.Site F.top → Fin 4 → imaginaryQuaternions) : ChartCoordinateIndex F → ℝ
  | .inl p => imaginaryCoord p.2 (dw p.1.1.1 p.1.1.2)
  | .inr p => imaginaryCoord p.2 (dv p.1.1.1 p.1.1.2)
def chartCoordinates (dw : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (dv : F.Site F.top → Fin 4 → imaginaryQuaternions) : Fin (chartDimension F) → ℝ :=
  fun k => coordinateOfIndex dw dv ((chartCoordinateEquiv F).symm k)
def ChartedEnergyInCoordinates : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (w dw : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (dv : F.Site F.top → Fin 4 → imaginaryQuaternions),
    Odd F.blockSide → (∀ i, 2 ≤ F.extent i) →
    chartRestriction a w V (chartDirections F) (chartCoordinates dw dv) =
        chartedEnergy a (fun x i => w x i + dw x i) (leftTranslate dv V) ∧
      ∀ σ : Fin (chartDimension F) → ℝ,
        chartRestriction a w V (chartDirections F) (chartCoordinates dw (fun _ _ => 0) + σ) =
          chartRestriction a (fun x i => w x i + dw x i) V (chartDirections F) σ
end ColdStepAtMirrorFrames
end YangMills.Construction
end
