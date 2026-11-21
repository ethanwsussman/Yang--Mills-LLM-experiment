import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
open Classical in
def quaternionUnitPart (q : Quaternion ℝ) : UnitQuaternion :=
  if h : ∃ g : UnitQuaternion, q ≠ 0 ∧ q = ‖q‖ • (g : Quaternion ℝ) then h.choose else 1
def finestSide (F : BlockFrame) (i : Fin 4) : ℕ := F.period 0 i
def constantCurvatureField (F : BlockFrame) (X : imaginaryQuaternions) (μ ν : Fin 4) (l : ℕ) :
    F.GaugeField 0 := fun z i =>
  let N : ℝ := finestSide F μ
  let κ : ℝ := 2 * Real.pi * l / N ^ 2
  if i = ν then expUnit ((κ * siteCoords z μ) • X)
  else if i = μ ∧ siteCoords z μ + 1 = finestSide F μ then expUnit ((- κ * N * siteCoords z ν) • X)
  else 1
def constantCurvatureChain (F : BlockFrame) (X : imaginaryQuaternions) (μ ν : Fin 4) (l : ℕ) :
    (j : ℕ) → F.GaugeField j
  | 0 => constantCurvatureField F X μ ν l
  | j + 1 => fun y i => quaternionUnitPart (contourAverage (constantCurvatureChain F X μ ν l j) (y, i))
end ColdStepAtMirrorFrames
end YangMills.Construction
end
