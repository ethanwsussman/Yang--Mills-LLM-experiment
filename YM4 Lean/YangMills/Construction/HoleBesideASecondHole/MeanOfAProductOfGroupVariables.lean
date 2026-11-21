import YangMills.Construction.ColdChainAtEveryLevel.ReferenceAndCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace GroupMeans
open YangMills.Construction.BlockAverages
theorem inv_norm_smul_mem_unitary (q : ℍ[ℝ]) (hq : q ≠ 0) : (‖q‖⁻¹ • q) ∈ unitary ℍ[ℝ] := by apply _root_.YangMills.Construction.BlockAverages.smul_inv_norm_mem_unitary <;> assumption
open Classical in
def polarPart (q : ℍ[ℝ]) : UnitQuaternion :=
  if hq : q = 0 then 1 else ⟨‖q‖⁻¹ • q, inv_norm_smul_mem_unitary q hq⟩
def quatAverage {ι : Type} (s : Finset ι) (f : ι → ℍ[ℝ]) : ℍ[ℝ] :=
  (1 / (s.card : ℝ)) • ∑ i ∈ s, f i
def average {ι : Type} (s : Finset ι) (f : ι → ℝ) : ℝ :=
  (1 / (s.card : ℝ)) * ∑ i ∈ s, f i
def meanDirection {ι : Type} (s : Finset ι) (g : ι → UnitQuaternion) : UnitQuaternion :=
  polarPart (quatAverage s fun i => (g i : ℍ[ℝ]))
def variance {ι : Type} (s : Finset ι) (g : ι → UnitQuaternion) : ℝ :=
  average s fun i => ‖(((meanDirection s g)⁻¹ * g i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2
def pointwiseProd {ι : Type} (l : List (ι → UnitQuaternion)) (i : ι) : UnitQuaternion :=
  (l.map fun g => g i).prod
def prodMeanDirections {ι : Type} (s : Finset ι) (l : List (ι → UnitQuaternion)) : UnitQuaternion :=
  (l.map (meanDirection s)).prod
def MeanProductEstimate : Prop :=
  ∀ (ι : Type) (s : Finset ι), s.Nonempty →
    (∀ l : List (ι → UnitQuaternion),
      ‖((prodMeanDirections s l : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        average s (fun i => ‖((pointwiseProd l i : UnitQuaternion) : ℍ[ℝ]) - 1‖) +
          (l.length / 2 : ℝ) * (l.map (variance s)).sum) ∧
    (∀ (g : ι → UnitQuaternion) (T : UnitQuaternion),
      variance s g ≤ average s fun i => ‖(g i : ℍ[ℝ]) - T‖ ^ 2) ∧
    (∀ g : ι → UnitQuaternion, meanDirection s (fun i => (g i)⁻¹) = (meanDirection s g)⁻¹ ∧
      variance s (fun i => (g i)⁻¹) = variance s g) ∧
    ∀ (g : ι → UnitQuaternion) (V : UnitQuaternion),
      ‖(V : ℍ[ℝ]) - meanDirection s g‖ ≤
        2 * Real.sqrt (‖quatAverage s fun i => (g i : ℍ[ℝ])‖ -
          ((quatAverage s fun i => (g i : ℍ[ℝ])) * ((V⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) +
          2 * variance s g
end GroupMeans
end YangMills.Construction
end
