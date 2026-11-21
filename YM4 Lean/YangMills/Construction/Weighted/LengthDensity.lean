import YangMills.Construction.Weighted.SeparatedRegions
import Mathlib
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace Weighted
theorem TorusData.side_pos (D : TorusData) : 0 < D.side := by
  obtain ⟨k, hk, hS⟩ := D.side_multiple
  have hL : 0 < D.L := by have := D.blocking.three_le_factor; omega
  have hM : 0 < D.blockNumber := lt_of_lt_of_le hL D.le_blockNumber
  have := D.bareSpacing_pos
  rw [hS]
  positivity
instance (D : TorusData) : Fact (0 < D.side) := ⟨D.side_pos⟩
variable {S : ℝ}
abbrev TorusL1 (S : ℝ) : Type := PiLp 1 fun _ : Fin 4 => AddCircle S
theorem norm_toLp_eq_torusL1Norm (x : Torus4 S) :
    ‖(WithLp.toLp 1 x : TorusL1 S)‖ = torusL1Norm x := by
  rw [torusL1Norm_eq_sum_norm, PiLp.norm_eq_of_L1]
def l1LengthMeasure (S : ℝ) [Fact (0 < S)] : Measure (Torus4 S) :=
  (μH[1] : Measure (TorusL1 S)).map WithLp.ofLp
def setLIntegralL1 [Fact (0 < S)] (Γ : Set (Torus4 S)) (g : Torus4 S → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x in Γ, g x ∂(l1LengthMeasure S)
def localLip (f : Torus4 S → ℝ) (x : Torus4 S) : ℝ≥0∞ :=
  limsup (fun x' => ENNReal.ofReal (|f x' - f x| / torusL1Norm (x' - x))) (𝓝[≠] x)
def LipschitzL1 (f : Torus4 S → ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ x x', |f x' - f x| ≤ C * torusL1Norm (x' - x)
namespace SeparatedChain
variable {D : TorusData} (B : SeparatedChain D)
def weightDensity (x : D.Space) : ℝ :=
  ∑ n ∈ Finset.Icc 1 D.top, (D.scale n)⁻¹ * (B.layer n).indicator (fun _ => (1 : ℝ)) x +
    (D.scale 0)⁻¹ * (B.stage 1)ᶜ.indicator (fun _ => (1 : ℝ)) x
end SeparatedChain
end Weighted
end YangMills.Construction
