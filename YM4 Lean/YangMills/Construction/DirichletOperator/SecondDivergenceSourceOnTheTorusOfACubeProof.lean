import YangMills.Construction.DirichletOperator.DivergenceSourceOnTheTorusOfACubeProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
open CubeTorus (torusSetting levelSpacing TensorAnchorSupported)
open CubeOperators (cubeDivOne cubeDivTwo)
open ApproxInverseScales
open CubeDivergence (leibnizRemainder pushBonds formDiv pushedRemainder)
noncomputable section
namespace CubeDivDivSource
variable {𝒮 : NestedRegions} {M : ℕ}
theorem supNorm_eq_norm {S : ℝ} (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem norm_unitStep_le (ν : Fin 4) : ‖(unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point)‖ ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.CubeDivergence.norm_unitStep_le <;> assumption
theorem mem_cubeHalfSide_iff {𝒯 : NestedRegions} (o x : 𝒯.Point) (lam : ℝ) :
    x ∈ cubeHalfSide o lam ↔ ‖x - o‖ ≤ lam := by apply _root_.YangMills.Construction.ApproxInverseTerms.mem_cubeHalfSide_iff <;> assumption
theorem ξ_le_levelScale (y : 𝒮.Point) : 𝒮.ξ ≤ 𝒮.levelScale y := by apply _root_.YangMills.Construction.DivSourceEstimate.ξ_le_levelScale <;> assumption
theorem finite_fineBond (hl : TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem bondInner_eq_sum {𝒯 : NestedRegions} [Fintype 𝒯.FineBond] (A B : 𝒯.FineBond → ℝ) :
    bondInner A B = 𝒯.ξ ^ 4 * ∑ b, A b * B b := by
  simp only [bondInner, finsum_eq_sum_of_fintype]
theorem bondInner_comm {𝒯 : NestedRegions} (A B : 𝒯.FineBond → ℝ) :
    bondInner A B = bondInner B A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
theorem tensorInner_comm {𝒯 : NestedRegions} {r : ℕ} (J J' : 𝒯.Tensor r) :
    tensorInner J J' = tensorInner J' J :=
  Finset.sum_congr rfl fun _ _ => bondInner_comm _ _
section Pushforward
variable (𝔏 : CubeSystem 𝒮)
end Pushforward
theorem leibnizRemainder_apply (Φ : 𝒮.FineSite → ℝ) (J : 𝒮.Tensor 1) (b : 𝒮.FineBond) :
    leibnizRemainder Φ J b =
      ∑ ν, translateBackward ν (forwardDiff ν Φ) b.source * J (constIdx ν) (shiftDown ν b) := by
  simp only [leibnizRemainder, Finset.sum_apply, smulSiteBond, smul_eq_mul]
def idxPair (ν ρ : Fin 4) : Fin 2 → Fin 4 := ![ν, ρ]
theorem sum_idxPair (F : (Fin 2 → Fin 4) → ℝ) :
    ∑ κ, F κ = ∑ ν : Fin 4, ∑ ρ : Fin 4, F (idxPair ν ρ) := by
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (finTwoArrowEquiv (Fin 4)) _ _ fun κ => ?_
  congr 1
  funext i
  fin_cases i <;> rfl
def column {𝒯 : NestedRegions} (J : 𝒯.Tensor 2) (μ : Fin 4) : 𝒯.Tensor 1 :=
  fun ν => J (idxPair (ν 0) μ)
def row {𝒯 : NestedRegions} (J : 𝒯.Tensor 2) (ν : Fin 4) : 𝒯.Tensor 1 :=
  fun ρ => J (idxPair ν (ρ 0))
theorem bondInner_sum_left {𝒯 : NestedRegions} [Fintype 𝒯.FineBond] (f : Fin 4 → 𝒯.FineBond → ℝ)
    (B : 𝒯.FineBond → ℝ) :
    bondInner (fun b => ∑ ν, f ν b) B = ∑ ν, bondInner (f ν) B := by
  simp only [bondInner_eq_sum, Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]
theorem bondInner_add_left {𝒯 : NestedRegions} [Fintype 𝒯.FineBond] (A A' B : 𝒯.FineBond → ℝ) :
    bondInner (A + A') B = bondInner A B + bondInner A' B := by
  simp only [bondInner_eq_sum, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
theorem ξ_le_scale (n : ℕ) : 𝒮.ξ ≤ 𝒮.scale n := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.ξ_le_scale <;> assumption
theorem scale_le_scale_succ (n : ℕ) : 𝒮.scale n ≤ 𝒮.scale (n + 1) := by apply _root_.YangMills.Construction.CubeSourceProof.scale_le_scale_succ <;> assumption
theorem mul_bwdDiff (φ : 𝒮.FineSite → ℝ) (A : 𝒮.FineBond → ℝ) (ν : Fin 4) (b : 𝒮.FineBond) :
    φ b.source * bwdDiff ν A b =
      bwdDiff ν (fun b => φ b.source * A b) b +
        translateBackward ν (forwardDiff ν φ) b.source * A (shiftDown ν b) := by
  change φ b.source * (𝒮.ξ⁻¹ * (A (shiftDown ν b) - A b)) =
    𝒮.ξ⁻¹ * (φ (b.source - unitStep 4 𝒮.side 𝒮.ξ ν) * A (shiftDown ν b) - φ b.source * A b) +
      𝒮.ξ⁻¹ * (φ (b.source - unitStep 4 𝒮.side 𝒮.ξ ν + unitStep 4 𝒮.side 𝒮.ξ ν) -
        φ (b.source - unitStep 4 𝒮.side 𝒮.ξ ν)) * A (shiftDown ν b)
  rw [sub_add_cancel]
  ring
theorem tensorInner_two_eq {𝒯 : NestedRegions} [Fintype 𝒯.FineBond] (J : 𝒯.Tensor 2) :
    tensorInner J J = 𝒯.ξ ^ 4 *
      ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ b, J (idxPair ν ρ) b * J (idxPair ν ρ) b := by
  unfold tensorInner
  rw [sum_idxPair, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ρ _ => bondInner_eq_sum _ _
theorem abs_second_difference_le {Q : LevelCube 𝒮 M} {c r : ℝ}
    (hb : CubeGeometry.IsScaleBounded (𝒮 := 𝒮) c r Q.partitionFn) (ν ρ : Fin 4)
    (x : 𝒮.FineSite) :
    |translateBackward ν (forwardDiff ν (translateBackward ρ
      (forwardDiff ρ (fun x : 𝒮.FineSite => Q.partitionFn x)))) x| ≤ c * r⁻¹ ^ 2 := by
  have e : translateBackward ν (forwardDiff ν (translateBackward ρ
      (forwardDiff ρ (fun x : 𝒮.FineSite => Q.partitionFn x)))) x =
      -forwardDiff ν (backwardDiff ρ (fun x : 𝒮.FineSite => Q.partitionFn x))
        (x - unitStep 4 𝒮.side 𝒮.ξ ν) := by
    simp only [translateBackward, forwardDiff, backwardDiff, sub_add_cancel]
    ring
  rw [e, abs_neg]
  exact hb.second_difference (forwardDiff ν) (backwardDiff ρ) ⟨ν, Or.inl rfl⟩ ⟨ρ, Or.inr rfl⟩ _
end CubeDivDivSource
end
end YangMills.Construction
