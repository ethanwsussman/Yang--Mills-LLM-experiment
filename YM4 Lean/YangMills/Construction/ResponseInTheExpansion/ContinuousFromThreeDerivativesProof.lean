import YangMills.Construction.ClusterExpansionOfAStep.MovesOfFreeBondsForm
import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.SmallUnitsAndTheirLogarithms
import YangMills.Construction.ResponseInTheExpansion.ContinuousFromThreeDerivatives
import YangMills.Construction.SummableBoundsOfTheFlow.MoveOfTheTopAlongItsFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames StepSettings TorusFields
namespace TorusFields
namespace ImaginaryCoords
theorem toImaginary_add (u v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (u + v) = toImaginary u + toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_add <;> assumption
theorem toImaginary_smul (c : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : toImaginary (c • v) = c • toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_smul <;> assumption
theorem toImaginary_toCoords (w : imaginaryQuaternions) : toImaginary (toCoords w) = w := by apply _root_.YangMills.Construction.BlockTrees.toImaginary_toCoords <;> assumption
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
def imaginaryBasis (j : Fin 3) : imaginaryQuaternions := toImaginary (EuclideanSpace.single j 1)
theorem sum_smul_imaginaryBasis (v : EuclideanSpace ℝ (Fin 3)) :
    ∑ j, v j • imaginaryBasis j = toImaginary v := by apply _root_.YangMills.Construction.FreeBondMoves.sum_smul_toImaginary_coordUnit <;> assumption
theorem abs_toCoords_le (w : imaginaryQuaternions) (j : Fin 3) : |toCoords w j| ≤ ‖w‖ := by
  have h1 : ‖toCoords w‖ = ‖w‖ := by
    rw [← norm_toImaginary, toImaginary_toCoords]
  rw [← h1]
  exact PiLp.norm_apply_le (toCoords w) j
theorem continuousAt_of_contDiffThreeAt {m : ℕ} [NeZero m] {G : TorusField m → ℝ} {W : TorusField m}
    (h : ContDiffThreeAt G W) : ContinuousAt G W := by
  classical
  let e : Fin (Fintype.card (TorusBond m × Fin 3)) ≃ TorusBond m × Fin 3 := (Fintype.equivFin _).symm
  let c : Fin (Fintype.card (TorusBond m × Fin 3)) → TorusBond m := fun l => (e l).1
  let X : Fin (Fintype.card (TorusBond m × Fin 3)) → imaginaryQuaternions := fun l => imaginaryBasis (e l).2
  let q : TorusField m → TorusBond m → UnitQuaternion := fun W' b => W' b.1 b.2 * (W b.1 b.2)⁻¹
  let τ : TorusField m → Fin (Fintype.card (TorusBond m × Fin 3)) → ℝ :=
    fun W' l => toCoords (SmallUnits.logUnit (q W' (e l).1)) (e l).2
  have hq : ∀ b, Continuous fun W' : TorusField m => q W' b := fun b => by
    have h1 : Continuous fun W' : TorusField m => W' b.1 b.2 := (continuous_apply b.2).comp (continuous_apply b.1)
    exact h1.mul continuous_const
  have hq1 : ∀ b, q W b = 1 := fun b => mul_inv_cancel _
  have hτ0 : τ W = 0 := by
    have h0 : SmallUnits.logUnit (1 : UnitQuaternion) = 0 := by
      have h1 := SmallUnits.norm_logUnit_le 1
      have g0 : BlockOffsets.distFromOne (1 : UnitQuaternion) = 0 := by simp [BlockOffsets.distFromOne]
      rw [g0, mul_zero] at h1
      exact norm_le_zero_iff.mp h1
    funext l
    simp only [τ, hq1, h0]
    have : toCoords (0 : imaginaryQuaternions) = 0 := by
      ext j
      fin_cases j <;> simp [toCoords]
    rw [this]
    rfl
  have hτc : ContinuousAt τ W := by
    refine continuousAt_pi.2 fun l => ?_
    have hlim : Tendsto (fun W' : TorusField m => 2 * BlockOffsets.distFromOne (q W' (e l).1)) (𝓝 W) (𝓝 0) := by
      have hc : Continuous fun W' : TorusField m => 2 * BlockOffsets.distFromOne (q W' (e l).1) :=
        continuous_const.mul ((continuous_subtype_val.comp (hq _)).sub continuous_const).norm
      have h2 := hc.tendsto W
      simpa [hq1, BlockOffsets.distFromOne] using h2
    rw [ContinuousAt, show τ W l = 0 from congrFun hτ0 l]
    refine squeeze_zero_norm (fun W' => ?_) hlim
    exact (abs_toCoords_le _ _).trans (SmallUnits.norm_logUnit_le _)
  have hre : ∀ᶠ W' in 𝓝 W, ∀ b, 0 < ((q W' b : UnitQuaternion) : ℍ[ℝ]).re := by
    rw [Filter.eventually_all]
    intro b
    have hc : Continuous fun W' : TorusField m => ((q W' b : UnitQuaternion) : ℍ[ℝ]).re :=
      Quaternion.continuous_re.comp (continuous_subtype_val.comp (hq b))
    have h1 : 0 < ((q W b : UnitQuaternion) : ℍ[ℝ]).re := by
      rw [hq1]
      simp
    exact (hc.tendsto W).eventually (lt_mem_nhds h1)
  have hmv : ∀ W' : TorusField m, (∀ b, 0 < ((q W' b : UnitQuaternion) : ℍ[ℝ]).re) →
      perturb c X (τ W') W = W' := by
    intro W' hW'
    funext x i
    have hs : (∑ l, if c l = (x, i) then τ W' l • X l else 0) = SmallUnits.logUnit (q W' (x, i)) := by
      have e1 := Equiv.sum_comp e fun p : TorusBond m × Fin 3 =>
        if p.1 = (x, i) then toCoords (SmallUnits.logUnit (q W' p.1)) p.2 • imaginaryBasis p.2 else 0
      have e2 : (∑ l, if c l = (x, i) then τ W' l • X l else 0) = ∑ l, (fun p : TorusBond m × Fin 3 =>
        if p.1 = (x, i) then toCoords (SmallUnits.logUnit (q W' p.1)) p.2 • imaginaryBasis p.2 else 0) (e l) := rfl
      rw [e2, e1, Fintype.sum_prod_type, Finset.sum_eq_single (x, i)]
      · simp only [if_true]
        rw [sum_smul_imaginaryBasis, toImaginary_toCoords]
      · intro b _ hb
        simp [hb]
      · simp
    show expUnit (∑ l, if c l = (x, i) then τ W' l • X l else 0) * W x i = W' x i
    rw [hs, SmallUnits.expUnit_logUnit _ (hW' _)]
    show W' x i * (W x i)⁻¹ * W x i = W' x i
    simp
  have hg : ContinuousAt (fun σ => G (perturb c X σ W)) (τ W) := by
    rw [hτ0]
    exact (h _ c X).continuousAt
  have hcomp := ContinuousAt.comp (f := τ) (g := fun σ => G (perturb c X σ W)) (x := W) hg hτc
  refine hcomp.congr ?_
  filter_upwards [hre] with W' hW'
  show G (perturb c X (τ W') W) = G W'
  rw [hmv W' hW']
end ImaginaryCoords
open ImaginaryCoords in
theorem continuousAtOfContDiffThreeAt_holds : ContinuousAtOfContDiffThreeAt :=
  fun _ _ _ _ h => continuousAt_of_contDiffThreeAt h
end TorusFields
end YangMills.Construction
end
