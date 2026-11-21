import YangMills.Construction.ColdStepAtMirrorFrames.SizeFromSquareBounds
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.BlockAverages YangMills.Construction.Interpolation
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace QuadraticBounds
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem momentBound_mono {r : ℝ → ℝ} {Ψ G : BondField ι → ℝ} {q : ℕ} {B B' : ℝ} (hB0 : 0 ≤ B) (hBB : B ≤ B')
    (hm : MomentBound r Ψ G q B) : MomentBound r Ψ G q B' :=
  ⟨hm.1, hm.2.trans (pow_le_pow_left₀ hB0 hBB q)⟩
private theorem lpMomentConstant_nonneg {lam W₀ W : ℝ} (hl : 0 < lam) (hW₀ : 0 ≤ W₀) (hW : 0 ≤ W) (q : ℕ) :
    0 ≤ lpMomentConstant lam W₀ W q := by
  have : 0 ≤ ∏ k ∈ Finset.range q, (4 * (k : ℝ) + 8 * W) := Finset.prod_nonneg fun k _ => by positivity
  unfold lpMomentConstant
  positivity
end QuadraticBounds
open QuadraticBounds in
theorem localSizeOfQuadraticBounds_of_momentBound (hM : momentBoundOfQuadraticBound) :
    LocalSizeOfQuadraticBounds := by
  intro ι _ _ ρ x lam κ W W₀ d Ψ K p hρ hx hlam hκ hW hW₀ hcut hd hconv hsum hslope G B h dZ hB hh hG hval hgrad
  set U : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ} with hU
  have hUo : IsOpen U := by
    have : U = ⋂ b, {η : BondField ι | ‖η b‖ < ρ} := by
      ext η
      simp [hU]
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt ((continuous_apply b).norm) continuous_const
  have hnum := fun q => lpMomentConstant_nonneg (W := W) hlam hW₀ hW q
  have hdiff : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → DifferentiableAt ℝ G η := fun η hη =>
    (hG.contDiffAt (hUo.mem_nhds hη)).differentiableAt (by simp)
  have hgc : ∀ b : ι, ContinuousOn (bondGradNorm G b) U := by
    intro b
    have h1 : ContinuousOn (fderiv ℝ G) U := hG.continuousOn_fderiv_of_isOpen hUo le_rfl
    unfold bondGradNorm
    exact (h1.clm_comp continuousOn_const).norm
  refine ⟨hdiff, 0, fun q hq => ⟨?_, fun b => ?_⟩⟩
  · obtain ⟨w, A, hA, hAa, hw, hSw, hb⟩ := hval
    have := hM ι ρ x lam κ W W₀ d Ψ K p hρ hx hlam hκ hW hW₀ hcut hd hconv hsum hslope
      (fun η => G η - 0) B A w q hq hB hA hw hSw (by simpa using hG.continuousOn)
      (fun η hη => by simpa using hb η hη)
    refine momentBound_mono (by have := hnum q; positivity) ?_ this
    calc lpMomentConstant lam W₀ W q * (B * A) ≤ lpMomentConstant lam W₀ W q * (B * h) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAa hB) (hnum q)
      _ = lpMomentConstant lam W₀ W q * B * h := by ring
  · obtain ⟨w, A, hA, hAa, hw, hSw, hb⟩ := hgrad b
    have hsx := Real.sqrt_nonneg x
    have := hM ι ρ x lam κ W W₀ d Ψ K p hρ hx hlam hκ hW hW₀ hcut hd hconv hsum hslope
      (bondGradNorm G b) (Real.sqrt x * B) A w q hq (by positivity) hA hw hSw (hgc b) hb
    refine momentBound_mono (by have := hnum q; positivity) ?_ this
    calc lpMomentConstant lam W₀ W q * (Real.sqrt x * B * A)
        ≤ lpMomentConstant lam W₀ W q * (Real.sqrt x * B * (h * Real.exp (-(2 * κ * dZ b)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAa (by positivity)) (hnum q)
      _ = lpMomentConstant lam W₀ W q * B * Real.sqrt x * h * Real.exp (-(2 * κ * dZ b)) := by ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
