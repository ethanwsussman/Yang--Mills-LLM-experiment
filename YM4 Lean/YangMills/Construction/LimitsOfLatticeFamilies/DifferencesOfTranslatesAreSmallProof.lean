import YangMills.Construction.LimitsOfLatticeFamilies.ClassC1AndTheGradientThroughTheLift
import YangMills.Construction.LimitsOfLatticeFamilies.CompactlySupportedClassC1FunctionsAreLipschitz
import YangMills.Construction.LimitsOfLatticeFamilies.DifferencesOfTranslatesAreSmall
import YangMills.Construction.LimitsOfLatticeFamilies.FunctionSpacesAndTheSharpSeminorm
import YangMills.Construction.LimitsOfLatticeFamilies.LengthOfAPointGivesAnInvariantDistance
import YangMills.Construction.LimitsOfLatticeFamilies.TranslationsActOnFunctionsAsIsometries
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits.ShiftDiff
open ModelSpace
theorem differentiableAt_coordLine {w : (Fin 4 → ℝ) → ℝ} (hw : TestFunctions.IsC1R4 w)
    (x : Fin 4 → ℝ) (μ : Fin 4) :
    DifferentiableAt ℝ (fun t : ℝ => w (x + t • Pi.single μ (1 : ℝ))) 0 := by
  have hd : Differentiable ℝ w := ContDiff.differentiable hw (by norm_num)
  have hl : Differentiable ℝ (fun t : ℝ => x + t • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)) := by
    fun_prop
  exact (hd.comp hl) 0
theorem gradR4_sub {u v : (Fin 4 → ℝ) → ℝ} (hu : TestFunctions.IsC1R4 u)
    (hv : TestFunctions.IsC1R4 v) :
    gradR4 (u - v) = gradR4 u - gradR4 v := by
  funext x μ
  exact ((differentiableAt_coordLine hu x μ).hasDerivAt.sub
    (differentiableAt_coordLine hv x μ).hasDerivAt).deriv
theorem grad_sub (hG : C1ViaLift.Claim) {s : Conventions.StandingParameters}
    {Y : ModelSpace} {u v : Y.Carrier s → ℝ} (hu : IsC1 s Y u) (hv : IsC1 s Y v)
    (huv : IsC1 s Y (u - v)) :
    grad s Y (u - v) = grad s Y u - grad s Y v := by
  have e1 := ((hG s Y).2.1 u hu).1
  have e2 := ((hG s Y).2.1 v hv).1
  have c1 := ((hG s Y).1 u).1 hu
  have c2 := ((hG s Y).1 v).1 hv
  refine (((hG s Y).2.1 (u - v) huv).2 _ ?_).symm
  have hc : (u - v) ∘ proj s Y = u ∘ proj s Y - v ∘ proj s Y := rfl
  rw [hc, gradR4_sub c1 c2, ← e1, ← e2]
  rfl
theorem shiftDifferenceBounds_holds (hT : ShiftIsIsometry)
    (hC : C1CompactSuppIsLipschitz)
    (hV : SharpSeminorm.Properties)
    (hL : InvariantDistFromNorm.Claim)
    (hG : C1ViaLift.Claim) :
    ShiftDifferenceBounds := by
  intro s M Y f a b
  obtain ⟨-, hneg, hnn, -, -, -, -⟩ := hL s Y
  have hcomp := (hC.1 s Y).1
  have hδ : 0 ≤ ModelSpace.norm s Y (a - b) := hnn a b
  have hta := (hT s M Y a).2.1 f.1 f.2
  have htb := (hT s M Y b).2.1 f.1 f.2
  obtain ⟨W, hW⟩ := (hV s M Y).2.1 univ
  have hmem : ModelSpace.shift a f.1 - ModelSpace.shift b f.1 ∈ c1CompactSupp s Y univ := by
    have h1 : ModelSpace.shift a f.1 ∈ W := by
      rw [← SetLike.mem_coe, hW]
      exact hta.1
    have h2 : ModelSpace.shift b f.1 ∈ W := by
      rw [← SetLike.mem_coe, hW]
      exact htb.1
    have h3 := W.sub_mem h1 h2
    rw [← SetLike.mem_coe, hW] at h3
    exact h3
  have hdist : ∀ x : Y.Carrier s,
      ModelSpace.dist s Y (x - a) (x - b) = ModelSpace.norm s Y (a - b) := by
    intro x
    have hx : (x - a) - (x - b) = -(a - b) := by abel
    rw [ModelSpace.dist, hx, hneg]
  set h := ModelSpace.shift a f.1 - ModelSpace.shift b f.1 with hh
  set δ := ModelSpace.norm s Y (a - b) with hδdef
  have hfin := (hcomp f).1
  have hsup : ENNReal.ofReal (TestFunctions.uniformNorm h) ≤ gradSup f * (δ.toNNReal : ℝ≥0∞) := by
    have hreal : TestFunctions.uniformNorm h ≤ (gradSup f).toReal * δ := by
      refine ciSup_le fun x => ?_
      have hx := (hcomp f).2.1 (x - a) (x - b)
      rw [hdist] at hx
      simpa [hh, ModelSpace.shift, Real.norm_eq_abs] using hx
    calc ENNReal.ofReal (TestFunctions.uniformNorm h)
        ≤ ENNReal.ofReal ((gradSup f).toReal * δ) := ENNReal.ofReal_le_ofReal hreal
      _ = gradSup f * (δ.toNNReal : ℝ≥0∞) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne]
        rfl
  have hgrad : ∀ y, grad s Y h y =
      grad s Y f.1 (y - a) - grad s Y f.1 (y - b) := by
    intro y
    rw [hh, grad_sub hG hta.1.1 htb.1.1 hmem.1, Pi.sub_apply, hta.2.2.1, htb.2.2.1]
    rfl
  have hosc : gradSup (⟨h, hmem⟩ : c1CompactSupp s Y univ) ≤
      gradOscillation f δ.toNNReal := by
    refine iSup_le fun y => ?_
    have hd : ModelSpace.dist s Y (y - a) (y - b) ≤ (δ.toNNReal : ℝ) := by
      rw [hdist, Real.coe_toNNReal _ hδ]
    rw [show grad s Y (⟨h, hmem⟩ : c1CompactSupp s Y univ).1 y = _ from hgrad y]
    exact le_iSup_of_le (y - a) (le_iSup_of_le (y - b) (le_iSup_of_le hd le_rfl))
  have hlip : ENNReal.ofReal (lipNumber s Y h) ≤ gradOscillation f δ.toNNReal := by
    have hc := hcomp ⟨h, hmem⟩
    calc ENNReal.ofReal (lipNumber s Y h)
        ≤ ENNReal.ofReal (gradSup (⟨h, hmem⟩ : c1CompactSupp s Y univ)).toReal :=
          ENNReal.ofReal_le_ofReal hc.2.2.2
      _ = gradSup (⟨h, hmem⟩ : c1CompactSupp s Y univ) := ENNReal.ofReal_toReal hc.1.ne
      _ ≤ _ := hosc
  refine ⟨hsup, hlip, ?_⟩
  have hscale : ENNReal.ofReal (40 * (M.1 : ℝ) * lipNumber s Y h) =
      40 * (M.1 : ℝ≥0∞) * ENNReal.ofReal (lipNumber s Y h) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [sharpNorm_eq_max s M Y h]
  rcases le_total (TestFunctions.uniformNorm h) (40 * (M.1 : ℝ) * lipNumber s Y h) with hle | hle
  · rw [max_eq_right hle, hscale]
    refine le_max_of_le_right ?_
    gcongr
  · rw [max_eq_left hle]
    exact le_max_of_le_left hsup
end YangMills.Construction.LatticeLimits.ShiftDiff
end
