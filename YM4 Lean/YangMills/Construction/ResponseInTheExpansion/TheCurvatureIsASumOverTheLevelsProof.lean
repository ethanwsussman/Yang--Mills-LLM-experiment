import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsASumOverTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps WeightedResponses
open Classical
private theorem sum_curlFunctional_smul {m : ℕ} [NeZero m] (p : TorusPlaquette m) (B : TorusBond m → imaginaryQuaternions) :
    ∑ c : TorusBond m, curlFunctional p c • B c = lieFormCurl B p := by
  have key : ∀ c₀ : TorusBond m, ∑ c : TorusBond m, (if c₀ = c then (1 : ℝ) else 0) • B c = B c₀ := by
    intro c₀
    rw [Finset.sum_eq_single c₀ (fun c _ hc => by rw [if_neg (Ne.symm hc), zero_smul])
      (fun h => absurd (Finset.mem_univ c₀) h), if_pos rfl, one_smul]
  have e : ∀ c : TorusBond m, curlFunctional p c • B c =
      (if (p.1, p.2.1) = c then (1 : ℝ) else 0) • B c + (if (p.1 + TorusFields.unitStep m p.2.1, p.2.2) = c then (1 : ℝ) else 0) • B c -
        (if (p.1 + TorusFields.unitStep m p.2.2, p.2.1) = c then (1 : ℝ) else 0) • B c - (if (p.1, p.2.2) = c then (1 : ℝ) else 0) • B c := by
    intro c
    rw [← add_smul, ← sub_smul, ← sub_smul]
    rfl
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, key]
  rfl
private theorem sum_smul_response_add (a ρA : ℝ) (L u : ℕ) [NeZero L] {n : ℕ} [NeZero n] (h : TorusBond (n * L) → ℝ)
    (B : TorusBond n → imaginaryQuaternions) (E : TorusBond (n * L) → imaginaryQuaternions) :
    ∑ c : TorusBond (n * L), h c • (responseOfLieForm a ρA L u B c + E c) =
      ∑ b : TorusBond (n * L), h b • E b + ∑ c : TorusBond n, responseAdjoint a ρA L u h c • B c := by
  have hswap : ∑ b : TorusBond (n * L), h b • responseOfLieForm a ρA L u B b =
      ∑ c : TorusBond n, responseAdjoint a ρA L u h c • B c := by
    simp only [responseOfLieForm, responseAdjoint, Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm
  simp only [smul_add, Finset.sum_add_distrib]
  rw [hswap, add_comm]
private theorem lieFormCurl_descendedForm (ℓ : TorusLumps.StepParameters) (T : StageTower ℓ) (ρA : ℝ)
    (hρ : ∀ j, (T.stage j).anchorRadius = ρA) (k : ℕ) (nn ρ₀ : ℝ) (d : ℕ) :
    ∀ (n : ℕ) [NeZero n] (u : MarkedSample ℓ (k + d) n) (o : TorusSite (fineSide ℓ.side d n))
      (B : TorusBond n → imaginaryQuaternions) (g : TorusSite n → UnitQuaternion) (p : TorusPlaquette (fineSide ℓ.side d n)),
      lieFormCurl (descendedForm T k nn ρ₀ d n u o B g) p =
        levelFluctuationSum T k nn ρ₀ ρA d n u o g p +
          ∑ c : TorusBond n, adjointTransport ℓ.coupling ρA ℓ.side k d n (curlFunctional p) c • B c := by
  induction d with
  | zero =>
    intro n _ u o B g p
    have h : ∑ c : TorusBond n, curlFunctional (m := n) p c • B c = lieFormCurl (m := n) B p :=
      sum_curlFunctional_smul (m := n) p B
    exact h.symm.trans (zero_add _).symm
  | succ d ih =>
    intro n _ u o B g p
    have e : (T.stage (k + d)).anchorRadius = ρA := hρ _
    simp only [descendedForm, levelFluctuationSum, adjointTransport, e]
    have h := ih (n * ℓ.side) u.1 o
      (fun b => responseOfLieForm ℓ.coupling ρA ℓ.side (k + d) B b +
        deviationInGauge T (k + d) g (supBall (siteAbove ℓ.side (d + 1) n o) (ballRadius ℓ.side nn ρ₀ (d + 1) - 3 * ρ₀)) u.2.2.1
          (topField ℓ (k + d) (n * ℓ.side) u.1) b)
      (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ (topField ℓ (k + d) (n * ℓ.side) u.1) x) p
    have hs := sum_smul_response_add ℓ.coupling ρA ℓ.side (k + d)
      (adjointTransport ℓ.coupling ρA ℓ.side k d (n * ℓ.side) (curlFunctional p)) B
      (deviationInGauge T (k + d) g (supBall (siteAbove ℓ.side (d + 1) n o) (ballRadius ℓ.side nn ρ₀ (d + 1) - 3 * ρ₀)) u.2.2.1
        (topField ℓ (k + d) (n * ℓ.side) u.1))
    exact h.trans ((congrArg (fun z => levelFluctuationSum T k nn ρ₀ ρA d (n * ℓ.side) u.1 o
      (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ (topField ℓ (k + d) (n * ℓ.side) u.1) x) p + z) hs).trans
        (add_assoc _ _ _).symm)
theorem curvatureLevelSum : curvatureLevelSumStatement := by
  intro ℓ T ρA hρ k nn ρ₀ d n _ u o B g p
  exact lieFormCurl_descendedForm ℓ T ρA hρ k nn ρ₀ d n u o B g p
end YangMills.Construction.ResponseInTheExpansion
end
