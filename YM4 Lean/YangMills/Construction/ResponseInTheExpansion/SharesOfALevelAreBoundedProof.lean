import YangMills.Construction.ResponseInTheExpansion.ContinuousFromThreeDerivatives
import YangMills.Construction.ResponseInTheExpansion.ImageOfOneAtABlockProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelShares
open TorusFields TorusLumps BlockAverages
variable {n : ℕ} [NeZero n]
omit [NeZero n] in
theorem mixedDeriv_fin_zero (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 0 → TorusBond n)
    (X : Fin 0 → imaginaryQuaternions) : mixedDeriv G W c X = G W := by apply _root_.YangMills.Construction.TorusLumps.mixedDeriv_of_fin_zero <;> assumption
omit [NeZero n] in
theorem fieldsAgreeNear_zero {n' : ℕ} (W : TorusField n) (W' : TorusField n') (y : TorusSite n)
    (y' : TorusSite n') : FieldsAgreeNear W W' y y' 0 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.BlockImageOfOne.fieldsAgreeNear_zero <;> assumption
open TorusFrame StepCosts ShareFamilies in
theorem levelShareBoundedContinuous_holds (hshares : LevelSharesFormCurvatureFamily)
    (hcont : ContinuousAtOfContDiffThreeAt) : LevelShareBoundedContinuous := by
  intro T hT y hy t n _ hn z
  have hn3 : 2 < n := by
    have := hT.n₀_ge
    omega
  cases t with
  | zero =>
    refine ⟨∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite n)),
      |(((plaquetteVertices p.1 p.2.1 p.2.2).count z : ℕ) : ℝ) / 4| * 2, fun W _ => ⟨?_, ?_⟩⟩
    · show |∑ p ∈ plaquettesIn Finset.univ, (((plaquetteVertices p.1 p.2.1 p.2.2).count z : ℕ) : ℝ) / 4 *
          plaquetteEnergy W p.1 p.2.1 p.2.2| ≤ _
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [abs_of_nonneg (plaquetteEnergy_nonneg W _ _ _)]
      exact plaquetteEnergy_le_two W _ _ _
    · have : Continuous fun W' : TorusField n => levelShare T.coupling T.side 0 Finset.univ z W' :=
        continuous_finsetSum _ fun p _ => continuous_const.mul (continuous_plaquetteEnergy p.1 p.2.1 p.2.2)
      exact this.continuousAt
  | succ s =>
    obtain ⟨hF, -, -⟩ := hshares T hT y hy s
    set share : TorusField n → ℝ := fun W => levelShare T.coupling T.side (s + 1) Finset.univ z W
      with hshare
    have e : ∀ W : TorusField n, levelShareFamily T.coupling T.side (s + 1) n z W = share W := by
      intro W
      unfold levelShareFamily
      rw [dif_neg (NeZero.ne n)]
    have ef : levelShareFamily T.coupling T.side (s + 1) n z = share := funext e
    have hσ : 0 < (T.stepParameters y).threshold := hT.σ_pos
    have hflat : IsCold (T.stepParameters y).threshold (trivialField n) := fun x μ ν _ => by
      simpa [curvature, holonomy, trivialField] using hσ
    set Cc := weightGrowthSup T.rt T.n₁ * maxOfFirstFour T.N with hCc
    refine ⟨Cc / (T.stepParameters y).weight 0 + |share (trivialField n)|, fun W hW => ⟨?_, ?_⟩⟩
    · have h := hF.local_density n n hn hn z z W (trivialField n) 0 (by omega) (by omega) hW hflat
        (fieldsAgreeNear_zero _ _ _ _) 0
        (fun l => l.elim0) (fun l => l.elim0) (by omega) (fun l => l.elim0) (fun l => l.elim0)
      rw [mixedDeriv_fin_zero, mixedDeriv_fin_zero] at h
      unfold centered at h
      rw [e W, e (trivialField n), sub_self, sub_zero] at h
      have h2 : |share W| ≤ |share W - share (trivialField n)| + |share (trivialField n)| := by
        simpa using abs_add_le (share W - share (trivialField n)) (share (trivialField n))
      linarith
    · have := hcont n _ W (hF.smooth n hn z W hW)
      rwa [ef] at this
end YangMills.Construction.LevelShares
end
