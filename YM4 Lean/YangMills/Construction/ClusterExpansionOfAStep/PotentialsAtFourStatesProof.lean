import YangMills.Construction.ClusterExpansionOfAStep.PotentialsAtFourStates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepSettings
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.RenormalizationStepParameters
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.ClusterExpansionOfAStep
theorem log_mixed_ratio_of_factorization (D k J Φ u : Fin 2 → Fin 2 → ℝ) (D₁ : ℝ) (hD₁ : 0 < D₁)
    (hk : ∀ i j, 0 < k i j) (hJ : ∀ i j, 0 < J i j) (hΦ : ∀ i j, 0 < Φ i j)
    (hfac : ∀ i j, D i j * k i j * J i j = D₁ * Φ i j * Real.exp (-(u i j)))
    (hΦmix : Φ 1 1 * Φ 0 0 = Φ 1 0 * Φ 0 1) (hkmix : k 1 1 * k 0 0 = k 1 0 * k 0 1)
    (hJmix : J 1 1 * J 0 0 = J 1 0 * J 0 1) :
    0 < D 1 1 * D 0 0 ∧
      Real.log (D 1 1 * D 0 0 / (D 1 0 * D 0 1)) = -(u 1 1 + u 0 0 - u 1 0 - u 0 1) := by
  have hDp : ∀ i j, 0 < D i j := by
    intro i j
    have h1 : 0 < D i j * (k i j * J i j) := by
      have := hfac i j
      rw [mul_assoc] at this
      rw [this]
      have := hΦ i j
      positivity
    have h2 : 0 < k i j * J i j := mul_pos (hk i j) (hJ i j)
    exact (pos_iff_pos_of_mul_pos h1).mpr h2
  refine ⟨mul_pos (hDp 1 1) (hDp 0 0), ?_⟩
  set e : Fin 2 → Fin 2 → ℝ := fun i j => Real.exp (-(u i j)) with he
  have hep : ∀ i j, 0 < e i j := fun i j => Real.exp_pos _
  set X : ℝ := k 1 1 * k 0 0 * (J 1 1 * J 0 0) with hX
  set Yq : ℝ := D₁ ^ 2 * (Φ 1 1 * Φ 0 0) with hY
  have hXp : 0 < X := by
    have := hk 1 1
    have := hk 0 0
    have := hJ 1 1
    have := hJ 0 0
    positivity
  have a1 : D 1 1 * D 0 0 * X = Yq * (e 1 1 * e 0 0) := by
    have h1 := hfac 1 1
    have h2 := hfac 0 0
    calc D 1 1 * D 0 0 * X = (D 1 1 * k 1 1 * J 1 1) * (D 0 0 * k 0 0 * J 0 0) := by
          simp only [hX]; ring
      _ = (D₁ * Φ 1 1 * e 1 1) * (D₁ * Φ 0 0 * e 0 0) := by rw [h1, h2]
      _ = Yq * (e 1 1 * e 0 0) := by simp only [hY]; ring
  have a2 : D 1 0 * D 0 1 * X = Yq * (e 1 0 * e 0 1) := by
    have h1 := hfac 1 0
    have h2 := hfac 0 1
    calc D 1 0 * D 0 1 * X = (D 1 0 * k 1 0 * J 1 0) * (D 0 1 * k 0 1 * J 0 1) := by
          simp only [hX, hkmix, hJmix]; ring
      _ = (D₁ * Φ 1 0 * e 1 0) * (D₁ * Φ 0 1 * e 0 1) := by rw [h1, h2]
      _ = Yq * (e 1 0 * e 0 1) := by simp only [hY, hΦmix]; ring
  have hratio : D 1 1 * D 0 0 / (D 1 0 * D 0 1) = e 1 1 * e 0 0 / (e 1 0 * e 0 1) := by
    have h1 : 0 < D 1 0 * D 0 1 := mul_pos (hDp 1 0) (hDp 0 1)
    have h2 : 0 < e 1 0 * e 0 1 := mul_pos (hep 1 0) (hep 0 1)
    rw [div_eq_div_iff h1.ne' h2.ne']
    apply mul_right_cancel₀ hXp.ne'
    calc D 1 1 * D 0 0 * (e 1 0 * e 0 1) * X = (D 1 1 * D 0 0 * X) * (e 1 0 * e 0 1) := by ring
      _ = Yq * (e 1 1 * e 0 0) * (e 1 0 * e 0 1) := by rw [a1]
      _ = (Yq * (e 1 0 * e 0 1)) * (e 1 1 * e 0 0) := by ring
      _ = (D 1 0 * D 0 1 * X) * (e 1 1 * e 0 0) := by rw [a2]
      _ = e 1 1 * e 0 0 * (D 1 0 * D 0 1) * X := by ring
  have hexp : e 1 1 * e 0 0 / (e 1 0 * e 0 1) = Real.exp (-(u 1 1 + u 0 0 - u 1 0 - u 0 1)) := by
    simp only [he]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  rw [hratio, hexp, Real.log_exp]
theorem potentialMixedDifferenceBound_of_fourCorner (hcorners : FourCornerBound)
    (hpot : PotentialFactorization) : potentialMixedDifferenceBound := by
  intro T hT
  obtain ⟨C, y₀, hC⟩ := hcorners T hT
  refine ⟨C, max y₀ T.floorMin, fun y hy R hR hρA hyx hrow n _ hn s η P P' d hset hin hfour hd hr hcl hk hj => ?_⟩
  have hy1 : y₀ ≤ y := (le_max_left _ _).trans hy
  have hy2 : T.floorMin ≤ y := (le_max_right _ _).trans hy
  have hadm : R.params.Admissible := by
    rw [hR]
    exact hT.fits y hy2
  have hnR : R.params.n₀ ≤ n := by
    rw [hR]
    exact hn
  have hside : IsBlockTorusSide R.params (n * R.params.side) := by
    refine ⟨Dvd.intro_left _ rfl, ?_⟩
    calc R.params.side * R.params.n₀ ≤ R.params.side * n := Nat.mul_le_mul_left _ hnR
      _ = n * R.params.side := mul_comm _ _
  have hchain := hT.chain
  have hanchor : 0 < R.anchorRadius := by
    rw [hρA]
    exact hchain.2.2.2.1
  have hanchor1 : R.anchorRadius ≤ 1 := by
    rw [hρA]
    exact hchain.2.2.2.2.1
  have hball : R.ballRadius ≤ 1 := by
    have h1 := hT.ρ_le
    have h2 := hT.σ_pos
    have h4 : 0 < T.N 0 := hchain.2.2.2.2.2.2.2.1 0
    have h5 : R.ballRadius = T.ballRadius := by
      simp only [StepSetup.ballRadius, ParameterAssignment.ballRadius, hR]
      rfl
    have h6 : 0 < T.N 0 * T.threshold := mul_pos h4 h2
    rw [h5]
    linarith
  have hπ : R.anchorRadius + R.ballRadius < Real.pi := by
    have := Real.pi_gt_three
    linarith
  have hP := fun i j => hpot R hadm hrow hanchor hπ n hnR (s i j) (hset i j) (η i j) (hin i j)
  have hc := hC y hy1 R hR hyx hrow (n * R.params.side) hside P P' _ _ _ d hfour
    (fun i j => (hset i j).isHull (η i j) (hin i j)) hd hr hcl
  obtain ⟨hΦmix, -, hbound⟩ := hc
  have hΦp : ∀ i j, 0 < ∏ X ∈ chainComponents R.range (s i j).support,
      R.clusterFactor (n * R.params.side) ((s i j).field (η i j)) (s i j).support (s i j).labelling X := by
    intro i j
    refine Finset.prod_pos fun X hX => ?_
    have h1 := hrow.2.factor_nonneg (n * R.params.side) hside ((s i j).field (η i j)) (s i j).support
      (s i j).labelling X
    exact lt_of_le_of_ne h1 (Ne.symm ((hset i j).factor_ne_zero (η i j) (hin i j) X hX))
  have hlog := log_mixed_ratio_of_factorization
    (fun i j => R.labelWeight (n * R.params.side) ((s i j).field (η i j)) (s i j).support (s i j).labelling)
    (fun i j => (s i j).kernelProduct (η i j)) (fun i j => (s i j).haarJacobian (η i j))
    (fun i j => ∏ X ∈ chainComponents R.range (s i j).support,
      R.clusterFactor (n * R.params.side) ((s i j).field (η i j)) (s i j).support (s i j).labelling X)
    (fun i j => (s i j).potential (η i j)) (R.functional (n * R.params.side) (trivialField (n * R.params.side)))
    (hP 0 0).1 (fun i j => (hP i j).2.1) (fun i j => (hP i j).2.2.1) hΦp
    (fun i j => (hP i j).2.2.2.1) hΦmix hk hj
  obtain ⟨hpos, hlog⟩ := hlog
  have hb := hbound hpos
  rw [hlog, abs_neg] at hb
  exact hb
end YangMills.Construction.StepSettings
end
