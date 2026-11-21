import YangMills.Construction.ReflectionPositivity.ReflectionOfAMirrorOfOneTorusProof
import YangMills.Construction.SystemOfAdmissibleConstants.CentredMomentsInTheFineCaseProof
import YangMills.Construction.Torus.DistancesAndLiftsOfTorusOrFourSpace
import YangMills.Construction.TorusOrFourSpace.ChartsOfAnAdmissibleFamilyProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints.DistanceFacts
variable (s : Conventions.StandingParameters)
theorem side_pos : 0 < s.side := by apply _root_.YangMills.Construction.ReflectionPositivity.TorusMirrors.AxisReflection.side_pos <;> assumption
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem euclidNormVec_single_zero {t : ℝ} (ht : 0 ≤ t) :
    euclidNormVec (Pi.single (0 : Fin 4) t) = t := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.AdmissibleCharts.euclidNormVec_single_zero <;> assumption
theorem torusProj_sub (ℓ : ℝ) (x x' : Fin 4 → ℝ) :
    torusProj ℓ x - torusProj ℓ x' = torusProj ℓ (x - x') := by apply _root_.YangMills.SharedProofs.p13492 <;> assumption
theorem pointDist_proj_torus (x x' : Fin 4 → ℝ) :
    pointDist s .torus (proj s .torus x) (proj s .torus x') =
      torusEuclidNorm (torusProj (PeriodicLattice.torusSide s.L s.m) (x - x')) := by
  change torusEuclidNorm (torusProj _ x - torusProj _ x') = _
  rw [torusProj_sub]
theorem torusEuclidNorm_torusProj_eq {v : Fin 4 → ℝ} (h : euclidNormVec v < s.side / 2) :
    torusEuclidNorm (torusProj (PeriodicLattice.torusSide s.L s.m) v) = euclidNormVec v := by
  have hpos := side_pos s
  have hne : PeriodicLattice.torusSide s.L s.m ≠ 0 := hpos.ne'
  rw [torusEuclidNorm_eq_sqrt, euclidNormVec]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hμ : |v μ| ≤ |PeriodicLattice.torusSide s.L s.m| / 2 := by
    have habs : |PeriodicLattice.torusSide s.L s.m| = s.side := abs_of_pos hpos
    rw [habs]
    exact ((abs_apply_le_euclidNormVec v μ).trans_lt h).le
  have hn : ‖torusProj (PeriodicLattice.torusSide s.L s.m) v μ‖ = |v μ| :=
    (AddCircle.norm_coe_eq_abs_iff _ hne).mpr hμ
  rw [hn, sq_abs]
theorem pointDist_proj_le' (E : Ambient) (x x' : Fin 4 → ℝ) :
    pointDist s E (proj s E x) (proj s E x') ≤ euclidNormVec (x - x') := by
  cases E
  · rw [pointDist_proj_torus]
    exact torusEuclidNorm_torusProj_le _
  · exact le_rfl
theorem pointDist_proj_eq' (E : Ambient) (x x' : Fin 4 → ℝ)
    (h : ENNReal.ofReal (euclidNormVec (x - x')) < 2 * injRadius s E) :
    pointDist s E (proj s E x) (proj s E x') = euclidNormVec (x - x') := by
  cases E
  · rw [two_mul_injRadius_torus,
      ENNReal.ofReal_lt_ofReal_iff (half_pos (side_pos s))] at h
    rw [pointDist_proj_torus, torusEuclidNorm_torusProj_eq s h]
  · rfl
theorem exists_lift_pointDist' (E : Ambient) (x : Fin 4 → ℝ) (y : Pt s E) :
    ∃ x', IsLift s E y x' ∧ euclidNormVec (x - x') = pointDist s E (proj s E x) y := by
  cases E
  · have key : ∀ y' : Torus4 (PeriodicLattice.torusSide s.L s.m),
        ∃ x', torusProj (PeriodicLattice.torusSide s.L s.m) x' = y' ∧ euclidNormVec (x - x') =
          torusEuclidNorm (torusProj (PeriodicLattice.torusSide s.L s.m) x - y') := by
      intro y'
      obtain ⟨b, hb, hb'⟩ :=
        exists_torusProj_eq_euclidNormVec_eq (torusProj (PeriodicLattice.torusSide s.L s.m) x - y')
      refine ⟨x - b, ?_, ?_⟩
      · rw [← torusProj_sub, hb, sub_sub_cancel]
      · rw [sub_sub_cancel, hb']
    exact key y
  · exact ⟨y, rfl, rfl⟩
theorem exists_isLift (E : Ambient) (y : Pt s E) : ∃ x, IsLift s E y x := by
  obtain ⟨x, hx, -⟩ := exists_lift_pointDist' s E 0 y
  exact ⟨x, hx⟩
theorem setDiam_openBall_le' (E : Ambient) (y : Pt s E) (r : ℝ) :
    setDiam s E (openBall s E y r) ≤ ENNReal.ofReal (2 * r) := by
  refine iSup₂_le fun a ha => iSup₂_le fun b hb => ENNReal.ofReal_le_ofReal ?_
  have ha' : pointDist s E a y < r := ha
  have hb' : pointDist s E b y < r := hb
  have h := pointDist_triangle E a y b
  rw [pointDist_comm E y b] at h
  linarith
theorem ofReal_pointDist_le_setDiam (E : Ambient) {A : Set (Pt s E)} {a b : Pt s E}
    (ha : a ∈ A) (hb : b ∈ A) : ENNReal.ofReal (pointDist s E a b) ≤ setDiam s E A :=
  le_iSup₂_of_le a ha (le_iSup₂_of_le b hb le_rfl)
theorem exists_pos_lt_two_mul_injRadius (E : Ambient) {r : ℝ} (hr : 0 < r) :
    ∃ t : ℝ, 0 < t ∧ t < r ∧ ENNReal.ofReal t < 2 * injRadius s E := by
  cases E
  · refine ⟨min (r / 2) (s.side / 4), lt_min (half_pos hr) (by linarith [side_pos s]), ?_, ?_⟩
    · exact (min_le_left _ _).trans_lt (half_lt_self hr)
    · rw [two_mul_injRadius_torus,
        ENNReal.ofReal_lt_ofReal_iff (half_pos (side_pos s))]
      exact (min_le_right _ _).trans_lt (by linarith [side_pos s])
  · refine ⟨r / 2, half_pos hr, half_lt_self hr, ?_⟩
    rw [two_mul_injRadius_euclidean]
    exact ENNReal.ofReal_lt_top
theorem setDiam_pos' (E : Ambient) (A : Set (Pt s E)) (hA : A.Nonempty) (hO : IsOpen A) :
    0 < setDiam s E A := by
  obtain ⟨y, hy⟩ := hA
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO y hy
  obtain ⟨t, ht, htr, htρ⟩ := exists_pos_lt_two_mul_injRadius s E hr
  obtain ⟨x, hx⟩ := exists_isLift s E y
  have hv : euclidNormVec ((x + Pi.single (0 : Fin 4) t) - x) = t := by
    rw [add_sub_cancel_left]
    exact euclidNormVec_single_zero ht.le
  have hd : pointDist s E (proj s E (x + Pi.single (0 : Fin 4) t)) y = t := by
    have hx' : proj s E x = y := hx
    have h := pointDist_proj_eq' s E (x + Pi.single (0 : Fin 4) t) x (by rwa [hv])
    rw [hv, hx'] at h
    exact h
  have hmem : proj s E (x + Pi.single (0 : Fin 4) t) ∈ A := by
    apply hball
    change pointDist s E _ y < r
    rw [hd]
    exact htr
  have hle := ofReal_pointDist_le_setDiam s E hmem hy
  rw [hd] at hle
  exact (ENNReal.ofReal_pos.mpr ht).trans_le hle
theorem metricFactsClaim_holds : MetricFactsClaim := fun s E =>
  { pointDist_proj_le := pointDist_proj_le' s E
    pointDist_proj_eq := pointDist_proj_eq' s E
    exists_lift_pointDist := exists_lift_pointDist' s E
    isOpen_openBall := fun y r _ => by
      rw [openBall_eq_ball]
      exact Metric.isOpen_ball
    setDiam_openBall_le := fun y r _ => setDiam_openBall_le' s E y r
    pointDist_comm := pointDist_comm E
    eq_of_pointDist_eq_zero := fun _ _ h => eq_of_pointDist_eq_zero E h
    pointDist_triangle := pointDist_triangle E
    setDiam_pos := setDiam_pos' s E }
end YangMills.Construction.AmbientPoints.DistanceFacts
end
