import YangMills.Construction.InfiniteLattice.TransportToATorusProof
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.TorusOrFourSpace.FiniteCoversByBallsAndPartitionsOfUnity
import YangMills.Construction.TorusOrFourSpace.FinitePartitionsOfUnityAtAGivenScale
import YangMills.Construction.TorusOrFourSpace.QuotientMapCompactSetsAndFunctionsOfClassC1
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefined
import Mathlib
set_option autoImplicit false
open scoped ENNReal ContDiff
noncomputable section
namespace YangMills.Construction.PeriodicSpace.ScalePartitions
open Kind TorusMetric
private theorem euclidNorm_le_two_supNorm (v : Fin 4 → ℝ) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_le_two_mul_norm <;> assumption
private def euclidDist (x y : Fin 4 → ℝ) : ℝ := euclidNormVec (x - y)
private theorem dist_le_euclidDist (x y : Fin 4 → ℝ) : dist x y ≤ euclidDist x y := by apply _root_.YangMills.Construction.PeriodicTransport.dist_le_euclidNormVec <;> assumption
private theorem euclidDist_le_two_dist (x y : Fin 4 → ℝ) : euclidDist x y ≤ 2 * dist x y := by
  rw [dist_eq_norm]
  exact euclidNorm_le_two_supNorm _
private theorem closureWrt_euclidDist (Z : Set (Fin 4 → ℝ)) :
    MetricNotions.closureWrt euclidDist Z = closure Z := by
  ext x
  rw [Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨y, hy, hxy⟩ := h ε hε
    exact ⟨y, hy, lt_of_le_of_lt (dist_le_euclidDist x y) hxy⟩
  · intro h r hr
    obtain ⟨y, hy, hxy⟩ := h (r / 2) (by positivity)
    exact ⟨y, hy, lt_of_le_of_lt (euclidDist_le_two_dist x y) (by linarith)⟩
private theorem isOpen_of_isOpenWrt {U : Set (Fin 4 → ℝ)}
    (hU : MetricNotions.IsOpenWrt euclidDist U) : IsOpen U := by
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨r, hr, h⟩ := hU x hx
  refine ⟨r / 2, by positivity, fun y hy => h y ?_⟩
  rw [Metric.mem_ball, dist_comm] at hy
  exact lt_of_le_of_lt (euclidDist_le_two_dist x y) (by linarith)
private theorem isCompactWrt_of_isCompact {Z : Set (Fin 4 → ℝ)} (hZ : IsCompact Z) :
    MetricNotions.IsCompactWrt euclidDist Z := by
  intro 𝒰 h𝒰 hcov
  obtain ⟨𝒱, hV, hfin, hc⟩ := hZ.elim_finite_subcover_image (b := 𝒰) (c := fun U => U)
    (fun U hU => isOpen_of_isOpenWrt (h𝒰 U hU))
    (fun x hx => by
      obtain ⟨U, hU, hxU⟩ := hcov hx
      exact Set.mem_biUnion hU hxU)
  refine ⟨𝒱, hV, hfin, fun x hx => ?_⟩
  obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.1 (hc hx)
  exact ⟨U, hU, hxU⟩
private theorem isOpenWrt_ball (c : Fin 4 → ℝ) (r : ℝ) :
    MetricNotions.IsOpenWrt euclidDist (Metric.ball c r) := by
  intro x hx
  rw [Metric.mem_ball] at hx
  refine ⟨r - dist x c, by linarith, fun y hy => ?_⟩
  have h1 := dist_le_euclidDist x y
  have h2 := dist_triangle y x c
  rw [dist_comm y x] at h2
  rw [Metric.mem_ball]
  linarith
private theorem sum_mul_prod_one_sub (B : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, B i * ∏ j ∈ Finset.range i, (1 - B j) =
      1 - ∏ j ∈ Finset.range n, (1 - B j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.prod_range_succ]
    ring
private theorem exists_bump_partition_euclidean {K : Set (Fin 4 → ℝ)}
    (hK : MetricNotions.IsCompactWrt euclidDist K) {η : ℝ} (hη : 0 < η) :
    ∃ (P : ℕ) (_ : 1 ≤ P) (θ : Fin P → (Fin 4 → ℝ) → ℝ),
      (∀ k, ContDiff ℝ ∞ (θ k)) ∧ (∀ k x, θ k x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ k, ∃ c, {x | θ k x ≠ 0} ⊆ Metric.ball c (η / 5)) ∧
      ∀ y ∈ K, ∑ k, θ k y = 1 := by
  let bump : (c : Fin 4 → ℝ) → ContDiffBump c := fun _ =>
    ⟨η / 10, η / 5, by positivity, by linarith⟩
  obtain ⟨𝒰, hsub, hfin, hcov⟩ := hK (Set.range fun c => Metric.ball c (η / 10))
    (by
      rintro _ ⟨c, rfl⟩
      exact isOpenWrt_ball c _)
    (fun x _ => ⟨Metric.ball x (η / 10), ⟨x, rfl⟩, Metric.mem_ball_self (by positivity)⟩)
  obtain ⟨t, -, htfin, htcov⟩ :=
    (Set.exists_subset_image_finite_and (f := fun c : Fin 4 → ℝ => Metric.ball c (η / 10))
      (s := Set.univ) (p := fun 𝒱 => K ⊆ ⋃₀ 𝒱)).1
      ⟨𝒰, by simpa [Set.image_univ] using hsub, hfin, hcov⟩
  let l : List (Fin 4 → ℝ) := 0 :: htfin.toFinset.toList
  let c : ℕ → Fin 4 → ℝ := fun j => l.getD j 0
  let B : ℕ → (Fin 4 → ℝ) → ℝ := fun j x => bump (c j) x
  have hB0 : ∀ j x, 0 ≤ B j x := fun j x => (bump (c j)).nonneg
  have hB1 : ∀ j x, B j x ≤ 1 := fun j x => (bump (c j)).le_one
  have hBs : ∀ j, ContDiff ℝ ∞ (B j) := fun j => (bump (c j)).contDiff
  have hP0 : ∀ (k : ℕ) (x : Fin 4 → ℝ), 0 ≤ ∏ j ∈ Finset.range k, (1 - B j x) := fun k x =>
    Finset.prod_nonneg fun j _ => by linarith [hB1 j x]
  have hP1 : ∀ (k : ℕ) (x : Fin 4 → ℝ), ∏ j ∈ Finset.range k, (1 - B j x) ≤ 1 := fun k x =>
    Finset.prod_le_one (fun j _ => by linarith [hB1 j x]) fun j _ => by linarith [hB0 j x]
  refine ⟨l.length, by simp [l],
    fun k x => B k x * ∏ j ∈ Finset.range k, (1 - B j x), ?_, ?_, ?_, ?_⟩
  · intro k
    exact (hBs k).mul (contDiff_prod fun j _ => contDiff_const.sub (hBs j))
  · intro k x
    exact ⟨mul_nonneg (hB0 k x) (hP0 k x), mul_le_one₀ (hB1 k x) (hP0 k x) (hP1 k x)⟩
  · intro k
    refine ⟨c k, fun x hx => ?_⟩
    have hne : B k x ≠ 0 := left_ne_zero_of_mul hx
    have hsupp : x ∈ Function.support (bump (c k)) := hne
    rw [(bump (c k)).support_eq] at hsupp
    exact hsupp
  · intro y hy
    obtain ⟨_, ⟨a, ha, rfl⟩, hya⟩ := htcov hy
    have hal : a ∈ l := List.mem_cons_of_mem _ (by simpa using ha)
    obtain ⟨i, hi, hia⟩ := List.getElem_of_mem hal
    have hci : c i = a := by
      simp only [c, List.getD_eq_getElem _ _ hi, hia]
    have hBi : B i y = 1 := by
      refine (bump (c i)).one_of_mem_closedBall (Metric.ball_subset_closedBall ?_)
      rw [hci]
      exact hya
    have hprod : ∏ j ∈ Finset.range l.length, (1 - B j y) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 hi) (by rw [hBi]; ring)
    have hsum := sum_mul_prod_one_sub (fun j => B j y) l.length
    rw [hprod, sub_zero] at hsum
    rw [Fin.sum_univ_eq_sum_range (fun k => B k y * ∏ j ∈ Finset.range k, (1 - B j y)) l.length]
    exact hsum
theorem smallScalePartitionsOfUnity_holds (hF : TorusBallCoversAndPartitionsOfUnity)
    (hS : Kind.QuotientCompactC1.Claim)
    (hW : WellPosedness.WellPosed) :
    SmallScalePartitionsOfUnity := by
  intro D E K hK η hη
  cases E with
  | euclidean =>
    have hd : (quotDist D euclidean : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ) = euclidDist :=
      funext₂ fun y y' => (hW D euclidean).2.2.2.2.2.2.2.1 y y'
    have hK' : MetricNotions.IsCompactWrt euclidDist (K : Set (Fin 4 → ℝ)) := by
      have h : MetricNotions.IsCompactWrt (quotDist D euclidean) K := hK
      rw [hd] at h
      exact h
    obtain ⟨P, hP, θ, hsm, hval, hsupp, hsum⟩ := exists_bump_partition_euclidean hK' hη
    have hclosure : ∀ k, supportQ D euclidean (θ k) = closure {x | θ k x ≠ 0} := by
      intro k
      rw [← closureWrt_euclidDist, ← hd]
      rfl
    refine ⟨P, hP, θ, fun k => ⟨hsm k, hval k⟩, fun k => ?_, fun k => ?_, hsum⟩
    · obtain ⟨c, hc⟩ := hsupp k
      have h : IsCompact (closure {x | θ k x ≠ 0}) :=
        (isCompact_closedBall c (η / 5)).of_isClosed_subset isClosed_closure
          (closure_minimal (hc.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall)
      have h' := isCompactWrt_of_isCompact h
      rw [← hclosure k, ← hd] at h'
      exact h'
    · obtain ⟨c, hc⟩ := hsupp k
      have hsub : closure {x | θ k x ≠ 0} ⊆ Metric.closedBall c (η / 5) :=
        closure_minimal (hc.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall
      have hle : setDiam D euclidean (supportQ D euclidean (θ k)) ≤
          ENNReal.ofReal (4 * η / 5) := by
        rw [hclosure k]
        refine iSup₂_le fun (z : Fin 4 → ℝ) hz => iSup₂_le fun (z' : Fin 4 → ℝ) hz' =>
          ENNReal.ofReal_le_ofReal ?_
        have h1 : dist z c ≤ η / 5 := hsub hz
        have h2 : dist z' c ≤ η / 5 := hsub hz'
        have h3 := dist_triangle_right z z' c
        have h4 := euclidDist_le_two_dist z z'
        rw [hd]
        linarith
      exact lt_of_le_of_lt hle ((ENNReal.ofReal_lt_ofReal_iff hη).2 (by linarith))
  | torus =>
    have hr : 0 < η / 3 := by positivity
    obtain ⟨⟨J, hJ, x, hx⟩, hb, hc⟩ := hF D (η / 3) hr
    obtain ⟨A, _, _, χ, hχ⟩ := hb J hJ x hx
    have hM := (hS D torus).1
    refine ⟨Fintype.card A, Fintype.card_pos, fun k => χ ((Fintype.equivFin A).symm k),
      fun k => hχ.mem_unitInterval _, fun k => ?_, fun k => ?_, fun y _ => ?_⟩
    · exact (hc _ (hχ.mem_unitInterval _).1).2.1
    · obtain ⟨j, hj⟩ := hχ.support_subset ((Fintype.equivFin A).symm k)
      have hle : setDiam D torus (supportQ D torus (χ ((Fintype.equivFin A).symm k))) ≤
          ENNReal.ofReal (2 * (η / 3)) := by
        refine iSup₂_le fun z hz => iSup₂_le fun z' hz' => ENNReal.ofReal_le_ofReal ?_
        have h1 : quotDist D torus z (x j) < η / 3 := hj hz
        have h2 : quotDist D torus z' (x j) < η / 3 := hj hz'
        have h3 := hM.2.2.2.1 z (x j) z'
        have h4 := hM.2.2.1 (x j) z'
        linarith
      exact lt_of_le_of_lt hle ((ENNReal.ofReal_lt_ofReal_iff hη).2 (by linarith))
    · rw [← hχ.sum_eq_one y]
      exact Equiv.sum_comp (Fintype.equivFin A).symm fun a => χ a y
end YangMills.Construction.PeriodicSpace.ScalePartitions
