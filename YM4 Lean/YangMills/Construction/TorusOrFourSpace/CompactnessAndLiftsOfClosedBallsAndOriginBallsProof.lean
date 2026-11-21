import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNormProof
import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.PassageToTheLimit.PartitionOfUnityOfClassC1WithSmallPiecesProof
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.TorusOrFourSpace.CompactnessAndLiftsOfClosedBallsAndOriginBalls
import YangMills.Construction.TorusOrFourSpace.QuotientMapCompactSetsAndFunctionsOfClassC1
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefined
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open TorusMetric (euclidNormVec)
open MetricNotions (IsOpenWrt IsCompactWrt)
namespace PeriodicSpace.BallCompactness
open Kind
open Kind.QuotientCompactC1 (QuotDistIsMetricWithLifts)
private theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem norm_le_euclidNormVec (v : Fin 4 → ℝ) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
private theorem euclidNormVec_le_two_mul {v : Fin 4 → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ μ, |v μ| ≤ c) : euclidNormVec v ≤ 2 * c := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.euclidNormVec_le <;> assumption
private theorem euclidNormVec_sub_comm (a b : Fin 4 → ℝ) :
    euclidNormVec (a - b) = euclidNormVec (b - a) := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_sub_comm <;> assumption
private theorem euclidNormVec_zero_sub (a : Fin 4 → ℝ) :
    euclidNormVec (0 - a) = euclidNormVec a := by
  simp [euclidNormVec]
private theorem euclidNormVec_sub_zero (a : Fin 4 → ℝ) :
    euclidNormVec (a - 0) = euclidNormVec a := by
  simp
private theorem le_euclidNormVec_of_mem_lattice {ℓ : ℝ} (hℓ : 0 < ℓ) {k : Fin 4 → ℝ}
    (hk : k ∈ InfiniteLattice.latticeSubgroup ℓ) (hne : k ≠ 0) : ℓ ≤ euclidNormVec k := by
  obtain ⟨n, hn⟩ := hk
  obtain ⟨μ, hμ⟩ : ∃ μ, n μ ≠ 0 := by
    by_contra hall
    have hzero : ∀ μ, n μ = 0 := fun μ => by_contra fun h => hall ⟨μ, h⟩
    exact hne (funext fun μ => by simp [hn μ, hzero μ])
  refine le_trans ?_ (abs_apply_le_euclidNormVec k μ)
  have hone : (1 : ℝ) ≤ |(n μ : ℝ)| := by
    have : (1 : ℤ) ≤ |n μ| := Int.one_le_abs hμ
    exact_mod_cast this
  rw [hn μ, abs_mul, abs_of_pos hℓ]
  nlinarith
private theorem isCompactWrt_of_subset {X : Type*} {d : X → X → ℝ} {K Z : Set X}
    (hK : IsCompactWrt d K) (hZ : IsOpenWrt d Zᶜ) (hsub : Z ⊆ K) : IsCompactWrt d Z := by apply _root_.YangMills.DeltaSharedProofs.p500420 <;> assumption
private theorem isOpen_of_isOpenWrt {d : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ}
    (hd : ∀ y y', d y y' = euclidNormVec (y - y')) {U : Set (Fin 4 → ℝ)}
    (hU : IsOpenWrt d U) : IsOpen U := by
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨r, hr, h⟩ := hU x hx
  refine ⟨r / 4, by positivity, fun y hy => h y ?_⟩
  rw [hd]
  have hxy : ‖x - y‖ < r / 4 := by
    rw [← dist_eq_norm, dist_comm]
    exact hy
  have hle := euclidNormVec_le_two_mul (v := x - y) (norm_nonneg (x - y)) fun μ => by
    have := norm_le_pi_norm (x - y) μ
    rwa [Real.norm_eq_abs] at this
  linarith
private theorem isCompactWrt_closedBall_euclid {d : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ}
    (hd : ∀ y y', d y y' = euclidNormVec (y - y')) (x : Fin 4 → ℝ) (R : ℝ) :
    IsCompactWrt d {y | d y x ≤ R} := by
  have hcl : IsClosed {y | d y x ≤ R} := by
    simp only [hd]
    refine isClosed_le ?_ continuous_const
    unfold euclidNormVec
    fun_prop
  have hbd : Bornology.IsBounded {y | d y x ≤ R} := by
    refine (Metric.isBounded_iff_subset_closedBall x).2 ⟨R, fun y hy => ?_⟩
    have hy' : d y x ≤ R := hy
    rw [hd] at hy'
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (norm_le_euclidNormVec _).trans hy'
  have hK : IsCompact {y | d y x ≤ R} := Metric.isCompact_of_isClosed_isBounded hcl hbd
  intro 𝒰 hU hcov
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun u : 𝒰 => (u : Set (Fin 4 → ℝ)))
    (fun u => isOpen_of_isOpenWrt hd (hU u u.2)) (by
      intro z hz
      obtain ⟨u, hu, hzu⟩ := hcov hz
      exact Set.mem_iUnion.2 ⟨⟨u, hu⟩, hzu⟩)
  refine ⟨Subtype.val '' (t : Set 𝒰), ?_, t.finite_toSet.image _, ?_⟩
  · rintro _ ⟨u, _, rfl⟩
    exact u.2
  · intro z hz
    obtain ⟨u, hu, hzu⟩ := Set.mem_iUnion₂.1 (ht hz)
    exact ⟨u, ⟨u, hu, rfl⟩, hzu⟩
variable (D : Params)
private theorem side_pos : 0 < D.side := by
  have hL : (0 : ℝ) < (D.L : ℝ) := by
    have h := D.isAdmissible.2
    exact_mod_cast (by omega : 0 < D.L)
  unfold Params.side PeriodicLattice.torusSide
  positivity
abbrev _root_.YangMills.SharedProofs.p25685 := @side_pos
variable {D} {E : Kind}
private theorem isOpenWrt_compl_closedBall (hM : QuotDistIsMetricWithLifts D E) (x : E.Pt D)
    (R : ℝ) : IsOpenWrt (quotDist D E) (closedBallAbout D E x R)ᶜ := by
  intro z hz
  have hz' : R < quotDist D E z x := not_le.1 hz
  refine ⟨quotDist D E z x - R, sub_pos.2 hz', ?_⟩
  intro y hy hyb
  have htri := hM.2.2.2.1 z y x
  have hyb' : quotDist D E y x ≤ R := hyb
  linarith
private theorem isOpenWrt_ball (hM : QuotDistIsMetricWithLifts D E) (o : E.Pt D) (r : ℝ) :
    IsOpenWrt (quotDist D E) {y | quotDist D E y o < r} := by
  intro x hx
  have hx' : quotDist D E x o < r := hx
  refine ⟨r - quotDist D E x o, sub_pos.2 hx', ?_⟩
  intro y hy
  have htri := hM.2.2.2.1 y x o
  have hsymm := hM.2.2.1 y x
  show quotDist D E y o < r
  linarith
abbrev _root_.YangMills.DeltaSharedProofs.p501249 := @isOpenWrt_ball
private theorem subset_centredBall_of_isCompactQ (hM : QuotDistIsMetricWithLifts D E)
    {S : Set (E.Pt D)} (hS : IsCompactQ D E S) :
    ∃ ρ : ℝ≥0∞, 0 < ρ ∧ ρ < ∞ ∧ S ⊆ centredBall D E ρ := by
  let B : ℕ → Set (E.Pt D) := fun n => {y | quotDist D E y (origin D E) < (n : ℝ) + 1}
  have hopen : ∀ U ∈ Set.range B, IsOpenWrt (quotDist D E) U := by
    rintro _ ⟨n, rfl⟩
    exact isOpenWrt_ball hM _ _
  have hcov : S ⊆ ⋃₀ Set.range B := by
    intro y _
    obtain ⟨n, hn⟩ := exists_nat_gt (quotDist D E y (origin D E))
    refine ⟨B n, ⟨n, rfl⟩, ?_⟩
    show quotDist D E y (origin D E) < (n : ℝ) + 1
    linarith
  obtain ⟨𝒱, hV, hfin, hSV⟩ := hS _ hopen hcov
  have hex : ∀ U ∈ 𝒱, ∃ n, B n = U := fun U hU => hV hU
  choose! f hf using hex
  obtain ⟨N, hN⟩ := (hfin.image f).bddAbove
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  refine ⟨ENNReal.ofReal ((N : ℝ) + 1), ENNReal.ofReal_pos.2 hpos, ENNReal.ofReal_lt_top, ?_⟩
  intro z hz
  obtain ⟨U, hU, hzU⟩ := hSV hz
  rw [centredBall, if_neg ENNReal.ofReal_ne_top]
  show quotDist D E z (origin D E) < (ENNReal.ofReal ((N : ℝ) + 1)).toReal
  rw [ENNReal.toReal_ofReal hpos.le]
  rw [← hf U hU] at hzU
  have hlt : quotDist D E z (origin D E) < (f U : ℝ) + 1 := hzU
  have hfN : f U ≤ N := hN ⟨U, hU, rfl⟩
  have hfN' : (f U : ℝ) ≤ N := by exact_mod_cast hfN
  linarith
private theorem exists_lift_mem_cube
    (hLift : WellPosedness.ExistsLiftOfEachPoint D torus)
    (hDiff : WellPosedness.SameLiftIffSubPeriod D torus)
    (y : Pt D torus) :
    ∃ x : Fin 4 → ℝ, IsLift D torus y x ∧
      ∀ μ, x μ ∈ Set.Icc (-(D.side / 2)) (D.side / 2) := by
  have hℓ := side_pos D
  obtain ⟨x, hx⟩ := hLift y
  let j : Fin 4 → ℤ := fun μ => round (x μ / D.side)
  let k : Fin 4 → ℝ := fun μ => (j μ : ℝ) * D.side
  have hk : k ∈ periodGroup D torus := ⟨j, fun μ => rfl⟩
  refine ⟨x - k, ?_, fun μ => ?_⟩
  · have hmem : x - (x - k) ∈ periodGroup D torus := by simpa using hk
    obtain ⟨y', hy1, hy2⟩ := (hDiff x (x - k)).2 hmem
    have hyy : y' = y := hy1.symm.trans hx
    rw [← hyy]
    exact hy2
  · have hr : |x μ / D.side - (j μ : ℝ)| ≤ 1 / 2 := abs_sub_round _
    have heq : x μ - (j μ : ℝ) * D.side = (x μ / D.side - (j μ : ℝ)) * D.side := by
      field_simp
    have habs : |x μ - (j μ : ℝ) * D.side| ≤ D.side / 2 := by
      rw [heq, abs_mul, abs_of_pos hℓ]
      nlinarith
    have hboth := abs_le.1 habs
    exact ⟨hboth.1, hboth.2⟩
private theorem euclidNormVec_le_side_of_mem_cube {v : Fin 4 → ℝ}
    (hv : ∀ μ, v μ ∈ Set.Icc (-(D.side / 2)) (D.side / 2)) : euclidNormVec v ≤ D.side := by
  have hℓ := side_pos D
  have h := euclidNormVec_le_two_mul (v := v) (c := D.side / 2) (by positivity) fun μ =>
    abs_le.2 ⟨(hv μ).1, (hv μ).2⟩
  linarith
private theorem quotDist_torus_le_side
    (hM : QuotDistIsMetricWithLifts D torus)
    (hHom : WellPosedness.QuotMapSurjectiveHomWithKernel D torus)
    (hLift : WellPosedness.ExistsLiftOfEachPoint D torus)
    (hDiff : WellPosedness.SameLiftIffSubPeriod D torus)
    (y x : Pt D torus) : quotDist D torus y x ≤ D.side := by
  obtain ⟨v, hv, hcube⟩ := exists_lift_mem_cube hLift hDiff (y - x)
  obtain ⟨xt, hxt⟩ := hLift x
  have hq : quotMap D torus (xt + v) = y := by
    rw [hHom.1, hxt, hv]
    exact add_sub_cancel x y
  have hle := hM.2.2.2.2.1 (xt + v) xt
  rw [hq, hxt] at hle
  have hsub : xt + v - xt = v := by simp
  rw [hsub] at hle
  exact hle.trans (euclidNormVec_le_side_of_mem_cube hcube)
theorem ballCompactnessAndTorusLifts_holds (hW : WellPosedness.WellPosed)
    (hQ : Kind.QuotientCompactC1.Claim) : BallCompactnessAndTorusLifts := by
  intro D
  obtain ⟨hHom, hLift, hDiff, -, -, -, hLeast, hEuc, hTor, -⟩ := hW D torus
  have hMt := (hQ D torus).1
  have hMe := (hQ D euclidean).1
  have hTc := (hQ D torus).2.2.1
  have hℓ := side_pos D
  have tri : ∀ a b c : Fin 4 → ℝ,
      euclidNormVec (a - c) ≤ euclidNormVec (a - b) + euclidNormVec (b - c) := by
    intro a b c
    have h := hMe.2.2.2.1 a b c
    rwa [hEuc, hEuc, hEuc] at h
  refine ⟨?_, ?_, ?_, exists_lift_mem_cube hLift hDiff,
    fun v hv => euclidNormVec_le_side_of_mem_cube hv, ?_, ?_, ?_⟩
  · intro E x R _
    cases E with
    | euclidean => exact isCompactWrt_closedBall_euclid hEuc x R
    | torus =>
      exact isCompactWrt_of_subset hTc (isOpenWrt_compl_closedBall hMt x R)
        (Set.subset_univ _)
  · intro x
    refine ⟨fun R _ _ => ?_, fun R hR => ?_⟩
    · ext y
      have h := (hTor y x).1
      constructor
      · intro hy
        show TorusMetric.torusEuclidNorm (y - x) ≤ R
        exact h.symm.le.trans hy
      · intro hy
        show quotDist D torus y x ≤ R
        exact h.le.trans hy
    · exact Set.eq_univ_of_forall fun y =>
        (quotDist_torus_le_side hMt hHom hLift hDiff y x).trans hR
  · intro ρ _ hρ
    rw [centredBall, if_neg hρ.ne]
    ext y
    constructor
    · intro hy
      have hy' : quotDist D torus y (origin D torus) < ρ.toReal := hy
      obtain ⟨x, hx, hd⟩ := hMt.2.2.2.2.2 (origin D torus) y 0 rfl
      refine ⟨x, ?_, hx⟩
      show euclidNormVec x < ρ.toReal
      rw [euclidNormVec_zero_sub] at hd
      rw [hd, hMt.2.2.1]
      exact hy'
    · rintro ⟨x, hx, rfl⟩
      have hx' : euclidNormVec x < ρ.toReal := hx
      have h := hMt.2.2.2.2.1 x 0
      rw [euclidNormVec_sub_zero] at h
      exact lt_of_le_of_lt h hx'
  · intro ρ hρ
    by_cases hinf : ρ = ∞
    · rw [centredBall, if_pos hinf]
    · rw [centredBall, if_neg hinf]
      refine Set.eq_univ_of_forall fun y => ?_
      have hle := quotDist_torus_le_side hMt hHom hLift hDiff y (origin D torus)
      have hlt := (ENNReal.ofReal_lt_iff_lt_toReal hℓ.le hinf).1 hρ
      exact lt_of_le_of_lt hle hlt
  · intro E S hS
    exact subset_centredBall_of_isCompactQ (hQ D E).1 hS
  · intro x R xl hR hRl hxl
    have hd2 : 2 * R < D.side / 2 := by linarith
    refine ⟨?_, hd2, ?_, ?_⟩
    · unfold setDiam
      refine iSup_le fun y => iSup_le fun hy => iSup_le fun y' => iSup_le fun hy' =>
        ENNReal.ofReal_le_ofReal ?_
      have htri := hMt.2.2.2.1 y x y'
      have hsymm := hMt.2.2.1 x y'
      have hy1 : quotDist D torus y x ≤ R := hy
      have hy2 : quotDist D torus y' x ≤ R := hy'
      linarith
    · ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hz' : euclidNormVec (z - xl) ≤ R := hz
        have h := hMt.2.2.2.2.1 z xl
        have hq : quotMap D torus xl = x := hxl
        rw [hq] at h
        exact h.trans hz'
      · intro hy
        have hy' : quotDist D torus y x ≤ R := hy
        obtain ⟨z, hz, hd⟩ := hMt.2.2.2.2.2 x y xl hxl
        refine ⟨z, ?_, hz⟩
        show euclidNormVec (z - xl) ≤ R
        rw [euclidNormVec_sub_comm, hd, hMt.2.2.1]
        exact hy'
    · intro z hz z' hz'
      have hz1 : euclidNormVec (z - xl) ≤ R := hz
      have hz2 : euclidNormVec (z' - xl) ≤ R := hz'
      have hle := hMt.2.2.2.2.1 z z'
      obtain ⟨⟨k, hk, hkeq⟩, -⟩ := hLeast z z'
      refine le_antisymm hle ?_
      rw [hkeq]
      have hzz : euclidNormVec (z - z') ≤ 2 * R := by
        have h1 := tri z xl z'
        have h2 := euclidNormVec_sub_comm xl z'
        linarith
      by_cases hk0 : k = 0
      · subst hk0
        simp
      · have h1 := le_euclidNormVec_of_mem_lattice hℓ hk hk0
        have h2 := tri k (z - z') 0
        rw [euclidNormVec_sub_zero, euclidNormVec_sub_zero, euclidNormVec_sub_comm k] at h2
        linarith
end PeriodicSpace.BallCompactness
end YangMills.Construction
