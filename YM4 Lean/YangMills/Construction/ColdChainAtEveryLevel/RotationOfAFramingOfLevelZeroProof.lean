import YangMills.Construction.ColdChainAtEveryLevel.DensityUnderAChangeOfFramingProof
import YangMills.Construction.ColdChainAtEveryLevel.RotationOfAFramingOfLevelZero
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.PinnedGaugeVariation
open GaugeMotions
variable {F : BlockFrame} {j : ℕ}
theorem hasDerivAt_expUnit_smul (w : imaginaryQuaternions) :
    HasDerivAt (fun τ : ℝ => ((expUnit (τ • w) : UnitQuaternion) : ℍ[ℝ])) (w : ℍ[ℝ]) 0 := by apply _root_.YangMills.Construction.GaugedCriticality.hasDerivAt_expUnit_smul <;> assumption
theorem hasDerivAt_quaternion_star {q : ℝ → ℍ[ℝ]} {q' : ℍ[ℝ]} {t : ℝ} (hq : HasDerivAt q q' t) :
    HasDerivAt (fun τ => star (q τ)) (star q') t := by apply _root_.YangMills.Construction.GaugedCriticality.hasDerivAt_quaternion_star <;> assumption
theorem coe_mul_star_coe (g : UnitQuaternion) : (g : ℍ[ℝ]) * star (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.BlockAverages.GaugeChangeDensity.unitQuaternion_mul_star <;> assumption
theorem star_coe_mul_coe (g : UnitQuaternion) : star (g : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := by
  rw [← coe_unitQuaternion_inv, ← Submonoid.coe_mul, inv_mul_cancel]
  rfl
theorem hasDerivAt_polarUnit_inv {C : ℝ → ℍ[ℝ]} {C' : ℍ[ℝ]} (hC : HasDerivAt C C' 0) (hC0 : C 0 ≠ 0) :
    HasDerivAt (fun τ => (((polarUnit (C τ))⁻¹ : UnitQuaternion) : ℍ[ℝ]))
      (((-(1 / ‖C 0‖)) • pureComponent ((((polarUnit (C 0))⁻¹ : UnitQuaternion) : ℍ[ℝ]) * C')) *
        (((polarUnit (C 0))⁻¹ : UnitQuaternion) : ℍ[ℝ])) 0 := by
  set u0 := polarUnit (C 0) with hu0
  set Q : ℝ → ℍ[ℝ] := fun τ => (((polarUnit (C τ))⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hQ
  have hr : 0 < ‖C 0‖ := norm_pos_iff.2 hC0
  have hdiff : DifferentiableAt ℝ Q 0 :=
    ChartCoordinates.differentiableAt_unitQuaternion_inv
      (ChartCoordinates.differentiableAt_polarUnit hC.differentiableAt hC0)
  obtain ⟨Q', hQ'⟩ : ∃ Q', HasDerivAt Q Q' 0 := ⟨_, hdiff.hasDerivAt⟩
  have hρd : DifferentiableAt ℝ (fun τ => ‖C τ‖) 0 := hC.differentiableAt.norm ℝ hC0
  obtain ⟨ρ', hρ⟩ : ∃ ρ', HasDerivAt (fun τ => ‖C τ‖) ρ' 0 := ⟨_, hρd.hasDerivAt⟩
  have hQ0 : Q 0 = star (u0 : ℍ[ℝ]) := rfl
  have hne : ∀ᶠ τ in nhds (0 : ℝ), C τ ≠ 0 := hC.continuousAt.eventually_ne hC0
  have hprod : (fun τ => C τ * Q τ) =ᶠ[nhds 0] fun τ => ‖C τ‖ • (1 : ℍ[ℝ]) := by
    filter_upwards [hne] with τ hτ
    have hn : ‖C τ‖ ≠ 0 := norm_ne_zero_iff.2 hτ
    show C τ * (((polarUnit (C τ))⁻¹ : UnitQuaternion) : ℍ[ℝ]) = _
    rw [coe_unitQuaternion_inv, coe_polarUnit hτ, quaternion_star_real_smul, mul_smul_comm, Quaternion.self_mul_star,
      Quaternion.normSq_eq_norm_mul_self]
    have e : ((‖C τ‖ * ‖C τ‖ : ℝ) : ℍ[ℝ]) = (‖C τ‖ * ‖C τ‖) • (1 : ℍ[ℝ]) := by
      ext <;> simp
    rw [e, smul_smul]
    congr 1
    field_simp
  have hd1 : HasDerivAt (fun τ => C τ * Q τ) (C' * Q 0 + C 0 * Q') 0 := hC.mul hQ'
  have hd2 : HasDerivAt (fun τ => ‖C τ‖ • (1 : ℍ[ℝ])) (ρ' • (1 : ℍ[ℝ])) 0 := hρ.smul_const 1
  have heq : C' * Q 0 + C 0 * Q' = ρ' • (1 : ℍ[ℝ]) := (hd1.congr_of_eventuallyEq hprod.symm).unique hd2
  set r := ‖C 0‖ with hrdef
  have hCr : C 0 = r • (u0 : ℍ[ℝ]) := by
    rw [hu0, coe_polarUnit hC0, smul_smul]
    have : r * ‖C 0‖⁻¹ = 1 := by
      rw [hrdef]
      field_simp
    rw [this, one_smul]
  set m := star (u0 : ℍ[ℝ]) * C' with hm
  set E := Q' * (u0 : ℍ[ℝ]) with hE
  have hsu : star (u0 : ℍ[ℝ]) * (u0 : ℍ[ℝ]) = 1 := star_coe_mul_coe u0
  have hus : (u0 : ℍ[ℝ]) * star (u0 : ℍ[ℝ]) = 1 := coe_mul_star_coe u0
  have hmain : m + r • E = ρ' • (1 : ℍ[ℝ]) := by
    have h1 := congrArg (fun w => star (u0 : ℍ[ℝ]) * w * (u0 : ℍ[ℝ])) heq
    simp only [hQ0, hCr] at h1
    have e1 : star (u0 : ℍ[ℝ]) * (C' * star (u0 : ℍ[ℝ]) + r • (u0 : ℍ[ℝ]) * Q') * (u0 : ℍ[ℝ]) =
        m * (star (u0 : ℍ[ℝ]) * (u0 : ℍ[ℝ])) + r • ((star (u0 : ℍ[ℝ]) * (u0 : ℍ[ℝ])) * (Q' * (u0 : ℍ[ℝ]))) := by
      simp only [hm, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
    have e2 : star (u0 : ℍ[ℝ]) * (ρ' • (1 : ℍ[ℝ])) * (u0 : ℍ[ℝ]) = ρ' • (star (u0 : ℍ[ℝ]) * (u0 : ℍ[ℝ])) := by
      simp only [smul_mul_assoc, mul_smul_comm, mul_one]
    rw [e1, e2, hsu, one_mul, mul_one] at h1
    exact h1
  have hstar : E + star E = 0 := by
    have hc : HasDerivAt (fun τ => Q τ * star (Q τ)) (Q' * star (Q 0) + Q 0 * star Q') 0 :=
      hQ'.mul (hasDerivAt_quaternion_star hQ')
    have e1 : (fun τ => Q τ * star (Q τ)) = fun _ => (1 : ℍ[ℝ]) := by
      funext τ
      exact coe_mul_star_coe _
    rw [e1] at hc
    have h2 := hc.unique (hasDerivAt_const _ _)
    rw [hQ0, star_star] at h2
    have e2 : star E = star (u0 : ℍ[ℝ]) * star Q' := by rw [hE, star_mul]
    rw [e2]
    exact h2
  have hpure : pureComponent E = E := by
    unfold pureComponent
    have e : star E = - E := by
      have := eq_neg_of_add_eq_zero_right hstar
      exact this
    rw [e, sub_neg_eq_add, ← two_smul ℝ E, smul_smul]
    norm_num
  have hEval : E = (-(1 / r)) • pureComponent m := by
    have e1 : r • E = ρ' • (1 : ℍ[ℝ]) - m := by rw [← hmain]; abel
    have e2 := congrArg pureComponent e1
    rw [pureComponent_smul, hpure, pureComponent_sub, pureComponent_smul, pureComponent_one, smul_zero, zero_sub] at e2
    have hr0 : r ≠ 0 := hr.ne'
    calc E = (1 / r) • (r • E) := by rw [smul_smul]; field_simp; simp
      _ = _ := by rw [e2, smul_neg, neg_smul]
  have hQval : Q' = E * star (u0 : ℍ[ℝ]) := by
    rw [hE, mul_assoc, hus, mul_one]
  rw [hQval, hEval] at hQ'
  have e3 : (((polarUnit (C 0))⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (u0 : ℍ[ℝ]) := rfl
  rw [e3]
  exact hQ'
theorem hasDerivAt_gaugedPathAverage {Γτ : ℝ → F.Site j → UnitQuaternion} (X R : F.GaugeField j)
    {f : F.Site j → ℍ[ℝ]} {y : F.Site (j + 1)}
    (hd : ∀ h ∈ centredCube F.blockSide,
      HasDerivAt (fun τ => ((Γτ τ (refineSite y + siteOfCoords j h) : UnitQuaternion) : ℍ[ℝ]))
        (f (refineSite y + siteOfCoords j h) * ((Γτ 0 (refineSite y + siteOfCoords j h) : UnitQuaternion) : ℍ[ℝ])) 0)
    (hf : ∀ h ∈ centredCube F.blockSide, (f (refineSite y + siteOfCoords j h)).re = 0) :
    HasDerivAt (fun τ => gaugedPathAverage (Γτ τ) X R y) (- pathAveragedGenerator (Γτ 0) X R f y) 0 := by
  unfold gaugedPathAverage pathAveragedGenerator
  rw [← smul_neg, ← Finset.sum_neg_distrib]
  refine HasDerivAt.const_smul (1 / (24 * (F.blockSide : ℝ) ^ 4) : ℝ) ?_
  refine HasDerivAt.fun_sum fun h hh => ?_
  rw [← Finset.sum_neg_distrib]
  refine HasDerivAt.fun_sum fun π _ => ?_
  have e : (fun τ => ((pathHolonomy X (refineSite y) (axisPath h π) * (Γτ τ (refineSite y + siteOfCoords j h))⁻¹ *
      (pathHolonomy R (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ])) = fun τ =>
      ((pathHolonomy X (refineSite y) (axisPath h π) : UnitQuaternion) : ℍ[ℝ]) *
        star ((Γτ τ (refineSite y + siteOfCoords j h) : UnitQuaternion) : ℍ[ℝ]) *
        (((pathHolonomy R (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    funext τ
    simp only [Submonoid.coe_mul, coe_unitQuaternion_inv]
  rw [e]
  have h1 := ((hasDerivAt_quaternion_star (hd h hh)).const_mul
    ((pathHolonomy X (refineSite y) (axisPath h π) : UnitQuaternion) : ℍ[ℝ])).mul_const
    (((pathHolonomy R (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ])
  refine h1.congr_deriv ?_
  rw [star_mul, star_eq_neg_of_re_eq_zero (hf h hh)]
  simp only [Submonoid.coe_mul, coe_unitQuaternion_inv, mul_neg, neg_mul, mul_assoc]
theorem coarseGenerator_re_and_hasDerivAt {Γτ : ℝ → F.Site j → UnitQuaternion} (X R : F.GaugeField j)
    (f : F.Site j → ℍ[ℝ]) (y : F.Site (j + 1)) (κ κ' : UnitQuaternion)
    (hd : ∀ h ∈ centredCube F.blockSide,
      HasDerivAt (fun τ => ((Γτ τ (refineSite y + siteOfCoords j h) : UnitQuaternion) : ℍ[ℝ]))
        (f (refineSite y + siteOfCoords j h) * ((Γτ 0 (refineSite y + siteOfCoords j h) : UnitQuaternion) : ℍ[ℝ])) 0)
    (hf : ∀ h ∈ centredCube F.blockSide, (f (refineSite y + siteOfCoords j h)).re = 0)
    (hne : gaugedPathAverage (Γτ 0) X R y ≠ 0) :
    (∀ᶠ τ in nhds (0 : ℝ), gaugedPathAverage (Γτ τ) X R y ≠ 0) ∧
    (coarseGenerator (Γτ 0) X R κ f y).re = 0 ∧
    HasDerivAt (fun τ => ((κ * (polarUnit (gaugedPathAverage (Γτ τ) X R y))⁻¹ * κ' : UnitQuaternion) : ℍ[ℝ]))
      (coarseGenerator (Γτ 0) X R κ f y *
        ((κ * (polarUnit (gaugedPathAverage (Γτ 0) X R y))⁻¹ * κ' : UnitQuaternion) : ℍ[ℝ])) 0 := by
  have hp := hasDerivAt_gaugedPathAverage X R hd hf
  refine ⟨hp.continuousAt.eventually_ne hne, ?_, ?_⟩
  · unfold coarseGenerator adjointAction
    rw [Quaternion.re_smul]
    have h1 : ((κ : ℍ[ℝ]) * pureComponent ((((polarUnit (gaugedPathAverage (Γτ 0) X R y))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
        pathAveragedGenerator (Γτ 0) X R f y) * ((κ⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = 0 := by
      have := pureComponent_adjointAction κ
        ((((polarUnit (gaugedPathAverage (Γτ 0) X R y))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          pathAveragedGenerator (Γτ 0) X R f y)
      have h2 := re_pureComponent (adjointAction κ
        ((((polarUnit (gaugedPathAverage (Γτ 0) X R y))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          pathAveragedGenerator (Γτ 0) X R f y))
      rw [this] at h2
      exact h2
    rw [h1, smul_zero]
  · have hu := hasDerivAt_polarUnit_inv hp hne
    set u0 := polarUnit (gaugedPathAverage (Γτ 0) X R y) with hu0
    set r := ‖gaugedPathAverage (Γτ 0) X R y‖ with hr
    set p := pureComponent (((u0⁻¹ : UnitQuaternion) : ℍ[ℝ]) * pathAveragedGenerator (Γτ 0) X R f y) with hpdef
    have e : (fun τ => ((κ * (polarUnit (gaugedPathAverage (Γτ τ) X R y))⁻¹ * κ' : UnitQuaternion) : ℍ[ℝ])) =
        fun τ => (κ : ℍ[ℝ]) * (((polarUnit (gaugedPathAverage (Γτ τ) X R y))⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          (κ' : ℍ[ℝ]) := by
      funext τ
      simp only [Submonoid.coe_mul]
    rw [e]
    refine ((hu.const_mul (κ : ℍ[ℝ])).mul_const (κ' : ℍ[ℝ])).congr_deriv ?_
    have e2 : pureComponent (((u0⁻¹ : UnitQuaternion) : ℍ[ℝ]) * - pathAveragedGenerator (Γτ 0) X R f y) = - p := by
      rw [mul_neg, hpdef]
      simp only [pureComponent, star_neg, smul_sub, smul_neg]
      abel
    rw [e2]
    have hk : ((κ⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (κ : ℍ[ℝ]) = 1 := by
      rw [← Submonoid.coe_mul, inv_mul_cancel]
      rfl
    show _ = ((1 / r) • adjointAction κ p) * _
    simp only [adjointAction, Submonoid.coe_mul, smul_mul_assoc, mul_smul_comm, smul_neg, neg_smul,
      neg_neg]
    congr 1
    calc (κ : ℍ[ℝ]) * (p * ((u0⁻¹ : UnitQuaternion) : ℍ[ℝ])) * (κ' : ℍ[ℝ]) =
        (κ : ℍ[ℝ]) * p * (((κ⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (κ : ℍ[ℝ])) * ((u0⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          (κ' : ℍ[ℝ]) := by
          rw [hk, mul_one]
          simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
theorem rotatedBaseGauge_zero (ξ : F.Site 0 → imaginaryQuaternions) (γ : F.Site 0 → UnitQuaternion) :
    rotatedBaseGauge ξ 0 γ = γ := by
  funext x
  have e : expUnit (0 : imaginaryQuaternions) = 1 := by
    apply Subtype.ext
    simp [expUnit, NormedSpace.exp_zero]
  simp [rotatedBaseGauge, e]
theorem pinnedGaugeVariationStatement_holds : pinnedGaugeVariationStatement := by
  intro F W kW X k γ ξ D hodd hne
  set gen := pinnedGaugeGenerator W kW X k γ (fun x => (ξ x : ℍ[ℝ])) with hgen
  have key : ∀ j, j < F.top → (∀ h : LatticeFractionalIntegration.Lattice4, True) →
      ∀ (y : F.Site (j + 1)) (κ κ' : UnitQuaternion), y ∈ sitesOfCells D (j + 1) →
      (∀ x ∈ sitesOfCells D j, (gen j x).re = 0 ∧
        HasDerivAt (fun τ : ℝ =>
            ((pinnedGaugeLevel W kW X k (rotatedBaseGauge ξ τ γ) j x : UnitQuaternion) : ℍ[ℝ]))
          (gen j x * ((pinnedGaugeLevel W kW X k γ j x : UnitQuaternion) : ℍ[ℝ])) 0) →
      (coarseGenerator (pinnedGaugeLevel W kW X k γ j) (X j) (W j) κ (gen j) y).re = 0 ∧
      HasDerivAt (fun τ : ℝ => ((κ * balancingGauge
            (gaugeTransform (pinnedGaugeLevel W kW X k (rotatedBaseGauge ξ τ γ) j) (X j)) (W j) y *
          pinnedGaugeLevel W kW X k (rotatedBaseGauge ξ τ γ) j (refineSite y) * κ' : UnitQuaternion) : ℍ[ℝ]))
        (coarseGenerator (pinnedGaugeLevel W kW X k γ j) (X j) (W j) κ (gen j) y *
          ((κ * balancingGauge (gaugeTransform (pinnedGaugeLevel W kW X k γ j) (X j)) (W j) y *
            pinnedGaugeLevel W kW X k γ j (refineSite y) * κ' : UnitQuaternion) : ℍ[ℝ])) 0 := by
    intro j hj _ y κ κ' hy ih
    have hb : ∀ h ∈ centredCube F.blockSide, refineSite y + siteOfCoords j h ∈ sitesOfCells D j := fun h hh =>
      ChartCoordinates.refineSite_add_mem_sitesOfCells hodd hj hy hh
    set Γτ : ℝ → F.Site j → UnitQuaternion := fun τ => pinnedGaugeLevel W kW X k (rotatedBaseGauge ξ τ γ) j
      with hΓτ
    have h0 : Γτ 0 = pinnedGaugeLevel W kW X k γ j := by
      simp only [hΓτ, rotatedBaseGauge_zero]
    have hp : gaugedPathAverage (Γτ 0) (X j) (W j) y ≠ 0 := by
      rw [h0]
      exact gaugedPathAverage_ne_zero (hne j hj y hy)
    have hd : ∀ h ∈ centredCube F.blockSide,
        HasDerivAt (fun τ => ((Γτ τ (refineSite y + siteOfCoords j h) : UnitQuaternion) : ℍ[ℝ]))
          (gen j (refineSite y + siteOfCoords j h) *
            ((Γτ 0 (refineSite y + siteOfCoords j h) : UnitQuaternion) : ℍ[ℝ])) 0 := by
      intro h hh
      rw [h0]
      exact (ih _ (hb h hh)).2
    have hf : ∀ h ∈ centredCube F.blockSide, (gen j (refineSite y + siteOfCoords j h)).re = 0 :=
      fun h hh => (ih _ (hb h hh)).1
    obtain ⟨hev, hre, hder⟩ := coarseGenerator_re_and_hasDerivAt (X j) (W j) (gen j) y κ κ' hd hf hp
    rw [h0] at hre hder hp
    refine ⟨hre, ?_⟩
    rw [balancingGauge_mul_eq _ _ _ κ κ' y hp]
    refine hder.congr_of_eventuallyEq ?_
    filter_upwards [hev] with τ hτ
    rw [balancingGauge_mul_eq _ _ _ κ κ' y hτ]
  have level : ∀ j, j < F.top → ∀ y ∈ sitesOfCells D j, (gen j y).re = 0 ∧
      HasDerivAt (fun τ : ℝ =>
          ((pinnedGaugeLevel W kW X k (rotatedBaseGauge ξ τ γ) j y : UnitQuaternion) : ℍ[ℝ]))
        (gen j y * ((pinnedGaugeLevel W kW X k γ j y : UnitQuaternion) : ℍ[ℝ])) 0 := by
    intro j
    induction j with
    | zero =>
      intro _ y _
      refine ⟨(ξ y).2, ?_⟩
      have e : (fun τ : ℝ =>
          ((pinnedGaugeLevel W kW X k (rotatedBaseGauge ξ τ γ) 0 y : UnitQuaternion) : ℍ[ℝ])) = fun τ : ℝ =>
          ((expUnit (τ • ξ y) : UnitQuaternion) : ℍ[ℝ]) * (γ y : ℍ[ℝ]) := by
        funext τ
        rfl
      rw [e]
      exact (hasDerivAt_expUnit_smul (ξ y)).mul_const _
    | succ j ih =>
      intro hj y hy
      have hj' : j < F.top := by omega
      have h1 := key j hj' (fun _ => trivial) y (kW (j + 1) y) (k (j + 1) y)⁻¹ hy (ih hj')
      have e1 : ∀ γ' : F.Site 0 → UnitQuaternion, pinnedGaugeLevel W kW X k γ' (j + 1) y = kW (j + 1) y *
          balancingGauge (gaugeTransform (pinnedGaugeLevel W kW X k γ' j) (X j)) (W j) y *
            pinnedGaugeLevel W kW X k γ' j (refineSite y) * (k (j + 1) y)⁻¹ := fun γ' => if_pos hj
      refine ⟨h1.1, ?_⟩
      simp only [e1]
      exact h1.2
  refine ⟨level, fun y hy => ?_⟩
  have h1 := key F.depth (Nat.lt_succ_self _) (fun _ => trivial) y (kW F.top y) (k F.top y)⁻¹ hy
    (level F.depth (Nat.lt_succ_self _))
  refine ⟨h1.1, ?_⟩
  simp only [topCorrection_eq]
  exact h1.2
end YangMills.Construction.BlockAverages.PinnedGaugeVariation
end
