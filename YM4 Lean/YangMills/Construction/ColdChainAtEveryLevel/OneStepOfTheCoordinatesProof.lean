import YangMills.Construction.ColdChainAtEveryLevel.FactsOfTheLogarithm
import YangMills.Construction.ColdChainAtEveryLevel.OneStepOfTheCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.RotationOfABondAtEveryLevel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace CoordinateStep
theorem norm_unitQuaternionLog_exp_mul_conj_sub_le {mu : imaginaryQuaternions} {m E : UnitQuaternion}
    {Q : ℍ[ℝ]} (hQ : Q.re = 0) {Δ κ : ℝ}
    (hν : ‖unitQuaternionLog E - Q‖ ≤ Δ) (hνκ : ‖unitQuaternionLog E‖ ≤ κ) (hQκ : ‖Q‖ ≤ κ)
    (hsmall : 3 * ‖(mu : ℍ[ℝ])‖ + 3 * κ ≤ 1 / 2) :
    ‖unitQuaternionLog (expUnit mu * (m * E * m⁻¹)) - (mu : ℍ[ℝ]) - Q‖ ≤
      2 * (Δ + 2 * κ ^ 2 + (2 * ‖((m : UnitQuaternion) : ℍ[ℝ]) - 1‖ + 3 * ‖(mu : ℍ[ℝ])‖) * κ) := by
  have hmu : (mu : ℍ[ℝ]).re = 0 := mu.2
  set μ := ‖(mu : ℍ[ℝ])‖ with hμ
  have hμ0 : 0 ≤ μ := norm_nonneg _
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans hQκ
  set h : UnitQuaternion := m * E * m⁻¹ with hh
  set g : UnitQuaternion := expUnit mu * h with hg
  have hE1 : ‖(E : ℍ[ℝ]) - 1‖ ≤ κ := (norm_coe_sub_one_le_norm_unitQuaternionLog E).trans hνκ
  have hh1 : ‖(h : ℍ[ℝ]) - 1‖ ≤ κ := by rw [hh, norm_coe_conj_sub_one]; exact hE1
  have hexp : ((expUnit mu : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (mu : ℍ[ℝ]) := rfl
  have hm1 : ‖((expUnit mu : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ μ := by
    rw [hexp]; exact norm_exp_sub_one_le hmu
  have hg1 : ‖(g : ℍ[ℝ]) - 1‖ ≤ μ + κ := (norm_coe_mul_sub_one_le _ _).trans (add_le_add hm1 hh1)
  have hlog : ‖unitQuaternionLog g‖ ≤ 2 * (μ + κ) :=
    (norm_unitQuaternionLog_le_two_mul g).trans (by linarith)
  set y : ℍ[ℝ] := (mu : ℍ[ℝ]) + Q with hy
  have hyre : y.re = 0 := by simp [hy, hmu, hQ]
  have hyn : ‖y‖ ≤ μ + κ := (norm_add_le _ _).trans (by linarith)
  have h1 := norm_sub_le_two_mul_pureComponent_exp (re_unitQuaternionLog g) hyre (by linarith)
  rw [exp_unitQuaternionLog] at h1
  have e1 : unitQuaternionLog g - (mu : ℍ[ℝ]) - Q = unitQuaternionLog g - y := by rw [hy]; abel
  rw [e1]
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have e2 := pureComponent_coe_mul (expUnit mu) h
  have e3 : pureComponent ((m * E * m⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      adjointAction m (pureComponent (E : ℍ[ℝ])) := by
    rw [coe_conj_eq_adjointAction, pureComponent_adjointAction]
  have hyle : ‖y‖ ≤ 1 := by linarith
  have hμle : μ ≤ 1 := by linarith
  have e4 := norm_pureComponent_exp_sub_sub_le hyre hmu hyle hμle
  have hQy : y - (mu : ℍ[ℝ]) = Q := by rw [hy]; abel
  rw [hQy] at e4
  have hpE : ‖pureComponent (E : ℍ[ℝ]) - unitQuaternionLog E‖ ≤ κ ^ 2 := by
    have := norm_pureComponent_exp_sub_self_le (re_unitQuaternionLog E) (by linarith)
    rw [exp_unitQuaternionLog] at this
    exact this.trans (pow_le_pow_left₀ (norm_nonneg _) hνκ 2)
  have hpEn : ‖pureComponent (E : ℍ[ℝ])‖ ≤ κ := by
    refine le_trans ?_ hE1
    have e : pureComponent (E : ℍ[ℝ]) = pureComponent ((E : ℍ[ℝ]) - 1) := by
      rw [pureComponent_sub, pureComponent_one, sub_zero]
    rw [e]
    exact norm_pureComponent_le _
  have hAd : ‖adjointAction m (pureComponent (E : ℍ[ℝ])) - pureComponent (E : ℍ[ℝ])‖ ≤
      2 * ‖(m : ℍ[ℝ]) - 1‖ * κ := by
    refine (BlockLines.norm_adjointAction_sub_le m _).trans ?_
    exact mul_le_mul_of_nonneg_left hpEn (by positivity)
  have hcross : ‖pureComponent ((((expUnit mu : UnitQuaternion) : ℍ[ℝ]) - 1) * ((h : ℍ[ℝ]) - 1))‖ ≤
      μ * κ := by
    refine (norm_pureComponent_le _).trans ?_
    rw [norm_mul]
    exact mul_le_mul hm1 hh1 (norm_nonneg _) hμ0
  have hfin : pureComponent (g : ℍ[ℝ]) - pureComponent (NormedSpace.exp y) =
      (adjointAction m (pureComponent (E : ℍ[ℝ])) - pureComponent (E : ℍ[ℝ])) +
        (pureComponent (E : ℍ[ℝ]) - unitQuaternionLog E) + (unitQuaternionLog E - Q) +
        pureComponent ((((expUnit mu : UnitQuaternion) : ℍ[ℝ]) - 1) * ((h : ℍ[ℝ]) - 1)) -
        (pureComponent (NormedSpace.exp y) - pureComponent (NormedSpace.exp (mu : ℍ[ℝ])) - Q) := by
    rw [hg, e2, hh, e3, hexp]
    abel
  rw [hfin]
  have b1 : (‖y‖ + μ) * ‖Q‖ ≤ (2 * μ + κ) * κ := by
    refine mul_le_mul (by linarith) hQκ (norm_nonneg _) (by positivity)
  calc _ ≤ ‖adjointAction m (pureComponent (E : ℍ[ℝ])) - pureComponent (E : ℍ[ℝ])‖ +
        ‖pureComponent (E : ℍ[ℝ]) - unitQuaternionLog E‖ + ‖unitQuaternionLog E - Q‖ +
        ‖pureComponent ((((expUnit mu : UnitQuaternion) : ℍ[ℝ]) - 1) * ((h : ℍ[ℝ]) - 1))‖ +
        ‖pureComponent (NormedSpace.exp y) - pureComponent (NormedSpace.exp (mu : ℍ[ℝ])) - Q‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 2 * ‖(m : ℍ[ℝ]) - 1‖ * κ + κ ^ 2 + Δ + μ * κ + (2 * μ + κ) * κ := by
        have := e4.trans b1
        linarith
    _ = Δ + 2 * κ ^ 2 + (2 * ‖(m : ℍ[ℝ]) - 1‖ + 3 * μ) * κ := by ring
variable {F : BlockFrame}
theorem re_finset_sum {ι : Type} (s : Finset ι) (f : ι → ℍ[ℝ]) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum (AddMonoidHom.mk' (fun q : ℍ[ℝ] => q.re) (fun a b => by simp)) f s
theorem re_parallelAverage_eq_zero {j : ℕ} (R : F.GaugeField j) {f : F.Site j → Fin 4 → ℍ[ℝ]}
    (hf : ∀ x i, (f x i).re = 0) (c : F.Site (j + 1) × Fin 4) : (parallelAverage R f c).re = 0 := by
  have hs : ∀ (r : ℝ) (q : ℍ[ℝ]), (r • q).re = r * q.re := fun r q => by simp
  unfold parallelAverage
  rw [hs, re_finset_sum]
  have : ∀ h ∈ centredCube F.blockSide, (∑ π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide,
      adjointAction (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
        (f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2)).re = 0 := by
    intro h _
    rw [re_finset_sum]
    refine Finset.sum_eq_zero fun π _ => ?_
    rw [re_finset_sum]
    exact Finset.sum_eq_zero fun r _ => re_adjointAction _ (hf _ _)
  rw [Finset.sum_eq_zero this]
  simp
theorem norm_parallelAverage_le_blockSide_mul {j : ℕ} (hL : Odd F.blockSide) (R : F.GaugeField j)
    {f : F.Site j → Fin 4 → ℍ[ℝ]} {c : F.Site (j + 1) × Fin 4} {d : ℝ}
    (h : ∀ h' ∈ centredCube F.blockSide, ∀ r ∈ Finset.range F.blockSide,
      ‖f (refineSite c.1 + siteOfCoords j h' + (r : ℤ) • unitStep j c.2) c.2‖ ≤ d) :
    ‖parallelAverage R f c‖ ≤ (F.blockSide : ℝ) * d := by
  have hLp : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  refine (BlockLines.norm_parallelAverage_le hL R f c).trans ?_
  have h1 : ∑ h' ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
      ‖f (BlockLines.lineBond c h' r).1 (BlockLines.lineBond c h' r).2‖ ≤
        (F.blockSide : ℝ) ^ 4 * ((F.blockSide : ℝ) * d) := by
    calc _ ≤ ∑ _h' ∈ centredCube F.blockSide, ∑ _r ∈ Finset.range F.blockSide, d :=
          Finset.sum_le_sum fun h' hh => Finset.sum_le_sum fun r hr => h h' hh r hr
      _ = (F.blockSide : ℝ) ^ 4 * ((F.blockSide : ℝ) * d) := by
          simp only [Finset.sum_const, LatticePaths.card_centredCube hL, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  calc _ ≤ 1 / (F.blockSide : ℝ) ^ 4 * ((F.blockSide : ℝ) ^ 4 * ((F.blockSide : ℝ) * d)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (F.blockSide : ℝ) * d := by field_simp
theorem step_error_le {t y μ M K C : ℝ} (ht : 0 ≤ t) (hy : 0 ≤ y) (hμ : 0 ≤ μ) (hM : 0 ≤ M)
    (hK : 0 ≤ K) (hC : 0 ≤ C) :
    2 * (C * (t ^ 2 + y * t) + 2 * (K * t) ^ 2 + (2 * M + 3 * μ) * (K * t)) ≤
      2 * (C + 2 * K ^ 2 + 6 * K) * (t ^ 2 + (y + μ + M) * t) := by
  have b1 : 0 ≤ K * (y * t) := by positivity
  have b2 : 0 ≤ K * (μ * t) := by positivity
  have b3 : 0 ≤ K * (M * t) := by positivity
  have b4 : 0 ≤ K ^ 2 * (y * t) := by positivity
  have b5 : 0 ≤ K ^ 2 * (μ * t) := by positivity
  have b6 : 0 ≤ K ^ 2 * (M * t) := by positivity
  have b7 : 0 ≤ K * t ^ 2 := by positivity
  have b8 : 0 ≤ C * (μ * t) := by positivity
  have b9 : 0 ≤ C * (M * t) := by positivity
  linarith
theorem chartGap_succ_eq (R : F.FieldChain) (U : ChainChart F) (j : ℕ) (b : F.Site (j + 1) × Fin 4) :
    chartGap R U (j + 1) b.1 b.2 = expUnit (U.coarse j b.1 b.2) *
      (referenceDefect R j b * bondAverageGap R U j b * (referenceDefect R j b)⁻¹) := by
  simp only [chartGap, chartField, bondAverageGap, gaugedBondAverage, referenceDefect]
  group
end CoordinateStep
open CoordinateStep in
theorem levelCoordinateStep_holds (hT : bondAngleAndAverageNormStatement) :
    levelCoordinateStepStatement := by
  obtain ⟨L0, hT⟩ := hT
  refine ⟨L0, fun L hodd hL0 => ?_⟩
  obtain ⟨C, c, hC, hc, hT⟩ := hT L hodd hL0
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hodd.pos
  set K : ℝ := (L : ℝ) + 1 with hK
  have hK1 : 1 ≤ K := by linarith
  set c' : ℝ := min c (min (1 / (4 * C + 1)) (1 / (12 * K))) with hc'
  have hc'p : 0 < c' := lt_min hc (lt_min (by positivity) (by positivity))
  have hc1 : c' ≤ c := min_le_left _ _
  have hc2 : c' ≤ 1 / (4 * C + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hc3 : c' ≤ 1 / (12 * K) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨2 * (C + 2 * K ^ 2 + 6 * K), c', by positivity, hc'p, ?_⟩
  intro F m S hFL hamb hm hreg s V hs0 hs hcold U j b hj hb t ht0 ht hmu hbl
  subst hFL
  have hj' : j < F.top := by omega
  have hLp : (0 : ℝ) < F.blockSide := by linarith
  set R := referenceFieldChain S V with hR
  have hcc1 : c' ≤ 1 := hc3.trans (by
    rw [div_le_one (by positivity)]
    linarith)
  obtain ⟨th, -, -⟩ := hT F m S rfl hamb hm hreg s V hs0 (hs.trans hc1) hcold U j b hj' hb t ht0
    (ht.trans hc1) hbl
  set l : ℝ := (1 / (F.blockSide : ℝ)) ^ (F.top - (j + 1)) with hl
  have hl0 : 0 ≤ l := by positivity
  have hl1 : l ≤ 1 := pow_le_one₀ (by positivity) (by rw [div_le_one hLp]; exact hLr)
  have hl2 : l ^ 2 ≤ 1 := pow_le_one₀ hl0 hl1
  set Q := parallelAverage (R j) (levelCoordinate R U j) b with hQ
  have hQre : Q.re = 0 := re_parallelAverage_eq_zero (R j) (fun x i => re_unitQuaternionLog _) b
  have hQn : ‖Q‖ ≤ (F.blockSide : ℝ) * t := norm_parallelAverage_le_blockSide_mul hodd (R j) hbl.2
  have hy : 0 ≤ s * l ^ 2 := by positivity
  have hy1 : s * l ^ 2 ≤ c' := by
    calc s * l ^ 2 ≤ s * 1 := mul_le_mul_of_nonneg_left hl2 hs0.le
      _ ≤ c' := by linarith
  set Δ : ℝ := C * (t ^ 2 + s * l ^ 2 * t) with hΔ
  have hΔt : Δ ≤ t := by
    have h1 : t ^ 2 + s * l ^ 2 * t ≤ (2 * c') * t := by nlinarith
    have h2 : C * (2 * c') ≤ 1 := by
      have : (4 * C + 1) * c' ≤ 1 := by
        calc (4 * C + 1) * c' ≤ (4 * C + 1) * (1 / (4 * C + 1)) :=
              mul_le_mul_of_nonneg_left hc2 (by positivity)
          _ = 1 := by field_simp
      nlinarith
    calc Δ ≤ C * ((2 * c') * t) := mul_le_mul_of_nonneg_left h1 hC.le
      _ = (C * (2 * c')) * t := by ring
      _ ≤ 1 * t := mul_le_mul_of_nonneg_right h2 ht0
      _ = t := one_mul t
  have hνκ : ‖bondAngle R U j b‖ ≤ K * t := by
    have : ‖bondAngle R U j b‖ ≤ ‖bondAngle R U j b - Q‖ + ‖Q‖ := by
      have := norm_add_le (bondAngle R U j b - Q) Q
      simpa using this
    rw [hK]
    nlinarith
  have hQκ : ‖Q‖ ≤ K * t := by rw [hK]; nlinarith
  have hsmall : 3 * ‖(U.coarse j b.1 b.2 : ℍ[ℝ])‖ + 3 * (K * t) ≤ 1 / 2 := by
    have h1 : K * t ≤ K * c' := mul_le_mul_of_nonneg_left ht (by linarith)
    have h2 : 12 * K * c' ≤ 1 := by
      calc 12 * K * c' ≤ 12 * K * (1 / (12 * K)) := mul_le_mul_of_nonneg_left hc3 (by positivity)
        _ = 1 := by field_simp
    have h3 : c' ≤ K * c' := by nlinarith
    linarith
  have hcore := norm_unitQuaternionLog_exp_mul_conj_sub_le (mu := U.coarse j b.1 b.2)
    (m := referenceDefect R j b) (E := bondAverageGap R U j b)
    hQre (Δ := Δ) (κ := K * t) th hνκ hQκ hsmall
  have e : levelCoordinate R U (j + 1) b.1 b.2 = unitQuaternionLog (expUnit (U.coarse j b.1 b.2) *
      (referenceDefect R j b * bondAverageGap R U j b * (referenceDefect R j b)⁻¹)) := by
    unfold levelCoordinate
    rw [chartGap_succ_eq]
  rw [e]
  refine hcore.trans ?_
  exact step_error_le ht0 hy (norm_nonneg _) (norm_nonneg _) (by linarith) hC.le
end YangMills.Construction.BlockAverages
end
