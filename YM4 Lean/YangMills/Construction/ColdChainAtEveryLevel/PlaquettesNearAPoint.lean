import YangMills.Construction.ColdChainAtEveryLevel.FactsOfTheLogarithm
import YangMills.Construction.ColdChainAtEveryLevel.PointsOfAPatchForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace PlaquetteExpansion
open BlockAverages BlockLines BlockWeights LatticePaths
variable {F : BlockFrame}
def covariantCurlAt {j : ℕ} (R : F.GaugeField j) (f : F.Site j → Fin 4 → ℍ[ℝ]) (p : F.Site j × Fin 4 × Fin 4) :
    ℍ[ℝ] :=
  f p.1 p.2.1 + adjointAction (R p.1 p.2.1) (f (p.1 + unitStep j p.2.1) p.2.2) -
    adjointAction (R p.1 p.2.1 * R (p.1 + unitStep j p.2.1) p.2.2 * (R (p.1 + unitStep j p.2.2) p.2.1)⁻¹)
      (f (p.1 + unitStep j p.2.2) p.2.1) -
    adjointAction (R p.1 p.2.1 * R (p.1 + unitStep j p.2.1) p.2.2 * (R (p.1 + unitStep j p.2.2) p.2.1)⁻¹ *
      (R p.1 p.2.2)⁻¹) (f p.1 p.2.2)
theorem plaquetteHolonomy_eq {j : ℕ} (X : F.GaugeField j) (x : F.Site j) (μ ν : Fin 4) :
    plaquetteHolonomy X (x, μ, ν) =
      X x μ * X (x + unitStep j μ) ν * (X (x + unitStep j ν) μ)⁻¹ * (X x ν)⁻¹ := by
  simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true, if_false,
    sub_eq_add_neg, add_neg_cancel_right, mul_one, mul_assoc]
  have hsum : x + unitStep j μ + unitStep j ν + -unitStep j μ = x + unitStep j ν := by abel
  rw [hsum]
  simp [mul_assoc]
theorem norm_coe_inv_sub_one_eq (g : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
theorem pureComponent_coe_inv (g : UnitQuaternion) :
    pureComponent ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = - pureComponent (g : ℍ[ℝ]) := by
  rw [BlockAverages.coe_unitQuaternion_inv, BlockAverages.pureComponent_star]
theorem norm_coe_sub_one_le_pureComponent (g : UnitQuaternion) :
    ‖(g : ℍ[ℝ]) - 1‖ ≤ ‖pureComponent (g : ℍ[ℝ])‖ + ‖(g : ℍ[ℝ]) - 1‖ ^ 2 := by
  have e : (g : ℍ[ℝ]) - 1 = pureComponent (g : ℍ[ℝ]) + (((g : ℍ[ℝ]).re - 1 : ℝ) : ℍ[ℝ]) := by
    conv_lhs => rw [← BlockAverages.re_add_pureComponent (g : ℍ[ℝ])]
    push_cast
    abel
  have h1 := BlockAverages.norm_coe_sub_one_sq g
  have h2 := BlockAverages.re_coe_le_one g
  have h3 : ‖((((g : ℍ[ℝ]).re - 1 : ℝ)) : ℍ[ℝ])‖ = 1 - (g : ℍ[ℝ]).re := by
    rw [Quaternion.norm_coe, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  calc ‖(g : ℍ[ℝ]) - 1‖ = ‖pureComponent (g : ℍ[ℝ]) + (((g : ℍ[ℝ]).re - 1 : ℝ) : ℍ[ℝ])‖ := by rw [← e]
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by rw [h3]; nlinarith [sq_nonneg ‖(g : ℍ[ℝ]) - 1‖]
theorem norm_coe_four_mul_sub_one_le (a b c d : UnitQuaternion) :
    ‖((a * b * c⁻¹ * d⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      ‖pureComponent (a : ℍ[ℝ]) + pureComponent (b : ℍ[ℝ]) - pureComponent (c : ℍ[ℝ]) -
          pureComponent (d : ℍ[ℝ])‖ +
        2 * (‖(a : ℍ[ℝ]) - 1‖ + ‖(b : ℍ[ℝ]) - 1‖ + ‖(c : ℍ[ℝ]) - 1‖ + ‖(d : ℍ[ℝ]) - 1‖) ^ 2 := by
  set A := ‖(a : ℍ[ℝ]) - 1‖ with hA
  set B := ‖(b : ℍ[ℝ]) - 1‖ with hB
  set C := ‖(c : ℍ[ℝ]) - 1‖ with hC
  set D := ‖(d : ℍ[ℝ]) - 1‖ with hD
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hC0 : 0 ≤ C := norm_nonneg _
  have hD0 : 0 ≤ D := norm_nonneg _
  have n1 : ‖((a * b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ A + B := BlockAverages.norm_coe_mul_sub_one_le a b
  have n2 : ‖((a * b * c⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ A + B + C := by
    have := BlockAverages.norm_coe_mul_sub_one_le (a * b) c⁻¹
    rw [norm_coe_inv_sub_one_eq] at this
    linarith
  have n3 : ‖((a * b * c⁻¹ * d⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ A + B + C + D := by
    have := BlockAverages.norm_coe_mul_sub_one_le (a * b * c⁻¹) d⁻¹
    rw [norm_coe_inv_sub_one_eq] at this
    linarith
  have p1 := BlockLines.norm_pureComponent_mul_sub_le a b
  have p2 := BlockLines.norm_pureComponent_mul_sub_le (a * b) c⁻¹
  have p3 := BlockLines.norm_pureComponent_mul_sub_le (a * b * c⁻¹) d⁻¹
  rw [norm_coe_inv_sub_one_eq, pureComponent_coe_inv] at p2 p3
  have q2 : ‖((a * b : UnitQuaternion) : ℍ[ℝ]) - 1‖ * C ≤ (A + B) * C := mul_le_mul_of_nonneg_right n1 hC0
  have q3 : ‖((a * b * c⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ * D ≤ (A + B + C) * D :=
    mul_le_mul_of_nonneg_right n2 hD0
  set P3 := pureComponent ((a * b * c⁻¹ * d⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hP3
  set P2 := pureComponent ((a * b * c⁻¹ : UnitQuaternion) : ℍ[ℝ]) with hP2
  set P1 := pureComponent ((a * b : UnitQuaternion) : ℍ[ℝ]) with hP1
  set pa := pureComponent (a : ℍ[ℝ])
  set pb := pureComponent (b : ℍ[ℝ])
  set pc := pureComponent (c : ℍ[ℝ])
  set pd := pureComponent (d : ℍ[ℝ])
  have e : P3 = (pa + pb - pc - pd) + (P1 - pa - pb) + (P2 - P1 - -pc) + (P3 - P2 - -pd) := by abel
  have hP : ‖P3‖ ≤ ‖pa + pb - pc - pd‖ + A * B + (A + B) * C + (A + B + C) * D := by
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_add_le ((pa + pb - pc - pd) + (P1 - pa - pb)) (P2 - P1 - -pc)
    have h2 := norm_add_le (pa + pb - pc - pd) (P1 - pa - pb)
    linarith
  have hs := norm_coe_sub_one_le_pureComponent (a * b * c⁻¹ * d⁻¹)
  have hsq : ‖((a * b * c⁻¹ * d⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 ≤ (A + B + C + D) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) n3 2
  nlinarith [mul_nonneg hA0 hB0, mul_nonneg hA0 hC0, mul_nonneg hA0 hD0, mul_nonneg hB0 hC0, mul_nonneg hB0 hD0,
    mul_nonneg hC0 hD0, sq_nonneg A, sq_nonneg B, sq_nonneg C, sq_nonneg D]
theorem norm_coe_conj_sub_one_eq (g h : UnitQuaternion) :
    ‖((g * h * g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(h : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_conj_sub_one <;> assumption
theorem four_mul_eq_conj_mul (X1 X2 X3 X4 r1 r2 r3 r4 : UnitQuaternion) : X1 * X2 * X3⁻¹ * X4⁻¹ =
    (X1 * r1⁻¹ * (r1 * (X2 * r2⁻¹) * r1⁻¹) * ((r1 * r2 * r3⁻¹) * (X3 * r3⁻¹) * (r1 * r2 * r3⁻¹)⁻¹)⁻¹ *
      ((r1 * r2 * r3⁻¹ * r4⁻¹) * (X4 * r4⁻¹) * (r1 * r2 * r3⁻¹ * r4⁻¹)⁻¹)⁻¹) * (r1 * r2 * r3⁻¹ * r4⁻¹) := by
  group
theorem plaquetteDefect_le_add_curl {j : ℕ} (X R : F.GaugeField j) (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteDefect X p ≤ plaquetteDefect R p +
      ‖covariantCurlAt R (fun x i => pureComponent ((X x i * (R x i)⁻¹ : UnitQuaternion) : ℍ[ℝ])) p‖ +
      2 * (‖((X p.1 p.2.1 * (R p.1 p.2.1)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
        ‖((X (p.1 + unitStep j p.2.1) p.2.2 * (R (p.1 + unitStep j p.2.1) p.2.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
        ‖((X (p.1 + unitStep j p.2.2) p.2.1 * (R (p.1 + unitStep j p.2.2) p.2.1)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
        ‖((X p.1 p.2.2 * (R p.1 p.2.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖) ^ 2 := by
  obtain ⟨x, μ, ν⟩ := p
  simp only []
  set r1 := R x μ with hr1
  set r2 := R (x + unitStep j μ) ν with hr2
  set r3 := R (x + unitStep j ν) μ with hr3
  set r4 := R x ν with hr4
  set g1 := X x μ * r1⁻¹ with hg1
  set g2 := X (x + unitStep j μ) ν * r2⁻¹ with hg2
  set g3 := X (x + unitStep j ν) μ * r3⁻¹ with hg3
  set g4 := X x ν * r4⁻¹ with hg4
  set t3 := r1 * r2 * r3⁻¹ with ht3
  set t4 := r1 * r2 * r3⁻¹ * r4⁻¹ with ht4
  have hX : plaquetteHolonomy X (x, μ, ν) =
      (g1 * (r1 * g2 * r1⁻¹) * (t3 * g3 * t3⁻¹)⁻¹ * (t4 * g4 * t4⁻¹)⁻¹) * plaquetteHolonomy R (x, μ, ν) := by
    rw [plaquetteHolonomy_eq, plaquetteHolonomy_eq]
    exact four_mul_eq_conj_mul _ _ _ _ r1 r2 r3 r4
  unfold plaquetteDefect
  rw [hX]
  refine (BlockAverages.norm_coe_mul_sub_one_le _ _).trans ?_
  have hf := norm_coe_four_mul_sub_one_le g1 (r1 * g2 * r1⁻¹) (t3 * g3 * t3⁻¹) (t4 * g4 * t4⁻¹)
  rw [norm_coe_conj_sub_one_eq, norm_coe_conj_sub_one_eq, norm_coe_conj_sub_one_eq] at hf
  have hc : covariantCurlAt R (fun x i => pureComponent ((X x i * (R x i)⁻¹ : UnitQuaternion) : ℍ[ℝ])) (x, μ, ν) =
      pureComponent (g1 : ℍ[ℝ]) + pureComponent ((r1 * g2 * r1⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
        pureComponent ((t3 * g3 * t3⁻¹ : UnitQuaternion) : ℍ[ℝ]) -
        pureComponent ((t4 * g4 * t4⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    simp only [covariantCurlAt, BlockAverages.coe_conj_eq_adjointAction, BlockAverages.pureComponent_adjointAction]
    rfl
  rw [hc]
  linarith
theorem norm_covariantCurlAt_sub_le {j : ℕ} (R : F.GaugeField j) (f g : F.Site j → Fin 4 → ℍ[ℝ])
    (p : F.Site j × Fin 4 × Fin 4) :
    ‖covariantCurlAt R f p - covariantCurlAt R g p‖ ≤ ‖f p.1 p.2.1 - g p.1 p.2.1‖ +
      ‖f (p.1 + unitStep j p.2.1) p.2.2 - g (p.1 + unitStep j p.2.1) p.2.2‖ +
      ‖f (p.1 + unitStep j p.2.2) p.2.1 - g (p.1 + unitStep j p.2.2) p.2.1‖ + ‖f p.1 p.2.2 - g p.1 p.2.2‖ := by
  obtain ⟨x, μ, ν⟩ := p
  simp only [covariantCurlAt]
  set A := f x μ - g x μ
  set t2 := R x μ
  set t3 := R x μ * R (x + unitStep j μ) ν * (R (x + unitStep j ν) μ)⁻¹
  set t4 := R x μ * R (x + unitStep j μ) ν * (R (x + unitStep j ν) μ)⁻¹ * (R x ν)⁻¹
  have e : f x μ + adjointAction t2 (f (x + unitStep j μ) ν) - adjointAction t3 (f (x + unitStep j ν) μ) -
      adjointAction t4 (f x ν) -
      (g x μ + adjointAction t2 (g (x + unitStep j μ) ν) - adjointAction t3 (g (x + unitStep j ν) μ) -
        adjointAction t4 (g x ν)) =
      A + adjointAction t2 (f (x + unitStep j μ) ν - g (x + unitStep j μ) ν) -
        adjointAction t3 (f (x + unitStep j ν) μ - g (x + unitStep j ν) μ) - adjointAction t4 (f x ν - g x ν) := by
    simp only [BlockLines.adjointAction_sub, A]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_sub_le (A + adjointAction t2 (f (x + unitStep j μ) ν - g (x + unitStep j μ) ν))
    (adjointAction t3 (f (x + unitStep j ν) μ - g (x + unitStep j ν) μ))
  have h2 := norm_add_le A (adjointAction t2 (f (x + unitStep j μ) ν - g (x + unitStep j μ) ν))
  simp only [BlockLines.norm_adjointAction] at h1 h2 ⊢
  linarith
theorem cellSupDist_enclosingCell_le_two (hodd : Odd F.blockSide) {S : Finset F.Cell} {j : ℕ} (hj : j ≤ F.top)
    {x : F.Site j} (hx : x ∈ sitesOfCells S j) (p : F.Site 0) (hd : 2 * baseDistance x p ≤ 3 * F.blockSide ^ F.top) :
    cellSupDist (enclosingCell x) (enclosingCell p) ≤ 2 := by
  obtain ⟨z, hz, h, hh, rfl⟩ := BlockAverages.mem_sitesOfCells.1 hx
  rw [BlockLines.enclosingCell_cellCentre_add hodd z h hh, BlockLines.cellSupDist_comm]
  refine PatchPoints.cellSupDist_enclosingCell_le hodd p z 2 fun i => ?_
  have hb : baseSite (cellCentre j z + siteOfCoords j h) =
      cellCentre 0 z + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ j * h i) := by
    rw [BlockAverages.baseSite_add j hj, BlockAverages.baseSite_cellCentre j hj]
  set x := cellCentre j z + siteOfCoords j h with hxdef
  have hdi : (((baseSite x - p : F.Site 0) i).valMinAbs).natAbs ≤ baseDistance x p :=
    Finset.le_sup (f := fun i => (((baseSite x - p : F.Site 0) i).valMinAbs).natAbs) (Finset.mem_univ i)
  have e : ((p - cellCentre 0 z : F.Site 0) i) = -((baseSite x - p : F.Site 0) i) +
      (siteOfCoords (F := F) 0 (fun i => (F.blockSide : ℤ) ^ j * h i)) i := by
    rw [hb]
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [e]
  refine (BlockWeights.natAbs_valMinAbs_add_le_add _ _).trans ?_
  rw [ZMod.natAbs_valMinAbs_neg]
  have hc := (LatticePaths.mem_centredCube_iff _ _).1 hh i
  obtain ⟨K, hK1, hK2, hK3⟩ := BlockLines.odd_pow_eq_two_mul_add_one hodd (F.top - j)
  rw [hK2] at hc
  have h2 : (((siteOfCoords (F := F) 0 (fun i => (F.blockSide : ℤ) ^ j * h i)) i).valMinAbs).natAbs ≤
      F.blockSide ^ j * K := by
    refine (BlockWeights.natAbs_valMinAbs_intCast_le _).trans ?_
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    refine Nat.mul_le_mul_left _ ?_
    omega
  have h3 : F.blockSide ^ j * K * 2 ≤ F.blockSide ^ F.top := by
    have : F.blockSide ^ F.top = F.blockSide ^ j * F.blockSide ^ (F.top - j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [this, hK1]
    nlinarith [Nat.zero_le (F.blockSide ^ j)]
  omega
theorem mem_innerBonds_cellsNearPoint (hodd : Odd F.blockSide) {S : Finset F.Cell} {j : ℕ} (hj : j ≤ F.top)
    {b : F.Site j × Fin 4} (hb : b ∈ innerBonds S j) (p : F.Site 0)
    (h1 : 2 * baseDistance b.1 p ≤ 3 * F.blockSide ^ F.top)
    (h2 : 2 * baseDistance (b.1 + unitStep j b.2) p ≤ 3 * F.blockSide ^ F.top) :
    b ∈ innerBonds (cellsNearPoint S p) j := by
  classical
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hb ⊢
  refine ⟨BlockLines.mem_sitesOfCells_of_enclosingCell_mem hodd hb.1 ?_,
    BlockLines.mem_sitesOfCells_of_enclosingCell_mem hodd hb.2 ?_⟩
  · exact Finset.mem_filter.2 ⟨BlockLines.enclosingCell_mem hodd hb.1, cellSupDist_enclosingCell_le_two hodd hj hb.1 p h1⟩
  · exact Finset.mem_filter.2 ⟨BlockLines.enclosingCell_mem hodd hb.2, cellSupDist_enclosingCell_le_two hodd hj hb.2 p h2⟩
theorem baseDistance_add_unitStep_le {j : ℕ} (hj : j ≤ F.top) (x : F.Site j) (i : Fin 4) (p : F.Site 0) :
    baseDistance (x + unitStep j i) p ≤ baseDistance x p + F.blockSide ^ j := by
  have := BlockWeights.baseDistance_add_le hj x (LatticeFractionalIntegration.basisVector i) p 1 fun l => by
    by_cases hl : l = i
    · subst hl
      simp [LatticeFractionalIntegration.basisVector]
    · simp [LatticeFractionalIntegration.basisVector, Pi.single_eq_of_ne hl]
  simpa [BlockAverages.unitStep_eq] using this
theorem sum_coarse_sq_le_of_localNorm_le (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (w : F.SiteWeights) (z : F.Cell) {β : ℝ} (hN : localNorm S R U w z ≤ β) (hβ : 0 ≤ β) :
    ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (cellBall S z 3) (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 ≤ β ^ 2 := by
  have hN' := (Real.sqrt_le_iff.1 hN).2
  unfold localNormSq at hN'
  have hA : 0 ≤ Real.sqrt (∑ b ∈ bondsOver S (cellBall S z 3) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) :=
    Real.sqrt_nonneg _
  have hB : 0 ≤ ∑ q ∈ plaquettesOver S (cellBall S z 3) 0, (w 0 q.1 * ‖linearizedCurl (R 0) U.fine q‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  linarith
theorem pureComponent_eq_im (q : ℍ[ℝ]) : pureComponent q = q.im := by
  have h1 := BlockAverages.re_add_pureComponent q
  have h2 := Quaternion.re_add_im q
  exact add_left_cancel (h1.trans h2.symm)
theorem norm_coe_im_le (g : UnitQuaternion) : ‖((g : UnitQuaternion) : ℍ[ℝ]).im‖ ≤ ‖(g : ℍ[ℝ]) - 1‖ := by
  rw [← pureComponent_eq_im]
  exact BlockLines.norm_pureComponent_coe_le g
theorem baseSite_zero (x : F.Site 0) : baseSite x = x := by apply _root_.YangMills.Construction.CellBumps.baseSite_zero <;> assumption
theorem card_innerPlaquettes_near_le {S : Finset F.Cell} (p : F.Site 0) {r : ℝ} (hr : 1 ≤ r) :
    (((innerPlaquettes S 0).filter fun q => (baseDistance q.1 p : ℝ) ≤ r).card : ℝ) ≤ 16 * (3 * r) ^ 4 := by
  classical
  set k : ℕ := ⌊r⌋₊ with hk
  have hk1 : (k : ℝ) ≤ r := Nat.floor_le (by linarith)
  have hkr : ∀ d : ℕ, (d : ℝ) ≤ r → d ≤ k := fun d hd => Nat.le_floor hd
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  have hcard : ((centredCube (2 * k + 1) ×ˢ (Finset.univ : Finset (Fin 4 × Fin 4))).card : ℝ) =
      16 * (2 * k + 1) ^ 4 := by
    rw [Finset.card_product, LatticePaths.card_centredCube hodd]
    simp
    ring
  have h1 : ((innerPlaquettes S 0).filter fun q => (baseDistance q.1 p : ℝ) ≤ r).card ≤
      (centredCube (2 * k + 1) ×ˢ (Finset.univ : Finset (Fin 4 × Fin 4))).card := by
    apply Finset.card_le_card_of_injOn (fun q => ((fun i => ((q.1 - p : F.Site 0) i).valMinAbs), q.2))
    · intro q hq
      have hq' : (baseDistance q.1 p : ℝ) ≤ r := (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).2
      have hd := hkr _ hq'
      refine Finset.mem_coe.2 (Finset.mem_product.2
        ⟨(LatticePaths.mem_centredCube_iff _ _).2 fun i => ?_, Finset.mem_univ _⟩)
      have h2 : (((q.1 - p : F.Site 0) i).valMinAbs).natAbs ≤ baseDistance q.1 p := by
        have := Finset.le_sup (f := fun i => (((baseSite q.1 - p : F.Site 0) i).valMinAbs).natAbs)
          (Finset.mem_univ i)
        simpa [baseDistance, baseSite_zero] using this
      push_cast
      have e : (2 * (k : ℤ) + 1 - 1) / 2 = k := by omega
      rw [e]
      omega
    · intro q _ q' _ e
      obtain ⟨e1, e2⟩ := Prod.ext_iff.1 e
      refine Prod.ext ?_ e2
      funext i
      have h1 := congrFun e1 i
      have h2 : ((q.1 - p : F.Site 0) i) = ((q'.1 - p : F.Site 0) i) := ZMod.injective_valMinAbs h1
      simpa using h2
  have h2 : (((innerPlaquettes S 0).filter fun q => (baseDistance q.1 p : ℝ) ≤ r).card : ℝ) ≤
      ((centredCube (2 * k + 1) ×ˢ (Finset.univ : Finset (Fin 4 × Fin 4))).card : ℝ) := by exact_mod_cast h1
  rw [hcard] at h2
  refine h2.trans ?_
  have h3 : (2 * (k : ℝ) + 1) ≤ 3 * r := by linarith
  have h4 : (2 * (k : ℝ) + 1) ^ 4 ≤ (3 * r) ^ 4 := pow_le_pow_left₀ (by positivity) h3 4
  linarith
end PlaquetteExpansion
end YangMills.Construction
end
