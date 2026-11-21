import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfTheReferenceProof
import YangMills.Construction.ColdChainAtEveryLevel.ChartOverAnotherTopProof
import YangMills.Construction.ColdChainAtEveryLevel.GapsOfTheLevelsNearACell
import YangMills.Construction.ColdChainAtEveryLevel.LastMisfitNearACell
import YangMills.Construction.ColdChainAtEveryLevel.MeanOfTheContoursOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace TopMisfit
open BlockLines FlatPairing LatticeFractionalIntegration
variable {F : BlockFrame}
theorem referenceFieldChain_top (S : Finset F.Cell) (V : F.GaugeField F.top) :
    referenceFieldChain S V F.top = V := by apply _root_.YangMills.Construction.ReferenceBounds.referenceFieldChain_top <;> assumption
theorem chartChain_top (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) :
    chartChain R U V F.top = V := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.chartChain_top <;> assumption
theorem chartChain_depth (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) :
    chartChain R U V F.depth = chartField R U F.depth := by apply _root_.YangMills.Construction.BlockAverages.ChartOverTop.chartChain_depth <;> assumption
theorem chartBondMisfit_depth_eq (S : Finset F.Cell) (V : F.GaugeField F.top) (U : ChainChart F)
    (c : F.Site F.top × Fin 4) :
    chartBondMisfit (referenceFieldChain S V) U V F.depth c =
      referenceDefect (referenceFieldChain S V) F.depth c *
        (relativeContourMean (chartField (referenceFieldChain S V) U F.depth)
          (referenceFieldChain S V F.depth) c)⁻¹ := by
  have h1 : chartChain (referenceFieldChain S V) U V (F.depth + 1) c.1 c.2 = V c.1 c.2 :=
    congrFun (congrFun (chartChain_top (referenceFieldChain S V) U V) c.1) c.2
  have h2 : referenceFieldChain S V (F.depth + 1) c.1 c.2 = V c.1 c.2 :=
    congrFun (congrFun (referenceFieldChain_top S V) c.1) c.2
  unfold chartBondMisfit referenceDefect relativeContourMean
  rw [h1, h2, chartChain_depth]
  simp only [chartGauge]
  group
theorem quadratic_smallness_le {C₀ Lr C₁ Db β r c : ℝ} (hC₀ : 0 ≤ C₀) (hLr : 0 ≤ Lr) (hC₁ : 0 ≤ C₁)
    (hDb : 0 ≤ Db) (hβ : 0 ≤ β) (hβc : β ≤ c) (hrc : r ≤ c)
    (hc : C₀ * (Lr * C₁) * (Lr * C₁ + Db) * c ≤ 1) :
    C₀ * (Lr * (C₁ * β)) * (Lr * (C₁ * β) + Db * r) ≤ β := by
  have h1 : Lr * (C₁ * β) + Db * r ≤ (Lr * C₁ + Db) * c := by
    have a1 : Lr * C₁ * β ≤ Lr * C₁ * c := mul_le_mul_of_nonneg_left hβc (by positivity)
    have a2 : Db * r ≤ Db * c := mul_le_mul_of_nonneg_left hrc hDb
    nlinarith
  have h2 : C₀ * (Lr * C₁) * (Lr * (C₁ * β) + Db * r) ≤ 1 :=
    (mul_le_mul_of_nonneg_left h1 (by positivity)).trans (by linarith)
  calc C₀ * (Lr * (C₁ * β)) * (Lr * (C₁ * β) + Db * r)
      = β * (C₀ * (Lr * C₁) * (Lr * (C₁ * β) + Db * r)) := by ring
    _ ≤ β * 1 := mul_le_mul_of_nonneg_left h2 hβ
    _ = β := mul_one _
theorem exists_small_threshold {c₀ cb cg A D : ℝ} (hc₀ : 0 < c₀) (hcb : 0 < cb) (hcg : 0 < cg)
    (hA : 0 < A) (hD : 0 ≤ D) :
    ∃ c : ℝ, 0 < c ∧ c ≤ cb ∧ c ≤ cg ∧ c * A ≤ c₀ ∧ D * c ≤ 1 := by
  have hD1 : 0 < D + 1 := by linarith
  refine ⟨min (min cb cg) (min (c₀ / A) (1 / (D + 1))), by positivity, ?_, ?_, ?_, ?_⟩
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (le_div_iff₀ hA).1 ((min_le_right _ _).trans (min_le_left _ _))
  · have h := (le_div_iff₀ hD1).1 (((min_le_right _ _).trans (min_le_right _ _) :
      min (min cb cg) (min (c₀ / A) (1 / (D + 1))) ≤ 1 / (D + 1)))
    have h0 : 0 < min (min cb cg) (min (c₀ / A) (1 / (D + 1))) := by positivity
    nlinarith
end TopMisfit
set_option maxHeartbeats 1000000 in
open TopMisfit BlockLines FlatPairing LatticeFractionalIntegration in
theorem topMisfitNearCell_holds (hMean : contourMeanFirstOrderStatement)
    (hB : referenceBoundsStatement) (hG : levelGapNearCellStatement) :
    topMisfitNearCellStatement := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hM⟩ := hMean
  obtain ⟨Db, cb, L1, hDb, hcb, hBd⟩ := hB
  obtain ⟨C₁, hC₁, L2, hG'⟩ := hG
  refine ⟨Db + 4 * C₁ + 1, by positivity, max (max L1 L2) 1, fun L hL hge => ?_⟩
  have hL1 : L1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hge)
  have hL2 : L2 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hge)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL.pos
  obtain ⟨cg, hcg, hG''⟩ := hG' L hL hL2
  obtain ⟨c, hc0, hccb, hccg, hcA, hcD⟩ := exists_small_threshold (A := (L : ℝ) * C₁ + Db + 1)
    (D := C₀ * ((L : ℝ) * C₁) * ((L : ℝ) * C₁ + Db)) hc₀ hcb hcg (by positivity) (by positivity)
  refine ⟨c, hc0, ?_⟩
  intro F m S hFL hamb hm hreg r V hr0 hrc hcold U z β hz hβ0 hβc hN b hb
  subst hFL
  have hodd : Odd F.blockSide := hL
  obtain ⟨-, -, -, c4, c5, -⟩ := hBd F m S hodd hL1 hamb hm hreg r V hr0 (hrc.trans hccb) hcold
  have hgap := (hG'' F m S rfl hamb hm hreg r V hr0 (hrc.trans hccg) hcold U z β hz hβ0 (hβc.trans hccg) hN
    F.depth (Nat.lt_succ_self _)).1
  set R := referenceFieldChain S V with hR
  set X := chartField R U F.depth with hX
  set B := cellBall S z 1 with hBdef
  have hBS : B ⊆ S := cellBall_subset S z 1
  have hbB : b ∈ innerBonds B F.top := mem_innerBonds_cellBall_of_mem_bondsOver hamb hodd S z le_rfl hb
  have hbS : b ∈ innerBonds S F.top := innerBonds_mono hBS _ hbB
  have hCb : 0 ≤ C₁ * β := by positivity
  have hsize : ∀ x ∈ innerBonds B F.depth, normSubOne (chartGap R U F.depth x.1 x.2) ≤ C₁ * β := by
    intro x hx
    have h1 := Finset.single_le_sum
      (f := fun x : F.Site F.depth × Fin 4 => normSubOne (chartGap R U F.depth x.1 x.2) ^ 4)
      (fun _ _ => by positivity) hx
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hCb (by norm_num)).1 (h1.trans hgap)
  have hcl : ∀ a ∈ twoBlockHull F.blockSide b.2, ∀ k, a + basisVector k ∈ twoBlockHull F.blockSide b.2 →
      ‖((X (refineSite b.1 + siteOfCoords F.depth a) k *
          (R F.depth (refineSite b.1 + siteOfCoords F.depth a) k)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        C₁ * β := by
    intro a ha k hk
    have hb' := bond_mem_innerBonds_of_mem_twoBlockHull (j := F.depth) (B := B) (Nat.lt_succ_self F.depth)
      hodd b hbB a k ha hk
    have h2 := hsize (refineSite b.1 + siteOfCoords F.depth a, k) hb'
    simp only [normSubOne, chartGap] at h2
    exact h2
  have hl : levelScale F (F.depth + 1) = 1 := by
    unfold levelScale
    have e : F.top - (F.depth + 1) = 0 := Nat.sub_self _
    rw [e, pow_zero]
  have hsp : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy (R F.depth) (refineSite b.1) (bondContour F.blockSide h π b.2) *
          (polarUnit (contourAverage (R F.depth) b))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Db * r := by
    intro h hh π
    have := c5 F.depth (Nat.lt_succ_self _) b hbS h hh π
    rw [hl, one_pow, mul_one] at this
    exact this
  have hLn : (F.blockSide : ℝ) * (C₁ * β) + Db * r ≤ c * ((F.blockSide : ℝ) * C₁ + Db + 1) := by
    have a1 : (F.blockSide : ℝ) * C₁ * β ≤ (F.blockSide : ℝ) * C₁ * c :=
      mul_le_mul_of_nonneg_left hβc (by positivity)
    have a2 : Db * r ≤ Db * c := mul_le_mul_of_nonneg_left hrc hDb.le
    have e : c * ((F.blockSide : ℝ) * C₁ + Db + 1) = (F.blockSide : ℝ) * C₁ * c + Db * c + c := by ring
    have e2 : (F.blockSide : ℝ) * (C₁ * β) = (F.blockSide : ℝ) * C₁ * β := by ring
    rw [e, e2]
    linarith
  have hτ0 : 0 ≤ (F.blockSide : ℝ) * (C₁ * β) := by positivity
  have hDr0 : 0 ≤ Db * r := by positivity
  obtain ⟨-, -, q3⟩ := hM F F.depth X (R F.depth) b (C₁ * β) (Db * r) hodd le_rfl hCb hDr0
    (by linarith) (by linarith) hcl hsp
  have hQ : ‖parallelAverage (R F.depth) (pureGap X (R F.depth)) b‖ ≤ C₁ * β := by
    have hY : ({b} : Finset (F.Site F.top × Fin 4)) ⊆ innerBonds B (F.depth + 1) :=
      Finset.singleton_subset_iff.2 hbB
    have h1 := sum_norm_parallelAverage_pow_four_le (Nat.lt_succ_self _) hodd {b} hY (R F.depth)
      (pureGap X (R F.depth))
    rw [Finset.sum_singleton] at h1
    have h2 : ∑ x ∈ innerBonds B F.depth, ‖pureGap X (R F.depth) x.1 x.2‖ ^ 4 ≤
        ∑ x ∈ innerBonds B F.depth, normSubOne (chartGap R U F.depth x.1 x.2) ^ 4 :=
      Finset.sum_le_sum fun x _ => pow_le_pow_left₀ (norm_nonneg _) (norm_pureComponent_coe_le _) 4
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hCb (by norm_num)).1 (h1.trans (h2.trans hgap))
  have hsec : C₀ * ((F.blockSide : ℝ) * (C₁ * β)) * ((F.blockSide : ℝ) * (C₁ * β) + Db * r) ≤ β :=
    quadratic_smallness_le hC₀.le (by positivity) hC₁.le hDb.le hβ0 hβc hrc hcD
  have hE : ‖((relativeContourMean X (R F.depth) b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 4 * (C₁ * β) + β := by
    linarith
  have hmis : ‖((referenceDefect R F.depth b : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ Db * r := c4 b hbS
  have hfin : normSubOne (chartBondMisfit R U V F.depth b) ≤ Db * r + (4 * (C₁ * β) + β) := by
    rw [chartBondMisfit_depth_eq]
    have h1 := norm_coe_mul_sub_one_le (referenceDefect R F.depth b) (relativeContourMean X (R F.depth) b)⁻¹
    rw [norm_coe_inv_sub_one] at h1
    exact h1.trans (add_le_add hmis hE)
  refine hfin.trans ?_
  have hrb : 0 ≤ r + β := by positivity
  nlinarith [mul_nonneg hDb.le hβ0, mul_nonneg hC₁.le hr0.le, mul_nonneg hDb.le hr0.le]
end YangMills.Construction.BlockAverages
end
