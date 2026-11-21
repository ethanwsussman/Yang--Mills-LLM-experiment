import YangMills.Construction.ColdChainAtEveryLevel.GapsOfTheLevelsNearACell
import YangMills.Construction.ColdChainAtEveryLevel.SmallCoordinatesAreRegular
import YangMills.Construction.HoleBesideASecondHole.NormsNearACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace RegularChart
open GaugeFixing LatticePaths ChartCoordinates
section Norms
variable {F : BlockFrame}
theorem cellSupDist_comm (x y : F.Cell) : cellSupDist x y = cellSupDist y x := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem localNormSq_nonneg (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    0 ≤ localNormSq S B R U w := by apply _root_.YangMills.Construction.CoordinateSeminorms.localNormSq_nonneg <;> assumption
theorem localNormSq_mono_weights {S B : Finset F.Cell} {R : F.FieldChain} {U : ChainChart F} {w w' : F.SiteWeights} {E : ℝ}
    (hE : 0 ≤ E) (h0 : ∀ (j : ℕ) (x : F.Site j), 0 ≤ w j x)
    (hw : ∀ (j : ℕ) (x : F.Site j), enclosingCell x ∈ B → E * w j x ≤ w' j x) :
    E ^ 2 * localNormSq S B R U w ≤ localNormSq S B R U w' := by apply _root_.YangMills.Construction.LocalNorms.localNormSq_le_of_mul_weight_le <;> assumption
theorem decayWeights_apply (del : ℝ) (y0 : F.Cell) (j : ℕ) (x : F.Site j) :
    decayWeights F del 0 0 y0 j x = Real.exp (-del * cellSupDist (enclosingCell x) y0) := by
  simp [decayWeights]
theorem localNorm_sq (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) (z : F.Cell) :
    localNorm S R U w z ^ 2 = localNormSq S (cellBall S z 3) R U w :=
  Real.sq_sqrt (localNormSq_nonneg _ _ _ _ _)
theorem localNorm_le_supWeightedNorm {del : ℝ} (hdel : 0 ≤ del) {S : Finset F.Cell} {R : F.FieldChain} {U : ChainChart F}
    {z : F.Cell} (hz : z ∈ S) :
    localNorm S R U (oneSiteWeights F) z ≤ Real.exp (3 * del) * supWeightedNorm S del R U := by
  have hbdd : BddAbove (Set.range fun y0 : F.Cell => weightedNorm S R U (decayWeights F del 0 0 y0)) := by
    refine ⟨weightedNorm S R U (oneSiteWeights F), ?_⟩
    rintro _ ⟨y0, rfl⟩
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun q _ => ?_)
    rw [localNorm_sq, localNorm_sq]
    have := localNormSq_mono_weights (S := S) (B := cellBall S q 3) (R := R) (U := U)
      (w := decayWeights F del 0 0 y0) (w' := oneSiteWeights F) (E := 1) zero_le_one
      (fun j x => by rw [decayWeights_apply]; exact (Real.exp_pos _).le)
      (fun j x _ => by
        rw [decayWeights_apply, one_mul]
        refine Real.exp_le_one_iff.2 ?_
        have : (0 : ℝ) ≤ del * cellSupDist (enclosingCell x) y0 := by positivity
        linarith)
    simpa using this
  have h1 : weightedNorm S R U (decayWeights F del 0 0 z) ≤ supWeightedNorm S del R U := le_ciSup hbdd z
  have h2 : localNorm S R U (decayWeights F del 0 0 z) z ≤ weightedNorm S R U (decayWeights F del 0 0 z) := by
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun q => localNorm S R U (decayWeights F del 0 0 z) q ^ 2)
      (fun _ _ => by positivity) hz
  have h3 : Real.exp (-(3 * del)) * localNorm S R U (oneSiteWeights F) z ≤
      localNorm S R U (decayWeights F del 0 0 z) z := by
    have hs := localNormSq_mono_weights (S := S) (B := cellBall S z 3) (R := R) (U := U)
      (w := oneSiteWeights F) (w' := decayWeights F del 0 0 z) (E := Real.exp (-(3 * del))) (Real.exp_pos _).le
      (fun _ _ => zero_le_one) (fun j x hx => by
        rw [decayWeights_apply]
        have hd : cellSupDist z (enclosingCell x) ≤ 3 := by
          simp only [cellBall, Finset.mem_filter] at hx
          exact hx.2
        rw [cellSupDist_comm] at hd
        have hd' : (cellSupDist (enclosingCell x) z : ℝ) ≤ 3 := by exact_mod_cast hd
        simp only [oneSiteWeights, mul_one]
        refine Real.exp_le_exp.2 ?_
        nlinarith)
    rw [← localNorm_sq, ← localNorm_sq] at hs
    have hn : 0 ≤ localNorm S R U (decayWeights F del 0 0 z) z := Real.sqrt_nonneg _
    have hn' : 0 ≤ localNorm S R U (oneSiteWeights F) z := Real.sqrt_nonneg _
    rw [← mul_pow] at hs
    exact (pow_le_pow_iff_left₀ (mul_nonneg (Real.exp_pos _).le hn') hn (by norm_num)).1 hs
  have h4 : localNorm S R U (decayWeights F del 0 0 z) z ≤ supWeightedNorm S del R U := h2.trans h1
  have e : Real.exp (3 * del) * Real.exp (-(3 * del)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc localNorm S R U (oneSiteWeights F) z
      = Real.exp (3 * del) * (Real.exp (-(3 * del)) * localNorm S R U (oneSiteWeights F) z) := by
        rw [← mul_assoc, e, one_mul]
    _ ≤ Real.exp (3 * del) * supWeightedNorm S del R U :=
        mul_le_mul_of_nonneg_left (h3.trans h4) (Real.exp_pos _).le
end Norms
theorem period_eq {F : BlockFrame} {j : ℕ} (i : Fin 4) :
    (F.period j i : ℤ) = (F.extent i : ℤ) * (F.blockSide : ℤ) ^ (F.top - j) := by
  simp [BlockFrame.period]
variable {F : BlockFrame}
theorem norm_average_sub_average_le (hL : Odd F.blockSide)
    (f g : LatticeFractionalIntegration.Lattice4 → Equiv.Perm (Fin 4) → ℍ[ℝ]) {B : ℝ}
    (h : ∀ a ∈ centredCube F.blockSide, ∀ π, ‖f a π - g a π‖ ≤ B) :
    ‖(1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ a ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), f a π -
      (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ a ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), g a π‖ ≤ B := by apply _root_.YangMills.Construction.GaugedCriticality.norm_average_sub_average_le <;> assumption
theorem average_one (hL : Odd F.blockSide) :
    (1 / (24 * (F.blockSide : ℝ) ^ 4)) • ∑ _a ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugedCriticality.average_one <;> assumption
theorem norm_linkValue_sub_le {j : ℕ} {D : Set (F.Site j)} {X X' : F.GaugeField j} {G : ℝ}
    (h : ∀ x i, x ∈ D → x + unitStep j i ∈ D →
      ‖((X x i : UnitQuaternion) : ℍ[ℝ]) - ((X' x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ G)
    {x : F.Site j} {st : PathStep} (hx : x ∈ D) (hx' : x + stepDisplacement j st ∈ D) :
    ‖((linkValue X x st : UnitQuaternion) : ℍ[ℝ]) - ((linkValue X' x st : UnitQuaternion) : ℍ[ℝ])‖ ≤ G := by
  rcases st with ⟨i, b⟩
  cases b
  · have e : x + stepDisplacement j (i, false) = x - unitStep j i := by
      simp [stepDisplacement, sub_eq_add_neg]
    rw [e] at hx'
    simp only [linkValue, Bool.false_eq_true, if_false, coe_unitQuaternion_inv]
    rw [← star_sub, Quaternion.norm_star]
    exact h _ i hx' (by rw [sub_add_cancel]; exact hx)
  · have e : x + stepDisplacement j (i, true) = x + unitStep j i := by
      simp [stepDisplacement]
    rw [e] at hx'
    simp only [linkValue, if_true]
    exact h _ i hx hx'
theorem norm_pathHolonomy_sub_le {j : ℕ} {D : Set (F.Site j)} {X X' : F.GaugeField j} {G : ℝ}
    (h : ∀ x i, x ∈ D → x + unitStep j i ∈ D →
      ‖((X x i : UnitQuaternion) : ℍ[ℝ]) - ((X' x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ G)
    (x0 : F.Site j) : ∀ (l : List PathStep) (v : LatticeFractionalIntegration.Lattice4),
      AllAlong (fun v => x0 + siteOfCoords j v ∈ D) v l →
      ‖((pathHolonomy X (x0 + siteOfCoords j v) l : UnitQuaternion) : ℍ[ℝ]) -
        ((pathHolonomy X' (x0 + siteOfCoords j v) l : UnitQuaternion) : ℍ[ℝ])‖ ≤ l.length * G := by
  intro l
  induction l with
  | nil =>
    intro v _
    simp [pathHolonomy]
  | cons st r ih =>
    intro v hp
    have hnext : x0 + siteOfCoords j v + stepDisplacement j st =
        x0 + siteOfCoords j (v + FlatPairing.stepDisplacement st) := by
      rw [stepDisplacement_eq_siteOfCoords, add_assoc, ← siteOfCoords_add]
    have hv : x0 + siteOfCoords j v ∈ D := hp.1
    have hw : x0 + siteOfCoords j v + stepDisplacement j st ∈ D := by
      rw [hnext]
      exact allAlong_head hp.2
    have h1 := norm_linkValue_sub_le h hv hw
    have h2 := ih _ hp.2
    simp only [pathHolonomy, List.length_cons]
    rw [hnext, Submonoid.coe_mul, Submonoid.coe_mul]
    set a : ℍ[ℝ] := ((linkValue X (x0 + siteOfCoords j v) st : UnitQuaternion) : ℍ[ℝ])
    set b : ℍ[ℝ] := ((linkValue X' (x0 + siteOfCoords j v) st : UnitQuaternion) : ℍ[ℝ])
    set A : ℍ[ℝ] := ((pathHolonomy X (x0 + siteOfCoords j (v + FlatPairing.stepDisplacement st)) r : UnitQuaternion) : ℍ[ℝ])
    set B : ℍ[ℝ] := ((pathHolonomy X' (x0 + siteOfCoords j (v + FlatPairing.stepDisplacement st)) r : UnitQuaternion) : ℍ[ℝ])
    have hA : ‖A‖ = 1 := norm_coe_unitQuaternion _
    have hb : ‖b‖ = 1 := norm_coe_unitQuaternion _
    have e : a * A - b * B = (a - b) * A + b * (A - B) := by noncomm_ring
    rw [e]
    calc _ ≤ ‖(a - b) * A‖ + ‖b * (A - B)‖ := norm_add_le _ _
      _ = ‖a - b‖ + ‖A - B‖ := by rw [norm_mul, norm_mul, hA, hb, mul_one, one_mul]
      _ ≤ G + r.length * G := add_le_add h1 h2
      _ = _ := by
        push_cast
        ring
theorem natAbs_valMinAbs_intCast_le (n : ℕ) (k : ℤ) : ((k : ZMod n).valMinAbs).natAbs ≤ k.natAbs := by apply _root_.YangMills.Construction.BlockWeights.natAbs_valMinAbs_intCast_le <;> assumption
theorem cellSupDist_le_one_of_adjacent (hodd : Odd F.blockSide) {j : ℕ} {z z' : F.Cell}
    {h h' : LatticeFractionalIntegration.Lattice4}
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) (hh' : h' ∈ centredCube (F.blockSide ^ (F.top - j)))
    (i : Fin 4)
    (e : cellCentre j z + siteOfCoords j h + unitStep j i = cellCentre j z' + siteOfCoords j h') :
    cellSupDist z z' ≤ 1 := by
  obtain ⟨A, hA⟩ : ∃ A : ℤ, ((F.blockSide ^ (F.top - j) : ℕ) : ℤ) = 2 * A + 1 := by
    obtain ⟨A, hA⟩ := hodd.pow (n := F.top - j)
    exact ⟨A, by rw [hA]; push_cast; ring⟩
  have hA' : (F.blockSide : ℤ) ^ (F.top - j) = 2 * A + 1 := by
    rw [← hA]
    push_cast
    rfl
  have hA0 : 0 ≤ A := by
    have : (0 : ℤ) < (F.blockSide : ℤ) ^ (F.top - j) := by
      have := hodd.pos
      positivity
    omega
  have e' : siteOfCoords j ((fun μ => (F.blockSide : ℤ) ^ (F.top - j) * siteCoords z μ) + h +
      LatticeFractionalIntegration.basisVector i) =
      siteOfCoords (F := F) j ((fun μ => (F.blockSide : ℤ) ^ (F.top - j) * siteCoords z' μ) + h') := by
    rw [siteOfCoords_add, siteOfCoords_add, siteOfCoords_add, ← unitStep_eq]
    exact e
  simp only [cellSupDist]
  apply Finset.sup_le
  intro μ _
  have eμ := congrFun e' μ
  simp only [siteOfCoords, Pi.add_apply] at eμ
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (by exact_mod_cast eμ :
    ((((F.blockSide : ℤ) ^ (F.top - j) * siteCoords z μ + h μ + LatticeFractionalIntegration.basisVector i μ : ℤ)) :
        ZMod (F.period j μ)) =
      (((F.blockSide : ℤ) ^ (F.top - j) * siteCoords z' μ + h' μ : ℤ) : ZMod (F.period j μ)))
  rw [period_eq] at hk
  rw [hA'] at hk
  set sd : ℤ := (F.extent μ : ℤ) with hsd
  set t : ℤ := sd * k + siteCoords z μ - siteCoords z' μ with ht
  have h1 := (mem_centredCube_iff _ _).1 hh μ
  have h2 := (mem_centredCube_iff _ _).1 hh' μ
  rw [hA] at h1 h2
  have hδ : 0 ≤ LatticeFractionalIntegration.basisVector i μ ∧ LatticeFractionalIntegration.basisVector i μ ≤ 1 := by
    simp only [LatticeFractionalIntegration.basisVector, Pi.single_apply]
    split_ifs <;> norm_num
  have hhalf : (2 * A + 1 - 1) / 2 = A := by omega
  rw [hhalf] at h1 h2
  have ht1 : -1 ≤ t ∧ t ≤ 1 := by
    constructor
    · by_contra hc
      have : t ≤ -2 := by omega
      nlinarith
    · by_contra hc
      have : 2 ≤ t := by omega
      nlinarith
  have hcast : z μ - z' μ = ((t : ℤ) : ZMod (F.period F.top μ)) := by
    have hz : ((sd : ℤ) : ZMod (F.period F.top μ)) = 0 := by
      refine (CharP.intCast_eq_zero_iff (ZMod (F.period F.top μ)) (F.period F.top μ) _).2 ?_
      rw [period_eq]
      simp [hsd]
    rw [ht]
    push_cast
    rw [show (((sd : ℤ) : ZMod (F.period F.top μ))) = 0 from hz, zero_mul, zero_add]
    simp only [siteCoords, ZMod.intCast_cast, ZMod.cast_id', id]
  rw [hcast]
  refine (natAbs_valMinAbs_intCast_le _ _).trans ?_
  omega
end RegularChart
open RegularChart GaugeFixing LatticePaths ChartCoordinates in
theorem smallChartIsRegular (hB : referenceBoundsStatement)
    (hG : levelGapNearCellStatement) : smallChartIsRegularStatement := by
  classical
  obtain ⟨CB, cB, L1, hCB, hcB, hB⟩ := hB
  obtain ⟨Cg, hCg, Lg, hG⟩ := hG
  refine ⟨max (max L1 Lg) 1, fun L hodd hLL del hdel hdel8 => ?_⟩
  obtain ⟨cg, hcg, hG⟩ := hG L hodd (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLL)
  have hL0 : 0 < L := hodd.pos
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL0
  set c : ℝ := min (min cB (cg / 2)) (min 1 (min (1 / (4 * CB)) (1 / (40 * (L : ℝ) * Cg)))) with hc
  have hc0 : 0 < c := by
    refine lt_min (lt_min hcB (by positivity)) (lt_min one_pos (lt_min (by positivity) (by positivity)))
  have hcB' : c ≤ cB := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcg' : c ≤ cg / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hc1 : c ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hc2 : c ≤ 1 / (4 * CB) := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hc3 : c ≤ 1 / (40 * (L : ℝ) * Cg) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hCc : CB * c ≤ 1 / 4 := by
    calc CB * c ≤ CB * (1 / (4 * CB)) := by gcongr
      _ = 1 / 4 := by field_simp
  have hLc : 5 * (L : ℝ) * (Cg * (2 * c)) ≤ 1 / 4 := by
    calc 5 * (L : ℝ) * (Cg * (2 * c)) = 10 * ((L : ℝ) * Cg) * c := by ring
      _ ≤ 10 * ((L : ℝ) * Cg) * (1 / (40 * (L : ℝ) * Cg)) := by gcongr
      _ = 1 / 4 := by field_simp; norm_num
  refine ⟨c, hc0, ?_⟩
  intro F m S hFL hamb hm hreg s V hs hsc hcold U hU
  have hoddF : Odd F.blockSide := hFL ▸ hodd
  have hL1 : L1 ≤ F.blockSide := hFL ▸ le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLL
  have hLF : (F.blockSide : ℝ) = L := by rw [hFL]
  set R := referenceFieldChain S V with hR
  have hexp : Real.exp (3 * del) ≤ 2 := by
    have h1 := Real.add_one_le_exp (-(3 * del))
    have h2 : Real.exp (3 * del) * Real.exp (-(3 * del)) = 1 := by
      rw [← Real.exp_add]
      simp
    have h3 := Real.exp_pos (3 * del)
    nlinarith
  have hnear : ∀ z ∈ S, localNorm S R U (oneSiteWeights F) z ≤ 2 * supWeightedNorm S del R U := by
    intro z hz
    have h1 := localNorm_le_supWeightedNorm (del := del) hdel.le (R := R) (U := U) hz
    have h0 : 0 ≤ localNorm S R U (oneSiteWeights F) z := Real.sqrt_nonneg _
    have hN : 0 ≤ supWeightedNorm S del R U := by
      by_contra hneg
      have := mul_neg_of_pos_of_neg (Real.exp_pos (3 * del)) (not_le.1 hneg)
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right hexp hN)
  have hgap : ∀ z ∈ S, ∀ j, j < F.top → ∀ x i, x ∈ (sitesOfCells (cellBall S z 1) j : Set (F.Site j)) →
      x + unitStep j i ∈ (sitesOfCells (cellBall S z 1) j : Set (F.Site j)) →
      ‖((chartField R U j x i : UnitQuaternion) : ℍ[ℝ]) - ((R j x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ Cg * (2 * c) := by
    intro z hz j hj x i hx hx'
    have h1 := (hG F m S hFL hamb hm hreg s V hs (hsc.trans (hcg'.trans (by linarith))) hcold U z (2 * c) hz
      (by positivity) (by linarith) ((hnear z hz).trans (by linarith)) j hj).1
    have hb : (x, i) ∈ innerBonds (cellBall S z 1) j := mem_innerBonds hx hx'
    have h2 : normSubOne (chartGap R U j x i) ^ 4 ≤ (Cg * (2 * c)) ^ 4 :=
      (Finset.single_le_sum (f := fun b : F.Site j × Fin 4 => normSubOne (chartGap R U j b.1 b.2) ^ 4)
        (fun _ _ => by positivity) hb).trans h1
    have h3 := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h2
    have h4 : normSubOne (chartGap R U j x i) =
        ‖((chartField R U j x i : UnitQuaternion) : ℍ[ℝ]) - ((R j x i : UnitQuaternion) : ℍ[ℝ])‖ :=
      norm_mul_inv_sub_one _ _
    rw [← h4]
    exact h3
  have hbox : ∀ z ∈ S, z ∈ cellBall S z 1 := by
    intro z hz
    simp [cellBall, hz, cellSupDist]
  have hGnn : 0 ≤ Cg * (2 * c) := by positivity
  refine ⟨fun j hj => ⟨fun y hy => ?_, fun b hb => ?_⟩, hnear⟩
  · have hj' : j + 1 ≤ F.top := hj
    obtain ⟨z, hz, h, hh, hye⟩ := mem_sitesOfCells.1 hy
    have hy' : y ∈ sitesOfCells (cellBall S z 1) (j + 1) := mem_sitesOfCells.2 ⟨z, hbox z hz, h, hh, hye⟩
    have hterm : ∀ a ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
        ‖((pathHolonomy (chartField R U j) (refineSite y) (axisPath a π) *
            (pathHolonomy (R j) (refineSite y) (axisPath a π))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 1 / 4 := by
      intro a ha π
      rw [norm_mul_inv_sub_one]
      have hp := allAlong_axisPath (S := cellBall S z 1) hoddF hj' hy' ha π
      have hq := norm_pathHolonomy_sub_le (hgap z hz j hj) (refineSite y) _ 0 hp
      rw [add_siteOfCoords_zero] at hq
      refine hq.trans ?_
      have hb' : ∀ k, (a k).natAbs ≤ F.blockSide := by
        intro k
        have := (mem_centredCube_iff _ _).1 ha k
        omega
      have h2 : (axisPath a π).length ≤ 5 * F.blockSide := by
        rw [length_axisPath]
        have := hb' (π 0)
        have := hb' (π 1)
        have := hb' (π 2)
        have := hb' (π 3)
        omega
      have h3 : ((axisPath a π).length : ℝ) ≤ 5 * (L : ℝ) := by
        rw [← hLF]
        exact_mod_cast h2
      exact (mul_le_mul_of_nonneg_right h3 hGnn).trans hLc
    have hclose := norm_average_sub_average_le hoddF
      (fun a π => ((pathHolonomy (chartField R U j) (refineSite y) (axisPath a π) *
        (pathHolonomy (R j) (refineSite y) (axisPath a π))⁻¹ : UnitQuaternion) : ℍ[ℝ])) (fun _ _ => 1) hterm
    rw [average_one hoddF] at hclose
    intro h0
    unfold relativePathAverage at h0
    rw [h0] at hclose
    norm_num at hclose
  · have hj' : j + 1 ≤ F.top := hj
    have hb2 := innerBonds_ends hb
    obtain ⟨z, hz, h, hh, e1⟩ := mem_sitesOfCells.1 hb2.1
    obtain ⟨z', hz', h', hh', e2⟩ := mem_sitesOfCells.1 hb2.2
    have hd : cellSupDist z z' ≤ 1 := cellSupDist_le_one_of_adjacent hoddF hh hh' b.2 (by rw [← e1, ← e2])
    have hz'b : z' ∈ cellBall S z 1 := by
      simp only [cellBall, Finset.mem_filter]
      exact ⟨hz', hd⟩
    have hb' : b ∈ innerBonds (cellBall S z 1) (j + 1) :=
      mem_innerBonds (S := cellBall S z 1) (x := b.1) (i := b.2)
        (mem_sitesOfCells.2 ⟨z, hbox z hz, h, hh, e1⟩) (mem_sitesOfCells.2 ⟨z', hz'b, h', hh', e2⟩)
    have hterm : ∀ a ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
        ‖((pathHolonomy (chartField R U j) (refineSite b.1) (bondContour F.blockSide a π b.2) : UnitQuaternion) : ℍ[ℝ]) -
          ((pathHolonomy (R j) (refineSite b.1) (bondContour F.blockSide a π b.2) : UnitQuaternion) : ℍ[ℝ])‖ ≤ 1 / 4 := by
      intro a ha π
      have hp := allAlong_bondContour (S := cellBall S z 1) hoddF hj' hb' ha π
      have hq := norm_pathHolonomy_sub_le (hgap z hz j hj) (refineSite b.1) _ 0 hp
      rw [add_siteOfCoords_zero] at hq
      refine hq.trans ?_
      have h3 : ((bondContour F.blockSide a π b.2).length : ℝ) ≤ 5 * (L : ℝ) := by
        rw [← hLF]
        exact_mod_cast length_bondContour_le π b.2 hoddF.pos ha
      exact (mul_le_mul_of_nonneg_right h3 hGnn).trans hLc
    have hclose := norm_average_sub_average_le hoddF (fun a π => ((pathHolonomy (chartField R U j) (refineSite b.1)
      (bondContour F.blockSide a π b.2) : UnitQuaternion) : ℍ[ℝ]))
      (fun a π => ((pathHolonomy (R j) (refineSite b.1) (bondContour F.blockSide a π b.2) : UnitQuaternion) : ℍ[ℝ])) hterm
    obtain ⟨_, _, _, _, _, hlast⟩ := hB F m S hoddF hL1 hamb hm hreg s V hs (hsc.trans hcB') hcold
    have hcm := (hlast j hj b hb).2
    have hls : levelScale F (j + 1) ^ 4 ≤ 1 := by
      have hF1 : (1 : ℝ) ≤ (F.blockSide : ℝ) := by exact_mod_cast hoddF.pos
      have h1 : 1 / (F.blockSide : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact hF1
      have h0 : 0 ≤ 1 / (F.blockSide : ℝ) := by positivity
      exact pow_le_one₀ (pow_nonneg h0 _) (pow_le_one₀ h0 h1)
    have hs2 : s ^ 2 ≤ c := by
      have := hsc.trans hc1
      nlinarith
    have hsmall : CB * s ^ 2 * levelScale F (j + 1) ^ 4 ≤ 1 / 4 := by
      calc CB * s ^ 2 * levelScale F (j + 1) ^ 4 ≤ CB * s ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hls (by positivity)
        _ ≤ CB * c := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_left hs2 hCB.le
        _ ≤ 1 / 4 := hCc
    have hne : contourAverage (chartField R U j) b ≠ 0 := by
      intro h0
      unfold contourAverage at h0
      rw [h0] at hclose
      have e0 : ‖contourAverage (R j) b‖ ≤ 1 / 4 := by
        have e1 : ‖contourAverage (R j) b‖ = ‖(0 : ℍ[ℝ]) - contourAverage (R j) b‖ := by
          rw [zero_sub, norm_neg]
        rw [e1]
        exact hclose
      linarith
    have hu : ∀ g : UnitQuaternion, (g : ℍ[ℝ]) ≠ 0 := by
      intro g hg
      have := norm_coe_unitQuaternion g
      rw [hg, norm_zero] at this
      exact zero_ne_one this
    unfold gaugedContourAverage
    exact mul_ne_zero (mul_ne_zero (hu _) hne) (hu _)
end YangMills.Construction.BlockAverages
end
