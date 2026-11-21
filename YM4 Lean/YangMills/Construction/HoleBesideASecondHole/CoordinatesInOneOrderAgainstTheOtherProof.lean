import YangMills.Construction.HoleBesideASecondHole.CoordinatesInOneOrderAgainstTheOther
import YangMills.Construction.HoleBesideASecondHole.EnergyInTheChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LumpContours
open BlockAverages GaugeFixing
variable {F : BlockFrame}
open Classical in
theorem gaugeTransform_axialGauge_eq (σ : Equiv.Perm (Fin 4)) (V : F.GaugeField F.top) (U : F.GaugeField F.depth)
    (c : F.Site F.depth × Fin 4) :
    gaugeTransform (axialGauge σ U) U c.1 c.2 =
      if IsCrossingBond c then expUnit (bondCoordinate σ V U c) * V (enclosingCell c.1) c.2
      else expUnit (bondCoordinate σ V U c) := by
  unfold bondCoordinate
  split_ifs with h
  · rw [expUnit_minimalLog]; simp
  · rw [expUnit_minimalLog]
def legHolonomy (σ : Equiv.Perm (Fin 4)) (U : F.GaugeField F.depth) (x : F.Site F.depth) : UnitQuaternion :=
  pathHolonomy (gaugeTransform (axialGauge 1 U) U) (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) σ)
theorem axialGauge_eq_legHolonomy_mul (hpos : ∀ i, 0 < F.extent i) (hodd : Odd F.blockSide)
    (σ : Equiv.Perm (Fin 4)) (U : F.GaugeField F.depth) (x : F.Site F.depth) :
    axialGauge σ U x = legHolonomy σ U x * axialGauge 1 U x := by
  obtain ⟨-, hx⟩ := cellOffset_mem_and_eq hpos hodd x
  unfold legHolonomy
  rw [pathHolonomy_gaugeTransform, pathDisplacement_axisPath, hx, axialGauge_cellCentre hpos hodd]
  simp only [one_mul, inv_mul_cancel_right]
  rfl
theorem gaugeTransform_axialGauge_eq_conj (hpos : ∀ i, 0 < F.extent i) (hodd : Odd F.blockSide)
    (σ : Equiv.Perm (Fin 4)) (U : F.GaugeField F.depth) (x : F.Site F.depth) (i : Fin 4) :
    gaugeTransform (axialGauge σ U) U x i =
      legHolonomy σ U x * gaugeTransform (axialGauge 1 U) U x i * (legHolonomy σ U (x + unitStep F.depth i))⁻¹ := by
  simp only [gaugeTransform]
  rw [axialGauge_eq_legHolonomy_mul hpos hodd σ U x, axialGauge_eq_legHolonomy_mul hpos hodd σ U (x + unitStep F.depth i)]
  group
theorem length_axisPath_le (hodd : Odd F.blockSide) (h : Fin 4 → ℤ) (hh : h ∈ centredCube F.blockSide)
    (σ : Equiv.Perm (Fin 4)) : (axisPath h σ).length ≤ 2 * F.blockSide := by
  have hLz := blockSide_eq_two_mul_halfSide_add_one hodd
  have hb : ∀ m, (h m).natAbs ≤ F.blockSide / 2 := fun m => by
    have := abs_le.1 (mem_centredCube_iff_abs_le.1 hh m)
    omega
  rw [axisPath_eq_append]
  simp only [List.length_append, List.length_replicate, List.length_nil]
  have := hb (σ 0)
  have := hb (σ 1)
  have := hb (σ 2)
  have := hb (σ 3)
  omega
theorem pathWithin_axisPath_cellOffset (hpos : ∀ i, 0 < F.extent i) (hodd : Odd F.blockSide)
    (σ : Equiv.Perm (Fin 4)) (x : F.Site F.depth) :
    PathWithin (sitesBelow F.depth (enclosingCell x)) (cellCentre F.depth (enclosingCell x))
      (axisPath (cellOffset x) σ) :=
  pathWithin_axisPath _ (fun o ho => cellCentre_add_mem_sitesBelow hodd _ o ho) _
    (cellOffset_mem_and_eq hpos hodd x).1 σ
def trivialField (F : BlockFrame) : F.GaugeField F.depth := fun _ _ => 1
theorem pathHolonomy_trivialField (l : List PathStep) : ∀ z, pathHolonomy (trivialField F) z l = 1 := by
  induction l with
  | nil => intro z; rfl
  | cons st r ih =>
    intro z
    obtain ⟨i, b⟩ := st
    cases b <;> simp [pathHolonomy, linkValue, ih, trivialField]
theorem legHolonomy_bounds (hpos : ∀ i, 0 < F.extent i) (hodd : Odd F.blockSide) (σ : Equiv.Perm (Fin 4))
    (U U' : F.GaugeField F.depth) (x : F.Site F.depth) (e d : ℝ) (he : 0 ≤ e) (hd : 0 ≤ d)
    (h1 : ∀ c ∈ cutBonds (sitesBelow F.depth (enclosingCell x)),
      ‖((gaugeTransform (axialGauge 1 U) U c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ e)
    (h2 : ∀ c ∈ cutBonds (sitesBelow F.depth (enclosingCell x)),
      ‖((gaugeTransform (axialGauge 1 U) U c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) -
        (gaugeTransform (axialGauge 1 U') U' c.1 c.2 : UnitQuaternion)‖ ≤ d) :
    ‖((legHolonomy σ U x : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * F.blockSide * e ∧
      ‖((legHolonomy σ U x : UnitQuaternion) : ℍ[ℝ]) - (legHolonomy σ U' x : UnitQuaternion)‖ ≤
        2 * F.blockSide * d := by
  have hp := pathWithin_axisPath_cellOffset hpos hodd σ x
  have hlen : ((axisPath (cellOffset x) σ).length : ℝ) ≤ 2 * F.blockSide := by
    exact_mod_cast length_axisPath_le hodd _ (cellOffset_mem_and_eq hpos hodd x).1 σ
  have h1' : ∀ c ∈ cutBonds (sitesBelow F.depth (enclosingCell x)),
      ‖((gaugeTransform (axialGauge 1 U) U c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) -
        (trivialField F c.1 c.2 : UnitQuaternion)‖ ≤ e := fun c hc => by
    have : ((trivialField F c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) = 1 := rfl
    rw [this]
    exact h1 c hc
  have a1 := norm_pathHolonomy_sub_le e h1' _ _ hp
  have a2 := norm_pathHolonomy_sub_le d h2 _ _ hp
  rw [pathHolonomy_trivialField] at a1
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right hlen he)
    exact a1
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right hlen hd)
    exact a2
set_option maxHeartbeats 1000000 in
theorem bondCoordinatesLexComparison_holds : BondCoordinatesLexComparison := by
  refine ⟨fun L => 64 * (L : ℝ) + 16, fun L => ?_, ?_⟩
  · have : (0 : ℝ) ≤ L := by positivity
    linarith
  intro F hodd hc V U U' b d hU hU' hd σ
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hc.1 i]; have := hc.2; omega
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  set K := 64 * (F.blockSide : ℝ) + 16 with hK
  have hLpos : (1 : ℝ) ≤ (F.blockSide : ℝ) := by exact_mod_cast hodd.pos
  have hKpos : 0 < K := by rw [hK]; linarith
  set e := 1 / K with he
  have he4 : e ≤ 1 / 4 := by
    rw [he]
    exact one_div_le_one_div_of_le (by norm_num) (by rw [hK]; linarith)
  have hKe : K * e = 1 := by rw [he]; field_simp
  set x := b.1 with hx
  set i := b.2 with hi
  set y := enclosingCell x with hy
  set y' := enclosingCell (x + unitStep F.depth i) with hy'
  have hd0 : 0 ≤ d := by
    have hbm : b ∈ bondsOfEndBlocks b := by
      simp only [bondsOfEndBlocks, cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
        Finset.mem_union]
      refine ⟨Or.inl ((mem_sitesBelow_depth hpos hodd _ _).2 rfl), Or.inr ((mem_sitesBelow_depth hpos hodd _ _).2 rfl)⟩
    exact (norm_nonneg _).trans (hd b hbm)
  have val : ∀ (Z : F.GaugeField F.depth) (c : F.Site F.depth × Fin 4), ¬ IsCrossingBond c →
      gaugeTransform (axialGauge 1 Z) Z c.1 c.2 = expUnit (lexBondCoordinate V Z c) := by
    intro Z c hc
    have := gaugeTransform_axialGauge_eq 1 V Z c
    rw [if_neg hc] at this
    exact this
  have valc : ∀ (Z : F.GaugeField F.depth) (c : F.Site F.depth × Fin 4), IsCrossingBond c →
      gaugeTransform (axialGauge 1 Z) Z c.1 c.2 = expUnit (lexBondCoordinate V Z c) * V (enclosingCell c.1) c.2 := by
    intro Z c hc
    have := gaugeTransform_axialGauge_eq 1 V Z c
    rw [if_pos hc] at this
    exact this
  have dist_c : ∀ c ∈ bondsOfEndBlocks b, ‖((gaugeTransform (axialGauge 1 U) U c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) -
      (gaugeTransform (axialGauge 1 U') U' c.1 c.2 : UnitQuaternion)‖ ≤ 2 * d := by
    intro c hc
    have a1 := (hU c hc).trans he4
    have a2 := (hU' c hc).trans he4
    have a3 := norm_exp_sub_exp_le _ _ a1 a2
    have a4 := hd c hc
    by_cases hcr : IsCrossingBond c
    · rw [valc U c hcr, valc U' c hcr, coe_mul_unitQuaternion, coe_mul_unitQuaternion, ← sub_mul, norm_mul_coe]
      simp only [coe_expUnit]
      linarith
    · rw [val U c hcr, val U' c hcr]
      simp only [coe_expUnit]
      linarith
  have sub1 : ∀ c ∈ cutBonds (sitesBelow F.depth y), c ∈ bondsOfEndBlocks b := fun c hc => by
    simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hc
    simp only [bondsOfEndBlocks, cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      Finset.mem_union]
    exact ⟨Or.inl hc.1, Or.inl hc.2⟩
  have sub2 : ∀ c ∈ cutBonds (sitesBelow F.depth y'), c ∈ bondsOfEndBlocks b := fun c hc => by
    simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hc
    simp only [bondsOfEndBlocks, cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      Finset.mem_union]
    exact ⟨Or.inr hc.1, Or.inr hc.2⟩
  have inner : ∀ (z : F.Cell) (c : F.Site F.depth × Fin 4), c ∈ cutBonds (sitesBelow F.depth z) →
      ¬ IsCrossingBond c := by
    intro z c hc
    simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hc
    intro hcr
    exact hcr (((mem_sitesBelow_depth hpos hodd z _).1 hc.2).trans ((mem_sitesBelow_depth hpos hodd z _).1 hc.1).symm)
  have near1 : ∀ (Z : F.GaugeField F.depth) (z : F.Cell),
      (∀ c ∈ cutBonds (sitesBelow F.depth z), ‖(lexBondCoordinate V Z c : ℍ[ℝ])‖ ≤ e) →
      ∀ c ∈ cutBonds (sitesBelow F.depth z),
        ‖((gaugeTransform (axialGauge 1 Z) Z c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * e := by
    intro Z z hz c hc
    rw [val Z c (inner z c hc)]
    have := norm_coe_expUnit_sub_one_le (lexBondCoordinate V Z c) ((hz c hc).trans he4)
    linarith [hz c hc]
  obtain ⟨A1, A2⟩ := legHolonomy_bounds hpos hodd σ U U' x (2 * e) (2 * d) (by positivity) (by positivity)
    (near1 U y fun c hc => hU c (sub1 c hc)) (fun c hc => dist_c c (sub1 c hc))
  obtain ⟨B1, B2⟩ := legHolonomy_bounds hpos hodd σ U U' (x + unitStep F.depth i) (2 * e) (2 * d) (by positivity)
    (by positivity) (near1 U y' fun c hc => hU c (sub2 c hc)) (fun c hc => dist_c c (sub2 c hc))
  obtain ⟨A1', -⟩ := legHolonomy_bounds hpos hodd σ U' U x (2 * e) (2 * d) (by positivity) (by positivity)
    (near1 U' y fun c hc => hU' c (sub1 c hc)) (fun c hc => by rw [norm_sub_rev]; exact dist_c c (sub1 c hc))
  obtain ⟨B1', -⟩ := legHolonomy_bounds hpos hodd σ U' U (x + unitStep F.depth i) (2 * e) (2 * d) (by positivity)
    (by positivity) (near1 U' y' fun c hc => hU' c (sub2 c hc))
    (fun c hc => by rw [norm_sub_rev]; exact dist_c c (sub2 c hc))
  have hbm : b ∈ bondsOfEndBlocks b := by
    simp only [bondsOfEndBlocks, cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      Finset.mem_union]
    exact ⟨Or.inl ((mem_sitesBelow_depth hpos hodd _ _).2 rfl), Or.inr ((mem_sitesBelow_depth hpos hodd _ _).2 rfl)⟩
  set A := legHolonomy σ U x with hA
  set A' := legHolonomy σ U' x with hA'
  set B := legHolonomy σ U (x + unitStep F.depth i) with hB
  set B' := legHolonomy σ U' (x + unitStep F.depth i) with hB'
  have g1 := gaugeTransform_axialGauge_eq_conj hpos hodd σ U x i
  have g2 := gaugeTransform_axialGauge_eq_conj hpos hodd σ U' x i
  rw [← hA, ← hB] at g1
  rw [← hA', ← hB'] at g2
  set X := gaugeTransform (axialGauge 1 U) U x i with hX
  set X' := gaugeTransform (axialGauge 1 U') U' x i with hX'
  set g := gaugeTransform (axialGauge σ U) U x i with hg
  set g' := gaugeTransform (axialGauge σ U') U' x i with hg'
  have hdist : ‖(g : ℍ[ℝ]) - g'‖ ≤ (8 * F.blockSide + 2) * d := by
    rw [g1, g2]
    refine (norm_coe_mul_sub_coe_mul_le _ _ _ _).trans ?_
    rw [norm_coe_inv_sub_coe_inv]
    have h1 := norm_coe_mul_sub_coe_mul_le A X A' X'
    have h2 := dist_c b hbm
    linarith
  have hw1 := norm_coe_expUnit_sub_one_le _ ((hU b hbm).trans he4)
  have hw2 := norm_coe_expUnit_sub_one_le _ ((hU' b hbm).trans he4)
  have hwe := hU b hbm
  have hwe' := hU' b hbm
  unfold bondCoordinate
  by_cases hcr : IsCrossingBond b
  · simp only [if_pos hcr]
    set v := V (enclosingCell b.1) b.2 with hv
    have n1 : ‖((g * v⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 1 / 8 := by
      have e1 : g * v⁻¹ = A * (expUnit (lexBondCoordinate V U b) * (v * B⁻¹ * v⁻¹)) := by
        rw [g1, hX, valc U b hcr, ← hv]
        group
      rw [e1]
      refine (norm_mul_sub_one_le _ _).trans ?_
      have e2 := norm_mul_sub_one_le (expUnit (lexBondCoordinate V U b)) (v * B⁻¹ * v⁻¹)
      rw [norm_conj_sub_one, norm_inv_sub_one] at e2
      linarith
    have n2 : ‖((g' * v⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 1 / 8 := by
      have e1 : g' * v⁻¹ = A' * (expUnit (lexBondCoordinate V U' b) * (v * B'⁻¹ * v⁻¹)) := by
        rw [g2, hX', valc U' b hcr, ← hv]
        group
      rw [e1]
      refine (norm_mul_sub_one_le _ _).trans ?_
      have e2 := norm_mul_sub_one_le (expUnit (lexBondCoordinate V U' b)) (v * B'⁻¹ * v⁻¹)
      rw [norm_conj_sub_one, norm_inv_sub_one] at e2
      linarith
    refine (norm_minimalLog_sub_minimalLog_le _ _ n1 n2).trans ?_
    have e3 : ((g * v⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((g' * v⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
        ((g : ℍ[ℝ]) - g') * ((v⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      rw [coe_mul_unitQuaternion, coe_mul_unitQuaternion, sub_mul]
    rw [e3, norm_mul_coe]
    have hfin : K * d = (64 * (F.blockSide : ℝ) + 16) * d := by rw [hK]
    have hLd : 0 ≤ (F.blockSide : ℝ) * d := by positivity
    rw [hfin]
    linarith
  · simp only [if_neg hcr]
    have n1 : ‖(g : ℍ[ℝ]) - 1‖ ≤ 1 / 8 := by
      have e1 : g = A * (expUnit (lexBondCoordinate V U b) * B⁻¹) := by
        rw [g1, hX, val U b hcr]
        group
      rw [e1]
      refine (norm_mul_sub_one_le _ _).trans ?_
      have e2 := norm_mul_sub_one_le (expUnit (lexBondCoordinate V U b)) B⁻¹
      rw [norm_inv_sub_one] at e2
      linarith
    have n2 : ‖(g' : ℍ[ℝ]) - 1‖ ≤ 1 / 8 := by
      have e1 : g' = A' * (expUnit (lexBondCoordinate V U' b) * B'⁻¹) := by
        rw [g2, hX', val U' b hcr]
        group
      rw [e1]
      refine (norm_mul_sub_one_le _ _).trans ?_
      have e2 := norm_mul_sub_one_le (expUnit (lexBondCoordinate V U' b)) B'⁻¹
      rw [norm_inv_sub_one] at e2
      linarith
    refine (norm_minimalLog_sub_minimalLog_le _ _ n1 n2).trans ?_
    have hfin : K * d = (64 * (F.blockSide : ℝ) + 16) * d := by rw [hK]
    have hLd : 0 ≤ (F.blockSide : ℝ) * d := by positivity
    rw [hfin]
    linarith
end YangMills.Construction.LumpContours
end
