import YangMills.Construction.ColdStepAtMirrorFrames.SitesCellsAndPositions
import YangMills.Construction.ColdStepAtMirrorFrames.SmallUnitsAndTheirLogarithms
import YangMills.Construction.ResponseInTheExpansion.FlatSumsOnTwoTori
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongATiltProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace WeightedResponses
variable {F : BlockFrame}
private def allTopBonds (F : BlockFrame) : Finset (F.Cell × Fin 4) := finiteCells F ×ˢ Finset.univ
open Classical in
private def radiusBonds (R : ℕ) : Finset ((Fin 4 → ℤ) × Fin 4) :=
  (centredCube (2 * R + 1) ×ˢ (Finset.univ : Finset (Fin 4))).filter fun q => BondWithinRadius R q
private def translateBond (Y : F.Cell) (q : (Fin 4 → ℤ) × Fin 4) : F.Cell × Fin 4 := (Y + siteOfCoords F.top q.1, q.2)
private theorem mem_centredCube_of_withinRadius {R : ℕ} {h : Fin 4 → ℤ} (hh : WithinRadius R h) :
    h ∈ centredCube (2 * R + 1) := by
  rw [TopLevelSites.mem_centredCube_iff]
  intro i
  have := abs_le.mp (hh i)
  unfold TopLevelSites.halfWidth
  push_cast
  have e : (2 * (R : ℤ) + 1 - 1) / 2 = R := by omega
  rw [e]
  exact this
private theorem valMinAbs_intCast_of_withinRadius {R : ℕ} (hs : ∀ l, 2 * R + 2 < F.extent l) {h : Fin 4 → ℤ}
    (hh : WithinRadius R h) (l : Fin 4) :
    (((h l : ℤ) : ZMod (F.period F.top l))).valMinAbs = h l := by
  have hp : F.period F.top l = F.extent l := TopLevelSites.period_top l
  have h0 : 0 < F.extent l := by have := hs l; omega
  have : NeZero (F.period F.top l) := ⟨by rw [hp]; omega⟩
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  rw [hp]
  have h1 := abs_le.mp (hh l)
  have h2 := hs l
  constructor <;> omega
private theorem translateBond_injOn {R : ℕ} (hs : ∀ l, 2 * R + 2 < F.extent l) (Y : F.Cell) :
    Set.InjOn (translateBond Y) (radiusBonds R : Set ((Fin 4 → ℤ) × Fin 4)) := by
  classical
  rintro ⟨h, l⟩ hq ⟨h', l'⟩ hq' e
  have hb := (Finset.mem_filter.mp hq).2
  have hb' := (Finset.mem_filter.mp hq').2
  have e1 : Y + siteOfCoords F.top h = Y + siteOfCoords F.top h' := congrArg Prod.fst e
  have e2 : l = l' := congrArg Prod.snd e
  have e3 : (siteOfCoords F.top h : F.Cell) = siteOfCoords F.top h' := add_left_cancel e1
  have e4 : h = h' := by
    funext m
    have e5 := congrFun e3 m
    have e6 := congrArg ZMod.valMinAbs e5
    change ((h m : ℤ) : ZMod (F.period F.top m)).valMinAbs = ((h' m : ℤ) : ZMod (F.period F.top m)).valMinAbs at e6
    rwa [valMinAbs_intCast_of_withinRadius hs hb.1, valMinAbs_intCast_of_withinRadius hs hb'.1] at e6
  rw [e2, e4]
private theorem cellSupDist_comm' (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
private theorem le_cellSupDist_of_not_mem_image {R : ℕ} (hR : 1 ≤ R) (Y z : F.Cell) (l : Fin 4)
    (h : ∀ q ∈ radiusBonds R, translateBond Y q ≠ (z, l)) : R ≤ cellSupDist Y z := by
  classical
  by_contra hlt
  have hlt' : cellSupDist z Y + 1 ≤ R := by
    rw [cellSupDist_comm']
    omega
  set o : Fin 4 → ℤ := fun i => ((z - Y) i).valMinAbs with ho
  have hz : z = Y + siteOfCoords F.top o := eq_add_siteOfCoords_valMinAbs z Y
  have hle : ∀ m, |o m| + 1 ≤ (R : ℤ) := fun m => by
    have h1 := natAbs_valMinAbs_le_siteSupDist z Y m
    have h2 : siteSupDist z Y = cellSupDist z Y := rfl
    rw [h2] at h1
    have h3 : ((o m).natAbs : ℤ) = |o m| := Int.natCast_natAbs _
    have h4 : (o m).natAbs + 1 ≤ R := by
      have : (o m).natAbs = (((z - Y) m).valMinAbs).natAbs := rfl
      omega
    omega
  have hbox : BondWithinRadius R (o, l) := by
    refine ⟨fun m => by have := hle m; change |o m| ≤ _; omega, fun m => ?_⟩
    have h5 := hle m
    have h6 := abs_le.mp (le_refl |o m|)
    by_cases hm : m = l
    · subst hm
      simp only [Pi.add_apply, Pi.single_eq_same]
      rw [abs_le]
      constructor <;> omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hm, add_zero]
      omega
  refine h (o, l) ?_ ?_
  · exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨mem_centredCube_of_withinRadius hbox.1, Finset.mem_univ _⟩, hbox⟩
  · change (Y + siteOfCoords F.top o, l) = (z, l)
    rw [← hz]
private theorem cellSupDist_translate {R : ℕ} (hs : ∀ l, 2 * R + 2 < F.extent l) (Y : F.Cell) {h : Fin 4 → ℤ}
    (hh : WithinRadius R h) :
    cellSupDist Y (Y + siteOfCoords F.top h) = Finset.univ.sup fun m => (h m).natAbs := by
  rw [cellSupDist_comm']
  unfold cellSupDist
  congr 1
  funext m
  have e : (Y + siteOfCoords F.top h : F.Cell) m - Y m = ((h m : ℤ) : ZMod (F.period F.top m)) := by
    simp [siteOfCoords]
  rw [e, valMinAbs_intCast_of_withinRadius hs hh]
section Coefficients
variable {a : ℝ} {L : ℕ} {c : ColdChainParameters}
private theorem abs_re_mul_le_norm (q : ℍ[ℝ]) (X : imaginaryQuaternions) (hX : ‖X‖ = 1) :
    |(q * (X : ℍ[ℝ])).re| ≤ ‖q‖ := by
  have h1 := SmallUnits.norm_sq_eq_re_sq_add_norm_imagPart_sq (q * (X : ℍ[ℝ]))
  have h2 : ‖q * (X : ℍ[ℝ])‖ = ‖q‖ := by
    rw [norm_mul]
    have : ‖(X : ℍ[ℝ])‖ = 1 := hX
    rw [this, mul_one]
  rw [h2] at h1
  have h3 : (q * (X : ℍ[ℝ])).re ^ 2 ≤ ‖q‖ ^ 2 := by
    nlinarith [sq_nonneg ‖SmallUnits.imagPart (q * (X : ℍ[ℝ]))‖]
  exact abs_le_of_sq_le_sq h3 (norm_nonneg q)
private theorem uniformField_smallCurvature {s : ℝ} (hs : 0 < s) :
    IsSmallCurvature s (ColdStepAtMirrorFrames.uniformField F F.top) := by apply _root_.YangMills.Construction.BlockMeans.SegmentMean.isSmallCurvature_uniformField <;> assumption
private theorem abs_flatCoefficient_le (hc : c.Admissible a L) (hF : IsBlockTorus L F)
    {b : F.Site F.depth × Fin 4} (hb : b ∈ chordBonds (finiteCells F)) {X : imaginaryQuaternions} (hX : ‖X‖ = 1)
    (e : F.Cell × Fin 4) :
    |flatCoefficient a c.ρA X b e| ≤ c.N 1 * Real.exp (-c.δ₁ * (cellSupDist (enclosingCell b.1) e.1 : ℝ)) := by
  have hσ : 0 < c.σA := hc.positivity.2.2.2.1
  have hcl := hc.estimates F c.σA _ hF hσ le_rfl (uniformField_smallCurvature (F := F) hσ)
  have h := (hcl.coordinates b hb).2 1 ![e] ![X] le_rfl (fun l => by fin_cases l; exact hX)
  have e1 : bondListDistance (enclosingCell b.1) ![e] = cellSupDist (enclosingCell b.1) e.1 := by
    unfold bondListDistance
    simp
  rw [e1] at h
  unfold flatCoefficient
  rw [abs_neg]
  exact (abs_re_mul_le_norm _ X hX).trans h
private theorem sum_exp_topBonds_le {δ S : ℝ} (hS : ∀ (F : BlockFrame) (j : ℕ) (y : F.Site j) (A : Finset (F.Site j)),
      ∑ z ∈ A, Real.exp (-(δ / 2 * siteSupDist y z)) ≤ S) (Y : F.Cell) :
    ∑ e ∈ allTopBonds F, Real.exp (-(δ / 2 * (cellSupDist Y e.1 : ℝ))) ≤ 4 * S := by
  classical
  unfold allTopBonds
  rw [Finset.sum_product]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have := hS F F.top Y (finiteCells F)
  have e : ∑ z ∈ finiteCells F, Real.exp (-(δ / 2 * (cellSupDist Y z : ℝ))) =
      ∑ z ∈ finiteCells F, Real.exp (-(δ / 2 * siteSupDist Y z)) := rfl
  rw [e]
  norm_num
  linarith
private theorem sum_sub_smul_eq {E ι : Type} [AddCommGroup E] [Module ℝ E] (A : Finset ι) (f g : ι → ℝ) (v : ι → E) :
    ∑ q ∈ A, (f q - g q) • v q = ∑ q ∈ A, f q • v q - ∑ q ∈ A, g q • v q := by
  simp only [sub_smul, Finset.sum_sub_distrib]
open Classical in
private def outerPart (a ρ : ℝ) (X : imaginaryQuaternions) (b : F.Site F.depth × Fin 4)
    (D : F.Cell → Fin 4 → imaginaryQuaternions) (Y : F.Cell) (R : ℕ) : imaginaryQuaternions :=
  ∑ e ∈ allTopBonds F \ (radiusBonds R).image (translateBond Y), flatCoefficient a ρ X b e • D e.1 e.2
private theorem flatLinearPart_eq_add_outerPart {R : ℕ} (hs : ∀ l, 2 * R + 2 < F.extent l) (a ρ : ℝ)
    (X : imaginaryQuaternions) (b : F.Site F.depth × Fin 4) (D : F.Cell → Fin 4 → imaginaryQuaternions) (Y : F.Cell) :
    flatLinearPart a ρ X b D = ∑ q ∈ radiusBonds R, flatCoefficient a ρ X b (translateBond Y q) •
        D (translateBond Y q).1 (translateBond Y q).2 +
      outerPart a ρ X b D Y R := by
  classical
  have hpos : ∀ l, 0 < F.extent l := fun l => by have := hs l; omega
  have hsub : (radiusBonds R).image (translateBond (F := F) Y) ⊆ allTopBonds F := fun e _ =>
    Finset.mem_product.2 ⟨TopLevelSites.mem_finiteCells hpos _, Finset.mem_univ _⟩
  unfold outerPart flatLinearPart
  rw [← Finset.sum_product' (s := finiteCells F) (t := Finset.univ)
    (f := fun z i => flatCoefficient a ρ X b (z, i) • D z i), add_comm]
  have h := Finset.sum_sdiff (f := fun e : F.Cell × Fin 4 => flatCoefficient a ρ X b e • D e.1 e.2) hsub
  rw [Finset.sum_image (translateBond_injOn hs Y)] at h
  exact h.symm
private theorem norm_outerPart_le {S : ℝ} (hc : c.Admissible a L) (hF : IsBlockTorus L F)
    {b : F.Site F.depth × Fin 4} (hb : b ∈ chordBonds (finiteCells F)) {X : imaginaryQuaternions} (hX : ‖X‖ = 1)
    {R : ℕ} (hR : 1 ≤ R)
    (hS : ∀ (F : BlockFrame) (j : ℕ) (y : F.Site j) (A : Finset (F.Site j)),
      ∑ z ∈ A, Real.exp (-(c.δ₁ / 2 * siteSupDist y z)) ≤ S) {Y : F.Cell} (hY : enclosingCell b.1 = Y)
    (D : F.Cell → Fin 4 → imaginaryQuaternions) {s : ℝ} (hs0 : 0 ≤ s) (hD : ∀ z l, ‖D z l‖ ≤ s) :
    ‖outerPart a c.ρA X b D Y R‖ ≤ 4 * c.N 1 * S * s * Real.exp (-(c.δ₁ / 2 * (R : ℝ))) := by
  classical
  have hδ : 0 < c.δ₁ := hc.positivity.1
  have hN : 0 < c.N 1 := hc.positivity.2.2.2.2.2.1 1
  have hterm : ∀ e ∈ allTopBonds F \ (radiusBonds R).image (translateBond Y),
      ‖flatCoefficient a c.ρA X b e • D e.1 e.2‖ ≤
      c.N 1 * s * Real.exp (-(c.δ₁ / 2 * (R : ℝ))) * Real.exp (-(c.δ₁ / 2 * (cellSupDist Y e.1 : ℝ))) := by
    intro e he
    have hoff : ∀ q ∈ radiusBonds R, translateBond Y q ≠ (e.1, e.2) := fun q hq h =>
      (Finset.mem_sdiff.mp he).2 (Finset.mem_image.2 ⟨q, hq, h⟩)
    have hfar : (R : ℝ) ≤ cellSupDist Y e.1 := by
      exact_mod_cast le_cellSupDist_of_not_mem_image hR Y e.1 e.2 hoff
    rw [norm_smul, Real.norm_eq_abs]
    have h1 := abs_flatCoefficient_le hc hF hb hX e
    rw [hY] at h1
    have h2 : Real.exp (-c.δ₁ * (cellSupDist Y e.1 : ℝ)) ≤
        Real.exp (-(c.δ₁ / 2 * (R : ℝ))) * Real.exp (-(c.δ₁ / 2 * (cellSupDist Y e.1 : ℝ))) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith
    calc |flatCoefficient a c.ρA X b e| * ‖D e.1 e.2‖
        ≤ (c.N 1 * (Real.exp (-(c.δ₁ / 2 * (R : ℝ))) * Real.exp (-(c.δ₁ / 2 * (cellSupDist Y e.1 : ℝ))))) * s :=
          mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h2 hN.le)) (hD _ _) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  calc ‖outerPart a c.ρA X b D Y R‖ ≤ ∑ e ∈ allTopBonds F \ (radiusBonds R).image (translateBond Y),
          ‖flatCoefficient a c.ρA X b e • D e.1 e.2‖ :=
        norm_sum_le _ _
    _ ≤ ∑ e ∈ allTopBonds F \ (radiusBonds R).image (translateBond Y),
          c.N 1 * s * Real.exp (-(c.δ₁ / 2 * (R : ℝ))) * Real.exp (-(c.δ₁ / 2 * (cellSupDist Y e.1 : ℝ))) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ e ∈ allTopBonds F,
          c.N 1 * s * Real.exp (-(c.δ₁ / 2 * (R : ℝ))) * Real.exp (-(c.δ₁ / 2 * (cellSupDist Y e.1 : ℝ))) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => by positivity
    _ = c.N 1 * s * Real.exp (-(c.δ₁ / 2 * (R : ℝ))) *
          ∑ e ∈ allTopBonds F, Real.exp (-(c.δ₁ / 2 * (cellSupDist Y e.1 : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ c.N 1 * s * Real.exp (-(c.δ₁ / 2 * (R : ℝ))) * (4 * S) :=
        mul_le_mul_of_nonneg_left (sum_exp_topBonds_le hS Y) (by positivity)
    _ = _ := by ring
end Coefficients
theorem flatLinearPartLocality_holds (hS : ExpDecaySumBounded) : FlatLinearPartLocality := by
  intro a L c hL hc
  have hδ : 0 < c.δ₁ := hc.positivity.1
  have hσ : 0 < c.σA := hc.positivity.2.2.2.1
  have hN : 0 < c.N 1 := hc.positivity.2.2.2.2.2.1 1
  obtain ⟨S, hS0, hSum⟩ := hS (c.δ₁ / 2) (by positivity)
  refine ⟨16 * c.N 1 * S, c.δ₁ / 2, by positivity, by positivity, ?_⟩
  intro F F' Y Y' R o i B D X s hF hF' ht hs hs' hR ho hb hb' hX hs0 hB hD hBD
  classical
  have hs2 : ∀ l, 2 ≤ F.extent l := fun l => by have := hs l; omega
  have hs2' : ∀ l, 2 ≤ F'.extent l := fun l => by have := hs' l; omega
  have hpos : ∀ l, 0 < F.extent l := fun l => by have := hs l; omega
  have hpos' : ∀ l, 0 < F'.extent l := fun l => by have := hs' l; omega
  have hOdd : Odd F.blockSide := by rw [hF.1]; exact hL
  have hOdd' : Odd F'.blockSide := by rw [hF'.1]; exact hL
  have ho' : o ∈ centredCube F.blockSide := by rw [hF.1]; exact ho
  have ho'' : o ∈ centredCube F'.blockSide := by rw [hF'.1]; exact ho
  have hz : ∀ {G : BlockFrame}, (siteOfCoords G.top (0 : Fin 4 → ℤ) : G.Cell) = 0 := fun {G} => by
    funext l
    simp [siteOfCoords]
  have hcell : enclosingCell (fineBondAt Y 0 o i).1 = Y := by
    unfold fineBondAt
    simp only [hz, add_zero]
    exact TopLevelSites.enclosingCell_centre_add hOdd hs2 Y o ho'
  have hcell' : enclosingCell (fineBondAt Y' 0 o i).1 = Y' := by
    unfold fineBondAt
    simp only [hz, add_zero]
    exact TopLevelSites.enclosingCell_centre_add hOdd' hs2' Y' o ho''
  have hcl := hc.estimates F c.σA _ hF hσ le_rfl (uniformField_smallCurvature (F := F) hσ)
  have hagree : AgreeOnBall (finiteCells F) (ColdStepAtMirrorFrames.uniformField F F.top) (finiteCells F')
      (ColdStepAtMirrorFrames.uniformField F' F'.top) Y Y' R :=
    ⟨fun l => Or.inr (hs l), fun l => Or.inr (hs' l),
      fun _ _ => ⟨fun _ => TopLevelSites.mem_finiteCells hpos' _, fun _ => TopLevelSites.mem_finiteCells hpos _⟩,
      fun _ _ => rfl⟩
  have hloc := (hcl.locality F' _ Y Y' R (by rw [hF.1, hF'.1]) ht hF'.2
    (uniformField_smallCurvature (F := F') hσ) hagree).2.1
  have hnext : cellSupDist Y (enclosingCell ((fineBondAt Y 0 o i).1 + unitStep F.depth i)) ≤ R := by
    have h1 := TopLevelSites.cellSupDist_enclosingCell_step_le hOdd hs2 (fineBondAt Y 0 o i).1 i
    rw [hcell] at h1
    omega
  have hin0 : BlockAverages.WithinRadius R (0 : Fin 4 → ℤ) := fun l => by simp
  have hlocal := (hloc 0 o i ho' hb hin0 hnext).2
  rw [hcell] at hlocal
  have hdiff : ∀ q ∈ radiusBonds R, |flatCoefficient a c.ρA X (fineBondAt Y 0 o i) (translateBond Y q) -
      flatCoefficient a c.ρA X (fineBondAt Y' 0 o i) (translateBond Y' q)| ≤
      2 * c.N 1 * (Real.exp (-(c.δ₁ / 2 * (R : ℝ))) *
        Real.exp (-(c.δ₁ / 2 * (cellSupDist Y (translateBond Y q).1 : ℝ)))) := by
    intro q hq
    have hbq := (Finset.mem_filter.mp hq).2
    have e1 : offsetBonds Y ![q] = ![translateBond Y q] := by
      funext l
      fin_cases l
      rfl
    have e2 : offsetBonds Y' ![q] = ![translateBond Y' q] := by
      funext l
      fin_cases l
      rfl
    have hl := hlocal 1 ![q] ![X] le_rfl (fun l => by fin_cases l; exact hbq) (fun l => by fin_cases l; exact hX)
    rw [e1, e2] at hl
    have hA : |flatCoefficient a c.ρA X (fineBondAt Y 0 o i) (translateBond Y q) -
        flatCoefficient a c.ρA X (fineBondAt Y' 0 o i) (translateBond Y' q)| ≤
        c.N 1 * Real.exp (-c.δ₁ * ((R : ℝ) - (cellSupDist Y Y : ℕ))) := by
      unfold flatCoefficient
      have e3 : ∀ u v : ℍ[ℝ], -(u * (X : ℍ[ℝ])).re - -(v * (X : ℍ[ℝ])).re = -((u - v) * (X : ℍ[ℝ])).re :=
        fun u v => by
          rw [sub_mul]
          simp
          ring
      rw [e3, abs_neg]
      exact (abs_re_mul_le_norm _ X hX).trans hl
    have hself : cellSupDist Y Y = 0 := TopLevelSites.cellSupDist_self Y
    rw [hself] at hA
    have hdd : cellSupDist Y (translateBond Y q).1 = cellSupDist Y' (translateBond Y' q).1 := by
      change cellSupDist Y (Y + siteOfCoords F.top q.1) = cellSupDist Y' (Y' + siteOfCoords F'.top q.1)
      rw [cellSupDist_translate hs Y hbq.1, cellSupDist_translate hs' Y' hbq.1]
    have hB1 := abs_flatCoefficient_le hc hF hb hX (translateBond Y q)
    have hB2 := abs_flatCoefficient_le hc hF' hb' hX (translateBond Y' q)
    rw [hcell] at hB1
    rw [hcell', ← hdd] at hB2
    set d : ℝ := (cellSupDist Y (translateBond Y q).1 : ℝ) with hd
    have hE : Real.exp (-(c.δ₁ / 2 * (R : ℝ))) * Real.exp (-(c.δ₁ / 2 * d)) =
        Real.exp (-(c.δ₁ / 2 * ((R : ℝ) + d))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hE]
    have hEp := Real.exp_pos (-(c.δ₁ / 2 * ((R : ℝ) + d)))
    rcases le_total d (R : ℝ) with hle | hle
    · have h1 : Real.exp (-c.δ₁ * ((R : ℝ) - ((0 : ℕ) : ℝ))) ≤ Real.exp (-(c.δ₁ / 2 * ((R : ℝ) + d))) := by
        rw [Real.exp_le_exp]
        push_cast
        nlinarith
      have h2 := hA.trans (mul_le_mul_of_nonneg_left h1 hN.le)
      have h3 := mul_pos hN hEp
      linarith
    · have h1 : Real.exp (-c.δ₁ * d) ≤ Real.exp (-(c.δ₁ / 2 * ((R : ℝ) + d))) := by
        rw [Real.exp_le_exp]
        nlinarith
      have h2 := mul_le_mul_of_nonneg_left h1 hN.le
      have h3 := abs_sub (flatCoefficient a c.ρA X (fineBondAt Y 0 o i) (translateBond Y q))
        (flatCoefficient a c.ρA X (fineBondAt Y' 0 o i) (translateBond Y' q))
      linarith
  have hbox : ‖∑ q ∈ radiusBonds R, (flatCoefficient a c.ρA X (fineBondAt Y 0 o i) (translateBond Y q) -
      flatCoefficient a c.ρA X (fineBondAt Y' 0 o i) (translateBond Y' q)) •
        B (translateBond Y q).1 (translateBond Y q).2‖ ≤
      8 * c.N 1 * S * s * Real.exp (-(c.δ₁ / 2 * (R : ℝ))) := by
    have hinj := translateBond_injOn hs Y
    have hsub : (radiusBonds R).image (translateBond (F := F) Y) ⊆ allTopBonds F := fun e _ =>
      Finset.mem_product.2 ⟨TopLevelSites.mem_finiteCells hpos _, Finset.mem_univ _⟩
    have hw : ∑ q ∈ radiusBonds R, Real.exp (-(c.δ₁ / 2 * (cellSupDist Y (translateBond Y q).1 : ℝ))) ≤ 4 * S := by
      have h1 := Finset.sum_image
        (f := fun e : F.Cell × Fin 4 => Real.exp (-(c.δ₁ / 2 * (cellSupDist Y e.1 : ℝ)))) hinj
      rw [← h1]
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => (Real.exp_pos _).le).trans
        (sum_exp_topBonds_le hSum Y)
    calc _ ≤ ∑ q ∈ radiusBonds R, ‖(flatCoefficient a c.ρA X (fineBondAt Y 0 o i) (translateBond Y q) -
          flatCoefficient a c.ρA X (fineBondAt Y' 0 o i) (translateBond Y' q)) •
            B (translateBond Y q).1 (translateBond Y q).2‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ radiusBonds R, 2 * c.N 1 * s * Real.exp (-(c.δ₁ / 2 * (R : ℝ))) *
            Real.exp (-(c.δ₁ / 2 * (cellSupDist Y (translateBond Y q).1 : ℝ))) := by
          refine Finset.sum_le_sum fun q hq => ?_
          rw [norm_smul, Real.norm_eq_abs]
          calc _ ≤ (2 * c.N 1 * (Real.exp (-(c.δ₁ / 2 * (R : ℝ))) *
                Real.exp (-(c.δ₁ / 2 * (cellSupDist Y (translateBond Y q).1 : ℝ))))) * s :=
                mul_le_mul (hdiff q hq) (hB _ _) (norm_nonneg _) (by positivity)
            _ = _ := by ring
      _ = 2 * c.N 1 * s * Real.exp (-(c.δ₁ / 2 * (R : ℝ))) *
            ∑ q ∈ radiusBonds R, Real.exp (-(c.δ₁ / 2 * (cellSupDist Y (translateBond Y q).1 : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * c.N 1 * s * Real.exp (-(c.δ₁ / 2 * (R : ℝ))) * (4 * S) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
      _ = _ := by ring
  have hr1 := norm_outerPart_le hc hF hb hX hR hSum hcell B hs0 hB
  have hr2 := norm_outerPart_le hc hF' hb' hX hR hSum hcell' D hs0 hD
  have hsplit : flatLinearPart a c.ρA X (fineBondAt Y 0 o i) B - flatLinearPart a c.ρA X (fineBondAt Y' 0 o i) D =
      ∑ q ∈ radiusBonds R, (flatCoefficient a c.ρA X (fineBondAt Y 0 o i) (translateBond Y q) -
        flatCoefficient a c.ρA X (fineBondAt Y' 0 o i) (translateBond Y' q)) •
          B (translateBond Y q).1 (translateBond Y q).2 +
      (outerPart a c.ρA X (fineBondAt Y 0 o i) B Y R - outerPart a c.ρA X (fineBondAt Y' 0 o i) D Y' R) := by
    rw [flatLinearPart_eq_add_outerPart hs _ _ _ _ B Y, flatLinearPart_eq_add_outerPart hs' _ _ _ _ D Y']
    have e : ∀ q ∈ radiusBonds R, flatCoefficient a c.ρA X (fineBondAt Y' 0 o i) (translateBond Y' q) •
          D (translateBond Y' q).1 (translateBond Y' q).2 =
        flatCoefficient a c.ρA X (fineBondAt Y' 0 o i) (translateBond Y' q) •
          B (translateBond Y q).1 (translateBond Y q).2 := fun q hq => by
      have := hBD q.1 q.2 (Finset.mem_filter.mp hq).2
      change _ • D (Y' + siteOfCoords F'.top q.1) q.2 = _ • B (Y + siteOfCoords F.top q.1) q.2
      rw [this]
    rw [Finset.sum_congr rfl e]
    have h3 : ∑ q ∈ radiusBonds R, (flatCoefficient a c.ρA X (fineBondAt Y 0 o i) (translateBond Y q) -
        flatCoefficient a c.ρA X (fineBondAt Y' 0 o i) (translateBond Y' q)) •
          B (translateBond Y q).1 (translateBond Y q).2 =
        ∑ q ∈ radiusBonds R, flatCoefficient a c.ρA X (fineBondAt Y 0 o i) (translateBond Y q) •
          B (translateBond Y q).1 (translateBond Y q).2 -
        ∑ q ∈ radiusBonds R, flatCoefficient a c.ρA X (fineBondAt Y' 0 o i) (translateBond Y' q) •
          B (translateBond Y q).1 (translateBond Y q).2 :=
      sum_sub_smul_eq _ _ _ _
    rw [h3]
    abel
  rw [← Submodule.coe_sub]
  change ‖flatLinearPart a c.ρA X (fineBondAt Y 0 o i) B - flatLinearPart a c.ρA X (fineBondAt Y' 0 o i) D‖ ≤ _
  rw [hsplit]
  have h1 := norm_add_le (∑ q ∈ radiusBonds R, (flatCoefficient a c.ρA X (fineBondAt Y 0 o i) (translateBond Y q) -
        flatCoefficient a c.ρA X (fineBondAt Y' 0 o i) (translateBond Y' q)) •
          B (translateBond Y q).1 (translateBond Y q).2)
    (outerPart a c.ρA X (fineBondAt Y 0 o i) B Y R - outerPart a c.ρA X (fineBondAt Y' 0 o i) D Y' R)
  have h2 := norm_sub_le (outerPart a c.ρA X (fineBondAt Y 0 o i) B Y R)
    (outerPart a c.ρA X (fineBondAt Y' 0 o i) D Y' R)
  have e : 16 * c.N 1 * S * s * Real.exp (-(c.δ₁ / 2 * (R : ℝ))) =
      8 * c.N 1 * S * s * Real.exp (-(c.δ₁ / 2 * (R : ℝ))) + 4 * c.N 1 * S * s * Real.exp (-(c.δ₁ / 2 * (R : ℝ))) +
        4 * c.N 1 * S * s * Real.exp (-(c.δ₁ / 2 * (R : ℝ))) := by ring
  rw [e]
  linarith
end WeightedResponses
end YangMills.Construction
end
