import YangMills.Construction.ColdChainAtEveryLevel.SizesOnARegion
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.VariationRates
open PatchLocality ChartCoordinates
variable {F : BlockFrame} {S : Finset F.Cell} {j : ℕ}
def actionTermCell (t : F.ActionTerm) : F.Cell := enclosingCell (actionTermSite t)
open Classical in
def actionTermsNear (S Zs : Finset F.Cell) : Finset F.ActionTerm :=
  (actionTerms S).filter fun t => ∀ z ∈ Zs, cellSupDist z (actionTermCell t) ≤ 4
open Classical in
def cellsNear (S Zs : Finset F.Cell) : Finset F.Cell := S.filter fun y => ∀ z ∈ Zs, cellSupDist z y ≤ 8
theorem card_cellsNear_le {Zs : Finset F.Cell} {z : F.Cell} (hz : z ∈ Zs) : (cellsNear S Zs).card ≤ 17 ^ 4 := by
  classical
  have := PatchLocality.card_le_of_cellSupDist_le z 8 (cellsNear S Zs) fun y hy => by
    rw [PatchLocality.cellSupDist_comm]
    exact (Finset.mem_filter.1 hy).2 z hz
  simpa using this
theorem mem_cellsNear {Zs : Finset F.Cell} {z : F.Cell} (hz : z ∈ Zs) :
    ∀ y ∈ cellsNear S Zs, y ∈ S ∧ cellSupDist z y ≤ 10 := fun y hy => by
  have h := Finset.mem_filter.1 hy
  exact ⟨h.1, (h.2 z hz).trans (by norm_num)⟩
theorem actionTermSite_mem (hodd : Odd F.blockSide) {t : F.ActionTerm} (ht : t ∈ actionTerms S) :
    actionTermSite t ∈ sitesOfCells S 0 := PatchLocality.actionTermSite_mem_sitesOfCells hodd ht
theorem scale_pow_actionTermLevel_le (hodd : Odd F.blockSide) {t : F.ActionTerm} (ht : t ∈ actionTerms S) :
    2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ actionTermLevel t ≤ 2 * GaugeMap.cellSideLength F := by
  have hlev : actionTermLevel t < F.top := by
    rcases t with p | ⟨j, c⟩
    · exact Nat.succ_pos _
    · exact Finset.mem_range.1 (Finset.mem_sigma.1 (Finset.inr_mem_disjSum.1 ht)).1
  have := mul_pow_le_cellSideLength hodd hlev
  nlinarith
theorem enclosingCell_mem_cellsNear (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {Zs : Finset F.Cell}
    {t : F.ActionTerm} (ht : t ∈ actionTermsNear S Zs) {x : F.Site j} (hj : j ≤ F.top) (hx : x ∈ sitesOfCells S j)
    (hw : SupClose (2 * (F.blockSide : ℤ) * (F.blockSide : ℤ) ^ actionTermLevel t) (actionTermSite t) (baseSite x)) :
    enclosingCell x ∈ cellsNear S Zs := by
  classical
  have ht' := Finset.mem_filter.1 ht
  have hs := actionTermSite_mem hodd ht'.1
  have hw' : SupClose (2 * GaugeMap.cellSideLength F) (baseSite (actionTermSite t)) (baseSite x) := by
    rw [baseSite_of_level_zero]
    exact SupClose.mono (scale_pow_actionTermLevel_le hodd ht'.1) hw
  have hd := cellSupDist_le_four hamb hodd (Nat.zero_le _) hj hs hx hw'
  refine Finset.mem_filter.2 ⟨(baseSite_eq_cellCentre_add hodd hj hx).1, fun z hz => ?_⟩
  have h1 := ht'.2 z hz
  have h2 := PatchLocality.cellSupDist_triangle z (enclosingCell (actionTermSite t)) (enclosingCell x)
  rw [PatchLocality.cellSupDist_comm (enclosingCell (actionTermSite t)) (enclosingCell x)] at h2
  unfold actionTermCell at h1
  omega
theorem enclosingCell_baseSite (hodd : Odd F.blockSide) {x : F.Site j} (hj : j ≤ F.top) (hx : x ∈ sitesOfCells S j) :
    enclosingCell (baseSite x) = enclosingCell x := by
  obtain ⟨-, h, hh, e⟩ := baseSite_eq_cellCentre_add hodd hj hx
  rw [e]
  exact LocalPartition.enclosingCell_cellCentre_add hodd _ h (by simpa using hh)
structure CellwiseSizes (a : ℝ) (S : Finset F.Cell) (W : F.FieldChain) (k : F.SiteGauge) (K ρ : ℝ) : Prop where
  plaquette_sum_le : ∀ v ∈ S, ∑ p ∈ plaquettesOver S {v} 0, actionTermSize a W k (Sum.inl p) ^ 2 ≤ K ^ 2
  bond_sum_le : ∀ j, j < F.top → ∀ v ∈ S,
    ∑ c ∈ bondsOver S {v} (j + 1), actionTermSize a W k (Sum.inr ⟨j, c⟩) ^ 2 ≤ (K * ρ ^ (F.top - 1 - j)) ^ 2
theorem sum_le_of_near_cells {α : Type} (P : Finset α) (cell : α → F.Cell) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    {z : F.Cell} {A : ℝ} (hA0 : 0 ≤ A) (hnear : ∀ a ∈ P, cell a ∈ S ∧ cellSupDist z (cell a) ≤ 4)
    (hcell : ∀ v ∈ S, ∑ a ∈ P with cell a = v, f a ≤ A) : ∑ a ∈ P, f a ≤ 6561 * A := by
  classical
  set Bx := S.filter fun y => cellSupDist z y ≤ 4 with hBx
  have hmem : ∀ a ∈ P, cell a ∈ Bx := fun a ha => Finset.mem_filter.2 (hnear a ha)
  rw [← Finset.sum_fiberwise_of_maps_to hmem]
  have h1 : ∑ v ∈ Bx, ∑ a ∈ P with cell a = v, f a ≤ Bx.card * A := by
    have := Finset.sum_le_card_nsmul Bx _ A fun v hv => hcell v (Finset.mem_filter.1 hv).1
    simpa using this
  have h2 : Bx.card ≤ 6561 := by
    have := PatchLocality.card_le_of_cellSupDist_le z 4 Bx fun y hy => by
      rw [PatchLocality.cellSupDist_comm]
      exact (Finset.mem_filter.1 hy).2
    simpa using this
  have h3 : (Bx.card : ℝ) ≤ 6561 := by exact_mod_cast h2
  exact h1.trans (mul_le_mul_of_nonneg_right h3 hA0)
theorem sum_farPart_actionTermsNear_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hinj : ∀ j, j < F.top → Function.Injective (refineSite (F := F) (j := j)))
    {a : ℝ} (ha : 0 ≤ a) {W : F.FieldChain} {k : F.SiteGauge} {K ρ : ℝ} (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2)
    (hsz : CellwiseSizes a S W k K ρ) {Zs : Finset F.Cell} {z : F.Cell} (hz : z ∈ Zs) {P Q : ℝ} (hP : 0 ≤ P)
    (hQ : 0 ≤ Q) {f e g : VariationSlot F → ℝ} (hf : ∀ u, 0 ≤ f u) (he : ∀ u, 0 ≤ e u) (hg0 : ∀ u, 0 ≤ g u)
    (hg : ∀ u, g u ≤ f u * e u) (hF : ScaledQuarticBound S (cellsNear S Zs) P f)
    (hE : QuarticBound S (cellsNear S Zs) Q e) :
    ∑ t ∈ actionTermsNear S Zs, EvaluationSums.farContribution a W k g t ≤
      EvaluationSums.contourSumConstant F.blockSide * (81 * K) * (P * Q) := by
  classical
  obtain ⟨hb, hl⟩ := scaled_sqrt_sum_sq_le hP hQ hf he hg0 hg hF hE
  have hnear : ∀ {t : F.ActionTerm}, t ∈ actionTermsNear S Zs →
      t ∈ actionTerms S ∧ cellSupDist z (actionTermCell t) ≤ 4 := fun ht =>
    ⟨(Finset.mem_filter.1 ht).1, (Finset.mem_filter.1 ht).2 z hz⟩
  refine EvaluationSums.sum_farPart_le hodd hinj ha W k (actionTermsNear S Zs)
    (fun t ht => (Finset.mem_filter.1 ht).1)
    (bondsOnRegion S (cellsNear S Zs)) (fun j => sitesOfCells (cellsNear S Zs) (j + 1)) g hg0 (mul_nonneg hP hQ)
    (by positivity) hρ0 hρ1 ?_ ?_ ?_ ?_ ?_ hb hl
  · intro p hp b hb'
    have hts := (hnear hp).1
    have hread : ReadsSlot (Sum.inl p : F.ActionTerm) (slotOfBond 0 b.1 b.2) := ⟨b, rfl, hb'⟩
    obtain ⟨w1, w2, s1, s2⟩ := supClose_of_readsSlot hodd hts hread
    have m1 : b.1 ∈ sitesOfCells S 0 := by simpa [slotStart, slotOfBond, baseSite_of_level_zero] using s1
    have m2 : b.1 + unitStep 0 b.2 ∈ sitesOfCells S 0 := by
      simpa [slotEnd, slotOfBond, baseSite_of_level_zero] using s2
    exact Finset.mem_filter.2 ⟨mem_innerBonds m1 m2, enclosingCell_mem_cellsNear hamb hodd hp (Nat.zero_le _) m1 w1,
      enclosingCell_mem_cellsNear hamb hodd hp (Nat.zero_le _) m2 w2⟩
  · intro j c ht e' he' π b hb'
    have hts := (hnear ht).1
    have hc := Finset.inr_mem_disjSum.1 hts
    have hj : j < F.top := Finset.mem_range.1 (Finset.mem_sigma.1 hc).1
    have hcb : c ∈ innerBonds S (j + 1) := (Finset.mem_sigma.1 hc).2
    obtain ⟨h1, h2, h3⟩ := mem_innerBonds_of_liesOnPath_bondContour hodd hj hcb he' π hb'
    obtain ⟨m1, m2⟩ := innerBonds_ends h1
    exact Finset.mem_filter.2 ⟨h1, enclosingCell_mem_cellsNear hamb hodd ht hj.le m1 h2,
      enclosingCell_mem_cellsNear hamb hodd ht hj.le m2 h3⟩
  · intro j c ht
    have hts := (hnear ht).1
    have hc := Finset.inr_mem_disjSum.1 hts
    have hj : j < F.top := Finset.mem_range.1 (Finset.mem_sigma.1 hc).1
    have hcb : c ∈ innerBonds S (j + 1) := (Finset.mem_sigma.1 hc).2
    obtain ⟨-, m2⟩ := innerBonds_ends hcb
    exact mem_sitesOfCells_of_enclosingCell_mem hodd m2
      (enclosingCell_mem_cellsNear hamb hodd (j := j + 1) ht hj m2 (supClose_baseSite_add_unitStep hj _ _))
  · have h1 := sum_le_of_near_cells (S := S) (z := z)
      ((innerPlaquettes S 0).filter fun p => (Sum.inl p : F.ActionTerm) ∈ actionTermsNear S Zs)
      (fun p => enclosingCell p.1) (fun p => actionTermSize a W k (Sum.inl p) ^ 2) (fun _ => sq_nonneg _)
      (A := K ^ 2) (sq_nonneg _)
      (fun p hp => by
        have hp' := (Finset.mem_filter.1 hp).2
        have hts := (hnear hp').1
        refine ⟨?_, (hnear hp').2⟩
        have := enclosingCell_actionTermSite hodd hts
        exact this.1)
      (fun v hv => by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _)
          (hsz.plaquette_sum_le v hv)
        intro p hp
        have hp' := Finset.mem_filter.1 hp
        have hp'' := Finset.mem_filter.1 hp'.1
        exact Finset.mem_filter.2 ⟨hp''.1, by simp [hp'.2]⟩)
    refine h1.trans (le_of_eq ?_)
    ring
  · intro j hj
    have h1 := sum_le_of_near_cells (S := S) (z := z)
      ((innerBonds S (j + 1)).filter fun c => (Sum.inr ⟨j, c⟩ : F.ActionTerm) ∈ actionTermsNear S Zs)
      (fun c => enclosingCell c.1) (fun c => actionTermSize a W k (Sum.inr ⟨j, c⟩) ^ 2) (fun _ => sq_nonneg _)
      (A := (K * ρ ^ (F.top - 1 - j)) ^ 2) (sq_nonneg _)
      (fun c hc => by
        have hc' := Finset.mem_filter.1 hc
        have hts := (hnear hc'.2).1
        have hd := (hnear hc'.2).2
        have m1 := (innerBonds_ends hc'.1).1
        have e := enclosingCell_baseSite hodd (j := j + 1) hj m1
        refine ⟨(baseSite_eq_cellCentre_add hodd (j := j + 1) hj m1).1, ?_⟩
        rw [← e]
        exact hd)
      (fun v hv => by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _) (hsz.bond_sum_le j hj v hv)
        intro c hc
        have hc' := Finset.mem_filter.1 hc
        have hc'' := Finset.mem_filter.1 hc'.1
        exact Finset.mem_filter.2 ⟨hc''.1, by simp [hc'.2]⟩)
    refine h1.trans (le_of_eq ?_)
    ring
end YangMills.Construction.BlockAverages.VariationRates
end
