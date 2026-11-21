import YangMills.Construction.ColdChainAtEveryLevel.OffsetsOfSites
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.CellTransport
open BlockAverages BlockAverages.Offsets BlockAverages.SiteOffsets CoordinateSeminorms TwistedTops
variable {F F' : BlockFrame}
structure FramePairing (S : Finset F.Cell) (S' : Finset F'.Cell) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) : Prop where
  blockSide_odd : Odd F.blockSide
  blockSide_eq : F'.blockSide = F.blockSide
  depth_eq : F'.depth = F.depth
  extent_cond : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i
  extent_cond' : ∀ i, F'.extent i = 0 ∨ 2 * r + 2 < F'.extent i
  mem_iff : ∀ h, WithinRadius r h → (Y + siteOfCoords F.top h ∈ S ↔ Y' + siteOfCoords F'.top h ∈ S')
theorem FramePairing.symm {S : Finset F.Cell} {S' : Finset F'.Cell} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ}
    (t : FramePairing S S' Y Y' r) : FramePairing S' S Y' Y r where
  blockSide_odd := t.blockSide_eq ▸ t.blockSide_odd
  blockSide_eq := t.blockSide_eq.symm
  depth_eq := t.depth_eq.symm
  extent_cond := t.extent_cond'
  extent_cond' := t.extent_cond
  mem_iff h hb := (t.mem_iff h hb).symm
variable {S : Finset F.Cell} {S' : Finset F'.Cell} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ}
theorem FramePairing.top_eq (t : FramePairing S S' Y Y' r) : F'.top = F.top := by
  show F'.depth + 1 = F.depth + 1
  rw [t.depth_eq]
theorem exists_cellOffset_decomposition (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}
    (hx : x ∈ sitesOfCells S j) (Y : F.Cell) {d : ℕ}
    (hd : cellSupDist (enclosingCell x) Y ≤ d) :
    ∃ (o h : Fin 4 → ℤ), (∀ i, |o i| ≤ (d : ℤ)) ∧ h ∈ centredCube (F.blockSide ^ (F.top - j)) ∧
      enclosingCell x = Y + siteOfCoords F.top o ∧
      x = siteAtOffset j Y ((fun i => (F.blockSide : ℤ) ^ (F.top - j) * o i) + h) ∧
      ∀ i, (F.blockSide : ℤ) ^ j * (|((fun i => (F.blockSide : ℤ) ^ (F.top - j) * o i) + h) i| + 1) ≤
        ((d + 1 : ℕ) : ℤ) * (F.blockSide : ℤ) ^ F.top := by
  classical
  obtain ⟨y, hy, h, hh, e⟩ := mem_sitesOfCells.1 hx
  have hc : enclosingCell x = y := by
    rw [e]
    exact CoordinateSeminorms.enclosingCell_cellCentre_add hodd y h hh
  rw [hc] at hd
  set o : Fin 4 → ℤ := fun i => (y i - Y i).valMinAbs with ho
  have hyY : y = Y + siteOfCoords F.top o := by
    funext i
    simp only [Pi.add_apply, siteOfCoords, ho, ZMod.coe_valMinAbs]
    abel
  have hle : ∀ i, |o i| ≤ (d : ℤ) := by
    intro i
    have h1 := Finset.le_sup (f := fun i => ((y i - Y i).valMinAbs).natAbs) (Finset.mem_univ i)
    have h2 : ((y i - Y i).valMinAbs).natAbs ≤ d := h1.trans hd
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h2
  have hL0 : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
  have hP : (0 : ℤ) < (F.blockSide : ℤ) ^ (F.top - j) := pow_pos hL0 _
  refine ⟨o, h, hle, hh, by rw [hc]; exact hyY, ?_, fun i => ?_⟩
  · unfold siteAtOffset
    rw [e, hyY, cellCentre_add j hj, _root_.YangMills.Construction.BlockAverages.siteOfCoords_add, add_assoc]
  · have hcube := (LatticePaths.mem_centredCube_iff _ _).1 hh i
    have e3 : ((F.blockSide ^ (F.top - j) : ℕ) : ℤ) = (F.blockSide : ℤ) ^ (F.top - j) := by simp
    rw [e3] at hcube
    have h2 : |h i| + 1 ≤ (F.blockSide : ℤ) ^ (F.top - j) := by
      have e5 : |h i| ≤ ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2 := by
        rw [abs_le]
        exact ⟨hcube.1, hcube.2⟩
      omega
    have h3 : |((fun i => (F.blockSide : ℤ) ^ (F.top - j) * o i) + h) i| + 1 ≤
        ((d : ℤ) + 1) * (F.blockSide : ℤ) ^ (F.top - j) := by
      simp only [Pi.add_apply]
      have h9 := abs_add_le ((F.blockSide : ℤ) ^ (F.top - j) * o i) (h i)
      rw [abs_mul, abs_of_pos hP] at h9
      nlinarith [hle i]
    have hn : (F.blockSide : ℤ) ^ F.top = (F.blockSide : ℤ) ^ j * (F.blockSide : ℤ) ^ (F.top - j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hn]
    have h4 := mul_le_mul_of_nonneg_left h3 (pow_pos hL0 j).le
    push_cast
    refine h4.trans (le_of_eq ?_)
    ring
theorem cellSupDist_add_siteOfCoords_le (Y : F.Cell) (g : Fin 4 → ℤ) {D : ℕ} (hg : ∀ i, |g i| ≤ (D : ℤ)) :
    cellSupDist (Y + siteOfCoords F.top g) Y ≤ D := by
  refine Finset.sup_le fun i _ => ?_
  have e : (Y + siteOfCoords F.top g : F.Cell) i - Y i = ((g i : ℤ) : ZMod (F.period F.top i)) := by
    simp [siteOfCoords]
  rw [e]
  refine (WeightedAverages.Chains.natAbs_valMinAbs_intCast_le _ _).trans ?_
  have := hg i
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this
structure MatchedCells (B : Finset F.Cell) (B' : Finset F'.Cell) (Y : F.Cell) (Y' : F'.Cell) (d : ℕ) : Prop where
  near : ∀ y ∈ B, cellSupDist y Y ≤ d
  near' : ∀ y ∈ B', cellSupDist y Y' ≤ d
  mem_iff : ∀ o : Fin 4 → ℤ, (∀ i, |o i| ≤ (d : ℤ)) →
    (Y + siteOfCoords F.top o ∈ B ↔ Y' + siteOfCoords F'.top o ∈ B')
theorem MatchedCells.symm {B : Finset F.Cell} {B' : Finset F'.Cell} {Y : F.Cell} {Y' : F'.Cell} {d : ℕ}
    (b : MatchedCells B B' Y Y' d) : MatchedCells B' B Y' Y d :=
  ⟨b.near', b.near, fun o ho => (b.mem_iff o ho).symm⟩
theorem exists_translate_bond (t : FramePairing S S' Y Y' r) {B : Finset F.Cell} {B' : Finset F'.Cell} {d : ℕ}
    (hb : MatchedCells B B' Y Y' d) (hd : d + 110 ≤ r) {j : ℕ} (hj : j ≤ F.top)
    (hS : ∀ q : Fin 4 → ℤ, WithinCellRadius F.blockSide F.top (d + 2) j q →
      (siteAtOffset j Y q ∈ sitesOfCells S j ↔ siteAtOffset j Y' q ∈ sitesOfCells S' j))
    {x : F.Site j × Fin 4} (hx : x ∈ bondsOver S B j) :
    ∃ p : Fin 4 → ℤ, x.1 = siteAtOffset j Y p ∧
      (∀ i, (F.blockSide : ℤ) ^ j * (|p i| + 1) ≤ ((d + 1 : ℕ) : ℤ) * (F.blockSide : ℤ) ^ F.top) ∧
      translateSite Y Y' x.1 = siteAtOffset j Y' p ∧ translateSite Y' Y (siteAtOffset j Y' p) = x.1 ∧
      (translateSite Y Y' x.1, x.2) ∈ bondsOver S' B' j := by
  classical
  obtain ⟨hbS, hc⟩ := mem_bondsOver.1 hx
  have hodd := t.blockSide_odd
  have hcd : cellSupDist (enclosingCell x.1) Y ≤ d := hb.near _ hc
  have hx1 : x.1 ∈ sitesOfCells S j := (Finset.mem_product.1 (Finset.mem_filter.1 hbS).1).1
  obtain ⟨o, h, ho, hh, hco, ex, hw2⟩ := exists_cellOffset_decomposition hodd hj hx1 Y hcd
  set p : Fin 4 → ℤ := (fun i => (F.blockSide : ℤ) ^ (F.top - j) * o i) + h with hp
  have hL0 : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
  have hw' : WithinCellRadius F.blockSide F.top (d + 1) j p := by
    intro i
    have h3 := hw2 i
    have h4 : (F.blockSide : ℤ) ^ j * |p i| ≤ (F.blockSide : ℤ) ^ j * (|p i| + 1) :=
      mul_le_mul_of_nonneg_left (by omega) (pow_pos hL0 j).le
    exact h4.trans h3
  have hsideρ : ∀ i, F.extent i = 0 ∨ 2 * (d + 1) + 2 < F.extent i :=
    fun i => (t.extent_cond i).imp id fun e => by omega
  have hsideρ' : ∀ i, F'.extent i = 0 ∨ 2 * (d + 1) + 2 < F'.extent i :=
    fun i => (t.extent_cond' i).imp id fun e => by omega
  have e1 : translateSite Y Y' x.1 = siteAtOffset j Y' p := by
    rw [ex]
    exact translateSite_siteAtOffset hodd.pos hj Y Y' hsideρ hw'
  have hn := t.top_eq
  have hj' : j ≤ F'.top := hn ▸ hj
  have hw'' : WithinCellRadius F'.blockSide F'.top (d + 1) j p := by
    rw [t.blockSide_eq, hn]
    exact hw'
  have e2 : translateSite Y' Y (siteAtOffset j Y' p) = x.1 := by
    rw [ex]
    exact translateSite_siteAtOffset (t.blockSide_eq ▸ hodd.pos) hj' Y' Y hsideρ' hw''
  refine ⟨p, ex, hw2, e1, e2, ?_⟩
  have hside9 : ∀ i, F.extent i = 0 ∨ 2 * (d + 2) + 2 < F.extent i :=
    fun i => (t.extent_cond i).imp id fun e => by omega
  have hbond := translateSite_mem_innerBonds hodd t.blockSide_eq t.depth_eq hj hside9 hS hbS hcd
  refine mem_bondsOver.2 ⟨hbond, ?_⟩
  have hcube' : h ∈ centredCube (F'.blockSide ^ (F'.top - j)) := by
    rw [t.blockSide_eq, hn]
    exact hh
  have hp' : siteAtOffset j Y' p = cellCentre j (Y' + siteOfCoords F'.top o) + siteOfCoords j h := by
    unfold siteAtOffset
    rw [cellCentre_add j hj', add_assoc, ← _root_.YangMills.Construction.BlockAverages.siteOfCoords_add]
    have e : (fun i => (F'.blockSide : ℤ) ^ (F'.top - j) * o i) + h = p := by
      rw [t.blockSide_eq, hn]
    rw [e]
  have hcell' : enclosingCell (siteAtOffset j Y' p) = Y' + siteOfCoords F'.top o := by
    rw [hp']
    exact CoordinateSeminorms.enclosingCell_cellCentre_add (t.blockSide_eq ▸ hodd) _ h hcube'
  show enclosingCell (translateSite Y Y' x.1) ∈ _
  rw [e1, hcell']
  refine (hb.mem_iff o ho).1 ?_
  rw [← hco]
  exact hc
theorem sum_bondsOver_eq (t : FramePairing S S' Y Y' r) {B : Finset F.Cell} {B' : Finset F'.Cell} {d : ℕ}
    (hb : MatchedCells B B' Y Y' d) (hd : d + 110 ≤ r) {j : ℕ} (hj : j ≤ F.top)
    (hS : ∀ q : Fin 4 → ℤ, WithinCellRadius F.blockSide F.top (d + 2) j q →
      (siteAtOffset j Y q ∈ sitesOfCells S j ↔ siteAtOffset j Y' q ∈ sitesOfCells S' j))
    (f : F.Site j × Fin 4 → ℂ) (f' : F'.Site j × Fin 4 → ℂ)
    (hf : ∀ (p : Fin 4 → ℤ) (i : Fin 4),
      (∀ l, (F.blockSide : ℤ) ^ j * (|p l| + 1) ≤ ((d + 1 : ℕ) : ℤ) * (F.blockSide : ℤ) ^ F.top) →
      (siteAtOffset j Y p, i) ∈ innerBonds S j → f (siteAtOffset j Y p, i) = f' (siteAtOffset j Y' p, i)) :
    ∑ x ∈ bondsOver S B j, f x = ∑ x ∈ bondsOver S' B' j, f' x := by
  have hn := t.top_eq
  have hj' : j ≤ F'.top := hn ▸ hj
  have hS' : ∀ q : Fin 4 → ℤ, WithinCellRadius F'.blockSide F'.top (d + 2) j q →
      (siteAtOffset j Y' q ∈ sitesOfCells S' j ↔ siteAtOffset j Y q ∈ sitesOfCells S j) := fun q hq =>
    (hS q (by rw [t.blockSide_eq, hn] at hq; exact hq)).symm
  refine Finset.sum_nbij' (fun x => (translateSite Y Y' x.1, x.2)) (fun x => (translateSite Y' Y x.1, x.2))
    (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨p, -, -, -, -, h5⟩ := exists_translate_bond t hb hd hj hS hx
    exact h5
  · obtain ⟨p, -, -, -, -, h5⟩ := exists_translate_bond t.symm hb.symm hd hj' hS' hx
    exact h5
  · obtain ⟨p, h1, h2, h3, h4, -⟩ := exists_translate_bond t hb hd hj hS hx
    show (translateSite Y' Y (translateSite Y Y' x.1), x.2) = x
    rw [h3, h4]
  · obtain ⟨p, h1, h2, h3, h4, -⟩ := exists_translate_bond t.symm hb.symm hd hj' hS' hx
    show (translateSite Y Y' (translateSite Y' Y x.1), x.2) = x
    rw [h3, h4]
  · obtain ⟨p, h1, h2, h3, h4, -⟩ := exists_translate_bond t hb hd hj hS hx
    show f x = f' (translateSite Y Y' x.1, x.2)
    rw [h3]
    have e : x = (siteAtOffset j Y p, x.2) := Prod.ext h1 rfl
    have hx' := (mem_bondsOver.1 hx).1
    rw [e] at hx' ⊢
    exact hf p x.2 h2 hx'
theorem exists_translate_plaquette (t : FramePairing S S' Y Y' r) {B : Finset F.Cell} {B' : Finset F'.Cell}
    {d : ℕ} (hb : MatchedCells B B' Y Y' d) (hd : d + 110 ≤ r)
    (hS : ∀ q : Fin 4 → ℤ, WithinCellRadius F.blockSide F.top (d + 3) 0 q →
      (siteAtOffset 0 Y q ∈ sitesOfCells S 0 ↔ siteAtOffset 0 Y' q ∈ sitesOfCells S' 0))
    {q : F.Site 0 × Fin 4 × Fin 4} (hq : q ∈ plaquettesOver S B 0) :
    ∃ p : Fin 4 → ℤ, q.1 = siteAtOffset 0 Y p ∧
      (∀ i, |p i| + 1 ≤ ((d + 1 : ℕ) : ℤ) * (F.blockSide : ℤ) ^ F.top) ∧
      translateSite Y Y' q.1 = siteAtOffset 0 Y' p ∧ translateSite Y' Y (siteAtOffset 0 Y' p) = q.1 ∧
      (translateSite Y Y' q.1, q.2) ∈ plaquettesOver S' B' 0 := by
  classical
  obtain ⟨hq1, hq2⟩ := mem_plaquettesOver.1 hq
  obtain ⟨hq3, hq4⟩ := Finset.mem_filter.1 hq1
  have hc := hq4.2
  have c0 : q.1 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c1 : q.1 + unitStep 0 q.2.1 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c2 : q.1 + unitStep 0 q.2.2 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c3 : q.1 + unitStep 0 q.2.1 + unitStep 0 q.2.2 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have hbond : (q.1, q.2.1) ∈ bondsOver S B 0 := by
    refine mem_bondsOver.2 ⟨?_, hq2⟩
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨c0, c1⟩
  have hL0 : (0 : ℤ) < F.blockSide := by exact_mod_cast t.blockSide_odd.pos
  have hup : ∀ {x : Fin 4 → ℤ} {k k' : ℕ}, k ≤ k' → WithinCellRadius F.blockSide F.top k 0 x →
      WithinCellRadius F.blockSide F.top k' 0 x :=
    fun {x k k'} hk hx i => (hx i).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (pow_pos hL0 _).le)
  obtain ⟨p, ep, hp1, e1, e2, hb'⟩ :=
    exists_translate_bond t hb hd (Nat.zero_le _) (fun x hx => hS x (hup (by omega) hx)) hbond
  simp only at ep e1 e2 hb'
  have hp1' : ∀ i, |p i| + 1 ≤ ((d + 1 : ℕ) : ℤ) * (F.blockSide : ℤ) ^ F.top := fun i => by
    simpa using hp1 i
  refine ⟨p, ep, hp1', e1, e2, ?_⟩
  obtain ⟨hb1, hb2⟩ := mem_bondsOver.1 hb'
  refine mem_plaquettesOver.2 ⟨?_, hb2⟩
  have hw : WithinCellRadius F.blockSide F.top (d + 1) 0 p := fun i => by
    have := hp1' i
    rw [pow_zero, one_mul]
    omega
  have hw1 := withinCellRadius_add_single t.blockSide_odd.pos (Nat.zero_le _) hw q.2.1
  have hw2 := withinCellRadius_add_single t.blockSide_odd.pos (Nat.zero_le _) hw q.2.2
  have hw3 := withinCellRadius_add_single t.blockSide_odd.pos (Nat.zero_le _) hw1 q.2.2
  have ea : ∀ (x : Fin 4 → ℤ) (i : Fin 4) {F₁ : BlockFrame} (Y₁ : F₁.Cell),
      siteAtOffset 0 Y₁ x + unitStep 0 i = siteAtOffset 0 Y₁ (x + Pi.single i 1) := by
    intro x i F₁ Y₁
    unfold siteAtOffset
    rw [_root_.YangMills.Construction.BlockAverages.siteOfCoords_add, add_assoc]
    rfl
  have d0 : siteAtOffset 0 Y' p ∈ sitesOfCells S' 0 := (hS p (hup (by omega) hw)).1 (ep ▸ c0)
  have d1 : siteAtOffset 0 Y' p + unitStep 0 q.2.1 ∈ sitesOfCells S' 0 := by
    rw [ea]
    refine (hS _ (hup (by omega) hw1)).1 ?_
    rw [← ea, ← ep]
    exact c1
  have d2 : siteAtOffset 0 Y' p + unitStep 0 q.2.2 ∈ sitesOfCells S' 0 := by
    rw [ea]
    refine (hS _ (hup (by omega) hw2)).1 ?_
    rw [← ea, ← ep]
    exact c2
  have d3 : siteAtOffset 0 Y' p + unitStep 0 q.2.1 + unitStep 0 q.2.2 ∈ sitesOfCells S' 0 := by
    rw [ea, ea]
    refine (hS _ hw3).1 ?_
    rw [← ea, ← ea, ← ep]
    exact c3
  rw [e1]
  simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  refine ⟨d0, hq4.1, fun x hx => ?_⟩
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact d0
  · exact d1
  · exact d2
  · exact d3
theorem sum_plaquettesOver_eq (t : FramePairing S S' Y Y' r) {B : Finset F.Cell} {B' : Finset F'.Cell} {d : ℕ}
    (hb : MatchedCells B B' Y Y' d) (hd : d + 110 ≤ r)
    (hS : ∀ q : Fin 4 → ℤ, WithinCellRadius F.blockSide F.top (d + 3) 0 q →
      (siteAtOffset 0 Y q ∈ sitesOfCells S 0 ↔ siteAtOffset 0 Y' q ∈ sitesOfCells S' 0))
    (f : F.Site 0 × Fin 4 × Fin 4 → ℂ) (f' : F'.Site 0 × Fin 4 × Fin 4 → ℂ)
    (hf : ∀ (p : Fin 4 → ℤ) (μ ν : Fin 4), (∀ i, |p i| + 1 ≤ ((d + 1 : ℕ) : ℤ) * (F.blockSide : ℤ) ^ F.top) →
      (siteAtOffset 0 Y p, μ, ν) ∈ innerPlaquettes S 0 →
        f (siteAtOffset 0 Y p, μ, ν) = f' (siteAtOffset 0 Y' p, μ, ν)) :
    ∑ x ∈ plaquettesOver S B 0, f x = ∑ x ∈ plaquettesOver S' B' 0, f' x := by
  have hn := t.top_eq
  have hS' : ∀ q : Fin 4 → ℤ, WithinCellRadius F'.blockSide F'.top (d + 3) 0 q →
      (siteAtOffset 0 Y' q ∈ sitesOfCells S' 0 ↔ siteAtOffset 0 Y q ∈ sitesOfCells S 0) := fun q hq =>
    (hS q (by rw [t.blockSide_eq, hn] at hq; exact hq)).symm
  refine Finset.sum_nbij' (fun x => (translateSite Y Y' x.1, x.2)) (fun x => (translateSite Y' Y x.1, x.2))
    (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨p, -, -, -, -, h5⟩ := exists_translate_plaquette t hb hd hS hx
    exact h5
  · obtain ⟨p, -, -, -, -, h5⟩ := exists_translate_plaquette t.symm hb.symm hd hS' hx
    exact h5
  · obtain ⟨p, h1, h2, h3, h4, -⟩ := exists_translate_plaquette t hb hd hS hx
    show (translateSite Y' Y (translateSite Y Y' x.1), x.2) = x
    rw [h3, h4]
  · obtain ⟨p, h1, h2, h3, h4, -⟩ := exists_translate_plaquette t.symm hb.symm hd hS' hx
    show (translateSite Y Y' (translateSite Y' Y x.1), x.2) = x
    rw [h3, h4]
  · obtain ⟨p, h1, h2, h3, h4, -⟩ := exists_translate_plaquette t hb hd hS hx
    show f x = f' (translateSite Y Y' x.1, x.2)
    rw [h3]
    have e : x = (siteAtOffset 0 Y p, x.2.1, x.2.2) := Prod.ext h1 rfl
    have hx' := (mem_plaquettesOver.1 hx).1
    rw [e] at hx' ⊢
    exact hf p x.2.1 x.2.2 h2 hx'
end YangMills.Construction.CellTransport
end
