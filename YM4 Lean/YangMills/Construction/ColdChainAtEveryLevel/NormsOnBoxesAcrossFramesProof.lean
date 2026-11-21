import YangMills.Construction.ColdChainAtEveryLevel.BondsAcrossFrames
import YangMills.Construction.ColdChainAtEveryLevel.LinesOfAgreeingPairs
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace BallNormsAcrossFrames
open Offsets CoordinateSeminorms TwistedTops SiteOffsets
variable {F F' : BlockFrame}
structure BallAgreement (S : Finset F.Cell) (S' : Finset F'.Cell) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) : Prop where
  blockSide_odd : Odd F.blockSide
  blockSide_eq : F'.blockSide = F.blockSide
  depth_eq : F'.depth = F.depth
  extent_cond : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i
  extent_cond' : ∀ i, F'.extent i = 0 ∨ 2 * r + 2 < F'.extent i
  mem_iff : ∀ h, WithinRadius r h → (Y + siteOfCoords F.top h ∈ S ↔ Y' + siteOfCoords F'.top h ∈ S')
theorem BallAgreement.symm {S : Finset F.Cell} {S' : Finset F'.Cell} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ}
    (t : BallAgreement S S' Y Y' r) : BallAgreement S' S Y' Y r where
  blockSide_odd := t.blockSide_eq ▸ t.blockSide_odd
  blockSide_eq := t.blockSide_eq.symm
  depth_eq := t.depth_eq.symm
  extent_cond := t.extent_cond'
  extent_cond' := t.extent_cond
  mem_iff h hb := (t.mem_iff h hb).symm
variable {S : Finset F.Cell} {S' : Finset F'.Cell} {Y : F.Cell} {Y' : F'.Cell} {r : ℕ}
theorem BallAgreement.top_eq (t : BallAgreement S S' Y Y' r) : F'.top = F.top := by
  show F'.depth + 1 = F.depth + 1
  rw [t.depth_eq]
theorem exists_siteAtOffset_decomp (hodd : Odd F.blockSide) {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}
    (hx : x ∈ sitesOfCells S j) (Y : F.Cell) {d : ℕ}
    (hd : cellSupDist (enclosingCell x) Y ≤ d) :
    ∃ (o h : Fin 4 → ℤ), (∀ i, |o i| ≤ (d : ℤ)) ∧ h ∈ centredCube (F.blockSide ^ (F.top - j)) ∧
      enclosingCell x = Y + siteOfCoords F.top o ∧
      x = siteAtOffset j Y ((fun i => (F.blockSide : ℤ) ^ (F.top - j) * o i) + h) ∧
      ∀ i, (F.blockSide : ℤ) ^ j * (|((fun i => (F.blockSide : ℤ) ^ (F.top - j) * o i) + h) i| + 1) ≤
        ((d + 1 : ℕ) : ℤ) * (F.blockSide : ℤ) ^ F.top := by apply _root_.YangMills.Construction.CellTransport.exists_cellOffset_decomposition <;> assumption
theorem cellSupDist_add_siteOfCoords_le (Y : F.Cell) (g : Fin 4 → ℤ) {D : ℕ} (hg : ∀ i, |g i| ≤ (D : ℤ)) :
    cellSupDist (Y + siteOfCoords F.top g) Y ≤ D := by apply _root_.YangMills.Construction.CellTransport.cellSupDist_add_siteOfCoords_le <;> assumption
theorem cellSupDist_transfer (t : BallAgreement S S' Y Y' r) {g o : Fin 4 → ℤ} (hg : ∀ i, |g i| + 10 ≤ (r : ℤ))
    (ho : ∀ i, |o i| + 10 ≤ (r : ℤ))
    (h : cellSupDist (Y + siteOfCoords F.top g) (Y + siteOfCoords F.top o) ≤ 4) :
    cellSupDist (Y' + siteOfCoords F'.top g) (Y' + siteOfCoords F'.top o) ≤ 4 := by
  have hdiff : ∀ i, |g i - o i| ≤ 4 := by
    intro i
    set w := (((Y + siteOfCoords F.top g : F.Cell) i - (Y + siteOfCoords F.top o : F.Cell) i)).valMinAbs with hw
    have hwle : |w| ≤ 4 := by
      have h1 := Finset.le_sup (f := fun i => (((Y + siteOfCoords F.top g : F.Cell) i -
        (Y + siteOfCoords F.top o : F.Cell) i).valMinAbs).natAbs) (Finset.mem_univ i)
      have h2 : w.natAbs ≤ 4 := h1.trans h
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h2
    have hcast : ((w : ℤ) : ZMod (F.period F.top i)) = ((g i - o i : ℤ) : ZMod (F.period F.top i)) := by
      rw [hw, ZMod.coe_valMinAbs]
      simp [siteOfCoords]
    have hdvd : ((F.period F.top i : ℕ) : ℤ) ∣ (g i - o i - w) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [← Int.cast_sub, hcast.symm]
      simp
    have hper : F.period F.top i = F.extent i := by simp [BlockFrame.period]
    rw [hper] at hdvd
    have hzero : g i - o i - w = 0 := by
      rcases t.extent_cond i with h0 | h0
      · rw [h0] at hdvd
        simpa using hdvd
      · have h2 : ((2 * r + 2 : ℕ) : ℤ) < (F.extent i : ℤ) := by exact_mod_cast h0
        push_cast at h2
        refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
        have a1 := hg i
        have a2 := ho i
        have a3 : |g i - o i - w| ≤ |g i| + |o i| + |w| := by
          refine (abs_sub _ _).trans ?_
          have := abs_sub (g i) (o i)
          linarith
        omega
    have : g i - o i = w := by omega
    rw [this]
    exact hwle
  refine Finset.sup_le fun i _ => ?_
  have e : (Y' + siteOfCoords F'.top g : F'.Cell) i - (Y' + siteOfCoords F'.top o : F'.Cell) i =
      ((g i - o i : ℤ) : ZMod (F'.period F'.top i)) := by
    simp [siteOfCoords]
  rw [e]
  refine (WeightedAverages.Chains.natAbs_valMinAbs_intCast_le _ _).trans ?_
  have := hdiff i
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this
theorem exists_bond_image (t : BallAgreement S S' Y Y' r) {ρ : ℕ} (hρ : ρ + 100 ≤ r) {j : ℕ} (hj : j ≤ F.top)
    (hS : ∀ q : Fin 4 → ℤ, WithinCellRadius F.blockSide F.top (ρ + 1) j q →
      (siteAtOffset j Y q ∈ sitesOfCells S j ↔ siteAtOffset j Y' q ∈ sitesOfCells S' j))
    {g : Fin 4 → ℤ} (hg : ∀ i, |g i| + 5 ≤ (ρ : ℤ)) {x : F.Site j × Fin 4}
    (hx : x ∈ bondsOver S (cellBall S (Y + siteOfCoords F.top g) 4) j) :
    ∃ p : Fin 4 → ℤ, x.1 = siteAtOffset j Y p ∧ WithinCellRadius F.blockSide F.top ρ j p ∧
      translateSite Y Y' x.1 = siteAtOffset j Y' p ∧ translateSite Y' Y (siteAtOffset j Y' p) = x.1 ∧
      (translateSite Y Y' x.1, x.2) ∈ bondsOver S' (cellBall S' (Y' + siteOfCoords F'.top g) 4) j ∧
      ∀ i, (F.blockSide : ℤ) ^ j * (|p i| + 1) ≤ (ρ : ℤ) * (F.blockSide : ℤ) ^ F.top := by
  classical
  obtain ⟨hb, hc⟩ := CoordinateSeminorms.mem_bondsOver.1 hx
  have hodd := t.blockSide_odd
  have hρ0 : 5 ≤ ρ := by
    have := hg 0
    have h0 := abs_nonneg (g 0)
    omega
  have hgd : cellSupDist (Y + siteOfCoords F.top g) Y ≤ ρ - 5 := cellSupDist_add_siteOfCoords_le Y g fun i => by
    have := hg i
    omega
  have hcd : cellSupDist (enclosingCell x.1) Y ≤ ρ - 1 := by
    have h1 : cellSupDist (Y + siteOfCoords F.top g) (enclosingCell x.1) ≤ 4 := (Finset.mem_filter.1 hc).2
    have h2 := CoordinateSeminorms.cellSupDist_triangle (enclosingCell x.1) (Y + siteOfCoords F.top g) Y
    have h3 : cellSupDist (enclosingCell x.1) (Y + siteOfCoords F.top g) ≤ 4 := by
      rw [CoordinateSeminorms.cellSupDist_comm]
      exact h1
    omega
  have hx1 : x.1 ∈ sitesOfCells S j := (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1
  obtain ⟨o, h, ho, hh, hco, ex, hw⟩ := exists_siteAtOffset_decomp hodd hj hx1 Y hcd
  set p : Fin 4 → ℤ := (fun i => (F.blockSide : ℤ) ^ (F.top - j) * o i) + h with hp
  have hw2 : ∀ i, (F.blockSide : ℤ) ^ j * (|p i| + 1) ≤ (ρ : ℤ) * (F.blockSide : ℤ) ^ F.top := by
    have e9 : ρ - 1 + 1 = ρ := by omega
    rw [e9] at hw
    exact hw
  have hw' : WithinCellRadius F.blockSide F.top ρ j p := by
    intro i
    have hL0 : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
    have h3 := hw2 i
    have h4 : (F.blockSide : ℤ) ^ j * |p i| ≤ (F.blockSide : ℤ) ^ j * (|p i| + 1) :=
      mul_le_mul_of_nonneg_left (by omega) (pow_pos hL0 j).le
    exact h4.trans h3
  have hsideρ : ∀ i, F.extent i = 0 ∨ 2 * ρ + 2 < F.extent i :=
    fun i => (t.extent_cond i).imp id fun e => by omega
  have hsideρ' : ∀ i, F'.extent i = 0 ∨ 2 * ρ + 2 < F'.extent i :=
    fun i => (t.extent_cond' i).imp id fun e => by omega
  have e1 : translateSite Y Y' x.1 = siteAtOffset j Y' p := by
    rw [ex]
    exact translateSite_siteAtOffset hodd.pos hj Y Y' hsideρ hw'
  have hn := t.top_eq
  have hj' : j ≤ F'.top := hn ▸ hj
  have hw'' : WithinCellRadius F'.blockSide F'.top ρ j p := by
    rw [t.blockSide_eq, hn]
    exact hw'
  have e2 : translateSite Y' Y (siteAtOffset j Y' p) = x.1 := by
    rw [ex]
    exact translateSite_siteAtOffset (t.blockSide_eq ▸ hodd.pos) hj' Y' Y hsideρ' hw''
  refine ⟨p, ex, hw', e1, e2, ?_, hw2⟩
  have hside9 : ∀ i, F.extent i = 0 ∨ 2 * (ρ - 1 + 2) + 2 < F.extent i :=
    fun i => (t.extent_cond i).imp id fun e => by omega
  have hbond := translateSite_mem_innerBonds hodd t.blockSide_eq t.depth_eq hj hside9 (fun q hq => by
    have e3 : ρ - 1 + 2 = ρ + 1 := by omega
    rw [e3] at hq
    exact hS q hq) hb hcd
  refine CoordinateSeminorms.mem_bondsOver.2 ⟨hbond, ?_⟩
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
  have hin : Y' + siteOfCoords F'.top o ∈ S' := by
    rw [← hcell']
    have h1 : siteAtOffset j Y' p ∈ sitesOfCells S' j := (hS p (fun i => (hw' i).trans (by
      have hL0 : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
      exact mul_le_mul_of_nonneg_right (by push_cast; omega) (pow_pos hL0 _).le))).1 (by rw [← ex]; exact hx1)
    exact CoordinateSeminorms.enclosingCell_mem (t.blockSide_eq ▸ hodd) h1
  refine Finset.mem_filter.2 ⟨hin, ?_⟩
  have hcz : cellSupDist (Y + siteOfCoords F.top g) (Y + siteOfCoords F.top o) ≤ 4 := by
    rw [← hco]
    exact (Finset.mem_filter.1 hc).2
  refine cellSupDist_transfer t (fun i => ?_) (fun i => ?_) hcz
  · have := hg i
    have h2 : ((ρ + 100 : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hρ
    push_cast at h2
    omega
  · have := ho i
    have h2 : ((ρ + 100 : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hρ
    push_cast at h2
    omega
theorem sum_bondsOver_eq (t : BallAgreement S S' Y Y' r) {ρ : ℕ} (hρ : ρ + 100 ≤ r) {j : ℕ} (hj : j ≤ F.top)
    (hS : ∀ q : Fin 4 → ℤ, WithinCellRadius F.blockSide F.top (ρ + 1) j q →
      (siteAtOffset j Y q ∈ sitesOfCells S j ↔ siteAtOffset j Y' q ∈ sitesOfCells S' j))
    {g : Fin 4 → ℤ} (hg : ∀ i, |g i| + 5 ≤ (ρ : ℤ)) (f : F.Site j × Fin 4 → ℝ) (f' : F'.Site j × Fin 4 → ℝ)
    (hf : ∀ (p : Fin 4 → ℤ) (i : Fin 4), WithinCellRadius F.blockSide F.top ρ j p →
      f (siteAtOffset j Y p, i) = f' (siteAtOffset j Y' p, i)) :
    ∑ b ∈ bondsOver S (cellBall S (Y + siteOfCoords F.top g) 4) j, f b =
      ∑ b ∈ bondsOver S' (cellBall S' (Y' + siteOfCoords F'.top g) 4) j, f' b := by
  have hn := t.top_eq
  have hj' : j ≤ F'.top := hn ▸ hj
  have hS' : ∀ q : Fin 4 → ℤ, WithinCellRadius F'.blockSide F'.top (ρ + 1) j q →
      (siteAtOffset j Y' q ∈ sitesOfCells S' j ↔ siteAtOffset j Y q ∈ sitesOfCells S j) := fun q hq =>
    (hS q (by rw [t.blockSide_eq, hn] at hq; exact hq)).symm
  refine Finset.sum_nbij' (fun b => (translateSite Y Y' b.1, b.2)) (fun b => (translateSite Y' Y b.1, b.2))
    (fun b hb => ?_) (fun b hb => ?_) (fun b hb => ?_) (fun b hb => ?_) (fun b hb => ?_)
  · obtain ⟨p, -, -, -, -, h5, -⟩ := exists_bond_image t hρ hj hS hg hb
    exact h5
  · obtain ⟨p, -, -, -, -, h5, -⟩ := exists_bond_image t.symm hρ hj' hS' hg hb
    exact h5
  · obtain ⟨p, h1, h2, h3, h4, -, -⟩ := exists_bond_image t hρ hj hS hg hb
    show (translateSite Y' Y (translateSite Y Y' b.1), b.2) = b
    rw [h3, h4]
  · obtain ⟨p, h1, h2, h3, h4, -, -⟩ := exists_bond_image t.symm hρ hj' hS' hg hb
    show (translateSite Y Y' (translateSite Y' Y b.1), b.2) = b
    rw [h3, h4]
  · obtain ⟨p, h1, h2, h3, h4, -, -⟩ := exists_bond_image t hρ hj hS hg hb
    show f b = f' (translateSite Y Y' b.1, b.2)
    rw [h3]
    have e : b = (siteAtOffset j Y p, b.2) := Prod.ext h1 rfl
    rw [e]
    exact hf p b.2 h2
theorem exists_plaquette_image (t : BallAgreement S S' Y Y' r) {ρ : ℕ} (hρ : ρ + 100 ≤ r)
    (hS : ∀ q : Fin 4 → ℤ, WithinCellRadius F.blockSide F.top (ρ + 2) 0 q →
      (siteAtOffset 0 Y q ∈ sitesOfCells S 0 ↔ siteAtOffset 0 Y' q ∈ sitesOfCells S' 0))
    {g : Fin 4 → ℤ} (hg : ∀ i, |g i| + 5 ≤ (ρ : ℤ)) {q : F.Site 0 × Fin 4 × Fin 4}
    (hq : q ∈ plaquettesOver S (cellBall S (Y + siteOfCoords F.top g) 4) 0) :
    ∃ p : Fin 4 → ℤ, q.1 = siteAtOffset 0 Y p ∧ (∀ i, |p i| + 1 ≤ (ρ : ℤ) * (F.blockSide : ℤ) ^ F.top) ∧
      translateSite Y Y' q.1 = siteAtOffset 0 Y' p ∧ translateSite Y' Y (siteAtOffset 0 Y' p) = q.1 ∧
      (translateSite Y Y' q.1, q.2) ∈ plaquettesOver S' (cellBall S' (Y' + siteOfCoords F'.top g) 4) 0 := by
  classical
  obtain ⟨hq1, hq2⟩ := CoordinateSeminorms.mem_plaquettesOver.1 hq
  obtain ⟨hq3, hq4⟩ := Finset.mem_filter.1 hq1
  have hc := hq4.2
  have c0 : q.1 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c1 : q.1 + unitStep 0 q.2.1 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c2 : q.1 + unitStep 0 q.2.2 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c3 : q.1 + unitStep 0 q.2.1 + unitStep 0 q.2.2 ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have hbond : (q.1, q.2.1) ∈ bondsOver S (cellBall S (Y + siteOfCoords F.top g) 4) 0 := by
    refine CoordinateSeminorms.mem_bondsOver.2 ⟨?_, hq2⟩
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨c0, c1⟩
  have hL0 : (0 : ℤ) < F.blockSide := by exact_mod_cast t.blockSide_odd.pos
  have hS1 : ∀ x : Fin 4 → ℤ, WithinCellRadius F.blockSide F.top (ρ + 1) 0 x →
      (siteAtOffset 0 Y x ∈ sitesOfCells S 0 ↔ siteAtOffset 0 Y' x ∈ sitesOfCells S' 0) := fun x hx => hS x fun i =>
    (hx i).trans (mul_le_mul_of_nonneg_right (by push_cast; omega) (pow_pos hL0 _).le)
  obtain ⟨p, ep, hw, e1, e2, hb', hp1⟩ := exists_bond_image t hρ (Nat.zero_le _) hS1 hg hbond
  simp only at ep e1 e2 hb'
  have hp1' : ∀ i, |p i| + 1 ≤ (ρ : ℤ) * (F.blockSide : ℤ) ^ F.top := fun i => by
    simpa using hp1 i
  refine ⟨p, ep, hp1', e1, e2, ?_⟩
  obtain ⟨hb1, hb2⟩ := CoordinateSeminorms.mem_bondsOver.1 hb'
  refine CoordinateSeminorms.mem_plaquettesOver.2 ⟨?_, hb2⟩
  have hw1 := withinCellRadius_add_single t.blockSide_odd.pos (Nat.zero_le _) hw q.2.1
  have hw2 := withinCellRadius_add_single t.blockSide_odd.pos (Nat.zero_le _) hw q.2.2
  have hw3 := withinCellRadius_add_single t.blockSide_odd.pos (Nat.zero_le _) hw1 q.2.2
  have hmono : ∀ {x : Fin 4 → ℤ}, WithinCellRadius F.blockSide F.top (ρ + 1) 0 x →
      WithinCellRadius F.blockSide F.top (ρ + 2) 0 x := fun {x} hx i =>
    (hx i).trans (mul_le_mul_of_nonneg_right (by push_cast; omega) (pow_pos hL0 _).le)
  have hmono0 : WithinCellRadius F.blockSide F.top (ρ + 2) 0 p := fun i =>
    (hw i).trans (mul_le_mul_of_nonneg_right (by push_cast; omega) (pow_pos hL0 _).le)
  have ea : ∀ (x : Fin 4 → ℤ) (i : Fin 4) {F₁ : BlockFrame} (Y₁ : F₁.Cell),
      siteAtOffset 0 Y₁ x + unitStep 0 i = siteAtOffset 0 Y₁ (x + Pi.single i 1) := by
    intro x i F₁ Y₁
    unfold siteAtOffset
    rw [_root_.YangMills.Construction.BlockAverages.siteOfCoords_add, add_assoc]
    rfl
  have d0 : siteAtOffset 0 Y' p ∈ sitesOfCells S' 0 := (hS p hmono0).1 (ep ▸ c0)
  have d1 : siteAtOffset 0 Y' p + unitStep 0 q.2.1 ∈ sitesOfCells S' 0 := by
    rw [ea]
    refine (hS _ (hmono hw1)).1 ?_
    rw [← ea, ← ep]
    exact c1
  have d2 : siteAtOffset 0 Y' p + unitStep 0 q.2.2 ∈ sitesOfCells S' 0 := by
    rw [ea]
    refine (hS _ (hmono hw2)).1 ?_
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
theorem sum_plaquettesOver_eq (t : BallAgreement S S' Y Y' r) {ρ : ℕ} (hρ : ρ + 100 ≤ r)
    (hS : ∀ q : Fin 4 → ℤ, WithinCellRadius F.blockSide F.top (ρ + 2) 0 q →
      (siteAtOffset 0 Y q ∈ sitesOfCells S 0 ↔ siteAtOffset 0 Y' q ∈ sitesOfCells S' 0))
    {g : Fin 4 → ℤ} (hg : ∀ i, |g i| + 5 ≤ (ρ : ℤ)) (f : F.Site 0 × Fin 4 × Fin 4 → ℝ)
    (f' : F'.Site 0 × Fin 4 × Fin 4 → ℝ)
    (hf : ∀ (p : Fin 4 → ℤ) (μ ν : Fin 4), (∀ i, |p i| + 1 ≤ (ρ : ℤ) * (F.blockSide : ℤ) ^ F.top) →
      (siteAtOffset 0 Y p, μ, ν) ∈ innerPlaquettes S 0 →
        f (siteAtOffset 0 Y p, μ, ν) = f' (siteAtOffset 0 Y' p, μ, ν)) :
    ∑ b ∈ plaquettesOver S (cellBall S (Y + siteOfCoords F.top g) 4) 0, f b =
      ∑ b ∈ plaquettesOver S' (cellBall S' (Y' + siteOfCoords F'.top g) 4) 0, f' b := by
  have hn := t.top_eq
  have hS' : ∀ q : Fin 4 → ℤ, WithinCellRadius F'.blockSide F'.top (ρ + 2) 0 q →
      (siteAtOffset 0 Y' q ∈ sitesOfCells S' 0 ↔ siteAtOffset 0 Y q ∈ sitesOfCells S 0) := fun q hq =>
    (hS q (by rw [t.blockSide_eq, hn] at hq; exact hq)).symm
  refine Finset.sum_nbij' (fun b => (translateSite Y Y' b.1, b.2)) (fun b => (translateSite Y' Y b.1, b.2))
    (fun b hb => ?_) (fun b hb => ?_) (fun b hb => ?_) (fun b hb => ?_) (fun b hb => ?_)
  · obtain ⟨p, -, -, -, -, h5⟩ := exists_plaquette_image t hρ hS hg hb
    exact h5
  · obtain ⟨p, -, -, -, -, h5⟩ := exists_plaquette_image t.symm hρ hS' hg hb
    exact h5
  · obtain ⟨p, h1, h2, h3, h4, -⟩ := exists_plaquette_image t hρ hS hg hb
    show (translateSite Y' Y (translateSite Y Y' b.1), b.2) = b
    rw [h3, h4]
  · obtain ⟨p, h1, h2, h3, h4, -⟩ := exists_plaquette_image t.symm hρ hS' hg hb
    show (translateSite Y Y' (translateSite Y' Y b.1), b.2) = b
    rw [h3, h4]
  · obtain ⟨p, h1, h2, h3, h4, -⟩ := exists_plaquette_image t hρ hS hg hb
    show f b = f' (translateSite Y Y' b.1, b.2)
    rw [h3]
    have e : b = (siteAtOffset 0 Y p, b.2.1, b.2.2) := Prod.ext h1 rfl
    have hb' := (CoordinateSeminorms.mem_plaquettesOver.1 hb).1
    rw [e] at hb' ⊢
    exact hf p b.2.1 b.2.2 h2 hb'
end BallNormsAcrossFrames
open BallNormsAcrossFrames Offsets CoordinateSeminorms in
theorem localNormSqOnBallsAcrossFrames_proof (hLines : agreeingPairsLocalityStatement)
    (hSt : sitesOfCellsAcrossFramesStatement) :
    localNormSqOnBallsAcrossFramesStatement := by
  obtain ⟨c, hc, hl⟩ := hLines
  refine ⟨c, hc, ?_⟩
  intro F F' m S S' s V V' Y Y' r ρ hL ht hodd hamb hamb' hm hreg hreg' hs hsc hcold hcold' hagree hρ A A' hA g hg
  have t : BallAgreement S S' Y Y' r := ⟨hodd, hL, ht, hagree.1, hagree.2.1, hagree.2.2.1⟩
  have hrefs := (hl F F' m S S' s V V' Y Y' r hL ht hodd hamb hamb' hm hreg hreg' hs hsc hcold hcold' hagree).2
  have hS : ∀ (j k : ℕ), j ≤ F.top → k + 2 ≤ r → ∀ q : Fin 4 → ℤ, WithinCellRadius F.blockSide F.top k j q →
      (siteAtOffset j Y q ∈ sitesOfCells S j ↔ siteAtOffset j Y' q ∈ sitesOfCells S' j) := fun j k hj hk q hq =>
    hSt F F' S S' V V' Y Y' r k j hL ht hodd hj hagree hk q hq
  have hn := t.top_eq
  have hL0 : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
  have e1 : ∑ b ∈ bondsOver S (cellBall S (Y + siteOfCoords F.top g) 4) 0, (1 * ‖A.fine b.1 b.2‖) ^ 4 =
      ∑ b ∈ bondsOver S' (cellBall S' (Y' + siteOfCoords F'.top g) 4) 0, (1 * ‖A'.fine b.1 b.2‖) ^ 4 :=
    sum_bondsOver_eq t hρ (Nat.zero_le _) (hS 0 (ρ + 1) (Nat.zero_le _) (by omega)) hg
      (fun b => (1 * ‖A.fine b.1 b.2‖) ^ 4) (fun b => (1 * ‖A'.fine b.1 b.2‖) ^ 4)
      (fun p i hp => by simp only; rw [hA.fine p i hp])
  have e3 : ∑ j ∈ Finset.range (F.top - 1), ∑ b ∈ bondsOver S (cellBall S (Y + siteOfCoords F.top g) 4) (j + 1),
        (1 * ‖A.coarse j b.1 b.2‖) ^ 2 =
      ∑ j ∈ Finset.range (F'.top - 1), ∑ b ∈ bondsOver S' (cellBall S' (Y' + siteOfCoords F'.top g) 4) (j + 1),
        (1 * ‖A'.coarse j b.1 b.2‖) ^ 2 := by
    have hr₀ : Finset.range (F'.top - 1) = Finset.range (F.top - 1) := by rw [hn]
    rw [hr₀]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j + 1 < F.top := by
      have := Finset.mem_range.1 hj
      omega
    exact sum_bondsOver_eq t hρ hj'.le (hS (j + 1) (ρ + 1) hj'.le (by omega)) hg
      (fun b => (1 * ‖A.coarse j b.1 b.2‖) ^ 2) (fun b => (1 * ‖A'.coarse j b.1 b.2‖) ^ 2)
      (fun p i hp => by simp only; rw [hA.coarse j p i hj' hp])
  have hR0 : referenceFieldChain S V 0 = referenceGaugeField S V 0 := by
    unfold referenceFieldChain
    exact Function.update_of_ne (by
      have : F.top = F.depth + 1 := rfl
      omega) _ _
  have hR0' : referenceFieldChain S' V' 0 = referenceGaugeField S' V' 0 := by
    unfold referenceFieldChain
    exact Function.update_of_ne (by
      have : F'.top = F'.depth + 1 := rfl
      omega) _ _
  have e2 : ∑ p ∈ plaquettesOver S (cellBall S (Y + siteOfCoords F.top g) 4) 0,
        (1 * ‖linearizedCurl (referenceFieldChain S V 0) A.fine p‖) ^ 2 =
      ∑ p ∈ plaquettesOver S' (cellBall S' (Y' + siteOfCoords F'.top g) 4) 0,
        (1 * ‖linearizedCurl (referenceFieldChain S' V' 0) A'.fine p‖) ^ 2 := by
    refine sum_plaquettesOver_eq t hρ (hS 0 (ρ + 2) (Nat.zero_le _) (by omega)) hg _ _ fun p μ ν hp hq => ?_
    obtain ⟨hq3, hq4⟩ := Finset.mem_filter.1 hq
    have hlt : μ < ν := hq4.1
    have hc := hq4.2
    have c0 : siteAtOffset 0 Y p ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
    have c1 : siteAtOffset 0 Y p + unitStep 0 μ ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
    have c2 : siteAtOffset 0 Y p + unitStep 0 ν ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
    have c3 : siteAtOffset 0 Y p + unitStep 0 μ + unitStep 0 ν ∈ sitesOfCells S 0 :=
      hc (by simp [plaquetteCorners])
    have c3' : siteAtOffset 0 Y p + unitStep 0 ν + unitStep 0 μ ∈ sitesOfCells S 0 := by
      have e : siteAtOffset 0 Y p + unitStep 0 ν + unitStep 0 μ =
          siteAtOffset 0 Y p + unitStep 0 μ + unitStep 0 ν := by abel
      rw [e]
      exact c3
    have hN1 : (0 : ℤ) ≤ (F.blockSide : ℤ) ^ F.top := (pow_pos hL0 _).le
    have hρr : (ρ : ℤ) ≤ (r : ℤ) - 100 := by
      have : ((ρ + 100 : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hρ
      push_cast at this
      omega
    have hinner : ∀ x : Fin 4 → ℤ, (∀ i, |x i| ≤ |p i| + 1) → IsInnerOffset F.blockSide F.top r 0 x := by
      intro x hx i
      rw [pow_zero, one_mul]
      exact ((hx i).trans (hp i)).trans (mul_le_mul_of_nonneg_right hρr hN1)
    have hwith : ∀ x : Fin 4 → ℤ, (∀ i, |x i| ≤ |p i| + 1) → WithinCellRadius F.blockSide F.top ρ 0 x := by
      intro x hx i
      rw [pow_zero, one_mul]
      exact (hx i).trans (hp i)
    have hs1 : ∀ (i l : Fin 4), |(Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ 1 := by
      intro i l
      by_cases h : l = i
      · subst h
        simp
      · simp [h]
    have hne : μ ≠ ν := hlt.ne
    have b0 : ∀ l, |p l| ≤ |p l| + 1 := fun l => by omega
    have b1 : ∀ (i l : Fin 4), |(p + (Pi.single i 1 : Fin 4 → ℤ)) l| ≤ |p l| + 1 := fun i l => by
      simp only [Pi.add_apply]
      refine (abs_add_le _ _).trans ?_
      linarith [hs1 i l]
    have b2 : ∀ l, |(p + (Pi.single μ 1 : Fin 4 → ℤ) + (Pi.single ν 1 : Fin 4 → ℤ)) l| ≤ |p l| + 1 := fun l => by
      by_cases h1 : l = μ
      · subst h1
        have : (Pi.single ν (1 : ℤ) : Fin 4 → ℤ) l = 0 := by simp [hne]
        simp only [Pi.add_apply, this, add_zero]
        exact b1 l l
      · have : (Pi.single μ (1 : ℤ) : Fin 4 → ℤ) l = 0 := by simp [h1]
        simp only [Pi.add_apply, this, add_zero]
        exact b1 ν l
    have b3 : ∀ l, |(p + (Pi.single ν 1 : Fin 4 → ℤ) + (Pi.single μ 1 : Fin 4 → ℤ)) l| ≤ |p l| + 1 := fun l => by
      have e : p + (Pi.single ν 1 : Fin 4 → ℤ) + (Pi.single μ 1 : Fin 4 → ℤ) =
          p + (Pi.single μ 1 : Fin 4 → ℤ) + (Pi.single ν 1 : Fin 4 → ℤ) := by abel
      rw [e]
      exact b2 l
    have ea : ∀ (x : Fin 4 → ℤ) (i : Fin 4) {F₁ : BlockFrame} (Y₁ : F₁.Cell),
        siteAtOffset 0 Y₁ x + unitStep 0 i = siteAtOffset 0 Y₁ (x + Pi.single i 1) := by
      intro x i F₁ Y₁
      unfold siteAtOffset
      rw [_root_.YangMills.Construction.BlockAverages.siteOfCoords_add, add_assoc]
      rfl
    have a1 : A.fine (siteAtOffset 0 Y p) μ = A'.fine (siteAtOffset 0 Y' p) μ := hA.fine p μ (hwith p b0)
    have a4 : A.fine (siteAtOffset 0 Y p) ν = A'.fine (siteAtOffset 0 Y' p) ν := hA.fine p ν (hwith p b0)
    have a2 : A.fine (siteAtOffset 0 Y p + unitStep 0 μ) ν = A'.fine (siteAtOffset 0 Y' p + unitStep 0 μ) ν := by
      rw [ea, ea]
      exact hA.fine _ ν (hwith _ (b1 μ))
    have a3 : A.fine (siteAtOffset 0 Y p + unitStep 0 ν) μ = A'.fine (siteAtOffset 0 Y' p + unitStep 0 ν) μ := by
      rw [ea, ea]
      exact hA.fine _ μ (hwith _ (b1 ν))
    have hbond : ∀ (x : Fin 4 → ℤ) (i : Fin 4), siteAtOffset 0 Y x ∈ sitesOfCells S 0 →
        siteAtOffset 0 Y x + unitStep 0 i ∈ sitesOfCells S 0 →
          (cellCentre 0 Y + siteOfCoords 0 x, i) ∈ innerBonds S 0 := by
      intro x i h1 h2
      simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      exact ⟨h1, h2⟩
    have hz : 0 < F.top := Nat.succ_pos _
    have r1 : referenceGaugeField S V 0 (siteAtOffset 0 Y p) μ =
        referenceGaugeField S' V' 0 (siteAtOffset 0 Y' p) μ :=
      hrefs 0 p μ hz (hinner _ b0) (hinner _ (b1 μ)) (hbond p μ c0 c1)
    have r4 : referenceGaugeField S V 0 (siteAtOffset 0 Y p) ν =
        referenceGaugeField S' V' 0 (siteAtOffset 0 Y' p) ν :=
      hrefs 0 p ν hz (hinner _ b0) (hinner _ (b1 ν)) (hbond p ν c0 c2)
    have r2 : referenceGaugeField S V 0 (siteAtOffset 0 Y p + unitStep 0 μ) ν =
        referenceGaugeField S' V' 0 (siteAtOffset 0 Y' p + unitStep 0 μ) ν := by
      rw [ea, ea]
      refine hrefs 0 _ ν hz (hinner _ (b1 μ)) (hinner _ b2) (hbond _ ν ?_ ?_)
      · rw [← ea]
        exact c1
      · rw [← ea]
        exact c3
    have r3 : referenceGaugeField S V 0 (siteAtOffset 0 Y p + unitStep 0 ν) μ =
        referenceGaugeField S' V' 0 (siteAtOffset 0 Y' p + unitStep 0 ν) μ := by
      rw [ea, ea]
      refine hrefs 0 _ μ hz (hinner _ (b1 ν)) (hinner _ b3) (hbond _ μ ?_ ?_)
      · rw [← ea]
        exact c2
      · rw [← ea]
        exact c3'
    have hcurl : linearizedCurl (referenceGaugeField S V 0) A.fine (siteAtOffset 0 Y p, μ, ν) =
        linearizedCurl (referenceGaugeField S' V' 0) A'.fine (siteAtOffset 0 Y' p, μ, ν) := by
      simp only [linearizedCurl]
      rw [a1, a2, a3, a4, r1, r2, r3, r4]
    simp only [hR0, hR0']
    rw [hcurl]
  unfold localNormSq
  simp only [constOneWeights]
  rw [e1, e2, e3]
end YangMills.Construction.BlockAverages
end
