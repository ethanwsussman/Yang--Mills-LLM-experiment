import YangMills.Construction.ColdChainAtEveryLevel.BondsAcrossFrames
import YangMills.Construction.ColdChainAtEveryLevel.ChainsAtTheSameOffsets
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.GaugeMapAcrossFrames
open BlockAverages BlockAverages.Offsets GaugeMap LatticeFractionalIntegration LatticePaths CellTransport
variable {F F' : BlockFrame}
theorem baseDistance_siteAtOffset_le (hL : 0 < F.blockSide) {j : ℕ} (hj : j ≤ F.top) (Y : F.Cell) {ρ : ℕ}
    {p : Fin 4 → ℤ} (hp : WithinCellRadius F.blockSide F.top ρ j p) :
    (baseDistance (siteAtOffset j Y p) (cellCentre 0 Y) : ℤ) ≤ (ρ : ℤ) * (F.blockSide : ℤ) ^ F.top := by apply _root_.YangMills.Construction.BlockAverages.AgreeingPairs.baseDistance_siteAtOffset_le <;> assumption
section Cutoffs
theorem cutoffProfile_eq_zero {t : ℝ} (ht : 0.9 ≤ |t|) : cutoffProfile t = 0 := by apply _root_.YangMills.Construction.BlockAverages.cutoffProfile_eq_zero <;> assumption
theorem cellCutoff_eq_zero (hodd : Odd F.blockSide) {x : F.Site 0} {y : F.Cell}
    (hd : 2 ≤ cellSupDist (enclosingCell x) y) : cellCutoff x y = 0 := by
  have h1 := CellDistances.cellSupDist_mul_le_baseDistance_add hodd x y
  have hN0 : (0 : ℤ) < (F.blockSide : ℤ) ^ F.top := by
    have : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
    exact pow_pos this _
  have h2 : (F.blockSide : ℤ) ^ F.top ≤ (baseDistance x (cellCentre 0 y) : ℤ) := by
    have h3 : (2 : ℤ) * (F.blockSide : ℤ) ^ F.top ≤ (cellSupDist (enclosingCell x) y : ℤ) * (F.blockSide : ℤ) ^ F.top :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hd) hN0.le
    linarith
  have hne : (Finset.univ : Finset (Fin 4)).Nonempty := ⟨0, Finset.mem_univ _⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hne
    (fun i => (((baseSite x - cellCentre 0 y : F.Site 0) i).valMinAbs).natAbs)
  have hb : baseDistance x (cellCentre 0 y) = (((x - cellCentre 0 y : F.Site 0) i).valMinAbs).natAbs := by
    unfold baseDistance
    rw [hi, PlaquettesNearCell.baseSite_zero]
  rw [hb] at h2
  unfold cellCutoff
  refine Finset.prod_eq_zero (Finset.mem_univ i) (cutoffProfile_eq_zero ?_)
  have hNr : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by exact_mod_cast hN0
  rw [abs_div, abs_of_pos hNr, le_div_iff₀ hNr]
  have h3 : ((F.blockSide : ℝ) ^ F.top) ≤ |((((x - cellCentre 0 y : F.Site 0) i).valMinAbs : ℤ) : ℝ)| := by
    have h4 : (F.blockSide : ℤ) ^ F.top ≤ |((x - cellCentre 0 y : F.Site 0) i).valMinAbs| := by
      rw [Int.abs_eq_natAbs]
      exact h2
    exact_mod_cast h4
  nlinarith
end Cutoffs
section Matched
structure MatchedBoxes (S : Finset F.Cell) (S' : Finset F'.Cell) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
    (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) : Prop where
  blockSide_odd : Odd F.blockSide
  blockSide_eq : F'.blockSide = F.blockSide
  depth_eq : F'.depth = F.depth
  ambient : IsAdmissibleAmbient F
  ambient' : IsAdmissibleAmbient F'
  radius_ge : 140 ≤ r
  extent_cond : ∀ i, F.extent i = 0 ∨ 2 * r + 2 < F.extent i
  extent_cond' : ∀ i, F'.extent i = 0 ∨ 2 * r + 2 < F'.extent i
  mem_iff : ∀ h, WithinRadius r h → (Y + siteOfCoords F.top h ∈ S ↔ Y' + siteOfCoords F'.top h ∈ S')
  field_eq : ∀ b, BondWithinRadius r b →
    V (Y + siteOfCoords F.top b.1) b.2 = V' (Y' + siteOfCoords F'.top b.1) b.2
  leadingFrame_eq : ∀ (b h : Fin 4 → ℤ), IsInnerOffset F.blockSide F.top r 0 b →
    cellCentre 0 Y + siteOfCoords 0 b ∈ sitesOfCells S 0 → WithinRadius r h →
    Y + siteOfCoords F.top h ∈ S →
    leadingFrame S V (cellCentre 0 Y + siteOfCoords 0 b) (Y + siteOfCoords F.top h) =
      leadingFrame S' V' (cellCentre 0 Y' + siteOfCoords 0 b) (Y' + siteOfCoords F'.top h)
variable {S : Finset F.Cell} {S' : Finset F'.Cell} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell}
  {Y' : F'.Cell} {r : ℕ}
theorem MatchedBoxes.top_eq (t : MatchedBoxes S S' V V' Y Y' r) : F'.top = F.top := by
  show F'.depth + 1 = F.depth + 1
  rw [t.depth_eq]
theorem MatchedBoxes.cellScale_eq (t : MatchedBoxes S S' V V' Y Y' r) :
    (F'.blockSide : ℤ) ^ F'.top = (F.blockSide : ℤ) ^ F.top := by
  rw [t.blockSide_eq, t.top_eq]
theorem MatchedBoxes.cellScale_eq_real (t : MatchedBoxes S S' V V' Y Y' r) :
    (F'.blockSide : ℝ) ^ F'.top = (F.blockSide : ℝ) ^ F.top := by
  rw [t.blockSide_eq, t.top_eq]
theorem MatchedBoxes.cellScale_pos (t : MatchedBoxes S S' V V' Y Y' r) : (0 : ℤ) < (F.blockSide : ℤ) ^ F.top := by
  have : (0 : ℤ) < F.blockSide := by exact_mod_cast t.blockSide_odd.pos
  exact pow_pos this _
theorem valMinAbs_base_of_small {G : BlockFrame} {r : ℕ} (hr : 140 ≤ r)
    (hs : ∀ i, G.extent i = 0 ∨ 2 * r + 2 < G.extent i) (hL : 0 < G.blockSide) {a : ℤ}
    {i : Fin 4} (h : |a| ≤ 80 * (G.blockSide : ℤ) ^ G.top) : ((a : ZMod (G.period 0 i))).valMinAbs = a := by
  apply valMinAbs_intCast_of_small
  have hN : (0 : ℤ) < (G.blockSide : ℤ) ^ G.top := by
    have : (0 : ℤ) < G.blockSide := by exact_mod_cast hL
    exact pow_pos this _
  have hper : (G.period 0 i : ℤ) = (G.extent i : ℤ) * (G.blockSide : ℤ) ^ G.top := by
    simp [BlockFrame.period]
  rcases hs i with h0 | h0
  · left
    simp [BlockFrame.period, h0]
  · right
    rw [hper]
    have h2 : ((2 * r + 2 : ℕ) : ℤ) < (G.extent i : ℤ) := by exact_mod_cast h0
    push_cast at h2
    nlinarith
theorem valMinAbs_cell_of_small {G : BlockFrame} {r : ℕ} (hr : 140 ≤ r)
    (hs : ∀ i, G.extent i = 0 ∨ 2 * r + 2 < G.extent i) {a : ℤ} {i : Fin 4}
    (h : |a| ≤ 130) : ((a : ZMod (G.period G.top i))).valMinAbs = a := by
  apply valMinAbs_intCast_of_small
  have hper : G.period G.top i = G.extent i := by simp [BlockFrame.period]
  rw [hper]
  rcases hs i with h0 | h0
  · exact Or.inl h0
  · right
    have h2 : ((2 * r + 2 : ℕ) : ℤ) < (G.extent i : ℤ) := by exact_mod_cast h0
    push_cast at h2
    omega
theorem siteAtOffset_sub_cellCentre {G : BlockFrame} (Y : G.Cell) (p g : Fin 4 → ℤ) (i : Fin 4) :
    (siteAtOffset 0 Y p - cellCentre 0 (Y + siteOfCoords G.top g) : G.Site 0) i =
      ((p i - (G.blockSide : ℤ) ^ G.top * g i : ℤ) : ZMod (G.period 0 i)) := by
  unfold siteAtOffset
  rw [cellCentre_add 0 (Nat.zero_le _)]
  simp [siteOfCoords]
theorem cellCutoff_eq (t : MatchedBoxes S S' V V' Y Y' r) {p g : Fin 4 → ℤ}
    (hp : ∀ i, |p i| ≤ 40 * (F.blockSide : ℤ) ^ F.top) (hg : ∀ i, |g i| ≤ 40) :
    cellCutoff (siteAtOffset 0 Y p) (Y + siteOfCoords F.top g) =
      cellCutoff (siteAtOffset 0 Y' p) (Y' + siteOfCoords F'.top g) := by
  have hN := t.cellScale_pos
  unfold cellCutoff
  refine Finset.prod_congr rfl fun i _ => ?_
  have hb : |p i - (F.blockSide : ℤ) ^ F.top * g i| ≤ 80 * (F.blockSide : ℤ) ^ F.top := by
    have h1 := abs_sub (p i) ((F.blockSide : ℤ) ^ F.top * g i)
    rw [abs_mul, abs_of_pos hN] at h1
    have h2 := mul_le_mul_of_nonneg_left (hg i) hN.le
    have h3 := hp i
    linarith
  rw [siteAtOffset_sub_cellCentre Y p g i, siteAtOffset_sub_cellCentre Y' p g i,
    valMinAbs_base_of_small t.radius_ge t.extent_cond t.blockSide_odd.pos hb, t.cellScale_eq,
    valMinAbs_base_of_small t.radius_ge t.extent_cond' (t.blockSide_eq ▸ t.blockSide_odd.pos)
      (by rw [t.cellScale_eq]; exact hb), t.cellScale_eq_real]
theorem interiorBump_eq (t : MatchedBoxes S S' V V' Y Y' r) {p g : Fin 4 → ℤ}
    (hp : ∀ i, |p i| ≤ 40 * (F.blockSide : ℤ) ^ F.top) (hg : ∀ i, |g i| ≤ 40) :
    interiorBump (siteAtOffset 0 Y p) (Y + siteOfCoords F.top g) =
      interiorBump (siteAtOffset 0 Y' p) (Y' + siteOfCoords F'.top g) := by
  have hN := t.cellScale_pos
  unfold interiorBump
  refine Finset.prod_congr rfl fun i _ => ?_
  have hb : |p i - (F.blockSide : ℤ) ^ F.top * g i| ≤ 80 * (F.blockSide : ℤ) ^ F.top := by
    have h1 := abs_sub (p i) ((F.blockSide : ℤ) ^ F.top * g i)
    rw [abs_mul, abs_of_pos hN] at h1
    have h2 := mul_le_mul_of_nonneg_left (hg i) hN.le
    have h3 := hp i
    linarith
  have hc : (cellSideLength F' : ℝ) = (cellSideLength F : ℝ) := by
    unfold cellSideLength
    rw [t.cellScale_eq]
  rw [siteAtOffset_sub_cellCentre Y p g i, siteAtOffset_sub_cellCentre Y' p g i,
    valMinAbs_base_of_small t.radius_ge t.extent_cond t.blockSide_odd.pos hb, t.cellScale_eq,
    valMinAbs_base_of_small t.radius_ge t.extent_cond' (t.blockSide_eq ▸ t.blockSide_odd.pos)
      (by rw [t.cellScale_eq]; exact hb), hc]
def cellOffsetFrom {G : BlockFrame} (Y y : G.Cell) : Fin 4 → ℤ := fun i => (y i - Y i).valMinAbs
theorem eq_add_cellOffsetFrom {G : BlockFrame} (Y y : G.Cell) : y = Y + siteOfCoords G.top (cellOffsetFrom Y y) := by
  funext i
  simp only [Pi.add_apply, siteOfCoords, cellOffsetFrom, ZMod.coe_valMinAbs]
  abel
theorem abs_cellOffsetFrom_le {G : BlockFrame} {Y y : G.Cell} {d : ℕ} (h : cellSupDist y Y ≤ d) (i : Fin 4) :
    |cellOffsetFrom Y y i| ≤ (d : ℤ) := by
  have h1 := Finset.le_sup (f := fun i => ((y i - Y i).valMinAbs).natAbs) (Finset.mem_univ i)
  have h2 : ((y i - Y i).valMinAbs).natAbs ≤ d := h1.trans h
  unfold cellOffsetFrom
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h2
theorem cellOffsetFrom_add_of_small {G : BlockFrame} {r : ℕ} (hr : 140 ≤ r)
    (hs : ∀ i, G.extent i = 0 ∨ 2 * r + 2 < G.extent i) (Y : G.Cell)
    {o : Fin 4 → ℤ} (ho : ∀ i, |o i| ≤ 130) : cellOffsetFrom Y (Y + siteOfCoords G.top o) = o := by
  funext i
  have e : (Y + siteOfCoords G.top o : G.Cell) i - Y i = ((o i : ℤ) : ZMod (G.period G.top i)) := by
    simp [siteOfCoords]
  simp only [cellOffsetFrom]
  rw [e]
  exact valMinAbs_cell_of_small hr hs (ho i)
theorem sum_eq_of_near {E : Type} [AddCommMonoid E] (t : MatchedBoxes S S' V V' Y Y' r) (f : F.Cell → E)
    (f' : F'.Cell → E)
    (hf : ∀ y ∈ S, ¬ cellSupDist y Y ≤ 40 → f y = 0) (hf' : ∀ y ∈ S', ¬ cellSupDist y Y' ≤ 40 → f' y = 0)
    (hs : ∀ o : Fin 4 → ℤ, (∀ i, |o i| ≤ 40) → Y + siteOfCoords F.top o ∈ S →
      f (Y + siteOfCoords F.top o) = f' (Y' + siteOfCoords F'.top o)) :
    ∑ y ∈ S, f y = ∑ y ∈ S', f' y := by
  classical
  have hr := t.radius_ge
  have e1 : ∑ y ∈ S, f y = ∑ y ∈ S.filter fun y => cellSupDist y Y ≤ 40, f y :=
    (Finset.sum_subset (Finset.filter_subset _ _) fun y hy hn => hf y hy fun h =>
      hn (Finset.mem_filter.2 ⟨hy, h⟩)).symm
  have e2 : ∑ y ∈ S', f' y = ∑ y ∈ S'.filter fun y => cellSupDist y Y' ≤ 40, f' y :=
    (Finset.sum_subset (Finset.filter_subset _ _) fun y hy hn => hf' y hy fun h =>
      hn (Finset.mem_filter.2 ⟨hy, h⟩)).symm
  rw [e1, e2]
  have hbig : ∀ o : Fin 4 → ℤ, (∀ i, |o i| ≤ 40) → WithinRadius r o := fun o ho i => by
    have := ho i
    omega
  refine Finset.sum_nbij' (fun y => Y' + siteOfCoords F'.top (cellOffsetFrom Y y))
    (fun y => Y + siteOfCoords F.top (cellOffsetFrom Y' y))
    (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨a1, a2⟩ := Finset.mem_filter.1 hy
    have ho := abs_cellOffsetFrom_le a2
    refine Finset.mem_filter.2 ⟨(t.mem_iff _ (hbig _ ho)).1 (by rw [← eq_add_cellOffsetFrom]; exact a1),
      cellSupDist_add_siteOfCoords_le Y' _ ho⟩
  · obtain ⟨a1, a2⟩ := Finset.mem_filter.1 hy
    have ho := abs_cellOffsetFrom_le a2
    refine Finset.mem_filter.2 ⟨(t.mem_iff _ (hbig _ ho)).2 (by rw [← eq_add_cellOffsetFrom]; exact a1),
      cellSupDist_add_siteOfCoords_le Y _ ho⟩
  · obtain ⟨a1, a2⟩ := Finset.mem_filter.1 hy
    have ho := abs_cellOffsetFrom_le a2
    show Y + siteOfCoords F.top (cellOffsetFrom Y' (Y' + siteOfCoords F'.top (cellOffsetFrom Y y))) = y
    rw [cellOffsetFrom_add_of_small hr t.extent_cond' Y' (fun i => by have := ho i; omega),
      ← eq_add_cellOffsetFrom]
  · obtain ⟨a1, a2⟩ := Finset.mem_filter.1 hy
    have ho := abs_cellOffsetFrom_le a2
    show Y' + siteOfCoords F'.top (cellOffsetFrom Y (Y + siteOfCoords F.top (cellOffsetFrom Y' y))) = y
    rw [cellOffsetFrom_add_of_small hr t.extent_cond Y (fun i => by have := ho i; omega),
      ← eq_add_cellOffsetFrom]
  · obtain ⟨a1, a2⟩ := Finset.mem_filter.1 hy
    have ho := abs_cellOffsetFrom_le a2
    have h1 := hs _ ho (by rw [← eq_add_cellOffsetFrom]; exact a1)
    rwa [← eq_add_cellOffsetFrom] at h1
end Matched
section Frames
variable {S : Finset F.Cell} {S' : Finset F'.Cell} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell}
  {Y' : F'.Cell} {r : ℕ}
theorem cellSupDist_enclosingCell_siteAtOffset_le {G : BlockFrame} (hodd : Odd G.blockSide) (Y : G.Cell)
    {p : Fin 4 → ℤ} (hp : ∀ i, |p i| ≤ 38 * (G.blockSide : ℤ) ^ G.top) :
    cellSupDist (enclosingCell (siteAtOffset 0 Y p)) Y ≤ 39 := by
  have hN : (0 : ℤ) < (G.blockSide : ℤ) ^ G.top := by
    have : (0 : ℤ) < G.blockSide := by exact_mod_cast hodd.pos
    exact pow_pos this _
  have h1 := CellDistances.cellSupDist_mul_le_baseDistance_add hodd (siteAtOffset 0 Y p) Y
  have h2 : (baseDistance (siteAtOffset 0 Y p) (cellCentre 0 Y) : ℤ) ≤ 38 * (G.blockSide : ℤ) ^ G.top := by
    have h3 : baseDistance (siteAtOffset 0 Y p) (cellCentre 0 Y) ≤ (38 * (G.blockSide : ℤ) ^ G.top).toNat := by
      refine Finset.sup_le fun i _ => ?_
      have e : (baseSite (siteAtOffset 0 Y p) - cellCentre 0 Y : G.Site 0) i =
          ((p i : ℤ) : ZMod (G.period 0 i)) := by
        rw [PlaquettesNearCell.baseSite_zero]
        unfold siteAtOffset
        simp [siteOfCoords]
      rw [e]
      refine (WeightedAverages.Chains.natAbs_valMinAbs_intCast_le _ _).trans ?_
      have h4 := hp i
      rw [Int.abs_eq_natAbs] at h4
      omega
    have h5 : ((38 * (G.blockSide : ℤ) ^ G.top).toNat : ℤ) = 38 * (G.blockSide : ℤ) ^ G.top :=
      Int.toNat_of_nonneg (by positivity)
    omega
  have h6 : (cellSupDist (enclosingCell (siteAtOffset 0 Y p)) Y : ℤ) * (G.blockSide : ℤ) ^ G.top ≤
      39 * (G.blockSide : ℤ) ^ G.top := by linarith
  have h7 := le_of_mul_le_mul_right h6 hN
  exact_mod_cast h7
theorem cellCutoff_eq_zero_of_far {G : BlockFrame} (hodd : Odd G.blockSide) {S₁ : Finset G.Cell} (Y : G.Cell)
    {p : Fin 4 → ℤ} (hp : ∀ i, |p i| ≤ 38 * (G.blockSide : ℤ) ^ G.top) {y : G.Cell}
    (hd : ¬ cellSupDist y Y ≤ 40) :
    cellCutoff (siteAtOffset 0 Y p) y = 0 := by
  refine cellCutoff_eq_zero hodd ?_
  have h1 := cellSupDist_enclosingCell_siteAtOffset_le hodd Y hp
  have h2 := CoordinateSeminorms.cellSupDist_triangle y (enclosingCell (siteAtOffset 0 Y p)) Y
  have h3 := CoordinateSeminorms.cellSupDist_comm y (enclosingCell (siteAtOffset 0 Y p))
  omega
theorem sum_sq_cellCutoff_eq (t : MatchedBoxes S S' V V' Y Y' r) {p : Fin 4 → ℤ}
    (hp : ∀ i, |p i| ≤ 38 * (F.blockSide : ℤ) ^ F.top) :
    ∑ y ∈ S, cellCutoff (siteAtOffset 0 Y p) y ^ 2 = ∑ y ∈ S', cellCutoff (siteAtOffset 0 Y' p) y ^ 2 := by
  have hN := t.cellScale_pos
  have hp' : ∀ i, |p i| ≤ 38 * (F'.blockSide : ℤ) ^ F'.top := fun i => by
    rw [t.cellScale_eq]
    exact hp i
  refine sum_eq_of_near t _ _ (fun y _ hd => ?_) (fun y _ hd => ?_) fun o ho _ => ?_
  · rw [cellCutoff_eq_zero_of_far (S₁ := S) t.blockSide_odd Y hp hd]
    simp
  · rw [cellCutoff_eq_zero_of_far (S₁ := S') (t.blockSide_eq ▸ t.blockSide_odd) Y' hp' hd]
    simp
  · rw [cellCutoff_eq t (fun i => (hp i).trans (by linarith)) ho]
theorem cellPartition_eq (t : MatchedBoxes S S' V V' Y Y' r) {p g : Fin 4 → ℤ}
    (hp : ∀ i, |p i| ≤ 38 * (F.blockSide : ℤ) ^ F.top) (hg : ∀ i, |g i| ≤ 40) :
    cellPartition S (siteAtOffset 0 Y p) (Y + siteOfCoords F.top g) =
      cellPartition S' (siteAtOffset 0 Y' p) (Y' + siteOfCoords F'.top g) := by
  have hN := t.cellScale_pos
  unfold cellPartition
  rw [cellCutoff_eq t (fun i => (hp i).trans (by linarith)) hg, sum_sq_cellCutoff_eq t hp]
theorem cellPartition_eq_zero_of_far {G : BlockFrame} (hodd : Odd G.blockSide) {S₁ : Finset G.Cell} (Y : G.Cell)
    {p : Fin 4 → ℤ} (hp : ∀ i, |p i| ≤ 38 * (G.blockSide : ℤ) ^ G.top) {y : G.Cell}
    (hd : ¬ cellSupDist y Y ≤ 40) :
    cellPartition S₁ (siteAtOffset 0 Y p) y = 0 := by
  unfold cellPartition
  rw [cellCutoff_eq_zero_of_far (S₁ := S₁) hodd Y hp hd]
  simp
theorem allAlong_add_shift {P : Lattice4 → Prop} (v₀ : Lattice4) : ∀ (l : List PathStep) (u : Lattice4),
    AllAlong (fun v => P (v₀ + v)) u l → AllAlong P (v₀ + u) l := by apply _root_.YangMills.Construction.BlockAverages.SameOffsets.allAlong_of_translate <;> assumption
theorem isOrthantClosedNear_transfer {G G' : BlockFrame} {S₁ : Finset G.Cell} {S₂ : Finset G'.Cell} {Y₁ : G.Cell}
    {Y₂ : G'.Cell} {r : ℕ}
    (hr : 140 ≤ r) (hs : ∀ i, G.extent i = 0 ∨ 2 * r + 2 < G.extent i)
    (hs' : ∀ i, G'.extent i = 0 ∨ 2 * r + 2 < G'.extent i)
    (hbox : ∀ h, WithinRadius r h → (Y₁ + siteOfCoords G.top h ∈ S₁ ↔ Y₂ + siteOfCoords G'.top h ∈ S₂))
    {g : Fin 4 → ℤ} (hg : ∀ i, |g i| ≤ 40) (e : Fin 4 → ℤ)
    (h : IsOrthantClosedNear S₁ (Y₁ + siteOfCoords G.top g) e) :
    IsOrthantClosedNear S₂ (Y₂ + siteOfCoords G'.top g) e := by
  intro q hq hd k hk hb
  have hz : cellSupDist (Y₂ + siteOfCoords G'.top g) Y₂ ≤ 40 := cellSupDist_add_siteOfCoords_le Y₂ g hg
  have hqY : cellSupDist q Y₂ ≤ 72 := by
    have := CoordinateSeminorms.cellSupDist_triangle q (Y₂ + siteOfCoords G'.top g) Y₂
    omega
  set o := cellOffsetFrom Y₂ q with ho
  have hob : ∀ i, |o i| ≤ 72 := fun i => by
    have := abs_cellOffsetFrom_le hqY i
    simpa using this
  have hqe : q = Y₂ + siteOfCoords G'.top o := eq_add_cellOffsetFrom Y₂ q
  have hin : WithinRadius r o := fun i => by
    have := hob i
    omega
  have hq₁ : Y₁ + siteOfCoords G.top o ∈ S₁ := (hbox o hin).2 (hqe ▸ hq)
  have hd₁ : cellSupDist (Y₁ + siteOfCoords G.top o) (Y₁ + siteOfCoords G.top g) ≤ 32 := by
    refine Finset.sup_le fun i _ => ?_
    have e1 : (Y₁ + siteOfCoords G.top o : G.Cell) i - (Y₁ + siteOfCoords G.top g : G.Cell) i =
        ((o i - g i : ℤ) : ZMod (G.period G.top i)) := by
      simp [siteOfCoords]
    have e2 : (Y₂ + siteOfCoords G'.top o : G'.Cell) i - (Y₂ + siteOfCoords G'.top g : G'.Cell) i =
        ((o i - g i : ℤ) : ZMod (G'.period G'.top i)) := by
      simp [siteOfCoords]
    have hsmall : |o i - g i| ≤ 130 := by
      have h1 := abs_sub (o i) (g i)
      have h2 := hob i
      have h3 := hg i
      omega
    have h4 : ((((Y₂ + siteOfCoords G'.top o : G'.Cell) i -
        (Y₂ + siteOfCoords G'.top g : G'.Cell) i)).valMinAbs).natAbs ≤ 32 := by
      have h5 := Finset.le_sup (f := fun i => (((Y₂ + siteOfCoords G'.top o : G'.Cell) i -
        (Y₂ + siteOfCoords G'.top g : G'.Cell) i).valMinAbs).natAbs) (Finset.mem_univ i)
      rw [← hqe] at h5 ⊢
      exact h5.trans hd
    rw [e2, valMinAbs_cell_of_small hr hs' hsmall] at h4
    rw [e1, valMinAbs_cell_of_small hr hs hsmall]
    exact h4
  have h1 := h _ hq₁ hd₁ k hk hb
  have e3 : Y₁ + siteOfCoords G.top o + siteOfCoords G.top k = Y₁ + siteOfCoords G.top (o + k) := by
    rw [_root_.YangMills.Construction.BlockAverages.siteOfCoords_add, add_assoc]
  rw [e3] at h1
  have hin2 : WithinRadius r (o + k) := fun i => by
    have a1 := hob i
    have a2 := hb i
    have a3 := abs_add_le (o i) (k i)
    simp only [Pi.add_apply]
    omega
  have h2 := (hbox _ hin2).1 h1
  rw [hqe, add_assoc, ← _root_.YangMills.Construction.BlockAverages.siteOfCoords_add]
  exact h2
theorem closedOrthant_eq (t : MatchedBoxes S S' V V' Y Y' r) {g : Fin 4 → ℤ} (hg : ∀ i, |g i| ≤ 40) :
    closedOrthant S (Y + siteOfCoords F.top g) = closedOrthant S' (Y' + siteOfCoords F'.top g) := by
  classical
  have hiff : ∀ e : Fin 4 → ℤ, IsOrthantClosedNear S (Y + siteOfCoords F.top g) e ↔
      IsOrthantClosedNear S' (Y' + siteOfCoords F'.top g) e := fun e =>
    ⟨isOrthantClosedNear_transfer t.radius_ge t.extent_cond t.extent_cond' t.mem_iff hg e,
      isOrthantClosedNear_transfer t.radius_ge t.extent_cond' t.extent_cond
        (fun h hb => (t.mem_iff h hb).symm) hg e⟩
  unfold closedOrthant
  have e : (fun e => decide (IsOrthantClosedNear S (Y + siteOfCoords F.top g) e)) =
      fun e => decide (IsOrthantClosedNear S' (Y' + siteOfCoords F'.top g) e) := by
    funext e
    exact decide_eq_decide.2 (hiff e)
  rw [e]
theorem pathHolonomy_eq (t : MatchedBoxes S S' V V' Y Y' r) :
    ∀ (l : List PathStep) (v : Lattice4), AllAlong (WithinRadius r) v l →
      pathHolonomy V (Y + siteOfCoords F.top v) l = pathHolonomy V' (Y' + siteOfCoords F'.top v) l := by
  have H : ∀ (p : Lattice4) (i : Fin 4), WithinRadius r p → WithinRadius r (p + basisVector i) →
      V (Y + siteOfCoords F.top p) i = V' (Y' + siteOfCoords F'.top p) i :=
    fun p i h1 h2 => t.field_eq (p, i) ⟨h1, h2⟩
  have hstep : ∀ {G : BlockFrame} (Z : G.Cell) (v : Lattice4) (st : PathStep),
      Z + siteOfCoords G.top v + stepDisplacement G.top st =
        Z + siteOfCoords G.top (v + FlatPairing.stepDisplacement st) := by
    intro G Z v st
    rw [ChartCoordinates.stepDisplacement_eq_siteOfCoords, add_assoc, ← _root_.YangMills.Construction.BlockAverages.siteOfCoords_add]
  have hsub : ∀ {G : BlockFrame} (Z : G.Cell) (v : Lattice4) (i : Fin 4),
      Z + siteOfCoords G.top v - unitStep G.top i =
        Z + siteOfCoords G.top (v + FlatPairing.stepDisplacement (i, false)) := by
    intro G Z v i
    have e0 : v + FlatPairing.stepDisplacement (i, false) = v - basisVector i := by
      simp [FlatPairing.stepDisplacement, sub_eq_add_neg]
    rw [e0, sub_eq_add_neg v, _root_.YangMills.Construction.BlockAverages.siteOfCoords_add, siteOfCoords_neg, unitStep_eq]
    abel
  intro l
  induction l with
  | nil => intro v _; rfl
  | cons st q ih =>
    intro v hp
    simp only [pathHolonomy]
    rw [hstep, hstep, ih _ hp.2]
    congr 1
    rcases st with ⟨i, b⟩
    cases b
    · have e0 : v + FlatPairing.stepDisplacement (i, false) = v - basisVector i := by
        simp [FlatPairing.stepDisplacement, sub_eq_add_neg]
      have hn : WithinRadius r (v + FlatPairing.stepDisplacement (i, false)) := allAlong_head hp.2
      simp only [linkValue, Bool.false_eq_true, if_false]
      rw [hsub, hsub, H _ i hn (by rw [e0, sub_add_cancel]; exact hp.1)]
    · have hn : WithinRadius r (v + FlatPairing.stepDisplacement (i, true)) := allAlong_head hp.2
      have e0 : v + FlatPairing.stepDisplacement (i, true) = v + basisVector i := by
        simp [FlatPairing.stepDisplacement]
      simp only [linkValue, if_true]
      exact H v i hp.1 (e0 ▸ hn)
theorem cellTransport_eq (t : MatchedBoxes S S' V V' Y Y' r) {g o : Fin 4 → ℤ} (hg : ∀ i, |g i| ≤ 40)
    (ho : ∀ i, |o i| ≤ 40) (hsign : ∀ i, |closedOrthant S (Y + siteOfCoords F.top g) i| ≤ 1) :
    cellTransport S V (Y + siteOfCoords F.top g) (Y + siteOfCoords F.top o) =
      cellTransport S' V' (Y' + siteOfCoords F'.top g) (Y' + siteOfCoords F'.top o) := by
  have hr := t.radius_ge
  have hs1 : ∀ i, cellDisplacement (Y + siteOfCoords F.top g) (Y + siteOfCoords F.top o) i = o i - g i := fun i => by
    have e : (Y + siteOfCoords F.top o : F.Cell) i - (Y + siteOfCoords F.top g : F.Cell) i =
        ((o i - g i : ℤ) : ZMod (F.period F.top i)) := by
      simp [siteOfCoords]
    unfold cellDisplacement
    have h2 := abs_sub (o i) (g i)
    have h3 := ho i
    have h4 := hg i
    rw [show ((Y + siteOfCoords F.top o - (Y + siteOfCoords F.top g) : F.Cell)) i = _ from e]
    exact valMinAbs_cell_of_small hr t.extent_cond (by omega)
  have hs2 : ∀ i, cellDisplacement (Y' + siteOfCoords F'.top g) (Y' + siteOfCoords F'.top o) i = o i - g i :=
    fun i => by
    have e : (Y' + siteOfCoords F'.top o : F'.Cell) i - (Y' + siteOfCoords F'.top g : F'.Cell) i =
        ((o i - g i : ℤ) : ZMod (F'.period F'.top i)) := by
      simp [siteOfCoords]
    unfold cellDisplacement
    have h2 := abs_sub (o i) (g i)
    have h3 := ho i
    have h4 := hg i
    rw [show ((Y' + siteOfCoords F'.top o - (Y' + siteOfCoords F'.top g) : F'.Cell)) i = _ from e]
    exact valMinAbs_cell_of_small hr t.extent_cond' (by omega)
  unfold cellTransport
  rw [← closedOrthant_eq t hg]
  simp only [hs1, hs2]
  set hh : Lattice4 := fun i => 21 * closedOrthant S (Y + siteOfCoords F.top g) i - (o i - g i) with hhd
  have hp1 := (axisPath_spec hh 1).1
  have hpath : AllAlong (WithinRadius r) o (axisPath hh 1) := by
    have h2 := allAlong_add_shift (P := WithinRadius r) o _ 0 (allAlong_mono (fun v hv i => ?_) hp1)
    · rwa [add_zero] at h2
    · have h3 := hv i
      have h4 := ho i
      have h5 := hg i
      have h6 := hsign i
      simp only [Pi.add_apply]
      simp only [hhd] at h3
      rw [abs_le] at h4 h5 h6 ⊢
      rcases le_total 0 (21 * closedOrthant S (Y + siteOfCoords F.top g) i - (o i - g i)) with c | c
      · rw [min_eq_left c, max_eq_right c] at h3
        constructor <;> omega
      · rw [min_eq_right c, max_eq_left c] at h3
        constructor <;> omega
  exact pathHolonomy_eq t _ _ hpath
end Frames
section Paths
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
def IsBetween (a b y : Lattice4) : Prop := ∀ i, a i ≤ y i ∧ y i ≤ b i
omit [NormedSpace ℝ E] in
theorem lineSum_congr (w w' : Lattice4 → Fin 4 → E) (y : Lattice4) (i : Fin 4) (n : ℤ)
    (h : ∀ r : ℤ, (0 ≤ r ∧ r < n) ∨ (n ≤ r ∧ r < 0) →
      w (y + r • basisVector i) i = w' (y + r • basisVector i) i) :
    lineSum w y i n = lineSum w' y i n := by
  simp only [lineSum]
  congr 1
  · apply Finset.sum_congr rfl
    intro r hr
    exact h r (Or.inl (Finset.mem_Ico.1 hr))
  · apply Finset.sum_congr rfl
    intro r hr
    exact h r (Or.inr (Finset.mem_Ico.1 hr))
theorem isBetween_staircasePoint_add (a b u v : Lattice4) (hu : IsBetween a b u) (hv : IsBetween a b v)
    (s : Fin 4) (t : ℤ)
    (h1 : min (u s) (v s) ≤ u s + t) (h2 : u s + t ≤ max (u s) (v s)) :
    IsBetween a b (staircasePoint u v s + t • basisVector s) := by
  intro j
  have hu' := hu j
  have hv' := hv j
  by_cases hj : j = s
  · subst hj
    have e : (staircasePoint u v j + t • basisVector j) j = u j + t := by
      simp [staircasePoint, basisVector]
    rw [e]
    omega
  · have e : (staircasePoint u v s + t • basisVector s) j = staircasePoint u v s j := by
      simp [basisVector, hj]
    rw [e]
    simp only [staircasePoint]
    split_ifs
    · exact hv'
    · exact hu'
omit [NormedSpace ℝ E] in
theorem staircaseSum_congr (a b : Lattice4) (w w' : Lattice4 → Fin 4 → E) (u v : Lattice4) (hu : IsBetween a b u)
    (hv : IsBetween a b v)
    (h : ∀ p i, IsBetween a b p → IsBetween a b (p + basisVector i) → w p i = w' p i) :
    staircaseSum w u v = staircaseSum w' u v := by
  simp only [staircaseSum]
  apply Finset.sum_congr rfl
  intro s _
  apply lineSum_congr
  intro r hr
  apply h
  · apply isBetween_staircasePoint_add a b u v hu hv <;> omega
  · have e : staircasePoint u v s + r • basisVector s + basisVector s =
        staircasePoint u v s + (r + 1) • basisVector s := by
      rw [add_smul, one_smul, add_assoc]
    rw [e]
    apply isBetween_staircasePoint_add a b u v hu hv <;> omega
theorem isBetween_dyadicPathPoint (K : ℕ) (x q : Lattice4) (ω : StaircaseSample) (hq : ∀ i, (ω i).1 = q i)
    (hx : ∀ i, x i ≤ q i)
    (hr : ∀ i, 0 ≤ (ω i).2 ∧ (ω i).2 < 2 ^ K) (m : ℕ) (hm : m ≤ K + 1) :
    IsBetween x q (dyadicPathPoint K x ω m) := by
  intro i
  cases m with
  | zero => exact ⟨le_refl _, hx i⟩
  | succ m =>
    have hd : 0 ≤ q i - x i := by linarith [hx i]
    have hK : (0 : ℤ) < 2 ^ K := by positivity
    have hmK : (2 : ℤ) ^ m ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (by omega)
    have hm0 : (0 : ℤ) < 2 ^ m := by positivity
    simp only [dyadicPathPoint, hq]
    have hlo : 0 ≤ (2 ^ m * (q i - x i) + (ω i).2) / 2 ^ K :=
      Int.ediv_nonneg (add_nonneg (mul_nonneg hm0.le hd) (hr i).1) hK.le
    have hhi : (2 ^ m * (q i - x i) + (ω i).2) / 2 ^ K < q i - x i + 1 := by
      apply Int.ediv_lt_of_lt_mul hK
      have := (hr i).2
      nlinarith [mul_le_mul_of_nonneg_right hmK hd]
    constructor <;> omega
theorem randomPathMean_congr (l : ℕ) (c : Lattice4) (w w' : Lattice4 → Fin 4 → E) (x : Lattice4)
    (hx : ∀ i, x i ≤ c i)
    (h : ∀ p i, IsBetween x (fun j => c j + l - 1) p → IsBetween x (fun j => c j + l - 1) (p + basisVector i) →
      w p i = w' p i) :
    randomPathMean l c w x = randomPathMean l c w' x := by
  simp only [randomPathMean]
  congr 1
  apply Finset.sum_congr rfl
  intro ω hω
  have hω' : ∀ i, (c i ≤ (ω i).1 ∧ (ω i).1 < c i + l) ∧ 0 ≤ (ω i).2 ∧ (ω i).2 < 2 ^ dyadicDepth l := by
    intro i
    have := Fintype.mem_piFinset.1 hω i
    simpa [Finset.mem_product, Finset.mem_Ico] using this
  simp only [dyadicPathSum]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' : m < dyadicDepth l + 1 := Finset.mem_range.1 hm
  have hwide : ∀ k, k ≤ dyadicDepth l + 1 →
      IsBetween x (fun j => c j + l - 1) (dyadicPathPoint (dyadicDepth l) x ω k) := by
    intro k hk i
    have := isBetween_dyadicPathPoint (dyadicDepth l) x (fun j => (ω j).1) ω (fun _ => rfl)
      (fun j => le_trans (hx j) (hω' j).1.1) (fun j => (hω' j).2) k hk i
    have h3 := (hω' i).1.2
    refine ⟨this.1, ?_⟩
    have h5 : dyadicPathPoint (dyadicDepth l) x ω k i ≤ (ω i).1 := this.2
    show _ ≤ c i + l - 1
    omega
  exact staircaseSum_congr _ _ w w' _ _ (hwide m (by omega)) (hwide (m + 1) (by omega)) h
end Paths
section Patches
variable {S : Finset F.Cell} {S' : Finset F'.Cell} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell}
  {Y' : F'.Cell} {r : ℕ}
structure MatchedRestrictions (m : ℕ) (S : Finset F.Cell) (S' : Finset F'.Cell) (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) (R : F.GaugeField 0) (R' : F'.GaugeField 0)
    (u : F.Site 0 → Fin 4 → ℍ[ℝ]) (u' : F'.Site 0 → Fin 4 → ℍ[ℝ]) : Prop where
  boxes : MatchedBoxes S S' V V' Y Y' r
  level_ge : 32 ≤ m
  regular : IsOrthantRegular S m
  regular' : IsOrthantRegular S' m
  reference_eq : ∀ (p : Fin 4 → ℤ) (i : Fin 4), (∀ l, |p l| ≤ 38 * (F.blockSide : ℤ) ^ F.top) →
    (siteAtOffset 0 Y p, i) ∈ innerBonds S 0 → R (siteAtOffset 0 Y p) i = R' (siteAtOffset 0 Y' p) i
  form_eq : ∀ (p : Fin 4 → ℤ) (i : Fin 4), (∀ l, |p l| ≤ 29 * (F.blockSide : ℤ) ^ F.top) →
    u (siteAtOffset 0 Y p) i = u' (siteAtOffset 0 Y' p) i
variable {R : F.GaugeField 0} {R' : F'.GaugeField 0} {u : F.Site 0 → Fin 4 → ℍ[ℝ]}
  {u' : F'.Site 0 → Fin 4 → ℍ[ℝ]} {m : ℕ}
theorem closedOrthant_eq_one_or_neg_one (t : MatchedRestrictions m S S' V V' Y Y' r R R' u u') (z : F.Cell) (i : Fin 4) :
    closedOrthant S z i = 1 ∨ closedOrthant S z i = -1 :=
  (closedOrthant_spec t.regular t.level_ge z).1 i
theorem abs_closedOrthant_le_one (t : MatchedRestrictions m S S' V V' Y Y' r R R' u u') (z : F.Cell) (i : Fin 4) :
    |closedOrthant S z i| ≤ 1 := by
  rcases closedOrthant_eq_one_or_neg_one t z i with h | h <;> rw [h] <;> norm_num
theorem frameChange_eq (t : MatchedRestrictions m S S' V V' Y Y' r R R' u u') {p g : Fin 4 → ℤ}
    (hg : ∀ i, |g i| ≤ 40)
    (hp : ∀ i, |p i| ≤ 38 * (F.blockSide : ℤ) ^ F.top) (hs : siteAtOffset 0 Y p ∈ sitesOfCells S 0) :
    frameChange S V (Y + siteOfCoords F.top g) (siteAtOffset 0 Y p) =
      frameChange S' V' (Y' + siteOfCoords F'.top g) (siteAtOffset 0 Y' p) := by
  have tl := t.boxes
  have hN := tl.cellScale_pos
  have hodd := tl.blockSide_odd
  have hp' : ∀ i, |p i| ≤ 38 * (F'.blockSide : ℤ) ^ F'.top := fun i => by
    rw [tl.cellScale_eq]
    exact hp i
  unfold frameChange
  congr 1
  unfold quaternionPairing
  refine sum_eq_of_near tl _ _ (fun y _ hd => ?_) (fun y _ hd => ?_) fun o ho hoS => ?_
  · simp only [transportVector]
    rw [cellPartition_eq_zero_of_far (S₁ := S) hodd Y hp hd]
    simp
  · simp only [transportVector]
    rw [cellPartition_eq_zero_of_far (S₁ := S') (tl.blockSide_eq ▸ hodd) Y' hp' hd]
    simp
  · have hin : WithinRadius r o := fun i => by
      have := ho i
      have := tl.radius_ge
      omega
    have hinner : IsInnerOffset F.blockSide F.top r 0 p := fun i => by
      rw [pow_zero, one_mul]
      have h1 := hp i
      have h2 : (140 : ℤ) ≤ r := by exact_mod_cast tl.radius_ge
      nlinarith
    have e1 := tl.leadingFrame_eq p o hinner hs hin hoS
    have e2 : leadingFrame S V (siteAtOffset 0 Y p) (Y + siteOfCoords F.top o) =
        leadingFrame S' V' (siteAtOffset 0 Y' p) (Y' + siteOfCoords F'.top o) := e1
    simp only [transportVector]
    rw [e2, cellPartition_eq tl hp ho, cellTransport_eq tl hg ho (abs_closedOrthant_le_one t _)]
theorem cellSideLength_eq (t : MatchedBoxes S S' V V' Y Y' r) : cellSideLength F' = cellSideLength F := by apply _root_.YangMills.Construction.GaugeMapAcrossFrames.MatchedBoxes.cellScale_eq <;> assumption
def patchDisplacement (N : ℤ) (e g x : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => N * g i + e i * (x i - (N - 1) / 2)
theorem patchSite_eq_siteAtOffset {G : BlockFrame} (S₁ : Finset G.Cell) (Y : G.Cell) (g x : Fin 4 → ℤ) :
    patchSite S₁ (Y + siteOfCoords G.top g) x =
      siteAtOffset 0 Y (patchDisplacement (cellSideLength G) (closedOrthant S₁ (Y + siteOfCoords G.top g)) g x) := by
  unfold patchSite siteAtOffset
  rw [cellCentre_add 0 (Nat.zero_le _), add_assoc, ← _root_.YangMills.Construction.BlockAverages.siteOfCoords_add]
  have e : (fun i => (G.blockSide : ℤ) ^ (G.top - 0) * g i) +
      (fun i => closedOrthant S₁ (Y + siteOfCoords G.top g) i * (x i - (cellSideLength G - 1) / 2)) =
      patchDisplacement (cellSideLength G) (closedOrthant S₁ (Y + siteOfCoords G.top g)) g x := by
    funext i
    simp [patchDisplacement, cellSideLength]
  rw [e]
theorem abs_patchDisplacement_le {N : ℤ} (hN : 1 ≤ N) {e g x : Fin 4 → ℤ} {D : ℤ} (he : ∀ i, |e i| ≤ 1)
    (hg : ∀ i, |g i| ≤ D)
    (hx : ∀ i, -(10 * N) ≤ x i ∧ x i ≤ 21 * N - 1) (i : Fin 4) :
    |patchDisplacement N e g x i| ≤ (D + 22) * N := by
  unfold patchDisplacement
  have h1 := abs_add_le (N * g i) (e i * (x i - (N - 1) / 2))
  rw [abs_mul, abs_mul, abs_of_pos (by omega : 0 < N)] at h1
  have h2 : |x i - (N - 1) / 2| ≤ 22 * N := by
    have := hx i
    rw [abs_le]
    constructor <;> omega
  have h3 := hg i
  have h4 := he i
  have h5 : |e i| * |x i - (N - 1) / 2| ≤ 1 * (22 * N) :=
    mul_le_mul h4 h2 (abs_nonneg _) (by norm_num)
  have h6 : N * |g i| ≤ N * D := mul_le_mul_of_nonneg_left h3 (by omega)
  nlinarith
theorem patchSite_mem (t : MatchedRestrictions m S S' V V' Y Y' r R R' u u') {z : F.Cell} {x : Lattice4}
    (hx : x ∈ patchDomain S z) :
    patchSite S z x ∈ sitesOfCells S 0 :=
  PatchPoints.patchSite_mem_sitesOfCells t.boxes.ambient t.boxes.blockSide_odd t.regular t.level_ge hx
theorem patchSite_add_unitStep {G : BlockFrame} (S₁ : Finset G.Cell) (z : G.Cell) (x : Lattice4) (i : Fin 4)
    (h : closedOrthant S₁ z i = -1)
    (he : ∀ l, closedOrthant S₁ z l = 1 ∨ closedOrthant S₁ z l = -1) (hne : ∀ l, l ≠ i → True) :
    patchSite S₁ z (x + basisVector i) + unitStep 0 i = patchSite S₁ z x := by
  unfold patchSite
  rw [add_assoc, unitStep_eq, ← _root_.YangMills.Construction.BlockAverages.siteOfCoords_add]
  congr 2
  funext l
  by_cases hl : l = i
  · subst hl
    simp [basisVector, h]
    ring
  · simp [basisVector, hl]
theorem localForm_eq (t : MatchedRestrictions m S S' V V' Y Y' r R R' u u') {g : Fin 4 → ℤ} (hg : ∀ i, |g i| ≤ 5)
    {x : Lattice4} {i : Fin 4}
    (hx : x ∈ patchDomain S (Y + siteOfCoords F.top g))
    (hx' : x + basisVector i ∈ patchDomain S (Y + siteOfCoords F.top g)) :
    localForm S V R (Y + siteOfCoords F.top g) u x i = localForm S' V' R' (Y' + siteOfCoords F'.top g) u' x i := by
  have tl := t.boxes
  have hN := tl.cellScale_pos
  have hg40 : ∀ i, |g i| ≤ 40 := fun i => by
    have := hg i
    omega
  have hsign := closedOrthant_eq tl hg40
  have hcs := cellSideLength_eq tl
  have hcN : cellSideLength F = (F.blockSide : ℤ) ^ F.top := rfl
  have hN1 : 1 ≤ cellSideLength F := by
    rw [hcN]
    exact hN
  set e := closedOrthant S (Y + siteOfCoords F.top g) with he
  have hsa : ∀ l, |e l| ≤ 1 := fun l => abs_closedOrthant_le_one t _ l
  have hoff : ∀ {w : Lattice4}, w ∈ patchDomain S (Y + siteOfCoords F.top g) →
      ∀ l, |patchDisplacement (cellSideLength F) e g w l| ≤ 27 * cellSideLength F := by
    intro w hw l
    have h1 := abs_patchDisplacement_le (D := 5) hN1 hsa hg
      (fun i => ⟨(PatchPoints.patchDomain_coord_bounds hw i).1,
        by have := (PatchPoints.patchDomain_coord_bounds hw i).2; omega⟩) l
    refine h1.trans (le_of_eq ?_)
    ring
  have hs1 := patchSite_eq_siteAtOffset S Y g x
  have hs2 := patchSite_eq_siteAtOffset S Y g (x + basisVector i)
  have hs1' := patchSite_eq_siteAtOffset S' Y' g x
  have hs2' := patchSite_eq_siteAtOffset S' Y' g (x + basisVector i)
  rw [← hsign, hcs] at hs1' hs2'
  rw [← he] at hs1 hs2
  set p₁ := patchDisplacement (cellSideLength F) e g x with hp₁
  set p₂ := patchDisplacement (cellSideLength F) e g (x + basisVector i) with hp₂
  have hb1 : ∀ l, |p₁ l| ≤ 38 * (F.blockSide : ℤ) ^ F.top := fun l => (hoff hx l).trans (by rw [hcN]; linarith)
  have hb2 : ∀ l, |p₂ l| ≤ 38 * (F.blockSide : ℤ) ^ F.top := fun l => (hoff hx' l).trans (by rw [hcN]; linarith)
  have hb1' : ∀ l, |p₁ l| ≤ 29 * (F.blockSide : ℤ) ^ F.top := fun l => (hoff hx l).trans (by rw [hcN]; linarith)
  have hb2' : ∀ l, |p₂ l| ≤ 29 * (F.blockSide : ℤ) ^ F.top := fun l => (hoff hx' l).trans (by rw [hcN]; linarith)
  have hm1 : siteAtOffset 0 Y p₁ ∈ sitesOfCells S 0 := by
    rw [← hs1]
    exact patchSite_mem t hx
  have hm2 : siteAtOffset 0 Y p₂ ∈ sitesOfCells S 0 := by
    rw [← hs2]
    exact patchSite_mem t hx'
  unfold localForm
  simp only
  rw [hs1, hs2, hs1', hs2', frameChange_eq t hg40 hb1 hm1, ← hsign, ← he]
  by_cases hc : e i = 1
  · rw [if_pos hc, if_pos hc, t.form_eq p₁ i hb1']
  · rw [if_neg hc, if_neg hc]
    have hneg : e i = -1 := (closedOrthant_eq_one_or_neg_one t _ i).resolve_left hc
    have hst := patchSite_add_unitStep S (Y + siteOfCoords F.top g) x i hneg
      (closedOrthant_eq_one_or_neg_one t _) (fun _ _ => trivial)
    rw [hs1, hs2] at hst
    have hbd : (siteAtOffset 0 Y p₂, i) ∈ innerBonds S 0 := by
      refine ChartCoordinates.mem_innerBonds hm2 ?_
      rw [hst]
      exact hm1
    rw [t.reference_eq p₂ i hb2 hbd, t.form_eq p₂ i hb2']
end Patches
section Potentials
variable {S : Finset F.Cell} {S' : Finset F'.Cell} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell}
  {Y' : F'.Cell} {r m : ℕ} {R : F.GaugeField 0} {R' : F'.GaugeField 0} {u : F.Site 0 → Fin 4 → ℍ[ℝ]}
  {u' : F'.Site 0 → Fin 4 → ℍ[ℝ]}
theorem cellSideLength_nonneg (t : MatchedBoxes S S' V V' Y Y' r) : 0 ≤ cellSideLength F := t.cellScale_pos.le
theorem localPotential_eq (t : MatchedRestrictions m S S' V V' Y Y' r R R' u u') {g : Fin 4 → ℤ} (hg : ∀ i, |g i| ≤ 5)
    {x : Lattice4}
    (hx : x ∈ patchDomain S (Y + siteOfCoords F.top g)) (hc : ∀ i, x i ≤ 12 * cellSideLength F) :
    localPotential S V R (Y + siteOfCoords F.top g) u x =
      localPotential S' V' R' (Y' + siteOfCoords F'.top g) u' x := by
  classical
  have tl := t.boxes
  have hcs := cellSideLength_eq tl
  have hN := cellSideLength_nonneg tl
  obtain ⟨hx1, a, ha, hax⟩ := Finset.mem_filter.1 hx
  have hr1 := Fintype.mem_piFinset.1 hx1
  have htn : (((9 * (cellSideLength F).toNat : ℕ)) : ℤ) = 9 * cellSideLength F := by
    push_cast
    rw [Int.toNat_of_nonneg hN]
  have inP : ∀ {p : Lattice4},
      IsBetween x (fun j => 12 * cellSideLength F + ((9 * (cellSideLength F).toNat : ℕ) : ℤ) - 1) p →
      p ∈ patchDomain S (Y + siteOfCoords F.top g) := by
    intro p hp
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, a, ha, fun i => ?_⟩
    · have h1 := Finset.mem_Icc.1 (hr1 i)
      have h2 := hp i
      simp only at h2
      rw [htn] at h2
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    · exact (hax i).trans (hp i).1
  unfold localPotential
  rw [hcs]
  exact randomPathMean_congr _ _ _ _ x hc fun p i h1 h2 => localForm_eq t hg (inP h1) (inP h2)
theorem mem_patchDomain_of_mem_cellOffsets (t : MatchedRestrictions m S S' V V' Y Y' r R R' u u') {z : F.Cell}
    (hz : z ∈ S) {x : Lattice4}
    (hx : x ∈ cellOffsets F) : x ∈ patchDomain S z := by
  classical
  have tl := t.boxes
  have hN := tl.cellScale_pos
  have hN' : 0 < cellSideLength F := hN
  refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, 0, ?_, fun i => ?_⟩
  · have h1 := Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hx i)
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · refine Finset.mem_image.2 ⟨z, Finset.mem_filter.2 ⟨hz, by rw [CoordinateSeminorms.cellSupDist_self]; omega⟩, ?_⟩
    funext i
    simp [cellDisplacement]
  · exact (Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hx i)).1
theorem localPotentialMean_eq (t : MatchedRestrictions m S S' V V' Y Y' r R R' u u') {g : Fin 4 → ℤ}
    (hg : ∀ i, |g i| ≤ 5)
    (hz : Y + siteOfCoords F.top g ∈ S) :
    localPotentialMean S V R (Y + siteOfCoords F.top g) u =
      localPotentialMean S' V' R' (Y' + siteOfCoords F'.top g) u' := by
  have tl := t.boxes
  have hcs := cellSideLength_eq tl
  have hN : 0 < cellSideLength F := tl.cellScale_pos
  have hoff : cellOffsets F' = cellOffsets F := by
    unfold cellOffsets
    rw [hcs]
  have hsum : ∑ x ∈ cellOffsets F, localPotential S V R (Y + siteOfCoords F.top g) u x =
      ∑ x ∈ cellOffsets F, localPotential S' V' R' (Y' + siteOfCoords F'.top g) u' x :=
    Finset.sum_congr rfl fun x hx => localPotential_eq t hg (mem_patchDomain_of_mem_cellOffsets t hz hx) fun i => by
      have h1 := Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hx i)
      omega
  unfold localPotentialMean
  rw [hoff, hcs, hsum]
theorem patchChart_eq (t : MatchedRestrictions m S S' V V' Y Y' r R R' u u') {p g : Fin 4 → ℤ} (hg : ∀ i, |g i| ≤ 40)
    (hp : ∀ i, |p i| ≤ 40 * (F.blockSide : ℤ) ^ F.top) :
    patchChart S (Y + siteOfCoords F.top g) (siteAtOffset 0 Y p) =
      patchChart S' (Y' + siteOfCoords F'.top g) (siteAtOffset 0 Y' p) := by
  have tl := t.boxes
  have hN := tl.cellScale_pos
  have hcs := cellSideLength_eq tl
  funext i
  have hb : |p i - (F.blockSide : ℤ) ^ F.top * g i| ≤ 80 * (F.blockSide : ℤ) ^ F.top := by
    have h1 := abs_sub (p i) ((F.blockSide : ℤ) ^ F.top * g i)
    rw [abs_mul, abs_of_pos hN] at h1
    have h2 := mul_le_mul_of_nonneg_left (hg i) hN.le
    have h3 := hp i
    linarith
  unfold patchChart
  rw [siteAtOffset_sub_cellCentre Y p g i, siteAtOffset_sub_cellCentre Y' p g i,
    valMinAbs_base_of_small tl.radius_ge tl.extent_cond tl.blockSide_odd.pos hb, tl.cellScale_eq,
    valMinAbs_base_of_small tl.radius_ge tl.extent_cond' (tl.blockSide_eq ▸ tl.blockSide_odd.pos)
      (by rw [tl.cellScale_eq]; exact hb), hcs, closedOrthant_eq tl hg]
theorem patchChart_le (t : MatchedRestrictions m S S' V V' Y Y' r R R' u u') {p g : Fin 4 → ℤ} (hg : ∀ i, |g i| ≤ 5)
    (hp : ∀ i, |p i| ≤ 6 * (F.blockSide : ℤ) ^ F.top) (i : Fin 4) :
    patchChart S (Y + siteOfCoords F.top g) (siteAtOffset 0 Y p) i ≤ 12 * cellSideLength F := by
  have tl := t.boxes
  have hN := tl.cellScale_pos
  have hcN : cellSideLength F = (F.blockSide : ℤ) ^ F.top := rfl
  have hb : |p i - (F.blockSide : ℤ) ^ F.top * g i| ≤ 11 * (F.blockSide : ℤ) ^ F.top := by
    have h1 := abs_sub (p i) ((F.blockSide : ℤ) ^ F.top * g i)
    rw [abs_mul, abs_of_pos hN] at h1
    have h2 := mul_le_mul_of_nonneg_left (hg i) hN.le
    have h3 := hp i
    linarith
  unfold patchChart
  rw [siteAtOffset_sub_cellCentre Y p g i,
    valMinAbs_base_of_small tl.radius_ge tl.extent_cond tl.blockSide_odd.pos (hb.trans (by linarith))]
  have h5 := abs_closedOrthant_le_one t (Y + siteOfCoords F.top g) i
  have h6 : closedOrthant S (Y + siteOfCoords F.top g) i * (p i - (F.blockSide : ℤ) ^ F.top * g i) ≤
      11 * (F.blockSide : ℤ) ^ F.top := by
    have h7 := abs_mul (closedOrthant S (Y + siteOfCoords F.top g) i) (p i - (F.blockSide : ℤ) ^ F.top * g i)
    have h8 := mul_le_mul h5 hb (abs_nonneg _) (by norm_num)
    have h9 := le_abs_self (closedOrthant S (Y + siteOfCoords F.top g) i * (p i - (F.blockSide : ℤ) ^ F.top * g i))
    linarith
  rw [hcN]
  omega
theorem gluedPotential_eq (t : MatchedRestrictions m S S' V V' Y Y' r R R' u u') {p : Fin 4 → ℤ}
    (hp : ∀ i, |p i| ≤ 3 * (F.blockSide : ℤ) ^ F.top)
    (hs : siteAtOffset 0 Y p ∈ sitesOfCells S 0) :
    gluedPotential S V R u (siteAtOffset 0 Y p) = gluedPotential S' V' R' u' (siteAtOffset 0 Y' p) := by
  classical
  have tl := t.boxes
  have hodd := tl.blockSide_odd
  have hN := tl.cellScale_pos
  have hp38 : ∀ i, |p i| ≤ 38 * (F.blockSide : ℤ) ^ F.top := fun i => (hp i).trans (by linarith)
  have hp40 : ∀ i, |p i| ≤ 40 * (F.blockSide : ℤ) ^ F.top := fun i => (hp i).trans (by linarith)
  have hp6 : ∀ i, |p i| ≤ 6 * (F.blockSide : ℤ) ^ F.top := fun i => (hp i).trans (by linarith)
  have hp38' : ∀ i, |p i| ≤ 38 * (F'.blockSide : ℤ) ^ F'.top := fun i => by
    rw [tl.cellScale_eq]
    exact hp38 i
  unfold gluedPotential
  refine sum_eq_of_near tl _ _ (fun y _ hd => ?_) (fun y _ hd => ?_) fun o ho hoS => ?_
  · rw [cellPartition_eq_zero_of_far (S₁ := S) hodd Y hp38 hd, zero_smul]
  · rw [cellPartition_eq_zero_of_far (S₁ := S') (tl.blockSide_eq ▸ hodd) Y' hp38' hd, zero_smul]
  · rw [← cellPartition_eq tl hp38 ho]
    by_cases h0 : cellPartition S (siteAtOffset 0 Y p) (Y + siteOfCoords F.top o) = 0
    · rw [h0, zero_smul, zero_smul]
    · have hnear : cellSupDist (enclosingCell (siteAtOffset 0 Y p)) (Y + siteOfCoords F.top o) ≤ 1 := by
        by_contra hc
        apply h0
        unfold cellPartition
        rw [cellCutoff_eq_zero hodd (by omega)]
        simp
      have hcY : cellSupDist (enclosingCell (siteAtOffset 0 Y p)) Y ≤ 4 := by
        have h1 := CellDistances.cellSupDist_mul_le_baseDistance_add hodd (siteAtOffset 0 Y p) Y
        have h2 : (baseDistance (siteAtOffset 0 Y p) (cellCentre 0 Y) : ℤ) ≤ 3 * (F.blockSide : ℤ) ^ F.top := by
          have h3 : baseDistance (siteAtOffset 0 Y p) (cellCentre 0 Y) ≤ (3 * (F.blockSide : ℤ) ^ F.top).toNat := by
            refine Finset.sup_le fun i _ => ?_
            have e : (baseSite (siteAtOffset 0 Y p) - cellCentre 0 Y : F.Site 0) i =
                ((p i : ℤ) : ZMod (F.period 0 i)) := by
              rw [PlaquettesNearCell.baseSite_zero]
              unfold siteAtOffset
              simp [siteOfCoords]
            rw [e]
            refine (WeightedAverages.Chains.natAbs_valMinAbs_intCast_le _ _).trans ?_
            have h4 := hp i
            rw [Int.abs_eq_natAbs] at h4
            omega
          have h5 : ((3 * (F.blockSide : ℤ) ^ F.top).toNat : ℤ) = 3 * (F.blockSide : ℤ) ^ F.top :=
            Int.toNat_of_nonneg (by positivity)
          omega
        have h6 : (cellSupDist (enclosingCell (siteAtOffset 0 Y p)) Y : ℤ) * (F.blockSide : ℤ) ^ F.top ≤
            4 * (F.blockSide : ℤ) ^ F.top := by linarith
        have h7 := le_of_mul_le_mul_right h6 hN
        exact_mod_cast h7
      have hoY : cellSupDist (Y + siteOfCoords F.top o) Y ≤ 5 := by
        have h1 := CoordinateSeminorms.cellSupDist_triangle (Y + siteOfCoords F.top o)
          (enclosingCell (siteAtOffset 0 Y p)) Y
        have h2 := CoordinateSeminorms.cellSupDist_comm (Y + siteOfCoords F.top o)
          (enclosingCell (siteAtOffset 0 Y p))
        omega
      have ho5 : ∀ i, |o i| ≤ 5 := fun i => by
        have h1 := abs_cellOffsetFrom_le hoY i
        rw [cellOffsetFrom_add_of_small tl.radius_ge tl.extent_cond Y (fun l => by have := ho l; omega)] at h1
        simpa using h1
      have hin : patchChart S (Y + siteOfCoords F.top o) (siteAtOffset 0 Y p) ∈
          patchDomain S (Y + siteOfCoords F.top o) := by
        obtain ⟨y, hy, h, hh, e⟩ := mem_sitesOfCells.1 hs
        have hcy : enclosingCell (siteAtOffset 0 Y p) = y := by
          rw [e]
          exact CoordinateSeminorms.enclosingCell_cellCentre_add hodd y h hh
        rw [e]
        have hd10 : cellSupDist (Y + siteOfCoords F.top o) y ≤ 10 := by
          rw [← hcy, CoordinateSeminorms.cellSupDist_comm]
          omega
        exact PatchPoints.patchChart_mem_patchDomain tl.ambient hodd (closedOrthant_eq_one_or_neg_one t _) hy hd10
          (by simpa using hh)
      rw [frameChange_eq t ho hp38 hs, ← patchChart_eq t ho hp40,
        localPotential_eq t ho5 hin (patchChart_le t ho5 hp6), localPotentialMean_eq t ho5 hoS]
end Potentials
section Map
variable {S : Finset F.Cell} {S' : Finset F'.Cell} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell}
  {Y' : F'.Cell} {r m : ℕ} {R : F.GaugeField 0} {R' : F'.GaugeField 0} {u : F.Site 0 → Fin 4 → ℍ[ℝ]}
  {u' : F'.Site 0 → Fin 4 → ℍ[ℝ]}
theorem abs_patchDisplacement_cellOffsets_le (t : MatchedRestrictions m S S' V V' Y Y' r R R' u u') {g : Fin 4 → ℤ}
    (hg : ∀ i, |g i| ≤ 2) {x : Lattice4}
    (hx : x ∈ cellOffsets F) (i : Fin 4) :
    |patchDisplacement (cellSideLength F) (closedOrthant S (Y + siteOfCoords F.top g)) g x i| ≤
      3 * (F.blockSide : ℤ) ^ F.top := by
  have hN : 0 < cellSideLength F := t.boxes.cellScale_pos
  have hcN : cellSideLength F = (F.blockSide : ℤ) ^ F.top := rfl
  rw [← hcN]
  unfold patchDisplacement
  have h1 := abs_add_le (cellSideLength F * g i)
    (closedOrthant S (Y + siteOfCoords F.top g) i * (x i - (cellSideLength F - 1) / 2))
  rw [abs_mul, abs_mul, abs_of_pos hN] at h1
  have h2 : |x i - (cellSideLength F - 1) / 2| ≤ cellSideLength F := by
    have := Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hx i)
    rw [abs_le]
    constructor <;> omega
  have h3 := hg i
  have h4 := abs_closedOrthant_le_one t (Y + siteOfCoords F.top g) i
  have h5 : |closedOrthant S (Y + siteOfCoords F.top g) i| * |x i - (cellSideLength F - 1) / 2| ≤
      1 * cellSideLength F :=
    mul_le_mul h4 h2 (abs_nonneg _) (by norm_num)
  have h6 : cellSideLength F * |g i| ≤ cellSideLength F * 2 := mul_le_mul_of_nonneg_left h3 hN.le
  linarith
theorem frameCellMean_eq (t : MatchedRestrictions m S S' V V' Y Y' r R R' u u') {g : Fin 4 → ℤ} (hg : ∀ i, |g i| ≤ 2)
    (hz : Y + siteOfCoords F.top g ∈ S) :
    frameCellMean S V (Y + siteOfCoords F.top g) (gluedPotential S V R u) =
      frameCellMean S' V' (Y' + siteOfCoords F'.top g) (gluedPotential S' V' R' u') := by
  have tl := t.boxes
  have hcs := cellSideLength_eq tl
  have hN := tl.cellScale_pos
  have hg40 : ∀ i, |g i| ≤ 40 := fun i => by
    have := hg i
    omega
  have hoff : cellOffsets F' = cellOffsets F := by
    unfold cellOffsets
    rw [hcs]
  have hsign := closedOrthant_eq tl hg40
  have hsum : ∑ x ∈ cellOffsets F,
        _root_.YangMills.Construction.BlockAverages.adjointAction (frameChange S V (Y + siteOfCoords F.top g) (patchSite S (Y + siteOfCoords F.top g) x))⁻¹
          (gluedPotential S V R u (patchSite S (Y + siteOfCoords F.top g) x)) =
      ∑ x ∈ cellOffsets F,
        _root_.YangMills.Construction.BlockAverages.adjointAction (frameChange S' V' (Y' + siteOfCoords F'.top g) (patchSite S' (Y' + siteOfCoords F'.top g) x))⁻¹
          (gluedPotential S' V' R' u' (patchSite S' (Y' + siteOfCoords F'.top g) x)) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hb := abs_patchDisplacement_cellOffsets_le t hg hx
    have hmem := patchSite_mem t (mem_patchDomain_of_mem_cellOffsets t hz hx)
    have e1 := patchSite_eq_siteAtOffset S Y g x
    have e2 := patchSite_eq_siteAtOffset S' Y' g x
    rw [← hsign, hcs] at e2
    rw [e1] at hmem
    rw [e1, e2, frameChange_eq t hg40 (fun i => (hb i).trans (by linarith)) hmem, gluedPotential_eq t hb hmem]
  unfold frameCellMean
  rw [hoff, hcs, hsum]
theorem interiorBump_eq_zero (hodd : Odd F.blockSide) {x : F.Site 0} {y : F.Cell}
    (hd : 2 ≤ cellSupDist (enclosingCell x) y) : interiorBump x y = 0 := by
  have h1 := CellDistances.cellSupDist_mul_le_baseDistance_add hodd x y
  have hN0 : (0 : ℤ) < (F.blockSide : ℤ) ^ F.top := by
    have : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
    exact pow_pos this _
  have h2 : (F.blockSide : ℤ) ^ F.top ≤ (baseDistance x (cellCentre 0 y) : ℤ) := by
    have h3 : (2 : ℤ) * (F.blockSide : ℤ) ^ F.top ≤ (cellSupDist (enclosingCell x) y : ℤ) * (F.blockSide : ℤ) ^ F.top :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hd) hN0.le
    linarith
  have hne : (Finset.univ : Finset (Fin 4)).Nonempty := ⟨0, Finset.mem_univ _⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hne
    (fun i => (((baseSite x - cellCentre 0 y : F.Site 0) i).valMinAbs).natAbs)
  have hb : baseDistance x (cellCentre 0 y) = (((x - cellCentre 0 y : F.Site 0) i).valMinAbs).natAbs := by
    unfold baseDistance
    rw [hi, PlaquettesNearCell.baseSite_zero]
  rw [hb] at h2
  unfold interiorBump
  refine Finset.prod_eq_zero (Finset.mem_univ i) (cutoffProfile_eq_zero ?_)
  have hNr : (0 : ℝ) < (cellSideLength F : ℝ) := by
    have : (0 : ℤ) < cellSideLength F := hN0
    exact_mod_cast this
  have h3 : (cellSideLength F : ℝ) ≤ |((((x - cellCentre 0 y : F.Site 0) i).valMinAbs : ℤ) : ℝ)| := by
    have h4 : cellSideLength F ≤ |((x - cellCentre 0 y : F.Site 0) i).valMinAbs| := by
      rw [Int.abs_eq_natAbs]
      exact h2
    exact_mod_cast h4
  rw [abs_div, abs_of_pos hNr, le_div_iff₀ hNr, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 2)]
  nlinarith
theorem gaugeMap_eq (t : MatchedRestrictions m S S' V V' Y Y' r R R' u u') {p : Fin 4 → ℤ}
    (hp : ∀ i, |p i| ≤ (F.blockSide : ℤ) ^ F.top)
    (hs : siteAtOffset 0 Y p ∈ sitesOfCells S 0) (hc : enclosingCell (siteAtOffset 0 Y p) = Y) :
    gaugeMap S V R u (siteAtOffset 0 Y p) = gaugeMap S' V' R' u' (siteAtOffset 0 Y' p) := by
  classical
  have tl := t.boxes
  have hodd := tl.blockSide_odd
  have hN := tl.cellScale_pos
  have hcs := cellSideLength_eq tl
  have hp3 : ∀ i, |p i| ≤ 3 * (F.blockSide : ℤ) ^ F.top := fun i => (hp i).trans (by linarith)
  have hp38 : ∀ i, |p i| ≤ 38 * (F.blockSide : ℤ) ^ F.top := fun i => (hp i).trans (by linarith)
  have hp40 : ∀ i, |p i| ≤ 40 * (F.blockSide : ℤ) ^ F.top := fun i => (hp i).trans (by linarith)
  have hp38' : ∀ i, |p i| ≤ 38 * (F'.blockSide : ℤ) ^ F'.top := fun i => by
    rw [tl.cellScale_eq]
    exact hp38 i
  have hfar' : ∀ y : F'.Cell, ¬ cellSupDist y Y' ≤ 40 → interiorBump (siteAtOffset 0 Y' p) y = 0 := by
    intro y hd
    refine interiorBump_eq_zero (tl.blockSide_eq ▸ hodd) ?_
    have h1 := cellSupDist_enclosingCell_siteAtOffset_le (tl.blockSide_eq ▸ hodd) Y' hp38'
    have h2 := CoordinateSeminorms.cellSupDist_triangle y (enclosingCell (siteAtOffset 0 Y' p)) Y'
    have h3 := CoordinateSeminorms.cellSupDist_comm y (enclosingCell (siteAtOffset 0 Y' p))
    omega
  have hfar : ∀ y : F.Cell, ¬ cellSupDist y Y ≤ 40 → interiorBump (siteAtOffset 0 Y p) y = 0 := by
    intro y hd
    refine interiorBump_eq_zero hodd ?_
    have h1 := cellSupDist_enclosingCell_siteAtOffset_le hodd Y hp38
    have h2 := CoordinateSeminorms.cellSupDist_triangle y (enclosingCell (siteAtOffset 0 Y p)) Y
    have h3 := CoordinateSeminorms.cellSupDist_comm y (enclosingCell (siteAtOffset 0 Y p))
    omega
  have hsum : ∑ y ∈ S, normalizedBump S (siteAtOffset 0 Y p) y • _root_.YangMills.Construction.BlockAverages.adjointAction (frameChange S V y (siteAtOffset 0 Y p))
        (frameCellMean S V y (gluedPotential S V R u)) =
      ∑ y ∈ S', normalizedBump S' (siteAtOffset 0 Y' p) y • _root_.YangMills.Construction.BlockAverages.adjointAction (frameChange S' V' y (siteAtOffset 0 Y' p))
        (frameCellMean S' V' y (gluedPotential S' V' R' u')) := by
    refine sum_eq_of_near tl _ _ (fun y _ hd => ?_) (fun y _ hd => ?_) fun o ho hoS => ?_
    · simp only [normalizedBump]
      rw [hfar y hd]
      simp
    · simp only [normalizedBump]
      rw [hfar' y hd]
      simp
    · have hinner := interiorBump_eq tl hp40 ho
      by_cases h0 : interiorBump (siteAtOffset 0 Y p) (Y + siteOfCoords F.top o) = 0
      · simp only [normalizedBump]
        rw [← hinner, h0]
        simp
      · have hnear : cellSupDist Y (Y + siteOfCoords F.top o) ≤ 1 := by
          by_contra hcd
          apply h0
          refine interiorBump_eq_zero hodd ?_
          rw [hc]
          omega
        have hoY : cellSupDist (Y + siteOfCoords F.top o) Y ≤ 1 := by
          rw [CoordinateSeminorms.cellSupDist_comm]
          exact hnear
        have ho2 : ∀ i, |o i| ≤ 2 := fun i => by
          have h1 := abs_cellOffsetFrom_le hoY i
          rw [cellOffsetFrom_add_of_small tl.radius_ge tl.extent_cond Y (fun l => by have := ho l; omega)] at h1
          have h2 : |o i| ≤ 1 := by simpa using h1
          omega
        have hsign := closedOrthant_eq tl ho
        have hden : ∑ x ∈ cellOffsets F, interiorBump (patchSite S (Y + siteOfCoords F.top o) x)
              (Y + siteOfCoords F.top o) =
            ∑ x ∈ cellOffsets F, interiorBump (patchSite S' (Y' + siteOfCoords F'.top o) x)
              (Y' + siteOfCoords F'.top o) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have hb := abs_patchDisplacement_cellOffsets_le t ho2 hx
          have e1 := patchSite_eq_siteAtOffset S Y o x
          have e2 := patchSite_eq_siteAtOffset S' Y' o x
          rw [← hsign, hcs] at e2
          rw [e1, e2]
          exact interiorBump_eq tl (fun i => (hb i).trans (by linarith)) ho
        have hoff : cellOffsets F' = cellOffsets F := by
          unfold cellOffsets
          rw [hcs]
        have hbump : normalizedBump S (siteAtOffset 0 Y p) (Y + siteOfCoords F.top o) =
            normalizedBump S' (siteAtOffset 0 Y' p) (Y' + siteOfCoords F'.top o) := by
          unfold normalizedBump
          rw [hinner, hden, hoff, hcs]
        rw [hbump, frameChange_eq t ho hp38 hs, frameCellMean_eq t ho2 hoS]
  unfold gaugeMap
  rw [gluedPotential_eq t hp3 hs, hsum]
end Map
set_option maxHeartbeats 1000000 in
theorem gaugeMapAcrossFramesStatement_holds (hLines : agreeingPairsLocalityStatement) :
    gaugeMapAcrossFramesStatement := by
  obtain ⟨c, hc, hl⟩ := hLines
  refine ⟨c, hc, ?_⟩
  intro F F' m S S' s V V' Y Y' r ρ hL ht hodd hamb hamb' hm hreg hreg' hs hsc hcold hcold' hagree hρ30 hρ u u' hu
    q hq hqS
  classical
  obtain ⟨hside, hside', hbox, hVb⟩ := id hagree
  have hL0 : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
  set N : ℤ := (F.blockSide : ℤ) ^ F.top with hN
  have hN0 : 0 < N := pow_pos hL0 _
  have hn : F'.top = F.top := by
    show F'.depth + 1 = F.depth + 1
    rw [ht]
  have hNe : (F'.blockSide : ℤ) ^ F'.top = N := by rw [hL, hn]
  obtain ⟨y, hy, h, hh, e⟩ := mem_sitesOfCells.1 hqS
  have hcube := (_root_.YangMills.Construction.LatticePaths.mem_centredCube_iff _ _).1 hh
  have ecast : (((F.blockSide ^ (F.top - 0) : ℕ)) : ℤ) = N := by
    simp [hN]
  rw [ecast] at hcube
  set o : Fin 4 → ℤ := cellOffsetFrom Y y with ho
  have hyY : y = Y + siteOfCoords F.top o := eq_add_cellOffsetFrom Y y
  have hc1 : siteAtOffset 0 Y q = siteAtOffset 0 Y ((fun i => N * o i) + h) := by
    rw [e]
    unfold siteAtOffset
    rw [hyY, cellCentre_add 0 (Nat.zero_le _), _root_.YangMills.Construction.BlockAverages.siteOfCoords_add, add_assoc]
    simp [hN]
  have hcell : enclosingCell (siteAtOffset 0 Y q) = y := by
    rw [e]
    exact CoordinateSeminorms.enclosingCell_cellCentre_add hodd y h hh
  have hdy : (cellSupDist y Y : ℤ) * N ≤ ((ρ - 30 : ℕ) : ℤ) * N + N := by
    have h1 := CellDistances.cellSupDist_mul_le_baseDistance_add hodd (siteAtOffset 0 Y q) Y
    rw [hcell] at h1
    have h2 := baseDistance_siteAtOffset_le hodd.pos (Nat.zero_le _) Y hq
    linarith
  have hdy' : cellSupDist y Y ≤ ρ - 29 := by
    have h3 : (cellSupDist y Y : ℤ) * N ≤ (((ρ - 30 : ℕ) : ℤ) + 1) * N := by linarith
    have h4 := le_of_mul_le_mul_right h3 hN0
    omega
  have hob : ∀ i, |o i| ≤ ((ρ - 29 : ℕ) : ℤ) := fun i => abs_cellOffsetFrom_le hdy' i
  have hqe : q = (fun i => N * o i) + h := by
    have h1 : siteOfCoords (F := F) 0 q = siteOfCoords 0 ((fun i => N * o i) + h) := add_left_cancel hc1
    funext i
    have h2 := congrFun h1 i
    simp only [siteOfCoords] at h2
    have hq1 : |q i| ≤ ((ρ - 30 : ℕ) : ℤ) * N := by
      have := hq i
      rwa [pow_zero, one_mul] at this
    have hdvd : ((F.period 0 i : ℕ) : ℤ) ∣ (q i - ((fun i => N * o i) + h) i) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      push_cast at h2
      rw [h2]
      simp
    have hper : ((F.period 0 i : ℕ) : ℤ) = (F.extent i : ℤ) * N := by
      simp [BlockFrame.period, hN]
    rw [hper] at hdvd
    have hzero : q i - ((fun i => N * o i) + h) i = 0 := by
      rcases hside i with h0 | h0
      · rw [h0] at hdvd
        simpa using hdvd
      · have h2' : ((2 * r + 2 : ℕ) : ℤ) < (F.extent i : ℤ) := by exact_mod_cast h0
        push_cast at h2'
        have hpos : 0 < (F.extent i : ℤ) * N := by
          have : (0 : ℤ) < F.extent i := by omega
          positivity
        refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
        have a1 := hob i
        have a2 := hcube i
        have a3 : |((fun i => N * o i) + h) i| ≤ N * |o i| + N := by
          simp only [Pi.add_apply]
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_pos hN0]
          have : |h i| ≤ N := by
            rw [abs_le]
            constructor <;> omega
          linarith
        have a4 := abs_sub (q i) (((fun i => N * o i) + h) i)
        have a5 : N * |o i| ≤ N * ((ρ - 29 : ℕ) : ℤ) := mul_le_mul_of_nonneg_left a1 hN0.le
        have a6 : ((ρ + 110 : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hρ
        push_cast at a6
        have a7 : ((ρ - 29 : ℕ) : ℤ) = (ρ : ℤ) - 29 := by omega
        have a8 : ((ρ - 30 : ℕ) : ℤ) = (ρ : ℤ) - 30 := by omega
        rw [a7] at a5
        rw [a8] at hq1
        nlinarith
    omega
  have hob2 : ∀ i, |o i| ≤ ((ρ - 30 : ℕ) : ℤ) := by
    intro i
    have h1 : |q i| ≤ ((ρ - 30 : ℕ) : ℤ) * N := by
      have := hq i
      rwa [pow_zero, one_mul] at this
    have h2 := hcube i
    have h3 : q i = N * o i + h i := by
      rw [hqe]
      rfl
    have h4 : |h i| + 1 ≤ N := by
      have e5 : |h i| ≤ (N - 1) / 2 := by
        rw [abs_le]
        exact ⟨h2.1, h2.2⟩
      omega
    have h5 : N * |o i| ≤ |q i| + |h i| := by
      have : N * o i = q i - h i := by omega
      have h6 := abs_sub (q i) (h i)
      rw [← this, abs_mul, abs_of_pos hN0] at h6
      exact h6
    have h6 : N * |o i| < N * (((ρ - 30 : ℕ) : ℤ) + 1) := by nlinarith
    have h7 := lt_of_mul_lt_mul_left h6 hN0.le
    omega
  set r₂ : ℕ := r - (ρ - 30) with hr₂
  have hr₂140 : 140 ≤ r₂ := by omega
  have hsum : ∀ (a : Fin 4 → ℤ), WithinRadius r₂ a → WithinRadius r (o + a) := by
    intro a ha i
    have h1 := hob2 i
    have h2 := ha i
    have h3 := abs_add_le (o i) (a i)
    simp only [Pi.add_apply]
    omega
  set cY : F.Cell := Y + siteOfCoords F.top o with hcY
  set cY' : F'.Cell := Y' + siteOfCoords F'.top o with hcY'
  have hag : AgreeOnBall S V S' V' cY cY' r₂ := by
    refine ⟨fun i => (hside i).imp id fun e => by omega, fun i => (hside' i).imp id fun e => by omega,
      fun a ha => ?_, fun b hb => ?_⟩
    · have e1 : cY + siteOfCoords F.top a = Y + siteOfCoords F.top (o + a) := by
        rw [siteOfCoords_add, add_assoc]
      have e2 : cY' + siteOfCoords F'.top a = Y' + siteOfCoords F'.top (o + a) := by
        rw [siteOfCoords_add, add_assoc]
      rw [e1, e2]
      exact hbox _ (hsum a ha)
    · have e1 : cY + siteOfCoords F.top b.1 = Y + siteOfCoords F.top (o + b.1) := by
        rw [siteOfCoords_add, add_assoc]
      have e2 : cY' + siteOfCoords F'.top b.1 = Y' + siteOfCoords F'.top (o + b.1) := by
        rw [siteOfCoords_add, add_assoc]
      rw [e1, e2]
      refine hVb (o + b.1, b.2) ⟨hsum _ hb.1, ?_⟩
      have e3 : o + b.1 + Pi.single b.2 1 = o + (b.1 + Pi.single b.2 1) := by abel
      show WithinRadius r (o + b.1 + Pi.single b.2 1)
      rw [e3]
      exact hsum _ hb.2
  obtain ⟨hl1, hl2⟩ := hl F F' m S S' s V V' cY cY' r₂ hL ht hodd hamb hamb' hm hreg hreg' hs hsc hcold hcold' hag
  have hat : ∀ p : Fin 4 → ℤ, siteAtOffset 0 cY p = siteAtOffset 0 Y ((fun i => N * o i) + p) := by
    intro p
    unfold siteAtOffset
    rw [hcY, cellCentre_add 0 (Nat.zero_le _), _root_.YangMills.Construction.BlockAverages.siteOfCoords_add, add_assoc]
    simp [hN]
  have hat' : ∀ p : Fin 4 → ℤ, siteAtOffset 0 cY' p = siteAtOffset 0 Y' ((fun i => N * o i) + p) := by
    intro p
    unfold siteAtOffset
    rw [hcY', cellCentre_add 0 (Nat.zero_le _), _root_.YangMills.Construction.BlockAverages.siteOfCoords_add, add_assoc]
    have e1 : (fun i => (F'.blockSide : ℤ) ^ (F'.top - 0) * o i) = fun i => N * o i := by
      funext i
      simp only [Nat.sub_zero]
      rw [hNe]
    rw [e1]
  have hRef : referenceFieldChain S V 0 = referenceGaugeField S V 0 := by
    unfold referenceFieldChain
    exact Function.update_of_ne (by
      have : F.top = F.depth + 1 := rfl
      omega) _ _
  have hRef' : referenceFieldChain S' V' 0 = referenceGaugeField S' V' 0 := by
    unfold referenceFieldChain
    exact Function.update_of_ne (by
      have : F'.top = F'.depth + 1 := rfl
      omega) _ _
  have tl : MatchedBoxes S S' V V' cY cY' r₂ :=
    ⟨hodd, hL, ht, hamb, hamb', hr₂140, hag.1, hag.2.1, hag.2.2.1, hag.2.2.2, hl1⟩
  have hr₂z : (140 : ℤ) ≤ r₂ := by exact_mod_cast hr₂140
  have tR : MatchedRestrictions m S S' V V' cY cY' r₂ (referenceFieldChain S V 0) (referenceFieldChain S' V' 0) u u' := by
    refine ⟨tl, by omega, hreg, hreg', fun p i hp hb => ?_, fun p i hp => ?_⟩
    · rw [hRef, hRef']
      have hin : ∀ x : Lattice4, (∀ l, |x l| ≤ 39 * N) → IsInnerOffset F.blockSide F.top r₂ 0 x := fun x hx l => by
        rw [pow_zero, one_mul]
        refine (hx l).trans ?_
        have : (39 : ℤ) ≤ (r₂ : ℤ) - 100 := by omega
        exact mul_le_mul_of_nonneg_right this hN0.le
      refine hl2 0 p i (Nat.succ_pos _) (hin _ fun l => (hp l).trans (by linarith)) (hin _ fun l => ?_) hb
      have h2 := abs_add_le (p l) ((Pi.single i (1 : ℤ) : Fin 4 → ℤ) l)
      have h3 : |(Pi.single i (1 : ℤ) : Fin 4 → ℤ) l| ≤ 1 := by
        by_cases hli : l = i
        · subst hli
          simp
        · simp [hli]
      have h4 := hp l
      simp only [Pi.add_apply]
      nlinarith
    · rw [hat, hat']
      refine hu _ i fun l => ?_
      rw [pow_zero, one_mul]
      have h1 := hp l
      have h2 := hob2 l
      simp only [Pi.add_apply]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hN0]
      have h3 : N * |o l| ≤ N * ((ρ - 30 : ℕ) : ℤ) := mul_le_mul_of_nonneg_left h2 hN0.le
      have h4 : ((ρ - 30 : ℕ) : ℤ) = (ρ : ℤ) - 30 := by omega
      rw [h4] at h3
      show _ ≤ (ρ : ℤ) * (F.blockSide : ℤ) ^ F.top
      rw [← hN]
      nlinarith
  have hhN : ∀ i, |h i| ≤ (F.blockSide : ℤ) ^ F.top := fun i => by
    have := hcube i
    rw [abs_le, ← hN]
    constructor <;> omega
  have hq1 : siteAtOffset 0 Y q = siteAtOffset 0 cY h := by
    rw [hat, ← hqe]
  have hq2 : siteAtOffset 0 Y' q = siteAtOffset 0 cY' h := by
    rw [hat', ← hqe]
  rw [hq1, hq2]
  refine gaugeMap_eq tR hhN (by rw [← hq1]; exact hqS) ?_
  rw [← hq1, hcell, hyY]
end YangMills.Construction.GaugeMapAcrossFrames
end
