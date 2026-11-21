import YangMills.Construction.HoleBesideASecondHole.DistancesBlocksAndLumpsProof
import YangMills.Construction.ColdStepAtMirrorFrames.SumsAgainstFlatResponsesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames.TorusCells
variable {F : BlockFrame}
theorem siteOfCoords_add (j : ℕ) (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j (a + b) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem abs_sub_mul_ediv_le_half (P u : ℤ) (hP : 0 < P) (hodd : P % 2 = 1) :
    |u - P * ((u + (P - 1) / 2) / P)| ≤ (P - 1) / 2 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.abs_sub_mul_ediv_le <;> assumption
theorem natAbs_valMinAbs_intCast_le (N : ℕ) [NeZero N] (b : ℤ) : ((b : ZMod N).valMinAbs).natAbs ≤ b.natAbs := by apply _root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le <;> assumption
theorem siteCoords_cast {j : ℕ} (x : F.Site j) (i : Fin 4) (hpos : 0 < F.period j i) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.CurlSize.siteCoords_intCast <;> assumption
theorem siteOfCoords_siteCoords {j : ℕ} (x : F.Site j) (hpos : ∀ i, 0 < F.period j i) :
    siteOfCoords j (siteCoords x) = x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.siteOfCoords_siteCoords <;> assumption
theorem top_sub_depth (F : BlockFrame) : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem period_depth (F : BlockFrame) (i : Fin 4) : F.period F.depth i = F.extent i * F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimizingChart.period_depth <;> assumption
theorem period_top (F : BlockFrame) (i : Fin 4) : F.period F.top i = F.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
structure IsAdmissible (F : BlockFrame) : Prop where
  odd : Odd F.blockSide
  extent_ge : ∀ i, 64 ≤ F.extent i
theorem IsAdmissible.blockSide_pos (h : IsAdmissible F) : 0 < F.blockSide := h.odd.pos
theorem IsAdmissible.period_pos (h : IsAdmissible F) (j : ℕ) (i : Fin 4) : 0 < F.period j i := by
  have := h.extent_ge i
  have h2 := h.blockSide_pos
  unfold BlockFrame.period
  positivity
theorem blockSide_pow_emod_two (h : IsAdmissible F) (k : ℕ) : ((F.blockSide : ℤ) ^ k) % 2 = 1 := by
  have : Odd ((F.blockSide : ℤ) ^ k) := Odd.pow (by exact_mod_cast h.odd)
  exact Int.odd_iff.mp this
theorem enclosingCell_spec (h : IsAdmissible F) {j : ℕ} (x : F.Site j) :
    ∃ w : Fin 4 → ℤ, enclosingCell x = siteOfCoords F.top w ∧
      ∀ i, |siteCoords x i - (F.blockSide : ℤ) ^ (F.top - j) * w i| ≤ ((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2 := by
  refine ⟨_, rfl, fun i => ?_⟩
  exact abs_sub_mul_ediv_le_half _ _ (by have := h.blockSide_pos; positivity) (blockSide_pow_emod_two h _)
theorem exists_eq_valMinAbs_add_mul {N : ℕ} (hN : 0 < N) (a : ℤ) (x : ZMod N) (hx : ((a : ℤ) : ZMod N) = x) :
    ∃ m : ℤ, a = x.valMinAbs + m * N := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.exists_eq_valMinAbs_add_mul <;> assumption
theorem blockSide_mul_cellSupDist_le (h : IsAdmissible F) (x x' : F.Site F.depth) :
    F.blockSide * cellSupDist (enclosingCell x) (enclosingCell x') ≤ siteSupDist x x' + F.blockSide := by
  obtain ⟨w, hw, hb⟩ := enclosingCell_spec h x
  obtain ⟨w', hw', hb'⟩ := enclosingCell_spec h x'
  simp only [top_sub_depth, pow_one] at hb hb'
  unfold cellSupDist
  rw [Nat.mul_comm]
  have hL := h.blockSide_pos
  suffices H : ∀ i : Fin 4, (((enclosingCell x) i - (enclosingCell x') i).valMinAbs).natAbs * F.blockSide ≤ siteSupDist x x' + F.blockSide by
    have : (Finset.univ.sup fun i => (((enclosingCell x) i - (enclosingCell x') i).valMinAbs).natAbs) ≤
        (siteSupDist x x' + F.blockSide) / F.blockSide := by
      apply Finset.sup_le
      intro i _
      exact (Nat.le_div_iff_mul_le hL).mpr (H i)
    calc _ ≤ ((siteSupDist x x' + F.blockSide) / F.blockSide) * F.blockSide := Nat.mul_le_mul_right _ this
      _ ≤ _ := Nat.div_mul_le_self _ _
  intro i
  have hpos := h.period_pos F.depth i
  have hposn := h.period_pos F.top i
  have : NeZero (F.period F.top i) := ⟨hposn.ne'⟩
  obtain ⟨m, hm⟩ := exists_eq_valMinAbs_add_mul hpos (siteCoords x i - siteCoords x' i) (x i - x' i) (by
    push_cast
    rw [siteCoords_cast x i hpos, siteCoords_cast x' i hpos])
  have hd : ((x i - x' i).valMinAbs).natAbs ≤ siteSupDist x x' := by
    unfold siteSupDist
    exact Finset.le_sup (f := fun i => ((x i - x' i).valMinAbs).natAbs) (Finset.mem_univ i)
  set d := (x i - x' i).valMinAbs
  have hper : (F.period F.depth i : ℤ) = (F.extent i : ℤ) * F.blockSide := by rw [period_depth]; push_cast; ring
  set β := w i - w' i - m * (F.extent i : ℤ) with hβ
  have hcast : (enclosingCell x) i - (enclosingCell x') i = ((β : ℤ) : ZMod (F.period F.top i)) := by
    rw [hw, hw']
    simp only [siteOfCoords, Pi.sub_apply, hβ]
    push_cast
    have : ((F.extent i : ℕ) : ZMod (F.period F.top i)) = 0 := by
      have e : F.period F.top i = F.extent i := period_top F i
      rw [← e]; simp
    rw [this]; ring
  have hB := natAbs_valMinAbs_intCast_le (F.period F.top i) β
  rw [← hcast] at hB
  rw [hper] at hm
  have e1 : (F.blockSide : ℤ) * β = d - (siteCoords x i - F.blockSide * w i) + (siteCoords x' i - F.blockSide * w' i) := by
    rw [hβ]
    linear_combination hm
  have h3 : |(F.blockSide : ℤ) * β| ≤ |d| + ((F.blockSide : ℤ) - 1) := by
    rw [e1]
    have a1 := abs_le.mp (hb i)
    have a2 := abs_le.mp (hb' i)
    have a3 := abs_le.mp (le_refl |d|)
    rw [abs_le]
    constructor <;> omega
  have h2 : |(F.blockSide : ℤ) * β| = (β.natAbs : ℤ) * F.blockSide := by
    rw [abs_mul, Nat.abs_cast, Int.natCast_natAbs]; ring
  have hB' : ((((enclosingCell x) i - (enclosingCell x') i).valMinAbs).natAbs : ℤ) * F.blockSide ≤ (β.natAbs : ℤ) * F.blockSide :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hB) (by positivity)
  have goalZ : ((((enclosingCell x) i - (enclosingCell x') i).valMinAbs).natAbs : ℤ) * F.blockSide ≤
      (siteSupDist x x' : ℤ) + F.blockSide := by linarith
  exact_mod_cast goalZ
theorem natAbs_le_cellSupDist (x y : F.Cell) (i : Fin 4) :
    ((x i - y i).valMinAbs).natAbs ≤ cellSupDist x y := by apply _root_.YangMills.Construction.PatchPoints.natAbs_valMinAbs_le_cellSupDist <;> assumption
theorem siteSupDist_comm {j : ℕ} (x y : F.Site j) : siteSupDist x y = siteSupDist y x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.siteSupDist_comm <;> assumption
theorem cellSupDist_comm (x y : F.Cell) : cellSupDist x y = cellSupDist y x := siteSupDist_comm x y
theorem cellSupDist_triangle (a b c : F.Cell) : cellSupDist a c ≤ cellSupDist a b + cellSupDist b c := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem mem_centredCube (M : ℕ) (o : Fin 4 → ℤ) :
    o ∈ centredCube M ↔ ∀ i, -(((M : ℤ) - 1) / 2) ≤ o i ∧ o i ≤ ((M : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.LumpContours.CutAction.mem_centredCube <;> assumption
theorem card_centredCube (h : IsAdmissible F) : (centredCube F.blockSide).card = F.blockSide ^ 4 := by
  simp only [centredCube, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  have := h.odd
  obtain ⟨k, hk⟩ := this
  rw [hk]
  push_cast
  have : (2 * (k : ℤ) + 1 - 1) / 2 = k := by omega
  rw [this]
  have : (k : ℤ) + 1 - -(k : ℤ) = ((2 * k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]
theorem cellCentre_siteOfCoords (h : IsAdmissible F) (w : Fin 4 → ℤ) :
    cellCentre F.depth (siteOfCoords F.top w) = siteOfCoords F.depth fun i => (F.blockSide : ℤ) * w i := by
  funext i
  simp only [cellCentre, siteOfCoords, top_sub_depth, pow_one]
  have hposn := h.period_pos F.top i
  have e : ((siteCoords (siteOfCoords (F := F) F.top w) i : ℤ) : ZMod (F.period F.top i)) = ((w i : ℤ) : ZMod (F.period F.top i)) :=
    siteCoords_cast _ i hposn
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at e
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  obtain ⟨m, hm⟩ := e
  rw [period_depth]
  rw [period_top] at hm
  refine ⟨m, ?_⟩
  push_cast
  linear_combination (F.blockSide : ℤ) * hm
theorem exists_offset_mem_centredCube (h : IsAdmissible F) (x : F.Site F.depth) :
    ∃ o ∈ centredCube F.blockSide, x = cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth o := by
  obtain ⟨w, hw, hb⟩ := enclosingCell_spec h x
  simp only [top_sub_depth, pow_one] at hb
  refine ⟨fun i => siteCoords x i - F.blockSide * w i, ?_, ?_⟩
  · rw [mem_centredCube]
    intro i
    exact abs_le.mp (hb i)
  · rw [hw, cellCentre_siteOfCoords h, ← siteOfCoords_add]
    have : ((fun i => (F.blockSide : ℤ) * w i) + fun i => siteCoords x i - F.blockSide * w i) = siteCoords x := by
      funext i; simp
    rw [this, siteOfCoords_siteCoords x (h.period_pos F.depth)]
theorem finite_cell (h : IsAdmissible F) : Finite F.Cell := by
  haveI : ∀ i, NeZero (F.period F.top i) := fun i => ⟨(h.period_pos _ i).ne'⟩
  exact Finite.of_fintype ((i : Fin 4) → ZMod (F.period F.top i))
theorem mem_finiteCells (h : IsAdmissible F) (z : F.Cell) : z ∈ finiteCells F := by
  haveI := finite_cell h
  unfold finiteCells
  rw [dif_pos (finite_cell h)]
  exact @Finset.mem_univ _ (Fintype.ofFinite _) z
theorem blockFineSites_subset (h : IsAdmissible F) (Y : F.Cell) :
    blockFineSites Y ⊆ (centredCube F.blockSide).image fun o => cellCentre F.depth Y + siteOfCoords F.depth o := by
  intro y hy
  unfold blockFineSites at hy
  rw [Finset.mem_filter] at hy
  obtain ⟨o, ho, e⟩ := exists_offset_mem_centredCube h y
  rw [Finset.mem_image]
  exact ⟨o, ho, by rw [← hy.2, ← e]⟩
theorem card_blockFineSites_le (h : IsAdmissible F) (Y : F.Cell) : (blockFineSites Y).card ≤ F.blockSide ^ 4 := by
  refine (Finset.card_le_card (blockFineSites_subset h Y)).trans ?_
  exact Finset.card_image_le.trans (card_centredCube h).le
theorem sum_sitesOfCells_le (h : IsAdmissible F) (f : F.Cell → ℝ) (hf : ∀ z, 0 ≤ f z) :
    ∑ x ∈ sitesOfCells (finiteCells F) F.depth, f (enclosingCell x) ≤
      (F.blockSide : ℝ) ^ 4 * ∑ z ∈ finiteCells F, f z := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := sitesOfCells (finiteCells F) F.depth) (t := finiteCells F)
    (g := enclosingCell) (fun x _ => mem_finiteCells h _), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have e : ∑ x ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun x => enclosingCell x = z), f (enclosingCell x) =
      (((sitesOfCells (finiteCells F) F.depth).filter (fun x => enclosingCell x = z)).card : ℝ) * f z := by
    rw [Finset.sum_congr rfl (g := fun _ => f z)
      (fun x hx => by rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const, nsmul_eq_mul]
  rw [e]
  apply mul_le_mul_of_nonneg_right _ (hf z)
  have : ((sitesOfCells (finiteCells F) F.depth).filter (fun x => enclosingCell x = z)).card ≤ F.blockSide ^ 4 := by
    refine le_trans (le_of_eq ?_) (card_blockFineSites_le h z)
    unfold blockFineSites
    congr
  exact_mod_cast this
def offsetBox (A : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(A : ℤ)) A
theorem mem_offsetBox (A : ℕ) (o : Fin 4 → ℤ) : o ∈ offsetBox A ↔ ∀ i, |o i| ≤ A := by
  simp [offsetBox, Fintype.mem_piFinset, abs_le]
theorem sum_Icc_pow_natAbs_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (M : ℕ) :
    ∑ m ∈ Finset.Icc (-(M : ℤ)) M, r ^ m.natAbs ≤ 2 * (1 - r)⁻¹ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.sum_Icc_pow_natAbs_le <;> assumption
def cellDecaySum (κ : ℝ) : ℝ := (2 * (1 - Real.exp (-(κ / 4)))⁻¹) ^ 4
theorem cellDecaySum_pos {κ : ℝ} (hκ : 0 < κ) : 0 < cellDecaySum κ := by
  have : Real.exp (-(κ / 4)) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  unfold cellDecaySum
  have : 0 < 1 - Real.exp (-(κ / 4)) := by linarith
  positivity
theorem sum_finiteCells_exp_le (h : IsAdmissible F) {κ : ℝ} (hκ : 0 < κ) (c : F.Cell) :
    ∑ z ∈ finiteCells F, Real.exp (-(κ * cellSupDist z c)) ≤ cellDecaySum κ := by
  classical
  set r := Real.exp (-(κ / 4)) with hr
  have r0 : 0 ≤ r := (Real.exp_pos _).le
  have r1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]; linarith
  set M : ℕ := ∑ i, F.period F.top i with hM
  let off : F.Cell → Fin 4 → ℤ := fun z i => (z i - c i).valMinAbs
  have hinj : Set.InjOn off (finiteCells F) := by
    intro z _ z' _ e
    funext i
    have := congrFun e i
    have h2 : ((z i - c i).valMinAbs : ZMod (F.period F.top i)) = ((z' i - c i).valMinAbs : ZMod (F.period F.top i)) := by
      simp only [off] at this
      rw [this]
    rw [ZMod.coe_valMinAbs, ZMod.coe_valMinAbs] at h2
    exact sub_left_injective h2
  have hbound : ∀ z ∈ finiteCells F, off z ∈ offsetBox M := by
    intro z _
    rw [mem_offsetBox]
    intro i
    have : NeZero (F.period F.top i) := ⟨(h.period_pos _ i).ne'⟩
    have a1 := ZMod.natAbs_valMinAbs_le (z i - c i)
    have a2 : F.period F.top i ≤ M := Finset.single_le_sum (f := fun i => F.period F.top i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have a3 : F.period F.top i / 2 ≤ F.period F.top i := Nat.div_le_self _ _
    simp only [off]
    rw [Int.abs_eq_natAbs]
    exact_mod_cast a1.trans (a3.trans a2)
  have term : ∀ z ∈ finiteCells F, Real.exp (-(κ * cellSupDist z c)) ≤ ∏ i, r ^ (off z i).natAbs := by
    intro z _
    rw [Finset.prod_pow_eq_pow_sum, hr, ← Real.exp_nat_mul, Real.exp_le_exp]
    have hs : ∑ i, (off z i).natAbs ≤ 4 * cellSupDist z c := by
      calc ∑ i, (off z i).natAbs ≤ ∑ _i : Fin 4, cellSupDist z c :=
            Finset.sum_le_sum fun i _ => natAbs_le_cellSupDist z c i
        _ = 4 * cellSupDist z c := by simp
    have hs' : ((∑ i, (off z i).natAbs : ℕ) : ℝ) ≤ 4 * cellSupDist z c := by exact_mod_cast hs
    nlinarith
  calc ∑ z ∈ finiteCells F, Real.exp (-(κ * cellSupDist z c))
      ≤ ∑ z ∈ finiteCells F, ∏ i, r ^ (off z i).natAbs := Finset.sum_le_sum term
    _ = ∑ o ∈ (finiteCells F).image off, ∏ i, r ^ (o i).natAbs := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ o ∈ offsetBox M, ∏ i, r ^ (o i).natAbs := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro o ho
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ho
          exact hbound z hz
        · intro o _ _
          exact Finset.prod_nonneg fun i _ => pow_nonneg r0 _
    _ = ∏ _i : Fin 4, ∑ m ∈ Finset.Icc (-(M : ℤ)) M, r ^ m.natAbs := by
        rw [Finset.prod_univ_sum]
        rfl
    _ ≤ ∏ _i : Fin 4, 2 * (1 - r)⁻¹ := by
        apply Finset.prod_le_prod
        · intro i _
          exact Finset.sum_nonneg fun m _ => pow_nonneg r0 _
        · intro i _
          exact sum_Icc_pow_natAbs_le r0 r1 M
    _ = cellDecaySum κ := by simp [cellDecaySum, hr]
theorem siteSupDist_triangle {j : ℕ} (x y z : F.Site j) : siteSupDist x z ≤ siteSupDist x y + siteSupDist y z := by apply _root_.YangMills.Construction.LumpContours.supDist_triangle <;> assumption
theorem isAdmissible_of (h1 : Odd F.blockSide) (h2 : IsLargeCubicTorus F) : IsAdmissible F := by
  obtain ⟨n, hn, hs⟩ := h2
  exact ⟨h1, fun i => by rw [hs i]; exact hn⟩
theorem sum_fineBonds_le (h : IsAdmissible F) (f : F.Cell → ℝ) (hf : ∀ z, 0 ≤ f z) :
    ∑ b ∈ fineBonds F, f (enclosingCell b.1) ≤ 4 * ((F.blockSide : ℝ) ^ 4 * ∑ z ∈ finiteCells F, f z) := by
  unfold fineBonds
  rw [Finset.sum_product]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have := sum_sitesOfCells_le h f hf
  push_cast
  linarith
theorem cubicTorusCellGeometry : CubicTorusCellGeometry := by
  constructor
  · intro F h1 h2
    have h := isAdmissible_of h1 h2
    exact ⟨fun _ x y => siteSupDist_comm x y, fun _ x y z => siteSupDist_triangle x y z, cellSupDist_comm,
      cellSupDist_triangle, fun x y => blockSide_mul_cellSupDist_le h x y⟩
  · intro r hr
    refine ⟨4 * cellDecaySum r, by have := cellDecaySum_pos hr; positivity, ?_⟩
    intro F h1 h2 z
    have h := isAdmissible_of h1 h2
    refine (sum_fineBonds_le h (fun w => Real.exp (-(r * cellSupDist w z))) fun _ => (Real.exp_pos _).le).trans ?_
    have := sum_finiteCells_exp_le h hr z
    calc 4 * ((F.blockSide : ℝ) ^ 4 * ∑ w ∈ finiteCells F, Real.exp (-(r * cellSupDist w z)))
        ≤ 4 * ((F.blockSide : ℝ) ^ 4 * cellDecaySum r) := by gcongr
      _ = _ := by ring
end YangMills.Construction.ColdStepAtMirrorFrames.TorusCells
end
