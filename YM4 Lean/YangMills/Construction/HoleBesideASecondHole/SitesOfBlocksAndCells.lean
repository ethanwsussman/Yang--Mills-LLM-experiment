import YangMills.Construction.ColdStepAtMirrorFrames.BlockEnergyAtTheLeastChartProof
import YangMills.Construction.HoleBesideASecondHole.BlocksOfTheLevels
import YangMills.Construction.HoleBesideASecondHole.BoxesByTheirCorners
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BlockSites
open BlockAverages LumpContours CornerBoxes
variable {F : BlockFrame}
theorem intCast_siteCoords {j : ℕ} (x : F.Site j) (i : Fin 4) :
    ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.siteCoords_cast <;> assumption
theorem siteOfCoords_siteCoords {j : ℕ} (x : F.Site j) : siteOfCoords j (siteCoords x) = x := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
theorem siteOfCoords_eq_iff {j : ℕ} {a b : Fin 4 → ℤ} :
    (siteOfCoords j a : F.Site j) = siteOfCoords j b ↔ ∀ i, (F.period j i : ℤ) ∣ b i - a i := by
  constructor
  · intro h i
    have := congrFun h i
    simp only [siteOfCoords] at this
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp this
  · intro h
    funext i
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (h i)
theorem siteOfCoords_add {j : ℕ} (a b : Fin 4 → ℤ) :
    (siteOfCoords j (a + b) : F.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem top_sub_depth (F : BlockFrame) : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem period_depth (F : BlockFrame) (i : Fin 4) : F.period F.depth i = F.extent i * F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimizingChart.period_depth <;> assumption
theorem period_top (F : BlockFrame) (i : Fin 4) : F.period F.top i = F.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
theorem dvd_period_depth_of_dvd_period_top (i : Fin 4) {a b : ℤ} (h : (F.period F.top i : ℤ) ∣ a)
    (hb : b = F.blockSide * a) : (F.period F.depth i : ℤ) ∣ b := by
  rw [period_top] at h
  rw [period_depth, hb]
  push_cast
  rw [mul_comm (F.extent i : ℤ)]
  exact mul_dvd_mul_left _ h
theorem mem_sitesBelow_iff {y : F.Cell} {x : F.Site F.depth} :
    x ∈ sitesBelow F.depth y ↔ ∃ o : Fin 4 → ℤ, (∀ i, |o i| ≤ ((F.blockSide : ℤ) - 1) / 2) ∧
      x = siteOfCoords F.depth fun i => (F.blockSide : ℤ) * siteCoords y i + o i := by
  simp only [sitesBelow, top_sub_depth, pow_one, centredCube, Finset.mem_image, Fintype.mem_piFinset,
    Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, rfl⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, rfl⟩
theorem mem_cellBall_iff {y z : F.Cell} {r : ℕ} :
    z ∈ _root_.YangMills.Construction.LumpContours.cellBall y r ↔ ∃ c : Fin 4 → ℤ, (∀ i, |c i| ≤ r) ∧ z = y + siteOfCoords F.top c := by
  have hm : (((2 * r + 1 : ℕ) : ℤ) - 1) / 2 = r := by
    push_cast
    omega
  simp only [_root_.YangMills.Construction.LumpContours.cellBall, centredCube, hm, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩
theorem mem_cutBelow_cellBall (hodd : Odd F.blockSide) (y : F.Cell) (r : ℕ) (e : Fin 4 → ℤ)
    (he : ∀ i, |e i| ≤ ((F.blockSide : ℤ) - 1) / 2 + F.blockSide * r) :
    (siteOfCoords F.depth (fun i => (F.blockSide : ℤ) * siteCoords y i + e i) : F.Site F.depth) ∈
      cutBelow F.depth (_root_.YangMills.Construction.LumpContours.cellBall y r) := by
  obtain ⟨k, hk⟩ := hodd
  have hL : (F.blockSide : ℤ) = 2 * k + 1 := by rw [hk]; push_cast; ring
  have hh : ((F.blockSide : ℤ) - 1) / 2 = k := by omega
  have hLp : (0 : ℤ) < F.blockSide := by omega
  let c : Fin 4 → ℤ := fun i => (e i + k) / F.blockSide
  let o : Fin 4 → ℤ := fun i => e i - F.blockSide * c i
  have hco : ∀ i, (F.blockSide : ℤ) * c i + o i = e i := fun i => by simp only [o]; ring
  have ho : ∀ i, -(k : ℤ) ≤ o i ∧ o i ≤ k := by
    intro i
    have h1 := Int.emod_add_mul_ediv (e i + k) (F.blockSide : ℤ)
    have h2 := Int.emod_nonneg (e i + k) hLp.ne'
    have h3 := Int.emod_lt_of_pos (e i + k) hLp
    simp only [o, c]
    constructor <;> linarith
  have hc : ∀ i, |c i| ≤ r := by
    intro i
    have h1 := he i
    rw [hh, abs_le] at h1
    have h2 := ho i
    have h3 := hco i
    rw [abs_le]
    constructor
    · by_contra hlt
      have : c i + 1 ≤ -(r : ℤ) := by omega
      nlinarith
    · by_contra hlt
      have : (r : ℤ) + 1 ≤ c i := by omega
      nlinarith
  refine Finset.mem_biUnion.mpr ⟨y + siteOfCoords F.top c, mem_cellBall_iff.mpr ⟨c, hc, rfl⟩, ?_⟩
  refine mem_sitesBelow_iff.mpr ⟨o, fun i => ?_, ?_⟩
  · rw [hh, abs_le]
    exact ho i
  · refine siteOfCoords_eq_iff.mpr fun i => ?_
    have h1 : ((siteCoords y i + c i : ℤ) : ZMod (F.period F.top i)) =
        ((siteCoords (y + siteOfCoords F.top c) i : ℤ) : ZMod (F.period F.top i)) := by
      rw [intCast_siteCoords]
      simp [intCast_siteCoords, siteOfCoords]
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
    exact dvd_period_depth_of_dvd_period_top i h2 (by
      have := hco i
      linear_combination this)
theorem eq_of_mem_sitesBelow (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {y y' : F.Cell}
    {x : F.Site F.depth} (h : x ∈ sitesBelow F.depth y) (h' : x ∈ sitesBelow F.depth y') : y = y' := by
  obtain ⟨k, hk⟩ := hodd
  have hL : (F.blockSide : ℤ) = 2 * k + 1 := by rw [hk]; push_cast; ring
  have hh : ((F.blockSide : ℤ) - 1) / 2 = k := by omega
  have hLp : (0 : ℤ) < F.blockSide := by omega
  obtain ⟨o, ho, e⟩ := mem_sitesBelow_iff.mp h
  obtain ⟨o', ho', e'⟩ := mem_sitesBelow_iff.mp h'
  have hd := siteOfCoords_eq_iff.mp (e.symm.trans e')
  funext i
  have hi := hd i
  rw [period_depth] at hi
  have h1 : (F.blockSide : ℤ) ∣ o' i - o i := by
    have h2 : (F.blockSide : ℤ) ∣ (F.blockSide : ℤ) * siteCoords y' i + o' i -
        ((F.blockSide : ℤ) * siteCoords y i + o i) :=
      (Dvd.intro_left _ rfl).trans (by push_cast at hi; exact hi)
    have h3 : (F.blockSide : ℤ) * siteCoords y' i + o' i - ((F.blockSide : ℤ) * siteCoords y i + o i) =
        (F.blockSide : ℤ) * (siteCoords y' i - siteCoords y i) + (o' i - o i) := by ring
    rw [h3] at h2
    exact (Int.dvd_add_right (Dvd.intro _ rfl)).mp h2
  have h2 := ho i
  have h3 := ho' i
  rw [hh, abs_le] at h2 h3
  have h4 : o' i - o i = 0 := Int.eq_zero_of_abs_lt_dvd h1 (by
    rw [abs_lt]
    constructor <;> omega)
  have h5 : (F.extent i : ℤ) ∣ siteCoords y' i - siteCoords y i := by
    have h6 : (F.blockSide : ℤ) * siteCoords y' i + o' i - ((F.blockSide : ℤ) * siteCoords y i + o i) =
        (F.blockSide : ℤ) * (siteCoords y' i - siteCoords y i) := by
      have : o' i = o i := by omega
      rw [this]
      ring
    rw [h6] at hi
    push_cast at hi
    rw [mul_comm (F.extent i : ℤ)] at hi
    exact (mul_dvd_mul_iff_left hLp.ne').mp hi
  rw [← period_top] at h5
  have h7 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr h5
  rwa [intCast_siteCoords, intCast_siteCoords] at h7
theorem mem_sitesBelow_enclosingCell (hodd : Odd F.blockSide) (x : F.Site F.depth) :
    x ∈ sitesBelow F.depth (enclosingCell x) := by
  obtain ⟨k, hk⟩ := hodd
  have hL : (F.blockSide : ℤ) = 2 * k + 1 := by rw [hk]; push_cast; ring
  have hh : ((F.blockSide : ℤ) - 1) / 2 = k := by omega
  have hLp : (0 : ℤ) < F.blockSide := by omega
  let m : Fin 4 → ℤ := fun i => (siteCoords x i + k) / F.blockSide
  let o : Fin 4 → ℤ := fun i => siteCoords x i - F.blockSide * m i
  have hm : (enclosingCell x : F.Cell) = siteOfCoords F.top m := by
    funext i
    simp only [enclosingCell, siteOfCoords, top_sub_depth, pow_one, m, hh]
  refine mem_sitesBelow_iff.mpr ⟨o, fun i => ?_, ?_⟩
  · rw [hh, abs_le]
    have h1 := Int.emod_add_mul_ediv (siteCoords x i + k) (F.blockSide : ℤ)
    have h2 := Int.emod_nonneg (siteCoords x i + k) hLp.ne'
    have h3 := Int.emod_lt_of_pos (siteCoords x i + k) hLp
    simp only [o, m]
    constructor <;> linarith
  · conv_lhs => rw [← siteOfCoords_siteCoords x]
    refine siteOfCoords_eq_iff.mpr fun i => ?_
    have h1 : ((m i : ℤ) : ZMod (F.period F.top i)) =
        ((siteCoords (enclosingCell x) i : ℤ) : ZMod (F.period F.top i)) := by
      rw [intCast_siteCoords, hm]
      rfl
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
    exact dvd_period_depth_of_dvd_period_top i h2 (by
      simp only [o]
      ring)
theorem enclosingCell_eq_of_mem_sitesBelow (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {x : F.Site F.depth} {y : F.Cell} (h : x ∈ sitesBelow F.depth y) : enclosingCell x = y :=
  eq_of_mem_sitesBelow hodd hs (mem_sitesBelow_enclosingCell hodd x) h
theorem mem_cutBelow_iff (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {x : F.Site F.depth}
    {X : Finset F.Cell} : x ∈ cutBelow F.depth X ↔ enclosingCell x ∈ X := by
  constructor
  · intro h
    obtain ⟨y, hy, hx⟩ := Finset.mem_biUnion.mp h
    rwa [enclosingCell_eq_of_mem_sitesBelow hodd hs hx]
  · intro h
    exact Finset.mem_biUnion.mpr ⟨_, h, mem_sitesBelow_enclosingCell hodd x⟩
theorem exists_offset_of_supDist_le {j : ℕ} [∀ i, NeZero (F.period j i)] {x x' : F.Site j} {m : ℕ}
    (h : supDist x x' ≤ m) : ∃ d : Fin 4 → ℤ, (∀ i, |d i| ≤ m) ∧ x' = x + siteOfCoords j d := by
  refine ⟨fun i => -((x i - x' i).valMinAbs), fun i => ?_, ?_⟩
  · have h1 : ((x i - x' i).valMinAbs).natAbs ≤ m :=
      (Finset.le_sup (f := fun i => ((x i - x' i).valMinAbs).natAbs) (Finset.mem_univ i)).trans h
    simp only [abs_neg]
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1
  · funext i
    simp [siteOfCoords, ZMod.coe_valMinAbs]
theorem supDist_add_le {j : ℕ} [∀ i, NeZero (F.period j i)] {x : F.Site j} {d : Fin 4 → ℤ} {m : ℕ}
    (hd : ∀ i, |d i| ≤ m) (hp : ∀ i, 2 * (m : ℤ) < F.period j i) :
    supDist x (x + siteOfCoords j d) ≤ m := by
  refine Finset.sup_le fun i _ => ?_
  have e : (x i - (x + siteOfCoords j d : F.Site j) i) = ((-d i : ℤ) : ZMod (F.period j i)) := by
    simp [siteOfCoords]
  have h1 : (((-d i : ℤ) : ZMod (F.period j i))).valMinAbs = -d i := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_, ?_⟩ <;> have := hd i <;> have := hp i <;> rw [abs_le] at * <;> omega
  rw [e, h1]
  have := hd i
  rw [abs_le] at this
  omega
theorem cellSupDist_add_le [∀ i, NeZero (F.period F.top i)] {y : F.Cell} {c : Fin 4 → ℤ} {m : ℕ}
    (hd : ∀ i, |c i| ≤ m) (hp : ∀ i, 2 * (m : ℤ) < F.period F.top i) :
    cellSupDist y (y + siteOfCoords F.top c) ≤ m :=
  supDist_add_le hd hp
theorem supDist_comm {j : ℕ} [∀ i, NeZero (F.period j i)] (x y : F.Site j) :
    supDist x y = supDist y x := by
  simp only [supDist]
  congr 1
  funext i
  rw [← neg_sub (y i) (x i), ZMod.natAbs_valMinAbs_neg]
theorem subset_thicken {j : ℕ} (m : ℕ) (X : Finset (F.Site j)) : X ⊆ thicken m X := by
  intro x hx
  refine Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨0, ?_, ?_⟩⟩
  · refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_
    have : (((2 * m + 1 : ℕ) : ℤ) - 1) / 2 = m := by
      push_cast
      omega
    rw [this]
    simp
  · funext i
    simp [siteOfCoords]
theorem add_mem_cutBelow_cellBall (hodd : Odd F.blockSide) {y : F.Cell} {x : F.Site F.depth}
    (hx : x ∈ sitesBelow F.depth y) (d : Fin 4 → ℤ) (r : ℕ) (hd : ∀ i, |d i| ≤ F.blockSide * r) :
    x + siteOfCoords F.depth d ∈ cutBelow F.depth (_root_.YangMills.Construction.LumpContours.cellBall y r) := by
  obtain ⟨o, ho, rfl⟩ := mem_sitesBelow_iff.mp hx
  have := mem_cutBelow_cellBall hodd y r (o + d) fun i => by
    have h1 := ho i
    have h2 := hd i
    rw [abs_le] at h1 h2 ⊢
    simp only [Pi.add_apply]
    constructor <;> linarith
  have e : (siteOfCoords F.depth (fun i => (F.blockSide : ℤ) * siteCoords y i + (o + d) i) :
      F.Site F.depth) =
      siteOfCoords F.depth (fun i => (F.blockSide : ℤ) * siteCoords y i + o i) + siteOfCoords F.depth d := by
    funext i
    simp [siteOfCoords, add_assoc]
  rwa [e] at this
theorem lumpOf_subset_sitesBelow (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    (g : LumpGrid F.blockSide) {x : F.Site F.depth} {y : F.Cell} (hx : x ∈ sitesBelow F.depth y) :
    lumpOf g x ⊆ sitesBelow F.depth y := by
  have hLpos := hodd.pos
  intro z hz
  obtain ⟨a, ha, rfl⟩ := (mem_boxOfCorners (F := F) (q := lumpCornerPair g x)).mp hz
  obtain ⟨o, ho, hxe⟩ := mem_sitesBelow_iff.mp hx
  refine mem_sitesBelow_iff.mpr ⟨fun i => a i - (siteCoords x i - offsetFromCentre F.blockSide (siteCoords x i)),
    fun i => ?_, ?_⟩
  · obtain ⟨_, hb⟩ := offsetFromCentre_spec hLpos hodd (siteCoords x i)
    obtain ⟨b1, b2, b3, b4⟩ := g.mem_interval _ hb
    have h1 := ha i
    simp only [lumpCornerPair] at h1
    rw [abs_le]
    beta_reduce
    constructor <;> omega
  · refine siteOfCoords_eq_iff.mpr fun i => ?_
    have h1 : (F.blockSide : ℤ) ∣ siteCoords x i - offsetFromCentre F.blockSide (siteCoords x i) :=
      (offsetFromCentre_spec hLpos hodd _).1
    have hc := siteOfCoords_eq_iff.mp ((siteOfCoords_siteCoords x).trans hxe) i
    have hLper : (F.blockSide : ℤ) ∣ (F.period F.depth i : ℤ) := by
      rw [period_depth]
      push_cast
      exact Dvd.intro_left _ rfl
    have h2 : (F.blockSide : ℤ) ∣ siteCoords x i - o i := by
      have h3 := hLper.trans hc
      have h4 : (F.blockSide : ℤ) ∣ (F.blockSide : ℤ) * siteCoords y i := Dvd.intro _ rfl
      have h5 := dvd_sub h4 h3
      have e : (F.blockSide : ℤ) * siteCoords y i - ((F.blockSide : ℤ) * siteCoords y i + o i - siteCoords x i) =
          siteCoords x i - o i := by ring
      rwa [e] at h5
    have h3 : offsetFromCentre F.blockSide (siteCoords x i) = o i := by
      have h4 := dvd_sub h2 h1
      have e : siteCoords x i - o i - (siteCoords x i - offsetFromCentre F.blockSide (siteCoords x i)) =
          offsetFromCentre F.blockSide (siteCoords x i) - o i := by
        ring
      rw [e] at h4
      obtain ⟨k, hk⟩ := hodd
      have hL : (F.blockSide : ℤ) = 2 * k + 1 := by rw [hk]; push_cast; ring
      have hh : ((F.blockSide : ℤ) - 1) / 2 = k := by omega
      have h5 := (offsetFromCentre_spec hLpos ⟨k, hk⟩ (siteCoords x i)).2
      have h6 := ho i
      rw [hh, abs_le] at h5 h6
      have h7 := Int.eq_zero_of_abs_lt_dvd h4 (by
        rw [abs_lt]
        constructor <;> omega)
      omega
    have e : (F.blockSide : ℤ) * siteCoords y i +
        (a i - (siteCoords x i - offsetFromCentre F.blockSide (siteCoords x i))) - a i =
        (F.blockSide : ℤ) * siteCoords y i + o i - siteCoords x i := by
      rw [h3]
      ring
    beta_reduce
    rw [e]
    exact hc
end YangMills.Construction.BlockSites
end
