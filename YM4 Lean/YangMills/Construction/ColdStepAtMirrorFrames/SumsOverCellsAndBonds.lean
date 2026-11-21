import YangMills.Construction.ColdChainAtEveryLevel.LinesOfTheBlocksOfABond
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsInABlock
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames.CellSums
open BlockOffsets
variable {F : BlockFrame}
def residueNorm {n : ℕ} (u : ZMod n) : ℕ := u.valMinAbs.natAbs
theorem residueNorm_le_natAbs_of_cast {n : ℕ} [NeZero n] (u : ZMod n) (z : ℤ) (h : (z : ZMod n) = u) :
    residueNorm u ≤ z.natAbs := by
  unfold residueNorm
  apply ZMod.natAbs_min_of_le_div_two n u.valMinAbs z
  · rw [ZMod.coe_valMinAbs, h]
  · exact ZMod.natAbs_valMinAbs_le u
theorem residueNorm_add_le {n : ℕ} [NeZero n] (u v : ZMod n) :
    residueNorm (u + v) ≤ residueNorm u + residueNorm v := by
  refine (residueNorm_le_natAbs_of_cast (u + v) (u.valMinAbs + v.valMinAbs) (by simp)).trans ?_
  exact Int.natAbs_add_le _ _
theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem cellSupDist_triangle (hs : ∀ i, 0 < F.extent i) (x y z : F.Cell) :
    cellSupDist x z ≤ cellSupDist x y + cellSupDist y z := by
  unfold cellSupDist
  refine Finset.sup_le fun i _ => ?_
  have : NeZero (F.period F.top i) := ⟨by rw [period_top]; exact (hs i).ne'⟩
  have h1 := residueNorm_add_le (x i - y i) (y i - z i)
  have e : x i - y i + (y i - z i) = x i - z i := by ring
  rw [e] at h1
  have h2 : residueNorm (x i - y i) ≤ Finset.univ.sup fun i => ((x i - y i).valMinAbs).natAbs :=
    Finset.le_sup (f := fun i => ((x i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
  have h3 : residueNorm (y i - z i) ≤ Finset.univ.sup fun i => ((y i - z i).valMinAbs).natAbs :=
    Finset.le_sup (f := fun i => ((y i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
  exact h1.trans (add_le_add h2 h3)
theorem exists_eq_cellCentre_add (hcov : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) :
    ∃ h ∈ centredCube F.blockSide, x = cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth h := by
  have hx := hcov F hL (fun i => by have := hs i; omega) x
  unfold sitesOfCells at hx
  obtain ⟨z, -, hz⟩ := Finset.mem_biUnion.1 hx
  obtain ⟨h, hh, e⟩ := Finset.mem_image.1 hz
  have hh' : h ∈ centredCube F.blockSide := by simpa [top_sub_depth] using hh
  have e' : enclosingCell x = z := by rw [← e]; exact enclosingCell_offset hL hs z h hh'
  exact ⟨h, hh', by rw [e', e]⟩
theorem two_mul_abs_le_of_mem_centredCube {L : ℕ} (hL : Odd L) {h : Fin 4 → ℤ} (hh : h ∈ centredCube L)
    (i : Fin 4) : 2 * |h i| ≤ (L : ℤ) - 1 := by
  have := (mem_centredCube_iff h).1 hh i
  obtain ⟨k, hk⟩ := hL
  have e : halfSide L = k := by
    unfold halfSide
    rw [hk]
    push_cast
    omega
  rw [e] at this
  have h2 : |h i| ≤ (k : ℤ) := abs_le.2 this
  rw [hk]
  push_cast
  linarith
theorem intCast_cast_eq {n : ℕ} [NeZero n] (u : ZMod n) : (((ZMod.cast u : ℤ)) : ZMod n) = u := by
  simp
theorem residueNorm_mul_le (n N L : ℕ) (hN : N = n * L) [NeZero n] [NeZero N] (hL : 0 < L) (u : ZMod n)
    (x : ZMod N) (ζ δ : ℤ) (hu : (ζ : ZMod n) = u) (hx : ((L * ζ + δ : ℤ) : ZMod N) = x)
    (hδ : |δ| ≤ (L : ℤ) - 1) :
    residueNorm u * L ≤ residueNorm x + L := by
  subst hN
  have hv : ((x.valMinAbs : ℤ) : ZMod (n * L)) = ((L * ζ + δ : ℤ) : ZMod (n * L)) := by
    rw [ZMod.coe_valMinAbs, hx]
  obtain ⟨e, he⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hv
  push_cast at he
  have hd : x.valMinAbs - δ = L * (ζ - n * e) := by
    have : (L : ℤ) * ζ + δ - x.valMinAbs = n * L * e := he
    linear_combination -this
  have hs : residueNorm u ≤ (ζ - n * e).natAbs := by
    apply residueNorm_le_natAbs_of_cast
    rw [← hu]
    have hz : ((n : ℤ) : ZMod n) = 0 := by
      rw [Int.cast_natCast]
      exact ZMod.natCast_self n
    rw [Int.cast_sub, Int.cast_mul, hz, zero_mul, sub_zero]
  have h1 : ((residueNorm u * L : ℕ) : ℤ) ≤ |x.valMinAbs - δ| := by
    rw [hd, abs_mul]
    have : ((residueNorm u : ℕ) : ℤ) ≤ |ζ - n * e| := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hs
    push_cast
    rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ L), mul_comm]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h2 : |x.valMinAbs - δ| ≤ |x.valMinAbs| + |δ| := abs_sub _ _
  have h3 : |x.valMinAbs| = ((residueNorm x : ℕ) : ℤ) := by
    unfold residueNorm
    rw [Int.abs_eq_natAbs]
  have : ((residueNorm u * L : ℕ) : ℤ) ≤ ((residueNorm x + L : ℕ) : ℤ) := by
    push_cast at h1 ⊢
    rw [h3] at h2
    linarith
  exact_mod_cast this
theorem cellSupDist_mul_le_siteSupDist (hcov : BlocksCoverLowerLevel) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (x y : F.Site F.depth) :
    cellSupDist (enclosingCell x) (enclosingCell y) * F.blockSide ≤ siteSupDist x y + F.blockSide := by
  have hL0 : 0 < F.blockSide := hL.pos
  obtain ⟨h, hh, ex⟩ := exists_eq_cellCentre_add hcov hL hs x
  obtain ⟨h', hh', ey⟩ := exists_eq_cellCentre_add hcov hL hs y
  suffices hsup : cellSupDist (enclosingCell x) (enclosingCell y) ≤ (siteSupDist x y + F.blockSide) / F.blockSide from
    (Nat.mul_le_mul_right _ hsup).trans (Nat.div_mul_le_self _ _)
  unfold cellSupDist
  refine Finset.sup_le fun i _ => ?_
  rw [Nat.le_div_iff_mul_le hL0]
  have hn : 0 < F.extent i := by have := hs i; omega
  have i3 : NeZero (F.period F.depth i) := ⟨by rw [period_depth]; exact (Nat.mul_pos hn hL0).ne'⟩
  have i4 : NeZero (F.period F.top i) := ⟨by rw [period_top]; exact hn.ne'⟩
  have hN : F.period F.depth i = F.period F.top i * F.blockSide := by rw [period_depth, period_top]
  obtain ⟨z, hz⟩ : ∃ z, z = enclosingCell x := ⟨_, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z, z = enclosingCell y := ⟨_, rfl⟩
  rw [← hz] at ex ⊢
  rw [← hz'] at ey ⊢
  have hres := residueNorm_mul_le (F.period F.top i) (F.period F.depth i) F.blockSide hN hL0 (z i - z' i)
    (x i - y i) (siteCoords z i - siteCoords z' i) (h i - h' i) (by
      rw [Int.cast_sub]
      unfold siteCoords
      rw [intCast_cast_eq, intCast_cast_eq]) (by
      rw [ex, ey]
      simp only [cellCentre, siteOfCoords, top_sub_depth, pow_one, Pi.add_apply]
      push_cast
      ring) (by
      have a1 := two_mul_abs_le_of_mem_centredCube hL hh i
      have a2 := two_mul_abs_le_of_mem_centredCube hL hh' i
      have a3 : |h i - h' i| ≤ |h i| + |h' i| := abs_sub _ _
      linarith)
  have hle : residueNorm (x i - y i) ≤ siteSupDist x y :=
    Finset.le_sup (f := fun i => ((x i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
  calc _ = residueNorm (z i - z' i) * F.blockSide := rfl
    _ ≤ residueNorm (x i - y i) + F.blockSide := hres
    _ ≤ _ := Nat.add_le_add_right hle _
theorem sum_bonds_le_sum_cells (hcov : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (g : F.Cell → ℝ) (hg : ∀ z, 0 ≤ g z) (B : Finset (F.Site F.depth × Fin 4)) :
    ∑ b ∈ B, g (enclosingCell b.1) ≤ 4 * ((centredCube F.blockSide).card : ℝ) * ∑ z ∈ finiteCells F, g z := by
  classical
  have hsub : B ⊆ sitesOfCells (finiteCells F) F.depth ×ˢ (Finset.univ : Finset (Fin 4)) := fun b _ =>
    Finset.mem_product.2 ⟨hcov F hL (fun i => by have := hs i; omega) b.1, Finset.mem_univ _⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => hg _).trans ?_
  rw [Finset.sum_product]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have hdis : ∀ z ∈ finiteCells F, ∀ x ∈ (centredCube (F.blockSide ^ (F.top - F.depth))).image
      (fun h => (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth)), enclosingCell x = z := by
    intro z _ x hx
    obtain ⟨h, hh, e⟩ := Finset.mem_image.1 hx
    rw [← e]
    exact enclosingCell_offset hL hs z h (by simpa [top_sub_depth] using hh)
  unfold sitesOfCells
  rw [Finset.sum_biUnion]
  · have : ∀ z ∈ finiteCells F, ∑ x ∈ (centredCube (F.blockSide ^ (F.top - F.depth))).image
        (fun h => (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth)), g (enclosingCell x) ≤
          ((centredCube F.blockSide).card : ℝ) * g z := by
      intro z hz
      rw [Finset.sum_congr rfl fun x hx => by rw [hdis z hz x hx]]
      rw [Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (hg z)
      have := Finset.card_image_le (s := centredCube (F.blockSide ^ (F.top - F.depth)))
        (f := fun h => (cellCentre F.depth z + siteOfCoords F.depth h : F.Site F.depth))
      simpa [top_sub_depth] using (Nat.cast_le (α := ℝ)).2 this
    have h2 := Finset.sum_le_sum this
    rw [← Finset.mul_sum] at h2
    have h4 : (0 : ℝ) ≤ 4 := by norm_num
    calc _ ≤ (4 : ℝ) * (((centredCube F.blockSide).card : ℝ) * ∑ z ∈ finiteCells F, g z) :=
          mul_le_mul_of_nonneg_left h2 h4
      _ = _ := by ring
  · intro z hz z' hz' hne
    refine Finset.disjoint_left.2 fun x hx hx' => hne ?_
    rw [← hdis z hz x hx, ← hdis z' hz' x hx']
theorem exists_bound_sum_exp_cellSupDist (r : ℝ) (hr : 0 < r) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ (F : BlockFrame) (c : F.Cell), (∀ i, 2 ≤ F.extent i) →
    ∑ z ∈ finiteCells F, Real.exp (-(r * cellSupDist z c)) ≤ M := by
  classical
  set φ : ℤ → ℝ := fun t => Real.exp (-(r / 4 * t.natAbs)) with hφ
  have hφ0 : ∀ t, 0 ≤ φ t := fun t => (Real.exp_pos _).le
  have hsum : Summable φ := by
    have hq : Real.exp (-(r / 4)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have hg := summable_geometric_of_lt_one (Real.exp_pos (-(r / 4))).le hq
    have e : ∀ n : ℕ, Real.exp (-(r / 4)) ^ n = Real.exp (-(r / 4 * n)) := fun n => by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    refine summable_int_iff_summable_nat_and_neg.2 ⟨?_, ?_⟩
    · refine hg.congr fun n => ?_
      simp [hφ, e]
    · refine hg.congr fun n => ?_
      simp [hφ, e]
  refine ⟨(∑' t, φ t) ^ 4, pow_nonneg (tsum_nonneg hφ0) 4, ?_⟩
  intro F c hs
  have hn : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have inst : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by rw [period_top]; exact (hn i).ne'⟩
  set o : F.Cell → Fin 4 → ℤ := fun z i => (z i - c i).valMinAbs with ho
  set N : ℤ := ∑ i, (F.extent i : ℤ) with hN
  have hinj : Function.Injective o := by
    intro z z' e
    funext i
    have := congrFun e i
    simp only [ho] at this
    have h2 := congrArg (fun t : ℤ => (t : ZMod (F.period F.top i))) this
    simp only [ZMod.coe_valMinAbs] at h2
    exact sub_left_injective h2
  have hpt : ∀ z ∈ finiteCells F, Real.exp (-(r * cellSupDist z c)) ≤ ∏ i, φ (o z i) := by
    intro z _
    rw [hφ]
    simp only
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    have hs4 : ∑ i, (((o z i).natAbs : ℕ) : ℝ) ≤ 4 * cellSupDist z c := by
      have : ∀ i ∈ (Finset.univ : Finset (Fin 4)), (((o z i).natAbs : ℕ) : ℝ) ≤ cellSupDist z c := fun i _ => by
        have : (o z i).natAbs ≤ cellSupDist z c :=
          Finset.le_sup (f := fun i => ((z i - c i).valMinAbs).natAbs) (Finset.mem_univ i)
        exact_mod_cast this
      have := Finset.sum_le_sum this
      simpa using this
    have e : ∑ i, -(r / 4 * ((o z i).natAbs : ℝ)) = -(r / 4 * ∑ i, ((o z i).natAbs : ℝ)) := by
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    rw [e]
    nlinarith
  refine (Finset.sum_le_sum hpt).trans ?_
  have hmem : ∀ z ∈ finiteCells F, o z ∈ Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-N) N := by
    intro z _
    refine Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ?_
    have h1 : (o z i).natAbs ≤ F.period F.top i / 2 := ZMod.natAbs_valMinAbs_le _
    have h2 : F.period F.top i / 2 ≤ F.extent i := by rw [period_top]; omega
    have h3 : (F.extent i : ℤ) ≤ N :=
      Finset.single_le_sum (f := fun i => (F.extent i : ℤ)) (fun i _ => by positivity) (Finset.mem_univ i)
    have h4 : |o z i| ≤ N := by
      rw [Int.abs_eq_natAbs]
      have : ((o z i).natAbs : ℤ) ≤ F.extent i := by exact_mod_cast h1.trans h2
      linarith
    exact abs_le.1 h4
  have h1 : ∑ z ∈ finiteCells F, ∏ i, φ (o z i) ≤
      ∑ v ∈ Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-N) N, ∏ i, φ (v i) := by
    have himg : ∑ z ∈ finiteCells F, ∏ i, φ (o z i) = ∑ v ∈ (finiteCells F).image o, ∏ i, φ (v i) := by
      rw [Finset.sum_image fun a _ b _ e => hinj e]
    rw [himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun v _ _ => Finset.prod_nonneg fun i _ => hφ0 _
    intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
    exact hmem z hz
  refine h1.trans ?_
  rw [← Finset.prod_univ_sum]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun t _ => hφ0 t) (hsum.sum_le_tsum _ fun t _ => hφ0 t) 4
theorem siteSupDist_add_unitStep_le (hs : ∀ i, 2 ≤ F.extent i) (hL : 0 < F.blockSide) (x : F.Site F.depth)
    (i : Fin 4) : siteSupDist x (x + unitStep F.depth i) ≤ 1 := by
  unfold siteSupDist
  refine Finset.sup_le fun l _ => ?_
  have : NeZero (F.period F.depth l) := ⟨by
    rw [period_depth]
    exact (Nat.mul_pos (by have := hs l; omega) hL).ne'⟩
  have e : x l - (x + unitStep F.depth i : F.Site F.depth) l =
      ((- (Pi.single i 1 : Fin 4 → ℤ) l : ℤ) : ZMod (F.period F.depth l)) := by
    simp [unitStep, siteOfCoords]
  have h := residueNorm_le_natAbs_of_cast (x l - (x + unitStep F.depth i : F.Site F.depth) l)
    (- (Pi.single i 1 : Fin 4 → ℤ) l) e.symm
  refine h.trans ?_
  by_cases hl : l = i
  · subst hl; simp
  · simp [Pi.single_eq_of_ne hl]
theorem cellSupDist_add_unitStep_le (hcov : BlocksCoverLowerLevel) (hL : Odd F.blockSide) (hL3 : 3 ≤ F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (x : F.Site F.depth) (i : Fin 4) :
    cellSupDist (enclosingCell x) (enclosingCell (x + unitStep F.depth i)) ≤ 1 := by
  have h1 := cellSupDist_mul_le_siteSupDist hcov hL hs x (x + unitStep F.depth i)
  have h2 := siteSupDist_add_unitStep_le hs hL.pos x i
  by_contra hc
  have : 2 ≤ cellSupDist (enclosingCell x) (enclosingCell (x + unitStep F.depth i)) := by omega
  have h3 : 2 * F.blockSide ≤
      cellSupDist (enclosingCell x) (enclosingCell (x + unitStep F.depth i)) * F.blockSide :=
    Nat.mul_le_mul_right _ this
  omega
end YangMills.Construction.ColdStepAtMirrorFrames.CellSums
end
