import YangMills.Construction.ColdChainAtEveryLevel.GaugeMapAgainstTheCurl
import YangMills.Construction.ColdChainAtEveryLevel.GaugeMapAtABondForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.GaugeCurlBound
open BlockAverages PatchForms PatchPotentials PotentialMeans BondGauge PatchDifferences PatchFrames PatchPoints GaugeMap
  LatticeFractionalIntegration FiniteDifferences
section Sizes
variable {F : BlockFrame} {S : Finset F.Cell} {ι : Type} [Fintype ι]
open Classical in
def indexSlice (Bd : Finset (F.Site 0 × ι)) (g : F.Site 0 × ι → ℝ) (k : ι) : F.Site 0 → ℝ :=
  fun x => if (x, k) ∈ Bd then g (x, k) else 0
open Classical in
theorem sum_enclosing_eq_sum_indexSlice {Bd At : Finset (F.Site 0 × ι)} (hBd : ∀ b ∈ Bd, b.1 ∈ sitesOfCells S 0)
    {z : F.Cell} (hAt : ∀ b, b ∈ At ↔ b ∈ Bd ∧ enclosingCell b.1 = z) (G : F.Site 0 × ι → ℝ) :
    ∑ b ∈ At, G b = ∑ k, ∑ x ∈ cellSites S z, if (x, k) ∈ Bd then G (x, k) else 0 := by
  have hsub : At ⊆ cellSites S z ×ˢ Finset.univ := by
    intro b hb
    obtain ⟨h1, h2⟩ := (hAt b).1 hb
    exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hBd b h1, h2⟩, Finset.mem_univ _⟩
  calc ∑ b ∈ At, G b = ∑ b ∈ At, (if b ∈ Bd then G b else 0) :=
        Finset.sum_congr rfl fun b hb => by rw [if_pos ((hAt b).1 hb).1]
    _ = ∑ b ∈ cellSites S z ×ˢ Finset.univ, (if b ∈ Bd then G b else 0) := by
        refine Finset.sum_subset hsub fun b hb hn => ?_
        rw [if_neg]
        intro h1
        exact hn ((hAt b).2 ⟨h1, (Finset.mem_filter.1 (Finset.mem_product.1 hb).1).2⟩)
    _ = _ := by
        rw [Finset.sum_product, Finset.sum_comm]
omit [Fintype ι] in
theorem indexSlice_nonneg {Bd : Finset (F.Site 0 × ι)} {g : F.Site 0 × ι → ℝ} (hg : ∀ b, 0 ≤ g b) (k : ι)
    (x : F.Site 0) :
    0 ≤ indexSlice Bd g k x := by
  classical
  simp only [indexSlice]
  split_ifs
  · exact hg _
  · exact le_rfl
theorem lpNorm_enclosing_le_sum_indexSlice {q : ℝ} (hq : 1 ≤ q) {Bd At : Finset (F.Site 0 × ι)}
    (hBd : ∀ b ∈ Bd, b.1 ∈ sitesOfCells S 0) {z : F.Cell}
    (hAt : ∀ b, b ∈ At ↔ b ∈ Bd ∧ enclosingCell b.1 = z) {g : F.Site 0 × ι → ℝ} (hg : ∀ b, 0 ≤ g b)
    {w : F.Site 0 → ℝ} (hw : ∀ x, 0 ≤ w x) :
    (∑ b ∈ At, (w b.1 * g b) ^ q) ^ (1 / q) ≤ ∑ k, weightedLpNormOnCell q S w (indexSlice Bd g k) z ∧
      ∀ k, weightedLpNormOnCell q S w (indexSlice Bd g k) z ≤ (∑ b ∈ At, (w b.1 * g b) ^ q) ^ (1 / q) := by
  classical
  have hq0 : 0 < q := by linarith
  have e : ∑ b ∈ At, (w b.1 * g b) ^ q = ∑ k, ∑ x ∈ cellSites S z, |w x * indexSlice Bd g k x| ^ q := by
    rw [sum_enclosing_eq_sum_indexSlice hBd hAt]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun x _ => ?_
    simp only [indexSlice]
    split_ifs with h1
    · rw [abs_of_nonneg (mul_nonneg (hw x) (hg _))]
    · rw [mul_zero, abs_zero, Real.zero_rpow hq0.ne']
  have hX : ∀ k, 0 ≤ ∑ x ∈ cellSites S z, |w x * indexSlice Bd g k x| ^ q := fun k =>
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
  rw [e]
  constructor
  · refine (rpow_sum_le_sum_rpow_of_le_one Finset.univ _ (fun k _ => hX k) (by positivity) ?_)
    rw [div_le_one hq0]
    exact hq
  · intro k
    refine Real.rpow_le_rpow (hX k) ?_ (by positivity)
    exact Finset.single_le_sum (f := fun k => ∑ x ∈ cellSites S z, |w x * indexSlice Bd g k x| ^ q)
      (fun k _ => hX k) (Finset.mem_univ k)
end Sizes
section Forms
variable {F : BlockFrame} {S : Finset F.Cell}
theorem formNormOn_eq_sum_indexSlice (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (x : F.Site 0) :
    formNormOn S f x = ∑ k, indexSlice (innerBonds S 0) (fun b => ‖f b.1 b.2‖) k x := by
  classical
  simp only [formNormOn, indexSlice]
theorem fst_mem_of_mem_innerBonds {b : F.Site 0 × Fin 4} (hb : b ∈ innerBonds S 0) : b.1 ∈ sitesOfCells S 0 :=
  (Finset.mem_product.1 (Finset.mem_filter.1 hb).1).1
theorem fst_mem_of_mem_innerPlaquettes {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S 0) :
    p.1 ∈ sitesOfCells S 0 :=
  (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).1
theorem mem_bondsOver_singleton (z : F.Cell) (b : F.Site 0 × Fin 4) :
    b ∈ bondsOver S {z} 0 ↔ b ∈ innerBonds S 0 ∧ enclosingCell b.1 = z := by
  classical
  simp [bondsOver]
theorem mem_plaquettesOver_singleton (z : F.Cell) (p : F.Site 0 × Fin 4 × Fin 4) :
    p ∈ plaquettesOver S {z} 0 ↔ p ∈ innerPlaquettes S 0 ∧ enclosingCell p.1 = z := by
  classical
  simp [plaquettesOver]
theorem cellBondNorm_le_formNormOn {q : ℝ} (hq : 1 ≤ q) {w : F.Site 0 → ℝ} (hw : ∀ x, 0 ≤ w x)
    (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (z : F.Cell) :
    cellBondNorm q S w f z ≤ 4 * weightedLpNormOnCell q S w (formNormOn S f) z := by
  classical
  have h1 := (lpNorm_enclosing_le_sum_indexSlice hq (fun b hb => fst_mem_of_mem_innerBonds hb)
    (mem_bondsOver_singleton (S := S) z) (g := fun b => ‖f b.1 b.2‖) (fun _ => norm_nonneg _) hw).1
  refine h1.trans ?_
  have hc := weightedLpNormOnCell_isCellSeminorm hq S w
  calc _ ≤ ∑ _k : Fin 4, weightedLpNormOnCell q S w (formNormOn S f) z := Finset.sum_le_sum fun k _ => by
        refine hc.mono_abs _ _ _ fun x _ => ?_
        rw [abs_of_nonneg (indexSlice_nonneg (fun _ => norm_nonneg _) k x), abs_of_nonneg (zero_le_formNormOn _ x),
          formNormOn_eq_sum_indexSlice]
        exact Finset.single_le_sum (f := fun k => indexSlice (innerBonds S 0) (fun b => ‖f b.1 b.2‖) k x)
          (fun k _ => indexSlice_nonneg (fun _ => norm_nonneg _) k x) (Finset.mem_univ k)
    _ = _ := by simp
theorem formNormOn_le_cellBondNorm {q : ℝ} (hq : 1 ≤ q) {w : F.Site 0 → ℝ} (hw : ∀ x, 0 ≤ w x)
    (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (z : F.Cell) :
    weightedLpNormOnCell q S w (formNormOn S f) z ≤ 4 * cellBondNorm q S w f z := by
  classical
  have h1 := (lpNorm_enclosing_le_sum_indexSlice hq (fun b hb => fst_mem_of_mem_innerBonds hb)
    (mem_bondsOver_singleton (S := S) z) (g := fun b => ‖f b.1 b.2‖) (fun _ => norm_nonneg _) hw).2
  have hc := weightedLpNormOnCell_isCellSeminorm hq S w
  have e : formNormOn S f = fun x => ∑ k, indexSlice (innerBonds S 0) (fun b => ‖f b.1 b.2‖) k x :=
    funext (formNormOn_eq_sum_indexSlice f)
  rw [e]
  refine (hc.sum_le Finset.univ _ z).trans ?_
  calc _ ≤ ∑ _k : Fin 4, cellBondNorm q S w f z := Finset.sum_le_sum fun k _ => h1 k
    _ = _ := by simp
theorem curlNorm_le_cellPlaquetteNorm {q : ℝ} (hq : 1 ≤ q) {w : F.Site 0 → ℝ} (hw : ∀ x, 0 ≤ w x)
    (V : F.GaugeField F.top) (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (z : F.Cell) :
    weightedLpNormOnCell q S w (curlNorm S V u) z ≤
      16 * cellPlaquetteNorm q S w (linearizedCurl (referenceFieldChain S V 0) u) z := by
  classical
  have h1 := (lpNorm_enclosing_le_sum_indexSlice hq (fun p hp => fst_mem_of_mem_innerPlaquettes hp)
    (mem_plaquettesOver_singleton (S := S) z)
    (g := fun p => ‖linearizedCurl (referenceFieldChain S V 0) u p‖) (fun _ => norm_nonneg _) hw).2
  have hc := weightedLpNormOnCell_isCellSeminorm hq S w
  have e : curlNorm S V u = fun x => ∑ k : Fin 4 × Fin 4,
      indexSlice (innerPlaquettes S 0) (fun p => ‖linearizedCurl (referenceFieldChain S V 0) u p‖) k x := by
    funext x
    simp only [curlNorm, indexSlice]
    rw [Fintype.sum_prod_type]
  rw [e]
  refine (hc.sum_le Finset.univ _ z).trans ?_
  calc _ ≤ ∑ _k : Fin 4 × Fin 4, cellPlaquetteNorm q S w (linearizedCurl (referenceFieldChain S V 0) u) z :=
        Finset.sum_le_sum fun k _ => h1 k
    _ = _ := by simp
theorem cellBondNorm_nonneg (q : ℝ) {w : F.Site 0 → ℝ} (hw : ∀ x, 0 ≤ w x) (f : F.Site 0 → Fin 4 → ℍ[ℝ])
    (z : F.Cell) :
    0 ≤ cellBondNorm q S w f z :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (mul_nonneg (hw _) (norm_nonneg _)) _) _
theorem cellPlaquetteNorm_nonneg (q : ℝ) {w : F.Site 0 → ℝ} (hw : ∀ x, 0 ≤ w x)
    (g : F.Site 0 × Fin 4 × Fin 4 → ℍ[ℝ]) (z : F.Cell) :
    0 ≤ cellPlaquetteNorm q S w g z :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (mul_nonneg (hw _) (norm_nonneg _)) _) _
end Forms
section Tops
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {Cs r Ch : ℝ}
  {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ}
theorem nestedAverage_top_nonneg (hodd : Odd F.blockSide) (f : F.Site 0 → Fin 4 → ℝ) (hf : ∀ x k, 0 ≤ f x k)
    (y : F.Cell) (i : Fin 4) :
    0 ≤ nestedAverage f F.top y i := by
  have hNp : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hodd.pos
  rw [nestedAverage_top_eq hodd, smul_eq_mul]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hf _ _)
theorem norm_nestedAverage_patchFrameForm_le (hodd : Odd F.blockSide) (z : F.Cell)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) (y : F.Cell) (i : Fin 4) :
    ‖nestedAverage (BlockAverages.patchFrameForm S V z (toQuaternionForm u)) F.top y i‖ ≤
      nestedAverage (fun x k => ‖toQuaternionForm u x k‖) F.top y i := by
  have hNp : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hodd.pos
  rw [patchFrameForm_base_eq, nestedAverage_top_eq hodd, nestedAverage_top_eq hodd, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity), smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  exact le_of_eq (PatchForms.norm_adjointAction_apply _ _)
theorem scale_mul_nestedAverage_norm_le (h : PotentialSetting S V Cs r Ch) (hN : CellNormFamily S Md Lf Sr σ K)
    (u : F.Site 0 → Fin 4 → imaginaryQuaternions) {y : F.Cell}
    {i : Fin 4} (hy : y ∈ S) (hy' : y + unitStep F.top i ∈ S) (hd : cellSupDist y (y + unitStep F.top i) ≤ 22) :
    σ y * nestedAverage (fun x k => ‖toQuaternionForm u x k‖) F.top y i ≤
      K * Md (formNormOn S (toQuaternionForm u)) y +
        K * (K * Md (formNormOn S (toQuaternionForm u)) (y + unitStep F.top i)) := by
  classical
  have hodd := h.odd_side
  have hNp := h.cellSideLength_pos
  have hsite : ∀ {g : Lattice4}, g ∈ centredCube (F.blockSide ^ F.top) → ∀ {r : ℕ}, r ≤ F.blockSide ^ F.top →
      cellCentre 0 y + siteOfCoords 0 g + (r : ℤ) • unitStep 0 i ∈ sitesOfCells S 0 := by
    intro g hg r hr
    rcases Finset.mem_union.1 (mem_cellSites_union_of_line hodd hy hy' hg hr) with h2 | h2
    · exact (Finset.mem_filter.1 h2).1
    · exact (Finset.mem_filter.1 h2).1
  have h1 : nestedAverage (fun x k => ‖toQuaternionForm u x k‖) F.top y i ≤
      (1 / (cellSideLength F : ℝ) ^ 4) * ∑ g ∈ centredCube (F.blockSide ^ F.top),
      ∑ r ∈ Finset.range (F.blockSide ^ F.top),
        formNormOn S (toQuaternionForm u) (cellCentre 0 y + siteOfCoords 0 g + (r : ℤ) • unitStep 0 i) := by
    rw [nestedAverage_top_eq hodd, smul_eq_mul]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g hg => Finset.sum_le_sum fun r hr => ?_)
      (by positivity)
    have hr' := Finset.mem_range.1 hr
    have p0 := hsite hg (r := r) hr'.le
    have p1 := hsite hg (r := r + 1) hr'
    have e : cellCentre (F := F) 0 y + siteOfCoords 0 g + (r : ℤ) • unitStep 0 i + unitStep 0 i =
        cellCentre 0 y + siteOfCoords 0 g + ((r + 1 : ℕ) : ℤ) • unitStep 0 i := by
      push_cast
      rw [add_smul, one_smul, add_assoc]
    exact norm_le_formNormOn (S := S) (toQuaternionForm u) (mem_innerBonds_of_step p0 p1 e)
  have h2 := scale_mul_flatMean_le hN h.ambient hodd hy hy' hd (formNormOn S (toQuaternionForm u))
    (zero_le_formNormOn _) (fun r => r) (fun r hr => hr.le)
  exact (mul_le_mul_of_nonneg_left h1 (hN.scale_pos y).le).trans h2
theorem classWeight_top (F : BlockFrame) (hL : 0 < F.blockSide) (φ : F.Cell → ℝ) (θ : ℝ) (p : F.Site 0)
    (c : F.Cell) :
    classWeight F φ θ p F.top c = Real.exp (φ c) := by
  have hN : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
    have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
    positivity
  have e : scaleRadius F F.top p c = (F.blockSide : ℝ) ^ F.top := by
    simp only [scaleRadius]
    exact min_eq_left (le_max_left _ _)
  simp only [classWeight]
  rw [e, div_self hN.ne', Real.one_rpow, mul_one, enclosingCell_self]
theorem exp_mul_norm_le_cellTopNorm (hL : 0 < F.blockSide) (φ : F.Cell → ℝ) (θ : ℝ) (p : F.Site 0)
    (f : F.Cell → Fin 4 → ℍ[ℝ]) {c : F.Cell × Fin 4} (hc : c ∈ innerBonds S F.top) :
    Real.exp (φ c.1) * ‖f c.1 c.2‖ ≤ cellTopNorm S (classWeight F φ θ p F.top) f c.1 := by
  classical
  have hm : c ∈ bondsOver S {c.1} F.top := by
    simp [bondsOver, hc, enclosingCell_self]
  have h1 : (classWeight F φ θ p F.top c.1 * ‖f c.1 c.2‖) ^ 2 ≤
      ∑ c' ∈ bondsOver S {c.1} F.top, (classWeight F φ θ p F.top c'.1 * ‖f c'.1 c'.2‖) ^ 2 :=
    Finset.single_le_sum (f := fun c' : F.Cell × Fin 4 =>
      (classWeight F φ θ p F.top c'.1 * ‖f c'.1 c'.2‖) ^ 2) (fun _ _ => sq_nonneg _) hm
  rw [classWeight_top F hL] at h1
  have h2 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq (by positivity)] at h2
  exact h2
end Tops
theorem isPatchFrame_mono {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell}
    {R : Lattice4 → Lattice4 → UnitQuaternion} {Cs Cs' r : ℝ}
    (hN : (0 : ℝ) ≤ cellSideLength F) (hle : Cs ≤ Cs') (hf : IsPatchFrame S V z R Cs r) :
    IsPatchFrame S V z R Cs' r :=
  ⟨hf.symm_inv, fun a ha b hb hd => (hf.norm_sub_one_le a ha b hb hd).trans
      (mul_le_mul_of_nonneg_right hle (div_nonneg (Nat.cast_nonneg _) hN)), hf.leadingTransport_eq,
    fun h a e e' h1 h2 h3 h4 h5 h6 => (hf.norm_second_diff_le h a e e' h1 h2 h3 h4 h5 h6).trans
      (div_le_div_of_nonneg_right hle (sq_nonneg _))⟩
set_option maxHeartbeats 4000000 in
theorem gaugeMapCurlBound (hHo : randomStaircaseHomotopyStatement) (hKe : cellKernelBoundsStatement)
    (hFr : patchFrameExistenceStatement) (hF2 : patchFrameComparisonStatement)
    (hTA : patchNestedAverageStatement) : gaugeMapCurlBoundStatement := by
  classical
  obtain ⟨Ch, hCh, hHom⟩ := hHo
  obtain ⟨K, hK, hKer⟩ := hKe
  obtain ⟨C1, rr, c1, hC1, hrr, hc1, hFra⟩ := hFr
  obtain ⟨C2, c2, L2, hC2, hc2, hFTw⟩ := hF2
  obtain ⟨C3, c3, L3, hC3, hc3, hTop⟩ := hTA
  obtain ⟨Cc, hCc⟩ : ∃ Cc, Cc = C1 + C2 + C3 := ⟨_, rfl⟩
  have hCc0 : 0 < Cc := by rw [hCc]; positivity
  obtain ⟨cC, hcC⟩ : ∃ cC, cC = bondCellConstant K Ch := ⟨_, rfl⟩
  have hcC0 : 0 ≤ cC := hcC ▸ bondCellConstant_nonneg hK.le hCh.le
  obtain ⟨Cf, hCf⟩ : ∃ Cf, Cf = 64 * cC * (1 + Cc) + 4 * cC * (45 ^ 4 * (20 + 8 * (K + K ^ 2))) + 1 := ⟨_, rfl⟩
  have hCf1 : 0 < Cf := by rw [hCf]; positivity
  refine ⟨min (min c1 c2) (min c3 (1 / Cc)), Cf, max (max L2 L3) ⌈1 / rr⌉₊, by positivity, hCf1, ?_⟩
  intro F m S hodd hL1 hamb hm hreg s V hs0 hsc hcold u
  have hsc1 : s ≤ c1 := hsc.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hsc2 : s ≤ c2 := hsc.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hsc3 : s ≤ c3 := hsc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsc4 : s ≤ 1 / Cc := hsc.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hL2 : L2 ≤ F.blockSide := (le_max_left _ _).trans ((le_max_left _ _).trans hL1)
  have hL3 : L3 ≤ F.blockSide := (le_max_right _ _).trans ((le_max_left _ _).trans hL1)
  have hL4 : ⌈1 / rr⌉₊ ≤ F.blockSide := (le_max_right _ _).trans hL1
  have hL := hodd.pos
  have hNp : (0 : ℝ) < cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
  obtain ⟨Cs, hCs⟩ : ∃ Cs, Cs = Cc * s := ⟨_, rfl⟩
  have hCs0 : 0 ≤ Cs := by rw [hCs]; positivity
  have hCs1 : Cs ≤ 1 := by
    rw [hCs]
    have := mul_le_mul_of_nonneg_left hsc4 hCc0.le
    rwa [mul_one_div, div_self hCc0.ne'] at this
  have hle1 : C1 * s ≤ Cs := by
    rw [hCs, hCc]
    nlinarith
  have hle2 : C2 * s ≤ Cs := by
    rw [hCs, hCc]
    nlinarith
  have hle3 : C3 * s ≤ Cs := by
    rw [hCs, hCc]
    nlinarith
  have hscale : 1 ≤ rr * cellSideLength F := by
    have h1 : 1 / rr ≤ (F.blockSide : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hL4)
    have h2 : (F.blockSide : ℝ) ≤ cellSideLength F := by
      rw [cellSideLength_cast]
      have h3 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
      exact le_self_pow₀ h3 (by simp [BlockFrame.top])
    have h3 : 1 / rr ≤ (cellSideLength F : ℝ) := h1.trans h2
    rw [div_le_iff₀ hrr] at h3
    linarith
  have hset : PotentialSetting S V Cs rr Ch := by
    refine ⟨hamb, hodd, ⟨m, by omega, hreg⟩, fun z hz => ?_, hscale, hCs0, hCs1, hCh.le, fun l c P hl hP => ?_⟩
    · obtain ⟨R, hR⟩ := hFra F m S hodd hamb hm hreg s V hs0 hsc1 hcold z hz
      exact ⟨R, isPatchFrame_mono hNp.le hle1 hR⟩
    · obtain ⟨H, G, h1, h2, h3⟩ := hHom l c P hl hP
      obtain ⟨a1, a2, a3⟩ := h3 ℍ[ℝ]
      exact ⟨H, G, h1, h2, a1, a2, a3⟩
  have hFT : ∀ b ∈ S, ∀ z ∈ cellBall S b 2, ∃ g : UnitQuaternion, ∀ x ∈ cellSites S b,
      ‖((patchFrameTransition S V z b x : UnitQuaternion) : ℍ[ℝ]) - (g : ℍ[ℝ])‖ ≤ Cs := by
    intro b hb z hz
    have hbb : b ∈ cellBall S b 2 := Finset.mem_filter.2 ⟨hb, by simp [cellSupDist]⟩
    have hbb5 : b ∈ cellBall S b 5 := Finset.mem_filter.2 ⟨hb, by simp [cellSupDist]⟩
    obtain ⟨g, h1, -⟩ := hFTw F m S hodd hL2 hamb hm hreg s V hs0 hsc2 hcold b hb z hz b hbb
    exact ⟨g, fun x hx => (h1 b hbb5 x hx).trans hle2⟩
  have hTopN : ∀ z ∈ S, ∀ c ∈ innerBonds S F.top, enclosingCell c.1 ∈ cellBall S z 10 →
      enclosingCell (c.1 + unitStep F.top c.2) ∈ cellBall S z 10 →
      ‖patchFrameForm S V z (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) c.1 c.2 -
        nestedAverage (BlockAverages.patchFrameForm S V z (toQuaternionForm u)) F.top c.1 c.2‖ ≤
      Cs * nestedAverage (fun x k => ‖toQuaternionForm u x k‖) F.top c.1 c.2 := by
    intro z hz c hc h1 h2
    have t := hTop F m S hodd hL3 hamb hm hreg s V hs0 hsc3 hcold z hz u F.top le_rfl c hc h1 h2
    simp only [Nat.sub_self, pow_zero, mul_one] at t
    exact t.trans (mul_le_mul_of_nonneg_right hle3
      (nestedAverage_top_nonneg hodd _ (fun _ _ => norm_nonneg _) c.1 c.2))
  obtain ⟨hA, hB⟩ := hKer F m S hodd hamb hm hreg
  refine ⟨fun φ θ del p hθ hdel hlip z₀ hz₀ => ?_, fun B hBd z hz => ?_⟩
  · have hN := hA φ θ del p hθ hdel hlip
    have hw0 : ∀ x, 0 ≤ classWeight F φ θ p 0 x := fun x => by
      have h1 : 0 < scaleRadius F 0 p x / (F.blockSide : ℝ) ^ F.top := by
        have a : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
          have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
          positivity
        have b : 0 < scaleRadius F 0 p x := by
          refine lt_min a (lt_max_of_lt_left ?_)
          have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
          positivity
        positivity
      exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg h1.le _)
    have hρ : ∀ x, 0 ≤ classWeight F φ θ p 0 x / scaleRadius F 0 p x := fun x => by
      have a : (0 : ℝ) < (F.blockSide : ℝ) ^ F.top := by
        have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
        positivity
      have b : 0 < scaleRadius F 0 p x := by
        refine lt_min a (lt_max_of_lt_left ?_)
        have : (0 : ℝ) < F.blockSide := by exact_mod_cast hL
        positivity
      exact div_nonneg (hw0 x) b.le
    obtain ⟨T, hTd⟩ : ∃ T : F.Cell → ℝ, T = fun z => cellTopNorm S (classWeight F φ θ p F.top)
      (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) z := ⟨_, rfl⟩
    have hT0 : ∀ y, 0 ≤ T y := fun y => by
      rw [hTd]
      exact Real.sqrt_nonneg _
    have hT : ∀ c ∈ innerBonds S F.top, Real.exp (φ c.1) *
        ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top c.1 c.2‖ ≤ T c.1 := by
      intro c hc
      rw [hTd]
      exact exp_mul_norm_le_cellTopNorm hL φ θ p _ hc
    have key := target_formAddGaugeDiff_le hset hK.le hN hFT u hT0 hT hTopN hz₀
    rw [← hcC] at key
    have e1 := cellBondNorm_le_formNormOn (S := S) (by norm_num : (1 : ℝ) ≤ 4) hw0 (formAddGaugeDiff S V u) z₀
    have e2 := cellBondNorm_le_formNormOn (S := S) (by norm_num : (1 : ℝ) ≤ 2) hρ (formAddGaugeDiff S V u) z₀
    have hLHS : cellBondNorm 4 S (classWeight F φ θ p 0) (formPlusGaugeDiff S V u) z₀ +
        cellBondNorm 2 S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x) (formPlusGaugeDiff S V u) z₀ ≤
        4 * (cC * localBound (weightedLpNormOnCell 4 S (classWeight F φ θ p 0))
          (weightedLpNormOnCell 2 S (classWeight F φ θ p 0)) Cs S V u T z₀) := by
      have : cellBondNorm 4 S (classWeight F φ θ p 0) (formPlusGaugeDiff S V u) z₀ +
          cellBondNorm 2 S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x) (formPlusGaugeDiff S V u) z₀ ≤
          4 * (weightedLpNormOnCell 4 S (classWeight F φ θ p 0) (formNormOn S (formAddGaugeDiff S V u)) z₀ +
            weightedLpNormOnCell 2 S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
              (formNormOn S (formAddGaugeDiff S V u)) z₀) := by
        have e3 : formPlusGaugeDiff S V u = formAddGaugeDiff S V u := rfl
        rw [e3]
        linarith
      exact this.trans (mul_le_mul_of_nonneg_left key (by norm_num))
    refine hLHS.trans ?_
    obtain ⟨Pp, hPp⟩ : ∃ Pp, Pp = ∑ z ∈ cellBall S z₀ 22,
      (cellPlaquetteNorm 2 S (classWeight F φ θ p 0) (linearizedCurl (referenceFieldChain S V 0) u) z +
        cellTopNorm S (classWeight F φ θ p F.top) (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) z) :=
      ⟨_, rfl⟩
    obtain ⟨Qq, hQq⟩ : ∃ Qq, Qq = ∑ z ∈ cellBall S z₀ 22,
      (cellBondNorm 4 S (classWeight F φ θ p 0) (fun x i => u x i) z +
        cellBondNorm 2 S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x) (fun x i => u x i) z) := ⟨_, rfl⟩
    have hPp0 : 0 ≤ Pp := by
      rw [hPp]
      exact Finset.sum_nonneg fun z _ => add_nonneg (cellPlaquetteNorm_nonneg _ hw0 _ z) (Real.sqrt_nonneg _)
    have hQq0 : 0 ≤ Qq := by
      rw [hQq]
      exact Finset.sum_nonneg fun z _ => add_nonneg (cellBondNorm_nonneg _ hw0 _ z) (cellBondNorm_nonneg _ hρ _ z)
    rw [← hPp, ← hQq]
    have hnb : localBound (weightedLpNormOnCell 4 S (classWeight F φ θ p 0))
        (weightedLpNormOnCell 2 S (classWeight F φ θ p 0)) Cs S V u T z₀ ≤ 16 * Pp + 4 * Cs * Qq := by
      rw [hPp, hQq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun x _ => ?_
      have a1 := curlNorm_le_cellPlaquetteNorm (S := S) (by norm_num : (1 : ℝ) ≤ 2) hw0 V u x
      have a2 : weightedLpNormOnCell 4 S (classWeight F φ θ p 0) (formNormOn S (toQuaternionForm u)) x ≤
          4 * cellBondNorm 4 S (classWeight F φ θ p 0) (fun x i => (u x i : ℍ[ℝ])) x :=
        formNormOn_le_cellBondNorm (S := S) (by norm_num : (1 : ℝ) ≤ 4) hw0 (toQuaternionForm u) x
      have a3 : T x = cellTopNorm S (classWeight F φ θ p F.top)
          (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) x := by
        rw [hTd]
      have a4 : 0 ≤ cellTopNorm S (classWeight F φ θ p F.top)
          (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) x :=
        Real.sqrt_nonneg _
      have a5 : 0 ≤ cellBondNorm 2 S (fun x => classWeight F φ θ p 0 x / scaleRadius F 0 p x)
          (fun x i => u x i) x :=
        cellBondNorm_nonneg _ hρ _ x
      have a6 := mul_le_mul_of_nonneg_left a2 hCs0
      have a8 := mul_nonneg (by positivity : 0 ≤ 4 * Cs) a5
      rw [a3]
      linarith
    have h1 := mul_le_mul_of_nonneg_left hnb (by positivity : 0 ≤ 4 * cC)
    have e4 : 4 * (cC * localBound (weightedLpNormOnCell 4 S (classWeight F φ θ p 0))
        (weightedLpNormOnCell 2 S (classWeight F φ θ p 0)) Cs S V u T z₀) =
        4 * cC * localBound (weightedLpNormOnCell 4 S (classWeight F φ θ p 0))
          (weightedLpNormOnCell 2 S (classWeight F φ θ p 0)) Cs S V u T z₀ := by ring
    rw [e4]
    refine h1.trans ?_
    have b1 : 4 * cC * 16 ≤ Cf := by
      rw [hCf]
      have : 0 ≤ 64 * cC * Cc + 4 * cC * (45 ^ 4 * (20 + 8 * (K + K ^ 2))) := by positivity
      nlinarith
    have b2 : 4 * cC * 4 * Cc ≤ Cf := by
      rw [hCf]
      have : 0 ≤ 64 * cC + 4 * cC * (45 ^ 4 * (20 + 8 * (K + K ^ 2))) := by positivity
      nlinarith
    have c1' := mul_le_mul_of_nonneg_right b1 hPp0
    have c2' := mul_le_mul_of_nonneg_right b2 (mul_nonneg hs0.le hQq0)
    have e5 : 4 * cC * (16 * Pp + 4 * Cs * Qq) = 4 * cC * 16 * Pp + 4 * cC * 4 * Cc * (s * Qq) := by
      rw [hCs]
      ring
    rw [e5]
    have e6 : Cf * s * Qq = Cf * (s * Qq) := by ring
    rw [e6]
    linarith
  · have hN := hB
    have hw1 : ∀ x : F.Site 0, (0 : ℝ) ≤ (fun _ => (1 : ℝ)) x := fun _ => zero_le_one
    have hzb := hBd z hz
    have hB0 : 0 ≤ B :=
      le_trans (add_nonneg (cellPlaquetteNorm_nonneg _ hw1 _ z) (cellBondNorm_nonneg _ hw1 _ z)) hzb
    have hK2 : 0 ≤ K + K ^ 2 := by positivity
    obtain ⟨T0, hT0d⟩ : ∃ T0, T0 = 8 * (K + K ^ 2) * B := ⟨_, rfl⟩
    have hT00 : 0 ≤ T0 := by rw [hT0d]; positivity
    have hbond : ∀ {x : F.Cell}, x ∈ S →
        weightedLpNormOnCell 3 S (fun _ => 1) (formNormOn S (toQuaternionForm u)) x ≤ 4 * B := by
      intro x hx
      have a1 := formNormOn_le_cellBondNorm (S := S) (by norm_num : (1 : ℝ) ≤ 3) hw1 (toQuaternionForm u) x
      have a2 := hBd x hx
      have a3 := cellPlaquetteNorm_nonneg (S := S) (12 / 7) hw1 (linearizedCurl (referenceFieldChain S V 0) u) x
      have a4 : toQuaternionForm u = fun x i => (u x i : ℍ[ℝ]) := rfl
      rw [a4] at a1 ⊢
      linarith
    have hT : ∀ c ∈ innerBonds S F.top, (fun _ : F.Cell => (cellSideLength F : ℝ) ^ ((1 : ℝ) / 3)) c.1 *
        ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top c.1 c.2‖ ≤ (fun _ : F.Cell => T0) c.1 := by
      intro c hc
      obtain ⟨y, i⟩ := c
      have hyS : y ∈ S := mem_sitesOfCells_top.1 (Finset.mem_product.1 (Finset.mem_filter.1 hc).1).1
      have hyS' : y + unitStep F.top i ∈ S := mem_sitesOfCells_top.1 (Finset.mem_filter.1 hc).2
      have hd1 : cellSupDist (y + unitStep F.top i) y ≤ 1 :=
        cellSupDist_add_le (r := 1) hamb y (a := basisVector i) (by norm_num)
        (fun k => by
        by_cases hk : k = i
        · subst hk
          simp [basisVector]
        · simp [basisVector, hk])
      have hd2 : cellSupDist y (y + unitStep F.top i) ≤ 1 := by rwa [cellSupDist_symm]
      have hy10 : enclosingCell y ∈ cellBall S y 10 := by
        rw [enclosingCell_self]
        exact Finset.mem_filter.2 ⟨hyS, by simp [cellSupDist]⟩
      have hy10' : enclosingCell (y + unitStep F.top i) ∈ cellBall S y 10 := by
        rw [enclosingCell_self]
        exact Finset.mem_filter.2 ⟨hyS', by omega⟩
      have t1 := hTopN y hyS (y, i) hc hy10 hy10'
      simp only [] at t1
      have t2 := norm_nestedAverage_patchFrameForm_le (S := S) (V := V) hodd y u y i
      have t3 : ‖patchFrameForm S V y (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) y i‖ =
          ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top y i‖ := PatchForms.norm_adjointAction_apply _ _
      have t4 := norm_sub_norm_le
        (patchFrameForm S V y (linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top) y i)
        (nestedAverage (BlockAverages.patchFrameForm S V y (toQuaternionForm u)) F.top y i)
      rw [t3] at t4
      obtain ⟨PU, hPU⟩ : ∃ PU, PU = nestedAverage (fun x k => ‖toQuaternionForm u x k‖) F.top y i := ⟨_, rfl⟩
      rw [← hPU] at t1 t2
      have hPU0 : 0 ≤ PU := hPU ▸ nestedAverage_top_nonneg hodd _ (fun _ _ => norm_nonneg _) y i
      have t5 : ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top y i‖ ≤ 2 * PU := by
        have := mul_le_of_le_one_left hPU0 hCs1
        linarith
      have t6 := scale_mul_nestedAverage_norm_le hset hN u hyS hyS' (by omega)
      rw [← hPU] at t6
      have hσ := (hN.scale_pos y).le
      have t7 := mul_le_mul_of_nonneg_left t5 hσ
      have a1 := mul_le_mul_of_nonneg_left (hbond hyS) hK.le
      have a2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hbond hyS') hK.le) hK.le
      show (cellSideLength F : ℝ) ^ ((1 : ℝ) / 3) *
        ‖linearPart (referenceFieldChain S V) (baseOnlyChart u) F.top y i‖ ≤ T0
      have e : T0 = 2 * (K * (4 * B) + K * (K * (4 * B))) := by
        rw [hT0d]
        ring
      rw [e]
      have hσe : (fun _ : F.Cell => (cellSideLength F : ℝ) ^ ((1 : ℝ) / 3)) y =
          (cellSideLength F : ℝ) ^ ((1 : ℝ) / 3) := rfl
      simp only [hσe] at t6 t7 hσ
      nlinarith
    have key := target_formAddGaugeDiff_le hset hK.le hN hFT u (T := fun _ => T0) (fun _ => hT00) hT hTopN hz
    rw [← hcC] at key
    have e1 := cellBondNorm_le_formNormOn (S := S) (by norm_num : (1 : ℝ) ≤ 3) hw1 (formAddGaugeDiff S V u) z
    have e3 : formPlusGaugeDiff S V u = formAddGaugeDiff S V u := rfl
    rw [e3]
    have hnb : localBound (weightedLpNormOnCell 3 S (fun _ => 1)) (weightedLpNormOnCell (12 / 7) S (fun _ => 1))
        Cs S V u (fun _ => T0) z ≤ 45 ^ 4 * ((20 + 8 * (K + K ^ 2)) * B) := by
      have := sum_cellBall_le hset z 22 (fun x => weightedLpNormOnCell (12 / 7) S (fun _ => 1) (curlNorm S V u) x +
        T0 + Cs * weightedLpNormOnCell 3 S (fun _ => 1) (formNormOn S (toQuaternionForm u)) x)
        (B := (20 + 8 * (K + K ^ 2)) * B)
        (by positivity) (fun x hx => by
          have hxS := (Finset.mem_filter.1 hx).1
          have a1 := curlNorm_le_cellPlaquetteNorm (S := S) (by norm_num : (1 : ℝ) ≤ 12 / 7) hw1 V u x
          have a2 := hBd x hxS
          have a3 := cellBondNorm_nonneg (S := S) 3 hw1 (fun x i => (u x i : ℍ[ℝ])) x
          have a4 := hbond hxS
          have a5 : Cs * weightedLpNormOnCell 3 S (fun _ => 1) (formNormOn S (toQuaternionForm u)) x ≤ 4 * B := by
            have b0 : 0 ≤ weightedLpNormOnCell 3 S (fun _ => 1) (formNormOn S (toQuaternionForm u)) x :=
              (weightedLpNormOnCell_isCellSeminorm (by norm_num : (1 : ℝ) ≤ 3) S (fun _ => 1)).nonneg _ _
            exact (mul_le_of_le_one_left b0 hCs1).trans a4
          have a6 : weightedLpNormOnCell (12 / 7) S (fun _ => 1) (curlNorm S V u) x ≤ 16 * B := by
            refine a1.trans ?_
            linarith
          rw [hT0d]
          nlinarith)
      norm_num at this ⊢
      exact this
    have h2 := mul_le_mul_of_nonneg_left hnb hcC0
    have b1 : 4 * (cC * (45 ^ 4 * ((20 + 8 * (K + K ^ 2)) * B))) ≤ Cf * B := by
      rw [hCf]
      have : 0 ≤ (64 * cC * (1 + Cc) + 1) * B := by positivity
      nlinarith
    linarith
end YangMills.Construction.GaugeCurlBound
end
