import YangMills.Construction.ColdChainAtEveryLevel.PointsOfAPatchForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
open Classical in
def cellSites (S : Finset F.Cell) (z : F.Cell) : Finset (F.Site 0) :=
  (sitesOfCells S 0).filter fun x => enclosingCell x = z
def weightedLpNormOnCell (q : ℝ) (S : Finset F.Cell) (w f : F.Site 0 → ℝ) (z : F.Cell) : ℝ :=
  (∑ x ∈ cellSites S z, |w x * f x| ^ q) ^ (1 / q)
open Classical in
def restrictToPatch (S : Finset F.Cell) (z : F.Cell) (f : F.Site 0 → ℝ) : F.Site 0 → ℝ :=
  fun s => if s ∈ PatchPoints.patchSiteSet S z then f s else 0
open Classical in
def patchCubicKernel (S : Finset F.Cell) (z : F.Cell) (f : F.Site 0 → ℝ) : F.Site 0 → ℝ :=
  fun s => if s ∈ PatchPoints.patchSiteSet S z then
    ∑ t ∈ PatchPoints.patchSiteSet S z,
      LatticeFractionalIntegration.cubicKernel (GaugeMap.patchChart S z s - GaugeMap.patchChart S z t) * f t
    else 0
structure IsCellSeminorm (S : Finset F.Cell) (M : (F.Site 0 → ℝ) → F.Cell → ℝ) : Prop where
  nonneg : ∀ f z, 0 ≤ M f z
  mono_abs : ∀ f g z, (∀ x ∈ cellSites S z, |f x| ≤ |g x|) → M f z ≤ M g z
  add_le : ∀ f g z, M (fun x => f x + g x) z ≤ M f z + M g z
  smul : ∀ (c : ℝ) f z, M (fun x => c * f x) z = |c| * M f z
theorem rpow_sum_le_sum_rpow_of_le_one {ι : Type} (t : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ t, 0 ≤ a i) {r : ℝ}
    (h0 : 0 < r) (h1 : r ≤ 1) : (∑ i ∈ t, a i) ^ r ≤ ∑ i ∈ t, a i ^ r := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Real.zero_rpow h0.ne']
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hai := ha i (Finset.mem_insert_self _ _)
    have hat : 0 ≤ ∑ j ∈ t, a j := Finset.sum_nonneg fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have h2 := Real.rpow_add_le_add_rpow hai hat h0.le h1
    have h3 := ih fun j hj => ha j (Finset.mem_insert_of_mem hj)
    linarith
theorem weightedLpNormOnCell_isCellSeminorm {q : ℝ} (hq : 1 ≤ q) (S : Finset F.Cell) (w : F.Site 0 → ℝ) :
    IsCellSeminorm S (weightedLpNormOnCell q S w) := by
  have hq0 : 0 < q := by linarith
  have hiq : 0 ≤ 1 / q := by positivity
  refine ⟨fun f z => ?_, fun f g z h => ?_, fun f g z => ?_, fun c f z => ?_⟩
  · exact Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
  · refine Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) ?_ hiq
    refine Finset.sum_le_sum fun x hx => Real.rpow_le_rpow (abs_nonneg _) ?_ hq0.le
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (h x hx) (abs_nonneg _)
  · simp only [weightedLpNormOnCell, mul_add]
    exact Real.Lp_add_le _ _ _ hq
  · simp only [weightedLpNormOnCell]
    have e : ∀ x, |w x * (c * f x)| ^ q = |c| ^ q * |w x * f x| ^ q := by
      intro x
      rw [show w x * (c * f x) = c * (w x * f x) by ring, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    simp only [e, ← Finset.mul_sum]
    rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _)
      (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _), ← Real.rpow_mul (abs_nonneg _)]
    rw [show q * (1 / q) = 1 by field_simp, Real.rpow_one]
theorem IsCellSeminorm.add {S : Finset F.Cell} {M M' : (F.Site 0 → ℝ) → F.Cell → ℝ} (h : IsCellSeminorm S M)
    (h' : IsCellSeminorm S M') : IsCellSeminorm S (fun f z => M f z + M' f z) := by
  refine ⟨fun f z => add_nonneg (h.nonneg f z) (h'.nonneg f z),
    fun f g z hfg => add_le_add (h.mono_abs f g z hfg) (h'.mono_abs f g z hfg),
    fun f g z => ?_, fun c f z => ?_⟩
  · have h1 := h.add_le f g z
    have h2 := h'.add_le f g z
    show M (fun x => f x + g x) z + M' (fun x => f x + g x) z ≤ M f z + M' f z + (M g z + M' g z)
    linarith
  · simp only [h.smul, h'.smul]
    ring
theorem IsCellSeminorm.sum_le {S : Finset F.Cell} {M : (F.Site 0 → ℝ) → F.Cell → ℝ} (h : IsCellSeminorm S M)
    {ι : Type} (t : Finset ι) (f : ι → F.Site 0 → ℝ) (z : F.Cell) :
    M (fun x => ∑ i ∈ t, f i x) z ≤ ∑ i ∈ t, M (f i) z := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have := h.smul 0 (fun _ => 0) z
    simp at this ⊢
    exact this.le
  | insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h.add_le _ _ z).trans (by linarith)
theorem lpNorm_le_card_rpow_mul_lpNorm {ι : Type} (t : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) {Q P : ℝ}
    (hQ : 0 < Q) (hQP : Q < P) :
    (∑ i ∈ t, a i ^ Q) ^ (1 / Q) ≤ (t.card : ℝ) ^ (1 / Q - 1 / P) * (∑ i ∈ t, a i ^ P) ^ (1 / P) := by
  have hP : 0 < P := hQ.trans hQP
  set p : ℝ := P / Q with hp
  have hp1 : 1 < p := by rw [hp, lt_div_iff₀ hQ]; linarith
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp1
  have h1 := Real.inner_le_Lp_mul_Lq t (fun i => a i ^ Q) (fun _ => (1 : ℝ)) hpq
  simp only [mul_one, abs_one, Real.one_rpow, Finset.sum_const, nsmul_eq_mul] at h1
  have e1 : ∀ i, |a i ^ Q| ^ p = a i ^ P := by
    intro i
    rw [abs_of_nonneg (Real.rpow_nonneg (ha i) _), ← Real.rpow_mul (ha i)]
    congr 1
    rw [hp]
    field_simp
  simp only [e1] at h1
  have hS : 0 ≤ ∑ i ∈ t, a i ^ P := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (ha i) _
  have hS0 : 0 ≤ ∑ i ∈ t, a i ^ Q := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (ha i) _
  have hn : (0 : ℝ) ≤ t.card := by positivity
  have hiQ : 0 ≤ 1 / Q := by positivity
  have h2 := Real.rpow_le_rpow hS0 (by simpa using h1) hiQ
  refine h2.trans (le_of_eq ?_)
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hS, ← Real.rpow_mul hn, mul_comm]
  have e2 : p⁻¹ * (1 / Q) = 1 / P := by rw [hp]; field_simp
  have e3 : (p - 1) / p * (1 / Q) = 1 / Q - 1 / P := by
    rw [hp]
    field_simp
  rw [e2, e3]
end YangMills.Construction.BlockAverages
end
