import YangMills.Construction.ColdChainAtEveryLevel.TheGaugeMapAsALinearMap
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace NearCellNorms
section FiniteLp
variable {ι : Type} (A : Finset ι)
def finLpNorm (p : ℝ) (f : ι → ℝ) : ℝ := (∑ i ∈ A, f i ^ p) ^ (1 / p)
theorem finLpNorm_nonneg (p : ℝ) {f : ι → ℝ} (hf : ∀ i ∈ A, 0 ≤ f i) : 0 ≤ finLpNorm A p f :=
  Real.rpow_nonneg (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hf i hi) _) _
theorem finLpNorm_mul_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : 1 / c = 1 / a + 1 / b)
    {f g : ι → ℝ} (hf : ∀ i ∈ A, 0 ≤ f i) (hg : ∀ i ∈ A, 0 ≤ g i) :
    finLpNorm A c (fun i => f i * g i) ≤ finLpNorm A a f * finLpNorm A b g := by
  have hsum : 1 / (a / c) + 1 / (b / c) = 1 := by
    field_simp
    field_simp at habc
    linarith
  have hconj : (a / c).HolderConjugate (b / c) := by
    refine Real.holderConjugate_iff.2 ⟨?_, ?_⟩
    · have h1 : 0 < 1 / (b / c) := by positivity
      have h2 : 1 / (a / c) < 1 := by linarith
      have hac : 0 < a / c := by positivity
      rw [div_lt_one hac] at h2
      exact h2
    · simpa [one_div] using hsum
  have hH := Real.inner_le_Lp_mul_Lq A (fun i => f i ^ c) (fun i => g i ^ c) hconj
  have hfc : ∀ i ∈ A, |f i ^ c| ^ (a / c) = f i ^ a := fun i hi => by
    rw [abs_of_nonneg (Real.rpow_nonneg (hf i hi) _), ← Real.rpow_mul (hf i hi)]
    congr 1
    field_simp
  have hgc : ∀ i ∈ A, |g i ^ c| ^ (b / c) = g i ^ b := fun i hi => by
    rw [abs_of_nonneg (Real.rpow_nonneg (hg i hi) _), ← Real.rpow_mul (hg i hi)]
    congr 1
    field_simp
  rw [Finset.sum_congr rfl hfc, Finset.sum_congr rfl hgc] at hH
  have e1 : ∑ i ∈ A, (f i * g i) ^ c = ∑ i ∈ A, f i ^ c * g i ^ c :=
    Finset.sum_congr rfl fun i hi => Real.mul_rpow (hf i hi) (hg i hi)
  have hX : 0 ≤ ∑ i ∈ A, f i ^ a := Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hf i hi) _
  have hY : 0 ≤ ∑ i ∈ A, g i ^ b := Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hg i hi) _
  unfold finLpNorm
  calc (∑ i ∈ A, (f i * g i) ^ c) ^ (1 / c)
      ≤ ((∑ i ∈ A, f i ^ a) ^ (1 / (a / c)) * (∑ i ∈ A, g i ^ b) ^ (1 / (b / c))) ^ (1 / c) := by
        refine Real.rpow_le_rpow (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (mul_nonneg (hf i hi) (hg i hi)) _)
          ?_ (by positivity)
        rw [e1]
        exact hH
    _ = (∑ i ∈ A, f i ^ a) ^ (1 / a) * (∑ i ∈ A, g i ^ b) ^ (1 / b) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hX _) (Real.rpow_nonneg hY _), ← Real.rpow_mul hX, ← Real.rpow_mul hY]
        congr 2 <;> field_simp
theorem finLpNorm_add_le {p : ℝ} (hp : 1 ≤ p) {f g : ι → ℝ} (hf : ∀ i ∈ A, 0 ≤ f i) (hg : ∀ i ∈ A, 0 ≤ g i) :
    finLpNorm A p (fun i => f i + g i) ≤ finLpNorm A p f + finLpNorm A p g := by
  have h := Real.Lp_add_le A f g hp
  have e1 : ∀ i ∈ A, |f i + g i| ^ p = (f i + g i) ^ p := fun i hi => by
    rw [abs_of_nonneg (add_nonneg (hf i hi) (hg i hi))]
  have e2 : ∀ i ∈ A, |f i| ^ p = f i ^ p := fun i hi => by rw [abs_of_nonneg (hf i hi)]
  have e3 : ∀ i ∈ A, |g i| ^ p = g i ^ p := fun i hi => by rw [abs_of_nonneg (hg i hi)]
  rwa [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at h
theorem finLpNorm_mono {p : ℝ} (hp : 0 < p) {f g : ι → ℝ} (hf : ∀ i ∈ A, 0 ≤ f i) (hfg : ∀ i ∈ A, f i ≤ g i) :
    finLpNorm A p f ≤ finLpNorm A p g := by
  refine Real.rpow_le_rpow (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hf i hi) _) ?_ (by positivity)
  exact Finset.sum_le_sum fun i hi => Real.rpow_le_rpow (hf i hi) (hfg i hi) hp.le
theorem finLpNorm_const_mul {p : ℝ} (hp : 0 < p) {c : ℝ} (hc : 0 ≤ c) {f : ι → ℝ} (hf : ∀ i ∈ A, 0 ≤ f i) :
    finLpNorm A p (fun i => c * f i) = c * finLpNorm A p f := by
  unfold finLpNorm
  have e : ∀ i ∈ A, (c * f i) ^ p = c ^ p * f i ^ p := fun i hi => Real.mul_rpow hc (hf i hi)
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg hc _)
    (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hf i hi) _), ← Real.rpow_mul hc]
  congr 1
  rw [mul_one_div_cancel hp.ne', Real.rpow_one]
theorem sum_rpow_eq_finLpNorm_rpow {p : ℝ} (hp : 0 < p) {f : ι → ℝ} (hf : ∀ i ∈ A, 0 ≤ f i) :
    ∑ i ∈ A, f i ^ p = finLpNorm A p f ^ p := by
  unfold finLpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hf i hi) _), one_div_mul_cancel hp.ne',
    Real.rpow_one]
theorem finLpNorm_le_of_sum_rpow_le {p B : ℝ} (hp : 0 < p) {f : ι → ℝ} (hf : ∀ i ∈ A, 0 ≤ f i) (hB : 0 ≤ B)
    (h : ∑ i ∈ A, f i ^ p ≤ B ^ p) : finLpNorm A p f ≤ B := by
  unfold finLpNorm
  have h1 := Real.rpow_le_rpow (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hf i hi) _) h
    (by positivity : 0 ≤ 1 / p)
  rwa [← Real.rpow_mul hB, mul_one_div_cancel hp.ne', Real.rpow_one] at h1
theorem finLpNorm_const {p : ℝ} (hp : 0 < p) (c : ℝ) (hc : 0 ≤ c) :
    finLpNorm A p (fun _ => c) = c * (A.card : ℝ) ^ (1 / p) := by
  unfold finLpNorm
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm, Real.mul_rpow (Real.rpow_nonneg hc _) (by positivity),
    ← Real.rpow_mul hc, mul_one_div_cancel hp.ne', Real.rpow_one]
end FiniteLp
section NeighbourCells
open BlockAverages LatticeFractionalIntegration
variable {F : BlockFrame}
theorem blockIndex_intCast_congr (hL : 0 < F.blockSide) (k : Fin 4) {t t' : ℤ}
    (h : ((t : ℤ) : ZMod (F.period 0 k)) = ((t' : ℤ) : ZMod (F.period 0 k))) :
    (((t + ((F.blockSide : ℤ) ^ (F.top - 0) - 1) / 2) / (F.blockSide : ℤ) ^ (F.top - 0) : ℤ) : ZMod (F.period F.top k)) =
      (((t' + ((F.blockSide : ℤ) ^ (F.top - 0) - 1) / 2) / (F.blockSide : ℤ) ^ (F.top - 0) : ℤ) :
        ZMod (F.period F.top k)) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h ⊢
  obtain ⟨m, hm⟩ := h
  set N : ℤ := (F.blockSide : ℤ) ^ (F.top - 0) with hN
  have hNpos : 0 < N := by
    have : (0 : ℤ) < (F.blockSide : ℤ) := by exact_mod_cast hL
    positivity
  have hper0 : ((F.period 0 k : ℕ) : ℤ) = (F.extent k : ℤ) * N := by
    simp [BlockFrame.period, hN]
  have hpertop : ((F.period F.top k : ℕ) : ℤ) = (F.extent k : ℤ) := by
    simp [BlockFrame.period]
  rw [hper0] at hm
  rw [hpertop]
  have e1 : t' + (N - 1) / 2 = (t + (N - 1) / 2) + N * ((F.extent k : ℤ) * m) := by
    linear_combination hm
  rw [e1, Int.add_mul_ediv_left _ _ hNpos.ne']
  refine ⟨m, ?_⟩
  ring
theorem enclosingCell_add_unitStep (hL : 0 < F.blockSide) (x : F.Site 0) (i : Fin 4) :
    enclosingCell (x + unitStep 0 i) = enclosingCell x ∨
      enclosingCell (x + unitStep 0 i) = enclosingCell x + unitStep F.top i := by
  set N : ℤ := (F.blockSide : ℤ) ^ (F.top - 0) with hN
  have hNpos : 0 < N := by
    have : (0 : ℤ) < (F.blockSide : ℤ) := by exact_mod_cast hL
    positivity
  have hcast : ∀ k, ((siteCoords (x + unitStep 0 i) k : ℤ) : ZMod (F.period 0 k)) =
      ((siteCoords x k + (basisVector i) k : ℤ) : ZMod (F.period 0 k)) := fun k => by
    rw [unitStep_eq]
    exact siteCoords_add_cast x (basisVector i) k
  have hstep : ∀ k, (((siteCoords (x + unitStep 0 i) k + (N - 1) / 2) / N : ℤ) : ZMod (F.period F.top k)) =
      (((siteCoords x k + (basisVector i) k + (N - 1) / 2) / N : ℤ) : ZMod (F.period F.top k)) := fun k =>
    blockIndex_intCast_congr hL k (hcast k)
  have hne : ∀ k, k ≠ i → (basisVector i) k = 0 := fun k hk => by simp [basisVector, hk]
  have hi : (basisVector i) i = 1 := by simp [basisVector]
  set a := siteCoords x i + (N - 1) / 2 with ha
  have hdiv := Int.mul_ediv_add_emod a N
  have hr0 := Int.emod_nonneg a hNpos.ne'
  have hr1 := Int.emod_lt_of_pos a hNpos
  by_cases hcase : a % N + 1 < N
  · left
    funext k
    show (((siteCoords (x + unitStep 0 i) k + (N - 1) / 2) / N : ℤ) : ZMod (F.period F.top k)) =
      (((siteCoords x k + (N - 1) / 2) / N : ℤ) : ZMod (F.period F.top k))
    rw [hstep]
    by_cases hk : k = i
    · subst hk
      rw [hi]
      have e1 : siteCoords x k + 1 + (N - 1) / 2 = (a % N + 1) + N * (a / N) := by
        rw [show siteCoords x k + 1 + (N - 1) / 2 = a + 1 by rw [ha]; ring]
        linarith
      have e2 : (a % N + 1) / N = 0 := Int.ediv_eq_zero_of_lt (by omega) hcase
      rw [e1, Int.add_mul_ediv_left _ _ hNpos.ne', e2, zero_add]
    · rw [hne k hk, add_zero]
  · right
    funext k
    show (((siteCoords (x + unitStep 0 i) k + (N - 1) / 2) / N : ℤ) : ZMod (F.period F.top k)) =
      (((siteCoords x k + (N - 1) / 2) / N : ℤ) : ZMod (F.period F.top k)) +
        ((Pi.single i 1 : Lattice4) k : ZMod (F.period F.top k))
    rw [hstep]
    by_cases hk : k = i
    · subst hk
      rw [hi]
      have e1 : siteCoords x k + 1 + (N - 1) / 2 = N * (a / N + 1) := by
        rw [show siteCoords x k + 1 + (N - 1) / 2 = a + 1 by rw [ha]; ring]
        linarith
      rw [e1, Int.mul_ediv_cancel_left _ hNpos.ne']
      simp [ha]
    · rw [hne k hk, add_zero]
      simp [hk]
theorem sum_comp_le_of_injOn {α β : Type} {A : Finset α} {B : Finset β} {T : α → β} {g : β → ℝ}
    (hinj : Set.InjOn T A) (hmap : ∀ a ∈ A, T a ∈ B) (hg : ∀ b ∈ B, 0 ≤ g b) :
    ∑ a ∈ A, g (T a) ≤ ∑ b ∈ B, g b := by
  classical
  rw [← Finset.sum_image hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.2 hmap) fun b hb _ => hg b hb
theorem sum_union_le_add {β : Type} [DecidableEq β] {B B' : Finset β} {g : β → ℝ}
    (hg : ∀ b ∈ B ∪ B', 0 ≤ g b) :
    ∑ b ∈ B ∪ B', g b ≤ ∑ b ∈ B, g b + ∑ b ∈ B', g b := by
  have h := Finset.sum_union_inter (s₁ := B) (s₂ := B') (f := g)
  have h2 : 0 ≤ ∑ b ∈ B ∩ B', g b := Finset.sum_nonneg fun b hb =>
    hg b (Finset.mem_union_left _ (Finset.mem_of_mem_inter_left hb))
  linarith
variable {S : Finset F.Cell}
open Classical in
def sitesInCell (S : Finset F.Cell) (z : F.Cell) : Finset (F.Site 0) :=
  (sitesOfCells S 0).filter fun x => enclosingCell x = z
theorem mem_bondsOver_singleton (z : F.Cell) :
    ∀ b ∈ bondsOver S {z} 0, b ∈ innerBonds S 0 ∧ enclosingCell b.1 = z := by
  intro b hb
  simp only [bondsOver, Finset.mem_filter, Finset.mem_singleton] at hb
  exact hb
theorem mem_bondsOver_singleton_of {z : F.Cell} {b : F.Site 0 × Fin 4} (h1 : b ∈ innerBonds S 0)
    (h2 : enclosingCell b.1 = z) : b ∈ bondsOver S {z} 0 := by
  simp only [bondsOver, Finset.mem_filter, Finset.mem_singleton]
  exact ⟨h1, h2⟩
theorem mem_plaquettesOver_singleton (z : F.Cell) :
    ∀ p ∈ plaquettesOver S {z} 0, p ∈ innerPlaquettes S 0 ∧ enclosingCell p.1 = z := by
  intro p hp
  simp only [plaquettesOver, Finset.mem_filter, Finset.mem_singleton] at hp
  exact hp
theorem sum_sitesInCell_le (hodd : Odd F.blockSide) {f : F.Site 0 → ℝ} {Y : ℝ} (hY0 : 0 ≤ Y)
    (hY : ∀ z ∈ S, ∑ x ∈ sitesInCell S z, f x ≤ Y) (z : F.Cell) : ∑ x ∈ sitesInCell S z, f x ≤ Y := by
  classical
  by_cases hz : z ∈ S
  · exact hY z hz
  · have : sitesInCell S z = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun x hx hxz => hz ?_
      rw [← hxz]
      exact GaugeMapLinear.enclosingCell_mem S hodd x hx
    rw [this]
    simpa using hY0
theorem sum_bondsOver_le (hodd : Odd F.blockSide) {g : F.Site 0 × Fin 4 → ℝ} {Y : ℝ} (hY0 : 0 ≤ Y)
    (hY : ∀ z ∈ S, ∑ b ∈ bondsOver S {z} 0, g b ≤ Y) (z : F.Cell) :
    ∑ b ∈ bondsOver S {z} 0, g b ≤ Y := by
  classical
  by_cases hz : z ∈ S
  · exact hY z hz
  · have : bondsOver S {z} 0 = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun b hb => hz ?_
      obtain ⟨h1, h2⟩ := mem_bondsOver_singleton z b hb
      rw [← h2]
      exact GaugeMapLinear.enclosingCell_mem S hodd _ (ChartCoordinates.innerBonds_ends h1).1
    rw [this]
    simpa using hY0
theorem sum_bondsOver_tail_le (hodd : Odd F.blockSide) {f : F.Site 0 → ℝ} {Y : ℝ} (hf : ∀ x, 0 ≤ f x)
    (hY0 : 0 ≤ Y) (hY : ∀ z ∈ S, ∑ x ∈ sitesInCell S z, f x ≤ Y) (z : F.Cell) :
    ∑ b ∈ bondsOver S {z} 0, f b.1 ≤ 4 * Y := by
  classical
  rw [← Finset.sum_fiberwise (s := bondsOver S {z} 0) (g := fun b => b.2)]
  have hi : ∀ i : Fin 4, ∑ b ∈ (bondsOver S {z} 0).filter (fun b => b.2 = i), f b.1 ≤ Y := by
    intro i
    refine le_trans (sum_comp_le_of_injOn (T := fun b : F.Site 0 × Fin 4 => b.1) ?_ ?_ fun b _ => hf b)
      (sum_sitesInCell_le hodd hY0 hY z)
    · intro b hb b' hb' h
      have e1 := (Finset.mem_filter.1 hb).2
      have e2 := (Finset.mem_filter.1 hb').2
      exact Prod.ext h (e1.trans e2.symm)
    · intro b hb
      obtain ⟨h1, h2⟩ := mem_bondsOver_singleton z b (Finset.mem_filter.1 hb).1
      exact Finset.mem_filter.2 ⟨(ChartCoordinates.innerBonds_ends h1).1, h2⟩
  calc _ ≤ ∑ _i : Fin 4, Y := Finset.sum_le_sum fun i _ => hi i
    _ = 4 * Y := by simp
theorem add_unitStep_mem_sitesInCell_union (hodd : Odd F.blockSide) {x : F.Site 0} {i : Fin 4} {z : F.Cell}
    (hz : enclosingCell x = z) (hx : x + unitStep 0 i ∈ sitesOfCells S 0) [DecidableEq (F.Site 0)] :
    x + unitStep 0 i ∈ sitesInCell S z ∪ sitesInCell S (z + unitStep F.top i) := by
  classical
  rcases enclosingCell_add_unitStep hodd.pos x i with h | h
  · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hx, by rw [h, hz]⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hx, by rw [h, hz]⟩)
theorem sum_sitesInCell_union_le (hodd : Odd F.blockSide) {f : F.Site 0 → ℝ} {Y : ℝ} (hf : ∀ x, 0 ≤ f x)
    (hY0 : 0 ≤ Y) (hY : ∀ z ∈ S, ∑ x ∈ sitesInCell S z, f x ≤ Y) (z z' : F.Cell) [DecidableEq (F.Site 0)] :
    ∑ x ∈ sitesInCell S z ∪ sitesInCell S z', f x ≤ 2 * Y := by
  have h1 := sum_sitesInCell_le hodd hY0 hY z
  have h2 := sum_sitesInCell_le hodd hY0 hY z'
  have := sum_union_le_add (B := sitesInCell S z) (B' := sitesInCell S z') (g := f) fun b _ => hf b
  linarith
theorem sum_bondsOver_head_le (hodd : Odd F.blockSide) {f : F.Site 0 → ℝ} {Y : ℝ} (hf : ∀ x, 0 ≤ f x)
    (hY0 : 0 ≤ Y) (hY : ∀ z ∈ S, ∑ x ∈ sitesInCell S z, f x ≤ Y) (z : F.Cell) :
    ∑ b ∈ bondsOver S {z} 0, f (b.1 + unitStep 0 b.2) ≤ 8 * Y := by
  classical
  rw [← Finset.sum_fiberwise (s := bondsOver S {z} 0) (g := fun b => b.2)]
  have hi : ∀ i : Fin 4,
      ∑ b ∈ (bondsOver S {z} 0).filter (fun b => b.2 = i), f (b.1 + unitStep 0 b.2) ≤ 2 * Y := by
    intro i
    have e : ∑ b ∈ (bondsOver S {z} 0).filter (fun b => b.2 = i), f (b.1 + unitStep 0 b.2) =
        ∑ b ∈ (bondsOver S {z} 0).filter (fun b => b.2 = i), f (b.1 + unitStep 0 i) :=
      Finset.sum_congr rfl fun b hb => by rw [(Finset.mem_filter.1 hb).2]
    rw [e]
    refine le_trans
      (sum_comp_le_of_injOn (T := fun b : F.Site 0 × Fin 4 => b.1 + unitStep 0 i) ?_ ?_ fun b _ => hf b)
      (sum_sitesInCell_union_le hodd hf hY0 hY z (z + unitStep F.top i))
    · intro b hb b' hb' h
      have e1 := (Finset.mem_filter.1 hb).2
      have e2 := (Finset.mem_filter.1 hb').2
      exact Prod.ext (add_right_cancel h) (e1.trans e2.symm)
    · intro b hb
      obtain ⟨h1, h2⟩ := mem_bondsOver_singleton z b (Finset.mem_filter.1 hb).1
      have e1 := (Finset.mem_filter.1 hb).2
      have h3 := (ChartCoordinates.innerBonds_ends h1).2
      rw [e1] at h3
      exact add_unitStep_mem_sitesInCell_union hodd h2 h3
  calc _ ≤ ∑ _i : Fin 4, 2 * Y := Finset.sum_le_sum fun i _ => hi i
    _ = 8 * Y := by simp; ring
theorem sum_le_of_fiber_le {G : F.Site 0 × Fin 4 × Fin 4 → ℝ} {Y : ℝ} (P : Finset (F.Site 0 × Fin 4 × Fin 4))
    (h : ∀ q : Fin 4 × Fin 4, ∑ p ∈ P.filter (fun p => p.2 = q), G p ≤ Y) : ∑ p ∈ P, G p ≤ 16 * Y := by
  classical
  rw [← Finset.sum_fiberwise (s := P) (g := fun p => p.2)]
  calc _ ≤ ∑ _q : Fin 4 × Fin 4, Y := Finset.sum_le_sum fun q _ => h q
    _ = 16 * Y := by simp
theorem injOn_fiber {β : Type} (T : F.Site 0 → β) (hT : Function.Injective T)
    (P : Finset (F.Site 0 × Fin 4 × Fin 4)) (q : Fin 4 × Fin 4) :
    Set.InjOn (fun p : F.Site 0 × Fin 4 × Fin 4 => T p.1) (P.filter fun p => p.2 = q) := by
  classical
  intro p hp p' hp' h
  have e1 := (Finset.mem_filter.1 hp).2
  have e2 := (Finset.mem_filter.1 hp').2
  exact Prod.ext (hT h) (e1.trans e2.symm)
theorem corners_mem_sitesOfCells {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S 0) :
    p.1 ∈ sitesOfCells S 0 ∧ p.1 + unitStep 0 p.2.1 ∈ sitesOfCells S 0 ∧
      p.1 + unitStep 0 p.2.2 ∈ sitesOfCells S 0 ∧
      p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 ∈ sitesOfCells S 0 := by
  have hc := (Finset.mem_filter.1 hp).2.2
  exact ⟨hc (by simp [plaquetteCorners]), hc (by simp [plaquetteCorners]), hc (by simp [plaquetteCorners]),
    hc (by simp [plaquetteCorners])⟩
theorem sum_plaquettesOver_corner_le (hodd : Odd F.blockSide) {f : F.Site 0 → ℝ} {Y : ℝ} (hf : ∀ x, 0 ≤ f x)
    (hY0 : 0 ≤ Y) (hY : ∀ z ∈ S, ∑ x ∈ sitesInCell S z, f x ≤ Y) (z : F.Cell) :
    ∑ p ∈ plaquettesOver S {z} 0, f p.1 ≤ 64 * Y ∧
    ∑ p ∈ plaquettesOver S {z} 0, f (p.1 + unitStep 0 p.2.1) ≤ 64 * Y ∧
    ∑ p ∈ plaquettesOver S {z} 0, f (p.1 + unitStep 0 p.2.2) ≤ 64 * Y ∧
    ∑ p ∈ plaquettesOver S {z} 0, f (p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2) ≤ 64 * Y := by
  classical
  set P := plaquettesOver S {z} 0 with hP
  have fact : ∀ q p, p ∈ P.filter (fun p => p.2 = q) →
      p ∈ innerPlaquettes S 0 ∧ enclosingCell p.1 = z ∧ p.2 = q := by
    intro q p hp
    have h1 := Finset.mem_filter.1 hp
    exact ⟨(mem_plaquettesOver_singleton z p h1.1).1, (mem_plaquettesOver_singleton z p h1.1).2, h1.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : ∑ p ∈ P, f p.1 ≤ 16 * Y := by
      refine sum_le_of_fiber_le P fun q => ?_
      refine le_trans (sum_comp_le_of_injOn (T := fun p : F.Site 0 × Fin 4 × Fin 4 => p.1)
        (injOn_fiber id Function.injective_id P q) ?_ fun b _ => hf b) (sum_sitesInCell_le hodd hY0 hY z)
      intro p hp
      obtain ⟨h1, h2, _⟩ := fact q p hp
      exact Finset.mem_filter.2 ⟨(corners_mem_sitesOfCells h1).1, h2⟩
    linarith
  · have : ∑ p ∈ P, f (p.1 + unitStep 0 p.2.1) ≤ 16 * (2 * Y) := by
      refine sum_le_of_fiber_le P fun q => ?_
      have e : ∑ p ∈ P.filter (fun p => p.2 = q), f (p.1 + unitStep 0 p.2.1) =
          ∑ p ∈ P.filter (fun p => p.2 = q), f (p.1 + unitStep 0 q.1) :=
        Finset.sum_congr rfl fun p hp => by rw [(fact q p hp).2.2]
      rw [e]
      refine le_trans (sum_comp_le_of_injOn (T := fun p : F.Site 0 × Fin 4 × Fin 4 => p.1 + unitStep 0 q.1)
        (injOn_fiber (fun x => x + unitStep 0 q.1) (add_left_injective _) P q) ?_ fun b _ => hf b)
        (sum_sitesInCell_union_le hodd hf hY0 hY z (z + unitStep F.top q.1))
      intro p hp
      obtain ⟨h1, h2, h3⟩ := fact q p hp
      have h4 := (corners_mem_sitesOfCells h1).2.1
      rw [h3] at h4
      exact add_unitStep_mem_sitesInCell_union hodd h2 h4
    linarith
  · have : ∑ p ∈ P, f (p.1 + unitStep 0 p.2.2) ≤ 16 * (2 * Y) := by
      refine sum_le_of_fiber_le P fun q => ?_
      have e : ∑ p ∈ P.filter (fun p => p.2 = q), f (p.1 + unitStep 0 p.2.2) =
          ∑ p ∈ P.filter (fun p => p.2 = q), f (p.1 + unitStep 0 q.2) :=
        Finset.sum_congr rfl fun p hp => by rw [(fact q p hp).2.2]
      rw [e]
      refine le_trans (sum_comp_le_of_injOn (T := fun p : F.Site 0 × Fin 4 × Fin 4 => p.1 + unitStep 0 q.2)
        (injOn_fiber (fun x => x + unitStep 0 q.2) (add_left_injective _) P q) ?_ fun b _ => hf b)
        (sum_sitesInCell_union_le hodd hf hY0 hY z (z + unitStep F.top q.2))
      intro p hp
      obtain ⟨h1, h2, h3⟩ := fact q p hp
      have h4 := (corners_mem_sitesOfCells h1).2.2.1
      rw [h3] at h4
      exact add_unitStep_mem_sitesInCell_union hodd h2 h4
    linarith
  · have : ∑ p ∈ P, f (p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2) ≤ 16 * (2 * Y + 2 * Y) := by
      refine sum_le_of_fiber_le P fun q => ?_
      have e : ∑ p ∈ P.filter (fun p => p.2 = q), f (p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2) =
          ∑ p ∈ P.filter (fun p => p.2 = q), f (p.1 + unitStep 0 q.1 + unitStep 0 q.2) :=
        Finset.sum_congr rfl fun p hp => by rw [(fact q p hp).2.2]
      rw [e]
      set C1 := sitesInCell S z ∪ sitesInCell S (z + unitStep F.top q.2)
      set C2 := sitesInCell S (z + unitStep F.top q.1) ∪
        sitesInCell S (z + unitStep F.top q.1 + unitStep F.top q.2)
      have hC : ∑ x ∈ C1 ∪ C2, f x ≤ 2 * Y + 2 * Y := by
        have h1 := sum_sitesInCell_union_le hodd hf hY0 hY z (z + unitStep F.top q.2)
        have h2 := sum_sitesInCell_union_le hodd hf hY0 hY (z + unitStep F.top q.1)
          (z + unitStep F.top q.1 + unitStep F.top q.2)
        have h3 := sum_union_le_add (B := C1) (B' := C2) (g := f) fun b _ => hf b
        linarith
      refine le_trans (sum_comp_le_of_injOn
        (T := fun p : F.Site 0 × Fin 4 × Fin 4 => p.1 + unitStep 0 q.1 + unitStep 0 q.2)
        (injOn_fiber (fun x => x + unitStep 0 q.1 + unitStep 0 q.2)
          (fun a b h => add_right_cancel (add_right_cancel h)) P q) ?_ fun b _ => hf b) hC
      intro p hp
      obtain ⟨h1, h2, h3⟩ := fact q p hp
      have h4 := (corners_mem_sitesOfCells h1).2.2.2
      rw [h3] at h4
      rcases enclosingCell_add_unitStep hodd.pos p.1 q.1 with c | c
      · exact Finset.mem_union_left _ (add_unitStep_mem_sitesInCell_union hodd (by rw [c, h2]) h4)
      · exact Finset.mem_union_right _ (add_unitStep_mem_sitesInCell_union hodd (by rw [c, h2]) h4)
    linarith
theorem sum_bondsOver_union_le (hodd : Odd F.blockSide) {g : F.Site 0 × Fin 4 → ℝ} {Y : ℝ} (hg : ∀ b, 0 ≤ g b)
    (hY0 : 0 ≤ Y) (hY : ∀ z ∈ S, ∑ b ∈ bondsOver S {z} 0, g b ≤ Y) (z z' : F.Cell)
    [DecidableEq (F.Site 0 × Fin 4)] :
    ∑ b ∈ bondsOver S {z} 0 ∪ bondsOver S {z'} 0, g b ≤ 2 * Y := by
  have h1 := sum_bondsOver_le hodd hY0 hY z
  have h2 := sum_bondsOver_le hodd hY0 hY z'
  have := sum_union_le_add (B := bondsOver S {z} 0) (B' := bondsOver S {z'} 0) (g := g) fun b _ => hg b
  linarith
theorem sum_plaquettesOver_bond_le (hodd : Odd F.blockSide) {g : F.Site 0 × Fin 4 → ℝ} {Y : ℝ}
    (hg : ∀ b, 0 ≤ g b) (hY0 : 0 ≤ Y) (hY : ∀ z ∈ S, ∑ b ∈ bondsOver S {z} 0, g b ≤ Y) (z : F.Cell) :
    ∑ p ∈ plaquettesOver S {z} 0, g (p.1, p.2.1) ≤ 32 * Y ∧
    ∑ p ∈ plaquettesOver S {z} 0, g (p.1 + unitStep 0 p.2.1, p.2.2) ≤ 32 * Y ∧
    ∑ p ∈ plaquettesOver S {z} 0, g (p.1 + unitStep 0 p.2.2, p.2.1) ≤ 32 * Y ∧
    ∑ p ∈ plaquettesOver S {z} 0, g (p.1, p.2.2) ≤ 32 * Y := by
  classical
  set P := plaquettesOver S {z} 0 with hP
  have fact : ∀ q p, p ∈ P.filter (fun p => p.2 = q) →
      p ∈ innerPlaquettes S 0 ∧ enclosingCell p.1 = z ∧ p.2 = q := by
    intro q p hp
    have h1 := Finset.mem_filter.1 hp
    exact ⟨(mem_plaquettesOver_singleton z p h1.1).1, (mem_plaquettesOver_singleton z p h1.1).2, h1.2⟩
  have same : ∀ sel : Fin 4 × Fin 4 → Fin 4,
      (∀ p ∈ innerPlaquettes S 0, p.1 + unitStep 0 (sel p.2) ∈ sitesOfCells S 0) →
      ∑ p ∈ P, g (p.1, sel p.2) ≤ 32 * Y := by
    intro sel hsel
    have : ∑ p ∈ P, g (p.1, sel p.2) ≤ 16 * Y := by
      refine sum_le_of_fiber_le P fun q => ?_
      have e : ∑ p ∈ P.filter (fun p => p.2 = q), g (p.1, sel p.2) =
          ∑ p ∈ P.filter (fun p => p.2 = q), g (p.1, sel q) :=
        Finset.sum_congr rfl fun p hp => by rw [(fact q p hp).2.2]
      rw [e]
      refine le_trans (sum_comp_le_of_injOn (T := fun p : F.Site 0 × Fin 4 × Fin 4 => (p.1, sel q))
        (injOn_fiber (fun x => (x, sel q)) (fun a b h => (Prod.ext_iff.1 h).1) P q) ?_ fun b _ => hg b)
        (sum_bondsOver_le hodd hY0 hY z)
      intro p hp
      obtain ⟨h1, h2, h3⟩ := fact q p hp
      have h4 := hsel p h1
      rw [h3] at h4
      exact mem_bondsOver_singleton_of
        (ChartCoordinates.mem_innerBonds (corners_mem_sitesOfCells h1).1 h4) h2
    linarith
  have other : ∀ sel sel' : Fin 4 × Fin 4 → Fin 4,
      (∀ p ∈ innerPlaquettes S 0, p.1 + unitStep 0 (sel p.2) ∈ sitesOfCells S 0 ∧
        p.1 + unitStep 0 (sel p.2) + unitStep 0 (sel' p.2) ∈ sitesOfCells S 0) →
      ∑ p ∈ P, g (p.1 + unitStep 0 (sel p.2), sel' p.2) ≤ 32 * Y := by
    intro sel sel' hsel
    refine le_trans (sum_le_of_fiber_le (Y := 2 * Y) P fun q => ?_) (by linarith)
    have e : ∑ p ∈ P.filter (fun p => p.2 = q), g (p.1 + unitStep 0 (sel p.2), sel' p.2) =
        ∑ p ∈ P.filter (fun p => p.2 = q), g (p.1 + unitStep 0 (sel q), sel' q) :=
      Finset.sum_congr rfl fun p hp => by rw [(fact q p hp).2.2]
    rw [e]
    refine le_trans
      (sum_comp_le_of_injOn (T := fun p : F.Site 0 × Fin 4 × Fin 4 => (p.1 + unitStep 0 (sel q), sel' q))
        (injOn_fiber (fun x => (x + unitStep 0 (sel q), sel' q))
          (fun a b h => add_right_cancel (Prod.ext_iff.1 h).1) P q) ?_ fun b _ => hg b)
      (sum_bondsOver_union_le hodd hg hY0 hY z (z + unitStep F.top (sel q)))
    intro p hp
    obtain ⟨h1, h2, h3⟩ := fact q p hp
    have h4 := hsel p h1
    rw [h3] at h4
    have hb := ChartCoordinates.mem_innerBonds h4.1 h4.2
    rcases enclosingCell_add_unitStep hodd.pos p.1 (sel q) with c | c
    · exact Finset.mem_union_left _ (mem_bondsOver_singleton_of hb (by rw [c, h2]))
    · exact Finset.mem_union_right _ (mem_bondsOver_singleton_of hb (by rw [c, h2]))
  refine ⟨same (fun q => q.1) fun p hp => (corners_mem_sitesOfCells hp).2.1,
    other (fun q => q.1) (fun q => q.2) fun p hp =>
      ⟨(corners_mem_sitesOfCells hp).2.1, (corners_mem_sitesOfCells hp).2.2.2⟩,
    other (fun q => q.2) (fun q => q.1) fun p hp =>
      ⟨(corners_mem_sitesOfCells hp).2.2.1, by
        have := (corners_mem_sitesOfCells hp).2.2.2
        rwa [add_right_comm] at this⟩,
    same (fun q => q.2) fun p hp => (corners_mem_sitesOfCells hp).2.2.1⟩
end NeighbourCells
end NearCellNorms
end YangMills.Construction
end
