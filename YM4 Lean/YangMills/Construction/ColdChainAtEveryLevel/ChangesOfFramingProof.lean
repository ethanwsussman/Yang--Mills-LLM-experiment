import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.ColdChainAtEveryLevel.ChangesOfFraming
import YangMills.Construction.ColdChainAtEveryLevel.EvaluationsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.PointsOfAPatchForm
import YangMills.Construction.ColdChainAtEveryLevel.SitesOfAPatch
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.GaugeChange
open LatticeFractionalIntegration
variable {F : BlockFrame}
section Sums
theorem sum_add_pow_le_add_pow {ι : Type*} (s : Finset ι) (f g : ι → ℝ) (p : ℕ) (hp : 1 ≤ p) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h1 : ∑ i ∈ s, f i ^ p ≤ A ^ p)
    (h2 : ∑ i ∈ s, g i ^ p ≤ B ^ p) : ∑ i ∈ s, (f i + g i) ^ p ≤ (A + B) ^ p := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : p ≠ 0 := by omega
  have key := Real.Lp_add_le_of_nonneg s hp' hf hg
  simp only [Real.rpow_natCast, one_div] at key
  have root : ∀ {u v : ℝ}, 0 ≤ u → 0 ≤ v → u ≤ v ^ p → u ^ ((p : ℝ)⁻¹) ≤ v := by
    intro u v hu hv h
    calc u ^ ((p : ℝ)⁻¹) ≤ (v ^ p) ^ ((p : ℝ)⁻¹) := Real.rpow_le_rpow hu h (by positivity)
      _ = v := Real.pow_rpow_inv_natCast hv hp0
  have a1 := root (Finset.sum_nonneg fun i hi => pow_nonneg (hf i hi) p) hA h1
  have a2 := root (Finset.sum_nonneg fun i hi => pow_nonneg (hg i hi) p) hB h2
  have hs : 0 ≤ ∑ i ∈ s, (f i + g i) ^ p :=
    Finset.sum_nonneg fun i hi => pow_nonneg (add_nonneg (hf i hi) (hg i hi)) p
  calc ∑ i ∈ s, (f i + g i) ^ p = ((∑ i ∈ s, (f i + g i) ^ p) ^ ((p : ℝ)⁻¹)) ^ p :=
        (Real.rpow_inv_natCast_pow hs hp0).symm
    _ ≤ (A + B) ^ p := pow_le_pow_left₀ (Real.rpow_nonneg hs _) (key.trans (add_le_add a1 a2)) p
theorem sum_mul_add_sq_le {ι : Type*} (s : Finset ι) (w f g : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h1 : ∑ i ∈ s, w i * f i ^ 2 ≤ A ^ 2) (h2 : ∑ i ∈ s, w i * g i ^ 2 ≤ B ^ 2) :
    ∑ i ∈ s, w i * (f i + g i) ^ 2 ≤ (A + B) ^ 2 := by
  have e : ∀ (u : ι → ℝ), ∀ i ∈ s, (Real.sqrt (w i) * u i) ^ 2 = w i * u i ^ 2 := by
    intro u i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have m := sum_add_pow_le_add_pow s (fun i => Real.sqrt (w i) * f i) (fun i => Real.sqrt (w i) * g i) 2 (by norm_num)
    (fun i hi => mul_nonneg (Real.sqrt_nonneg _) (hf i hi)) (fun i hi => mul_nonneg (Real.sqrt_nonneg _) (hg i hi))
    hA hB (by rw [Finset.sum_congr rfl (e f)]; exact h1) (by rw [Finset.sum_congr rfl (e g)]; exact h2)
  have e2 : ∀ i ∈ s, (Real.sqrt (w i) * f i + Real.sqrt (w i) * g i) ^ 2 = w i * (f i + g i) ^ 2 := by
    intro i hi
    rw [← mul_add, mul_pow, Real.sq_sqrt (hw i hi)]
  rwa [Finset.sum_congr rfl e2] at m
theorem sum_mul_sq_le_of_fourth {ι : Type*} (s : Finset ι) (f m : ι → ℝ) {P Q : ℝ}
    (h1 : ∑ i ∈ s, f i ^ 4 ≤ P ^ 4) (h2 : ∑ i ∈ s, m i ^ 4 ≤ Q ^ 4) :
    ∑ i ∈ s, (f i * m i) ^ 2 ≤ (P * Q) ^ 2 := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => f i ^ 2) (fun i => m i ^ 2)
  have e1 : ∀ u : ι → ℝ, ∀ i ∈ s, (u i ^ 2) ^ 2 = u i ^ 4 := fun u i _ => by ring
  rw [Finset.sum_congr rfl (e1 f), Finset.sum_congr rfl (e1 m)] at cs
  have e2 : ∑ i ∈ s, f i ^ 2 * m i ^ 2 = ∑ i ∈ s, (f i * m i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e2] at cs
  have hs : 0 ≤ ∑ i ∈ s, (f i * m i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h3 : (∑ i ∈ s, (f i * m i) ^ 2) ^ 2 ≤ ((P * Q) ^ 2) ^ 2 := by
    calc _ ≤ (∑ i ∈ s, f i ^ 4) * ∑ i ∈ s, m i ^ 4 := cs
      _ ≤ P ^ 4 * Q ^ 4 := mul_le_mul h1 h2 (Finset.sum_nonneg fun i _ => by positivity) (by positivity)
      _ = ((P * Q) ^ 2) ^ 2 := by ring
  exact (sq_le_sq₀ hs (by positivity)).1 h3
end Sums
section Tree
theorem exists_centredCube_pow_succ_decomp (hodd : Odd F.blockSide) (e : ℕ) {h : Lattice4}
    (hh : h ∈ centredCube (F.blockSide ^ (e + 1))) :
    ∃ h' ∈ centredCube (F.blockSide ^ e), ∃ g ∈ centredCube F.blockSide,
      ∀ i, h i = (F.blockSide : ℤ) * h' i + g i := by
  obtain ⟨k, hk1, hk2, hk3⟩ := BlockLines.odd_pow_eq_two_mul_add_one hodd 1
  obtain ⟨k', hk1', hk2', hk3'⟩ := BlockLines.odd_pow_eq_two_mul_add_one hodd e
  obtain ⟨K, hK1, hK2, hK3⟩ := BlockLines.odd_pow_eq_two_mul_add_one hodd (e + 1)
  rw [pow_one] at hk1 hk2 hk3
  have hrel : (K : ℤ) = (F.blockSide : ℤ) * k' + k := by
    have e1 : (F.blockSide : ℤ) ^ (e + 1) = F.blockSide * (F.blockSide : ℤ) ^ e := by ring
    rw [hK3, hk3'] at e1
    have : 2 * (K : ℤ) = 2 * ((F.blockSide : ℤ) * k' + k) := by rw [hk3] at e1 ⊢; nlinarith
    omega
  have hLpos : (0 : ℤ) < F.blockSide := by rw [hk3]; omega
  rw [LatticePaths.mem_centredCube_iff, hK2] at hh
  refine ⟨fun i => (h i + k) / (F.blockSide : ℤ), ?_,
    fun i => h i - (F.blockSide : ℤ) * ((h i + k) / (F.blockSide : ℤ)), ?_, fun i => by ring⟩
  · rw [LatticePaths.mem_centredCube_iff, hk2']
    intro i
    have h1 := hh i
    have r1 := Int.emod_add_mul_ediv (h i + k) (F.blockSide : ℤ)
    have r2 := Int.emod_nonneg (h i + k) hLpos.ne'
    have r3 := Int.emod_lt_of_pos (h i + k) hLpos
    set q := (h i + k) / (F.blockSide : ℤ)
    set r := (h i + k) % (F.blockSide : ℤ)
    constructor
    · by_contra hc
      have hc' : q + 1 ≤ -(k' : ℤ) := by omega
      have := mul_le_mul_of_nonneg_left hc' hLpos.le
      nlinarith
    · by_contra hc
      have hc' : (k' : ℤ) + 1 ≤ q := by omega
      have := mul_le_mul_of_nonneg_left hc' hLpos.le
      nlinarith
  · rw [LatticePaths.mem_centredCube_iff, hk2]
    intro i
    have r1 := Int.emod_add_mul_ediv (h i + k) (F.blockSide : ℤ)
    have r2 := Int.emod_nonneg (h i + k) hLpos.ne'
    have r3 := Int.emod_lt_of_pos (h i + k) hLpos
    set q := (h i + k) / (F.blockSide : ℤ)
    set r := (h i + k) % (F.blockSide : ℤ)
    constructor <;> omega
theorem sum_sitesOfCells_eq_sum_blocks (hodd : Odd F.blockSide) {j : ℕ} (hj : j < F.top) (y : F.Cell)
    (φ : F.Site j → ℝ) :
    ∑ x ∈ sitesOfCells {y} j, φ x =
      ∑ y' ∈ sitesOfCells {y} (j + 1), ∑ h ∈ centredCube F.blockSide, φ (refineSite y' + siteOfCoords j h) := by
  classical
  have himg : sitesOfCells {y} j = ((sitesOfCells {y} (j + 1)) ×ˢ centredCube F.blockSide).image
      (fun q : F.Site (j + 1) × Lattice4 => refineSite q.1 + siteOfCoords j q.2) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y₁, hy₁, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
      obtain rfl := Finset.mem_singleton.1 hy₁
      have e1 : F.top - j = (F.top - (j + 1)) + 1 := by omega
      rw [e1] at hh
      obtain ⟨h', hh', g, hg, hs⟩ := exists_centredCube_pow_succ_decomp hodd _ hh
      refine Finset.mem_image.2 ⟨(cellCentre (j + 1) y₁ + siteOfCoords (j + 1) h', g), Finset.mem_product.2
        ⟨mem_sitesOfCells.2 ⟨y₁, Finset.mem_singleton_self _, h', hh', rfl⟩, hg⟩, ?_⟩
      have e2 : cellCentre (j + 1) y₁ + siteOfCoords (j + 1) h' =
          siteOfCoords (F := F) (j + 1)
            (fun i => (F.blockSide : ℤ) ^ (F.top - (j + 1)) * siteCoords y₁ i + h' i) := by
        simp only [cellCentre]
        rw [BlockLines.siteOfCoords_add_fun]
      simp only []
      rw [e2, BlockLines.refineSite_siteOfCoords hj]
      simp only [cellCentre]
      rw [BlockLines.siteOfCoords_add_fun, BlockLines.siteOfCoords_add_fun]
      congr 1
      funext i
      rw [BlockLines.blockSide_pow_sub_eq hj, hs i]
      ring
    · intro hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx
      have hq' := Finset.mem_product.1 hq
      exact BlockLines.refineSite_add_mem_sitesOfCells hj hodd q.1 hq'.1 q.2 hq'.2
  rw [himg, Finset.sum_image, Finset.sum_product]
  intro q hq q' hq' e
  have hq₁ := Finset.mem_product.1 hq
  have hq₂ := Finset.mem_product.1 hq'
  obtain ⟨a, b⟩ := BlockLines.refineSite_add_injective hj hodd q.1 q'.1 q.2 q'.2 hq₁.2 hq₂.2 e
  exact Prod.ext a b
theorem sum_fourth_levels_le (hodd : Odd F.blockSide) (hL : 2 ≤ F.blockSide) (y : F.Cell)
    (f : (j : ℕ) → F.Site j → ℝ) (b : (j : ℕ) → F.Site (j + 1) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ j x, 0 ≤ f j x) (hb : ∀ j x, 0 ≤ b j x)
    (hstep : ∀ j, j < F.top → ∀ y' ∈ sitesOfCells {y} (j + 1), ∀ h ∈ centredCube F.blockSide,
      f j (refineSite y' + siteOfCoords j h) ≤ f (j + 1) y' + b j y')
    (hsum : ∀ j, j < F.top → ∑ y' ∈ sitesOfCells {y} (j + 1), b j y' ^ 4 ≤ B ^ 4)
    (htop : ∑ x ∈ sitesOfCells {y} F.top, f F.top x ^ 4 ≤ B ^ 4) :
    ∀ e j, j + e = F.top → ∑ x ∈ sitesOfCells {y} j, f j x ^ 4 ≤ ((3 * (F.blockSide : ℝ) ^ e - 2) * B) ^ 4 := by
  have hL' : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
  have hpow : ∀ e : ℕ, (1 : ℝ) ≤ (F.blockSide : ℝ) ^ e := fun e => one_le_pow₀ (by linarith)
  intro e
  induction e with
  | zero =>
    intro j hj
    obtain rfl : j = F.top := by omega
    have : (3 * (F.blockSide : ℝ) ^ 0 - 2) * B = B := by simp; ring
    rw [this]
    exact htop
  | succ e ih =>
    intro j hj
    have hjn : j < F.top := by omega
    have hi := ih (j + 1) (by omega)
    have hA : 0 ≤ (3 * (F.blockSide : ℝ) ^ e - 2) * B := mul_nonneg (by linarith [hpow e]) hB
    have m := sum_add_pow_le_add_pow (sitesOfCells {y} (j + 1)) (f (j + 1)) (b j) 4 (by norm_num)
      (fun i _ => hf _ i) (fun i _ => hb _ i) hA hB hi (hsum j hjn)
    rw [sum_sitesOfCells_eq_sum_blocks hodd hjn]
    have hc : ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by
      rw [LatticePaths.card_centredCube hodd]; push_cast; rfl
    calc ∑ y' ∈ sitesOfCells {y} (j + 1), ∑ h ∈ centredCube F.blockSide, f j (refineSite y' + siteOfCoords j h) ^ 4
        ≤ ∑ y' ∈ sitesOfCells {y} (j + 1), ∑ _h ∈ centredCube F.blockSide, (f (j + 1) y' + b j y') ^ 4 :=
          Finset.sum_le_sum fun y' hy' => Finset.sum_le_sum fun h hh =>
            pow_le_pow_left₀ (hf _ _) (hstep j hjn y' hy' h hh) 4
      _ = (F.blockSide : ℝ) ^ 4 * ∑ y' ∈ sitesOfCells {y} (j + 1), (f (j + 1) y' + b j y') ^ 4 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y' _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul, hc]
      _ ≤ (F.blockSide : ℝ) ^ 4 * ((3 * (F.blockSide : ℝ) ^ e - 2) * B + B) ^ 4 :=
          mul_le_mul_of_nonneg_left m (by positivity)
      _ = ((F.blockSide : ℝ) * ((3 * (F.blockSide : ℝ) ^ e - 2) * B + B)) ^ 4 := by ring
      _ ≤ ((3 * (F.blockSide : ℝ) ^ (e + 1) - 2) * B) ^ 4 := by
          refine pow_le_pow_left₀ (by positivity) ?_ 4
          have : (F.blockSide : ℝ) * ((3 * (F.blockSide : ℝ) ^ e - 2) * B + B) =
              (3 * (F.blockSide : ℝ) ^ (e + 1) - F.blockSide) * B := by
            rw [pow_succ]; ring
          rw [this]
          exact mul_le_mul_of_nonneg_right (by linarith) hB
theorem sum_weighted_sq_levels_le (hodd : Odd F.blockSide) (y : F.Cell) (f : (j : ℕ) → F.Site j → ℝ)
    (b : (j : ℕ) → F.Site (j + 1) → ℝ) (w : (j : ℕ) → F.Site j → ℝ) {B D ρ : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hρ : 0 ≤ ρ) (hf : ∀ j x, 0 ≤ f j x) (hb : ∀ j x, 0 ≤ b j x) (hw : ∀ j x, 0 ≤ w j x)
    (hstep : ∀ j, j < F.top → ∀ y' ∈ sitesOfCells {y} (j + 1), ∀ h ∈ centredCube F.blockSide,
      f j (refineSite y' + siteOfCoords j h) ≤ f (j + 1) y' + b j y')
    (hsum : ∀ j, j < F.top → ∑ y' ∈ sitesOfCells {y} (j + 1), b j y' ^ 4 ≤ B ^ 4)
    (htop : ∀ x ∈ sitesOfCells {y} F.top, f F.top x ≤ B)
    (hrec : ∀ j, j < F.top → ∀ y' ∈ sitesOfCells {y} (j + 1),
      ∑ h ∈ centredCube F.blockSide, w j (refineSite y' + siteOfCoords j h) = w (j + 1) y')
    (hsup : ∀ e j, j + 1 + e = F.top → ∀ y' ∈ sitesOfCells {y} (j + 1), w (j + 1) y' ≤ D ^ 2 * (ρ ^ e) ^ 4)
    (htot : ∑ x ∈ sitesOfCells {y} F.top, w F.top x ≤ D ^ 2) :
    ∀ e j, j + e = F.top → ∑ x ∈ sitesOfCells {y} j, w j x * f j x ^ 2 ≤
      (D * B * (1 + ∑ i ∈ Finset.range e, ρ ^ i)) ^ 2 := by
  have total : ∀ e j, j + e = F.top → ∑ x ∈ sitesOfCells {y} j, w j x ≤ D ^ 2 := by
    intro e
    induction e with
    | zero =>
      intro j hj
      obtain rfl : j = F.top := by omega
      exact htot
    | succ e ih =>
      intro j hj
      have hjn : j < F.top := by omega
      rw [sum_sitesOfCells_eq_sum_blocks hodd hjn, Finset.sum_congr rfl (hrec j hjn)]
      exact ih (j + 1) (by omega)
  intro e
  induction e with
  | zero =>
    intro j hj
    obtain rfl : j = F.top := by omega
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, mul_one]
    calc ∑ x ∈ sitesOfCells {y} F.top, w F.top x * f F.top x ^ 2
        ≤ ∑ x ∈ sitesOfCells {y} F.top, w F.top x * B ^ 2 :=
          Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (hf _ _) (htop x hx) 2) (hw _ _)
      _ = (∑ x ∈ sitesOfCells {y} F.top, w F.top x) * B ^ 2 := by rw [Finset.sum_mul]
      _ ≤ D ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_right htot (by positivity)
      _ = (D * B) ^ 2 := by ring
  | succ e ih =>
    intro j hj
    have hjn : j < F.top := by omega
    have hi := ih (j + 1) (by omega)
    have hsumρ : 0 ≤ ∑ i ∈ Finset.range e, ρ ^ i := Finset.sum_nonneg fun i _ => pow_nonneg hρ i
    have hA : 0 ≤ D * B * (1 + ∑ i ∈ Finset.range e, ρ ^ i) := by positivity
    have hE : 0 ≤ D * ρ ^ e * B := by positivity
    have hcs : ∑ y' ∈ sitesOfCells {y} (j + 1), w (j + 1) y' * b j y' ^ 2 ≤ (D * ρ ^ e * B) ^ 2 := by
      have cs := Finset.sum_mul_sq_le_sq_mul_sq (sitesOfCells {y} (j + 1)) (w (j + 1)) (fun i => b j i ^ 2)
      have e1 : ∑ i ∈ sitesOfCells {y} (j + 1), (b j i ^ 2) ^ 2 = ∑ i ∈ sitesOfCells {y} (j + 1), b j i ^ 4 :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [e1] at cs
      have h2 : ∑ i ∈ sitesOfCells {y} (j + 1), w (j + 1) i ^ 2 ≤ D ^ 2 * (ρ ^ e) ^ 4 * D ^ 2 := by
        calc ∑ i ∈ sitesOfCells {y} (j + 1), w (j + 1) i ^ 2
            ≤ ∑ i ∈ sitesOfCells {y} (j + 1), D ^ 2 * (ρ ^ e) ^ 4 * w (j + 1) i :=
              Finset.sum_le_sum fun i hi' => by
                rw [sq]
                exact mul_le_mul_of_nonneg_right (hsup e j (by omega) i hi') (hw _ _)
          _ = D ^ 2 * (ρ ^ e) ^ 4 * ∑ i ∈ sitesOfCells {y} (j + 1), w (j + 1) i := by rw [Finset.mul_sum]
          _ ≤ D ^ 2 * (ρ ^ e) ^ 4 * D ^ 2 :=
              mul_le_mul_of_nonneg_left (total (e) (j + 1) (by omega)) (by positivity)
      have h3 : (∑ y' ∈ sitesOfCells {y} (j + 1), w (j + 1) y' * b j y' ^ 2) ^ 2 ≤ ((D * ρ ^ e * B) ^ 2) ^ 2 := by
        calc _ ≤ (∑ i ∈ sitesOfCells {y} (j + 1), w (j + 1) i ^ 2) * ∑ i ∈ sitesOfCells {y} (j + 1), b j i ^ 4 := cs
          _ ≤ (D ^ 2 * (ρ ^ e) ^ 4 * D ^ 2) * B ^ 4 :=
              mul_le_mul h2 (hsum j hjn) (Finset.sum_nonneg fun i _ => by
                have := hb j i
                positivity) (by positivity)
          _ = ((D * ρ ^ e * B) ^ 2) ^ 2 := by ring
      exact (sq_le_sq₀ (Finset.sum_nonneg fun i _ => mul_nonneg (hw _ _) (sq_nonneg _)) (by positivity)).1 h3
    have m := sum_mul_add_sq_le (sitesOfCells {y} (j + 1)) (w (j + 1)) (f (j + 1)) (b j)
      (fun i _ => hw _ i) (fun i _ => hf _ i) (fun i _ => hb _ i) hA hE hi hcs
    rw [sum_sitesOfCells_eq_sum_blocks hodd hjn]
    calc ∑ y' ∈ sitesOfCells {y} (j + 1), ∑ h ∈ centredCube F.blockSide,
          w j (refineSite y' + siteOfCoords j h) * f j (refineSite y' + siteOfCoords j h) ^ 2
        ≤ ∑ y' ∈ sitesOfCells {y} (j + 1), ∑ h ∈ centredCube F.blockSide,
          w j (refineSite y' + siteOfCoords j h) * (f (j + 1) y' + b j y') ^ 2 :=
          Finset.sum_le_sum fun y' hy' => Finset.sum_le_sum fun h hh => mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (hf _ _) (hstep j hjn y' hy' h hh) 2) (hw _ _)
      _ = ∑ y' ∈ sitesOfCells {y} (j + 1), w (j + 1) y' * (f (j + 1) y' + b j y') ^ 2 := by
          refine Finset.sum_congr rfl fun y' hy' => ?_
          rw [← Finset.sum_mul, hrec j hjn y' hy']
      _ ≤ (D * B * (1 + ∑ i ∈ Finset.range e, ρ ^ i) + D * ρ ^ e * B) ^ 2 := m
      _ = (D * B * (1 + ∑ i ∈ Finset.range (e + 1), ρ ^ i)) ^ 2 := by
          rw [Finset.sum_range_succ]
          ring
end Tree
section Units
theorem normSubOne_mul_le (a b : UnitQuaternion) : normSubOne (a * b) ≤ normSubOne a + normSubOne b := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
theorem normSubOne_inv (a : UnitQuaternion) : normSubOne a⁻¹ = normSubOne a := norm_coe_inv_sub_one a
theorem normSubOne_conj (a b : UnitQuaternion) : normSubOne (a * b * a⁻¹) = normSubOne b := norm_coe_conj_sub_one a b
theorem normSubOne_nonneg (a : UnitQuaternion) : 0 ≤ normSubOne a := norm_nonneg _
theorem normSubOne_polarUnit_le (q : ℍ[ℝ]) : normSubOne (polarUnit q) ≤ 2 * ‖q - 1‖ := by
  by_cases h : q = 0
  · have e : polarUnit q = 1 := by simp [polarUnit, h]
    rw [e]
    have : normSubOne (1 : UnitQuaternion) = 0 := by simp [normSubOne]
    rw [this]
    positivity
  · unfold normSubOne
    rw [coe_polarUnit h]
    have hn : 0 < ‖q‖ := norm_pos_iff.2 h
    have e : ‖q‖⁻¹ • q - 1 = (‖q‖⁻¹ - 1) • q + (q - 1) := by
      rw [sub_smul, one_smul]
      abel
    have e2 : ‖(‖q‖⁻¹ - 1) • q‖ = |1 - ‖q‖| := by
      rw [norm_smul, Real.norm_eq_abs]
      have : |‖q‖⁻¹ - 1| * ‖q‖ = |(‖q‖⁻¹ - 1) * ‖q‖| := by
        rw [abs_mul, abs_of_pos hn]
      rw [this]
      congr 1
      field_simp
    have e3 : |1 - ‖q‖| ≤ ‖q - 1‖ := by
      have := abs_norm_sub_norm_le (1 : ℍ[ℝ]) q
      rw [norm_one, norm_sub_rev] at this
      exact this
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [e2]
    linarith
end Units
section Paths
variable {j : ℕ}
def linkDiscrepancy (X R : F.GaugeField j) (x : F.Site j) (st : PathStep) : UnitQuaternion :=
  linkValue X x st * (linkValue R x st)⁻¹
def pathDiscrepancy (X R : F.GaugeField j) (x : F.Site j) (l : List PathStep) : UnitQuaternion :=
  pathHolonomy X x l * (pathHolonomy R x l)⁻¹
theorem pathDiscrepancy_cons (X R : F.GaugeField j) (x : F.Site j) (st : PathStep) (l : List PathStep) :
    pathDiscrepancy X R x (st :: l) = linkDiscrepancy X R x st *
      (linkValue R x st * pathDiscrepancy X R (x + stepDisplacement j st) l * (linkValue R x st)⁻¹) := by
  simp only [pathDiscrepancy, linkDiscrepancy, pathHolonomy]
  group
theorem stepDisplacement_eq_siteOfCoords (st : PathStep) :
    stepDisplacement (F := F) j st = siteOfCoords j (FlatPairing.stepDisplacement st) := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.stepDisplacement_eq_siteOfCoords <;> assumption
theorem linkDiscrepancy_forward (X R : F.GaugeField j) (x : F.Site j) (k : Fin 4) :
    linkDiscrepancy X R x (k, true) = X x k * (R x k)⁻¹ := by
  simp [linkDiscrepancy, linkValue]
theorem normSubOne_linkDiscrepancy_backward (X R : F.GaugeField j) (x : F.Site j) (k : Fin 4) :
    normSubOne (linkDiscrepancy X R x (k, false)) =
      normSubOne (X (x - unitStep j k) k * (R (x - unitStep j k) k)⁻¹) := by
  have e : ∀ a b : UnitQuaternion, a⁻¹ * (b⁻¹)⁻¹ = (b⁻¹ * (a * b⁻¹) * (b⁻¹)⁻¹)⁻¹ := by
    intro a b
    group
  have e2 : linkDiscrepancy X R x (k, false) = (X (x - unitStep j k) k)⁻¹ * ((R (x - unitStep j k) k)⁻¹)⁻¹ := by
    simp [linkDiscrepancy, linkValue]
  rw [e2, e, normSubOne_inv, normSubOne_conj]
theorem normSubOne_linkDiscrepancy_le (X R : F.GaugeField j) (x₀ : F.Site j) (H : Set Lattice4) (t : ℝ)
    (hcl : ∀ a ∈ H, ∀ k, a + basisVector k ∈ H →
      normSubOne (X (x₀ + siteOfCoords j a) k * (R (x₀ + siteOfCoords j a) k)⁻¹) ≤ t)
    (u : Lattice4) (st : PathStep) (hu : u ∈ H) (hv : u + FlatPairing.stepDisplacement st ∈ H) :
    normSubOne (linkDiscrepancy X R (x₀ + siteOfCoords j u) st) ≤ t := by
  obtain ⟨k, b⟩ := st
  cases b with
  | true =>
    rw [linkDiscrepancy_forward]
    exact hcl u hu k (by simpa [FlatPairing.stepDisplacement] using hv)
  | false =>
    rw [normSubOne_linkDiscrepancy_backward]
    have hv' : u - basisVector k ∈ H := by simpa [FlatPairing.stepDisplacement, sub_eq_add_neg] using hv
    have e : x₀ + siteOfCoords j u - unitStep j k = x₀ + siteOfCoords j (u - basisVector k) := by
      rw [unitStep_eq, siteOfCoords_sub, add_sub_assoc]
    rw [e]
    exact hcl _ hv' k (by simpa using hu)
theorem normSubOne_pathDiscrepancy_le (X R : F.GaugeField j) (x₀ : F.Site j) (p : Lattice4 → Prop) (t : ℝ)
    (ht : ∀ u st, p u → p (u + FlatPairing.stepDisplacement st) →
      normSubOne (linkDiscrepancy X R (x₀ + siteOfCoords j u) st) ≤ t) :
    ∀ (l : List PathStep) (u : Lattice4), LatticePaths.AllAlong p u l →
      normSubOne (pathDiscrepancy X R (x₀ + siteOfCoords j u) l) ≤ l.length * t := by
  intro l
  induction l with
  | nil =>
    intro u _
    simp [pathDiscrepancy, pathHolonomy, normSubOne]
  | cons st r ih =>
    intro u hu
    have e : x₀ + siteOfCoords j u + stepDisplacement j st =
        x₀ + siteOfCoords j (u + FlatPairing.stepDisplacement st) := by
      rw [stepDisplacement_eq_siteOfCoords, siteOfCoords_add, add_assoc]
    rw [pathDiscrepancy_cons, e]
    have h1 := ht u st hu.1 (LatticePaths.allAlong_head hu.2)
    have h2 := ih _ hu.2
    have h3 := normSubOne_mul_le (linkDiscrepancy X R (x₀ + siteOfCoords j u) st)
      (linkValue R (x₀ + siteOfCoords j u) st *
        pathDiscrepancy X R (x₀ + siteOfCoords j (u + FlatPairing.stepDisplacement st)) r *
        (linkValue R (x₀ + siteOfCoords j u) st)⁻¹)
    rw [normSubOne_conj] at h3
    have hl : (((st :: r).length : ℕ) : ℝ) * t = (r.length : ℝ) * t + t := by
      simp only [List.length_cons]
      push_cast
      ring
    rw [hl]
    linarith
theorem length_axisPath_le {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) (π : Equiv.Perm (Fin 4)) :
    ((axisPath h π).length : ℝ) ≤ 2 * L := by
  have hlen : ∀ μ, (h μ).natAbs ≤ (L - 1) / 2 := by
    intro μ
    have h1 := ((LatticePaths.mem_centredCube_iff L h).1 hh) μ
    omega
  have h0 := hlen (π 0)
  have h1 := hlen (π 1)
  have h2 := hlen (π 2)
  have h3 := hlen (π 3)
  have hl := LatticePaths.length_axisPath h π
  have : (axisPath h π).length ≤ 2 * L := by omega
  exact_mod_cast this
theorem normSubOne_axisPath_discrepancy_le (T R : F.GaugeField j) (y : F.Site (j + 1)) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ∀ a ∈ centredCube F.blockSide, ∀ k, a + basisVector k ∈ centredCube F.blockSide →
      normSubOne (T (refineSite y + siteOfCoords j a) k * (R (refineSite y + siteOfCoords j a) k)⁻¹) ≤ t)
    {h : Lattice4} (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    normSubOne (pathHolonomy T (refineSite y) (axisPath h π) * (pathHolonomy R (refineSite y) (axisPath h π))⁻¹) ≤
      2 * F.blockSide * t := by
  have hp : LatticePaths.AllAlong (fun u => u ∈ centredCube F.blockSide) 0 (axisPath h π) := by
    refine LatticePaths.allAlong_mono (fun v hv => ?_) (LatticePaths.axisPath_spec h π).1
    rw [LatticePaths.mem_centredCube_iff]
    intro i
    have b := ((LatticePaths.mem_centredCube_iff F.blockSide h).1 hh) i
    have c := hv i
    omega
  have key := normSubOne_pathDiscrepancy_le T R (refineSite y) (fun u => u ∈ centredCube F.blockSide) t
    (fun u st hu hv => normSubOne_linkDiscrepancy_le T R (refineSite y) (↑(centredCube F.blockSide) : Set Lattice4) t
      (fun a ha k hk => ht a ha k hk) u st hu hv) _ _ hp
  have e0 : refineSite y + siteOfCoords j (0 : Lattice4) = refineSite y := by
    have : siteOfCoords (F := F) j (0 : Lattice4) = 0 := by
      funext i
      simp [siteOfCoords]
    rw [this, add_zero]
  rw [e0] at key
  refine key.trans ?_
  exact mul_le_mul_of_nonneg_right (length_axisPath_le hh π) ht0
theorem norm_relativePathAverage_sub_one_le (hodd : Odd F.blockSide) (T R : F.GaugeField j) (y : F.Site (j + 1)) {δ : ℝ}
    (hδ : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      normSubOne (pathHolonomy T (refineSite y) (axisPath h π) *
        (pathHolonomy R (refineSite y) (axisPath h π))⁻¹) ≤ δ) :
    ‖relativePathAverage T R y - 1‖ ≤ δ := by
  have hL : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have hc : ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by
    rw [LatticePaths.card_centredCube hodd]; push_cast; rfl
  have hperm : ((Finset.univ : Finset (Equiv.Perm (Fin 4))).card : ℝ) = 24 := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  set c : ℝ := 1 / (24 * (F.blockSide : ℝ) ^ 4) with hcdef
  have hcpos : 0 < c := by positivity
  have hone : (1 : ℍ[ℝ]) = c • ∑ _h ∈ centredCube F.blockSide, ∑ _π : Equiv.Perm (Fin 4), (1 : ℍ[ℝ]) := by
    simp only [Finset.sum_const]
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul, hc, hperm]
    have : c * (F.blockSide : ℝ) ^ 4 * 24 = 1 := by
      rw [hcdef]
      field_simp
    rw [this, one_smul]
  have e : relativePathAverage T R y - 1 = c • ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      (((pathHolonomy T (refineSite y) (axisPath h π) * (pathHolonomy R (refineSite y) (axisPath h π))⁻¹ :
        UnitQuaternion) : ℍ[ℝ]) - 1) := by
    simp only [Finset.sum_sub_distrib]
    rw [smul_sub, ← hone]
    rfl
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
  have b : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4),
      (((pathHolonomy T (refineSite y) (axisPath h π) * (pathHolonomy R (refineSite y) (axisPath h π))⁻¹ :
        UnitQuaternion) : ℍ[ℝ]) - 1)‖ ≤
      (F.blockSide : ℝ) ^ 4 * 24 * δ := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), δ :=
          Finset.sum_le_sum fun h hh => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun π _ => hδ h hh π)
      _ = (F.blockSide : ℝ) ^ 4 * 24 * δ := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [hc, hperm]
          ring
  calc c * _ ≤ c * ((F.blockSide : ℝ) ^ 4 * 24 * δ) := mul_le_mul_of_nonneg_left b hcpos.le
    _ = δ := by
      rw [hcdef]
      field_simp
theorem linkValue_gaugeTransform (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j) (x : F.Site j)
    (st : PathStep) :
    linkValue (gaugeTransform γ X) x st = γ x * linkValue X x st * (γ (x + stepDisplacement j st))⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.linkValue_gaugeTransform <;> assumption
theorem pathHolonomy_gaugeTransform (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j) (x₀ : F.Site j)
    (l : List PathStep) :
    ∀ u : Lattice4, pathHolonomy (gaugeTransform γ X) (x₀ + siteOfCoords j u) l =
      γ (x₀ + siteOfCoords j u) * pathHolonomy X (x₀ + siteOfCoords j u) l *
        (γ (x₀ + siteOfCoords j (LatticePaths.endpoint u l)))⁻¹ := by
  induction l with
  | nil =>
    intro u
    simp [pathHolonomy, LatticePaths.endpoint]
  | cons st r ih =>
    intro u
    have e : x₀ + siteOfCoords j u + stepDisplacement j st =
        x₀ + siteOfCoords j (u + FlatPairing.stepDisplacement st) := by
      rw [stepDisplacement_eq_siteOfCoords, siteOfCoords_add, add_assoc]
    simp only [pathHolonomy, LatticePaths.endpoint]
    rw [e, ih, linkValue_gaugeTransform, e]
    simp only [mul_assoc, inv_mul_cancel_left]
end Paths
section Links
variable (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k Γ Γ' : F.SiteGauge)
theorem gaugeChangeAbove_eq {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (h1 : ∀ y, Γ F.top y = 1)
    (h1' : ∀ y, Γ' F.top y = 1)
    (hb : j + 1 < F.top → gaugedLink k Γ j y = balancedLinkAgainst W kW (gaugedChainFields X Γ) j y)
    (hb' : j + 1 < F.top → gaugedLink k Γ' j y = balancedLinkAgainst W kW (gaugedChainFields X Γ') j y) :
    gaugeChangeAbove W kW X k Γ Γ' j y = kW (j + 1) y * (balancingGauge (gaugedChainFields X Γ j) (W j) y *
      gaugeChange Γ Γ' j (refineSite y) * (balancingGauge (gaugedChainFields X Γ' j) (W j) y)⁻¹) *
        (kW (j + 1) y)⁻¹ := by
  have hn : F.top = F.depth + 1 := rfl
  by_cases ht : j = F.depth
  · subst ht
    simp only [gaugeChangeAbove, if_true, balancedRotation, balancedLinkAgainst, gaugedLink, gaugeChange]
    have a1 : Γ (F.depth + 1) y = 1 := h1 y
    have a2 : Γ' (F.depth + 1) y = 1 := h1' y
    rw [a1, a2]
    group
  · have hlt : j + 1 < F.top := by omega
    have e1 := hb hlt
    have e2 := hb' hlt
    simp only [gaugedLink, balancedLinkAgainst] at e1 e2
    simp only [gaugeChangeAbove, if_neg ht, gaugeChange]
    have a1 : Γ (j + 1) y = kW (j + 1) y * balancingGauge (gaugedChainFields X Γ j) (W j) y *
        Γ j (refineSite y) * (k (j + 1) y)⁻¹ := by
      rw [← e1]
      group
    have a2 : Γ' (j + 1) y = kW (j + 1) y * balancingGauge (gaugedChainFields X Γ' j) (W j) y *
        Γ' j (refineSite y) * (k (j + 1) y)⁻¹ := by
      rw [← e2]
      group
    rw [a1, a2]
    group
theorem normSubOne_gaugeChange_le (hodd : Odd F.blockSide) {j : ℕ} (y : F.Site (j + 1))
    (hch : gaugeChangeAbove W kW X k Γ Γ' j y = kW (j + 1) y * (balancingGauge (gaugedChainFields X Γ j) (W j) y *
      gaugeChange Γ Γ' j (refineSite y) * (balancingGauge (gaugedChainFields X Γ' j) (W j) y)⁻¹) *
        (kW (j + 1) y)⁻¹)
    {δ δ' : ℝ}
    (hδ : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      normSubOne (pathHolonomy (gaugedChainFields X Γ j) (refineSite y) (axisPath h π) *
        (pathHolonomy (W j) (refineSite y) (axisPath h π))⁻¹) ≤ δ)
    (hδ' : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      normSubOne (pathHolonomy (gaugedChainFields X Γ' j) (refineSite y) (axisPath h π) *
        (pathHolonomy (W j) (refineSite y) (axisPath h π))⁻¹) ≤ δ')
    {h : Lattice4} (hh : h ∈ centredCube F.blockSide) :
    normSubOne (gaugeChange Γ Γ' j (refineSite y + siteOfCoords j h)) ≤
      normSubOne (gaugeChangeAbove W kW X k Γ Γ' j y) + 3 * (δ + δ') := by
  set d := refineSite y with hd
  set B := balancingGauge (gaugedChainFields X Γ j) (W j) y with hB
  set B' := balancingGauge (gaugedChainFields X Γ' j) (W j) y with hB'
  have sB : normSubOne B ≤ 2 * δ := by
    rw [hB, balancingGauge, normSubOne_inv]
    exact (normSubOne_polarUnit_le _).trans
      (mul_le_mul_of_nonneg_left (norm_relativePathAverage_sub_one_le hodd _ _ y hδ) (by norm_num))
  have sB' : normSubOne B' ≤ 2 * δ' := by
    rw [hB', balancingGauge, normSubOne_inv]
    exact (normSubOne_polarUnit_le _).trans
      (mul_le_mul_of_nonneg_left (norm_relativePathAverage_sub_one_le hodd _ _ y hδ') (by norm_num))
  have scentre : normSubOne (gaugeChange Γ Γ' j d) ≤
      normSubOne (gaugeChangeAbove W kW X k Γ Γ' j y) + 2 * δ + 2 * δ' := by
    have e : gaugeChange Γ Γ' j d = B⁻¹ * (B * gaugeChange Γ Γ' j d * B'⁻¹) * B' := by group
    have e2 : normSubOne (B * gaugeChange Γ Γ' j d * B'⁻¹) = normSubOne (gaugeChangeAbove W kW X k Γ Γ' j y) := by
      rw [hch, normSubOne_conj]
    have s1 := normSubOne_mul_le (B⁻¹ * (B * gaugeChange Γ Γ' j d * B'⁻¹)) B'
    have s2 := normSubOne_mul_le B⁻¹ (B * gaugeChange Γ Γ' j d * B'⁻¹)
    rw [normSubOne_inv] at s2
    rw [e]
    linarith
  set l := axisPath h (1 : Equiv.Perm (Fin 4)) with hl
  have hend : LatticePaths.endpoint 0 l = h := (LatticePaths.axisPath_spec h 1).2
  have e0 : d + siteOfCoords j (0 : Lattice4) = d := by
    have : siteOfCoords (F := F) j (0 : Lattice4) = 0 := by
      funext i
      simp [siteOfCoords]
    rw [this, add_zero]
  have g1 : pathHolonomy (gaugedChainFields X Γ j) d l =
      Γ j d * pathHolonomy (X j) d l * (Γ j (d + siteOfCoords j h))⁻¹ := by
    have := pathHolonomy_gaugeTransform (Γ j) (X j) d l 0
    rw [e0, hend] at this
    exact this
  have g2 : pathHolonomy (gaugedChainFields X Γ' j) d l =
      Γ' j d * pathHolonomy (X j) d l * (Γ' j (d + siteOfCoords j h))⁻¹ := by
    have := pathHolonomy_gaugeTransform (Γ' j) (X j) d l 0
    rw [e0, hend] at this
    exact this
  set G := pathHolonomy (gaugedChainFields X Γ j) d l * (pathHolonomy (W j) d l)⁻¹ with hG
  set G' := pathHolonomy (gaugedChainFields X Γ' j) d l * (pathHolonomy (W j) d l)⁻¹ with hG'
  have sG : normSubOne G ≤ δ := hδ h hh 1
  have sG' : normSubOne G' ≤ δ' := hδ' h hh 1
  have key : pathHolonomy (W j) d l * (gaugeChange Γ Γ' j (d + siteOfCoords j h))⁻¹ * (pathHolonomy (W j) d l)⁻¹ =
      G'⁻¹ * (gaugeChange Γ Γ' j d)⁻¹ * G := by
    rw [hG, hG', g1, g2]
    simp only [gaugeChange]
    group
  have s3 : normSubOne (gaugeChange Γ Γ' j (d + siteOfCoords j h)) =
      normSubOne (G'⁻¹ * (gaugeChange Γ Γ' j d)⁻¹ * G) := by
    rw [← key, normSubOne_conj, normSubOne_inv]
  have s4 := normSubOne_mul_le (G'⁻¹ * (gaugeChange Γ Γ' j d)⁻¹) G
  have s5 := normSubOne_mul_le G'⁻¹ (gaugeChange Γ Γ' j d)⁻¹
  rw [normSubOne_inv, normSubOne_inv] at s5
  rw [s3]
  linarith
end Links
section Blocks
open Classical in
def blockBondOffsets (L : ℕ) : Finset (Lattice4 × Fin 4) :=
  ((centredCube L) ×ˢ (Finset.univ : Finset (Fin 4))).filter fun q => q.1 + basisVector q.2 ∈ centredCube L
variable {j : ℕ}
def blockQuarticSum (g : F.Site j × Fin 4 → ℝ) (y : F.Site (j + 1)) : ℝ :=
  ∑ q ∈ blockBondOffsets F.blockSide, g (refineSite y + siteOfCoords j q.1, q.2) ^ 4
def blockQuarticRoot (g : F.Site j × Fin 4 → ℝ) (y : F.Site (j + 1)) : ℝ :=
  Real.sqrt (Real.sqrt (blockQuarticSum g y))
theorem blockQuarticSum_nonneg (g : F.Site j × Fin 4 → ℝ) (y : F.Site (j + 1)) : 0 ≤ blockQuarticSum g y :=
  Finset.sum_nonneg fun _ _ => by positivity
theorem blockQuarticRoot_nonneg (g : F.Site j × Fin 4 → ℝ) (y : F.Site (j + 1)) : 0 ≤ blockQuarticRoot g y :=
  Real.sqrt_nonneg _
theorem blockQuarticRoot_pow_four (g : F.Site j × Fin 4 → ℝ) (y : F.Site (j + 1)) :
    blockQuarticRoot g y ^ 4 = blockQuarticSum g y := by
  have h := blockQuarticSum_nonneg g y
  have e : blockQuarticRoot g y ^ 4 = (Real.sqrt (Real.sqrt (blockQuarticSum g y)) ^ 2) ^ 2 := by
    unfold blockQuarticRoot
    ring
  rw [e, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt h]
theorem le_blockQuarticRoot (g : F.Site j × Fin 4 → ℝ) (hg : ∀ b, 0 ≤ g b) (y : F.Site (j + 1)) {a : Lattice4}
    {k : Fin 4} (ha : a ∈ centredCube F.blockSide) (hk : a + basisVector k ∈ centredCube F.blockSide) :
    g (refineSite y + siteOfCoords j a, k) ≤ blockQuarticRoot g y := by
  have hm : (a, k) ∈ blockBondOffsets F.blockSide :=
    Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, Finset.mem_univ _⟩, hk⟩
  have h1 : g (refineSite y + siteOfCoords j a, k) ^ 4 ≤ blockQuarticSum g y :=
    Finset.single_le_sum (f := fun q : Lattice4 × Fin 4 => g (refineSite y + siteOfCoords j q.1, q.2) ^ 4)
      (fun _ _ => by positivity) hm
  rw [← blockQuarticRoot_pow_four] at h1
  exact (pow_le_pow_iff_left₀ (hg _) (blockQuarticRoot_nonneg _ _) (by norm_num)).1 h1
def blockBondAt (q : F.Site (j + 1) × (Lattice4 × Fin 4)) : F.Site j × Fin 4 :=
  (refineSite q.1 + siteOfCoords j q.2.1, q.2.2)
theorem blockBondAt_injective (hodd : Odd F.blockSide) (hj : j < F.top) (q q' : F.Site (j + 1) × (Lattice4 × Fin 4))
    (hq : q.2 ∈ blockBondOffsets F.blockSide) (hq' : q'.2 ∈ blockBondOffsets F.blockSide)
    (e : blockBondAt q = blockBondAt q') : q = q' := by
  have a1 := Finset.mem_product.1 (Finset.mem_filter.1 hq).1
  have a2 := Finset.mem_product.1 (Finset.mem_filter.1 hq').1
  have e1 : refineSite q.1 + siteOfCoords j q.2.1 = refineSite q'.1 + siteOfCoords j q'.2.1 := congrArg Prod.fst e
  have e2 : q.2.2 = q'.2.2 := congrArg (fun b : F.Site j × Fin 4 => b.2) e
  obtain ⟨b1, b2⟩ := BlockLines.refineSite_add_injective hj hodd q.1 q'.1 q.2.1 q'.2.1 a1.1 a2.1 e1
  exact Prod.ext b1 (Prod.ext b2 e2)
theorem blockBondAt_mem_innerBonds (hodd : Odd F.blockSide) (hj : j < F.top) (y : F.Cell)
    (q : F.Site (j + 1) × (Lattice4 × Fin 4))
    (h1 : q.1 ∈ sitesOfCells {y} (j + 1)) (hq : q.2 ∈ blockBondOffsets F.blockSide) :
    blockBondAt q ∈ innerBonds {y} j := by
  have hq2 := Finset.mem_filter.1 hq
  have hq3 := Finset.mem_product.1 hq2.1
  have e : refineSite q.1 + siteOfCoords j q.2.1 + unitStep j q.2.2 =
      refineSite q.1 + siteOfCoords j (q.2.1 + basisVector q.2.2) := by
    rw [unitStep_eq, add_assoc, ← siteOfCoords_add]
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2
    ⟨BlockLines.refineSite_add_mem_sitesOfCells hj hodd q.1 h1 _ hq3.1, Finset.mem_univ _⟩, ?_⟩
  show refineSite q.1 + siteOfCoords j q.2.1 + unitStep j q.2.2 ∈ sitesOfCells {y} j
  rw [e]
  exact BlockLines.refineSite_add_mem_sitesOfCells hj hodd q.1 h1 _ hq2.2
theorem sum_blockQuarticSum_le (hodd : Odd F.blockSide) (hj : j < F.top) (y : F.Cell) (g : F.Site j × Fin 4 → ℝ) :
    ∑ y' ∈ sitesOfCells {y} (j + 1), blockQuarticSum g y' ≤ ∑ b ∈ innerBonds {y} j, g b ^ 4 := by
  classical
  unfold blockQuarticSum
  rw [← Finset.sum_product']
  have hinj : Set.InjOn (blockBondAt (F := F) (j := j))
      (↑(sitesOfCells {y} (j + 1) ×ˢ blockBondOffsets F.blockSide)) := by
    intro q hq q' hq' e
    exact blockBondAt_injective hodd hj q q' (Finset.mem_product.1 hq).2 (Finset.mem_product.1 hq').2 e
  have e1 : ∑ b ∈ (sitesOfCells {y} (j + 1) ×ˢ blockBondOffsets F.blockSide).image (blockBondAt (F := F) (j := j)),
      g b ^ 4 = ∑ q ∈ sitesOfCells {y} (j + 1) ×ˢ blockBondOffsets F.blockSide, g (blockBondAt q) ^ 4 :=
    Finset.sum_image hinj
  have e2 : ∑ b ∈ (sitesOfCells {y} (j + 1) ×ˢ blockBondOffsets F.blockSide).image (blockBondAt (F := F) (j := j)),
      g b ^ 4 ≤ ∑ b ∈ innerBonds {y} j, g b ^ 4 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro b hb
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hb
    have hq1 := Finset.mem_product.1 hq
    exact blockBondAt_mem_innerBonds hodd hj y q hq1.1 hq1.2
  exact e1 ▸ e2
end Blocks
section Levels
variable (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k Γ Γ' : F.SiteGauge)
def bondDiscrepancy (Γ : F.SiteGauge) (j : ℕ) (b : F.Site j × Fin 4) : ℝ :=
  normSubOne (gaugedChainFields X Γ j b.1 b.2 * (W j b.1 b.2)⁻¹)
def levelChange : (j : ℕ) → F.Site j → ℝ
  | 0 => fun x => normSubOne (gaugeChange Γ Γ' 0 x)
  | j + 1 => fun y => normSubOne (gaugeChangeAbove W kW X k Γ Γ' j y)
theorem levelChange_nonneg (j : ℕ) (x : F.Site j) : 0 ≤ levelChange W kW X k Γ Γ' j x := by
  cases j <;> exact normSubOne_nonneg _
theorem levelChange_eq {j : ℕ} (hj : j < F.top) (x : F.Site j) :
    levelChange W kW X k Γ Γ' j x = normSubOne (gaugeChange Γ Γ' j x) := by
  have hn : F.top = F.depth + 1 := rfl
  cases j with
  | zero => rfl
  | succ i =>
    have ht : i ≠ F.depth := by omega
    simp only [levelChange, gaugeChangeAbove, if_neg ht]
structure LevelData (y : F.Cell) (e : ℝ) : Prop where
  odd : Odd F.blockSide
  five_le : 5 ≤ F.blockSide
  nonneg : 0 ≤ e
  top_one : ∀ y, Γ F.top y = 1
  top_one' : ∀ y, Γ' F.top y = 1
  balanced : ∀ j, j + 1 < F.top → ∀ x ∈ sitesOfCells {y} (j + 1),
    gaugedLink k Γ j x = balancedLinkAgainst W kW (gaugedChainFields X Γ) j x
  balanced' : ∀ j, j + 1 < F.top → ∀ x ∈ sitesOfCells {y} (j + 1),
    gaugedLink k Γ' j x = balancedLinkAgainst W kW (gaugedChainFields X Γ') j x
  quartic : ∀ j, j < F.top → ∑ b ∈ innerBonds {y} j, bondDiscrepancy W X Γ j b ^ 4 ≤ e ^ 4
  quartic' : ∀ j, j < F.top → ∑ b ∈ innerBonds {y} j, bondDiscrepancy W X Γ' j b ^ 4 ≤ e ^ 4
  correction : normSubOne (topCorrection W kW X k Γ y) ≤ e
  correction' : normSubOne (topCorrection W kW X k Γ' y) ≤ e
def blockTerm (j : ℕ) (y : F.Site (j + 1)) : ℝ :=
  6 * F.blockSide * (blockQuarticRoot (bondDiscrepancy W X Γ j) y + blockQuarticRoot (bondDiscrepancy W X Γ' j) y)
theorem blockTerm_nonneg (j : ℕ) (y : F.Site (j + 1)) : 0 ≤ blockTerm W X Γ Γ' j y := by
  have h1 := blockQuarticRoot_nonneg (bondDiscrepancy W X Γ j) y
  have h2 := blockQuarticRoot_nonneg (bondDiscrepancy W X Γ' j) y
  unfold blockTerm
  positivity
variable {W kW X k Γ Γ'} {y : F.Cell} {e : ℝ}
theorem LevelData.step_le (D : LevelData W kW X k Γ Γ' y e) (j : ℕ) (hj : j < F.top) (y' : F.Site (j + 1))
    (hy' : y' ∈ sitesOfCells {y} (j + 1)) (h : Lattice4) (hh : h ∈ centredCube F.blockSide) :
    levelChange W kW X k Γ Γ' j (refineSite y' + siteOfCoords j h) ≤
      levelChange W kW X k Γ Γ' (j + 1) y' + blockTerm W X Γ Γ' j y' := by
  rw [levelChange_eq _ _ _ _ _ _ hj]
  have hch := gaugeChangeAbove_eq W kW X k Γ Γ' hj y' D.top_one D.top_one' (fun hlt => D.balanced j hlt y' hy')
    (fun hlt => D.balanced' j hlt y' hy')
  have ht : ∀ a ∈ centredCube F.blockSide, ∀ l, a + basisVector l ∈ centredCube F.blockSide →
      normSubOne (gaugedChainFields X Γ j (refineSite y' + siteOfCoords j a) l *
        (W j (refineSite y' + siteOfCoords j a) l)⁻¹) ≤
        blockQuarticRoot (bondDiscrepancy W X Γ j) y' := fun a ha l hl =>
    le_blockQuarticRoot (bondDiscrepancy W X Γ j) (fun _ => normSubOne_nonneg _) y' ha hl
  have ht' : ∀ a ∈ centredCube F.blockSide, ∀ l, a + basisVector l ∈ centredCube F.blockSide →
      normSubOne (gaugedChainFields X Γ' j (refineSite y' + siteOfCoords j a) l *
        (W j (refineSite y' + siteOfCoords j a) l)⁻¹) ≤
        blockQuarticRoot (bondDiscrepancy W X Γ' j) y' := fun a ha l hl =>
    le_blockQuarticRoot (bondDiscrepancy W X Γ' j) (fun _ => normSubOne_nonneg _) y' ha hl
  have key := normSubOne_gaugeChange_le W kW X k Γ Γ' D.odd y' hch
    (fun h hh π => normSubOne_axisPath_discrepancy_le _ _ y' (blockQuarticRoot_nonneg _ _) ht hh π)
    (fun h hh π => normSubOne_axisPath_discrepancy_le _ _ y' (blockQuarticRoot_nonneg _ _) ht' hh π) hh
  refine key.trans (le_of_eq ?_)
  simp only [levelChange, blockTerm]
  ring
theorem LevelData.sum_le (D : LevelData W kW X k Γ Γ' y e) (j : ℕ) (hj : j < F.top) :
    ∑ y' ∈ sitesOfCells {y} (j + 1), blockTerm W X Γ Γ' j y' ^ 4 ≤ (12 * F.blockSide * e) ^ 4 := by
  have root : ∀ Δ : F.SiteGauge, (∑ b ∈ innerBonds {y} j, bondDiscrepancy W X Δ j b ^ 4 ≤ e ^ 4) →
      ∑ y' ∈ sitesOfCells {y} (j + 1), blockQuarticRoot (bondDiscrepancy W X Δ j) y' ^ 4 ≤ e ^ 4 := by
    intro Δ hΔ
    simp only [blockQuarticRoot_pow_four]
    exact (sum_blockQuarticSum_le D.odd hj y _).trans hΔ
  have m := sum_add_pow_le_add_pow (sitesOfCells {y} (j + 1)) (blockQuarticRoot (bondDiscrepancy W X Γ j))
    (blockQuarticRoot (bondDiscrepancy W X Γ' j)) 4 (by norm_num)
    (fun _ _ => blockQuarticRoot_nonneg _ _) (fun _ _ => blockQuarticRoot_nonneg _ _) D.nonneg D.nonneg
    (root Γ (D.quartic j hj)) (root Γ' (D.quartic' j hj))
  calc ∑ y' ∈ sitesOfCells {y} (j + 1), blockTerm W X Γ Γ' j y' ^ 4
      = (6 * (F.blockSide : ℝ)) ^ 4 * ∑ y' ∈ sitesOfCells {y} (j + 1),
          (blockQuarticRoot (bondDiscrepancy W X Γ j) y' + blockQuarticRoot (bondDiscrepancy W X Γ' j) y') ^ 4 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y' _ => ?_
        unfold blockTerm
        ring
    _ ≤ (6 * (F.blockSide : ℝ)) ^ 4 * (e + e) ^ 4 := mul_le_mul_of_nonneg_left m (by positivity)
    _ = (12 * F.blockSide * e) ^ 4 := by ring
theorem LevelData.top_le (D : LevelData W kW X k Γ Γ' y e) (x : F.Cell) (hx : x ∈ sitesOfCells {y} F.top) :
    levelChange W kW X k Γ Γ' F.top x ≤ 12 * F.blockSide * e := by
  obtain rfl := Finset.mem_singleton.1 (mem_sitesOfCells_top.1 hx)
  have hL : (5 : ℝ) ≤ F.blockSide := by exact_mod_cast D.five_le
  have e0 := D.nonneg
  have s : normSubOne (gaugeChangeAbove W kW X k Γ Γ' F.depth x) ≤ e + e := by
    simp only [gaugeChangeAbove, if_true]
    have s1 := normSubOne_mul_le (balancedRotation W kW X k Γ F.depth x) (balancedRotation W kW X k Γ' F.depth x)⁻¹
    rw [normSubOne_inv] at s1
    have t1 : normSubOne (balancedRotation W kW X k Γ F.depth x) ≤ e := D.correction
    have t2 : normSubOne (balancedRotation W kW X k Γ' F.depth x) ≤ e := D.correction'
    linarith
  have : levelChange W kW X k Γ Γ' F.top x = normSubOne (gaugeChangeAbove W kW X k Γ Γ' F.depth x) := rfl
  rw [this]
  nlinarith
theorem LevelData.sum_fourth_le (D : LevelData W kW X k Γ Γ' y e) : ∀ e₀ j, j + e₀ = F.top →
    ∑ x ∈ sitesOfCells {y} j, levelChange W kW X k Γ Γ' j x ^ 4 ≤
      ((3 * (F.blockSide : ℝ) ^ e₀ - 2) * (12 * F.blockSide * e)) ^ 4 := by
  have hL : (5 : ℝ) ≤ F.blockSide := by exact_mod_cast D.five_le
  have e0 := D.nonneg
  have hB : 0 ≤ 12 * (F.blockSide : ℝ) * e := by positivity
  refine sum_fourth_levels_le D.odd (by have := D.five_le; omega) y _ (blockTerm W X Γ Γ') hB
    (levelChange_nonneg W kW X k Γ Γ') (blockTerm_nonneg W X Γ Γ') D.step_le D.sum_le ?_
  have hs : sitesOfCells {y} F.top = ({y} : Finset F.Cell) := by
    ext x
    exact mem_sitesOfCells_top
  rw [hs, Finset.sum_singleton]
  exact pow_le_pow_left₀ (levelChange_nonneg _ _ _ _ _ _ _ _)
    (D.top_le y (mem_sitesOfCells_top.2 (Finset.mem_singleton_self y))) 4
theorem LevelData.scaled_le (D : LevelData W kW X k Γ Γ' y e) (j : ℕ) (hj : j < F.top) :
    ((1 / (F.blockSide : ℝ)) ^ (F.top - j)) ^ 4 * ∑ x ∈ sitesOfCells {y} j, normSubOne (gaugeChange Γ Γ' j x) ^ 4 ≤
      (36 * F.blockSide * e) ^ 4 := by
  have hL : (5 : ℝ) ≤ F.blockSide := by exact_mod_cast D.five_le
  have hL0 : (F.blockSide : ℝ) ≠ 0 := by linarith
  have e0 := D.nonneg
  have l := D.sum_fourth_le (F.top - j) j (by omega)
  rw [Finset.sum_congr rfl fun x _ => by rw [levelChange_eq _ _ _ _ _ _ hj]] at l
  set u : ℝ := (F.blockSide : ℝ) ^ (F.top - j) with hu
  have hu1 : 1 ≤ u := one_le_pow₀ (by linarith)
  have hv : (1 / (F.blockSide : ℝ)) ^ (F.top - j) * u = 1 := by
    rw [hu, ← mul_pow, one_div, inv_mul_cancel₀ hL0, one_pow]
  set v : ℝ := (1 / (F.blockSide : ℝ)) ^ (F.top - j) with hvdef
  calc v ^ 4 * ∑ x ∈ sitesOfCells {y} j, normSubOne (gaugeChange Γ Γ' j x) ^ 4
      ≤ v ^ 4 * ((3 * u - 2) * (12 * F.blockSide * e)) ^ 4 := mul_le_mul_of_nonneg_left l (by positivity)
    _ = (v * ((3 * u - 2) * (12 * F.blockSide * e))) ^ 4 := by ring
    _ ≤ (36 * F.blockSide * e) ^ 4 := by
        have h1 : 0 ≤ v * ((3 * u - 2) * (12 * F.blockSide * e)) := by
          have : 0 ≤ 3 * u - 2 := by linarith
          positivity
        refine pow_le_pow_left₀ h1 ?_ 4
        have : v * ((3 * u - 2) * (12 * F.blockSide * e)) = (3 * (v * u) - 2 * v) * (12 * F.blockSide * e) := by ring
        rw [this, hv]
        nlinarith
end Levels
section Masses
def levelMass (μ : F.Site 0 → ℝ) : (j : ℕ) → F.Site j → ℝ
  | 0 => μ
  | j + 1 => fun y => ∑ h ∈ centredCube F.blockSide, levelMass μ j (refineSite y + siteOfCoords j h)
open Classical in
def baseHull : (j : ℕ) → F.Site j → Finset (F.Site 0)
  | 0 => fun x => {x}
  | j + 1 => fun y => (centredCube F.blockSide).biUnion fun h => baseHull j (refineSite y + siteOfCoords j h)
open Classical in
def baseMass (P : Finset (F.Site 0 × Fin 4 × Fin 4)) (φ : F.Site 0 × Fin 4 × Fin 4 → ℝ) (v : F.Site 0) : ℝ :=
  ∑ p ∈ P.filter (fun p => p.1 = v), φ p
theorem levelMass_nonneg {μ : F.Site 0 → ℝ} (hμ : ∀ x, 0 ≤ μ x) (j : ℕ) : ∀ x : F.Site j, 0 ≤ levelMass μ j x := by
  induction j with
  | zero => exact hμ
  | succ i ih => exact fun x => Finset.sum_nonneg fun h _ => ih _
theorem levelMass_eq_sum_baseHull (hodd : Odd F.blockSide) (μ : F.Site 0 → ℝ) : ∀ i, i ≤ F.top →
    (∀ x x' : F.Site i, x ≠ x' → Disjoint (baseHull i x) (baseHull i x')) ∧
      ∀ x : F.Site i, levelMass μ i x = ∑ v ∈ baseHull i x, μ v := by
  classical
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨fun x x' hne => ?_, fun x => ?_⟩
    · simpa [baseHull] using hne
    · simp [levelMass, baseHull]
  | succ i ih =>
    intro hi
    have hj : i < F.top := by omega
    obtain ⟨d, m⟩ := ih (by omega)
    refine ⟨fun y₁ y₂ hne => ?_, fun y' => ?_⟩
    · rw [Finset.disjoint_left]
      intro v h1 h2
      simp only [baseHull, Finset.mem_biUnion] at h1 h2
      obtain ⟨a, ha, h1⟩ := h1
      obtain ⟨b, hb, h2⟩ := h2
      by_cases e : refineSite y₁ + siteOfCoords i a = refineSite y₂ + siteOfCoords i b
      · exact hne (BlockLines.refineSite_add_injective hj hodd _ _ _ _ ha hb e).1
      · exact Finset.disjoint_left.1 (d _ _ e) h1 h2
    · simp only [levelMass, baseHull]
      rw [Finset.sum_biUnion]
      · exact Finset.sum_congr rfl fun h _ => m _
      · intro a ha b hb hab
        exact d _ _ fun e => hab (BlockLines.refineSite_add_injective hj hodd _ _ _ _ ha hb e).2
theorem zero_mem_centredCube {M : ℕ} (hM : 0 < M) : (0 : Lattice4) ∈ centredCube M := by
  rw [LatticePaths.mem_centredCube_iff]
  intro i
  simp only [Pi.zero_apply]
  omega
theorem siteOfCoords_zero_lattice (j : ℕ) : siteOfCoords (F := F) j (0 : Lattice4) = 0 := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_zero <;> assumption
theorem baseSite_of_base (x : F.Site 0) : baseSite x = x := by apply _root_.YangMills.Construction.CellBumps.baseSite_zero <;> assumption
theorem exists_of_mem_baseHull (hodd : Odd F.blockSide) : ∀ i, i ≤ F.top → ∀ (x : F.Site i), ∀ v ∈ baseHull i x,
    ∃ g ∈ centredCube (F.blockSide ^ i), v = baseSite x + siteOfCoords 0 g := by
  classical
  intro i
  induction i with
  | zero =>
    intro _ x v hv
    have hv' : v = x := by simpa [baseHull] using hv
    refine ⟨0, zero_mem_centredCube (by simp), ?_⟩
    rw [siteOfCoords_zero_lattice, add_zero, baseSite_of_base, hv']
  | succ i ih =>
    intro hi y v hv
    simp only [baseHull, Finset.mem_biUnion] at hv
    obtain ⟨h, hh, hv⟩ := hv
    obtain ⟨g, hg, e⟩ := ih (by omega) _ v hv
    rw [baseSite_add i (by omega), baseSite_refineSite i (by omega)] at e
    refine ⟨fun c => (F.blockSide : ℤ) ^ i * h c + g c, ?_, ?_⟩
    · obtain ⟨k, _, hk2, hk3⟩ := BlockLines.odd_pow_eq_two_mul_add_one hodd 1
      obtain ⟨K, _, hK2, hK3⟩ := BlockLines.odd_pow_eq_two_mul_add_one hodd i
      obtain ⟨M, _, hM2, hM3⟩ := BlockLines.odd_pow_eq_two_mul_add_one hodd (i + 1)
      rw [pow_one] at hk2 hk3
      rw [LatticePaths.mem_centredCube_iff, hk2] at hh
      rw [LatticePaths.mem_centredCube_iff, hK2] at hg
      rw [LatticePaths.mem_centredCube_iff, hM2]
      have hrel : (M : ℤ) = (F.blockSide : ℤ) ^ i * k + K := by
        have e1 : 2 * (M : ℤ) + 1 = (F.blockSide : ℤ) ^ i * (2 * k + 1) := by
          rw [← hM3, ← hk3]
          exact pow_succ _ _
        have : 2 * (M : ℤ) = 2 * ((F.blockSide : ℤ) ^ i * k + K) := by
          linear_combination e1 + hK3
        omega
      have hp : (0 : ℤ) ≤ (F.blockSide : ℤ) ^ i := by positivity
      intro c
      have a1 := hh c
      have a2 := hg c
      rw [hrel]
      constructor
      · nlinarith [a1.1, a2.1]
      · nlinarith [a1.2, a2.2]
    · rw [e, add_assoc, ← siteOfCoords_add]
      rfl
theorem baseDistance_add_le (hodd : Odd F.blockSide) {i : ℕ} {g : Lattice4} (hg : g ∈ centredCube (F.blockSide ^ i))
    (p : F.Site 0) :
    (baseDistance (p + siteOfCoords 0 g : F.Site 0) p : ℝ) ≤ (F.blockSide : ℝ) ^ i := by
  have hb : baseDistance (p + siteOfCoords 0 g : F.Site 0) p ≤ F.blockSide ^ i := by
    unfold baseDistance
    rw [baseSite_of_base, add_sub_cancel_left]
    refine Finset.sup_le fun c _ => ?_
    refine (PatchPoints.natAbs_valMinAbs_intCast_le _ (g c)).trans ?_
    have a := ((LatticePaths.mem_centredCube_iff _ g).1 hg) c
    have hp : 0 < F.blockSide ^ i := pow_pos hodd.pos i
    omega
  exact_mod_cast hb
open Classical in
theorem levelMass_le_local (hodd : Odd F.blockSide) (S : Finset F.Cell) (P : Finset (F.Site 0 × Fin 4 × Fin 4))
    (φ : F.Site 0 × Fin 4 × Fin 4 → ℝ) (hφ : ∀ p, 0 ≤ φ p) (hP : P ⊆ innerPlaquettes S 0) {i : ℕ} (hi : i ≤ F.top)
    (x : F.Site i) :
    levelMass (baseMass P φ) i x ≤
      ∑ q ∈ (innerPlaquettes S 0).filter
        (fun q => (baseDistance q.1 (baseSite x) : ℝ) ≤ (F.blockSide : ℝ) ^ i), φ q := by
  rw [(levelMass_eq_sum_baseHull hodd _ i hi).2 x]
  have e : ∑ v ∈ baseHull i x, baseMass P φ v = ∑ p ∈ P.filter (fun p => p.1 ∈ baseHull i x), φ p := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := P.filter (fun p => p.1 ∈ baseHull i x)) (t := baseHull i x)
      (g := Prod.fst) (fun p hp => (Finset.mem_filter.1 hp).2)]
    refine Finset.sum_congr rfl fun v hv => ?_
    unfold baseMass
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by rw [h2]; exact hv⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩
  rw [e]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hφ _
  intro p hp
  have hp' := Finset.mem_filter.1 hp
  refine Finset.mem_filter.2 ⟨hP hp'.1, ?_⟩
  obtain ⟨g, hg, e⟩ := exists_of_mem_baseHull hodd i hi x _ hp'.2
  rw [e]
  exact baseDistance_add_le hodd hg _
end Masses
section Sizes
variable {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain} {k Γ Γ' : F.SiteGauge} {y : F.Cell} {e : ℝ}
theorem geom_sum_le_inv_one_sub {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i ≤ 1 / (1 - r) := by
  have key : (1 - r) * ∑ i ∈ Finset.range n, r ^ i = 1 - r ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring
  rw [le_div_iff₀ (by linarith)]
  have := pow_nonneg h0 n
  nlinarith
open Classical in
theorem LevelData.curvature_le (D : LevelData W kW X k Γ Γ' y e) (P : Finset (F.Site 0 × Fin 4 × Fin 4))
    (φ : F.Site 0 × Fin 4 × Fin 4 → ℝ) (hφ : ∀ p, 0 ≤ φ p) (hP : ∀ p ∈ P, p.1 ∈ sitesOfCells {y} 0) {Dc ρ : ℝ}
    (hDc : 0 ≤ Dc) (hρ : 0 ≤ ρ)
    (hsup : ∀ e₀ j, j + 1 + e₀ = F.top → ∀ y' ∈ sitesOfCells {y} (j + 1),
      levelMass (baseMass P φ) (j + 1) y' ≤ Dc ^ 2 * (ρ ^ e₀) ^ 4) :
    ∑ p ∈ P, normSubOne (gaugeChange Γ Γ' 0 p.1) ^ 2 * φ p ≤
      (Dc * (12 * F.blockSide * e) * (1 + ∑ i ∈ Finset.range F.top, ρ ^ i)) ^ 2 := by
  have hL : (5 : ℝ) ≤ F.blockSide := by exact_mod_cast D.five_le
  have e0 := D.nonneg
  have hB : 0 ≤ 12 * (F.blockSide : ℝ) * e := by positivity
  have hs : sitesOfCells {y} F.top = ({y} : Finset F.Cell) := by
    ext x
    exact mem_sitesOfCells_top
  have hμ : ∀ x, 0 ≤ baseMass P φ x := fun x => Finset.sum_nonneg fun _ _ => hφ _
  have htot : ∑ x ∈ sitesOfCells {y} F.top, levelMass (baseMass P φ) F.top x ≤ Dc ^ 2 := by
    rw [hs, Finset.sum_singleton]
    have := hsup 0 F.depth rfl y (mem_sitesOfCells_top.2 (Finset.mem_singleton_self y))
    simpa using this
  have key := sum_weighted_sq_levels_le D.odd y (levelChange W kW X k Γ Γ') (blockTerm W X Γ Γ')
    (levelMass (baseMass P φ)) hB hDc hρ (levelChange_nonneg W kW X k Γ Γ') (blockTerm_nonneg W X Γ Γ')
    (levelMass_nonneg hμ) D.step_le D.sum_le D.top_le (fun _ _ _ _ => rfl) hsup htot F.top 0 (by omega)
  refine le_trans (le_of_eq ?_) key
  rw [← Finset.sum_fiberwise_of_maps_to hP]
  refine Finset.sum_congr rfl fun x _ => ?_
  show _ = baseMass P φ x * normSubOne (gaugeChange Γ Γ' 0 x) ^ 2
  unfold baseMass
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [(Finset.mem_filter.1 hp).2]
  ring
theorem LevelData.misfit_le (D : LevelData W kW X k Γ Γ' y e) (Qs : (j : ℕ) → Finset (F.Site (j + 1) × Fin 4))
    (hQ : ∀ j, j < F.top → ∀ c ∈ Qs j, c.1 ∈ sitesOfCells {y} (j + 1)) (m : (j : ℕ) → F.Site (j + 1) × Fin 4 → ℝ)
    {A : ℝ} (hA : 0 ≤ A)
    (hm : ∀ j, j < F.top → ∑ c ∈ Qs j, m j c ^ 4 ≤ (A * (4 / (F.blockSide : ℝ) ^ 2) ^ (F.top - 1 - j)) ^ 4) :
    ∑ j ∈ Finset.range F.top,
        Real.sqrt (∑ c ∈ Qs j, (normSubOne (gaugeChangeAbove W kW X k Γ Γ' j c.1) * m j c) ^ 2) ≤
      360 * F.blockSide * e * A := by
  classical
  have hL : (5 : ℝ) ≤ F.blockSide := by exact_mod_cast D.five_le
  have hL0 : (F.blockSide : ℝ) ≠ 0 := by linarith
  have e0 := D.nonneg
  set B : ℝ := 12 * (F.blockSide : ℝ) * e with hB
  have hB0 : 0 ≤ B := by positivity
  have term : ∀ j ∈ Finset.range F.top,
      Real.sqrt (∑ c ∈ Qs j, (normSubOne (gaugeChangeAbove W kW X k Γ Γ' j c.1) * m j c) ^ 2) ≤
        6 * B * A * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j) := by
    intro j hj'
    have hj : j < F.top := Finset.mem_range.1 hj'
    set e₁ := F.top - 1 - j with he₁
    have lvl := D.sum_fourth_le e₁ (j + 1) (by omega)
    set u : ℝ := (F.blockSide : ℝ) ^ e₁ with hu
    have hu1 : 1 ≤ u := one_le_pow₀ (by linarith)
    have h1 : ∑ c ∈ Qs j, normSubOne (gaugeChangeAbove W kW X k Γ Γ' j c.1) ^ 4 ≤ (6 * u * B) ^ 4 := by
      calc ∑ c ∈ Qs j, normSubOne (gaugeChangeAbove W kW X k Γ Γ' j c.1) ^ 4
          ≤ ∑ c ∈ sitesOfCells {y} (j + 1) ×ˢ (Finset.univ : Finset (Fin 4)),
              levelChange W kW X k Γ Γ' (j + 1) c.1 ^ 4 := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
            intro c hc
            exact Finset.mem_product.2 ⟨hQ j hj c hc, Finset.mem_univ _⟩
        _ = 4 * ∑ x ∈ sitesOfCells {y} (j + 1), levelChange W kW X k Γ Γ' (j + 1) x ^ 4 := by
            rw [Finset.sum_product, Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            simp
        _ ≤ 4 * ((3 * u - 2) * B) ^ 4 := mul_le_mul_of_nonneg_left lvl (by norm_num)
        _ ≤ (6 * u * B) ^ 4 := by
            have a0 : 0 ≤ (3 * u - 2) * B := mul_nonneg (by linarith) hB0
            have a1 : (3 * u - 2) * B ≤ 3 * u * B := mul_le_mul_of_nonneg_right (by linarith) hB0
            have a2 := pow_le_pow_left₀ a0 a1 4
            have a3 : 0 ≤ (3 * u * B) ^ 4 := by positivity
            have a4 : (6 * u * B) ^ 4 = 16 * (3 * u * B) ^ 4 := by ring
            rw [a4]
            linarith
    have h2 := sum_mul_sq_le_of_fourth (Qs j) (fun c => normSubOne (gaugeChangeAbove W kW X k Γ Γ' j c.1)) (m j)
      h1 (hm j hj)
    have hprod : 6 * u * B * (A * (4 / (F.blockSide : ℝ) ^ 2) ^ e₁) = 6 * B * A * (4 / (F.blockSide : ℝ)) ^ e₁ := by
      have : u * (4 / (F.blockSide : ℝ) ^ 2) ^ e₁ = (4 / (F.blockSide : ℝ)) ^ e₁ := by
        rw [hu, ← mul_pow]
        congr 1
        field_simp
      calc 6 * u * B * (A * (4 / (F.blockSide : ℝ) ^ 2) ^ e₁) =
          6 * B * A * (u * (4 / (F.blockSide : ℝ) ^ 2) ^ e₁) := by ring
        _ = _ := by rw [this]
    rw [hprod] at h2
    calc Real.sqrt (∑ c ∈ Qs j, (normSubOne (gaugeChangeAbove W kW X k Γ Γ' j c.1) * m j c) ^ 2)
        ≤ Real.sqrt ((6 * B * A * (4 / (F.blockSide : ℝ)) ^ e₁) ^ 2) := Real.sqrt_le_sqrt h2
      _ = 6 * B * A * (4 / (F.blockSide : ℝ)) ^ e₁ := Real.sqrt_sq (by positivity)
  have hr0 : 0 ≤ 4 / (F.blockSide : ℝ) := by positivity
  have hr1 : 4 / (F.blockSide : ℝ) ≤ 4 / 5 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hg := geom_sum_le_inv_one_sub hr0 (by linarith) F.top
  have hg5 : 1 / (1 - 4 / (F.blockSide : ℝ)) ≤ 5 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  calc ∑ j ∈ Finset.range F.top,
        Real.sqrt (∑ c ∈ Qs j, (normSubOne (gaugeChangeAbove W kW X k Γ Γ' j c.1) * m j c) ^ 2)
      ≤ ∑ j ∈ Finset.range F.top, 6 * B * A * (4 / (F.blockSide : ℝ)) ^ (F.top - 1 - j) := Finset.sum_le_sum term
    _ = 6 * B * A * ∑ j ∈ Finset.range F.top, (4 / (F.blockSide : ℝ)) ^ j := by
        rw [← Finset.mul_sum, Finset.sum_range_reflect (fun i => (4 / (F.blockSide : ℝ)) ^ i) F.top]
    _ ≤ 6 * B * A * 5 := mul_le_mul_of_nonneg_left (hg.trans hg5) (by positivity)
    _ = 360 * F.blockSide * e * A := by
        rw [hB]
        ring
end Sizes
section Geometry
variable {S : Finset F.Cell} {z : F.Cell}
theorem baseSite_mem_patchBaseSites (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {y : F.Cell} (hy : baseSite y ∈ patchBaseSites S z) {j : ℕ} (hj : j ≤ F.top) {x : F.Site j}
    (hx : x ∈ sitesOfCells {y} j) :
    baseSite x ∈ patchBaseSites S z := by
  have hyy : y ∈ sitesOfCells {y} F.top := mem_sitesOfCells_top.2 (Finset.mem_singleton_self y)
  have z1 : (0 : Lattice4) ∈ centredCube (F.blockSide ^ F.top) := zero_mem_centredCube (pow_pos hodd.pos _)
  have z2 : (0 : Lattice4) ∈ centredCube (F.blockSide ^ j) := zero_mem_centredCube (pow_pos hodd.pos _)
  obtain ⟨y₁, hy₁, h₁, hh₁, e₁⟩ := PatchLocality.exists_cell_of_mem_sitesOfCells (S := {y}) hodd le_rfl hyy z1
  obtain ⟨y₂, hy₂, h₂, hh₂, e₂⟩ := PatchLocality.exists_cell_of_mem_sitesOfCells (S := {y}) hodd hj hx z2
  have a1 := Finset.mem_singleton.1 hy₁
  have a2 := Finset.mem_singleton.1 hy₂
  rw [a1] at e₁
  rw [a2] at e₂
  rw [siteOfCoords_zero_lattice, add_zero] at e₁ e₂
  rw [e₁] at hy
  rw [e₂]
  exact PatchLocality.mem_patchBaseSites_of_same_cell hamb hodd he hh₁ hh₂ hy
variable {a C : ℝ} {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain} {k Γ Γ' : F.SiteGauge}
theorem sum_bondDiscrepancy_le (hp : IsPinnedGauge a C S z W kW X k Γ) {j : ℕ} (hj : j < F.top)
    (Q : Finset (F.Site j × Fin 4))
    (hQ : ∀ b ∈ Q, b ∈ innerBonds S j ∧ baseSite b.1 ∈ patchBaseSites S z ∧
      baseSite (b.1 + unitStep j b.2) ∈ patchBaseSites S z) :
    ∑ b ∈ Q, bondDiscrepancy W X Γ j b ^ 4 ≤ (C * Real.sqrt (relativeEnergy a S z W kW X k Γ)) ^ 4 := by
  classical
  refine le_trans ?_ (hp.2.2.1 j hj)
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => (hQ b hb).1) ?_)
  · refine Finset.sum_congr rfl fun b hb => ?_
    rw [if_pos (hQ b hb).2]
    rfl
  · intro b _ _
    split_ifs <;> positivity
theorem relativeEnergy_nonneg (ha : 0 < a) (S : Finset F.Cell) (z : F.Cell) (W : F.FieldChain) (kW : F.SiteGauge)
    (X : F.FieldChain) (k Γ : F.SiteGauge) : 0 ≤ relativeEnergy a S z W kW X k Γ :=
  add_nonneg (Finset.sum_nonneg fun _ _ => by positivity)
    (mul_nonneg ha.le (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity))
theorem normSubOne_covariantDiff_le (W : F.FieldChain) (X : F.FieldChain) (Γ Γ' : F.SiteGauge) (j : ℕ)
    (b : F.Site j × Fin 4) :
    normSubOne (gaugeChange Γ Γ' j b.1 * W j b.1 b.2 * (gaugeChange Γ Γ' j (b.1 + unitStep j b.2))⁻¹ *
      (W j b.1 b.2)⁻¹) ≤ bondDiscrepancy W X Γ j b + bondDiscrepancy W X Γ' j b := by
  set g := gaugedChainFields X Γ j b.1 b.2 * (W j b.1 b.2)⁻¹ with hg
  set g' := gaugedChainFields X Γ' j b.1 b.2 * (W j b.1 b.2)⁻¹ with hg'
  have id : gaugeChange Γ Γ' j b.1 * W j b.1 b.2 * (gaugeChange Γ Γ' j (b.1 + unitStep j b.2))⁻¹ *
      (W j b.1 b.2)⁻¹ = gaugeChange Γ Γ' j b.1 * g'⁻¹ * (gaugeChange Γ Γ' j b.1)⁻¹ * g := by
    rw [hg, hg']
    simp only [gaugedChainFields, gaugeTransform, gaugeChange]
    group
  rw [id]
  have s := normSubOne_mul_le (gaugeChange Γ Γ' j b.1 * g'⁻¹ * (gaugeChange Γ Γ' j b.1)⁻¹) g
  rw [normSubOne_conj, normSubOne_inv] at s
  have e1 : bondDiscrepancy W X Γ j b = normSubOne g := rfl
  have e2 : bondDiscrepancy W X Γ' j b = normSubOne g' := rfl
  rw [e1, e2]
  linarith
theorem pow_rpow_two_mul_eq {b θ : ℝ} (hb : 0 ≤ b) (e : ℕ) : (b ^ e) ^ (2 * θ) = ((b ^ (θ / 2)) ^ e) ^ 4 := by
  rw [← Real.rpow_natCast b e, ← Real.rpow_mul hb, ← Real.rpow_natCast (b ^ (θ / 2)) e, ← Real.rpow_mul hb,
    ← Real.rpow_natCast (b ^ (θ / 2 * (e : ℝ))) 4, ← Real.rpow_mul hb]
  congr 1
  push_cast
  ring
end Geometry
def curvatureRatio (L : ℕ) (θ : ℝ) : ℝ := (1 / (L : ℝ)) ^ (θ / 2)
def gaugeChangeConstant (L : ℕ) (C₁ C θ : ℝ) : ℝ :=
  2 * C + 36 * L * C + 12 * L * C * C₁ * (1 + 1 / (1 - curvatureRatio L θ)) + 360 * L * C * C₁
theorem curvatureRatio_nonneg (L : ℕ) (θ : ℝ) : 0 ≤ curvatureRatio L θ := by
  unfold curvatureRatio
  positivity
theorem curvatureRatio_lt_one {L : ℕ} (hL : 5 ≤ L) {θ : ℝ} (hθ : 0 < θ) : curvatureRatio L θ < 1 := by
  have h5 : (5 : ℝ) ≤ L := by exact_mod_cast hL
  have h1 : 1 / (L : ℝ) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  exact Real.rpow_lt_one (by positivity) h1 (by linarith)
theorem gaugeChangeConstant_bounds {L : ℕ} (hL : 5 ≤ L) {C₁ C θ : ℝ} (hC₁ : 0 < C₁) (hC : 0 < C) (hθ : 0 < θ) :
    0 < gaugeChangeConstant L C₁ C θ ∧ 2 * C ≤ gaugeChangeConstant L C₁ C θ ∧
      36 * L * C ≤ gaugeChangeConstant L C₁ C θ ∧
      12 * L * C * C₁ * (1 + 1 / (1 - curvatureRatio L θ)) ≤ gaugeChangeConstant L C₁ C θ ∧
      360 * L * C * C₁ ≤ gaugeChangeConstant L C₁ C θ := by
  have hr := curvatureRatio_lt_one hL hθ
  have t2 : 0 < 36 * (L : ℝ) * C := by positivity
  have t3 : 0 < 12 * (L : ℝ) * C * C₁ * (1 + 1 / (1 - curvatureRatio L θ)) := by positivity
  have t4 : 0 < 360 * (L : ℝ) * C * C₁ := by positivity
  unfold gaugeChangeConstant
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
theorem gaugeChangeBounds_of_pinned {a θ C₁ C : ℝ} (hθ : 0 < θ) (hC₁ : 0 < C₁) (hC : 0 < C) {m : ℕ}
    {S : Finset F.Cell} (hodd : Odd F.blockSide) (h5 : 5 ≤ F.blockSide) (hamb : IsAdmissibleAmbient F)
    (hm : 1024 ≤ m) (hreg : IsOrthantRegular S m)
    {s : ℝ} (hs : 0 < s) {W : F.FieldChain} {kW : F.SiteGauge} {X : F.FieldChain} {k Γ Γ' : F.SiteGauge}
    {z z' y : F.Cell} (hy : y ∈ S) (hyz : baseSite y ∈ patchBaseSites S z) (hyz' : baseSite y ∈ patchBaseSites S z')
    (hp : IsPinnedGauge a C S z W kW X k Γ) (hp' : IsPinnedGauge a C S z' W kW X k Γ') {d : ℝ} (hd0 : 0 ≤ d)
    (hle : C * Real.sqrt (relativeEnergy a S z W kW X k Γ) ≤ C * d)
    (hle' : C * Real.sqrt (relativeEnergy a S z' W kW X k Γ') ≤ C * d)
    (hcurv : ∀ (p : F.Site 0) (r : ℝ), 1 ≤ r → r ≤ (F.blockSide : ℝ) ^ F.top →
      ∑ q ∈ (innerPlaquettes S 0).filter (fun q => (baseDistance q.1 p : ℝ) ≤ r),
        ‖((plaquetteHolonomy (W 0) q : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 ≤
          (C₁ * s) ^ 2 * (r / (F.blockSide : ℝ) ^ F.top) ^ (2 * θ))
    (hmis : ∀ j, j < F.top → ∑ c ∈ bondsOver S {y} (j + 1),
      normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) ^ 4 ≤
        (C₁ * s * (4 / (F.blockSide : ℝ) ^ 2) ^ (F.top - 1 - j)) ^ 4) :
    GaugeChangeBounds (gaugeChangeConstant F.blockSide C₁ C θ) s S z z' y W kW X k Γ Γ' d := by
  classical
  have hCR : 0 ≤ C * Real.sqrt (relativeEnergy a S z W kW X k Γ) := mul_nonneg hC.le (Real.sqrt_nonneg _)
  have hCR' : 0 ≤ C * Real.sqrt (relativeEnergy a S z' W kW X k Γ') := mul_nonneg hC.le (Real.sqrt_nonneg _)
  have he := (closedOrthant_spec (z := z) hreg (by omega)).1
  have he' := (closedOrthant_spec (z := z') hreg (by omega)).1
  have hsub : ({y} : Finset F.Cell) ⊆ S := Finset.singleton_subset_iff.2 hy
  have cellBonds : ∀ (w : F.Cell), baseSite y ∈ patchBaseSites S w →
      (∀ i, closedOrthant S w i = 1 ∨ closedOrthant S w i = -1) →
      ∀ j, j < F.top → ∀ b ∈ innerBonds {y} j, b ∈ innerBonds S j ∧ baseSite b.1 ∈ patchBaseSites S w ∧
        baseSite (b.1 + unitStep j b.2) ∈ patchBaseSites S w := by
    intro w hw hs' j hj b hb
    have hb' := Finset.mem_filter.1 hb
    exact ⟨BlockLines.innerBonds_mono hsub j hb,
      baseSite_mem_patchBaseSites hamb hodd hs' hw hj.le (Finset.mem_product.1 hb'.1).1,
      baseSite_mem_patchBaseSites hamb hodd hs' hw hj.le hb'.2⟩
  have D : LevelData W kW X k Γ Γ' y (C * d) :=
    { odd := hodd
      five_le := h5
      nonneg := by positivity
      top_one := hp.1
      top_one' := hp'.1
      balanced := fun j hlt x hx =>
        hp.2.1 j hlt x (baseSite_mem_patchBaseSites hamb hodd he hyz (by omega) hx)
      balanced' := fun j hlt x hx =>
        hp'.2.1 j hlt x (baseSite_mem_patchBaseSites hamb hodd he' hyz' (by omega) hx)
      quartic := fun j hj =>
        (sum_bondDiscrepancy_le hp hj _ (cellBonds z hyz he j hj)).trans (pow_le_pow_left₀ hCR hle 4)
      quartic' := fun j hj =>
        (sum_bondDiscrepancy_le hp' hj _ (cellBonds z' hyz' he' j hj)).trans (pow_le_pow_left₀ hCR' hle' 4)
      correction := (hp.2.2.2 y hyz).trans hle
      correction' := (hp'.2.2.2 y hyz').trans hle' }
  obtain ⟨_, c1, c2, c3, c4⟩ := gaugeChangeConstant_bounds h5 hC₁ hC hθ
  generalize gaugeChangeConstant F.blockSide C₁ C θ = C₂ at c1 c2 c3 c4 ⊢
  have hL : (5 : ℝ) ≤ F.blockSide := by exact_mod_cast h5
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    have patchOf' : ∀ (w w' : F.Cell), ∀ b ∈ (patchInnerBonds S w j ∩ patchInnerBonds S w' j).filter
        (fun b => enclosingCell b.1 = y), b ∈ innerBonds S j ∧ baseSite b.1 ∈ patchBaseSites S w ∧
          baseSite (b.1 + unitStep j b.2) ∈ patchBaseSites S w := by
      intro w w' b hb
      have h1 := Finset.mem_filter.1 (Finset.mem_inter.1 (Finset.mem_filter.1 hb).1).1
      exact ⟨h1.1, h1.2.1, h1.2.2⟩
    have patchOf'' : ∀ b ∈ (patchInnerBonds S z j ∩ patchInnerBonds S z' j).filter (fun b => enclosingCell b.1 = y),
        b ∈ innerBonds S j ∧ baseSite b.1 ∈ patchBaseSites S z' ∧
          baseSite (b.1 + unitStep j b.2) ∈ patchBaseSites S z' := by
      intro b hb
      have h1 := Finset.mem_filter.1 (Finset.mem_inter.1 (Finset.mem_filter.1 hb).1).2
      exact ⟨h1.1, h1.2.1, h1.2.2⟩
    have h1 := (sum_bondDiscrepancy_le hp hj _ (patchOf' z z')).trans (pow_le_pow_left₀ hCR hle 4)
    have h2 := (sum_bondDiscrepancy_le hp' hj _ patchOf'').trans (pow_le_pow_left₀ hCR' hle' 4)
    have m' := sum_add_pow_le_add_pow _ (bondDiscrepancy W X Γ j) (bondDiscrepancy W X Γ' j) 4 (by norm_num)
      (fun _ _ => normSubOne_nonneg _) (fun _ _ => normSubOne_nonneg _) (by positivity : 0 ≤ C * d)
      (by positivity : 0 ≤ C * d) h1 h2
    refine (Finset.sum_le_sum fun b _ => pow_le_pow_left₀ (normSubOne_nonneg _)
      (normSubOne_covariantDiff_le W X Γ Γ' j b) 4).trans (m'.trans (pow_le_pow_left₀ (by positivity) ?_ 4))
    nlinarith
  · intro j hj
    refine (D.scaled_le j hj).trans (pow_le_pow_left₀ (by positivity) ?_ 4)
    have : 36 * (F.blockSide : ℝ) * (C * d) = 36 * F.blockSide * C * d := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right c2 hd0
  · set φ : F.Site 0 × Fin 4 × Fin 4 → ℝ :=
      fun p => ‖((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 with hφ
    set P := (patchPlaquettes S z ∩ patchPlaquettes S z').filter (fun p => enclosingCell p.1 = y) with hPdef
    have hPS : P ⊆ innerPlaquettes S 0 := fun p hp =>
      (Finset.mem_filter.1 (Finset.mem_inter.1 (Finset.mem_filter.1 hp).1).1).1
    have hPy : ∀ p ∈ P, p.1 ∈ sitesOfCells {y} 0 := by
      intro p hp
      have h1 := Finset.mem_filter.1 (hPS hp)
      have h2 := (Finset.mem_filter.1 hp).2
      exact BlockLines.mem_sitesOfCells_of_enclosingCell_mem hodd (Finset.mem_product.1 h1.1).1
        (by rw [h2]; exact Finset.mem_singleton_self y)
    have hsup : ∀ e₀ j, j + 1 + e₀ = F.top → ∀ y' ∈ sitesOfCells {y} (j + 1),
        levelMass (baseMass P φ) (j + 1) y' ≤ (C₁ * s) ^ 2 * ((curvatureRatio F.blockSide θ) ^ e₀) ^ 4 := by
      intro e₀ j hje y' _
      have a1 := levelMass_le_local hodd S P φ (fun _ => by positivity) hPS (i := j + 1) (by omega) y'
      have r1 : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ (j + 1) := one_le_pow₀ (by linarith)
      have r2 : (F.blockSide : ℝ) ^ (j + 1) ≤ (F.blockSide : ℝ) ^ F.top := pow_le_pow_right₀ (by linarith) (by omega)
      have a2 := hcurv (baseSite y') ((F.blockSide : ℝ) ^ (j + 1)) r1 r2
      have a3 : ((F.blockSide : ℝ) ^ (j + 1) / (F.blockSide : ℝ) ^ F.top) = (1 / (F.blockSide : ℝ)) ^ e₀ := by
        have hn : (F.blockSide : ℝ) ^ F.top = (F.blockSide : ℝ) ^ (j + 1) * (F.blockSide : ℝ) ^ e₀ := by
          rw [← pow_add, hje]
        rw [hn, one_div, inv_pow]
        field_simp
      rw [a3, pow_rpow_two_mul_eq (by positivity)] at a2
      exact a1.trans a2
    have key := D.curvature_le P φ (fun _ => by positivity) hPy (by positivity : 0 ≤ C₁ * s)
      (curvatureRatio_nonneg F.blockSide θ) hsup
    have e1 : ∑ p ∈ P, (normSubOne (gaugeChange Γ Γ' 0 p.1) *
        ‖((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).im‖) ^ 2 =
        ∑ p ∈ P, normSubOne (gaugeChange Γ Γ' 0 p.1) ^ 2 * φ p :=
      Finset.sum_congr rfl fun p _ => by rw [mul_pow]
    refine e1.trans_le (key.trans (pow_le_pow_left₀ (by
      have : 0 ≤ ∑ i ∈ Finset.range F.top, (curvatureRatio F.blockSide θ) ^ i :=
        Finset.sum_nonneg fun i _ => pow_nonneg (curvatureRatio_nonneg F.blockSide θ) i
      positivity) ?_ 2))
    have hg := geom_sum_le_inv_one_sub (curvatureRatio_nonneg F.blockSide θ) (curvatureRatio_lt_one h5 hθ) F.top
    have hsd : 0 ≤ s * d := by positivity
    calc C₁ * s * (12 * F.blockSide * (C * d)) * (1 + ∑ i ∈ Finset.range F.top, (curvatureRatio F.blockSide θ) ^ i)
        ≤ C₁ * s * (12 * F.blockSide * (C * d)) * (1 + 1 / (1 - curvatureRatio F.blockSide θ)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (12 * F.blockSide * C * C₁ * (1 + 1 / (1 - curvatureRatio F.blockSide θ))) * (s * d) := by ring
      _ ≤ C₂ * (s * d) := mul_le_mul_of_nonneg_right c3 hsd
      _ = C₂ * s * d := by ring
  · have hQ : ∀ j, j < F.top → ∀ c ∈ (patchFitBonds S z j ∩ patchFitBonds S z' j).filter
        (fun c => enclosingCell c.1 = y), c.1 ∈ sitesOfCells {y} (j + 1) := by
      intro j _ c hc
      have h1 := Finset.mem_filter.1 (Finset.mem_inter.1 (Finset.mem_filter.1 hc).1).1
      have h2 := (Finset.mem_filter.1 hc).2
      exact BlockLines.mem_sitesOfCells_of_enclosingCell_mem hodd (Finset.mem_product.1 (Finset.mem_filter.1 h1.1).1).1
        (by rw [h2]; exact Finset.mem_singleton_self y)
    have key := D.misfit_le
      (fun j => (patchFitBonds S z j ∩ patchFitBonds S z' j).filter (fun c => enclosingCell c.1 = y)) hQ
      (fun j c => normSubOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)) (by positivity : 0 ≤ C₁ * s) (by
        intro j hj
        refine le_trans ?_ (hmis j hj)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro c hc
        have h1 := Finset.mem_filter.1 (Finset.mem_inter.1 (Finset.mem_filter.1 hc).1).1
        have h2 := (Finset.mem_filter.1 hc).2
        simp only [bondsOver]
        exact Finset.mem_filter.2 ⟨h1.1, by rw [h2]; exact Finset.mem_singleton_self y⟩)
    refine key.trans ?_
    have hsd : 0 ≤ s * d := by positivity
    calc 360 * (F.blockSide : ℝ) * (C * d) * (C₁ * s) = (360 * F.blockSide * C * C₁) * (s * d) := by ring
      _ ≤ C₂ * (s * d) := mul_le_mul_of_nonneg_right c4 hsd
      _ = C₂ * s * d := by ring
theorem gaugeChangeBounds_critical {a θ del Ca C₁ C Cd e0 : ℝ} (ha : 0 < a) (hθ : 0 < θ) (hC₁ : 0 < C₁) (hC : 0 < C)
    {m : ℕ} {S : Finset F.Cell} (hodd : Odd F.blockSide) (h5 : 5 ≤ F.blockSide) (hamb : IsAdmissibleAmbient F)
    (hm : 1024 ≤ m) (hreg : IsOrthantRegular S m)
    {s : ℝ} {V : F.GaugeField F.top} {v : F.Site F.top → Fin 4 → imaginaryQuaternions} (hs : 0 < s) {U : ChainChart F}
    (hU : IsCriticalChainOverTop a θ del Ca C₁ s S V (rotatedField v V) U) {X : F.FieldChain} {k Γ Γ' : F.SiteGauge}
    {z z' y : F.Cell} (hy : y ∈ S) (hyz : baseSite y ∈ patchBaseSites S z) (hyz' : baseSite y ∈ patchBaseSites S z')
    (hp : HasPinnedGaugeAt a C Cd e0 S z (criticalFieldChain S V v U) (criticalGauge S V U) X k Γ)
    (hp' : HasPinnedGaugeAt a C Cd e0 S z' (criticalFieldChain S V v U) (criticalGauge S V U) X k Γ') :
    GaugeChangeBounds (gaugeChangeConstant F.blockSide C₁ C θ) s S z z' y (criticalFieldChain S V v U)
      (criticalGauge S V U) X k Γ Γ'
      (Real.sqrt (relativeEnergy a S z (criticalFieldChain S V v U) (criticalGauge S V U) X k Γ +
        relativeEnergy a S z' (criticalFieldChain S V v U) (criticalGauge S V U) X k Γ')) := by
  have hW0 : criticalFieldChain S V v U 0 = chartField (referenceFieldChain S V) U 0 := by
    unfold criticalFieldChain chartChain
    exact Function.update_of_ne (by simp [BlockFrame.top]) _ _
  refine gaugeChangeBounds_of_pinned hθ hC₁ hC hodd h5 hamb hm hreg hs hy hyz hyz' hp.1 hp'.1 (Real.sqrt_nonneg _)
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (le_add_of_nonneg_right (relativeEnergy_nonneg ha _ _ _ _ _ _ _))) hC.le)
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (le_add_of_nonneg_left (relativeEnergy_nonneg ha _ _ _ _ _ _ _))) hC.le)
    ?_ (fun j hj => (hU.misfits_on_cells j y hj).1)
  intro p r h1 h2
  rw [hW0]
  exact (hU.curvature_and_misfits p r h1 h2).1
theorem gaugeChangeBound : gaugeChangeBoundStatement := by
  intro a θ del Ca ha hθ _ _ _ _
  refine ⟨5, fun L hodd hL C₁ C Cd hC₁ hC _ => ⟨gaugeChangeConstant L C₁ C θ, 1,
    (gaugeChangeConstant_bounds hL hC₁ hC hθ).1, one_pos, fun e0 _ _ => ⟨1, one_pos, ?_⟩⟩⟩
  intro F m S hFL hamb hm hreg s V v hs _ _ _ U hU X k Γ Γ' z z' y _ _ _ hy _ hyz hyz' hp hp'
  subst hFL
  exact gaugeChangeBounds_critical ha hθ hC₁ hC hodd hL hamb hm hreg hs hU hy hyz hyz' hp hp'
end YangMills.Construction.BlockAverages.GaugeChange
end
