import YangMills.Construction.ColdChainAtEveryLevel.DensityUnderAChangeOfFraming
import YangMills.Construction.ColdChainAtEveryLevel.ExcessOverTheCriticalChain
import YangMills.Construction.ColdChainAtEveryLevel.FirstOrderOfTheFramings
import YangMills.Construction.ColdChainAtEveryLevel.PinnedFramingAtAGoodCell
import YangMills.Construction.ColdChainAtEveryLevel.ShareOfTheCriticalChain
import YangMills.Construction.ColdChainAtEveryLevel.SitesOfAPatch
import YangMills.Construction.ColdChainAtEveryLevel.TermsAgainstTheirFirstOrder
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.CriticalChainExcess
section Sums
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
theorem excess_split_le (T : Finset ι) (Sc A B : Finset κ) (P : κ → Finset ι) (x w : ι → ℝ) (chi : κ → ι → ℝ)
    (fo dens err : κ → ι → ℝ) (D : κ → ℝ) (e O Wb Ct : ℝ) (hO : 0 < O)
    (hx : ∀ t ∈ T, 0 ≤ x t) (hw : ∀ t ∈ T, 0 ≤ w t) (hchi : ∀ z t, 0 ≤ chi z t)
    (hchi1 : ∀ z ∈ Sc, ∀ t, chi z t ≤ 1) (hsum : ∀ t ∈ T, ∑ z ∈ Sc, chi z t = 1) (hAS : A ⊆ Sc)
    (hPT : ∀ z ∈ Sc, P z ⊆ T) (hBS : B ⊆ Sc) (hsupp : ∀ z ∈ A, ∀ t ∈ T, chi z t ≠ 0 → t ∈ P z)
    (hbad0 : ∀ y ∈ B, ∀ t ∈ P y, ∀ z ∈ A, chi z t = 0)
    (hcost : ∀ y ∈ B, e ^ 2 ≤ ∑ t ∈ P y, x t)
    (hover : ∀ t ∈ T, ((B.filter fun y => t ∈ P y).card : ℝ) ≤ O)
    (hnear : ∑ t ∈ T.filter (fun t => ∑ z ∈ A, chi z t ≠ 1), w t ≤ Wb * B.card)
    (hterm : ∀ z ∈ A, ∀ t ∈ P z, fo z t + (1 / 32) * dens z t - err z t ≤ x t - w t)
    (herr0 : ∀ z t, 0 ≤ err z t) (herr : ∀ z ∈ A, ∑ t ∈ P z, err z t ≤ Ct * D z) :
    e ^ 2 / O * B.card - Wb * B.card + ∑ z ∈ A, ∑ t ∈ T, chi z t * fo z t +
        (1 / 32) * ∑ z ∈ A, ∑ t ∈ T, chi z t * dens z t - Ct * ∑ z ∈ A, D z ≤ ∑ t ∈ T, (x t - w t) := by
  set c : ι → ℝ := fun t => ∑ z ∈ A, chi z t with hc
  have hc0 : ∀ t, 0 ≤ c t := fun t => Finset.sum_nonneg fun z _ => hchi z t
  have hc1 : ∀ t ∈ T, c t ≤ 1 := by
    intro t ht
    rw [← hsum t ht]
    exact Finset.sum_le_sum_of_subset_of_nonneg hAS fun z _ _ => hchi z t
  have hsplit : ∑ t ∈ T, (x t - w t) = ∑ t ∈ T, (1 - c t) * (x t - w t) +
      ∑ z ∈ A, ∑ t ∈ T, chi z t * (x t - w t) := by
    rw [Finset.sum_comm (s := A), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_mul]
    ring
  have hclear : ∀ z ∈ A, ∑ t ∈ T, chi z t * fo z t + (1 / 32) * ∑ t ∈ T, chi z t * dens z t - Ct * D z ≤
      ∑ t ∈ T, chi z t * (x t - w t) := by
    intro z hz
    have h1 : ∑ t ∈ T, chi z t * err z t ≤ Ct * D z := by
      refine le_trans ?_ (herr z hz)
      have hs : ∑ t ∈ T, chi z t * err z t = ∑ t ∈ P z, chi z t * err z t := by
        symm
        refine Finset.sum_subset (hPT z (hAS hz)) fun t ht hn => ?_
        by_contra hne
        exact hn (hsupp z hz t ht (left_ne_zero_of_mul hne))
      rw [hs]
      refine Finset.sum_le_sum fun t _ => ?_
      have := herr0 z t
      have h2 := hchi1 z (hAS hz) t
      nlinarith [hchi z t]
    have h2 : ∑ t ∈ T, chi z t * fo z t + (1 / 32) * ∑ t ∈ T, chi z t * dens z t - ∑ t ∈ T, chi z t * err z t ≤
        ∑ t ∈ T, chi z t * (x t - w t) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun t ht => ?_
      by_cases h0 : chi z t = 0
      · simp [h0]
      · have h3 := hterm z hz t (hsupp z hz t ht h0)
        have h4 := mul_le_mul_of_nonneg_left h3 (hchi z t)
        nlinarith
    linarith
  have hfirst : e ^ 2 / O * B.card - Wb * B.card ≤ ∑ t ∈ T, (1 - c t) * (x t - w t) := by
    have h1 : ∑ t ∈ T, (1 - c t) * w t ≤ Wb * B.card := by
      refine le_trans ?_ hnear
      have hs : ∑ t ∈ T.filter (fun t => c t ≠ 1), (1 - c t) * w t = ∑ t ∈ T, (1 - c t) * w t := by
        refine Finset.sum_subset (Finset.filter_subset _ _) fun t ht hn => ?_
        have : c t = 1 := by
          by_contra hne
          exact hn (Finset.mem_filter.2 ⟨ht, hne⟩)
        simp [this]
      rw [← hs]
      refine Finset.sum_le_sum fun t ht => ?_
      have ht' := (Finset.mem_filter.1 ht).1
      have := hw t ht'
      nlinarith [hc0 t]
    have h2 : (e ^ 2) * B.card ≤ O * ∑ t ∈ T, (1 - c t) * x t := by
      have a1 : (e ^ 2) * B.card ≤ ∑ y ∈ B, ∑ t ∈ P y, x t := by
        have : ∑ y ∈ B, e ^ 2 ≤ ∑ y ∈ B, ∑ t ∈ P y, x t := Finset.sum_le_sum hcost
        simpa [mul_comm] using this
      have a2 : ∑ y ∈ B, ∑ t ∈ P y, x t = ∑ t ∈ T, ((B.filter fun y => t ∈ P y).card : ℝ) * x t := by
        have s1 : ∀ y ∈ B, ∑ t ∈ P y, x t = ∑ t ∈ T, if t ∈ P y then x t else 0 := by
          intro y hy
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext t
          simp only [Finset.mem_filter]
          exact ⟨fun h => ⟨hPT y (hBS hy) h, h⟩, fun h => h.2⟩
        rw [Finset.sum_congr rfl s1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rw [a2] at a1
      refine a1.trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun t ht => ?_
      by_cases hcard : (B.filter fun y => t ∈ P y).card = 0
      · rw [hcard]
        have : 0 ≤ (1 - c t) * x t := mul_nonneg (by linarith [hc1 t ht]) (hx t ht)
        simp only [Nat.cast_zero, zero_mul]
        positivity
      · obtain ⟨y, hy⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hcard)
        have hy' := Finset.mem_filter.1 hy
        have h0 : c t = 0 := Finset.sum_eq_zero fun z hz => hbad0 y hy'.1 t hy'.2 z hz
        rw [h0, sub_zero, one_mul]
        exact mul_le_mul_of_nonneg_right (hover t ht) (hx t ht)
    have h3 : e ^ 2 / O * B.card ≤ ∑ t ∈ T, (1 - c t) * x t := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hO]
      linarith
    have h4 : ∑ t ∈ T, (1 - c t) * (x t - w t) = ∑ t ∈ T, (1 - c t) * x t - ∑ t ∈ T, (1 - c t) * w t := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    linarith
  have hsecond := Finset.sum_le_sum hclear
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsecond
  linarith
theorem sum_energy_le_of_local (A A0 : Finset κ) (T : Finset ι) (P : κ → Finset ι) (g : ι → ℝ) (D : κ → ℝ)
    (N : κ → Finset κ) (Cq O Nc Bb : ℝ) (hA0 : A0 ⊆ A) (hD0 : ∀ z ∈ A, 0 ≤ D z) (hg : ∀ t ∈ T, 0 ≤ g t)
    (hPT : ∀ z ∈ A0, P z ⊆ T) (hO : ∀ t ∈ T, ((A0.filter fun z => t ∈ P z).card : ℝ) ≤ O)
    (hNA : ∀ z ∈ A0, N z ⊆ A) (hN1 : ∀ z ∈ A0, ((N z).card : ℝ) ≤ Nc)
    (hN2 : ∀ y ∈ A, ((A0.filter fun z => y ∈ N z).card : ℝ) ≤ Nc) (hNc : 0 ≤ Nc) (hCq : 0 ≤ Cq)
    (hz : ∀ z ∈ A0, D z ≤ 3 * ∑ t ∈ P z, g t + Cq * ∑ y ∈ N z, (D z + D y))
    (hout : ∑ z ∈ A \ A0, D z ≤ Bb) :
    ∑ z ∈ A, D z ≤ 3 * (O * ∑ t ∈ T, g t) + 2 * (Cq * (Nc * ∑ z ∈ A, D z)) + Bb := by
  have hsplit : ∑ z ∈ A, D z = ∑ z ∈ A \ A0, D z + ∑ z ∈ A0, D z := (Finset.sum_sdiff hA0).symm
  have h1 : ∑ z ∈ A0, ∑ t ∈ P z, g t ≤ O * ∑ t ∈ T, g t := by
    have s1 : ∀ z ∈ A0, ∑ t ∈ P z, g t = ∑ t ∈ T, if t ∈ P z then g t else 0 := by
      intro z hz'
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext t
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hPT z hz' h, h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl s1, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hO t ht) (hg t ht)
  have hsub : ∑ z ∈ A0, D z ≤ ∑ z ∈ A, D z :=
    Finset.sum_le_sum_of_subset_of_nonneg hA0 fun z hz' _ => hD0 z hz'
  have h2 : ∑ z ∈ A0, ∑ y ∈ N z, D z ≤ Nc * ∑ z ∈ A, D z := by
    have h3 : ∑ z ∈ A0, ∑ y ∈ N z, D z ≤ ∑ z ∈ A0, Nc * D z := by
      refine Finset.sum_le_sum fun z hz' => ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (hN1 z hz') (hD0 z (hA0 hz'))
    rw [← Finset.mul_sum] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left hsub hNc)
  have h3 : ∑ z ∈ A0, ∑ y ∈ N z, D y ≤ Nc * ∑ z ∈ A, D z := by
    have s1 : ∀ z ∈ A0, ∑ y ∈ N z, D y = ∑ y ∈ A, if y ∈ N z then D y else 0 := by
      intro z hz'
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext y
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hNA z hz' h, h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl s1, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun y hy => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hN2 y hy) (hD0 y hy)
  have h4 : ∑ z ∈ A0, D z ≤ 3 * ∑ z ∈ A0, ∑ t ∈ P z, g t +
      Cq * (∑ z ∈ A0, ∑ y ∈ N z, D z + ∑ z ∈ A0, ∑ y ∈ N z, D y) := by
    have := Finset.sum_le_sum hz
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
    simpa only [Finset.sum_add_distrib] using this
  have h5 := mul_le_mul_of_nonneg_left (add_le_add h2 h3) hCq
  linarith
theorem local_density_le (T : Finset ι) (Sc A Nz Yz : Finset κ) (P : κ → Finset ι) (chi dens : κ → ι → ℝ)
    (ee : κ → κ → ι → ℝ) (cell : ι → κ) (D : κ → ℝ) (z : κ) (Cc Yc : ℝ) (hPT : P z ⊆ T)
    (hsum : ∀ t ∈ T, ∑ y ∈ Sc, chi y t = 1) (hAS : A ⊆ Sc) (hNA : Nz ⊆ A) (hchi0 : ∀ y t, 0 ≤ chi y t)
    (hchi1 : ∀ y ∈ A, ∀ t, chi y t ≤ 1) (hee0 : ∀ y c t, 0 ≤ ee y c t)
    (key : ∀ t ∈ P z, ∀ y ∈ Sc, chi y t ≠ 0 → y ∈ Nz ∧ t ∈ P y)
    (hd : ∀ y ∈ Nz, ∀ t ∈ P z ∩ P y, dens z t ≤ 3 * dens y t + ee y (cell t) t)
    (hf : ∀ y ∈ Nz, ∀ c ∈ Yz, ∑ t ∈ (P z ∩ P y).filter (fun t => cell t = c), ee y c t ≤ Cc * (D z + D y))
    (hmaps : ∀ t ∈ P z, cell t ∈ Yz) (hYc : (Yz.card : ℝ) ≤ Yc) (hDn : ∀ y ∈ Nz, 0 ≤ Cc * (D z + D y)) :
    ∑ t ∈ P z, dens z t ≤ 3 * ∑ t ∈ P z, ∑ y ∈ A, chi y t * dens y t +
      (Yc * Cc) * ∑ y ∈ Nz, (D z + D y) := by
  have hpt : ∀ t ∈ P z, dens z t ≤ 3 * ∑ y ∈ A, chi y t * dens y t + ∑ y ∈ Nz,
      (if t ∈ P y then ee y (cell t) t else 0) := by
    intro t ht
    have sum1 : ∑ y ∈ A, chi y t = 1 := by
      rw [← hsum t (hPT ht)]
      refine Finset.sum_subset hAS fun y hy hyA => ?_
      by_contra hne
      exact hyA (hNA (key t ht y hy hne).1)
    have per : ∀ y ∈ A, chi y t * dens z t ≤ 3 * (chi y t * dens y t) + if y ∈ Nz then
        (if t ∈ P y then ee y (cell t) t else 0) else 0 := by
      intro y hy
      by_cases h0 : chi y t = 0
      · rw [h0, zero_mul, zero_mul, mul_zero, zero_add]
        split_ifs
        · exact hee0 _ _ _
        · exact le_rfl
        · exact le_rfl
      · obtain ⟨k1, k3⟩ := key t ht y (hAS hy) h0
        rw [if_pos k1, if_pos k3]
        have h1 := hd y k1 t (Finset.mem_inter.2 ⟨ht, k3⟩)
        have h2 := mul_le_mul_of_nonneg_left h1 (hchi0 y t)
        have h3 := hee0 y (cell t) t
        have h4 := hchi1 y hy t
        nlinarith [hchi0 y t]
    have hs1 := Finset.sum_le_sum per
    rw [← Finset.sum_mul, sum1, one_mul, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_mem,
      Finset.inter_eq_right.2 hNA] at hs1
    exact hs1
  have hs2 := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm (s := P z) (t := Nz)] at hs2
  have hy : ∀ y ∈ Nz, ∑ t ∈ P z, (if t ∈ P y then ee y (cell t) t else 0) ≤ (Yc * Cc) * (D z + D y) := by
    intro y hyN
    have e1 : ∑ t ∈ P z, (if t ∈ P y then ee y (cell t) t else 0) = ∑ t ∈ P z ∩ P y, ee y (cell t) t := by
      rw [Finset.sum_ite_mem]
    rw [e1]
    have hmaps' : ∀ t ∈ P z ∩ P y, cell t ∈ Yz := fun t ht => hmaps t (Finset.mem_inter.1 ht).1
    rw [← Finset.sum_fiberwise_of_maps_to hmaps']
    have hc : ∀ c ∈ Yz, ∑ t ∈ (P z ∩ P y).filter (fun t => cell t = c), ee y (cell t) t ≤ Cc * (D z + D y) := by
      intro c hc
      refine le_trans (le_of_eq ?_) (hf y hyN c hc)
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [(Finset.mem_filter.1 ht).2]
    have h1 := Finset.sum_le_sum hc
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    refine h1.trans ?_
    have := hDn y hyN
    nlinarith
  have hs3 := Finset.sum_le_sum hy
  rw [← Finset.mul_sum] at hs3
  linarith
theorem mul_le_quarter_of_le_inv {Q s : ℝ} (hQ : 0 < Q) (h : s ≤ 1 / (4 * Q)) : Q * s ≤ 1 / 4 := by
  rw [le_div_iff₀ (by positivity)] at h
  linarith
theorem two_mul_mul_le_half {x s P : ℝ} (hx : x ≤ 1 / 4) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hP : 0 ≤ P) (hx0 : 0 ≤ x) :
    2 * (x * s * P) ≤ P / 2 := by
  have h1 : x * s ≤ 1 / 4 := by nlinarith
  nlinarith
theorem mul_sq_le_of_le_div {W s y : ℝ} (hW : 0 < W) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (h : s ≤ y / W) : W * s ^ 2 ≤ y := by
  rw [le_div_iff₀ hW] at h
  have h1 : s * W * s ≤ s * W * 1 := mul_le_mul_of_nonneg_left hs1 (by positivity)
  have e1 : W * s ^ 2 = s * W * s := by ring
  rw [e1]
  linarith
theorem add_mul_le_of_le_div {K s y : ℝ} (hK : 0 < K) (h : s ≤ y / K) {a b : ℝ} (hab : a + b = K) :
    a * s + b * s ≤ y := by
  rw [le_div_iff₀ hK] at h
  rw [← add_mul, hab]
  linarith
theorem mul_mul_le_of_le_div {Cf s e u : ℝ} (hC : 0 < Cf) (he : 0 < e) (h : s ≤ e * u / 8 / Cf) :
    Cf * s * e ≤ e ^ 2 * u / 8 := by
  rw [le_div_iff₀ hC] at h
  have := mul_le_mul_of_nonneg_right h he.le
  nlinarith
theorem excess_final_bound (e u O Bc Pd G Lf E Wb ρ₁ ρ₂ lam M : ℝ) (hu : 0 < u) (hOu : O * u = 1) (hBc : 0 ≤ Bc)
    (hPd : 0 ≤ Pd) (hG : 0 ≤ G) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hsplit : e ^ 2 * u * Bc - Wb * Bc + Lf + (1 / 32) * G - ρ₁ * Pd ≤ E)
    (hlin : |Lf| ≤ ρ₂ * (Pd + e * Bc))
    (hener : Pd ≤ 3 * (O * G) + Pd / 2 + M * e ^ 2 * Bc)
    (hWb : Wb ≤ e ^ 2 * u / 8) (hρ : ρ₁ + ρ₂ ≤ lam * u / 384) (hρe : ρ₂ * e ≤ e ^ 2 * u / 8)
    (hlamM : lam * M ≤ 24) : e ^ 2 * u / 2 * Bc + lam * u / 384 * Pd ≤ E := by
  have h1 : u * Pd ≤ 3 * G + u * Pd / 2 + u * (M * e ^ 2 * Bc) := by
    have := mul_le_mul_of_nonneg_left hener hu.le
    have e1 : u * (3 * (O * G) + Pd / 2 + M * e ^ 2 * Bc) =
        3 * ((O * u) * G) + u * Pd / 2 + u * (M * e ^ 2 * Bc) := by ring
    rw [e1, hOu, one_mul] at this
    exact this
  have h2 : lam * (u * Pd / 2) ≤ 3 * (lam * G) + (lam * M) * (u * e ^ 2 * Bc) := by
    have := mul_le_mul_of_nonneg_left h1 hlam0
    nlinarith
  have hB : 0 ≤ u * e ^ 2 * Bc := by positivity
  have h3 : (lam * M) * (u * e ^ 2 * Bc) ≤ 24 * (u * e ^ 2 * Bc) := mul_le_mul_of_nonneg_right hlamM hB
  have h4 : lam * G ≤ G := by nlinarith
  have h5 := neg_abs_le Lf
  have h6 : ρ₂ * (e * Bc) ≤ e ^ 2 * u / 8 * Bc := by
    have := mul_le_mul_of_nonneg_right hρe hBc
    nlinarith
  have h7 : Wb * Bc ≤ e ^ 2 * u / 8 * Bc := mul_le_mul_of_nonneg_right hWb hBc
  have h8 : (ρ₁ + ρ₂) * Pd ≤ lam * u / 384 * Pd := mul_le_mul_of_nonneg_right hρ hPd
  nlinarith
end Sums
variable {F : BlockFrame}
open PatchLocality
theorem baseSite_enclosingCell_mem_patchBaseSites (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S : Finset F.Cell} {z : F.Cell}
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {t : F.ActionTerm} (ht : t ∈ patchActionTerms S z) :
    baseSite (enclosingCell (actionTermSite t)) ∈ patchBaseSites S z := by
  obtain ⟨_, h, hh, e⟩ := enclosingCell_actionTermSite (S := S) hodd (patchActionTerms_subset ht)
  have h1 := actionTermSite_mem_patchBaseSites hodd ht
  rw [e] at h1
  have hz0 : (0 : LatticeFractionalIntegration.Lattice4) ∈ centredCube (F.blockSide ^ F.top) := by
    refine Fintype.mem_piFinset.2 fun i => ?_
    have : 0 < F.blockSide ^ F.top := by have := hodd.pos; positivity
    simp only [Pi.zero_apply, Finset.mem_Icc]
    omega
  have h2 := mem_patchBaseSites_of_same_cell hamb hodd he hh hz0 h1
  rw [siteOfCoords_zero, add_zero] at h2
  have h3 := baseSite_cellCentre (F := F) F.top le_rfl (enclosingCell (actionTermSite t))
  rw [cellCentre_top] at h3
  rw [h3]
  exact h2
set_option maxHeartbeats 2000000 in
theorem criticalChainExcess (hP : pinnedGaugeAtGoodCellStatement) (hD : relativeDensityComparisonStatement)
    (hT : termwiseFirstVariationStatement) (hL : gluedFirstVariationStatement)
    (hS : criticalCellShareBoundStatement) : criticalChainExcessStatement := by
  classical
  intro a θ del Ca ha hθ hθ8 hd hd8 hCa
  obtain ⟨Cd, hCd, L₁, hP1⟩ := hP a θ del Ca ha hθ hθ8 hd hd8 hCa
  obtain ⟨L₂, hD1⟩ := hD a θ del Ca ha hθ hθ8 hd hd8 hCa
  obtain ⟨L₃, hT1⟩ := hT a θ del Ca ha hθ hθ8 hd hd8 hCa
  obtain ⟨L₄, hL1⟩ := hL a θ del Ca ha hθ hθ8 hd hd8 hCa
  obtain ⟨L₅, hS1⟩ := hS a θ del Ca ha hθ hθ8 hd hd8 hCa
  refine ⟨max L₁ (max L₂ (max L₃ (max L₄ L₅))), fun L hodd hLge C₁ hC₁ => ?_⟩
  have l₁ : L₁ ≤ L := le_trans (le_max_left _ _) hLge
  have l₂ : L₂ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLge
  have l₃ : L₃ ≤ L := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hLge
  have l₄ : L₄ ≤ L := le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) (le_max_right _ _)) hLge
  have l₅ : L₅ ≤ L := le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) (le_max_right _ _)) hLge
  obtain ⟨C, c₁, hC, hc₁, hP2⟩ := hP1 L hodd l₁ C₁ hC₁
  obtain ⟨Cx, c₂, hCx, hc₂, hD2⟩ := hD1 L hodd l₂ C₁ C Cd hC₁ hC hCd
  obtain ⟨Ct, c₃, hCt, hc₃, hT2⟩ := hT1 L hodd l₃ C₁ C Cd hC₁ hC hCd
  obtain ⟨Cf, c₄, hCf, hc₄, hL2⟩ := hL1 L hodd l₄ C₁ C Cd hC₁ hC hCd
  obtain ⟨Cs, σ₅, hCs, hσ₅, hS2⟩ := hS1 L hodd l₅ C₁ hC₁
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = min (min c₁ c₂) (min c₃ c₄) := ⟨_, rfl⟩
  have he0 : 0 < e := by
    rw [he]
    exact lt_min (lt_min hc₁ hc₂) (lt_min hc₃ hc₄)
  have e₁ : e ≤ c₁ := by rw [he]; exact (min_le_left _ _).trans (min_le_left _ _)
  have e₂ : e ≤ c₂ := by rw [he]; exact (min_le_left _ _).trans (min_le_right _ _)
  have e₃ : e ≤ c₃ := by rw [he]; exact (min_le_right _ _).trans (min_le_left _ _)
  have e₄ : e ≤ c₄ := by rw [he]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨σ₁, hσ₁, hP3⟩ := hP2 e he0 e₁
  obtain ⟨σ₂, hσ₂, hD3⟩ := hD2 e he0 e₂
  obtain ⟨σ₃, hσ₃, hT3⟩ := hT2 e he0 e₃
  obtain ⟨σ₄, hσ₄, hL3⟩ := hL2 e he0 e₄
  obtain ⟨O, hOdef⟩ : ∃ O : ℝ, O = 47 ^ 4 := ⟨_, rfl⟩
  have hO : 0 < O := by rw [hOdef]; norm_num
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = 1 / O := ⟨_, rfl⟩
  have hu : 0 < u := by rw [hudef]; positivity
  have hOu : O * u = 1 := by rw [hudef]; field_simp
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 2 * (131 ^ 4 * Cd) := ⟨_, rfl⟩
  have hM : 0 < M := by rw [hMdef]; positivity
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = min 1 (24 / M) := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlamdef]; exact lt_min one_pos (by positivity)
  have hlam1 : lam ≤ 1 := by rw [hlamdef]; exact min_le_left _ _
  have hlamM : lam * M ≤ 24 := by
    have : lam ≤ 24 / M := by rw [hlamdef]; exact min_le_right _ _
    rw [le_div_iff₀ hM] at this
    exact this
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : ℝ, W₀ = 85 ^ 4 * Cs := ⟨_, rfl⟩
  have hW₀p : 0 < W₀ := by rw [hW₀]; positivity
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 47 ^ 4 * Cx * 51 ^ 4 := ⟨_, rfl⟩
  have hQp : 0 < Q := by rw [hQ]; positivity
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = min (min (min σ₁ σ₂) (min σ₃ σ₄)) (min (min σ₅ 1)
      (min (min (lam * u / 384 / (Ct + Cf)) (e ^ 2 * u / 8 / W₀)) (min (e * u / 8 / Cf) (1 / (4 * Q))))) := ⟨_, rfl⟩
  have hσ : 0 < σ := by
    rw [hσdef]
    refine lt_min (lt_min (lt_min hσ₁ hσ₂) (lt_min hσ₃ hσ₄)) (lt_min (lt_min hσ₅ one_pos)
      (lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))))
  have s₁ : σ ≤ σ₁ := by
    rw [hσdef]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have s₂ : σ ≤ σ₂ := by
    rw [hσdef]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have s₃ : σ ≤ σ₃ := by
    rw [hσdef]; exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have s₄ : σ ≤ σ₄ := by
    rw [hσdef]; exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have s₅ : σ ≤ σ₅ := by
    rw [hσdef]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have s₆ : σ ≤ 1 := by
    rw [hσdef]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have s₇ : σ ≤ lam * u / 384 / (Ct + Cf) := by
    rw [hσdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have s₈ : σ ≤ e ^ 2 * u / 8 / W₀ := by
    rw [hσdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have s₉ : σ ≤ e * u / 8 / Cf := by
    rw [hσdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have s₁₀ : σ ≤ 1 / (4 * Q) := by
    rw [hσdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨C, hC, e, σ, min (e ^ 2 * u / 2) (lam * u / 384), he0, hσ, lt_min (by positivity) (by positivity), ?_⟩
  intro F m S hFL hamb hm hreg s V v hs hsσ hcold hv U hU X k hX
  have hodd' : Odd F.blockSide := hFL ▸ hodd
  have hsign : ∀ z, ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1 :=
    fun z => (closedOrthant_spec hreg (by omega) z).1
  have ha0 : 0 ≤ a := ha.le
  obtain ⟨A, hA⟩ : ∃ A : Finset F.Cell, A = cellsClearOfHighEnergy a e S X k := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset F.Cell, B = highEnergyCells a e S X k := ⟨_, rfl⟩
  have hAS : A ⊆ S := by rw [hA]; exact Finset.filter_subset _ _
  have hBS : B ⊆ S := by rw [hB]; exact Finset.filter_subset _ _
  have memA : ∀ {z}, z ∈ A ↔ z ∈ S ∧ ∀ y ∈ S, e ^ 2 < patchAction a S y X k → 40 < cellSupDist z y := by
    intro z
    rw [hA]
    exact Finset.mem_filter
  have memB : ∀ {z}, z ∈ B ↔ z ∈ S ∧ e ^ 2 < patchAction a S z X k := by
    intro z
    rw [hB]
    exact Finset.mem_filter
  have hgood : ∀ z ∈ A, patchAction a S z X k ≤ e ^ 2 := by
    intro z hz
    by_contra hc
    have := (memA.1 hz).2 z (memA.1 hz).1 (not_le.1 hc)
    rw [cellSupDist_self] at this
    omega
  have hΓ0 : ∀ z, ∃ Γ : F.SiteGauge, z ∈ A →
      HasPinnedGaugeAt a C Cd e S z (criticalFieldChain S V v U) (criticalGauge S V U) X k Γ := by
    intro z
    by_cases hz : z ∈ A
    · obtain ⟨Γ, h1, h2⟩ := hP3 F m S hFL hamb hm hreg s V v hs (hsσ.trans s₁) hcold hv U hU X k z hX (hAS hz)
        (hgood z hz)
      exact ⟨Γ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ _ => 1, fun h => absurd h hz⟩
  choose Γ hΓ using hΓ0
  obtain ⟨D, hDdef⟩ : ∃ D : F.Cell → ℝ, D = fun z =>
    relativeEnergy a S z (criticalFieldChain S V v U) (criticalGauge S V U) X k (Γ z) := ⟨_, rfl⟩
  obtain ⟨dens, hdens⟩ : ∃ dens : F.Cell → F.ActionTerm → ℝ, dens = fun z t =>
    relativeEnergyDensity a (criticalFieldChain S V v U) (criticalGauge S V U) X k (Γ z) t := ⟨_, rfl⟩
  obtain ⟨fo, hfo⟩ : ∃ fo : F.Cell → F.ActionTerm → ℝ, fo = fun z t =>
    firstVariation a (criticalFieldChain S V v U) (criticalGauge S V U)
      (gaugeVariation (criticalFieldChain S V v U) (criticalGauge S V U) X k (Γ z)) t := ⟨_, rfl⟩
  obtain ⟨chi, hchidef⟩ : ∃ chi : F.Cell → F.ActionTerm → ℝ, chi = fun z t =>
    cellPartition S (actionTermSite t) z := ⟨_, rfl⟩
  have hD0 : ∀ z, 0 ≤ D z := by
    intro z
    rw [hDdef]
    simp only
    rw [relativeEnergy_eq_sum]
    exact Finset.sum_nonneg fun t _ => relativeEnergyDensity_nonneg ha0 _ _ _ _ _ t
  have hdens0 : ∀ z t, 0 ≤ dens z t := by
    intro z t
    rw [hdens]
    exact relativeEnergyDensity_nonneg ha0 _ _ _ _ _ t
  have hDsum : ∀ z, D z = ∑ t ∈ patchActionTerms S z, dens z t := by
    intro z
    rw [hDdef, hdens]
    exact relativeEnergy_eq_sum a S z _ _ X k (Γ z)
  have hchi0 : ∀ z t, 0 ≤ chi z t := by
    intro z t
    rw [hchidef]
    exact cellPartition_nonneg _ _
  have hchi1 : ∀ z ∈ S, ∀ t, chi z t ≤ 1 := by
    intro z hz t
    rw [hchidef]
    exact cellPartition_le_one _ hz
  have hsum : ∀ t ∈ actionTerms S, ∑ z ∈ S, chi z t = 1 := by
    intro t ht
    rw [hchidef]
    exact sum_cellPartition hamb hodd' (actionTermSite_mem_sitesOfCells hodd' ht)
  have hbump : ∀ {z t}, chi z t ≠ 0 → cellCutoff (actionTermSite t) z ≠ 0 := by
    intro z t h
    rw [hchidef] at h
    exact cellCutoff_ne_zero_of_cellPartition_ne_zero h
  have hE0 : ∀ z, ∃ err : F.ActionTerm → ℝ, (∀ t, 0 ≤ err t) ∧ (z ∈ A →
      (∀ t ∈ patchActionTerms S z, fo z t + (1 / 32) * dens z t - err t ≤
        actionTermValue a X k t - actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) t) ∧
      ∑ t ∈ patchActionTerms S z, err t ≤ (Ct * s) * D z) := by
    intro z
    by_cases hz : z ∈ A
    · obtain ⟨err, h1, h2, h3⟩ := hT3 F m S hFL hamb hm hreg s V v hs (hsσ.trans s₃) hcold hv U hU X k (Γ z) z hX
        (hAS hz) (hgood z hz) (hΓ z hz)
      refine ⟨err, h2, fun _ => ⟨fun t ht => ?_, ?_⟩⟩
      · rw [hfo, hdens]
        exact h1 t ht
      · rw [hDdef]
        exact h3
    · exact ⟨fun _ => 0, fun _ => le_rfl, fun h => absurd h hz⟩
  choose err herr0 herr using hE0
  have hcount : ∀ (Z : Finset F.Cell), ∀ t ∈ actionTerms S,
      ((Z.filter fun y => t ∈ patchActionTerms S y).card : ℝ) ≤ O := by
    intro Z t ht
    obtain ⟨_, h, hh, eq⟩ := enclosingCell_actionTermSite (S := S) hodd' ht
    have h1 := card_le_of_cellSupDist_le (enclosingCell (actionTermSite t)) 23
      (Z.filter fun y => t ∈ patchActionTerms S y) (fun y hy => by
        have hy' := (Finset.mem_filter.1 hy).2
        rw [cellSupDist_comm]
        exact cellSupDist_le_of_mem_patchBaseSites hamb hodd' (hsign y)
          (actionTermSite_mem_patchBaseSites hodd' hy') hh eq)
    calc ((Z.filter fun y => t ∈ patchActionTerms S y).card : ℝ) ≤ (((2 * 23 + 1) ^ 4 : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ = O := by rw [hOdef]; norm_num
  have hw0 : ∀ t, 0 ≤ actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) t :=
    fun t => actionTermValue_nonneg ha0 _ _ t
  have hnear : ∑ t ∈ (actionTerms S).filter (fun t => ∑ z ∈ A, chi z t ≠ 1),
      actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) t ≤ (W₀ * s ^ 2) * B.card := by
    have hshare : ∀ y, ∑ t ∈ (actionTerms S).filter (fun t => enclosingCell (actionTermSite t) = y),
        actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) t ≤ Cs * s ^ 2 :=
      fun y => hS2 F m S hFL hamb hm hreg s V v hs (hsσ.trans s₅) hcold hv U hU y
    obtain ⟨Y, hY⟩ : ∃ Y : F.Cell → Finset F.Cell, Y = fun b => S.filter (fun y => cellSupDist y b ≤ 42) :=
      ⟨_, rfl⟩
    have hcover : ∀ t ∈ (actionTerms S).filter (fun t => ∑ z ∈ A, chi z t ≠ 1),
        ∃ b ∈ B, ∃ y ∈ Y b, enclosingCell (actionTermSite t) = y := by
      intro t ht
      obtain ⟨ht1, ht2⟩ := Finset.mem_filter.1 ht
      obtain ⟨hcS, h, hh, eq⟩ := enclosingCell_actionTermSite (S := S) hodd' ht1
      have hex : ∃ z ∈ S, z ∉ A ∧ chi z t ≠ 0 := by
        by_contra hc
        push Not at hc
        apply ht2
        rw [← hsum t ht1]
        exact Finset.sum_subset hAS fun z hz hzA => hc z hz hzA
      obtain ⟨z, hz, hzA, hne⟩ := hex
      have hbad : ∃ b ∈ S, e ^ 2 < patchAction a S b X k ∧ cellSupDist z b ≤ 40 := by
        by_contra hc
        push Not at hc
        exact hzA (memA.2 ⟨hz, fun y hy hb => hc y hy hb⟩)
      obtain ⟨b, hbS, hbb, hdb⟩ := hbad
      refine ⟨b, memB.2 ⟨hbS, hbb⟩, _, ?_, rfl⟩
      rw [hY]
      refine Finset.mem_filter.2 ⟨hcS, ?_⟩
      have d1 := cellSupDist_le_two_of_cellCutoff_ne_zero hamb hodd' (hbump hne) hh eq
      have d2 := cellSupDist_triangle (enclosingCell (actionTermSite t)) z b
      rw [cellSupDist_comm (enclosingCell (actionTermSite t)) z] at d2
      omega
    have step1 : ∀ t ∈ (actionTerms S).filter (fun t => ∑ z ∈ A, chi z t ≠ 1),
        actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) t ≤ ∑ b ∈ B, ∑ y ∈ Y b,
          if enclosingCell (actionTermSite t) = y then
            actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) t else 0 := by
      intro t ht
      obtain ⟨b, hb, y, hy, eq⟩ := hcover t ht
      have hnn : ∀ y, 0 ≤ if enclosingCell (actionTermSite t) = y then
          actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) t else 0 := by
        intro y
        split_ifs
        · exact hw0 t
        · exact le_rfl
      calc actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) t
          = if enclosingCell (actionTermSite t) = y then
              actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) t else 0 := by
            rw [if_pos eq]
        _ ≤ ∑ y ∈ Y b, if enclosingCell (actionTermSite t) = y then
              actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) t else 0 :=
            Finset.single_le_sum (f := fun y => if enclosingCell (actionTermSite t) = y then
              actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) t else 0) (fun y _ => hnn y) hy
        _ ≤ _ := Finset.single_le_sum (f := fun b => ∑ y ∈ Y b, if enclosingCell (actionTermSite t) = y then
              actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) t else 0)
              (fun b _ => Finset.sum_nonneg fun y _ => hnn y) hb
    have step2 := (Finset.sum_le_sum step1).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun t => ∑ z ∈ A, chi z t ≠ 1) (actionTerms S)) (fun t _ _ =>
        Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun y _ => by
          split_ifs
          · exact hw0 t
          · exact le_rfl))
    refine step2.trans ?_
    rw [Finset.sum_comm]
    have hb : ∀ b ∈ B, ∑ t ∈ actionTerms S, ∑ y ∈ Y b, (if enclosingCell (actionTermSite t) = y then
        actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) t else 0) ≤ W₀ * s ^ 2 := by
      intro b _
      rw [Finset.sum_comm]
      have h1 : ∀ y ∈ Y b, ∑ t ∈ actionTerms S, (if enclosingCell (actionTermSite t) = y then
          actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) t else 0) ≤ Cs * s ^ 2 := by
        intro y _
        rw [← Finset.sum_filter]
        exact hshare y
      have h2 := Finset.sum_le_sum h1
      rw [Finset.sum_const, nsmul_eq_mul] at h2
      refine h2.trans ?_
      have h3 : (Y b).card ≤ (2 * 42 + 1) ^ 4 := card_le_of_cellSupDist_le b 42 (Y b) (fun y hy => by
        rw [hY] at hy
        exact (Finset.mem_filter.1 hy).2)
      have h4 : ((Y b).card : ℝ) ≤ 85 ^ 4 := by
        have : ((Y b).card : ℝ) ≤ (((2 * 42 + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast h3
        norm_num at this ⊢
        exact this
      have h5 : 0 ≤ Cs * s ^ 2 := by positivity
      calc ((Y b).card : ℝ) * (Cs * s ^ 2) ≤ 85 ^ 4 * (Cs * s ^ 2) := mul_le_mul_of_nonneg_right h4 h5
        _ = W₀ * s ^ 2 := by rw [hW₀]; ring
    have h6 := Finset.sum_le_sum hb
    rw [Finset.sum_const, nsmul_eq_mul] at h6
    rw [mul_comm (W₀ * s ^ 2)]
    exact h6
  have hbad0 : ∀ y ∈ B, ∀ t ∈ patchActionTerms S y, ∀ z ∈ A, chi z t = 0 := by
    intro y hy t ht z hz
    by_contra hne
    obtain ⟨_, h, hh, eq⟩ := enclosingCell_actionTermSite (S := S) hodd' (patchActionTerms_subset ht)
    have d1 := cellSupDist_le_two_of_cellCutoff_ne_zero hamb hodd' (hbump hne) hh eq
    have d2 := cellSupDist_le_of_mem_patchBaseSites hamb hodd' (hsign y)
      (actionTermSite_mem_patchBaseSites hodd' ht) hh eq
    have d3 := cellSupDist_triangle z (enclosingCell (actionTermSite t)) y
    have d4 := (memA.1 hz).2 y (memB.1 hy).1 (memB.1 hy).2
    omega
  have hcost : ∀ y ∈ B, e ^ 2 ≤ ∑ t ∈ patchActionTerms S y, actionTermValue a X k t := by
    intro y hy
    rw [← patchAction_eq_sum]
    exact (memB.1 hy).2.le
  have hsplit := excess_split_le (actionTerms S) S A B (patchActionTerms S) (actionTermValue a X k)
    (actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U)) chi fo dens err D e O (W₀ * s ^ 2)
    (Ct * s) hO
    (fun t _ => actionTermValue_nonneg ha0 _ _ t) (fun t _ => hw0 t) hchi0 hchi1 hsum hAS
    (fun _ _ => patchActionTerms_subset) hBS
    (fun z _ t ht h => mem_patchActionTerms_of_cellCutoff_ne_zero hamb hodd' (hsign z) ht (hbump h)) hbad0 hcost
    (fun t ht => by convert hcount B t ht) hnear (fun z hz => (herr z hz).1) herr0 (fun z hz => (herr z hz).2)
  have hE1 : ∀ z y c, ∃ ee : F.ActionTerm → ℝ, (∀ t, 0 ≤ ee t) ∧ (z ∈ A → y ∈ A → cellSupDist z y ≤ 40 →
      c ∈ S → baseSite c ∈ patchBaseSites S z → baseSite c ∈ patchBaseSites S y →
      (∀ t ∈ patchActionTerms S z ∩ patchActionTerms S y, enclosingCell (actionTermSite t) = c →
        dens z t ≤ 3 * dens y t + ee t) ∧
      ∑ t ∈ (patchActionTerms S z ∩ patchActionTerms S y).filter (fun t => enclosingCell (actionTermSite t) = c),
        ee t ≤ Cx * s ^ 2 * (D z + D y)) := by
    intro z y c
    by_cases hcond : z ∈ A ∧ y ∈ A ∧ cellSupDist z y ≤ 40 ∧ c ∈ S ∧ baseSite c ∈ patchBaseSites S z ∧
        baseSite c ∈ patchBaseSites S y
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hcond
      obtain ⟨ee, g1, g2, g3⟩ := hD3 F m S hFL hamb hm hreg s V v hs (hsσ.trans s₂) hcold hv U hU X k (Γ z) (Γ y)
        z y c hX (hAS h1) (hAS h2) h4 h3 h5 h6 (hgood z h1) (hgood y h2) (hΓ z h1) (hΓ y h2)
      refine ⟨ee, g2, fun _ _ _ _ _ _ => ⟨fun t ht hc => ?_, ?_⟩⟩
      · rw [hdens]
        exact g1 t ht hc
      · rw [hDdef]
        exact g3
    · refine ⟨fun _ => 0, fun _ => le_rfl, fun h1 h2 h3 h4 h5 h6 => absurd ⟨h1, h2, h3, h4, h5, h6⟩ hcond⟩
  choose ee hee0 hee using hE1
  obtain ⟨A0, hA0⟩ : ∃ A0 : Finset F.Cell, A0 = A.filter (fun z => ∀ y ∈ S, cellSupDist z y ≤ 25 → y ∈ A) :=
    ⟨_, rfl⟩
  have memA0 : ∀ {z}, z ∈ A0 ↔ z ∈ A ∧ ∀ y ∈ S, cellSupDist z y ≤ 25 → y ∈ A := by
    intro z
    rw [hA0]
    exact Finset.mem_filter
  obtain ⟨N, hN⟩ : ∃ N : F.Cell → Finset F.Cell, N = fun z => A.filter (fun y => cellSupDist z y ≤ 25) := ⟨_, rfl⟩
  have memN : ∀ {z y}, y ∈ N z ↔ y ∈ A ∧ cellSupDist z y ≤ 25 := by
    intro z y
    rw [hN]
    exact Finset.mem_filter
  obtain ⟨g, hg⟩ : ∃ g : F.ActionTerm → ℝ, g = fun t => ∑ y ∈ A, chi y t * dens y t := ⟨_, rfl⟩
  have hg0 : ∀ t, 0 ≤ g t := by
    intro t
    rw [hg]
    exact Finset.sum_nonneg fun y _ => mul_nonneg (hchi0 y t) (hdens0 y t)
  have hloc : ∀ z ∈ A0, D z ≤ 3 * ∑ t ∈ patchActionTerms S z, g t +
      (47 ^ 4 * (Cx * s ^ 2)) * ∑ y ∈ N z, (D z + D y) := by
    intro z hz0
    have hzA := (memA0.1 hz0).1
    have hmain : ∑ t ∈ patchActionTerms S z, dens z t ≤
        3 * ∑ t ∈ patchActionTerms S z, ∑ y ∈ A, chi y t * dens y t +
        (47 ^ 4 * (Cx * s ^ 2)) * ∑ y ∈ N z, (D z + D y) := by
      refine local_density_le (actionTerms S) S A (N z) (S.filter (fun c => cellSupDist c z ≤ 23))
        (patchActionTerms S) chi dens (ee z) (fun t => enclosingCell (actionTermSite t)) D z (Cx * s ^ 2) (47 ^ 4)
        patchActionTerms_subset hsum hAS (by rw [hN]; exact Finset.filter_subset _ _) hchi0
        (fun y hy => hchi1 y (hAS hy)) (hee0 z) ?_ ?_ ?_ ?_ ?_ ?_
      · intro t ht y hy hne
        obtain ⟨_, h, hh, eq⟩ := enclosingCell_actionTermSite (S := S) hodd' (patchActionTerms_subset ht)
        have dcz := cellSupDist_le_of_mem_patchBaseSites hamb hodd' (hsign z)
          (actionTermSite_mem_patchBaseSites hodd' ht) hh eq
        have d1 := cellSupDist_le_two_of_cellCutoff_ne_zero hamb hodd' (hbump hne) hh eq
        have d2 := cellSupDist_triangle z (enclosingCell (actionTermSite t)) y
        have c1 := cellSupDist_comm z (enclosingCell (actionTermSite t))
        have c2 := cellSupDist_comm y (enclosingCell (actionTermSite t))
        have hd : cellSupDist z y ≤ 25 := by omega
        exact ⟨memN.2 ⟨(memA0.1 hz0).2 y hy hd, hd⟩,
          mem_patchActionTerms_of_cellCutoff_ne_zero hamb hodd' (hsign y) (patchActionTerms_subset ht) (hbump hne)⟩
      · intro y hyN t ht
        obtain ⟨hyA, hyd⟩ := memN.1 hyN
        obtain ⟨ht₃, ht₄⟩ := Finset.mem_inter.1 ht
        have hcS := (enclosingCell_actionTermSite (S := S) hodd' (patchActionTerms_subset ht₃)).1
        exact ((hee z y (enclosingCell (actionTermSite t))) hzA hyA (by omega) hcS
          (baseSite_enclosingCell_mem_patchBaseSites hamb hodd' (hsign z) ht₃)
          (baseSite_enclosingCell_mem_patchBaseSites hamb hodd' (hsign y) ht₄)).1 t ht rfl
      · intro y hyN c hc
        obtain ⟨hyA, hyd⟩ := memN.1 hyN
        by_cases hne : ((patchActionTerms S z ∩ patchActionTerms S y).filter
            (fun t => enclosingCell (actionTermSite t) = c)).Nonempty
        · obtain ⟨t₀, ht₀⟩ := hne
          obtain ⟨ht₁, ht₂⟩ := Finset.mem_filter.1 ht₀
          obtain ⟨ht₃, ht₄⟩ := Finset.mem_inter.1 ht₁
          have hcS : c ∈ S := (Finset.mem_filter.1 hc).1
          have hc1 := baseSite_enclosingCell_mem_patchBaseSites hamb hodd' (hsign z) ht₃
          have hc2 := baseSite_enclosingCell_mem_patchBaseSites hamb hodd' (hsign y) ht₄
          rw [ht₂] at hc1 hc2
          exact ((hee z y c) hzA hyA (by omega) hcS hc1 hc2).2
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          rw [hne, Finset.sum_empty]
          exact mul_nonneg (by positivity) (add_nonneg (hD0 z) (hD0 y))
      · intro t ht
        obtain ⟨hcS, h, hh, eq⟩ := enclosingCell_actionTermSite (S := S) hodd' (patchActionTerms_subset ht)
        exact Finset.mem_filter.2 ⟨hcS, cellSupDist_le_of_mem_patchBaseSites hamb hodd' (hsign z)
          (actionTermSite_mem_patchBaseSites hodd' ht) hh eq⟩
      · have h3 := card_le_of_cellSupDist_le z 23 (S.filter (fun c => cellSupDist c z ≤ 23))
          (fun c hc => (Finset.mem_filter.1 hc).2)
        have : ((S.filter (fun c => cellSupDist c z ≤ 23)).card : ℝ) ≤ (((2 * 23 + 1) ^ 4 : ℕ) : ℝ) := by
          exact_mod_cast h3
        norm_num at this ⊢
        exact this
      · intro y _
        exact mul_nonneg (by positivity) (add_nonneg (hD0 z) (hD0 y))
    rw [← hDsum z] at hmain
    rw [hg]
    exact hmain
  have hout : ∑ z ∈ A \ A0, D z ≤ (131 ^ 4 * (Cd * e ^ 2)) * B.card := by
    have h1 : ∀ z ∈ A \ A0, D z ≤ Cd * e ^ 2 := by
      intro z hz
      have := (hΓ z (Finset.mem_sdiff.1 hz).1).2
      rw [hDdef]
      exact this
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    refine h2.trans ?_
    have hsub : A \ A0 ⊆ B.biUnion (fun b => S.filter (fun z => cellSupDist z b ≤ 65)) := by
      intro z hz
      obtain ⟨hzA, hz0⟩ := Finset.mem_sdiff.1 hz
      have hex : ∃ y ∈ S, cellSupDist z y ≤ 25 ∧ y ∉ A := by
        by_contra hc
        push Not at hc
        exact hz0 (memA0.2 ⟨hzA, fun y hy hd => hc y hy hd⟩)
      obtain ⟨y, hyS, hd, hyA⟩ := hex
      have hbad : ∃ b ∈ S, e ^ 2 < patchAction a S b X k ∧ cellSupDist y b ≤ 40 := by
        by_contra hc
        push Not at hc
        exact hyA (memA.2 ⟨hyS, fun w hw hb => hc w hw hb⟩)
      obtain ⟨b, hbS, hbb, hdb⟩ := hbad
      refine Finset.mem_biUnion.2 ⟨b, memB.2 ⟨hbS, hbb⟩, Finset.mem_filter.2 ⟨hAS hzA, ?_⟩⟩
      have := cellSupDist_triangle z y b
      omega
    have hcard : (A \ A0).card ≤ B.card * (2 * 65 + 1) ^ 4 := by
      refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul _ _ _ fun b _ => ?_)
      exact card_le_of_cellSupDist_le b 65 _ (fun c hc => (Finset.mem_filter.1 hc).2)
    have hcard' : ((A \ A0).card : ℝ) ≤ B.card * 131 ^ 4 := by
      have : ((A \ A0).card : ℝ) ≤ ((B.card * (2 * 65 + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast hcard
      push_cast at this
      norm_num at this ⊢
      exact this
    have h5 : 0 ≤ Cd * e ^ 2 := by positivity
    calc ((A \ A0).card : ℝ) * (Cd * e ^ 2) ≤ ((B.card : ℝ) * 131 ^ 4) * (Cd * e ^ 2) :=
          mul_le_mul_of_nonneg_right hcard' h5
      _ = 131 ^ 4 * (Cd * e ^ 2) * B.card := by ring
  have hA0A : A0 ⊆ A := by rw [hA0]; exact Finset.filter_subset _ _
  have hener := sum_energy_le_of_local A A0 (actionTerms S) (patchActionTerms S) g D N (47 ^ 4 * (Cx * s ^ 2)) O
    (51 ^ 4) ((131 ^ 4 * (Cd * e ^ 2)) * B.card) hA0A (fun z _ => hD0 z) (fun t _ => hg0 t)
    (fun _ _ => patchActionTerms_subset) (fun t ht => by convert hcount A0 t ht)
    (fun z _ => by rw [hN]; exact Finset.filter_subset _ _)
    (fun z _ => by
      have h3 := card_le_of_cellSupDist_le z 25 (N z) (fun y hy => by
        rw [cellSupDist_comm]
        exact (memN.1 hy).2)
      have : ((N z).card : ℝ) ≤ (((2 * 25 + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast h3
      norm_num at this ⊢
      exact this)
    (fun y _ => by
      have h3 := card_le_of_cellSupDist_le y 25 (A0.filter fun z => y ∈ N z)
        (fun z hz => (memN.1 (Finset.mem_filter.1 hz).2).2)
      have : ((A0.filter fun z => y ∈ N z).card : ℝ) ≤ (((2 * 25 + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast h3
      norm_num at this ⊢
      convert this)
    (by positivity) (by positivity) hloc hout
  have hlin := hL3 F m S hFL hamb hm hreg s V v hs (hsσ.trans s₄) hcold hv U hU X k Γ hX
    (fun z hz => hΓ z (by rw [hA]; exact hz))
  obtain ⟨Lf, hLf⟩ : ∃ Lf : ℝ, Lf = ∑ z ∈ A, ∑ t ∈ actionTerms S, chi z t * fo z t := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = ∑ z ∈ A, ∑ t ∈ actionTerms S, chi z t * dens z t := ⟨_, rfl⟩
  obtain ⟨Pd, hPddef⟩ : ∃ Pd : ℝ, Pd = ∑ z ∈ A, D z := ⟨_, rfl⟩
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = (B.card : ℝ) := ⟨_, rfl⟩
  have hBc0 : 0 ≤ Bc := by rw [hBc]; positivity
  have hPd0 : 0 ≤ Pd := by rw [hPddef]; exact Finset.sum_nonneg fun z _ => hD0 z
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    exact Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun t _ => mul_nonneg (hchi0 z t) (hdens0 z t)
  have hlin' : |Lf| ≤ (Cf * s) * (Pd + e * Bc) := by
    rw [hLf, hPddef, hBc, hchidef, hfo, hDdef, hA, hB]
    exact hlin
  have hGg : ∑ t ∈ actionTerms S, g t = G := by
    rw [hGdef, hg]
    exact Finset.sum_comm
  rw [hGg, ← hPddef, ← hBc] at hener
  have hs1 : s ≤ 1 := hsσ.trans s₆
  have hs0 : 0 ≤ s := hs.le
  have hQs : Q * s ≤ 1 / 4 := mul_le_quarter_of_le_inv hQp (hsσ.trans s₁₀)
  have hener' : Pd ≤ 3 * (O * G) + Pd / 2 + M * e ^ 2 * Bc := by
    have h1 : 2 * (47 ^ 4 * (Cx * s ^ 2) * (51 ^ 4 * Pd)) ≤ Pd / 2 := by
      have h2 : 47 ^ 4 * (Cx * s ^ 2) * (51 ^ 4 * Pd) = (Q * s) * s * Pd := by
        rw [hQ]
        ring
      rw [h2]
      exact two_mul_mul_le_half hQs hs0 hs1 hPd0 (mul_nonneg hQp.le hs0)
    have h4 : 131 ^ 4 * (Cd * e ^ 2) * Bc ≤ M * e ^ 2 * Bc := by
      rw [hMdef]
      have h5 : 0 ≤ 131 ^ 4 * (Cd * e ^ 2) * Bc := by positivity
      have e2 : 2 * (131 ^ 4 * Cd) * e ^ 2 * Bc = 2 * (131 ^ 4 * (Cd * e ^ 2) * Bc) := by ring
      rw [e2]
      linarith
    linarith
  have hWb : W₀ * s ^ 2 ≤ e ^ 2 * u / 8 := mul_sq_le_of_le_div hW₀p hs0 hs1 (hsσ.trans s₈)
  have hρ : Ct * s + Cf * s ≤ lam * u / 384 := add_mul_le_of_le_div (add_pos hCt hCf) (hsσ.trans s₇) rfl
  have hρe : Cf * s * e ≤ e ^ 2 * u / 8 := mul_mul_le_of_le_div hCf he0 (hsσ.trans s₉)
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = ∑ t ∈ actionTerms S, (actionTermValue a X k t -
      actionTermValue a (criticalFieldChain S V v U) (criticalGauge S V U) t) := ⟨_, rfl⟩
  have hsplit' : e ^ 2 * u * Bc - W₀ * s ^ 2 * Bc + Lf + 1 / 32 * G - Ct * s * Pd ≤ E := by
    have e1 : e ^ 2 / O = e ^ 2 * u := by rw [hudef]; ring
    rw [e1, ← hBc, ← hLf, ← hGdef, ← hPddef, ← hE] at hsplit
    exact hsplit
  have hfin := excess_final_bound e u O Bc Pd G Lf E (W₀ * s ^ 2) (Ct * s) (Cf * s) lam M hu hOu hBc0 hPd0 hG0
    hlam0.le hlam1 hsplit' hlin' hener' hWb hρ hρe hlamM
  have hfarA : ∀ z ∈ cellsFarFromHighEnergy a e S X k, z ∈ A := by
    intro z hz
    obtain ⟨hzS, hzb⟩ := Finset.mem_filter.1 hz
    refine memA.2 ⟨hzS, fun y hy hb => ?_⟩
    have := hzb y (Finset.mem_filter.2 ⟨hy, hb⟩)
    omega
  refine ⟨Γ, fun z hz => (hΓ z (hfarA z hz)).1, ?_⟩
  obtain ⟨Pf, hPf⟩ : ∃ Pf : ℝ, Pf = ∑ z ∈ cellsFarFromHighEnergy a e S X k, D z := ⟨_, rfl⟩
  have hPfPd : Pf ≤ Pd := by
    rw [hPf, hPddef]
    exact Finset.sum_le_sum_of_subset_of_nonneg hfarA fun z _ _ => hD0 z
  have hPf0 : 0 ≤ Pf := by rw [hPf]; exact Finset.sum_nonneg fun z _ => hD0 z
  have hEeq : gaugedChainAction a S X k - chartAction a S (referenceFieldChain S V) U (rotatedField v V) = E := by
    rw [hE, Finset.sum_sub_distrib, gaugedChainAction_eq_sum]
    congr 1
    exact gaugedChainAction_eq_sum a S _ _
  have hcard : ((highEnergyCells a e S X k).card : ℝ) = Bc := by rw [hBc, hB]
  have hsumPf : ∑ z ∈ cellsFarFromHighEnergy a e S X k,
      relativeEnergy a S z (chartChain (referenceFieldChain S V) U (rotatedField v V))
        (chartGauge (referenceFieldChain S V) U) X k (Γ z) = Pf := by
    rw [hPf, hDdef]
    rfl
  rw [hEeq, hcard, hsumPf]
  have hc1 := min_le_left (e ^ 2 * u / 2) (lam * u / 384)
  have hc2 := min_le_right (e ^ 2 * u / 2) (lam * u / 384)
  have hc0 : 0 ≤ min (e ^ 2 * u / 2) (lam * u / 384) := le_min (by positivity) (by positivity)
  have t1 := mul_le_mul_of_nonneg_right hc1 hBc0
  have t2 := mul_le_mul_of_nonneg_right hc2 hPf0
  have t3 : lam * u / 384 * Pf ≤ lam * u / 384 * Pd := mul_le_mul_of_nonneg_left hPfPd (by positivity)
  rw [mul_add]
  linarith
end YangMills.Construction.BlockAverages.CriticalChainExcess
end
