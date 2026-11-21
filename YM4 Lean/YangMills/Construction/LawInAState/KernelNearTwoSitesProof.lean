import YangMills.Construction.QuaternionicWilsonModel.WhatTheTopGivesAtEveryCouplingProof
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.LawInAState.HatsSumToTheFreeKernelProof
import YangMills.Construction.LawInAState.KernelNearTwoSites
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
private theorem one_le_siteWeight {N : ℕ} (y : TorusFields.TorusSite N) (p : TorusFields.TorusPlaquette N) :
    1 ≤ siteWeight y p :=
  one_le_pow₀ (by have : (0 : ℝ) ≤ TorusFields.supDist p.1 y := Nat.cast_nonneg _; linarith)
private theorem maxwellKernel_eq_kernel (z : Fin 4 → ℤ) (m n r s : Fin 4) :
    LimitForms.maxwellKernel z m n r s = ReflectionKernel.kernel (fun i => (z i : ℝ)) m n r s := rfl
private theorem intNormSq_eq_normSq (z : Fin 4 → ℤ) :
    LimitForms.intNormSq z = ReflectionKernel.normSq fun i => (z i : ℝ) := rfl
private theorem valMinAbs_intCast_of_small {N : ℕ} [NeZero N] (w : ℤ) (h : 2 * |w| < (N : ℤ)) :
    ((w : ZMod N)).valMinAbs = w := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
private theorem abs_coord_le_supDist {N : ℕ} [NeZero N] (x y : TorusFields.TorusSite N) (i : Fin 4) :
    |(((x i - y i).valMinAbs : ℤ) : ℝ)| ≤ (TorusFields.supDist x y : ℝ) := by
  have h : ((x i - y i).valMinAbs).natAbs ≤ TorusFields.supDist x y :=
    Finset.le_sup (f := fun i => ((x i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
  have h2 : (((x i - y i).valMinAbs).natAbs : ℝ) ≤ (TorusFields.supDist x y : ℝ) := by exact_mod_cast h
  rwa [Nat.cast_natAbs, Int.cast_abs] at h2
private theorem supDist_vertex_le_one {N : ℕ} [NeZero N] (s c : TorusFields.TorusSite N) (μ ν : Fin 4)
    (hc : c ∈ TorusFields.plaquetteVertices s μ ν) (hlt : μ < ν) : TorusFields.supDist s c ≤ 1 := by
  have hne : μ ≠ ν := ne_of_lt hlt
  simp only [TorusFields.plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · simp [TorusFields.supDist_self]
  · have := TorusFields.supDist_add_siteOfInt_le s (Pi.single μ 1) 1 fun i => by
      by_cases h : i = μ
      · subst h; simp
      · simp [Pi.single_apply, h]
    rwa [← BlockOffsets.unitStep_eq_siteOfInt] at this
  · have := TorusFields.supDist_add_siteOfInt_le s (Pi.single ν 1) 1 fun i => by
      by_cases h : i = ν
      · subst h; simp
      · simp [Pi.single_apply, h]
    rwa [← BlockOffsets.unitStep_eq_siteOfInt] at this
  · have := TorusFields.supDist_add_siteOfInt_le s (Pi.single μ 1 + Pi.single ν 1) 1 fun i => by
      by_cases h : i = μ
      · subst h; simp [Pi.single_apply, hne]
      · by_cases h' : i = ν
        · subst h'; simp [Pi.single_apply, h]
        · simp [Pi.single_apply, h, h']
    rw [TorusFields.siteOfInt_add, ← BlockOffsets.unitStep_eq_siteOfInt,
      ← BlockOffsets.unitStep_eq_siteOfInt, ← add_assoc] at this
    exact this
abbrev _root_.YangMills.SharedProofs.p36485 := @supDist_vertex_le_one
private theorem normSq_le_of_abs_le {v : Fin 4 → ℝ} {s : ℝ} (h : ∀ i, |v i| ≤ s) :
    ReflectionKernel.normSq v ≤ 4 * s ^ 2 := by apply _root_.YangMills.Construction.NonGaussianLimits.sum_sq_le_four_mul_sq <;> assumption
private theorem normSq_le_two_mul_add (v v' : Fin 4 → ℝ) :
    ReflectionKernel.normSq v ≤ 2 * ReflectionKernel.normSq v' + 2 * ReflectionKernel.normSq (v - v') := by
  simp only [ReflectionKernel.normSq, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.sub_apply]
  exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (v i - 2 * (v i - v' i))]
set_option maxHeartbeats 4000000 in
private theorem abs_sub_kernel_le_of_near (hR : ReflectionKernel.KernelEstimates) {N : ℕ} [NeZero N]
    (T : TorusFields.TorusPlaquette N → TorusFields.TorusPlaquette N → ℝ)
    (Ck cT n : ℝ) (R : ℕ) (o : TorusFields.TorusSite N) (hn : 64 ≤ n) (hN : 64 * n ≤ N)
    (hTn : ∀ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o ((R : ℝ) / 8)),
      ∀ p' ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o ((R : ℝ) / 8)),
      ∀ z : Fin 4 → ℤ, (∀ i, z i = ((p.1 - p'.1) i).valMinAbs) → z ≠ 0 →
        |T p p' - LimitForms.maxwellKernel z p.2.1 p.2.2 p'.2.1 p'.2.2| ≤
          Ck * ((1 + Real.sqrt (LimitForms.intNormSq z)) ^ 5)⁻¹ + Ck * ((R : ℝ) ^ 4)⁻¹)
    (y w : TorusFields.TorusSite N) (hy : (TorusFields.supDist y o : ℝ) ≤ (R : ℝ) / 8 - n + 2)
    (hw : (TorusFields.supDist w o : ℝ) ≤ (R : ℝ) / 8 - n + 2)
    (hD : ∀ i, |(minimalSiteDiff y w i : ℝ)| ≤ 13 * n)
    (hD2 : n ^ 2 / 4 ≤ ReflectionKernel.normSq fun i => (minimalSiteDiff y w i : ℝ))
    (p p' : TorusFields.TorusPlaquette N) (hp : p.2.1 < p.2.2) (hp' : p'.2.1 < p'.2.2) (hTb : |T p p'| ≤ cT) :
    |T p p' - ReflectionKernel.kernel (fun i => (minimalSiteDiff y w i : ℝ)) p.2.1 p.2.2 p'.2.1 p'.2.2| ≤
      (1024 * |Ck| + 192000 + (|cT| + 1) * 16 ^ 5) *
        (((n ^ 5)⁻¹ + ((R : ℝ) ^ 4)⁻¹) * (siteWeight y p * siteWeight w p')) := by
  set a : ℝ := (TorusFields.supDist p.1 y : ℝ) with ha
  set b : ℝ := (TorusFields.supDist p'.1 w : ℝ) with hb
  set v : Fin 4 → ℝ := fun i => (minimalSiteDiff y w i : ℝ) with hv
  have hsqv : 0 < ReflectionKernel.normSq v := by
    have : 0 < n ^ 2 / 4 := by positivity
    linarith
  have hv0 : v ≠ 0 := by
    rintro h0
    rw [h0] at hsqv
    simp [ReflectionKernel.normSq] at hsqv
  obtain ⟨hsize, hmove, -⟩ := hR
  have hWy : 1 ≤ siteWeight y p := one_le_siteWeight _ _
  have hWw : 1 ≤ siteWeight w p' := one_le_siteWeight _ _
  have hWW : 1 ≤ siteWeight y p * siteWeight w p' := one_le_mul_of_one_le_of_one_le hWy hWw
  have hinvn : 0 < (n ^ 5)⁻¹ := by positivity
  have hinvR : 0 ≤ ((R : ℝ) ^ 4)⁻¹ := by positivity
  by_cases hnear : a ≤ n / 16 ∧ b ≤ n / 16
  · obtain ⟨han, hbn⟩ := hnear
    have hin : ∀ (q : TorusFields.TorusPlaquette N) (s : TorusFields.TorusSite N), q.2.1 < q.2.2 →
        (TorusFields.supDist q.1 s : ℝ) ≤ n / 16 →
        (TorusFields.supDist s o : ℝ) ≤ (R : ℝ) / 8 - n + 2 →
        q ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall o ((R : ℝ) / 8)) := by
      intro q s hq h1 h2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, fun c hc => ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have t1 : (TorusFields.supDist q.1 c : ℝ) ≤ 1 := by
        exact_mod_cast supDist_vertex_le_one q.1 c _ _ hc hq
      have t2 : TorusFields.supDist c o ≤ TorusFields.supDist c q.1 + TorusFields.supDist q.1 o :=
        TorusFields.supDist_triangle _ _ _
      have t3 : TorusFields.supDist q.1 o ≤ TorusFields.supDist q.1 s + TorusFields.supDist s o :=
        TorusFields.supDist_triangle _ _ _
      rw [TorusFields.supDist_comm c q.1] at t2
      have t2' : (TorusFields.supDist c o : ℝ) ≤
          (TorusFields.supDist q.1 c : ℝ) + (TorusFields.supDist q.1 o : ℝ) := by exact_mod_cast t2
      have t3' : (TorusFields.supDist q.1 o : ℝ) ≤
          (TorusFields.supDist q.1 s : ℝ) + (TorusFields.supDist s o : ℝ) := by exact_mod_cast t3
      linarith
    have hpin := hin p y hp han hy
    have hpin' := hin p' w hp' hbn hw
    set t : Fin 4 → ℤ := fun i => (p.1 i - y i).valMinAbs with ht
    set t' : Fin 4 → ℤ := fun i => (p'.1 i - w i).valMinAbs with ht'
    set z : Fin 4 → ℤ := fun i => minimalSiteDiff y w i + t i - t' i with hz
    have hta : ∀ i, |(t i : ℝ)| ≤ a := fun i => abs_coord_le_supDist _ _ i
    have htb : ∀ i, |(t' i : ℝ)| ≤ b := fun i => abs_coord_le_supDist _ _ i
    have hzz : ∀ i, z i = ((p.1 - p'.1) i).valMinAbs := by
      intro i
      have hcast : (((z i : ℤ)) : ZMod N) = (p.1 - p'.1) i := by
        simp only [hz, ht, ht', minimalSiteDiff]
        push_cast
        simp only [ZMod.coe_valMinAbs, Pi.sub_apply]
        ring
      rw [← hcast]
      refine (valMinAbs_intCast_of_small _ ?_).symm
      have b1 := abs_le.mp (hD i)
      have b2 := abs_le.mp (hta i)
      have b3 := abs_le.mp (htb i)
      have h1 : 2 * |(z i : ℝ)| < (N : ℝ) := by
        have : |(z i : ℝ)| ≤ 14 * n := by
          simp only [hz]
          push_cast
          rw [abs_le]
          constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2]
        linarith
      have h3 : ((2 * |z i| : ℤ) : ℝ) < (((N : ℕ) : ℤ) : ℝ) := by
        push_cast
        push_cast at h1
        exact h1
      exact_mod_cast h3
    set v' : Fin 4 → ℝ := fun i => (z i : ℝ) with hv'
    have hdiff : ∀ i, |(v - v') i| ≤ a + b := by
      intro i
      have b2 := abs_le.mp (hta i)
      have b3 := abs_le.mp (htb i)
      simp only [Pi.sub_apply, hv, hv', hz]
      push_cast
      rw [abs_le]
      constructor <;> linarith [b2.1, b2.2, b3.1, b3.2]
    have hsd : ReflectionKernel.normSq (v - v') ≤ 4 * (a + b) ^ 2 := normSq_le_of_abs_le hdiff
    have hab2 : (a + b) ^ 2 ≤ n ^ 2 / 64 := by nlinarith
    have hcond : 4 * ReflectionKernel.normSq (v - v') ≤ ReflectionKernel.normSq v := by nlinarith
    have hsv' : n ^ 2 / 16 ≤ ReflectionKernel.normSq v' := by
      have := normSq_le_two_mul_add v v'
      nlinarith
    have hv'0 : 0 < ReflectionKernel.normSq v' := by
      have : 0 < n ^ 2 / 16 := by positivity
      linarith
    have hz0 : z ≠ 0 := by
      rintro h0
      have : v' = 0 := by
        funext i
        simp [hv', h0]
      rw [this] at hv'0
      simp [ReflectionKernel.normSq] at hv'0
    have hk := hTn p hpin p' hpin' z hzz hz0
    rw [maxwellKernel_eq_kernel, intNormSq_eq_normSq] at hk
    have hroot : n / 4 ≤ Real.sqrt (ReflectionKernel.normSq v') := by
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith
    have hpow : (n / 4) ^ 5 ≤ (1 + Real.sqrt (ReflectionKernel.normSq v')) ^ 5 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 5
    have hinv : ((1 + Real.sqrt (ReflectionKernel.normSq v')) ^ 5)⁻¹ ≤ 1024 * (n ^ 5)⁻¹ := by
      have : ((1 + Real.sqrt (ReflectionKernel.normSq v')) ^ 5)⁻¹ ≤ ((n / 4) ^ 5)⁻¹ :=
        inv_anti₀ (by positivity) hpow
      refine this.trans (le_of_eq ?_)
      field_simp
      norm_num
    have hm := hmove v v' p.2.1 p.2.2 p'.2.1 p'.2.2 hv0 hcond
    have hr1 : n / 2 ≤ Real.sqrt (ReflectionKernel.normSq v) := by
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith
    have hr2 : Real.sqrt (ReflectionKernel.normSq (v - v')) ≤ 2 * (a + b) := by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      nlinarith
    have hm' : |ReflectionKernel.kernel v p.2.1 p.2.2 p'.2.1 p'.2.2 -
        ReflectionKernel.kernel v' p.2.1 p.2.2 p'.2.1 p'.2.2| ≤ 192000 * (a + b) * (n ^ 5)⁻¹ := by
      refine hm.trans ?_
      have h5 : (n / 2) ^ 5 ≤ Real.sqrt (ReflectionKernel.normSq v) ^ 5 :=
        pow_le_pow_left₀ (by positivity) hr1 5
      calc _ ≤ (3000 * (2 * (a + b))) / (n / 2) ^ 5 :=
            div_le_div₀ (by positivity) (by linarith) (by positivity) h5
        _ = _ := by field_simp; ring
    have htri := abs_sub_le (T p p') (ReflectionKernel.kernel v' p.2.1 p.2.2 p'.2.1 p'.2.2)
      (ReflectionKernel.kernel v p.2.1 p.2.2 p'.2.1 p'.2.2)
    rw [abs_sub_comm (ReflectionKernel.kernel v' _ _ _ _)] at htri
    have hk' : |T p p' - ReflectionKernel.kernel v' p.2.1 p.2.2 p'.2.1 p'.2.2| ≤
        |Ck| * (1024 * (n ^ 5)⁻¹) + |Ck| * ((R : ℝ) ^ 4)⁻¹ := by
      refine hk.trans (add_le_add ?_ ?_)
      · exact (mul_le_mul_of_nonneg_right (le_abs_self Ck) (by positivity)).trans
          (mul_le_mul_of_nonneg_left hinv (abs_nonneg _))
      · exact mul_le_mul_of_nonneg_right (le_abs_self Ck) hinvR
    have hwa : (1 + a + b) ≤ siteWeight y p * siteWeight w p' := by
      have k1 : 1 + a ≤ siteWeight y p := by
        have : (1 + a) ^ 1 ≤ (1 + a) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
        simpa [siteWeight] using this
      have k2 : 1 + b ≤ siteWeight w p' := by
        have : (1 + b) ^ 1 ≤ (1 + b) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
        simpa [siteWeight] using this
      calc 1 + a + b ≤ (1 + a) * (1 + b) := by nlinarith
        _ ≤ _ := mul_le_mul k1 k2 (by linarith) (by linarith)
    set WW := siteWeight y p * siteWeight w p' with hWWd
    have hCk := abs_nonneg Ck
    have hcT := abs_nonneg cT
    have f1 : |Ck| * (1024 * (n ^ 5)⁻¹) ≤ 1024 * |Ck| * ((n ^ 5)⁻¹ * WW) := by
      have : (n ^ 5)⁻¹ * 1 ≤ (n ^ 5)⁻¹ * WW := mul_le_mul_of_nonneg_left hWW hinvn.le
      nlinarith
    have f2 : |Ck| * ((R : ℝ) ^ 4)⁻¹ ≤ 1024 * |Ck| * (((R : ℝ) ^ 4)⁻¹ * WW) := by
      have : ((R : ℝ) ^ 4)⁻¹ * 1 ≤ ((R : ℝ) ^ 4)⁻¹ * WW := mul_le_mul_of_nonneg_left hWW hinvR
      nlinarith
    have f3 : 192000 * (a + b) * (n ^ 5)⁻¹ ≤ 192000 * ((n ^ 5)⁻¹ * WW) := by
      have : (n ^ 5)⁻¹ * (a + b) ≤ (n ^ 5)⁻¹ * WW :=
        mul_le_mul_of_nonneg_left (by linarith) hinvn.le
      nlinarith
    have f4 : 0 ≤ ((R : ℝ) ^ 4)⁻¹ * WW := by positivity
    have f5 : 0 ≤ (n ^ 5)⁻¹ * WW := by positivity
    calc _ ≤ |Ck| * (1024 * (n ^ 5)⁻¹) + |Ck| * ((R : ℝ) ^ 4)⁻¹ + 192000 * (a + b) * (n ^ 5)⁻¹ := by
          linarith
      _ ≤ 1024 * |Ck| * ((n ^ 5)⁻¹ * WW) + 1024 * |Ck| * (((R : ℝ) ^ 4)⁻¹ * WW) +
          192000 * ((n ^ 5)⁻¹ * WW) := by linarith
      _ ≤ _ := by
        nlinarith [mul_nonneg (by positivity : 0 ≤ (|cT| + 1) * 16 ^ 5) f4,
          mul_nonneg (by positivity : 0 ≤ (|cT| + 1) * 16 ^ 5) f5, mul_nonneg hCk f4, mul_nonneg hCk f5]
  · have hfar : n / 16 ≤ 1 + a + b := by
      by_contra hcon
      push_neg at hcon
      exact hnear ⟨by linarith, by linarith⟩
    have hWbig : (n / 16) ^ 5 ≤ siteWeight y p * siteWeight w p' := by
      have k1 : (1 + a) ^ 5 * (1 + b) ^ 5 = ((1 + a) * (1 + b)) ^ 5 := by ring
      simp only [siteWeight]
      rw [← ha, ← hb, k1]
      refine pow_le_pow_left₀ (by positivity) ?_ 5
      nlinarith
    have hsz := hsize v p.2.1 p.2.2 p'.2.1 p'.2.2 hv0
    have hsz' : 18 / ReflectionKernel.normSq v ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (n ^ 2 / 4) ^ 2 ≤ ReflectionKernel.normSq v ^ 2 := pow_le_pow_left₀ (by positivity) hD2 2
      nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 64) hn 2]
    have hdiff : |T p p' - ReflectionKernel.kernel v p.2.1 p.2.2 p'.2.1 p'.2.2| ≤ |cT| + 1 := by
      have := abs_sub (T p p') (ReflectionKernel.kernel v p.2.1 p.2.2 p'.2.1 p'.2.2)
      linarith [le_abs_self cT]
    have hq : 1 ≤ 16 ^ 5 * ((n ^ 5)⁻¹ * (siteWeight y p * siteWeight w p')) := by
      have h1 : (n / 16) ^ 5 * (16 ^ 5 * (n ^ 5)⁻¹) = 1 := by
        field_simp
      have h2 : 0 ≤ 16 ^ 5 * (n ^ 5)⁻¹ := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hWbig h2]
    have hcT := abs_nonneg cT
    have hCk := abs_nonneg Ck
    set WW := siteWeight y p * siteWeight w p' with hWWd
    have f4 : 0 ≤ ((R : ℝ) ^ 4)⁻¹ * WW := by positivity
    have f5 : 0 ≤ (n ^ 5)⁻¹ * WW := by positivity
    calc _ ≤ (|cT| + 1) * 1 := by linarith
      _ ≤ (|cT| + 1) * (16 ^ 5 * ((n ^ 5)⁻¹ * WW)) := mul_le_mul_of_nonneg_left hq (by positivity)
      _ ≤ _ := by
        nlinarith [mul_nonneg (by positivity : 0 ≤ (|cT| + 1) * 16 ^ 5) f4,
          mul_nonneg hCk f4, mul_nonneg hCk f5]
theorem maxwellKernelNearSites_of_kernelEstimates (hR : ReflectionKernel.KernelEstimates) :
    maxwellKernelNearSitesStatement :=
  fun T Ck cT n R o hn hN hTn y w hy hw hD hD2 p p' hp hp' hTb =>
    abs_sub_kernel_le_of_near hR T Ck cT n R o hn hN hTn y w hy hw hD hD2 p p' hp hp' hTb
end YangMills.Construction.StateLaws
end
