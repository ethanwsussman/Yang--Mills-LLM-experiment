import YangMills.Construction.EuclideanFunctionals.OperatorsOfThePlaneSemigroupExpansionAndProductsOverTheWedgeProof
import YangMills.Construction.ForwardTube.ArgumentsOfTheGramKernel
import Mathlib
set_option autoImplicit false
open Complex (I)
open ComplexConjugate
noncomputable section
namespace YangMills.Construction.ForwardTube
namespace GramKernelArgs
variable {n n' : ℕ}
theorem eq_of_lightCone {u v : ℂ × ℂ} (hp : lightConePlus u = lightConePlus v)
    (hm : lightConeMinus u = lightConeMinus v) : u = v := by apply _root_.YangMills.Construction.EuclideanFunctionals.TubeSemigroup.pair_ext_lightCone <;> assumption
theorem lightConePlus_sub (p q : ℂ × ℂ) :
    lightConePlus (p - q) = lightConePlus p - lightConePlus q := by
  simp only [lightConePlus, Prod.fst_sub, Prod.snd_sub]
  ring
theorem lightConeMinus_sub (p q : ℂ × ℂ) :
    lightConeMinus (p - q) = lightConeMinus p - lightConeMinus q := by
  simp only [lightConeMinus, Prod.fst_sub, Prod.snd_sub]
  ring
theorem lightConePlus_add (p q : ℂ × ℂ) :
    lightConePlus (p + q) = lightConePlus p + lightConePlus q := by apply _root_.YangMills.Construction.EuclideanFunctionals.TubeSemigroup.lightConePlus_add <;> assumption
theorem lightConeMinus_add (p q : ℂ × ℂ) :
    lightConeMinus (p + q) = lightConeMinus p + lightConeMinus q := by apply _root_.YangMills.Construction.EuclideanFunctionals.TubeSemigroup.lightConeMinus_add <;> assumption
theorem lightConePlus_tubeStar (v : ℂ × ℂ) :
    lightConePlus (tubeStar v) = conj (lightConePlus v) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TubeSemigroup.lightConePlus_tubeStar_eq_conj <;> assumption
theorem lightConeMinus_tubeStar (v : ℂ × ℂ) :
    lightConeMinus (tubeStar v) = conj (lightConeMinus v) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TubeSemigroup.lightConeMinus_tubeStar_eq_conj <;> assumption
theorem tubeStar_mem {v : ℂ × ℂ} (hv : v ∈ forwardTube) : tubeStar v ∈ forwardTube := by
  refine ⟨?_, ?_⟩
  · rw [lightConePlus_tubeStar, Complex.conj_re]
    exact hv.1
  · rw [lightConeMinus_tubeStar, Complex.conj_re]
    exact hv.2
theorem add_mem_forwardTube {u v : ℂ × ℂ} (hu : u ∈ forwardTube) (hv : v ∈ forwardTube) :
    u + v ∈ forwardTube := by
  refine ⟨?_, ?_⟩
  · rw [lightConePlus_add, Complex.add_re]
    exact add_pos hu.1 hv.1
  · rw [lightConeMinus_add, Complex.add_re]
    exact add_pos hu.2 hv.2
theorem embedPlane_sub (p q : RealPlane) : embedPlane (p - q) = embedPlane p - embedPlane q := by
  simp [embedPlane]
theorem embedPlane_mem_iff (y : RealPlane) : embedPlane y ∈ forwardTube ↔ 0 < y 0 := by
  simp [forwardTube, lightConePlus, lightConeMinus, embedPlane]
theorem tubeStar_embedPlane (y : RealPlane) :
    tubeStar (embedPlane y) = embedPlane (-RealPlane.reflectFirst y) := by
  simp [tubeStar, embedPlane, RealPlane.reflectFirst]
theorem reflectFirst_apply_zero (v : RealPlane) : RealPlane.reflectFirst v 0 = -v 0 := by
  simp [RealPlane.reflectFirst]
theorem strictMono_of_succ {m : ℕ} (f : Fin m → ℝ)
    (h : ∀ (i : ℕ) (hi : i + 1 < m), f ⟨i, by omega⟩ < f ⟨i + 1, hi⟩) : StrictMono f := by
  cases m with
  | zero =>
    intro i
    exact i.elim0
  | succ m => exact Fin.strictMono_iff_lt_succ.2 fun i => h i.1 (by omega)
theorem realTuple_mem_successiveDomain_iff (a : Fin n → RealPlane) :
    realTuple a ∈ successiveDomain n ↔
      (∀ h : 0 < n, 0 < a ⟨0, h⟩ 0) ∧ StrictMono fun i => a i 0 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun h => (embedPlane_mem_iff _).1 (h₁ h), strictMono_of_succ _ fun i hi => ?_⟩
    have h₃ : embedPlane (a ⟨i + 1, hi⟩ - a ⟨i, by omega⟩) ∈ forwardTube := by
      rw [embedPlane_sub]
      exact h₂ i hi
    have h₄ := (embedPlane_mem_iff _).1 h₃
    simpa [sub_pos] using h₄
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun h => (embedPlane_mem_iff _).2 (h₁ h), fun i hi => ?_⟩
    show embedPlane _ - embedPlane _ ∈ forwardTube
    rw [← embedPlane_sub, embedPlane_mem_iff]
    have h₃ : a ⟨i, by omega⟩ 0 < a ⟨i + 1, hi⟩ 0 := h₂ (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
    simpa [sub_pos] using h₃
theorem firstCoord_pos {a : Fin n → RealPlane} (h₀ : ∀ h : 0 < n, 0 < a ⟨0, h⟩ 0)
    (hm : StrictMono fun i => a i 0) (i : Fin n) : 0 < a i 0 :=
  lt_of_lt_of_le (h₀ i.pos) (hm.monotone (show (⟨0, i.pos⟩ : Fin n) ≤ i from Nat.zero_le _))
theorem inter_range_realTuple (S : Set (Fin n → RealPlane))
    (hS : ∀ a, realTuple a ∈ successiveDomain n ↔ a ∈ S) :
    successiveDomain n ∩ Set.range (realTuple (n := n)) = realTuple '' S := by
  ext x
  constructor
  · rintro ⟨hx, a, rfl⟩
    exact ⟨a, (hS a).1 hx, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(hS a).2 ha, a, rfl⟩
theorem sub_mem_of_succ {x : Fin n → ℂ × ℂ} (hx : x ∈ successiveDomain n) (i j : Fin n)
    (hij : (j : ℕ) = i + 1) : x j - x i ∈ forwardTube := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  obtain rfl : j = i + 1 := hij
  exact hx.2 i hj
theorem gramKernelArgs_of_lt (x : Fin n → ℂ × ℂ) (y : Fin n' → ℂ × ℂ) (k : Fin (n + n' - 1))
    (h : (k : ℕ) + 1 < n) :
    gramKernelArgs x y k = tubeStar (x ⟨n - 1 - k, by omega⟩ - x ⟨n - 2 - k, by omega⟩) :=
  dif_pos h
theorem gramKernelArgs_of_eq (x : Fin n → ℂ × ℂ) (y : Fin n' → ℂ × ℂ) (k : Fin (n + n' - 1))
    (h : (k : ℕ) + 1 = n) :
    gramKernelArgs x y k = tubeStar (x ⟨0, by omega⟩) + y ⟨0, by omega⟩ := by
  unfold gramKernelArgs
  rw [dif_neg (by omega), dif_pos h]
theorem gramKernelArgs_of_gt (x : Fin n → ℂ × ℂ) (y : Fin n' → ℂ × ℂ) (k : Fin (n + n' - 1))
    (h : n < (k : ℕ) + 1) :
    gramKernelArgs x y k = y ⟨k + 1 - n, by omega⟩ - y ⟨k - n, by omega⟩ := by
  unfold gramKernelArgs
  rw [dif_neg (by omega), dif_neg (by omega)]
theorem gramKernelArgs_mem {x : Fin n → ℂ × ℂ} {y : Fin n' → ℂ × ℂ}
    (hx : x ∈ successiveDomain n) (hy : y ∈ successiveDomain n') (k : Fin (n + n' - 1)) :
    gramKernelArgs x y k ∈ forwardTube := by
  rcases lt_trichotomy ((k : ℕ) + 1) n with h | h | h
  · rw [gramKernelArgs_of_lt x y k h]
    exact tubeStar_mem (sub_mem_of_succ hx _ _ (show n - 1 - (k : ℕ) = n - 2 - k + 1 by omega))
  · rw [gramKernelArgs_of_eq x y k h]
    exact add_mem_forwardTube (tubeStar_mem (hx.1 _)) (hy.1 _)
  · rw [gramKernelArgs_of_gt x y k h]
    exact sub_mem_of_succ hy _ _ (show (k : ℕ) + 1 - n = k - n + 1 by omega)
theorem reflectAppend_left (a : Fin n → RealPlane) (b : Fin n' → RealPlane) (i : ℕ) (h : i < n) :
    reflectAppend a b ⟨i, by omega⟩ = RealPlane.reflectFirst (a ⟨n - 1 - i, by omega⟩) := by
  have e : (⟨i, by omega⟩ : Fin (n + n')) = Fin.castAdd n' ⟨i, h⟩ := rfl
  have r : Fin.rev (⟨i, h⟩ : Fin n) = ⟨n - 1 - i, by omega⟩ :=
    Fin.ext (by rw [Fin.val_rev]; show n - (i + 1) = n - 1 - i; omega)
  rw [e, reflectAppend, Fin.append_left, r]
theorem reflectAppend_right (a : Fin n → RealPlane) (b : Fin n' → RealPlane) (j : ℕ)
    (h₁ : n ≤ j) (h₂ : j < n + n') :
    reflectAppend a b ⟨j, h₂⟩ = b ⟨j - n, by omega⟩ := by
  have e : (⟨j, h₂⟩ : Fin (n + n')) = Fin.natAdd n ⟨j - n, by omega⟩ :=
    Fin.ext (by show j = n + (j - n); omega)
  rw [e, reflectAppend, Fin.append_right]
theorem tubeStar_embedPlane_sub (u v : RealPlane) :
    tubeStar (embedPlane u - embedPlane v) =
      embedPlane (RealPlane.reflectFirst v - RealPlane.reflectFirst u) := by
  rw [← embedPlane_sub, tubeStar_embedPlane]
  congr 1
  ext i
  fin_cases i <;> simp [RealPlane.reflectFirst]
  ring
theorem tubeStar_embedPlane_add (u v : RealPlane) :
    tubeStar (embedPlane u) + embedPlane v = embedPlane (v - RealPlane.reflectFirst u) := by
  rw [tubeStar_embedPlane, embedPlane_sub]
  simp [embedPlane, add_comm, sub_eq_add_neg]
theorem gramKernelArgs_realTuple (a : Fin n → RealPlane) (b : Fin n' → RealPlane)
    (k : Fin (n + n' - 1)) :
    gramKernelArgs (realTuple a) (realTuple b) k =
      embedPlane (RealPlane.successiveDifferences (reflectAppend a b) k) := by
  show _ = embedPlane (reflectAppend a b ⟨k + 1, by omega⟩ - reflectAppend a b ⟨k, by omega⟩)
  rcases lt_trichotomy ((k : ℕ) + 1) n with h | h | h
  · rw [gramKernelArgs_of_lt _ _ k h, reflectAppend_left a b (k + 1) h,
      reflectAppend_left a b k (by omega)]
    have e : (⟨n - 1 - ((k : ℕ) + 1), by omega⟩ : Fin n) = ⟨n - 2 - k, by omega⟩ :=
      Fin.ext (show n - 1 - ((k : ℕ) + 1) = n - 2 - k by omega)
    rw [e]
    exact tubeStar_embedPlane_sub _ _
  · rw [gramKernelArgs_of_eq _ _ k h, reflectAppend_right a b (k + 1) (by omega) (by omega),
      reflectAppend_left a b k (by omega)]
    have e₁ : (⟨n - 1 - (k : ℕ), by omega⟩ : Fin n) = ⟨0, by omega⟩ :=
      Fin.ext (show n - 1 - (k : ℕ) = 0 by omega)
    have e₂ : (⟨(k : ℕ) + 1 - n, by omega⟩ : Fin n') = ⟨0, by omega⟩ :=
      Fin.ext (show (k : ℕ) + 1 - n = 0 by omega)
    rw [e₁, e₂]
    exact tubeStar_embedPlane_add _ _
  · rw [gramKernelArgs_of_gt _ _ k h, reflectAppend_right a b (k + 1) (by omega) (by omega),
      reflectAppend_right a b k (by omega) (by omega), embedPlane_sub]
    rfl
theorem reflectAppend_castAdd_rev (a : Fin n → RealPlane) (b : Fin n' → RealPlane) (i : Fin n) :
    reflectAppend a b (Fin.castAdd n' (Fin.rev i)) 0 = -a i 0 := by
  rw [reflectAppend, Fin.append_left]
  simp [reflectFirst_apply_zero]
theorem reflectAppend_natAdd (a : Fin n → RealPlane) (b : Fin n' → RealPlane) (j : Fin n') :
    reflectAppend a b (Fin.natAdd n j) 0 = b j 0 := by
  rw [reflectAppend, Fin.append_right]
theorem reflectAppend_strictMono {a : Fin n → RealPlane} {b : Fin n' → RealPlane}
    (ha₀ : ∀ h : 0 < n, 0 < a ⟨0, h⟩ 0) (ha : StrictMono fun i => a i 0)
    (hb₀ : ∀ h : 0 < n', 0 < b ⟨0, h⟩ 0) (hb : StrictMono fun i => b i 0) :
    StrictMono fun k => reflectAppend a b k 0 := by
  refine strictMono_of_succ _ fun i hi => ?_
  show reflectAppend a b ⟨i, by omega⟩ 0 < reflectAppend a b ⟨i + 1, hi⟩ 0
  rcases lt_trichotomy (i + 1) n with h | h | h
  · rw [reflectAppend_left a b (i + 1) h, reflectAppend_left a b i (by omega),
      reflectFirst_apply_zero, reflectFirst_apply_zero]
    exact neg_lt_neg (ha (Fin.mk_lt_mk.2 (by omega)))
  · rw [reflectAppend_right a b (i + 1) (by omega) hi, reflectAppend_left a b i (by omega),
      reflectFirst_apply_zero]
    have h₁ := firstCoord_pos ha₀ ha ⟨n - 1 - i, by omega⟩
    have h₂ := firstCoord_pos hb₀ hb ⟨i + 1 - n, by omega⟩
    linarith
  · rw [reflectAppend_right a b (i + 1) (by omega) hi,
      reflectAppend_right a b i (by omega) (by omega)]
    exact hb (Fin.mk_lt_mk.2 (by omega))
theorem lightConePlus_imagBoost (s : ℝ) (v : ℂ × ℂ) :
    lightConePlus (imagBoost s v) = ((Real.exp (-s) : ℝ) : ℂ) * lightConePlus v := by
  rw [imagBoost, lightConePlus_complexBoost, ← mul_assoc I, Complex.I_mul_I]
  push_cast
  congr 2
  ring
theorem lightConeMinus_imagBoost (s : ℝ) (v : ℂ × ℂ) :
    lightConeMinus (imagBoost s v) = ((Real.exp s : ℝ) : ℂ) * lightConeMinus v := by
  rw [imagBoost, lightConeMinus_complexBoost, ← mul_assoc I, Complex.I_mul_I]
  push_cast
  congr 2
  ring
theorem imagBoost_imagBoost_neg (s : ℝ) (v : ℂ × ℂ) : imagBoost s (imagBoost (-s) v) = v := by
  refine eq_of_lightCone ?_ ?_
  · rw [lightConePlus_imagBoost, lightConePlus_imagBoost, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.exp_add]
    simp
  · rw [lightConeMinus_imagBoost, lightConeMinus_imagBoost, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.exp_add]
    simp
theorem imagBoost_sub (s : ℝ) (p q : ℂ × ℂ) :
    imagBoost s (p - q) = imagBoost s p - imagBoost s q := by
  refine eq_of_lightCone ?_ ?_
  · simp only [lightConePlus_imagBoost, lightConePlus_sub, mul_sub]
  · simp only [lightConeMinus_imagBoost, lightConeMinus_sub, mul_sub]
theorem imagBoost_add (s : ℝ) (p q : ℂ × ℂ) :
    imagBoost s (p + q) = imagBoost s p + imagBoost s q := by
  refine eq_of_lightCone ?_ ?_
  · simp only [lightConePlus_imagBoost, lightConePlus_add, mul_add]
  · simp only [lightConeMinus_imagBoost, lightConeMinus_add, mul_add]
theorem imagBoost_tubeStar (s : ℝ) (v : ℂ × ℂ) :
    imagBoost s (tubeStar v) = tubeStar (imagBoost s v) := by
  refine eq_of_lightCone ?_ ?_
  · simp only [lightConePlus_imagBoost, lightConePlus_tubeStar, map_mul, Complex.conj_ofReal]
  · simp only [lightConeMinus_imagBoost, lightConeMinus_tubeStar, map_mul, Complex.conj_ofReal]
theorem imagBoostTuple_image (s : ℝ) (n : ℕ) :
    imagBoostTuple s '' successiveDomain n = successiveDomain n := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact imagBoostTuple_mem s hz
  · intro hx
    exact ⟨imagBoostTuple (-s) x, imagBoostTuple_mem (-s) hx,
      funext fun i => imagBoost_imagBoost_neg s (x i)⟩
theorem gramKernelArgs_imagBoostTuple (s : ℝ) (x : Fin n → ℂ × ℂ) (y : Fin n' → ℂ × ℂ)
    (k : Fin (n + n' - 1)) :
    gramKernelArgs (imagBoostTuple s x) (imagBoostTuple s y) k =
      imagBoost s (gramKernelArgs x y k) := by
  rcases lt_trichotomy ((k : ℕ) + 1) n with h | h | h
  · rw [gramKernelArgs_of_lt _ _ k h, gramKernelArgs_of_lt x y k h, imagBoost_tubeStar,
      imagBoost_sub]
    rfl
  · rw [gramKernelArgs_of_eq _ _ k h, gramKernelArgs_of_eq x y k h, imagBoost_add,
      imagBoost_tubeStar]
    rfl
  · rw [gramKernelArgs_of_gt _ _ k h, gramKernelArgs_of_gt x y k h, imagBoost_sub]
    rfl
theorem tubeStar_complexBoost (t : ℝ) (v : ℂ × ℂ) :
    tubeStar (complexBoost (t : ℂ) v) = complexBoost ((-t : ℝ) : ℂ) (tubeStar v) := by
  refine eq_of_lightCone ?_ ?_
  · rw [lightConePlus_tubeStar, lightConePlus_complexBoost, lightConePlus_complexBoost,
      lightConePlus_tubeStar, map_mul, ← Complex.exp_conj]
    congr 2
    simp
  · rw [lightConeMinus_tubeStar, lightConeMinus_complexBoost, lightConeMinus_complexBoost,
      lightConeMinus_tubeStar, map_mul, ← Complex.exp_conj]
    congr 2
    simp
theorem complexBoost_image_ne (t : ℝ) (ht : ∀ m : ℤ, t ≠ m * (2 * Real.pi)) :
    complexBoost (t : ℂ) '' forwardTube ≠ forwardTube := by
  intro he
  have key : ∀ w : ℂ, 0 < w.re → 0 < Real.cos t * w.re - Real.sin t * w.im := by
    intro w hw
    have hv : ofLightConeCoords w 1 ∈ forwardTube :=
      ⟨by rw [lightConePlus_ofLightConeCoords]; exact hw,
        by rw [lightConeMinus_ofLightConeCoords]; simp⟩
    have h₁ := (he.subset (Set.mem_image_of_mem _ hv)).1
    rw [lightConePlus_complexBoost, lightConePlus_ofLightConeCoords, mul_comm I,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at h₁
    simpa [Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re] using h₁
  have hc : 0 < Real.cos t := by simpa using key 1 (by simp)
  have hs : Real.sin t = 0 := by
    by_contra hne
    have h₂ := key ⟨1, (Real.cos t + 1) / Real.sin t⟩ (by simp)
    have h₃ : Real.sin t * ((Real.cos t + 1) / Real.sin t) = Real.cos t + 1 := by
      field_simp
    simp only [h₃] at h₂
    linarith
  have h₁ : Real.cos t = 1 := by
    have h₂ := Real.sin_sq_add_cos_sq t
    rw [hs] at h₂
    nlinarith
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff t).1 h₁
  exact ht m hm.symm
end GramKernelArgs
open GramKernelArgs in
theorem gramKernelArgsFacts_holds : GramKernelArgsFacts := by
  refine ⟨fun n hn => ⟨?_, ?_⟩, fun n n' _ x hx y hy k => gramKernelArgs_mem hx hy k, ?_,
    ⟨fun s n _ => imagBoostTuple_image s n,
      fun s n n' _ x _ y _ k => gramKernelArgs_imagBoostTuple s x y k⟩,
    tubeStar_complexBoost, complexBoost_image_ne⟩
  · exact inter_range_realTuple _ fun a => (realTuple_mem_successiveDomain_iff a).trans
      ⟨fun h => ⟨h.1 hn, h.2⟩, fun h => ⟨fun _ => h.1, h.2⟩⟩
  · exact inter_range_realTuple _ fun a => (realTuple_mem_successiveDomain_iff a).trans
      ⟨fun h => ⟨firstCoord_pos h.1 h.2, h.2⟩, fun h => ⟨fun _ => h.1 _, h.2⟩⟩
  · intro n n' _ a b ha hb
    obtain ⟨ha₀, ham⟩ := (realTuple_mem_successiveDomain_iff a).1 ha
    obtain ⟨hb₀, hbm⟩ := (realTuple_mem_successiveDomain_iff b).1 hb
    refine ⟨gramKernelArgs_realTuple a b, reflectAppend_castAdd_rev a b, reflectAppend_natAdd a b,
      reflectAppend_strictMono ha₀ ham hb₀ hbm, fun i => ?_, fun j => ?_⟩
    · have h₁ := reflectAppend_castAdd_rev a b (Fin.rev i)
      rw [Fin.rev_rev] at h₁
      rw [h₁]
      exact neg_lt_zero.2 (firstCoord_pos ha₀ ham _)
    · rw [reflectAppend_natAdd]
      exact firstCoord_pos hb₀ hbm j
end YangMills.Construction.ForwardTube
end
