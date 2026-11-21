import YangMills.Construction.FormsOnATorus.PropertiesOfTheSymbolProof
import YangMills.Construction.FreeKernel.SecondDifferencesOfTheGreenFunctionOfTheTorusProof
import YangMills.Construction.LawByMomentsOfTheFlow.CurlOfTheGreenPotential
import YangMills.Construction.LawByMomentsOfTheFlow.GreenFunctionAsATimeIntegral
import YangMills.Construction.LawByMomentsOfTheFlow.KernelOfTheCurvatureOnTheLattice
import YangMills.Construction.LawByMomentsOfTheFlow.PairingOfACurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
private theorem sum_inv_sq_le_two (A : Finset ℕ) (h0 : 0 ∉ A) : ∑ m ∈ A, ((m : ℝ) ^ 2)⁻¹ ≤ 2 := by apply _root_.YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof.sum_inv_sq_natCast_le_two <;> assumption
open PeriodicLattice.ShortDistanceTwoPoint FreeKernel.UnitLattice
private def maxAbsCoord (w : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun μ => (w μ).natAbs
private theorem exists_natAbs_eq_maxAbsCoord {w : Fin 4 → ℤ} (hw : w ≠ 0) :
    ∃ μ, (w μ).natAbs = maxAbsCoord w ∧ 1 ≤ maxAbsCoord w := by apply _root_.YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof.exists_coord_eq_supNormInt <;> assumption
private theorem sum_inv_maxAbsCoord_pow_six_le (S : Finset (Fin 4 → ℤ)) (h0 : (0 : Fin 4 → ℤ) ∉ S) :
    ∑ w ∈ S, (((maxAbsCoord w : ℕ) : ℝ) ^ 6)⁻¹ ≤ 162 := by apply _root_.YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof.sum_inv_supNormInt_pow_six_le <;> assumption
private def cubicDecay (z : Fin 4 → ℤ) : ℝ := ((l1Length z + 1) ^ 3)⁻¹
private theorem l1Length_nonneg' (z : Fin 4 → ℤ) : 0 ≤ l1Length z :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
private theorem cubicDecay_nonneg (z : Fin 4 → ℤ) : 0 ≤ cubicDecay z := by
  have := l1Length_nonneg' z
  unfold cubicDecay
  positivity
private theorem l1Length_add_le (z e : Fin 4 → ℤ) : l1Length (z + e) ≤ l1Length z + l1Length e := by
  unfold l1Length
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun μ _ => ?_
  simpa using abs_add_le (z μ : ℝ) (e μ : ℝ)
private theorem l1Length_single (μ : Fin 4) (s : ℤ) (hs : |s| = 1) :
    l1Length (Pi.single μ s : Fin 4 → ℤ) = 1 := by
  unfold l1Length
  rw [Finset.sum_eq_single μ]
  · simp only [Pi.single_eq_same]
    have : |(s : ℝ)| = ((|s| : ℤ) : ℝ) := by simp
    rw [this, hs]
    simp
  · intro ν _ h
    simp [Pi.single_eq_of_ne h]
  · simp
private theorem cubicDecay_add_le (z e : Fin 4 → ℤ) (he : l1Length e ≤ 1) :
    cubicDecay (z + e) ≤ 8 * cubicDecay z := by
  have h0 := l1Length_nonneg' z
  have h1 := l1Length_nonneg' (z + e)
  have h2 : l1Length z ≤ l1Length (z + e) + 1 := by
    have h3 := l1Length_add_le (z + e) (-e)
    have h4 : l1Length (-e) = l1Length e := by simp [l1Length]
    simp only [add_neg_cancel_right] at h3
    linarith
  unfold cubicDecay
  have h5 : l1Length z + 1 ≤ 2 * (l1Length (z + e) + 1) := by linarith
  have h6 : (l1Length z + 1) ^ 3 ≤ 8 * (l1Length (z + e) + 1) ^ 3 := by
    calc (l1Length z + 1) ^ 3 ≤ (2 * (l1Length (z + e) + 1)) ^ 3 :=
          pow_le_pow_left₀ (by linarith) h5 3
      _ = 8 * (l1Length (z + e) + 1) ^ 3 := by ring
  have hp : 0 < (l1Length z + 1) ^ 3 := by positivity
  have hq : 0 < (l1Length (z + e) + 1) ^ 3 := by positivity
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hq hp]
  linarith
private theorem maxAbsCoord_le_l1Length (z : Fin 4 → ℤ) : (maxAbsCoord z : ℝ) ≤ l1Length z := by apply _root_.YangMills.DeltaSharedProofs.p500619 <;> assumption
private theorem summable_cubicDecay_sq : Summable fun z : Fin 4 → ℤ => cubicDecay z ^ 2 := by
  classical
  refine summable_of_sum_le (c := 163) (fun z => by positivity) fun S => ?_
  have h1 : ∑ z ∈ S, cubicDecay z ^ 2 ≤ 1 + ∑ z ∈ S.erase 0, cubicDecay z ^ 2 := by
    by_cases h : (0 : Fin 4 → ℤ) ∈ S
    · rw [← Finset.add_sum_erase S _ h]
      simp [cubicDecay, l1Length]
    · rw [Finset.erase_eq_of_notMem h]
      linarith
  have h2 : ∑ z ∈ S.erase 0, cubicDecay z ^ 2 ≤ ∑ z ∈ S.erase 0, (((maxAbsCoord z : ℕ) : ℝ) ^ 6)⁻¹ := by
    refine Finset.sum_le_sum fun z hz => ?_
    have hz0 := Finset.ne_of_mem_erase hz
    obtain ⟨μ, -, h1'⟩ := exists_natAbs_eq_maxAbsCoord hz0
    have hs : (1 : ℝ) ≤ (maxAbsCoord z : ℝ) := by exact_mod_cast h1'
    have hl := maxAbsCoord_le_l1Length z
    have hu := l1Length_nonneg' z
    have e : cubicDecay z ^ 2 = ((l1Length z + 1) ^ 6)⁻¹ := by
      unfold cubicDecay
      rw [inv_pow, ← pow_mul]
    rw [e]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 6)
  have h3 := sum_inv_maxAbsCoord_pow_six_le (S.erase 0) (Finset.notMem_erase _ _)
  linarith
private theorem summable_mul_of_summable_sq {α : Type*} {f g : α → ℝ} (hf : Summable fun x => f x ^ 2)
    (hg : Summable fun x => g x ^ 2) : Summable fun x => f x * g x := by
  refine Summable.of_norm_bounded ((hf.add hg).mul_left (1 / 2)) fun x => ?_
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]
private theorem discreteLaplacian_apply (f : (Fin 4 → ℤ) → ℝ) (z : Fin 4 → ℤ) :
    discreteLaplacian f z = latticeLaplacian f z := by
  simp only [discreteLaplacian, PeriodicLattice.ShortDistanceTwoPoint.backwardDiff,
    PeriodicLattice.ShortDistanceTwoPoint.forwardDiff, PeriodicLattice.ShortDistanceTwoPoint.unitVector,
    Pi.neg_apply, Finset.sum_apply, sub_add_cancel, ← Finset.sum_neg_distrib, latticeLaplacian]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring
private def antisymmExtend (u : PlaquetteL2) (x : Fin 4 → ℤ) (a b : Fin 4) : ℝ :=
  if h : a < b then u (x, ⟨(a, b), h⟩) else if h' : b < a then -u (x, ⟨(b, a), h'⟩) else 0
private theorem antisymmExtend_swap (u : PlaquetteL2) (x : Fin 4 → ℤ) (a b : Fin 4) :
    antisymmExtend u x a b = -antisymmExtend u x b a := by
  rcases lt_trichotomy a b with h | h | h
  · simp [antisymmExtend, h, not_lt.2 h.le]
  · subst h
    simp [antisymmExtend]
  · simp [antisymmExtend, h, not_lt.2 h.le]
private theorem antisymmExtend_pair (u : PlaquetteL2) (x : Fin 4 → ℤ) (r : CyclicFormula.OrderedDirectionPair) :
    antisymmExtend u x r.1.1 r.1.2 = u (x, r) := by
  simp [antisymmExtend, r.2]
private theorem summable_sq_apply (u : PlaquetteL2) : Summable fun P : IntPlaquette => u P ^ 2 := by
  have h := (lp.memℓp u).summable (by norm_num)
  have e : (fun P : IntPlaquette => ‖u P‖ ^ (2 : ENNReal).toReal) = fun P => u P ^ 2 := by
    funext P
    simp [Real.norm_eq_abs, sq_abs]
  rwa [e] at h
private theorem summable_antisymmExtend_sq (u : PlaquetteL2) (a b : Fin 4) :
    Summable fun x => antisymmExtend u x a b ^ 2 := by
  have hr : ∀ r : CyclicFormula.OrderedDirectionPair, Summable fun x : Fin 4 → ℤ => u (x, r) ^ 2 := fun r =>
    (summable_sq_apply u).comp_injective (i := fun x : Fin 4 → ℤ => (x, r))
      (fun x x' h => by simpa using congrArg Prod.fst h)
  rcases lt_trichotomy a b with h | h | h
  · simpa [antisymmExtend, h, not_lt.2 h.le] using hr ⟨(a, b), h⟩
  · subst h
    simp [antisymmExtend, summable_zero]
  · simpa [antisymmExtend, h, not_lt.2 h.le] using hr ⟨(b, a), h⟩
private theorem inner_eq_tsum_sum (v w : PlaquetteL2) :
    inner ℝ v w = ∑' x : Fin 4 → ℤ, ∑ r : CyclicFormula.OrderedDirectionPair, v (x, r) * w (x, r) := by
  have h := lp.hasSum_inner (𝕜 := ℝ) v w
  have h2 := h.prod_fiberwise (fun x => hasSum_fintype _)
  rw [← h2.tsum_eq]
  refine tsum_congr fun x => Finset.sum_congr rfl fun r _ => ?_
  simp [mul_comm]
private theorem support_curl_finite (B : (Fin 4 → ℤ) → Fin 4 → ℝ)
    (hB : (Function.support (Function.uncurry B)).Finite) :
    (Function.support fun P : IntPlaquette => plaquetteCurlAt B P.1 P.2.1.1 P.2.1.2).Finite := by
  set S : Set (Fin 4 → ℤ) := Prod.fst '' Function.support (Function.uncurry B) with hS
  have hSf : S.Finite := hB.image _
  have hT : (S ∪ ⋃ a : Fin 4, (fun x => x - unitVector a) '' S).Finite :=
    hSf.union (Set.finite_iUnion fun a => hSf.image _)
  refine (hT.prod (Set.finite_univ (α := CyclicFormula.OrderedDirectionPair))).subset ?_
  rintro ⟨x, r⟩ hP
  have key : ∀ (w : Fin 4 → ℤ) (μ : Fin 4), B w μ ≠ 0 → w ∈ S := fun w μ h => ⟨(w, μ), h, rfl⟩
  refine ⟨?_, trivial⟩
  by_contra hx
  have hx1 : ∀ μ, B x μ = 0 := fun μ => by
    by_contra h
    exact hx (Or.inl (key _ _ h))
  have hx2 : ∀ a μ, B (x + unitVector a) μ = 0 := fun a μ => by
    by_contra h
    exact hx (Or.inr (Set.mem_iUnion.2 ⟨a, _, key _ _ h, by simp⟩))
  exact hP (by simp [plaquetteCurlAt, hx1, hx2])
private theorem memℓp_curl (B : (Fin 4 → ℤ) → Fin 4 → ℝ)
    (hB : (Function.support (Function.uncurry B)).Finite) :
    Memℓp (fun P : IntPlaquette => plaquetteCurlAt B P.1 P.2.1.1 P.2.1.2) 2 := by
  refine memℓp_gen (summable_of_hasFiniteSupport ((support_curl_finite B hB).subset fun P hP => ?_))
  simp only [Function.mem_support] at hP ⊢
  intro h
  apply hP
  simp [h]
private theorem curl_mem_intCurvatures (A : IntBond →₀ ℝ)
    (hB : (Function.support (Function.uncurry fun x μ => A (x, μ))).Finite) :
    (⟨_, memℓp_curl _ hB⟩ : PlaquetteL2) ∈ intCurvatures :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨A, fun _ => rfl⟩)
private theorem support_uncurry_finite (A : IntBond →₀ ℝ) :
    (Function.support (Function.uncurry fun x μ => A (x, μ))).Finite := by
  have e : Function.uncurry (fun x μ => A (x, μ)) = ⇑A := by
    funext ⟨x, μ⟩
    rfl
  rw [e]
  exact A.hasFiniteSupport
private theorem summable_finsupp_sq (A : IntBond →₀ ℝ) (c : Fin 4) :
    Summable fun x : Fin 4 → ℤ => A (x, c) ^ 2 := by
  refine summable_of_hasFiniteSupport ?_
  have hinj : Function.Injective (fun x : Fin 4 → ℤ => (x, c)) := fun x x' h => by
    simpa using congrArg Prod.fst h
  refine (A.hasFiniteSupport.preimage hinj.injOn).subset fun x hx => ?_
  simp only [Function.mem_support, Set.mem_preimage] at hx ⊢
  intro h
  apply hx
  simp [h]
private theorem codifferential_eq_zero (hP : curvaturePairingSummationByParts) (u : PlaquetteL2)
    (hu : u ∈ intCurvaturesᗮ) (x₀ : Fin 4 → ℤ) (μ₀ : Fin 4) :
    ∑ ν, (antisymmExtend u x₀ μ₀ ν - antisymmExtend u (x₀ - unitVector ν) μ₀ ν) = 0 := by
  classical
  set A : IntBond →₀ ℝ := Finsupp.single (x₀, μ₀) 1 with hA
  have hfin := support_uncurry_finite A
  have h0 := (Submodule.mem_orthogonal _ _).1 hu _ (curl_mem_intCurvatures A hfin)
  rw [inner_eq_tsum_sum] at h0
  have hs : ∀ (a b c : Fin 4) (v : Fin 4 → ℤ),
      Summable fun x => antisymmExtend u (x - v) a b * (fun x μ => A (x, μ)) x c := fun a b c v =>
    summable_mul_of_summable_sq ((summable_antisymmExtend_sq u a b).comp_injective (sub_left_injective (b := v)))
      (summable_finsupp_sq A c)
  have h1 := hP ℤ (antisymmExtend u) (fun x μ => A (x, μ)) (antisymmExtend_swap u) hs
  have h2 : ∑' x : Fin 4 → ℤ, ∑ r : CyclicFormula.OrderedDirectionPair,
      antisymmExtend u x r.1.1 r.1.2 * plaquetteCurlAt (fun x μ => A (x, μ)) x r.1.1 r.1.2 = 0 := by
    rw [← h0]
    refine tsum_congr fun x => Finset.sum_congr rfl fun r _ => ?_
    rw [antisymmExtend_pair, mul_comm]
  rw [h2] at h1
  rw [tsum_eq_single x₀] at h1
  · rw [Finset.sum_eq_single μ₀] at h1
    · simpa [hA] using h1.symm
    · intro μ _ hμ
      have : A (x₀, μ) = 0 := by
        simp [hA, Ne.symm hμ]
      simp [this]
    · simp
  · intro x hx
    refine Finset.sum_eq_zero fun μ _ => ?_
    have : A (x, μ) = 0 := by
      simp [hA, Ne.symm hx]
    simp [this]
private theorem rpow_neg_three_eq_cubicDecay (z : Fin 4 → ℤ) : (l1Length z + 1) ^ (-3 : ℝ) = cubicDecay z := by
  have h := l1Length_nonneg' z
  rw [Real.rpow_neg (by linarith)]
  unfold cubicDecay
  norm_cast
private theorem l1Length_neg (e : Fin 4 → ℤ) : l1Length (-e) = l1Length e := by
  simp [l1Length]
theorem curvatureProjectionGreenStatement_holds (hC : curlGreenPotentialStatement)
    (hP : curvaturePairingSummationByParts) (hG : greenAsHeatTimeIntegralStatement) :
    curvatureProjectionGreenStatement := by
  classical
  rintro P ⟨y, q⟩
  obtain ⟨-, hLap, c, hc, hdec⟩ := hG
  set g := latticeGreen with hg
  have hLg : ∀ z : Fin 4 → ℤ, discreteLaplacian g z = (if z = 0 then 1 else 0) - 0 := fun z => by
    rw [discreteLaplacian_apply, hLap z, sub_zero]
  obtain ⟨hval, hpair⟩ := hC ℤ g y q
  have hp0 := hpair 0 (fun z => by
    have := hLg z
    convert this)
  set B₀ := greenPlaquettePotential g y q.1.1 q.1.2 with hB₀
  have hstep : ∀ (w : Fin 4 → ℤ) (μ : Fin 4), |g (w - unitVector μ) - g w| ≤ 8 * c * cubicDecay w := by
    intro w μ
    have h1 := hdec μ (w - unitVector μ)
    rw [rpow_neg_three_eq_cubicDecay] at h1
    have e : w - unitVector μ + Pi.single μ 1 = w := by
      simp [unitVector]
    rw [e, abs_sub_comm] at h1
    have h2 : cubicDecay (w - unitVector μ) ≤ 8 * cubicDecay w := by
      rw [sub_eq_add_neg]
      refine cubicDecay_add_le w _ ?_
      rw [l1Length_neg]
      exact (l1Length_single μ 1 (by simp)).le
    calc _ ≤ c * cubicDecay (w - unitVector μ) := h1
      _ ≤ c * (8 * cubicDecay w) := mul_le_mul_of_nonneg_left h2 hc
      _ = 8 * c * cubicDecay w := by ring
  have hdecay0 : ∀ w, 0 ≤ 8 * c * cubicDecay w := fun w => mul_nonneg (by positivity) (cubicDecay_nonneg w)
  have hB : ∀ x μ, |B₀ x μ| ≤ 16 * c * cubicDecay (x - y) := by
    intro x μ
    have t1 : |if μ = q.1.2 then g (x - y - unitVector q.1.1) - g (x - y) else 0| ≤
        8 * c * cubicDecay (x - y) := by
      split_ifs
      · exact hstep _ _
      · simpa using hdecay0 _
    have t2 : |if μ = q.1.1 then g (x - y - unitVector q.1.2) - g (x - y) else 0| ≤
        8 * c * cubicDecay (x - y) := by
      split_ifs
      · exact hstep _ _
      · simpa using hdecay0 _
    have := abs_sub (if μ = q.1.2 then g (x - y - unitVector q.1.1) - g (x - y) else 0)
      (if μ = q.1.1 then g (x - y - unitVector q.1.2) - g (x - y) else 0)
    simp only [hB₀, greenPlaquettePotential]
    linarith
  have hshift : Summable fun x : Fin 4 → ℤ => cubicDecay (x - y) ^ 2 :=
    summable_cubicDecay_sq.comp_injective (sub_left_injective (b := y))
  have hBsq : ∀ μ, Summable fun x => B₀ x μ ^ 2 := fun μ => by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun x => ?_) (hshift.mul_left ((16 * c) ^ 2))
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hB x μ) 2
  have hV0 : ∀ x (a b : Fin 4), |plaquetteCurlAt B₀ x a b| ≤ 288 * c * cubicDecay (x - y) := by
    intro x a b
    have e1 := hB x a
    have e2 := hB (x + unitVector a) b
    have e3 := hB (x + unitVector b) a
    have e4 := hB x b
    have s : ∀ e : Fin 4, cubicDecay (x + unitVector e - y) ≤ 8 * cubicDecay (x - y) := fun e => by
      rw [show x + unitVector e - y = x - y + unitVector e by abel]
      exact cubicDecay_add_le _ _ (l1Length_single e 1 (by simp)).le
    have hc16 : 0 ≤ 16 * c := by positivity
    have e2' := mul_le_mul_of_nonneg_left (s a) hc16
    have e3' := mul_le_mul_of_nonneg_left (s b) hc16
    have t : |plaquetteCurlAt B₀ x a b| ≤
        |B₀ x a| + |B₀ (x + unitVector a) b| + |B₀ (x + unitVector b) a| + |B₀ x b| := by
      unfold plaquetteCurlAt
      have h1 := abs_sub (B₀ x a + B₀ (x + unitVector a) b - B₀ (x + unitVector b) a) (B₀ x b)
      have h2 := abs_sub (B₀ x a + B₀ (x + unitVector a) b) (B₀ (x + unitVector b) a)
      have h3 := abs_add_le (B₀ x a) (B₀ (x + unitVector a) b)
      linarith
    nlinarith
  have hV : Memℓp (fun P : IntPlaquette => plaquetteCurlAt B₀ P.1 P.2.1.1 P.2.1.2) 2 := by
    refine memℓp_gen ?_
    have hprod : Summable fun P : IntPlaquette => ((288 * c) ^ 2 * cubicDecay (P.1 - y) ^ 2) * (1 : ℝ) :=
      Summable.mul_of_nonneg (f := fun x : Fin 4 → ℤ => (288 * c) ^ 2 * cubicDecay (x - y) ^ 2)
        (g := fun _ : CyclicFormula.OrderedDirectionPair => (1 : ℝ)) (hshift.mul_left _) (hasSum_fintype _).summable
        (fun _ => by positivity) (fun _ => zero_le_one)
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun P => ?_) hprod
    have h := hV0 P.1 P.2.1.1 P.2.1.2
    have e : ‖plaquetteCurlAt B₀ P.1 P.2.1.1 P.2.1.2‖ ^ (2 : ENNReal).toReal =
        |plaquetteCurlAt B₀ P.1 P.2.1.1 P.2.1.2| ^ 2 := by
      simp [Real.norm_eq_abs]
    rw [e, mul_one, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  set vec : PlaquetteL2 := ⟨_, hV⟩ with hvec
  have hvapp : ∀ x r, vec (x, r) = plaquetteCurlAt B₀ x r.1.1 r.1.2 := fun _ _ => rfl
  set e₀ : PlaquetteL2 := lp.single 2 (y, q) (1 : ℝ) with he₀
  have hspan : ∀ w ∈ Submodule.span ℝ {v : PlaquetteL2 | ∃ A : IntBond →₀ ℝ, ∀ p, v p = intCurl A p},
      inner ℝ (e₀ - vec) w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w h =>
      obtain ⟨A, hA⟩ := h
      have h1 := hp0 (fun x μ => A (x, μ)) (support_uncurry_finite A)
      rw [inner_sub_left, he₀, lp.inner_single_left, inner_eq_tsum_sum]
      have e1 : ∑' x : Fin 4 → ℤ, ∑ r : CyclicFormula.OrderedDirectionPair, vec (x, r) * w (x, r) =
          ∑' x : Fin 4 → ℤ, ∑ r : CyclicFormula.OrderedDirectionPair, plaquetteCurlAt B₀ x r.1.1 r.1.2 *
            plaquetteCurlAt (fun x μ => A (x, μ)) x r.1.1 r.1.2 := by
        refine tsum_congr fun x => Finset.sum_congr rfl fun r _ => ?_
        rw [hvapp, hA]
        rfl
      rw [e1, h1, hA]
      simp only [map_one, one_mul, sub_eq_zero]
      simp [inner, intCurl, plaquetteCurlAt, unitVector]
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]
  have hK : e₀ - vec ∈ intCurvaturesᗮ := by
    unfold intCurvatures
    rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal']
    exact hspan
  have hmem : vec ∈ intCurvatures := by
    rw [← Submodule.orthogonal_orthogonal intCurvatures, Submodule.mem_orthogonal]
    intro u hu
    rw [inner_eq_tsum_sum]
    have hs : ∀ (a b c : Fin 4) (v : Fin 4 → ℤ), Summable fun x => antisymmExtend u (x - v) a b * B₀ x c :=
      fun a b c v => summable_mul_of_summable_sq
        ((summable_antisymmExtend_sq u a b).comp_injective (sub_left_injective (b := v))) (hBsq c)
    have h1 := hP ℤ (antisymmExtend u) B₀ (antisymmExtend_swap u) hs
    have e1 : ∑' x : Fin 4 → ℤ, ∑ r : CyclicFormula.OrderedDirectionPair, u (x, r) * vec (x, r) =
        ∑' x : Fin 4 → ℤ, ∑ r : CyclicFormula.OrderedDirectionPair,
          antisymmExtend u x r.1.1 r.1.2 * plaquetteCurlAt B₀ x r.1.1 r.1.2 := by
      refine tsum_congr fun x => Finset.sum_congr rfl fun r _ => ?_
      rw [antisymmExtend_pair, hvapp]
    rw [e1, h1]
    simp [codifferential_eq_zero hP u hu]
  have hproj : intCurvatures.starProjection e₀ = vec :=
    Submodule.eq_starProjection_of_mem_orthogonal hmem hK
  unfold intCurvatureProjection
  rw [hproj, lp.inner_single_left]
  have hv := hval P.1 P.2
  have e : inner ℝ (1 : ℝ) (vec P) = vec P := by simp
  rw [e]
  exact hv
end YangMills.Construction.MomentLaw
end
