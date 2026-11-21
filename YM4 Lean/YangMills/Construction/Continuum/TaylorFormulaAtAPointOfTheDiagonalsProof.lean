import YangMills.Construction.ConfigSpace.IteratedPartialCalculus
import YangMills.Construction.Continuum.BumpsSmoothedIndicatorsAndTensorsOfBumpsProof
import YangMills.Construction.Continuum.OperationsKeepTheSpacesProof
import YangMills.Construction.Continuum.TruncationOfSchwartzFunctionsAtInfinityProof
import YangMills.Construction.Continuum.OperationsOnTestFunctionsProof
import YangMills.Construction.Continuum.TaylorFormulaAtAPointOfTheDiagonals
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.ConfigSpace.TaylorNearDiagonal
variable {n : ℕ}
def coordDir (c : Fin n × Fin 4) : Config n := Pi.single c.1 (Pi.single c.2 1)
def partialAlong (l : List (Fin n × Fin 4)) (g : Config n → ℂ) : Config n → ℂ :=
  l.foldr (fun c h => coordPartial c.1 c.2 h) g
theorem partialAlong_cons (c : Fin n × Fin 4) (l : List (Fin n × Fin 4)) (g : Config n → ℂ) :
    partialAlong (c :: l) g = coordPartial c.1 c.2 (partialAlong l g) := rfl
theorem partialAlong_append (l l' : List (Fin n × Fin 4)) (g : Config n → ℂ) :
    partialAlong (l ++ l') g = partialAlong l (partialAlong l' g) := by
  simp [partialAlong, List.foldr_append]
theorem coordPartial_eq_fderiv {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (c : Fin n × Fin 4) :
    coordPartial c.1 c.2 g = fun x => fderiv ℝ g x (coordDir c) := by apply _root_.YangMills.Construction.ConfigSpace.PartialCalculus.partialIn_eq_fderiv <;> assumption
theorem contDiff_coordPartial {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (c : Fin n × Fin 4) :
    ContDiff ℝ ∞ (coordPartial c.1 c.2 g) := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzOps.contDiff_dirPartial <;> assumption
theorem contDiff_partialAlong {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (l : List (Fin n × Fin 4)) :
    ContDiff ℝ ∞ (partialAlong l g) := by apply _root_.YangMills.Construction.ConfigSpace.PartialCalculus.contDiff_derivAlong <;> assumption
theorem partialAlong_perm {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) {l l' : List (Fin n × Fin 4)}
    (h : l.Perm l') : partialAlong l g = partialAlong l' g := by apply _root_.YangMills.Construction.ConfigSpace.PartialCalculus.derivAlong_perm <;> assumption
def coordList (α : MultiIndex n) : List (Fin n × Fin 4) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange 4).flatMap fun μ => List.replicate (α i μ) (i, μ)
theorem foldr_flatMap_eq {A B C : Type*} (f : B → C → C) (init : C) (l : List A) (t : A → List B) :
    (l.flatMap t).foldr f init = l.foldr (fun a acc => (t a).foldr f acc) init := by apply _root_.YangMills.Construction.TestFunctionOps.list_foldr_flatMap <;> assumption
theorem foldr_replicate_eq {B C : Type*} (f : B → C → C) (init : C) (m : ℕ) (a : B) :
    (List.replicate m a).foldr f init = (f a)^[m] init := by apply _root_.YangMills.Construction.TestFunctionOps.list_foldr_replicate <;> assumption
theorem iteratedPartial_eq_partialAlong (α : MultiIndex n) (g : Config n → ℂ) :
    iteratedPartial α g = partialAlong (coordList α) g := by apply _root_.YangMills.Construction.ConfigSpace.PartialCalculus.iteratedPartial_eq_derivAlong <;> assumption
theorem count_coordList (α : MultiIndex n) (c : Fin n × Fin 4) :
    (coordList α).count c = α c.1 c.2 := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzOps.count_indexList <;> assumption
def countIndex (l : List (Fin n × Fin 4)) : MultiIndex n := fun i μ => l.count (i, μ)
theorem length_coordList (α : MultiIndex n) : (coordList α).length = α.order := by apply _root_.YangMills.Construction.ConfigSpace.SchwartzOps.length_indexList <;> assumption
theorem order_countIndex (l : List (Fin n × Fin 4)) : (countIndex l).order = l.length := by apply _root_.YangMills.Construction.ConfigSpace.PartialCalculus.order_countIndex <;> assumption
theorem partialAlong_iteratedPartial {f : Config n → ℂ} (hf : ContDiff ℝ ∞ f) (β : MultiIndex n)
    (l : List (Fin n × Fin 4)) :
    partialAlong l (iteratedPartial β f) = iteratedPartial (β + countIndex l) f := by
  rw [iteratedPartial_eq_partialAlong, iteratedPartial_eq_partialAlong, ← partialAlong_append]
  refine partialAlong_perm hf (List.perm_iff_count.2 fun c => ?_)
  rw [List.count_append, count_coordList, count_coordList]
  simp [countIndex, add_comm]
theorem contDiff_iteratedPartial {f : Config n → ℂ} (hf : ContDiff ℝ ∞ f) (β : MultiIndex n) :
    ContDiff ℝ ∞ (iteratedPartial β f) := by
  rw [iteratedPartial_eq_partialAlong]
  exact contDiff_partialAlong hf _
theorem iteratedFDeriv_coordDir {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (p : ℕ) :
    ∀ (L : Fin p → Fin n × Fin 4) (z : Config n),
      iteratedFDeriv ℝ p g z (fun j => coordDir (L j)) = partialAlong (List.ofFn L) g z := by
  induction p with
  | zero =>
    intro L z
    simp [partialAlong]
  | succ p ih =>
    intro L z
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ p g) z :=
      (hg.differentiable_iteratedFDeriv (m := p) (by exact_mod_cast ENat.natCast_lt_top p)) z
    have hfun : partialAlong (List.ofFn fun j => L j.succ) g =
        fun z => iteratedFDeriv ℝ p g z (fun j => coordDir (L j.succ)) :=
      funext fun z => (ih (fun j => L j.succ) z).symm
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ, partialAlong_cons, hfun]
    have := (HasFDerivAt.hasLineDerivAt
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin p => Config n) ℂ
        (fun j => coordDir (L j.succ))).hasFDerivAt.comp z hd.hasFDerivAt)
      (coordDir (L 0))).lineDeriv
    exact this.symm
theorem hasDerivAt_iteratedFDeriv_line {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) (p : ℕ)
    (y v : Config n) (s : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ p g (y + s • v) (fun _ => v))
      (iteratedFDeriv ℝ (p + 1) g (y + s • v) (fun _ => v)) s := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ p g) (y + s • v) :=
    (hg.differentiable_iteratedFDeriv (m := p) (by exact_mod_cast ENat.natCast_lt_top p)) _
  have hpath : HasDerivAt (fun s : ℝ => y + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add y
  have happ := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin p => Config n) ℂ
    (fun _ => v)).hasFDerivAt.comp (y + s • v) hd.hasFDerivAt).comp_hasDerivAt s hpath
  rw [iteratedFDeriv_succ_apply_left]
  exact happ
theorem eq_sum_coordDir (v : Config n) :
    v = ∑ c : Fin n × Fin 4, v c.1 c.2 • coordDir c := by
  funext i μ
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_apply, Pi.smul_apply, coordDir, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj.symm]) (by simp)]
  rw [Finset.sum_eq_single μ (fun ν _ hν => by simp [Pi.single_eq_of_ne hν.symm]) (by simp)]
  simp
theorem multilinear_apply_diag_eq_sum {p : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin p => Config n) ℂ) (v : Config n) :
    A (fun _ => v) = ∑ L : Fin p → Fin n × Fin 4,
      (∏ j, v (L j).1 (L j).2) • A (fun j => coordDir (L j)) := by
  conv_lhs => rw [eq_sum_coordDir v]
  rw [ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun L _ => ?_
  exact A.toMultilinearMap.map_smul_univ _ _
theorem norm_le_of_iterated_deriv_vanish (r : ℕ) :
    ∀ (H : ℕ → ℝ → ℂ) (C : ℝ), (∀ p s, HasDerivAt (H p) (H (p + 1) s) s) →
      (∀ p, p < r → H p 0 = 0) → (∀ s ∈ Set.Icc (0 : ℝ) 1, ‖H r s‖ ≤ C) → 0 ≤ C →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖H 0 t‖ ≤ C * t ^ r / (r.factorial : ℝ) := by
  induction r with
  | zero =>
    intro H C _ _ hC _ t ht
    simpa using hC t ht
  | succ r ih =>
    intro H C hH h0 hC hC0
    have h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖H 1 t‖ ≤ C * t ^ r / (r.factorial : ℝ) :=
      ih (fun p => H (p + 1)) C (fun p s => hH (p + 1) s)
        (fun p hp => h0 (p + 1) (by omega)) hC hC0
    have hB : ∀ t : ℝ, HasDerivAt (fun t => C * t ^ (r + 1) / ((r + 1).factorial : ℝ))
        (C * t ^ r / (r.factorial : ℝ)) t := by
      intro t
      have := ((hasDerivAt_pow (r + 1) t).const_mul C).div_const ((r + 1).factorial : ℝ)
      have hr : ((r.factorial : ℝ)) ≠ 0 := by positivity
      have hr' : ((r : ℝ) + 1) ≠ 0 := by positivity
      have heq : C * (((r + 1 : ℕ) : ℝ) * t ^ (r + 1 - 1)) / ((r + 1).factorial : ℝ) =
          C * t ^ r / (r.factorial : ℝ) := by
        rw [Nat.factorial_succ, Nat.add_sub_cancel]
        push_cast
        field_simp
      rw [heq] at this
      exact this
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := H 0) (f' := H 1) (a := 0)
      (b := 1) (B' := fun t => C * t ^ r / (r.factorial : ℝ)) ?_ ?_ ?_ hB ?_
    · exact fun t _ => (hH 0 t).continuousAt.continuousWithinAt
    · exact fun t _ => (hH 0 t).hasDerivWithinAt
    · rw [h0 0 (by omega)]
      simp
    · exact fun t ht => h1 t ⟨ht.1, ht.2.le⟩
theorem zero_le_euclidNorm (x : Config n) : 0 ≤ euclidNorm x := Real.sqrt_nonneg _
theorem abs_apply_le_euclidNorm (v : Config n) (i : Fin n) (μ : Fin 4) :
    |v i μ| ≤ euclidNorm v := by apply _root_.YangMills.DeltaSharedProofs.p501753 <;> assumption
theorem euclidNorm_eq_norm_toLp (x : Config n) :
    euclidNorm x =
      ‖(WithLp.toLp 2 fun c : Fin n × Fin 4 => x c.1 c.2 : EuclideanSpace ℝ (Fin n × Fin 4))‖ := by
  rw [EuclideanSpace.norm_eq, euclidNorm, Fintype.sum_prod_type]
  simp
theorem euclidNorm_triangle (x x' : Config n) :
    euclidNorm (x + x') ≤ euclidNorm x + euclidNorm x' := by apply _root_.YangMills.Construction.TestSpaces.SchwartzTruncation.tupleNorm_add_le <;> assumption
theorem euclidNorm_smul_eq (a : ℝ) (x : Config n) :
    euclidNorm (a • x) = |a| * euclidNorm x := by apply _root_.YangMills.DeltaSharedProofs.p501995 <;> assumption
theorem eq_of_euclidNorm_sub_eq_zero {x y : Config n} (h : euclidNorm (x - y) = 0) : x = y := by
  funext i μ
  have := abs_apply_le_euclidNorm (x - y) i μ
  rw [h] at this
  have h0 : (x - y) i μ = 0 := abs_nonpos_iff.1 this
  simpa [sub_eq_zero] using h0
theorem order_add_eq (β γ : MultiIndex n) : (β + γ).order = β.order + γ.order := by
  simp [MultiIndex.order, Finset.sum_add_distrib]
theorem norm_iteratedPartial_le {f : Config n → ℂ} (hf : ContDiff ℝ ∞ f) {y : Config n}
    (hflat : ∀ α : MultiIndex n, iteratedPartial α f y = 0) (β : MultiIndex n) (x : Config n)
    (r : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ w ∈ segmentSet y x, ∀ γ : MultiIndex n, γ.order = r →
      ‖iteratedPartial (β + γ) f w‖ ≤ C) :
    ‖iteratedPartial β f x‖ ≤
      (4 * (n : ℝ)) ^ r / (r.factorial : ℝ) * euclidNorm (x - y) ^ r * C := by
  have hψ := contDiff_iteratedPartial hf β
  set ψ := iteratedPartial β f with hψdef
  set v := x - y with hv
  have hexp : ∀ (p : ℕ) (z : Config n), iteratedFDeriv ℝ p ψ z (fun _ => v) =
      ∑ L : Fin p → Fin n × Fin 4, (∏ j, v (L j).1 (L j).2) •
        iteratedPartial (β + countIndex (List.ofFn L)) f z := by
    intro p z
    rw [multilinear_apply_diag_eq_sum]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [iteratedFDeriv_coordDir hψ, hψdef, partialAlong_iteratedPartial hf]
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ r ψ (y + s • v) (fun _ => v)‖ ≤
        (4 * (n : ℝ)) ^ r * euclidNorm v ^ r * C := by
    intro s hs
    rw [hexp]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ L ∈ (Finset.univ : Finset (Fin r → Fin n × Fin 4)),
        ‖(∏ j, v (L j).1 (L j).2) • iteratedPartial (β + countIndex (List.ofFn L)) f (y + s • v)‖ ≤
          euclidNorm v ^ r * C := by
      intro L _
      rw [norm_smul]
      have h1 : ‖∏ j, v (L j).1 (L j).2‖ ≤ euclidNorm v ^ r := by
        rw [norm_prod]
        calc ∏ j, ‖v (L j).1 (L j).2‖ ≤ ∏ _j : Fin r, euclidNorm v :=
              Finset.prod_le_prod (fun _ _ => norm_nonneg _)
                (fun j _ => abs_apply_le_euclidNorm v _ _)
          _ = euclidNorm v ^ r := by simp
      have h2 : ‖iteratedPartial (β + countIndex (List.ofFn L)) f (y + s • v)‖ ≤ C :=
        hC _ ⟨s, hs.1, hs.2, rfl⟩ _ (by rw [order_countIndex]; simp)
      exact mul_le_mul h1 h2 (norm_nonneg _) (pow_nonneg (zero_le_euclidNorm _) _)
    refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans_eq ?_
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring
  have hzero : ∀ p, p < r → iteratedFDeriv ℝ p ψ (y + (0 : ℝ) • v) (fun _ => v) = 0 := by
    intro p _
    rw [hexp]
    simp [hflat]
  have hfinal := norm_le_of_iterated_deriv_vanish r
    (fun p s => iteratedFDeriv ℝ p ψ (y + s • v) (fun _ => v))
    ((4 * (n : ℝ)) ^ r * euclidNorm v ^ r * C)
    (fun p s => hasDerivAt_iteratedFDeriv_line hψ p y v s) hzero hbound
    (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (zero_le_euclidNorm _) _)) hC0)
    1 ⟨zero_le_one, le_rfl⟩
  have hx : y + (1 : ℝ) • v = x := by simp [hv]
  simp only [hx, iteratedFDeriv_zero_apply, one_pow, mul_one] at hfinal
  calc ‖ψ x‖ ≤ (4 * (n : ℝ)) ^ r * euclidNorm v ^ r * C / (r.factorial : ℝ) := hfinal
    _ = _ := by ring
theorem one_add_euclidNorm_le {x y w : Config n} {δ : ℝ} (hδ : 0 < δ)
    (hxy : euclidNorm (x - y) ≤ δ) (hw : w ∈ segmentSet y x) :
    1 + euclidNorm x ≤ (1 + δ) * (1 + euclidNorm w) := by
  obtain ⟨ς, h0, h1, rfl⟩ := hw
  have hsplit : x = (y + ς • (x - y)) + (1 - ς) • (x - y) := by
    funext i μ
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hd : euclidNorm ((1 - ς) • (x - y)) ≤ δ := by
    rw [euclidNorm_smul_eq, abs_of_nonneg (by linarith)]
    have hn := zero_le_euclidNorm (x - y)
    nlinarith
  have ht := euclidNorm_triangle (y + ς • (x - y)) ((1 - ς) • (x - y))
  rw [← hsplit] at ht
  have hn := zero_le_euclidNorm (y + ς • (x - y))
  nlinarith
theorem taylorBoundNearDiagonal_holds : taylorBoundNearDiagonal := by
  intro n hn f hfm y hy x β r hr
  have hf : ContDiff ℝ ∞ f := hfm.1.1
  have hflat : ∀ α : MultiIndex n, iteratedPartial α f y = 0 := fun α => hfm.2 α y hy
  refine ⟨?_, ?_⟩
  · set S : ℝ≥0∞ := ⨆ (w : Config n) (_ : w ∈ segmentSet y x) (γ : MultiIndex n)
      (_ : γ.order = r), ENNReal.ofReal ‖iteratedPartial (β + γ) f w‖ with hS
    by_cases hStop : S = ⊤
    · by_cases hv : euclidNorm (x - y) = 0
      · have hxy := eq_of_euclidNorm_sub_eq_zero hv
        rw [hxy, hflat β]
        simp
      · have hpos : 0 < (4 * (n : ℝ)) ^ r / (r.factorial : ℝ) * euclidNorm (x - y) ^ r :=
          mul_pos (by positivity)
            (pow_pos (lt_of_le_of_ne (zero_le_euclidNorm _) (Ne.symm hv)) _)
        rw [hStop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
        exact le_top
    · have hb : ∀ w ∈ segmentSet y x, ∀ γ : MultiIndex n, γ.order = r →
          ‖iteratedPartial (β + γ) f w‖ ≤ S.toReal := by
        intro w hw γ hγ
        refine (ENNReal.ofReal_le_iff_le_toReal hStop).1 ?_
        exact le_iSup_of_le w (le_iSup_of_le hw (le_iSup_of_le γ (le_iSup_of_le hγ le_rfl)))
      have hmain := norm_iteratedPartial_le hf hflat β x r ENNReal.toReal_nonneg hb
      have hcoef : 0 ≤ (4 * (n : ℝ)) ^ r / (r.factorial : ℝ) * euclidNorm (x - y) ^ r :=
        mul_nonneg (by positivity) (pow_nonneg (zero_le_euclidNorm _) _)
      calc ENNReal.ofReal ‖iteratedPartial β f x‖
          ≤ ENNReal.ofReal ((4 * (n : ℝ)) ^ r / (r.factorial : ℝ) * euclidNorm (x - y) ^ r *
              S.toReal) := ENNReal.ofReal_le_ofReal hmain
        _ = _ := by rw [ENNReal.ofReal_mul hcoef, ENNReal.ofReal_toReal hStop]
  · intro δ hδ hxy k'
    set N : ℝ≥0∞ := decaySeminorm k' (β.order + r) f with hN
    have hcoefpos : 0 < (1 + δ) ^ k' * ((4 * (n : ℝ) * δ) ^ r / (r.factorial : ℝ)) := by
      positivity
    by_cases hNtop : N = ⊤
    · rw [hNtop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hcoefpos).ne']
      exact le_top
    · have hxpos : 0 < (1 + euclidNorm x) ^ k' :=
        pow_pos (by linarith [zero_le_euclidNorm x]) _
      have hb : ∀ w ∈ segmentSet y x, ∀ γ : MultiIndex n, γ.order = r →
          ‖iteratedPartial (β + γ) f w‖ ≤ (1 + δ) ^ k' * N.toReal / (1 + euclidNorm x) ^ k' := by
        intro w hw γ hγ
        have h1 : (1 + euclidNorm w) ^ k' * ‖iteratedPartial (β + γ) f w‖ ≤ N.toReal := by
          refine (ENNReal.ofReal_le_iff_le_toReal hNtop).1 ?_
          exact le_iSup_of_le (β + γ)
            (le_iSup_of_le (by rw [order_add_eq, hγ]) (le_iSup_of_le w le_rfl))
        have h2 : (1 + euclidNorm x) ^ k' ≤ (1 + δ) ^ k' * (1 + euclidNorm w) ^ k' := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by linarith [zero_le_euclidNorm x])
            (one_add_euclidNorm_le hδ hxy hw) _
        rw [le_div_iff₀ hxpos]
        calc ‖iteratedPartial (β + γ) f w‖ * (1 + euclidNorm x) ^ k'
            ≤ ‖iteratedPartial (β + γ) f w‖ * ((1 + δ) ^ k' * (1 + euclidNorm w) ^ k') :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ = (1 + δ) ^ k' * ((1 + euclidNorm w) ^ k' * ‖iteratedPartial (β + γ) f w‖) := by
              ring
          _ ≤ (1 + δ) ^ k' * N.toReal := mul_le_mul_of_nonneg_left h1 (by positivity)
      have hmain := norm_iteratedPartial_le hf hflat β x r
        (div_nonneg (mul_nonneg (by positivity) ENNReal.toReal_nonneg) hxpos.le) hb
      have hpow : euclidNorm (x - y) ^ r ≤ δ ^ r :=
        pow_le_pow_left₀ (zero_le_euclidNorm _) hxy r
      have hreal : (1 + euclidNorm x) ^ k' * ‖iteratedPartial β f x‖ ≤
          (1 + δ) ^ k' * ((4 * (n : ℝ) * δ) ^ r / (r.factorial : ℝ)) * N.toReal := by
        calc (1 + euclidNorm x) ^ k' * ‖iteratedPartial β f x‖
            ≤ (1 + euclidNorm x) ^ k' * ((4 * (n : ℝ)) ^ r / (r.factorial : ℝ) *
                euclidNorm (x - y) ^ r *
                ((1 + δ) ^ k' * N.toReal / (1 + euclidNorm x) ^ k')) :=
              mul_le_mul_of_nonneg_left hmain hxpos.le
          _ = (1 + δ) ^ k' * ((4 * (n : ℝ)) ^ r / (r.factorial : ℝ) * euclidNorm (x - y) ^ r) *
                N.toReal := by
              field_simp
          _ ≤ (1 + δ) ^ k' * ((4 * (n : ℝ)) ^ r / (r.factorial : ℝ) * δ ^ r) * N.toReal := by
              refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = _ := by rw [mul_pow]; ring
      calc ENNReal.ofReal ((1 + euclidNorm x) ^ k' * ‖iteratedPartial β f x‖)
          ≤ ENNReal.ofReal ((1 + δ) ^ k' * ((4 * (n : ℝ) * δ) ^ r / (r.factorial : ℝ)) *
              N.toReal) := ENNReal.ofReal_le_ofReal hreal
        _ = _ := by rw [ENNReal.ofReal_mul hcoefpos.le, ENNReal.ofReal_toReal hNtop]
end YangMills.Construction.ConfigSpace.TaylorNearDiagonal
end
