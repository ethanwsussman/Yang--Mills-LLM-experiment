import YangMills.Construction.Continuum.CompactSupportAndTensorsOfSeparatedTuplesProof
import YangMills.Construction.Continuum.SupremaOfASmoothFunctionAndTheVectorSpaceOfSchwartzFunctions
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.ConfigSpace
namespace SchwartzSuprema
variable {n : ℕ}
theorem iteratedPartial_induction (R : (Config n → ℂ) → (Config n → ℂ) → (Config n → ℂ) → Prop)
    (step : ∀ i μ f g h, R f g h → R (coordPartial i μ f) (coordPartial i μ g)
      (coordPartial i μ h))
    (α : MultiIndex n) {f g h : Config n → ℂ} (hR : R f g h) :
    R (iteratedPartial α f) (iteratedPartial α g) (iteratedPartial α h) := by
  have iter : ∀ (i : Fin n) (μ : Fin 4) (m : ℕ) (f g h : Config n → ℂ), R f g h →
      R ((coordPartial i μ)^[m] f) ((coordPartial i μ)^[m] g)
        ((coordPartial i μ)^[m] h) := by
    intro i μ m
    induction m with
    | zero => exact fun _ _ _ r => r
    | succ m ih =>
      intro f g h r
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply']
      exact step _ _ _ _ _ (ih f g h r)
  have inner : ∀ (i : Fin n) (l : List (Fin 4)) (f g h : Config n → ℂ), R f g h →
      R (l.foldr (fun μ k => (coordPartial i μ)^[α i μ] k) f)
        (l.foldr (fun μ k => (coordPartial i μ)^[α i μ] k) g)
        (l.foldr (fun μ k => (coordPartial i μ)^[α i μ] k) h) := by
    intro i l
    induction l with
    | nil => exact fun _ _ _ r => r
    | cons μ l ih => exact fun f g h r => iter i μ _ _ _ _ (ih f g h r)
  have outer : ∀ l : List (Fin n),
      R (l.foldr (fun i h => (List.finRange 4).foldr
          (fun μ k => (coordPartial i μ)^[α i μ] k) h) f)
        (l.foldr (fun i h => (List.finRange 4).foldr
          (fun μ k => (coordPartial i μ)^[α i μ] k) h) g)
        (l.foldr (fun i h => (List.finRange 4).foldr
          (fun μ k => (coordPartial i μ)^[α i μ] k) h) h) := by
    intro l
    induction l with
    | nil => exact hR
    | cons i l ih => exact inner i _ _ _ _ ih
  exact outer _
theorem differentiable_of_contDiff_top {g : Config n → ℂ} (hg : ContDiff ℝ ∞ g) :
    Differentiable ℝ g :=
  hg.differentiable (by simp)
theorem contDiff_coordPartial (i : Fin n) (μ : Fin 4) {g : Config n → ℂ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (coordPartial i μ g) := by apply _root_.YangMills.Construction.ConfigSpace.TensorSupport.contDiff_coordPartial <;> assumption
theorem coordPartial_linear_comb (i : Fin n) (μ : Fin 4) (c c' : ℂ) {f g : Config n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    coordPartial i μ (c • f + c' • g) =
      c • coordPartial i μ f + c' • coordPartial i μ g := by
  funext x
  have df := differentiable_of_contDiff_top hf x
  have dg := differentiable_of_contDiff_top hg x
  have e := (((df.hasFDerivAt.const_smul c).add (dg.hasFDerivAt.const_smul c')).hasLineDerivAt
    (Pi.single i (Pi.single μ 1) : Config n)).lineDeriv
  have ef : coordPartial i μ f x = fderiv ℝ f x (Pi.single i (Pi.single μ 1)) :=
    df.lineDeriv_eq_fderiv
  have eg : coordPartial i μ g x = fderiv ℝ g x (Pi.single i (Pi.single μ 1)) :=
    dg.lineDeriv_eq_fderiv
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, ef, eg]
  exact e
theorem contDiff_linear_comb (c c' : ℂ) {f g : Config n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (c • f + c' • g) :=
  (hf.const_smul c).add (hg.const_smul c')
theorem iteratedPartial_linear_comb (c c' : ℂ) {f g : Config n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (α : MultiIndex n) :
    iteratedPartial α (c • f + c' • g) =
      c • iteratedPartial α f + c' • iteratedPartial α g := by
  have step : ∀ (i : Fin n) (μ : Fin 4) (f g h : Config n → ℂ),
      (ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧ h = c • f + c' • g) →
      (ContDiff ℝ ∞ (coordPartial i μ f) ∧ ContDiff ℝ ∞ (coordPartial i μ g) ∧
        coordPartial i μ h =
          c • coordPartial i μ f + c' • coordPartial i μ g) := by
    rintro i μ f g _ ⟨hf, hg, rfl⟩
    exact ⟨contDiff_coordPartial i μ hf, contDiff_coordPartial i μ hg,
      coordPartial_linear_comb i μ c c' hf hg⟩
  exact (iteratedPartial_induction
    (fun f g h => ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧ h = c • f + c' • g) step α
    (f := f) (g := g) (h := c • f + c' • g) ⟨hf, hg, rfl⟩).2.2
theorem iteratedPartial_smul (c : ℂ) {f : Config n → ℂ} (hf : ContDiff ℝ ∞ f)
    (α : MultiIndex n) : iteratedPartial α (c • f) = c • iteratedPartial α f := by
  simpa using iteratedPartial_linear_comb c 0 hf hf α
theorem contDiff_zero_on_config : ContDiff ℝ ∞ (0 : Config n → ℂ) := contDiff_const
theorem iteratedPartial_zero (α : MultiIndex n) :
    iteratedPartial α (0 : Config n → ℂ) = 0 := by
  simpa using iteratedPartial_linear_comb 0 0 (contDiff_zero_on_config (n := n))
    contDiff_zero_on_config α
theorem rpow_half_of_sq {b : ℝ} (hb : 0 ≤ b) (k : ℕ) : (b ^ 2) ^ ((k : ℝ) / 2) = b ^ k := by
  rw [← Real.rpow_natCast b 2, ← Real.rpow_mul hb]
  have e : ((2 : ℕ) : ℝ) * ((k : ℝ) / 2) = k := by
    push_cast
    ring
  rw [e, Real.rpow_natCast]
theorem japanese_le_one_add_pow {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    (1 + a ^ 2) ^ ((k : ℝ) / 2) ≤ (1 + a) ^ k := by
  have h : 1 + a ^ 2 ≤ (1 + a) ^ 2 := by nlinarith
  calc (1 + a ^ 2) ^ ((k : ℝ) / 2) ≤ ((1 + a) ^ 2) ^ ((k : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = (1 + a) ^ k := rpow_half_of_sq (by positivity) k
theorem one_add_pow_le_japanese {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    (1 + a) ^ k ≤ 2 ^ ((k : ℝ) / 2) * (1 + a ^ 2) ^ ((k : ℝ) / 2) := by
  have h : (1 + a) ^ 2 ≤ 2 * (1 + a ^ 2) := by nlinarith [sq_nonneg (1 - a)]
  calc (1 + a) ^ k = ((1 + a) ^ 2) ^ ((k : ℝ) / 2) := (rpow_half_of_sq (by positivity) k).symm
    _ ≤ (2 * (1 + a ^ 2)) ^ ((k : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = 2 ^ ((k : ℝ) / 2) * (1 + a ^ 2) ^ ((k : ℝ) / 2) :=
        Real.mul_rpow (by norm_num) (by positivity)
theorem japanese_mono {a : ℝ} {k k' : ℕ} (h : k ≤ k') :
    (1 + a ^ 2) ^ ((k : ℝ) / 2) ≤ (1 + a ^ 2) ^ ((k' : ℝ) / 2) := by
  have h1 : (1 : ℝ) ≤ 1 + a ^ 2 := by nlinarith [sq_nonneg a]
  have h2 : (k : ℝ) ≤ k' := by exact_mod_cast h
  exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
theorem zero_le_euclidNorm (x : Config n) : 0 ≤ euclidNorm x := Real.sqrt_nonneg _
theorem japanese_nonneg (k : ℕ) (x : Config n) :
    0 ≤ (1 + euclidNorm x ^ 2) ^ ((k : ℝ) / 2) := by positivity
theorem le_schwartzSeminorm (k : ℕ) (φ : Config n → ℂ) (x : Config n) {α : MultiIndex n}
    (h : α.order ≤ k) :
    ENNReal.ofReal ((1 + euclidNorm x ^ 2) ^ ((k : ℝ) / 2) * ‖iteratedPartial α φ x‖) ≤
      schwartzSeminorm k φ :=
  le_iSup_of_le x (le_iSup_of_le α (le_iSup_of_le h le_rfl))
theorem le_decaySeminorm (k q : ℕ) (φ : Config n → ℂ) (x : Config n) {α : MultiIndex n}
    (h : α.order ≤ q) :
    ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖iteratedPartial α φ x‖) ≤
      decaySeminorm k q φ :=
  le_iSup_of_le α (le_iSup_of_le h (le_iSup_of_le x le_rfl))
theorem schwartzSeminorm_mono (φ : Config n → ℂ) {k k' : ℕ} (h : k ≤ k') :
    schwartzSeminorm k φ ≤ schwartzSeminorm k' φ := by
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ?_
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (le_schwartzSeminorm k' φ x (hα.trans h))
  exact mul_le_mul_of_nonneg_right (japanese_mono h) (norm_nonneg _)
theorem schwartzSeminorm_le_decaySeminorm (φ : Config n → ℂ) (k : ℕ) :
    schwartzSeminorm k φ ≤ decaySeminorm k k φ := by
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ?_
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (le_decaySeminorm k k φ x hα)
  exact mul_le_mul_of_nonneg_right (japanese_le_one_add_pow (zero_le_euclidNorm x) k)
    (norm_nonneg _)
theorem decaySeminorm_le_schwartzSeminorm (φ : Config n → ℂ) (k q : ℕ) :
    decaySeminorm k q φ ≤ ENNReal.ofReal (2 ^ ((k : ℝ) / 2)) * schwartzSeminorm (max k q) φ := by
  refine iSup_le fun α => iSup_le fun hα => iSup_le fun x => ?_
  have h0 : (0 : ℝ) ≤ 2 ^ ((k : ℝ) / 2) := by positivity
  have hp := le_schwartzSeminorm (max k q) φ x (hα.trans (le_max_right k q))
  refine le_trans ?_ (mul_le_mul_right hp _)
  rw [← ENNReal.ofReal_mul h0]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact (one_add_pow_le_japanese (zero_le_euclidNorm x) k).trans
    (mul_le_mul_of_nonneg_left (japanese_mono (le_max_left k q)) h0)
theorem weighted_norm_linear_comb_le {W : ℝ} (hW : 0 ≤ W) (c c' d d' : ℂ) :
    ENNReal.ofReal (W * ‖c • d + c' • d'‖) ≤
      ENNReal.ofReal ‖c‖ * ENNReal.ofReal (W * ‖d‖) +
        ENNReal.ofReal ‖c'‖ * ENNReal.ofReal (W * ‖d'‖) := by
  rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (norm_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h : ‖c • d + c' • d'‖ ≤ ‖c‖ * ‖d‖ + ‖c'‖ * ‖d'‖ := by
    simpa [norm_smul] using norm_add_le (c • d) (c' • d')
  calc W * ‖c • d + c' • d'‖ ≤ W * (‖c‖ * ‖d‖ + ‖c'‖ * ‖d'‖) :=
        mul_le_mul_of_nonneg_left h hW
    _ = ‖c‖ * (W * ‖d‖) + ‖c'‖ * (W * ‖d'‖) := by ring
theorem schwartzSeminorm_linear_comb_le (k : ℕ) (c c' : ℂ) {φ ψ : Config n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) :
    schwartzSeminorm k (c • φ + c' • ψ) ≤
      ENNReal.ofReal ‖c‖ * schwartzSeminorm k φ + ENNReal.ofReal ‖c'‖ * schwartzSeminorm k ψ := by
  refine iSup_le fun x => iSup_le fun α => iSup_le fun hα => ?_
  rw [iteratedPartial_linear_comb c c' hφ hψ α]
  refine (weighted_norm_linear_comb_le (japanese_nonneg k x) c c' _ _).trans ?_
  exact add_le_add (mul_le_mul_right (le_schwartzSeminorm k φ x hα) _)
    (mul_le_mul_right (le_schwartzSeminorm k ψ x hα) _)
theorem decaySeminorm_linear_comb_le (k q : ℕ) (c c' : ℂ) {φ ψ : Config n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) :
    decaySeminorm k q (c • φ + c' • ψ) ≤
      ENNReal.ofReal ‖c‖ * decaySeminorm k q φ +
        ENNReal.ofReal ‖c'‖ * decaySeminorm k q ψ := by
  refine iSup_le fun α => iSup_le fun hα => iSup_le fun x => ?_
  rw [iteratedPartial_linear_comb c c' hφ hψ α]
  have hW : 0 ≤ (1 + euclidNorm x) ^ k := pow_nonneg (by
    linarith [zero_le_euclidNorm x]) k
  refine (weighted_norm_linear_comb_le hW c c' _ _).trans ?_
  exact add_le_add (mul_le_mul_right (le_decaySeminorm k q φ x hα) _)
    (mul_le_mul_right (le_decaySeminorm k q ψ x hα) _)
theorem schwartzSeminorm_smul (k : ℕ) (c : ℂ) {φ : Config n → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    schwartzSeminorm k (c • φ) = ENNReal.ofReal ‖c‖ * schwartzSeminorm k φ := by
  simp only [schwartzSeminorm, ENNReal.mul_iSup]
  refine iSup_congr fun x => iSup_congr fun α => iSup_congr fun _ => ?_
  rw [iteratedPartial_smul c hφ α, Pi.smul_apply, norm_smul,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  ring
theorem decaySeminorm_smul (k q : ℕ) (c : ℂ) {φ : Config n → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    decaySeminorm k q (c • φ) = ENNReal.ofReal ‖c‖ * decaySeminorm k q φ := by
  simp only [decaySeminorm, ENNReal.mul_iSup]
  refine iSup_congr fun α => iSup_congr fun _ => iSup_congr fun x => ?_
  rw [iteratedPartial_smul c hφ α, Pi.smul_apply, norm_smul,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  ring
theorem finite_setOf_order_le (q : ℕ) : {α : MultiIndex n | α.order ≤ q}.Finite := by apply _root_.YangMills.Construction.ConfigSpace.TensorSupport.finite_setOf_order_le <;> assumption
theorem decaySeminorm_lt_top {φ : Config n → ℂ} (k q : ℕ)
    (h : ∀ α : MultiIndex n, multiIndexDecaySup k α φ < ⊤) : decaySeminorm k q φ < ⊤ := by
  have hs : (finite_setOf_order_le (n := n) q).toFinset.sup
      (fun α => multiIndexDecaySup k α φ) < ⊤ :=
    (Finset.sup_lt_iff bot_lt_top).2 fun α _ => h α
  refine lt_of_le_of_lt (iSup₂_le fun α hα => ?_) hs
  exact Finset.le_sup (f := fun α => multiIndexDecaySup k α φ)
    ((finite_setOf_order_le q).mem_toFinset.2 hα)
theorem schwartzSeminorm_lt_top {φ : Config n → ℂ} (h : IsSchwartz φ) (k : ℕ) :
    schwartzSeminorm k φ < ⊤ :=
  (isSchwartz_iff_mem_schwartzSpace.1 h).2 k
theorem decaySeminorm_lt_top_of_isSchwartz {φ : Config n → ℂ} (h : IsSchwartz φ)
    (k q : ℕ) : decaySeminorm k q φ < ⊤ :=
  lt_of_le_of_lt (decaySeminorm_le_schwartzSeminorm φ k q)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (schwartzSeminorm_lt_top h _))
theorem isSchwartz_linear_comb (c c' : ℂ) {φ ψ : Config n → ℂ} (h : IsSchwartz φ)
    (h' : IsSchwartz ψ) : IsSchwartz (c • φ + c' • ψ) := by
  refine ⟨contDiff_linear_comb c c' h.1 h'.1, fun k _ => ?_⟩
  exact lt_of_le_of_lt (schwartzSeminorm_linear_comb_le k c c' h.1 h'.1)
    (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (schwartzSeminorm_lt_top h k),
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (schwartzSeminorm_lt_top h' k)⟩)
theorem isSchwartz_zero : IsSchwartz (0 : Config n → ℂ) := by
  refine ⟨contDiff_zero_on_config, fun k _ => ?_⟩
  have : schwartzSeminorm k (0 : Config n → ℂ) = 0 := by
    simp [schwartzSeminorm, iteratedPartial_zero]
  simp [this]
theorem isSchwartz_iff_multiIndexDecaySup_lt_top {φ : Config n → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    IsSchwartz φ ↔ ∀ (k : ℕ) (α : MultiIndex n), multiIndexDecaySup k α φ < ⊤ := by
  constructor
  · intro h k α
    refine lt_of_le_of_lt (iSup_le fun x => ?_) (decaySeminorm_lt_top_of_isSchwartz h k α.order)
    exact le_decaySeminorm k α.order φ x le_rfl
  · intro h
    exact ⟨hφ, fun k _ => lt_of_le_of_lt (schwartzSeminorm_le_decaySeminorm φ k)
      (decaySeminorm_lt_top k k (h k))⟩
def schwartzSubmodule (n : ℕ) : Submodule ℂ (Config n → ℂ) where
  carrier := {φ | IsSchwartz φ}
  add_mem' := fun {φ ψ} h h' => by
    simpa using isSchwartz_linear_comb 1 1 h h'
  zero_mem' := isSchwartz_zero
  smul_mem' := fun c φ h => by
    simpa using isSchwartz_linear_comb c 0 h h
theorem isComplexSeminorm_toReal (p : (Config n → ℂ) → ℝ≥0∞)
    (fin : ∀ φ : schwartzSubmodule n, p φ.1 < ⊤)
    (smul : ∀ (c : ℂ) (φ : schwartzSubmodule n), p (c • φ.1) = ENNReal.ofReal ‖c‖ * p φ.1)
    (add : ∀ φ ψ : schwartzSubmodule n, p (φ.1 + ψ.1) ≤ p φ.1 + p ψ.1) :
    Continuum.IsComplexSeminorm fun φ : schwartzSubmodule n => (p φ.1).toReal where
  nonneg := fun _ => ENNReal.toReal_nonneg
  smul := fun c φ => by
    change (p (c • φ.1)).toReal = ‖c‖ * (p φ.1).toReal
    rw [smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
  add_le := fun φ ψ => by
    change (p (φ.1 + ψ.1)).toReal ≤ (p φ.1).toReal + (p ψ.1).toReal
    rw [← ENNReal.toReal_add (fin φ).ne (fin ψ).ne]
    exact ENNReal.toReal_mono (ENNReal.add_lt_top.2 ⟨fin φ, fin ψ⟩).ne (add φ ψ)
end SchwartzSuprema
open SchwartzSuprema in
theorem schwartzSupremaStatement_holds : SchwartzSupremaStatement := by
  intro n _
  refine ⟨fun φ hφ => ⟨fun h => h.2, fun h => ⟨hφ, h⟩⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ ψ hφ hψ c c' k k' hk
    exact ⟨schwartzSeminorm_mono φ hk, contDiff_linear_comb c c' hφ hψ,
      iteratedPartial_linear_comb c c' hφ hψ⟩
  · intro φ ψ h h' c c'
    exact ⟨schwartzSeminorm_lt_top h, isSchwartz_linear_comb c c' h h'⟩
  · intro φ _ k q
    exact ⟨schwartzSeminorm_le_decaySeminorm φ k, decaySeminorm_le_schwartzSeminorm φ k q⟩
  · intro φ hφ
    exact isSchwartz_iff_multiIndexDecaySup_lt_top hφ
  · refine ⟨schwartzSubmodule n, rfl, fun k => ⟨fun φ => schwartzSeminorm_lt_top φ.2 k, ?_⟩,
      fun k q => ⟨fun φ => decaySeminorm_lt_top_of_isSchwartz φ.2 k q, ?_⟩⟩
    · refine isComplexSeminorm_toReal (schwartzSeminorm k) (fun φ => schwartzSeminorm_lt_top φ.2 k)
        (fun c φ => schwartzSeminorm_smul k c φ.2.1) fun φ ψ => ?_
      simpa using schwartzSeminorm_linear_comb_le k 1 1 φ.2.1 ψ.2.1
    · refine isComplexSeminorm_toReal (decaySeminorm k q)
        (fun φ => decaySeminorm_lt_top_of_isSchwartz φ.2 k q)
        (fun c φ => decaySeminorm_smul k q c φ.2.1) fun φ ψ => ?_
      simpa using decaySeminorm_linear_comb_le k q 1 1 φ.2.1 ψ.2.1
end YangMills.Construction.ConfigSpace
end
