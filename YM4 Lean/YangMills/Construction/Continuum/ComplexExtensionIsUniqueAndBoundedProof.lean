import YangMills.Construction.Continuum.CostOfTheModesOfASeparatedSystemProof
import YangMills.Construction.Continuum.OneClassOfTuplesAndOneNotionOfMultilinearityProof
import Mathlib
set_option autoImplicit false
open Set Function
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.ConfigSpace
open YangMills.Construction.SmoothMaps YangMills.Construction.TestFunctions
namespace Complexify
variable {n : ℕ}
def complexPartCLM (e : Fin 2) : ℂ →L[ℝ] ℂ :=
  if e = 0 then Complex.ofRealCLM.comp Complex.reCLM else Complex.ofRealCLM.comp Complex.imCLM
theorem complexPartCLM_apply (e : Fin 2) (z : ℂ) : complexPartCLM e z = complexPart e z := by
  unfold complexPartCLM complexPart
  split_ifs <;> simp
theorem complexPart_add (e : Fin 2) (z w : ℂ) :
    complexPart e (z + w) = complexPart e z + complexPart e w := by
  simp only [← complexPartCLM_apply, map_add]
theorem complexPart_ofReal_mul (e : Fin 2) (r : ℝ) (z : ℂ) :
    complexPart e ((r : ℂ) * z) = (r : ℂ) * complexPart e z := by
  unfold complexPart
  split_ifs <;> simp
theorem norm_complexPart_le (e : Fin 2) (z : ℂ) : ‖complexPart e z‖ ≤ ‖z‖ := by
  unfold complexPart
  split_ifs
  · simpa using Complex.abs_re_le_norm z
  · simpa using Complex.abs_im_le_norm z
theorem fnComplexPart_add (e : Fin 2) (f g : (Fin 4 → ℝ) → ℂ) :
    fnComplexPart e (f + g) = fnComplexPart e f + fnComplexPart e g := by
  funext y
  exact complexPart_add e (f y) (g y)
theorem fnComplexPart_ofReal_smul (e : Fin 2) (r : ℝ) (f : (Fin 4 → ℝ) → ℂ) :
    fnComplexPart e ((r : ℂ) • f) = (r : ℂ) • fnComplexPart e f := by
  funext y
  exact complexPart_ofReal_mul e r (f y)
theorem fnComplexPart_zero_I_smul (f : (Fin 4 → ℝ) → ℂ) :
    fnComplexPart 0 (Complex.I • f) = ((-1 : ℝ) : ℂ) • fnComplexPart 1 f := by
  funext y
  simp [fnComplexPart, complexPart]
theorem fnComplexPart_one_I_smul (f : (Fin 4 → ℝ) → ℂ) :
    fnComplexPart 1 (Complex.I • f) = fnComplexPart 0 f := by
  funext y
  simp [fnComplexPart, complexPart]
theorem isRealValued_fnComplexPart (e : Fin 2) (f : (Fin 4 → ℝ) → ℂ) :
    IsRealValued (fnComplexPart e f) := by
  intro y
  simp only [fnComplexPart, complexPart, Function.comp_apply]
  split_ifs <;> simp
theorem contDiff_fnComplexPart (e : Fin 2) {f : (Fin 4 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fnComplexPart e f) :=
  (contDiff_complexPart e).comp hf
theorem eq_re_add_I_smul_im (f : (Fin 4 → ℝ) → ℂ) :
    f = fnComplexPart 0 f + Complex.I • fnComplexPart 1 f := by
  funext y
  simp only [fnComplexPart, complexPart, Function.comp_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  simp only [if_true, Fin.isValue, one_ne_zero, if_false]
  rw [mul_comm]
  exact (Complex.re_add_im _).symm
theorem tupleComplexParts_update (ε : Fin n → Fin 2) (φ : FnTuple n) (i : Fin n)
    (g : (Fin 4 → ℝ) → ℂ) (b : Fin 2) :
    tupleComplexParts ε (update φ i g) =
      update (tupleComplexParts (update ε i b) φ) i (fnComplexPart (ε i) g) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [tupleComplexParts]
  · simp [tupleComplexParts, hk]
theorem tupleComplexParts_update_self (ε : Fin n → Fin 2) (φ : FnTuple n) (i : Fin n)
    (g : (Fin 4 → ℝ) → ℂ) :
    tupleComplexParts ε (update φ i g) =
      update (tupleComplexParts ε φ) i (fnComplexPart (ε i) g) := by
  simpa using tupleComplexParts_update ε φ i g (ε i)
theorem tsupport_const_smul_subset (c : ℂ) (f : (Fin 4 → ℝ) → ℂ) :
    tsupport (c • f) ⊆ tsupport f :=
  tsupport_comp_subset (g := fun z : ℂ => c * z) (by simp) f
theorem mem_smoothComplexTupleSet_of_tsupport_subset (h : smoothComplexTupleSet n) (g : FnTuple n)
    (hs : ∀ i, ContDiff ℝ ∞ (g i)) (hd : ∀ i, tsupport (g i) ⊆ tsupport (h.1 i)) :
    g ∈ smoothComplexTupleSet n :=
  ⟨fun i => ⟨hs i, IsCompact.of_isClosed_subset (h.2.1 i).2 (isClosed_tsupport _) (hd i)⟩,
    fun i k hik => (h.2.2 i k hik).mono (hd i) (hd k)⟩
theorem update_mem_smoothComplexTupleSet (h : smoothComplexTupleSet n) (i : Fin n)
    (g : (Fin 4 → ℝ) → ℂ) (hs : ContDiff ℝ ∞ g) (hd : tsupport g ⊆ tsupport (h.1 i)) :
    update h.1 i g ∈ smoothComplexTupleSet n := by
  refine mem_smoothComplexTupleSet_of_tsupport_subset h _ (fun k => ?_) (fun k => ?_)
  · by_cases hk : k = i
    · subst hk
      simpa using hs
    · simpa [hk] using (h.2.1 k).1
  · by_cases hk : k = i
    · subst hk
      simpa using hd
    · simp [hk]
theorem update_smul_mem_smoothComplexTupleSet (h : smoothComplexTupleSet n) (i : Fin n) (c : ℂ) :
    update h.1 i (c • h.1 i) ∈ smoothComplexTupleSet n :=
  update_mem_smoothComplexTupleSet h i _ (contDiff_const.smul (h.2.1 i).1)
    (tsupport_const_smul_subset c _)
theorem mem_smoothRealTupleSet_of_isRealValued (φ : smoothComplexTupleSet n)
    (hr : ∀ i, IsRealValued (φ.1 i)) : φ.1 ∈ smoothRealTupleSet n :=
  ⟨⟨fun i => ⟨hr i, ((φ.2.1 i).1).of_le (by exact_mod_cast le_top), (φ.2.1 i).2, subset_univ _⟩,
    φ.2.2⟩, fun i => (φ.2.1 i).1⟩
variable {T : smoothRealTupleSet n → ℝ}
theorem complexify_add (hT : IsRealMultilinearSmooth T) (i : Fin n)
    (h h' s : smoothComplexTupleSet n) (hag : AgreeExcept i h.1 h'.1)
    (hs : s.1 = update h.1 i (h.1 i + h'.1 i)) :
    complexify T s = complexify T h + complexify T h' := by
  unfold complexify
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [← mul_add, ← Complex.ofReal_add]
  congr 2
  refine (hT i ⟨_, tupleComplexParts_mem ε h⟩ ⟨_, tupleComplexParts_mem ε h'⟩ ?_).1
    ⟨_, tupleComplexParts_mem ε s⟩ ?_
  · intro k hk
    simp only [tupleComplexParts, hag k hk]
  · simp only [hs, tupleComplexParts_update_self, fnComplexPart_add]
    rfl
theorem complexify_ofReal_smul (hT : IsRealMultilinearSmooth T) (i : Fin n)
    (h s : smoothComplexTupleSet n) (r : ℝ) (hs : s.1 = update h.1 i ((r : ℂ) • h.1 i)) :
    complexify T s = (r : ℂ) * complexify T h := by
  unfold complexify
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  have key : T ⟨_, tupleComplexParts_mem ε s⟩ = r * T ⟨_, tupleComplexParts_mem ε h⟩ := by
    refine (hT i ⟨_, tupleComplexParts_mem ε h⟩ ⟨_, tupleComplexParts_mem ε h⟩
      fun _ _ => rfl).2 r ⟨_, tupleComplexParts_mem ε s⟩ ?_
    simp only [hs, tupleComplexParts_update_self, fnComplexPart_ofReal_smul]
    rfl
  rw [key]
  push_cast
  ring
def flipBit (i : Fin n) (ε : Fin n → Fin 2) : Fin n → Fin 2 := update ε i (1 - ε i)
theorem flipCoord_involutive (i : Fin n) : Involutive (flipBit i) := by
  intro ε
  have h : (1 : Fin 2) - (1 - ε i) = ε i := by
    generalize ε i = e
    revert e
    decide
  simp [flipBit, h]
theorem sum_update_add_eq (i : Fin n) (ε : Fin n → Fin 2) (b : Fin 2) :
    ∑ j, ((update ε i b j : Fin 2) : ℕ) + (ε i : ℕ) = ∑ j, (ε j : ℕ) + (b : ℕ) := by
  have e₁ := Finset.add_sum_erase Finset.univ (fun j => ((update ε i b j : Fin 2) : ℕ))
    (Finset.mem_univ i)
  have e₂ := Finset.add_sum_erase Finset.univ (fun j => (ε j : ℕ)) (Finset.mem_univ i)
  have e₃ : ∑ j ∈ Finset.univ.erase i, ((update ε i b j : Fin 2) : ℕ) =
      ∑ j ∈ Finset.univ.erase i, (ε j : ℕ) :=
    Finset.sum_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
  simp only [update_self] at e₁
  beta_reduce at e₂
  rw [← e₁, ← e₂, e₃]
  omega
theorem complexify_I_smul (hT : IsRealMultilinearSmooth T) (i : Fin n)
    (h s : smoothComplexTupleSet n) (hs : s.1 = update h.1 i (Complex.I • h.1 i)) :
    complexify T s = Complex.I * complexify T h := by
  unfold complexify
  rw [Finset.mul_sum, ← Equiv.sum_comp (flipCoord_involutive i).toPerm
    (fun ε => Complex.I * (Complex.I ^ (∑ j, (ε j : ℕ)) *
      (T ⟨_, tupleComplexParts_mem ε h⟩ : ℂ)))]
  refine Finset.sum_congr rfl fun ε _ => ?_
  simp only [Involutive.coe_toPerm]
  have hsum := sum_update_add_eq i ε (1 - ε i)
  have hcases : ε i = 0 ∨ ε i = 1 := by
    generalize ε i = e
    revert e
    decide
  rcases hcases with h0 | h1
  · have hp : ∑ j, ((flipBit i ε j : Fin 2) : ℕ) = ∑ j, (ε j : ℕ) + 1 := by
      simpa [flipBit, h0] using hsum
    have key : T ⟨_, tupleComplexParts_mem ε s⟩ =
        (-1 : ℝ) * T ⟨_, tupleComplexParts_mem (flipBit i ε) h⟩ := by
      refine (hT i ⟨_, tupleComplexParts_mem (flipBit i ε) h⟩
        ⟨_, tupleComplexParts_mem (flipBit i ε) h⟩ fun _ _ => rfl).2 (-1)
        ⟨_, tupleComplexParts_mem ε s⟩ ?_
      show tupleComplexParts ε s.1 = _
      rw [hs, tupleComplexParts_update ε h.1 i _ (1 - ε i), h0, fnComplexPart_zero_I_smul]
      simp [flipBit, tupleComplexParts, h0]
    rw [key, hp, pow_succ]
    push_cast
    linear_combination (-(Complex.I ^ (∑ j, (ε j : ℕ))) *
      (T ⟨_, tupleComplexParts_mem (flipBit i ε) h⟩ : ℂ)) * Complex.I_mul_I
  · have hp : ∑ j, ((flipBit i ε j : Fin 2) : ℕ) + 1 = ∑ j, (ε j : ℕ) := by
      simpa [flipBit, h1] using hsum
    have key : (⟨_, tupleComplexParts_mem ε s⟩ : smoothRealTupleSet n) =
        ⟨_, tupleComplexParts_mem (flipBit i ε) h⟩ := by
      refine Subtype.ext ?_
      show tupleComplexParts ε s.1 = tupleComplexParts (flipBit i ε) h.1
      rw [hs, tupleComplexParts_update ε h.1 i _ (1 - ε i), h1, fnComplexPart_one_I_smul]
      funext k
      by_cases hk : k = i
      · subst hk
        simp [flipBit, tupleComplexParts, h1]
      · simp [flipBit, tupleComplexParts, hk, h1]
    rw [key, ← hp, pow_succ]
    ring
theorem complexify_smul (hT : IsRealMultilinearSmooth T) (i : Fin n)
    (h s : smoothComplexTupleSet n) (c : ℂ) (hs : s.1 = update h.1 i (c • h.1 i)) :
    complexify T s = c * complexify T h := by
  let h₃ : smoothComplexTupleSet n := ⟨_, update_smul_mem_smoothComplexTupleSet h i Complex.I⟩
  let h₁ : smoothComplexTupleSet n := ⟨_, update_smul_mem_smoothComplexTupleSet h i (c.re : ℂ)⟩
  let h₂ : smoothComplexTupleSet n := ⟨_, update_smul_mem_smoothComplexTupleSet h₃ i (c.im : ℂ)⟩
  have e₃ : complexify T h₃ = Complex.I * complexify T h :=
    complexify_I_smul hT i h h₃ rfl
  have e₁ : complexify T h₁ = (c.re : ℂ) * complexify T h :=
    complexify_ofReal_smul hT i h h₁ c.re rfl
  have e₂ : complexify T h₂ = (c.im : ℂ) * complexify T h₃ :=
    complexify_ofReal_smul hT i h₃ h₂ c.im rfl
  have hag : AgreeExcept i h₁.1 h₂.1 := by
    intro k hk
    simp [h₁, h₂, h₃, hk]
  have hsum : s.1 = update h₁.1 i (h₁.1 i + h₂.1 i) := by
    rw [hs]
    simp only [h₁, h₂, h₃, update_self, update_idem]
    congr 1
    funext y
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    linear_combination (h.1 i y) * (Complex.re_add_im c).symm
  rw [complexify_add hT i h₁ h₂ s hag hsum, e₁, e₂, e₃]
  linear_combination (complexify T h) * (Complex.re_add_im c)
theorem isComplexMultilinearSmooth_complexify (hT : IsRealMultilinearSmooth T) :
    IsComplexMultilinearSmooth (complexify T) := fun i h h' hag =>
  ⟨fun s hs => complexify_add hT i h h' s hag hs,
    fun c s hs => complexify_smul hT i h s c hs⟩
theorem eq_zero_of_entry_eq_zero (hT : IsRealMultilinearSmooth T) (f : smoothRealTupleSet n)
    (i : Fin n) (hi : f.1 i = 0) : T f = 0 := by
  have := (hT i f f fun _ _ => rfl).2 0 f (by simp [hi])
  simpa using this
theorem complexify_agreesOnRealTuples (hT : IsRealMultilinearSmooth T) :
    AgreesOnRealTuples (complexify T) T := by
  intro f
  have hre : ∀ i y, (f.1 i y).im = 0 := fun i => f.2.1.1 i |>.1
  have hzero : tupleComplexParts (0 : Fin n → Fin 2) f.1 = f.1 := by
    funext i y
    simp only [tupleComplexParts, fnComplexPart, complexPart, Function.comp_apply, Pi.zero_apply,
      if_true]
    exact Complex.ext (by simp) (by simp [hre])
  unfold complexify
  rw [Finset.sum_eq_single (0 : Fin n → Fin 2)]
  · have : (⟨_, tupleComplexParts_mem 0 ⟨f.1, mem_smoothComplexTupleSet_of_real f⟩⟩ :
        smoothRealTupleSet n) = f := Subtype.ext hzero
    rw [this]
    simp
  · intro ε _ hε
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hε
    have h1 : ε i = 1 := by
      have hi' : ε i ≠ 0 := hi
      revert hi'
      generalize ε i = e
      revert e
      decide
    rw [eq_zero_of_entry_eq_zero hT ⟨_, tupleComplexParts_mem ε _⟩ i ?_]
    · simp
    · funext y
      simp [tupleComplexParts, fnComplexPart, complexPart, h1, hre]
  · simp
theorem eq_of_eq_on_real_entries (A B : smoothComplexTupleSet n → ℂ)
    (hA : IsComplexMultilinearSmooth A) (hB : IsComplexMultilinearSmooth B)
    (hAB : ∀ φ : smoothComplexTupleSet n, (∀ i, IsRealValued (φ.1 i)) → A φ = B φ) :
    A = B := by
  have main : ∀ S : Finset (Fin n), ∀ ψ : smoothComplexTupleSet n,
      (∀ i, i ∉ S → IsRealValued (ψ.1 i)) → A ψ = B ψ := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun ψ hψ => hAB ψ fun i => hψ i (by simp)
    | insert j S hj ih =>
      intro ψ hψ
      have hsm := (ψ.2.1 j).1
      let ψ₁ : smoothComplexTupleSet n := ⟨_, update_mem_smoothComplexTupleSet ψ j
        (fnComplexPart 0 (ψ.1 j)) (contDiff_fnComplexPart 0 hsm)
        (tsupport_fnComplexPart_subset 0 _)⟩
      let ψ₂ : smoothComplexTupleSet n := ⟨_, update_mem_smoothComplexTupleSet ψ j
        (fnComplexPart 1 (ψ.1 j)) (contDiff_fnComplexPart 1 hsm)
        (tsupport_fnComplexPart_subset 1 _)⟩
      let ψ₃ : smoothComplexTupleSet n :=
        ⟨_, update_smul_mem_smoothComplexTupleSet ψ₂ j Complex.I⟩
      have real₁ : ∀ i, i ∉ S → IsRealValued (ψ₁.1 i) := by
        intro i hi
        by_cases hij : i = j
        · subst hij
          simpa [ψ₁] using isRealValued_fnComplexPart 0 (ψ.1 i)
        · simpa [ψ₁, hij] using hψ i (by simp [hij, hi])
      have real₂ : ∀ i, i ∉ S → IsRealValued (ψ₂.1 i) := by
        intro i hi
        by_cases hij : i = j
        · subst hij
          simpa [ψ₂] using isRealValued_fnComplexPart 1 (ψ.1 i)
        · simpa [ψ₂, hij] using hψ i (by simp [hij, hi])
      have hag : AgreeExcept j ψ₁.1 ψ₃.1 := by
        intro k hk
        simp [ψ₁, ψ₂, ψ₃, hk]
      have hsum : ψ.1 = update ψ₁.1 j (ψ₁.1 j + ψ₃.1 j) := by
        simp only [ψ₁, ψ₂, ψ₃, update_self, update_idem]
        rw [← eq_re_add_I_smul_im, update_eq_self]
      have a₁ := (hA j ψ₁ ψ₃ hag).1 ψ hsum
      have b₁ := (hB j ψ₁ ψ₃ hag).1 ψ hsum
      have a₂ := (hA j ψ₂ ψ₂ fun _ _ => rfl).2 Complex.I ψ₃ rfl
      have b₂ := (hB j ψ₂ ψ₂ fun _ _ => rfl).2 Complex.I ψ₃ rfl
      rw [a₁, b₁, a₂, b₂, ih ψ₁ real₁, ih ψ₂ real₂]
  funext φ
  exact main Finset.univ φ fun i hi => absurd (Finset.mem_univ i) hi
theorem complexify_unique (hT : IsRealMultilinearSmooth T) (T' : smoothComplexTupleSet n → ℂ)
    (h₁ : IsComplexMultilinearSmooth T') (h₂ : AgreesOnRealTuples T' T) :
    T' = complexify T := by
  refine eq_of_eq_on_real_entries _ _ h₁ (isComplexMultilinearSmooth_complexify hT)
    fun φ hr => ?_
  have a := h₂ ⟨φ.1, mem_smoothRealTupleSet_of_isRealValued φ hr⟩
  have b := complexify_agreesOnRealTuples hT ⟨φ.1, mem_smoothRealTupleSet_of_isRealValued φ hr⟩
  exact a.trans b.symm
theorem zero_le_uniformNorm (f : (Fin 4 → ℝ) → ℂ) : 0 ≤ uniformNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem uniformNorm_fnComplexPart_le (e : Fin 2) {f : (Fin 4 → ℝ) → ℂ}
    (hf : f ∈ smoothCompactSet (Fin 4 → ℝ)) :
    uniformNorm (fnComplexPart e f) ≤ uniformNorm f := by
  obtain ⟨C, hC⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2
  refine ciSup_mono ⟨C, ?_⟩ fun y => norm_complexPart_le e (f y)
  rintro _ ⟨y, rfl⟩
  exact hC y
theorem partialDerivR4_fnComplexPart (e : Fin 2) {f : (Fin 4 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (c : Fin 4) (y : Fin 4 → ℝ) :
    partialDerivR4 c (fnComplexPart e f) y = complexPartCLM e (partialDerivR4 c f y) := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hl : Differentiable ℝ fun t : ℝ => y + t • Pi.single c (1 : ℝ) := by fun_prop
  have hg : HasDerivAt (fun t : ℝ => f (y + t • Pi.single c (1 : ℝ)))
      (partialDerivR4 c f y) 0 := ((hd.comp hl) 0).hasDerivAt
  have hc := ((complexPartCLM e).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg).deriv
  unfold partialDerivR4 at hc ⊢
  rw [← hc]
  congr 1
  funext t
  exact (complexPartCLM_apply e _).symm
theorem gradNorm_fnComplexPart_le (e : Fin 2) {f : (Fin 4 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (y : Fin 4 → ℝ) : gradNorm (fnComplexPart e f) y ≤ gradNorm f y := by
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun c _ => ?_)
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [partialDerivR4_fnComplexPart e hf, complexPartCLM_apply]
  exact norm_complexPart_le e _
theorem bddAbove_range_gradNorm {f : (Fin 4 → ℝ) → ℂ} (hf : f ∈ smoothCompactSet (Fin 4 → ℝ)) :
    BddAbove (range (gradNorm f)) := by apply _root_.YangMills.Construction.ConfigSpace.ModeCost.gradNorm_bddAbove <;> assumption
theorem gradSupNorm_fnComplexPart_le (e : Fin 2) {f : (Fin 4 → ℝ) → ℂ}
    (hf : f ∈ smoothCompactSet (Fin 4 → ℝ)) :
    gradSupNorm (fnComplexPart e f) ≤ gradSupNorm f :=
  ciSup_mono (bddAbove_range_gradNorm hf) fun y => gradNorm_fnComplexPart_le e hf.1 y
theorem setDistR4_mono {A A' B B' : Set (Fin 4 → ℝ)} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    setDistR4 A B ≤ setDistR4 A' B' := by apply _root_.YangMills.Construction.TestSpaces.UnifiedSeparatedTuples.setDistR4_anti <;> assumption
theorem norm_complexify_le {c : ℝ} {a : ℕ} {G : ℝ} (hb : SeparatedBallBound c a G T) {d : ℝ}
    (hd : 0 < d) (φ : smoothComplexTupleSet n) (hball : ∀ i, SupportInSmallBall (φ.1 i))
    (hsep : ∀ i i', i ≠ i' →
      ENNReal.ofReal d ≤ setDistR4 (tsupport (φ.1 i)) (tsupport (φ.1 i'))) :
    ‖complexify T φ‖ ≤ 2 ^ n * G * max 1 (d ^ (-(a : ℤ))) *
      ∏ i, max (uniformNorm (φ.1 i)) (c * gradSupNorm (φ.1 i)) := by
  obtain ⟨-, hc, hG, -, hbound⟩ := hb
  have hmax : 0 ≤ max 1 (d ^ (-(a : ℤ))) := le_max_of_le_left zero_le_one
  have term : ∀ ε : Fin n → Fin 2,
      ‖Complex.I ^ (∑ i, (ε i : ℕ)) * (T ⟨_, tupleComplexParts_mem ε φ⟩ : ℂ)‖ ≤
        G * max 1 (d ^ (-(a : ℤ))) *
          ∏ i, max (uniformNorm (φ.1 i)) (c * gradSupNorm (φ.1 i)) := by
    intro ε
    have hsub : ∀ i, tsupport (tupleComplexParts ε φ.1 i) ⊆ tsupport (φ.1 i) :=
      fun i => tsupport_fnComplexPart_subset _ _
    have hball' : ∀ i, SupportInSmallBall (tupleComplexParts ε φ.1 i) := by
      intro i
      obtain ⟨B, ϱ, hB, hϱ, hs⟩ := hball i
      exact ⟨B, ϱ, hB, hϱ, (hsub i).trans hs⟩
    have hsep' : HasSeparatedSupportsR4 (tupleComplexParts ε φ.1) d :=
      ⟨hd, fun i k hik => (hsep i k hik).trans (setDistR4_mono (hsub i) (hsub k))⟩
    have h := hbound d hd ⟨_, tupleComplexParts_mem ε φ⟩ hball' hsep'
    have hprod : ∏ i, max (uniformNorm (tupleComplexParts ε φ.1 i))
          (c * gradSupNorm (tupleComplexParts ε φ.1 i)) ≤
        ∏ i, max (uniformNorm (φ.1 i)) (c * gradSupNorm (φ.1 i)) := by
      refine Finset.prod_le_prod
        (fun i _ => le_max_of_le_left (zero_le_uniformNorm _)) fun i _ => ?_
      exact max_le_max (uniformNorm_fnComplexPart_le _ (φ.2.1 i))
        (mul_le_mul_of_nonneg_left (gradSupNorm_fnComplexPart_le _ (φ.2.1 i)) hc.le)
    rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact h.trans (mul_le_mul_of_nonneg_left hprod (mul_nonneg hG hmax))
  unfold complexify
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun ε _ => term ε).trans (le_of_eq ?_))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring
theorem complexify_unique_and_bounded : complexifyUniqueAndBounded := by
  intro n _ T hT
  refine ⟨⟨fun φ ε => ⟨tupleComplexParts_mem ε φ, fun i => tsupport_fnComplexPart_subset _ _⟩,
    isComplexMultilinearSmooth_complexify hT, complexify_agreesOnRealTuples hT,
    fun T' h₁ h₂ => complexify_unique hT T' h₁ h₂⟩, ?_⟩
  intro c a G hb d hd φ hball hsep
  exact norm_complexify_le hb hd φ hball hsep
end Complexify
end YangMills.Construction.ConfigSpace
end
