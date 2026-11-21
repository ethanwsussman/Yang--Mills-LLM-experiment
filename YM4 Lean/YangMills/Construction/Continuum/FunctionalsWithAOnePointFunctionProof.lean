import YangMills.Construction.Continuum.FirstFactsOnTheTestSpaces
import YangMills.Construction.Continuum.FunctionalsWithAOnePointFunction
import YangMills.Construction.Continuum.TensorBoundsIntegrationBoundsAndDensity
import YangMills.Construction.Continuum.UncentringOfAFunctional
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TestSpaces.OnePointFunctional
variable {n : ℕ}
theorem evalOrZero_of_mem {p : ℕ} (T : flatSchwartzSet p → ℂ) {g : PointTuple p → ℂ}
    (h : g ∈ flatSchwartzSet p) : evalOrZero T g = T ⟨g, h⟩ :=
  dif_pos h
theorem card_lt_of_mem_ssubsets_univ {A : Finset (Fin n)}
    (hA : A ∈ (Finset.univ : Finset (Fin n)).ssubsets) : A.card < n := by
  simpa using Finset.card_lt_card (Finset.mem_ssubsets.1 hA)
theorem integrableFibers_and_integrateOut_mem (hInt : TestSpaceFacts.IntegrateOutBound)
    {k : ℕ} (hk : 4 < k) (hn : 0 < n) (φ : flatSchwartzSet n) {A : Finset (Fin n)}
    (hA : A ∈ (Finset.univ : Finset (Fin n)).ssubsets) :
    integrableFibers A φ.1 = Set.univ ∧
      integrateOut A φ.1 ∈ flatSchwartzSet (n - A.card) := by
  obtain ⟨h₁, h₂, -⟩ := (hInt n k hn hk φ.1 φ.2 A).1 (card_lt_of_mem_ssubsets_univ hA)
  refine ⟨?_, h₂⟩
  by_cases h0 : A.card = 0
  · rw [Finset.card_eq_zero.1 h0]
    exact integrableFibers_empty φ.1
  · exact Set.eq_univ_of_forall (h₁ (by omega))
theorem integrateOut_linear_combination (A : Finset (Fin n)) {φ ψ χ : PointTuple n → ℂ}
    (a b : ℂ) (hχ : χ = a • φ + b • ψ) (hφ : integrableFibers A φ = Set.univ)
    (hψ : integrableFibers A ψ = Set.univ) :
    integrateOut A χ = a • integrateOut A φ + b • integrateOut A ψ := by
  subst hχ
  funext y
  have h₁ : Integrable fun w : PointTuple A.card => φ (mergeTuples A y w) := by
    exact show y ∈ integrableFibers A φ from hφ ▸ Set.mem_univ y
  have h₂ : Integrable fun w : PointTuple A.card => ψ (mergeTuples A y w) := by
    exact show y ∈ integrableFibers A ψ from hψ ▸ Set.mem_univ y
  simp only [integrateOut, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_add (h₁.const_mul a) (h₂.const_mul b), integral_const_mul, integral_const_mul]
theorem schwingerFromCentred_isCLinear (hInt : TestSpaceFacts.IntegrateOutBound) {k : ℕ}
    (hk : 4 < k) (hn : 0 < n) (𝔠 : ℝ) {T : (p : ℕ) → flatSchwartzSet p → ℂ}
    (hT : ∀ p, 1 ≤ p → IsCLinearOnFlat (T p)) :
    IsCLinearOnFlat (schwingerFromCentred 𝔠 T n) := by
  intro a b φ ψ χ hχ
  have hφi := (hInt n k hn hk φ.1 φ.2 ∅).2.1
  have hψi := (hInt n k hn hk ψ.1 ψ.2 ∅).2.1
  have hint : ∫ x, χ.1 x = a * (∫ x, φ.1 x) + b * ∫ x, ψ.1 x := by
    rw [hχ]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add (hφi.const_mul a) (hψi.const_mul b), integral_const_mul, integral_const_mul]
  have hterm : ∀ A ∈ (Finset.univ : Finset (Fin n)).ssubsets,
      evalOrZero (T (n - A.card)) (integrateOut A χ.1) =
        a * evalOrZero (T (n - A.card)) (integrateOut A φ.1) +
          b * evalOrZero (T (n - A.card)) (integrateOut A ψ.1) := by
    intro A hA
    obtain ⟨hφs, hφm⟩ := integrableFibers_and_integrateOut_mem hInt hk hn φ hA
    obtain ⟨hψs, hψm⟩ := integrableFibers_and_integrateOut_mem hInt hk hn ψ hA
    obtain ⟨-, hχm⟩ := integrableFibers_and_integrateOut_mem hInt hk hn χ hA
    have hp : 1 ≤ n - A.card := by
      have := card_lt_of_mem_ssubsets_univ hA
      omega
    rw [evalOrZero_of_mem _ hφm, evalOrZero_of_mem _ hψm, evalOrZero_of_mem _ hχm]
    exact hT _ hp a b ⟨_, hφm⟩ ⟨_, hψm⟩ ⟨_, hχm⟩
      (integrateOut_linear_combination A a b hχ hφs hψs)
  have hsum : ∀ u v : Finset (Fin n) → ℂ,
      ∑ A ∈ (Finset.univ : Finset (Fin n)).ssubsets, (𝔠 : ℂ) ^ A.card * (a * u A + b * v A) =
        a * ∑ A ∈ (Finset.univ : Finset (Fin n)).ssubsets, (𝔠 : ℂ) ^ A.card * u A +
          b * ∑ A ∈ (Finset.univ : Finset (Fin n)).ssubsets, (𝔠 : ℂ) ^ A.card * v A := by
    intro u v
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [schwingerFromCentred]
  rw [Finset.sum_congr rfl fun A hA => by rw [hterm A hA], hsum, hint]
  ring
theorem prod_orderEmbOfFin_eq {R : Type*} [CommMonoid R] (s : Finset (Fin n)) {k : ℕ}
    (h : s.card = k) (f : Fin n → R) : ∏ t : Fin k, f (s.orderEmbOfFin h t) = ∏ i ∈ s, f i := by
  rw [← Finset.prod_coe_sort s f, ← Equiv.prod_comp (s.orderIsoOfFin h).toEquiv]
  exact Finset.prod_congr rfl fun t _ => by simp
theorem orderEmbOfFin_eq_cast (s : Finset (Fin n)) {k : ℕ} (h : s.card = k) (t : Fin s.card) :
    s.orderEmbOfFin rfl t = s.orderEmbOfFin h (Fin.cast h t) := by
  subst h
  rfl
theorem prod_mergeTuples {R : Type*} [CommMonoid R] (A : Finset (Fin n))
    (g : Fin n → (Fin 4 → ℝ) → R) (y : PointTuple (n - A.card)) (w : PointTuple A.card) :
    ∏ i, g i (mergeTuples A y w i) =
      (∏ t : Fin A.card, g (A.orderEmbOfFin rfl t) (w t)) *
        ∏ t : Fin (n - A.card), g (Aᶜ.orderEmbOfFin (card_compl_indices A) t) (y t) := by
  have hw : ∀ t, mergeTuples A y w (A.orderEmbOfFin rfl t) = w t := fun t =>
    congrFun (restrictTo_mergeTuples A y w) t
  have hy : ∀ t, mergeTuples A y w (Aᶜ.orderEmbOfFin (card_compl_indices A) t) = y t :=
    fun t => congrFun (restrictToCompl_mergeTuples A y w) t
  rw [← Finset.prod_mul_prod_compl A,
    ← prod_orderEmbOfFin_eq A rfl fun i => g i (mergeTuples A y w i),
    ← prod_orderEmbOfFin_eq Aᶜ (card_compl_indices A) fun i => g i (mergeTuples A y w i)]
  congr 1
  · exact Finset.prod_congr rfl fun t _ => congrArg (g _) (hw t)
  · exact Finset.prod_congr rfl fun t _ => congrArg (g _) (hy t)
theorem integral_tensorProdComplex (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    ∫ x, tensorProdComplex f x = ((∏ i, ∫ u, f i u : ℝ) : ℂ) := by
  have h : ∫ x : PointTuple n, tensorProd f x = ∏ i, ∫ u, f i u :=
    integral_fintype_prod_volume_eq_prod f
  rw [← h]
  exact integral_ofReal
theorem integrateOut_tensorProdComplex (A : Finset (Fin n)) (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    integrateOut A (tensorProdComplex f) =
      ((∏ i ∈ A, ∫ u, f i u : ℝ) : ℂ) •
        tensorProdComplex fun t => f (Aᶜ.orderEmbOfFin (card_compl_indices A) t) := by
  funext y
  have h : ∫ w : PointTuple A.card, ∏ t, f (A.orderEmbOfFin rfl t) (w t) =
      ∏ i ∈ A, ∫ u, f i u := by
    rw [integral_fintype_prod_volume_eq_prod fun t => f (A.orderEmbOfFin rfl t)]
    exact prod_orderEmbOfFin_eq A rfl fun i => ∫ u, f i u
  have h' : ∀ w : PointTuple A.card, tensorProdComplex f (mergeTuples A y w) =
      (((∏ t, f (A.orderEmbOfFin rfl t) (w t)) *
        tensorProd (fun t => f (Aᶜ.orderEmbOfFin (card_compl_indices A) t)) y : ℝ) : ℂ) := by
    intro w
    simp only [tensorProdComplex, tensorProd]
    rw [prod_mergeTuples A f y w]
  have e : integrateOut A (tensorProdComplex f) y = ∫ w : PointTuple A.card,
      (((∏ t, f (A.orderEmbOfFin rfl t) (w t)) *
        tensorProd (fun t => f (Aᶜ.orderEmbOfFin (card_compl_indices A) t)) y : ℝ) : ℂ) :=
    integral_congr_ae (Filter.Eventually.of_forall h')
  rw [e, integral_complex_ofReal, integral_mul_const, h, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_mul]
  rfl
def complComponents (X : SepTupleOfCard n) (A : Finset (Fin n)) : SepTupleOfCard (n - A.card) :=
  ⟨fun t => X.1 (Aᶜ.orderEmbOfFin (card_compl_indices A) t),
    fun _ => X.2.1 _, fun _ _ h => X.2.2 fun e => h ((Aᶜ.orderEmbOfFin _).injective e)⟩
theorem sepRestrict_compl_eq (X : SepTupleOfCard n) (A : Finset (Fin n)) :
    (⟨Aᶜ.card, sepRestrict X Aᶜ⟩ : SepTuple) = ⟨n - A.card, complComponents X A⟩ :=
  sepTuple_ext _ _ (card_compl_indices A) fun t =>
    congrArg X.1 (orderEmbOfFin_eq_cast Aᶜ (card_compl_indices A) t)
theorem schwingerFromCentred_tensorProdComplex (hInt : TestSpaceFacts.IntegrateOutBound)
    {k : ℕ} (hk : 4 < k) (hn : 0 < n) (𝔠 : ℝ) (σ : SepTuple → ℝ)
    {T : (p : ℕ) → flatSchwartzSet p → ℂ} (hT : IsSchwingerFamily (centredPart σ) T)
    (hmem : ∀ p, 1 ≤ p → ∀ Y : SepTupleOfCard p, HasSmoothComponents Set.univ Y.1 →
      tensorProdComplex Y.1 ∈ flatSchwartzSet p)
    (hunc : ∀ X : SepTupleOfCard n, σ ⟨n, X⟩ = ∑ A : Finset (Fin n),
      (∏ i ∈ A, (𝔠 * ∫ u, X.1 i u)) * centredPart σ ⟨Aᶜ.card, sepRestrict X Aᶜ⟩)
    (hempty : centredPart σ sepTupleNil = 1)
    (X : SepTupleOfCard n) (hs : HasSmoothComponents Set.univ X.1)
    (h : tensorProdComplex X.1 ∈ flatSchwartzSet n) :
    schwingerFromCentred 𝔠 T n ⟨_, h⟩ = σ ⟨n, X⟩ := by
  have hterm : ∀ A ∈ (Finset.univ : Finset (Fin n)).ssubsets,
      (𝔠 : ℂ) ^ A.card * evalOrZero (T (n - A.card))
          (integrateOut A (tensorProdComplex X.1)) =
        (((∏ i ∈ A, (𝔠 * ∫ u, X.1 i u)) * centredPart σ ⟨Aᶜ.card, sepRestrict X Aᶜ⟩ : ℝ) :
          ℂ) := by
    intro A hA
    have hp : 1 ≤ n - A.card := by
      have := card_lt_of_mem_ssubsets_univ hA
      omega
    obtain ⟨-, hψ⟩ := integrableFibers_and_integrateOut_mem hInt hk hn ⟨_, h⟩ hA
    have hsm : HasSmoothComponents Set.univ (complComponents X A).1 := fun _ => hs _
    have hg := hmem _ hp (complComponents X A) hsm
    have hval := (hT.1 _ hp).2.2 (complComponents X A) hsm hg
    have hlin := (hT.1 _ hp).1 ((∏ i ∈ A, ∫ u, X.1 i u : ℝ) : ℂ) 0 ⟨_, hg⟩ ⟨_, hg⟩ ⟨_, hψ⟩
      (by simp only [zero_smul, add_zero]; exact integrateOut_tensorProdComplex A X.1)
    rw [evalOrZero_of_mem _ hψ, hlin, hval, sepRestrict_compl_eq, Finset.prod_mul_distrib,
      Finset.prod_const]
    push_cast
    ring
  have hlast : ((𝔠 : ℂ) ^ n * ∫ x, tensorProdComplex X.1 x) =
      (((∏ i ∈ (Finset.univ : Finset (Fin n)), (𝔠 * ∫ u, X.1 i u)) *
        centredPart σ ⟨(Finset.univ : Finset (Fin n))ᶜ.card,
          sepRestrict X (Finset.univ : Finset (Fin n))ᶜ⟩ : ℝ) : ℂ) := by
    have he : (⟨(Finset.univ : Finset (Fin n))ᶜ.card,
        sepRestrict X (Finset.univ : Finset (Fin n))ᶜ⟩ : SepTuple) = sepTupleNil := by
      rw [Finset.compl_univ]
      exact sepRestrict_empty X
    rw [he, hempty, integral_tensorProdComplex, Finset.prod_mul_distrib, Finset.prod_const]
    simp
  simp only [schwingerFromCentred]
  rw [Finset.sum_congr rfl hterm, hlast, hunc X, Complex.ofReal_sum, ← Finset.powerset_univ]
  exact Finset.sum_erase_add _ _ (Finset.mem_powerset_self _)
theorem sum_ssubsets_add_pow_eq (x C : ℝ) :
    ∑ A ∈ (Finset.univ : Finset (Fin n)).ssubsets, x ^ A.card * C ^ (n - A.card) + x ^ n =
      (x + C) ^ n := by
  have h := Finset.sum_pow_mul_eq_add_pow x C (Finset.univ : Finset (Fin n))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  rw [← h, ← Finset.sum_erase_add _ _ (Finset.mem_powerset_self (Finset.univ : Finset (Fin n)))]
  simp [Finset.ssubsets]
theorem norm_schwingerFromCentred_le (hInt : TestSpaceFacts.IntegrateOutBound) {k : ℕ}
    (hk : 4 < k) (hn : 0 < n) {ϰ cσ Cσ cBar 𝔠 : ℝ} (hϰ : 0 ≤ ϰ) (hcσ : 0 ≤ cσ)
    (hCσ : 0 ≤ Cσ) (hcBar : 0 ≤ cBar) (h𝔠 : |𝔠| ≤ cBar) (hfin : weightIntegral k < ⊤)
    {T : (p : ℕ) → flatSchwartzSet p → ℂ}
    (hT : ∀ p, 1 ≤ p → ∀ φ : flatSchwartzSet p,
      ENNReal.ofReal ‖T p φ‖ ≤
        ENNReal.ofReal (cσ * Cσ ^ p * (p.factorial : ℝ) ^ ϰ) * weightedSeminorm (k * p) φ.1)
    (φ : flatSchwartzSet n) :
    ENNReal.ofReal ‖schwingerFromCentred 𝔠 T n φ‖ ≤
      ENNReal.ofReal ((1 + cσ) * onePointConst k Cσ cBar ^ n *
        (n.factorial : ℝ) ^ ϰ) * weightedSeminorm (k * n) φ.1 := by
  have hWfin : weightedSeminorm (k * n) φ.1 < ⊤ := φ.2.1.2 _ (Nat.mul_pos (by omega) hn)
  set w := (weightedSeminorm (k * n) φ.1).toReal with hw
  have hW : weightedSeminorm (k * n) φ.1 = ENNReal.ofReal w :=
    (ENNReal.ofReal_toReal hWfin.ne).symm
  have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
  set Ci := (weightIntegral k).toReal with hCi
  have hI : weightIntegral k = ENNReal.ofReal Ci := (ENNReal.ofReal_toReal hfin.ne).symm
  have hCi0 : 0 ≤ Ci := ENNReal.toReal_nonneg
  have hpow : ∀ m : ℕ, weightIntegral k ^ m * weightedSeminorm (k * n) φ.1 =
      ENNReal.ofReal (Ci ^ m * w) := fun m => by
    rw [hI, hW, ENNReal.ofReal_mul (pow_nonneg hCi0 m), ENNReal.ofReal_pow hCi0]
  set F := (n.factorial : ℝ) ^ ϰ with hF
  have hF1 : 1 ≤ F :=
    Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.2 n.factorial_ne_zero) hϰ
  set x := cBar * Ci with hx
  have hx0 : 0 ≤ x := mul_nonneg hcBar hCi0
  have h𝔠pow : ∀ m : ℕ, ‖(𝔠 : ℂ) ^ m‖ ≤ cBar ^ m := fun m => by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h𝔠 m
  have hterm : ∀ A ∈ (Finset.univ : Finset (Fin n)).ssubsets,
      ‖(𝔠 : ℂ) ^ A.card * evalOrZero (T (n - A.card)) (integrateOut A φ.1)‖ ≤
        x ^ A.card * Cσ ^ (n - A.card) * (cσ * F * w) := by
    intro A hA
    have hlt := card_lt_of_mem_ssubsets_univ hA
    obtain ⟨-, hψ⟩ := integrableFibers_and_integrateOut_mem hInt hk hn φ hA
    have hb := ((hInt n k hn hk φ.1 φ.2 A).1 hlt).2.2
    have hp : 1 ≤ n - A.card := by omega
    have h₁ := (hT _ hp ⟨_, hψ⟩).trans (mul_le_mul_right hb _)
    have hc0 : 0 ≤ cσ * Cσ ^ (n - A.card) * ((n - A.card).factorial : ℝ) ^ ϰ := by positivity
    rw [hpow, ← ENNReal.ofReal_mul hc0, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h₁
    have hfac : ((n - A.card).factorial : ℝ) ^ ϰ ≤ F :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.factorial_le (Nat.sub_le _ _)) hϰ
    rw [evalOrZero_of_mem _ hψ, norm_mul]
    calc ‖(𝔠 : ℂ) ^ A.card‖ * ‖T (n - A.card) ⟨_, hψ⟩‖
        ≤ cBar ^ A.card * (cσ * Cσ ^ (n - A.card) * F * (Ci ^ A.card * w)) := by
          refine mul_le_mul (h𝔠pow _) (h₁.trans ?_) (norm_nonneg _) (by positivity)
          gcongr
      _ = x ^ A.card * Cσ ^ (n - A.card) * (cσ * F * w) := by
          rw [hx, mul_pow]
          ring
  have hlast : ‖(𝔠 : ℂ) ^ n * ∫ x, φ.1 x‖ ≤ x ^ n * w := by
    have hb := (hInt n k hn hk φ.1 φ.2 ∅).2.2
    rw [hpow, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hb
    rw [norm_mul, hx, mul_pow, mul_assoc]
    exact mul_le_mul (h𝔠pow _) hb (norm_nonneg _) (by positivity)
  have hbin := sum_ssubsets_add_pow_eq (n := n) x Cσ
  have hsum0 : 0 ≤ ∑ A ∈ (Finset.univ : Finset (Fin n)).ssubsets,
      x ^ A.card * Cσ ^ (n - A.card) :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hxn0 : 0 ≤ x ^ n := by positivity
  have hreal : ‖schwingerFromCentred 𝔠 T n φ‖ ≤
      (1 + cσ) * onePointConst k Cσ cBar ^ n * F * w := by
    have hC : onePointConst k Cσ cBar = x + Cσ := by
      rw [onePointConst, add_comm]
    rw [hC]
    have h₂ : ‖schwingerFromCentred 𝔠 T n φ‖ ≤
        (∑ A ∈ (Finset.univ : Finset (Fin n)).ssubsets, x ^ A.card * Cσ ^ (n - A.card)) *
          (cσ * F * w) + x ^ n * w := by
      rw [Finset.sum_mul]
      exact (norm_add_le _ _).trans
        (add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm)) hlast)
    have h₃ : (∑ A ∈ (Finset.univ : Finset (Fin n)).ssubsets,
        x ^ A.card * Cσ ^ (n - A.card)) ≤ (x + Cσ) ^ n := by linarith
    have h₄ : x ^ n ≤ (x + Cσ) ^ n := by linarith
    have hFw : 0 ≤ cσ * F * w := by positivity
    calc ‖schwingerFromCentred 𝔠 T n φ‖ ≤ _ := h₂
      _ ≤ (x + Cσ) ^ n * (cσ * F * w) + (x + Cσ) ^ n * (F * w) := by
          refine add_le_add (mul_le_mul_of_nonneg_right h₃ hFw) ?_
          exact mul_le_mul h₄ (le_mul_of_one_le_left hw0 hF1) hw0 (by positivity)
      _ = (1 + cσ) * (x + Cσ) ^ n * F * w := by ring
  rw [hW, ← ENNReal.ofReal_mul (by
    have : 0 ≤ onePointConst k Cσ cBar := add_nonneg hCσ hx0
    positivity)]
  exact ENNReal.ofReal_le_ofReal hreal
def schwingerFromCentredFamily (𝔠 : ℝ) (T : (p : ℕ) → flatSchwartzSet p → ℂ) :
    (n : ℕ) → flatSchwartzSet n → ℂ
  | 0, φ => φ.1 fun i => i.elim0
  | m + 1, φ => schwingerFromCentred 𝔠 T (m + 1) φ
theorem growth_holds (hFirst : Elementary.BasicProperties)
    (hThree : TestSpaceFacts.Statement) (hUnc : UncentringFormula) : growth := by
  intro k ϰ cσ Cσ cBar 𝔠 σ T hk hϰ hcσ hCσ hcBar hσ hone h𝔠 hS hgrowth
  have hInt : TestSpaceFacts.IntegrateOutBound := hThree.2.2.1
  have hfin : weightIntegral k < ⊤ := ((hFirst 1 one_pos).2.2.2.2 k hk).2.1
  have hmem : ∀ p, 1 ≤ p → ∀ Y : SepTupleOfCard p, HasSmoothComponents Set.univ Y.1 →
      tensorProdComplex Y.1 ∈ flatSchwartzSet p := fun p hp Y hY =>
    (((hFirst p hp).2.2.2.1 Set.univ isOpen_univ Y.1 Y.2).2 hY).2.1
  obtain ⟨hUn, hempty, -⟩ := hUnc σ 𝔠 hσ hone
  have hLin : ∀ p, 1 ≤ p → IsCLinearOnFlat (T p) := fun p hp => (hS.1 p hp).1
  have hC0 : 0 ≤ onePointConst k Cσ cBar :=
    add_nonneg hCσ (mul_nonneg hcBar ENNReal.toReal_nonneg)
  have hlinear : ∀ n, 1 ≤ n → IsCLinearOnFlat (schwingerFromCentred 𝔠 T n) := fun n hn =>
    schwingerFromCentred_isCLinear hInt hk hn 𝔠 hLin
  have htensor : ∀ n, 1 ≤ n → ∀ X : SepTupleOfCard n, HasSmoothComponents Set.univ X.1 →
      ∀ h : tensorProdComplex X.1 ∈ flatSchwartzSet n,
        schwingerFromCentred 𝔠 T n ⟨_, h⟩ = σ ⟨n, X⟩ := fun n hn X hs h =>
    schwingerFromCentred_tensorProdComplex hInt hk hn 𝔠 σ hS hmem (hUn n hn) hempty X hs h
  have hbound : ∀ n, 1 ≤ n → ∀ φ : flatSchwartzSet n,
      ENNReal.ofReal ‖schwingerFromCentred 𝔠 T n φ‖ ≤
        ENNReal.ofReal ((1 + cσ) * onePointConst k Cσ cBar ^ n *
          (n.factorial : ℝ) ^ ϰ) * weightedSeminorm (k * n) φ.1 := fun n hn φ =>
    norm_schwingerFromCentred_le hInt hk hn hϰ hcσ hCσ hcBar h𝔠 hfin hgrowth φ
  refine ⟨fun n hn => ⟨fun φ => ⟨(hInt n k hn hk φ.1 φ.2 ∅).2.1, fun A hA =>
    integrableFibers_and_integrateOut_mem hInt hk hn φ hA⟩, hlinear n hn, htensor n hn,
    hbound n hn⟩, ?_⟩
  refine ⟨by omega, by linarith, hC0, hϰ, schwingerFromCentredFamily 𝔠 T,
    ⟨fun n hn => ?_, fun φ => rfl⟩, fun n hn φ => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨hlinear _ hn, ⟨k * (m + 1), _, Nat.mul_pos (by omega) hn,
      by positivity, hbound _ hn⟩, htensor _ hn⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact hbound _ hn φ
end YangMills.Construction.TestSpaces.OnePointFunctional
