import YangMills.Construction.PeriodicOperators.NormOfAMatrixWithABoundedKernelOfFiniteValence
import YangMills.Construction.PeriodicOperators.SumsOfExponentialsProof
import YangMills.Construction.Towers.ActionOfTheDifferencesOnPlaneWavesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.FiniteValenceNorm
theorem exists_mkQuot_eq (I : PeriodicData) (c : I.UnitQuot) : ∃ x, I.mkQuot 1 x = c :=
  Quot.exists_rep c
theorem translate_neg_translate {I : PeriodicData} (hI : IsPeriodic I) (n : Fin 4 → ℤ) (x : I.Carrier) :
    I.translate (-n) (I.translate n x) = x := by
  rw [← hI.translate_add, add_neg_cancel, hI.translate_zero]
theorem translate_translate_neg {I : PeriodicData} (hI : IsPeriodic I) (n : Fin 4 → ℤ) (x : I.Carrier) :
    I.translate n (I.translate (-n) x) = x := by
  rw [← hI.translate_add, neg_add_cancel, hI.translate_zero]
theorem mkQuot_translate (I : PeriodicData) (n : Fin 4 → ℤ) (x : I.Carrier) :
    I.mkQuot 1 (I.translate n x) = I.mkQuot 1 x :=
  (Quot.sound ⟨n, by simp⟩ : I.mkQuot 1 x = I.mkQuot 1 (I.translate n x)).symm
theorem exists_translate_of_mkQuot_eq {I : PeriodicData} (hI : IsPeriodic I) {x y : I.Carrier}
    (h : I.mkQuot 1 x = I.mkQuot 1 y) : ∃ n, y = I.translate n x := by apply _root_.YangMills.Construction.PeriodicOperators.ExponentialSums.exists_translate_of_mkQuot_eq <;> assumption
theorem quotWeight_eq_of_const (I : PeriodicData) (w : ℝ) (hw : ∀ x, I.weightOf x = w) (c : I.UnitQuot) :
    I.quotWeight 1 c = w := by apply _root_.YangMills.Construction.Tower.PlaneWaveCoboundaries.quotWeight_of_const <;> assumption
open Classical in
theorem sum_sq_le_of_card_rows_fibres {K K' X : Type} [Fintype K] [Fintype K'] (q : X → K)
    (S : K' → Finset X) (N : ℕ) (β : ℝ) (a : K → ℝ) (g : K' → ℝ) (hg₀ : ∀ k, 0 ≤ g k)
    (hg : ∀ k, g k ≤ β * ∑ x ∈ S k, a (q x)) (hrow : ∀ k, (S k).card ≤ N)
    (hfib : ∀ c, ((Finset.univ.sigma S).filter fun x => q x.2 = c).card ≤ N) :
    ∑ k, g k ^ 2 ≤ (N * β) ^ 2 * ∑ c, a c ^ 2 := by
  have hpt : ∀ k, g k ^ 2 ≤ β ^ 2 * N * ∑ x ∈ S k, a (q x) ^ 2 := by
    intro k
    have h₁ : (∑ x ∈ S k, a (q x)) ^ 2 ≤ (S k).card * ∑ x ∈ S k, a (q x) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h₀ : 0 ≤ ∑ x ∈ S k, a (q x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hN : ((S k).card : ℝ) ≤ N := by exact_mod_cast hrow k
    calc g k ^ 2 ≤ (β * ∑ x ∈ S k, a (q x)) ^ 2 := pow_le_pow_left₀ (hg₀ k) (hg k) 2
      _ = β ^ 2 * (∑ x ∈ S k, a (q x)) ^ 2 := mul_pow _ _ _
      _ ≤ β ^ 2 * ((S k).card * ∑ x ∈ S k, a (q x) ^ 2) :=
        mul_le_mul_of_nonneg_left h₁ (sq_nonneg _)
      _ ≤ β ^ 2 * (N * ∑ x ∈ S k, a (q x) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN h₀) (sq_nonneg _)
      _ = β ^ 2 * N * ∑ x ∈ S k, a (q x) ^ 2 := by ring
  have hsum : ∑ k, ∑ x ∈ S k, a (q x) ^ 2 ≤ N * ∑ c, a c ^ 2 := by
    rw [Finset.sum_sigma' Finset.univ S fun _ x => a (q x) ^ 2,
      ← Finset.sum_fiberwise (Finset.univ.sigma S) (fun x => q x.2), Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have hconst : ∀ x ∈ (Finset.univ.sigma S).filter (fun x => q x.2 = c),
        a (q x.2) ^ 2 = a c ^ 2 := by
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfib c) (sq_nonneg _)
  calc ∑ k, g k ^ 2 ≤ ∑ k, β ^ 2 * N * ∑ x ∈ S k, a (q x) ^ 2 :=
        Finset.sum_le_sum fun k _ => hpt k
    _ = β ^ 2 * N * ∑ k, ∑ x ∈ S k, a (q x) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ β ^ 2 * N * (N * ∑ c, a c ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (N * β) ^ 2 * ∑ c, a c ^ 2 := by ring
open Classical in
theorem card_fibre_le {I I' : PeriodicData} (hI : IsPeriodic I) (hI' : IsPeriodic I')
    [Fintype I'.UnitQuot] (C : I'.Carrier → I.Carrier → Prop) (N : ℕ)
    (hC : ∀ (n : Fin 4 → ℤ) y x, C y x → C (I'.translate n y) (I.translate n x))
    (hcol : ∀ x, {y | C y x}.encard ≤ N) (r : I'.UnitQuot → I'.Carrier)
    (hr : ∀ k, I'.mkQuot 1 (r k) = k) (S : I'.UnitQuot → Finset I.Carrier)
    (hS : ∀ k x, x ∈ S k ↔ C (r k) x) (x₀ : I.Carrier) :
    ((Finset.univ.sigma S).filter fun z => I.mkQuot 1 z.2 = I.mkQuot 1 x₀).card ≤ N := by
  have hn : ∀ x, I.mkQuot 1 x = I.mkQuot 1 x₀ → ∃ n, x = I.translate n x₀ :=
    fun x h => exists_translate_of_mkQuot_eq hI h.symm
  choose! n hn using hn
  set F := (Finset.univ.sigma S).filter fun z => I.mkQuot 1 z.2 = I.mkQuot 1 x₀ with hF
  let f : (Σ _ : I'.UnitQuot, I.Carrier) → I'.Carrier := fun z => I'.translate (-n z.2) (r z.1)
  have hinj : Set.InjOn f (F : Set (Σ _ : I'.UnitQuot, I.Carrier)) := by
    rintro ⟨k₁, x₁⟩ h₁ ⟨k₂, x₂⟩ h₂ e
    have h₁' := (Finset.mem_filter.mp (Finset.mem_coe.mp h₁)).2
    have h₂' := (Finset.mem_filter.mp (Finset.mem_coe.mp h₂)).2
    have e' : I'.translate (-n x₁) (r k₁) = I'.translate (-n x₂) (r k₂) := e
    have hk : k₁ = k₂ := by
      have := congrArg (I'.mkQuot 1) e'
      rwa [mkQuot_translate, mkQuot_translate, hr, hr] at this
    subst hk
    have hz : I'.translate (-n x₁ + n x₂) (r k₁) = r k₁ := by
      rw [hI'.translate_add, e', translate_translate_neg hI']
    have hnn : n x₂ = n x₁ := by
      have := hI'.free _ _ hz
      exact (neg_add_eq_zero.mp this).symm
    have hx : x₁ = x₂ := by
      rw [hn x₁ h₁', hn x₂ h₂', hnn]
    rw [hx]
  have himg : f '' (F : Set (Σ _ : I'.UnitQuot, I.Carrier)) ⊆ {y | C y x₀} := by
    rintro _ ⟨⟨k, x⟩, hz, rfl⟩
    have hz' := Finset.mem_filter.mp (Finset.mem_coe.mp hz)
    have hmem : C (r k) x := (hS k x).mp (Finset.mem_sigma.mp hz'.1).2
    have := hC (-n x) _ _ hmem
    have hback : I.translate (-n x) x = x₀ := by
      have h := translate_neg_translate hI (n x) x₀
      rwa [← hn x hz'.2] at h
    rw [hback] at this
    exact this
  have hle : ((F.card : ℕ) : ℕ∞) ≤ N := by
    rw [← Set.encard_coe_eq_coe_finsetCard, ← hinj.encard_image]
    exact (Set.encard_le_encard himg).trans (hcol x₀)
  exact_mod_cast hle
theorem holds : Claim := by
  intro I I' hI hI' w hw hw' M Θ C N β hβ hC hrow hcol hΘ hΘC hM
  classical
  have : Finite I.UnitQuot := hI.finite_quot
  have : Finite I'.UnitQuot := hI'.finite_quot
  let : Fintype I.UnitQuot := Fintype.ofFinite _
  let : Fintype I'.UnitQuot := Fintype.ofFinite _
  choose r hr using exists_mkQuot_eq I'
  have hfin : ∀ k, {x | C (r k) x}.Finite := fun k => Set.finite_of_encard_le_coe (hrow (r k))
  let S : I'.UnitQuot → Finset I.Carrier := fun k => (hfin k).toFinset
  have hS : ∀ k x, x ∈ S k ↔ C (r k) x := fun k x => by simp [S]
  have hScard : ∀ k, (S k).card ≤ N := by
    intro k
    have h := hrow (r k)
    rw [Set.Finite.encard_eq_coe_toFinset_card (hfin k)] at h
    exact_mod_cast h
  have hfib : ∀ c, ((Finset.univ.sigma S).filter fun z => I.mkQuot 1 z.2 = c).card ≤ N := by
    intro c
    obtain ⟨x₀, rfl⟩ := exists_mkQuot_eq I c
    exact card_fibre_le hI hI' C N hC hcol r hr S hS x₀
  have hbound : ∀ (f : I.UnitQuot → ℂ) k,
      ‖M f k‖ ≤ β * ∑ x ∈ S k, ‖f (I.mkQuot 1 x)‖ := by
    intro f k
    have h := hM f (r k)
    rw [hr k, tsum_eq_sum (s := S k) (fun x hx => by
      rw [hΘC _ _ (fun hc => hx ((hS k x).mpr hc)), zero_mul])] at h
    rw [h, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hΘ _ _) (norm_nonneg _)
  have hkey : ∀ f : I.UnitQuot → ℂ, ∑ k, ‖M f k‖ ^ 2 ≤ (N * β) ^ 2 * ∑ c, ‖f c‖ ^ 2 :=
    fun f => sum_sq_le_of_card_rows_fibres (I.mkQuot 1) S N β (fun c => ‖f c‖)
      (fun k => ‖M f k‖) (fun _ => norm_nonneg _) (hbound f) hScard hfib
  have hNβ : 0 ≤ (N : ℝ) * β := by positivity
  unfold quotHomNorm wOpNorm
  refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
  obtain ⟨-, -, hf₁⟩ := hf
  have hf₂ : ∑ c, I.quotWeight 1 c * ‖f c‖ ^ 2 ≤ 1 := by
    unfold wNorm at hf₁
    rw [tsum_fintype] at hf₁
    simpa using (Real.sqrt_le_iff.mp hf₁).2
  have e₁ : ∑ c, I.quotWeight 1 c * ‖f c‖ ^ 2 = w * ∑ c, ‖f c‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [quotWeight_eq_of_const I w hw c]
  have e₂ : ∑ k, I'.quotWeight 1 k * ‖M f k‖ ^ 2 = w * ∑ k, ‖M f k‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [quotWeight_eq_of_const I' w hw' k]
  unfold wNorm
  rw [tsum_fintype]
  refine Real.sqrt_le_iff.mpr ⟨hNβ, ?_⟩
  show ∑ k, I'.quotWeight 1 k * ‖M f k‖ ^ 2 ≤ (N * β) ^ 2
  by_cases hne : Nonempty I'.UnitQuot
  · obtain ⟨k⟩ := hne
    obtain ⟨y, -⟩ := exists_mkQuot_eq I' k
    have hwpos : 0 < w := by
      rw [← hw' y]
      exact hI'.weight_pos _
    calc ∑ k, I'.quotWeight 1 k * ‖M f k‖ ^ 2 = w * ∑ k, ‖M f k‖ ^ 2 := e₂
      _ ≤ w * ((N * β) ^ 2 * ∑ c, ‖f c‖ ^ 2) := mul_le_mul_of_nonneg_left (hkey f) hwpos.le
      _ = (N * β) ^ 2 * ∑ c, I.quotWeight 1 c * ‖f c‖ ^ 2 := by rw [e₁]; ring
      _ ≤ (N * β) ^ 2 * 1 := mul_le_mul_of_nonneg_left hf₂ (sq_nonneg _)
      _ = (N * β) ^ 2 := mul_one _
  · have := not_nonempty_iff.mp hne
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact sq_nonneg _
end YangMills.Construction.PeriodicOperators.FiniteValenceNorm
end
