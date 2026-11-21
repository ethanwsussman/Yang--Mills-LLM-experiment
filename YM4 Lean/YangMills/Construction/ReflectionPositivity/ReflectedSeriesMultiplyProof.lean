import YangMills.Construction.ReflectionPositivity.ReflectedSeriesMultiply
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice.ReflectionSeriesProducts
open NormalFamilies
variable {Γ : PeriodSublattice 1} {P : NormalLevelPair 1}
theorem conjReflect_mul (F G : Γ.QuotientField → ℂ) :
    Γ.conjReflect P (F * G) = Γ.conjReflect P F * Γ.conjReflect P G := by
  funext V
  simp [PeriodSublattice.conjReflect, PeriodSublattice.compPullback]
theorem norm_apply_le_one {S : Set Γ.QuotientLink} {f : Γ.QuotientField → ℂ}
    (hf : f ∈ Γ.boundedAlgebra S) (hsup : PeriodSublattice.supNorm f ≤ 1)
    (V : Γ.QuotientField) : ‖f V‖ ≤ 1 := by
  obtain ⟨-, ⟨M, hM⟩, -⟩ := hf
  have hbdd : BddAbove (Set.range fun V => ‖f V‖) := ⟨M, by rintro _ ⟨V, rfl⟩; exact hM V⟩
  exact (le_ciSup hbdd V).trans hsup
theorem norm_reflTerm_le {c : ℝ} (hc : 0 ≤ c) {f : Γ.QuotientField → ℂ}
    (hf : ∀ V, ‖f V‖ ≤ 1) (V : Γ.QuotientField) :
    ‖(c : ℂ) * f V * Γ.conjReflect P f V‖ ≤ c := by
  have hrefl : ‖Γ.conjReflect P f V‖ ≤ 1 := by
    simpa [PeriodSublattice.conjReflect, PeriodSublattice.compPullback] using hf _
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  calc c * ‖f V‖ * ‖Γ.conjReflect P f V‖ ≤ c * 1 * 1 := by
        have := hf V
        gcongr
    _ = c := by ring
theorem hasReflectionSeries_one (z : ℤ) : Γ.HasReflectionSeries z P 1 1 := by
  have hΘ : ∀ V, Γ.conjReflect P 1 V = 1 := fun V => by
    simp [PeriodSublattice.conjReflect, PeriodSublattice.compPullback]
  refine ⟨Unit, inferInstance, fun _ => 1, fun _ => 1, fun _ => zero_le_one,
    hasSum_unique _, fun _ => one_mem _, fun _ => ?_, fun V => Summable.of_finite, ?_⟩
  · refine Real.iSup_le (fun V => ?_) zero_le_one
    simp
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [Filter.eventually_ge_atTop ({()} : Finset Unit)] with t ht V
    have ht' : t = {()} := Finset.eq_singleton_iff_unique_mem.2
      ⟨ht (Finset.mem_singleton_self _), fun _ _ => rfl⟩
    simpa [ht', hΘ] using hε
theorem tendstoUniformly_prod_series {X A B : Type} {f : A → X → ℂ} {g : B → X → ℂ}
    {F : A × B → X → ℂ} {Sf Sg : X → ℂ} {c : A × B → ℝ}
    (hc : Summable c) (hbound : ∀ k V, ‖F k V‖ ≤ c k)
    (hF : ∀ k V, F k V = f k.1 V * g k.2 V)
    (hf : TendstoUniformly (fun (t : Finset A) V => ∑ k ∈ t, f k V) Sf Filter.atTop)
    (hg : TendstoUniformly (fun (t : Finset B) V => ∑ k ∈ t, g k V) Sg Filter.atTop) :
    TendstoUniformly (fun (t : Finset (A × B)) V => ∑ k ∈ t, F k V) (Sf * Sg) Filter.atTop := by
  have hsum : ∀ V, HasSum (fun k => F k V) (Sf V * Sg V) := fun V => by
    have hprod : Summable fun k : A × B => f k.1 V * g k.2 V :=
      Summable.of_norm_bounded hc fun k => by
        rw [← hF]
        exact hbound k V
    have hfV : HasSum (fun k => f k V) (Sf V) := hf.tendsto_at V
    have hgV : HasSum (fun k => g k V) (Sg V) := hg.tendsto_at V
    have heq : (fun k => F k V) = fun k : A × B => f k.1 V * g k.2 V :=
      funext fun k => hF k V
    rw [heq]
    exact HasSum.mul (f := fun k => f k V) (g := fun k => g k V) hfV hgV hprod
  have hunif := tendstoUniformly_tsum hc hbound
  have hlim : (fun V => ∑' k, F k V) = Sf * Sg := funext fun V => (hsum V).tsum_eq
  rwa [hlim] at hunif
theorem hasReflectionSeries_mul {z : ℤ} {S₁ S₂ : Γ.QuotientField → ℂ} {a₁ a₂ : ℝ}
    (h₁ : Γ.HasReflectionSeries z P S₁ a₁) (h₂ : Γ.HasReflectionSeries z P S₂ a₂) :
    Γ.HasReflectionSeries z P (S₁ * S₂) (a₁ * a₂) := by
  obtain ⟨A, _, c₁, f₁, hc₁, hs₁, hm₁, hn₁, -, hu₁⟩ := h₁
  obtain ⟨B, _, c₂, f₂, hc₂, hs₂, hm₂, hn₂, -, hu₂⟩ := h₂
  have hb₁ : ∀ k V, ‖f₁ k V‖ ≤ 1 := fun k V => norm_apply_le_one (hm₁ k) (hn₁ k) V
  have hb₂ : ∀ k V, ‖f₂ k V‖ ≤ 1 := fun k V => norm_apply_le_one (hm₂ k) (hn₂ k) V
  have hb : ∀ (k : A × B) V, ‖(f₁ k.1 * f₂ k.2) V‖ ≤ 1 := fun k V => by
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_one₀ (hb₁ _ _) (norm_nonneg _) (hb₂ _ _)
  have hc : ∀ k : A × B, 0 ≤ c₁ k.1 * c₂ k.2 := fun k => mul_nonneg (hc₁ _) (hc₂ _)
  have hsc : Summable fun k : A × B => c₁ k.1 * c₂ k.2 :=
    hs₁.summable.mul_of_nonneg hs₂.summable hc₁ hc₂
  have hbound : ∀ (k : A × B) V,
      ‖((c₁ k.1 * c₂ k.2 : ℝ) : ℂ) * (f₁ k.1 * f₂ k.2) V *
        Γ.conjReflect P (f₁ k.1 * f₂ k.2) V‖ ≤ c₁ k.1 * c₂ k.2 :=
    fun k V => norm_reflTerm_le (hc k) (hb k) V
  have hF : ∀ (k : A × B) V,
      ((c₁ k.1 * c₂ k.2 : ℝ) : ℂ) * (f₁ k.1 * f₂ k.2) V *
          Γ.conjReflect P (f₁ k.1 * f₂ k.2) V =
        ((c₁ k.1 : ℂ) * f₁ k.1 V * Γ.conjReflect P (f₁ k.1) V) *
          ((c₂ k.2 : ℂ) * f₂ k.2 V * Γ.conjReflect P (f₂ k.2) V) := fun k V => by
    rw [conjReflect_mul]
    simp only [Pi.mul_apply]
    push_cast
    ring
  have hunif := tendstoUniformly_prod_series hsc hbound hF hu₁ hu₂
  refine ⟨A × B, inferInstance, fun k => c₁ k.1 * c₂ k.2, fun k => f₁ k.1 * f₂ k.2, hc,
    hs₁.mul hs₂ hsc, fun k => mul_mem (hm₁ _) (hm₂ _), fun k => Real.iSup_le (hb k) zero_le_one,
    fun V => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hbound k V) hsc, ?_⟩
  exact hunif
theorem hasReflectionSeries_prod {z : ℤ} {ι : Type} (s : Finset ι) (S : ι → Γ.QuotientField → ℂ)
    (a : ι → ℝ) (h : ∀ i ∈ s, Γ.HasReflectionSeries z P (S i) (a i)) :
    Γ.HasReflectionSeries z P (∏ i ∈ s, S i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasReflectionSeries_one z
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact hasReflectionSeries_mul (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
theorem reflectionSeriesMul_holds : ReflectionSeriesMul := fun _ z _ =>
  ⟨hasReflectionSeries_one z, fun _ _ _ _ h₁ h₂ => hasReflectionSeries_mul h₁ h₂,
    fun _ s S a h => hasReflectionSeries_prod s S a h⟩
end YangMills.Construction.InfiniteLattice.ReflectionSeriesProducts
