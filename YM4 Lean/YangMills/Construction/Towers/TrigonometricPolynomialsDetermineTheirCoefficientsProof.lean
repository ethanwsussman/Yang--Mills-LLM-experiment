import YangMills.Construction.Towers.TrigonometricPolynomialsDetermineTheirCoefficients
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FourierCoefficients
open Tower.AbelianFieldFacts
variable {E : Type}
def fourierModeHom [Finite E] (n : E → ℤ) : Multiplicative (E → ℝ) →* ℂ where
  toFun φ := fourierMode n (Multiplicative.toAdd φ)
  map_one' := by
    simp [fourierMode]
  map_mul' φ ψ := by
    have hsum : (∑ᶠ β, (n β : ℝ) * (Multiplicative.toAdd (φ * ψ) : E → ℝ) β : ℝ) =
        (∑ᶠ β, (n β : ℝ) * (Multiplicative.toAdd φ : E → ℝ) β) +
          ∑ᶠ β, (n β : ℝ) * (Multiplicative.toAdd ψ : E → ℝ) β := by
      rw [← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
      refine finsum_congr fun β => ?_
      simp [mul_add]
    simp only [fourierMode]
    rw [hsum, ← Complex.exp_add]
    congr 1
    push_cast
    ring
theorem fourierMode_single [Finite E] [DecidableEq E] (n : E → ℤ) (β : E) (t : ℝ) :
    fourierMode n (Pi.single β t) = Complex.exp (Complex.I * (((n β : ℝ) * t : ℝ) : ℂ)) := by
  have hsum : (∑ᶠ α, (n α : ℝ) * (Pi.single β t : E → ℝ) α : ℝ) = (n β : ℝ) * t := by
    rw [finsum_eq_single _ β]
    · simp
    · intro α hα
      simp [Pi.single_eq_of_ne hα]
  simp only [fourierMode]
  rw [hsum]
theorem fourierModeHom_injective [Finite E] :
    Function.Injective (fourierModeHom : (E → ℤ) → Multiplicative (E → ℝ) →* ℂ) := by
  classical
  intro n m hnm
  funext β
  by_contra hne
  have hd : ((n β - m β : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hne
  set d : ℝ := ((n β - m β : ℤ) : ℝ) with hdef
  have hval := DFunLike.congr_fun hnm (Multiplicative.ofAdd (Pi.single β (Real.pi / d)))
  have hval' : fourierMode n (Pi.single β (Real.pi / d)) =
      fourierMode m (Pi.single β (Real.pi / d)) := hval
  rw [fourierMode_single, fourierMode_single] at hval'
  have hsplit : (((n β : ℝ) * (Real.pi / d) : ℝ) : ℂ) =
      (((m β : ℝ) * (Real.pi / d) : ℝ) : ℂ) + (Real.pi : ℂ) := by
    have : (n β : ℝ) * (Real.pi / d) = (m β : ℝ) * (Real.pi / d) + Real.pi := by
      have hn : (n β : ℝ) = (m β : ℝ) + d := by
        simp [hdef]
      rw [hn]
      field_simp
    rw [this]
    push_cast
    ring
  rw [hsplit, mul_add, Complex.exp_add, mul_comm Complex.I (Real.pi : ℂ), Complex.exp_pi_mul_I] at hval'
  have hz := Complex.exp_ne_zero (Complex.I * (((m β : ℝ) * (Real.pi / d) : ℝ) : ℂ))
  have h2 : (-1 : ℂ) = 1 := by
    apply mul_left_cancel₀ hz
    simpa using hval'
  norm_num at h2
theorem fourierCoeffsDetermined_holds : FourierCoeffsDetermined := by
  classical
  intro E hfin _ Q γ γ' hγ hγ'
  have hli : LinearIndependent ℂ
      (fun n : E → ℤ => ((fourierModeHom n : Multiplicative (E → ℝ) →* ℂ) :
        Multiplicative (E → ℝ) → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative (E → ℝ)) ℂ).comp _ fourierModeHom_injective
  let s : Finset (E → ℤ) := hγ.1.toFinset ∪ hγ'.1.toFinset
  have hs : Function.support γ ⊆ s := fun n hn => by
    simp only [s, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl hn
  have hs' : Function.support γ' ⊆ s := fun n hn => by
    simp only [s, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inr hn
  have hexpand : ∀ (c : (E → ℤ) → ℂ), Function.support c ⊆ s → ∀ φ : E → ℝ,
      ∑ᶠ n, c n * fourierMode n φ = ∑ n ∈ s, c n * fourierMode n φ := by
    intro c hc φ
    refine finsum_eq_sum_of_support_subset _ ?_
    intro n hn
    exact hc (fun h0 => hn (by simp [h0]))
  have hzero : ∑ n ∈ s, (γ n - γ' n) •
      ((fourierModeHom n : Multiplicative (E → ℝ) →* ℂ) : Multiplicative (E → ℝ) → ℂ) = 0 := by
    funext φ
    have h1 := hγ.2 (Multiplicative.toAdd φ)
    have h2 := hγ'.2 (Multiplicative.toAdd φ)
    rw [hexpand γ hs] at h1
    rw [hexpand γ' hs'] at h2
    have h3 := h1.symm.trans h2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    change ∑ n ∈ s, (γ n - γ' n) * fourierMode n (Multiplicative.toAdd φ) = 0
    simp only [sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h3
  have hall := linearIndependent_iff'.mp hli s (fun n => γ n - γ' n) hzero
  funext n
  by_cases hn : n ∈ s
  · exact sub_eq_zero.mp (hall n hn)
  · have h1 : γ n = 0 := by
      by_contra h
      exact hn (hs h)
    have h2 : γ' n = 0 := by
      by_contra h
      exact hn (hs' h)
    rw [h1, h2]
end YangMills.Construction.Tower.FourierCoefficients
end
