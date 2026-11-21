import YangMills.Construction.Continuum.SumOverIntegerPointsOfTheDecayWeight
import YangMills.Construction.Continuum.SumOverTheFrequenciesOfASystem
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FrequencySum
open ConfigSpace
theorem frequencySumBound_of_integerLatticeDecaySum
    (hLat : IntegerLatticeDecaySum) : FrequencySumBound := by
  intro n hn Q C f hf
  obtain ⟨hSum, hBd⟩ := hLat n hn
  have hs : 0 < Q.scale := Q.scale_pos
  have hc : 0 < Real.pi / Q.scale := div_pos Real.pi_pos hs
  let ofInt : (Fin n → Fin 4 → ℤ) → Q.freqLattice := fun ζ =>
    ⟨fun i c => Real.pi / Q.scale * ζ i c, ζ, fun _ _ => rfl⟩
  have hBij : Function.Bijective ofInt := by
    constructor
    · intro a b hab
      funext i c
      have h1 : Real.pi / Q.scale * (a i c : ℝ) = Real.pi / Q.scale * (b i c : ℝ) :=
        congrFun (congrFun (congrArg Subtype.val hab) i) c
      have h2 : ((a i c : ℤ) : ℝ) = b i c := mul_left_cancel₀ hc.ne' h1
      exact_mod_cast h2
    · rintro ⟨ξ, ζ, hζ⟩
      exact ⟨ζ, Subtype.ext (funext fun i => funext fun c => (hζ i c).symm)⟩
  let e := Equiv.ofBijective ofInt hBij
  have hNorm : ∀ ζ : Fin n → Fin 4 → ℤ,
      Q.scale * coordSupNorm ((e ζ : Q.freqLattice) : Config n) =
        Real.pi * coordSupNorm (fun i c => (ζ i c : ℝ)) := by
    intro ζ
    have h1 : coordSupNorm ((e ζ : Q.freqLattice) : Config n) =
        Real.pi / Q.scale * coordSupNorm (fun i c => (ζ i c : ℝ)) := by
      have h2 : ∀ i c, |((e ζ : Q.freqLattice) : Config n) i c| =
          Real.pi / Q.scale * |(ζ i c : ℝ)| := by
        intro i c
        change |Real.pi / Q.scale * (ζ i c : ℝ)| = _
        rw [abs_mul, abs_of_pos hc]
      simp only [coordSupNorm, h2, Real.mul_iSup_of_nonneg hc.le]
    rw [h1]
    field_simp
  have hNonneg : ∀ ζ : Fin n → Fin 4 → ℤ, 0 ≤ coordSupNorm (fun i c => (ζ i c : ℝ)) := fun ζ =>
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
  have hWeight : ∀ ζ : Fin n → Fin 4 → ℤ,
      0 < (1 + Real.pi * coordSupNorm (fun i c => (ζ i c : ℝ))) ^ (-(4 * (n : ℤ)) - 1) := fun ζ =>
    zpow_pos (by have := mul_nonneg Real.pi_pos.le (hNonneg ζ); linarith) _
  have hTerm : ∀ ζ : Fin n → Fin 4 → ℤ, ‖f (e ζ)‖ ≤
      C * (1 + Real.pi * coordSupNorm (fun i c => (ζ i c : ℝ))) ^ (-(4 * (n : ℤ)) - 1) := by
    intro ζ
    have h1 := hf (e ζ)
    rwa [hNorm ζ] at h1
  have hC : 0 ≤ C :=
    (mul_nonneg_iff_of_pos_right (hWeight 0)).1 ((norm_nonneg _).trans (hTerm 0))
  have hSumm : Summable (fun ζ : Fin n → Fin 4 → ℤ => ‖f (e ζ)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hTerm (hSum.mul_left C)
  refine ⟨(e.summable_iff (f := fun ξ => ‖f ξ‖)).1 hSumm, ?_⟩
  rw [← e.tsum_eq (fun ξ => ‖f ξ‖)]
  calc ∑' ζ : Fin n → Fin 4 → ℤ, ‖f (e ζ)‖
      ≤ ∑' ζ : Fin n → Fin 4 → ℤ,
          C * (1 + Real.pi * coordSupNorm (fun i c => (ζ i c : ℝ))) ^ (-(4 * (n : ℤ)) - 1) :=
        hSumm.tsum_le_tsum hTerm (hSum.mul_left C)
    _ = C * ∑' ζ : Fin n → Fin 4 → ℤ,
          (1 + Real.pi * coordSupNorm (fun i c => (ζ i c : ℝ))) ^ (-(4 * (n : ℤ)) - 1) :=
        tsum_mul_left
    _ ≤ C * (1 + 8 * (n : ℝ)) := mul_le_mul_of_nonneg_left hBd hC
end YangMills.Construction.FrequencySum
