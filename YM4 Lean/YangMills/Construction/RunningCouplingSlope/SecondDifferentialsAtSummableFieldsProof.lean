import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBoundedProof
import YangMills.Construction.PeriodicOperators.InverseOfAPeriodicOperatorOnAnOpenStrip
import YangMills.Construction.PeriodicOperators.KernelsOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.MatricesOnATorusInCoordinates
import YangMills.Construction.PeriodicOperators.OrbitsOfAPeriodicIndexSetProof
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.PeriodicOperators.RealLogarithmOfTheDeterminantOfLinearMaps
import YangMills.Construction.PeriodicOperators.SecondDifferentialsAreBoundedOnAStrip
import YangMills.Construction.PeriodicOperators.SymbolOfAnOperatorWithDecay
import YangMills.Construction.PeriodicOperators.TheSecondDifferentialOnATorusByTraces
import YangMills.Construction.PeriodicOperators.TheTracesOnTheToriAtUnitFieldsConverge
import YangMills.Construction.PeriodicOperators.WaveSpacesOnATorus
import YangMills.Construction.RunningCouplingSlope.SecondDifferentialsAtSummableFields
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.SummableFields
open YangMills.Construction.PeriodicOperators YangMills.Construction.PeriodicOperators.LogDetSecondDerivs
open YangMills.Construction.PeriodicOperators.UnitFieldTraces
open YangMills.Construction.InfiniteLattice (AmbientSpace)
variable {F I : PeriodicData} {s : ℕ}
private theorem translate_neg_translate (hF : IsPeriodic F) (n : Fin 4 → ℤ) (ι : F.Carrier) :
    F.translate (-n) (F.translate n ι) = ι := by
  rw [← hF.translate_add, add_neg_cancel, hF.translate_zero]
private theorem mkQuot_eq_iff (hF : IsPeriodic F) (s : ℕ) (ι ι' : F.Carrier) :
    F.mkQuot s ι = F.mkQuot s ι' ↔ ∃ n : Fin 4 → ℤ, ι' = F.translate (s • n) ι := by apply _root_.YangMills.Construction.PeriodicOperators.QuotOrbits.mkQuot_eq_iff <;> assumption
private def dualPoint (σ : ℝ) (s : ℕ) (m : Fin 4 → Fin s) : AmbientSpace :=
  fun μ => ((σ * ((m μ : ℕ) : ℝ) : ℝ)) * (2 * Real.pi / s)
private theorem sum_char_one_dim {s : ℕ} (hs : 0 < s) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (n : ℤ) :
    (∑ m : Fin s, Complex.exp (Complex.I *
        (((σ * ((m : ℕ) : ℝ) * (2 * Real.pi / s) * (n : ℝ) : ℝ)) : ℂ))) =
      if (s : ℤ) ∣ n then (s : ℂ) else 0 := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  set ω : ℂ := Complex.exp (Complex.I * (((σ * (2 * Real.pi / s) * (n : ℝ) : ℝ)) : ℂ)) with hω
  have hterm : ∀ m : Fin s, Complex.exp (Complex.I *
      (((σ * ((m : ℕ) : ℝ) * (2 * Real.pi / s) * (n : ℝ) : ℝ)) : ℂ)) = ω ^ (m : ℕ) := by
    intro m
    rw [hω, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun i => ω ^ i) s]
  have hpow : ω ^ s = 1 := by
    rw [hω, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    rcases hσ with rfl | rfl
    · refine ⟨n, ?_⟩
      push_cast
      field_simp
    · refine ⟨-n, ?_⟩
      push_cast
      field_simp
  by_cases hd : (s : ℤ) ∣ n
  · obtain ⟨t, rfl⟩ := hd
    have hone : ω = 1 := by
      rw [hω, Complex.exp_eq_one_iff]
      rcases hσ with rfl | rfl
      · refine ⟨t, ?_⟩
        push_cast
        field_simp
      · refine ⟨-t, ?_⟩
        push_cast
        field_simp
    simp [hone]
  · have hne : ω ≠ 1 := by
      intro h1
      rw [hω, Complex.exp_eq_one_iff] at h1
      obtain ⟨t, ht⟩ := h1
      apply hd
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have h3 : ((σ : ℂ) * n - t * s) * (2 * Real.pi * Complex.I / s) = 0 := by
        have e : ((σ : ℂ) * n - t * s) * (2 * Real.pi * Complex.I / s) =
            Complex.I * (((σ * (2 * Real.pi / s) * (n : ℝ) : ℝ)) : ℂ) -
              t * (2 * Real.pi * Complex.I) := by
          push_cast
          field_simp
        rw [e, ht, sub_self]
      have h4 : (2 * Real.pi * Complex.I / s : ℂ) ≠ 0 :=
        div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero) hsC
      have h5 : (σ : ℂ) * n = t * s := sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right h4)
      rcases hσ with rfl | rfl
      · refine ⟨t, ?_⟩
        have : (n : ℂ) = ((s : ℤ) * t : ℤ) := by
          push_cast
          push_cast at h5
          linear_combination h5
        exact_mod_cast this
      · refine ⟨-t, ?_⟩
        have : (n : ℂ) = ((s : ℤ) * -t : ℤ) := by
          push_cast
          push_cast at h5
          linear_combination -h5
        exact_mod_cast this
    rw [if_neg hd, geom_sum_eq hne, hpow, sub_self, zero_div]
private theorem sum_char {s : ℕ} (hs : 0 < s) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (n : Fin 4 → ℤ) :
    (∑ m : Fin 4 → Fin s, Complex.exp (Complex.I *
        bilinDot (toComplexVec (dualPoint σ s m)) (toComplexVec (castVec n)))) =
      if ∀ μ, (s : ℤ) ∣ n μ then (s : ℂ) ^ 4 else 0 := by
  have hprod : ∀ m : Fin 4 → Fin s, Complex.exp (Complex.I *
        bilinDot (toComplexVec (dualPoint σ s m)) (toComplexVec (castVec n))) =
      ∏ μ, Complex.exp (Complex.I *
        (((σ * ((m μ : ℕ) : ℝ) * (2 * Real.pi / s) * (n μ : ℝ) : ℝ)) : ℂ)) := by
    intro m
    rw [← Complex.exp_sum, ← Finset.mul_sum]
    congr 2
    simp only [bilinDot, toComplexVec, dualPoint, castVec]
    refine Finset.sum_congr rfl fun μ _ => ?_
    push_cast
    ring
  simp only [hprod]
  have := (Finset.prod_univ_sum (fun _ : Fin 4 => (Finset.univ : Finset (Fin s)))
    (fun μ (m : Fin s) => Complex.exp (Complex.I *
      (((σ * ((m : ℕ) : ℝ) * (2 * Real.pi / s) * (n μ : ℝ) : ℝ)) : ℂ)))).symm
  rw [Fintype.piFinset_univ] at this
  rw [this]
  simp only [sum_char_one_dim hs hσ]
  by_cases h : ∀ μ, (s : ℤ) ∣ n μ
  · simp [h]
  · rw [if_neg h]
    obtain ⟨μ, hμ⟩ := not_forall.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ μ) (if_neg hμ)
private theorem dualPoint_mem (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (s : ℕ) (m : Fin 4 → Fin s) :
    dualPoint σ s m ∈ dualLattice s := by
  rcases hσ with rfl | rfl
  · exact ⟨fun μ => ((m μ : ℕ) : ℤ), fun μ => by simp [dualPoint]⟩
  · exact ⟨fun μ => -((m μ : ℕ) : ℤ), fun μ => by simp [dualPoint]⟩
open Classical in
private theorem descendField_blochWave (hW : BlochDecomposition.Facts F) {s : ℕ} (hs : 0 < s)
    {p : AmbientSpace} (hp : p ∈ dualLattice s) (φ : F.UnitQuot → ℂ) (ι : F.Carrier) :
    descendField F s (blochWave F (toComplexVec p) φ) (F.mkQuot s ι) =
      blochWave F (toComplexVec p) φ ι := by
  obtain ⟨g, hg⟩ := hW.blochWave_descends s hs p hp φ
  have hex : ∃ z, ∀ κ, F.mkQuot s κ = F.mkQuot s ι → blochWave F (toComplexVec p) φ κ = z :=
    ⟨g (F.mkQuot s ι), fun κ hκ => by rw [← hκ, hg]⟩
  exact (Classical.epsilon_spec hex ι rfl).symm
private def phase (σ : ℝ) (s : ℕ) (m : Fin 4 → Fin s) (ι₀ : F.Carrier) : ℂ :=
  Complex.exp (-(Complex.I * bilinDot (toComplexVec (dualPoint σ s m))
    (toComplexVec (F.pos ι₀))))
open Classical in
private theorem quotIndicator_eq_mean (hF : IsPeriodic F) (hW : BlochDecomposition.Facts F)
    {s : ℕ} (hs : 0 < s) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (ι₀ : F.Carrier) :
    quotIndicator F s ι₀ = ((s : ℂ) ^ 4)⁻¹ • ∑ m : Fin 4 → Fin s, phase σ s m ι₀ •
      descendField F s (blochWave F (toComplexVec (dualPoint σ s m))
        (Pi.single (F.mkQuot 1 ι₀) 1)) := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  funext c
  obtain ⟨ι, rfl⟩ : ∃ ι, F.mkQuot s ι = c := Quot.exists_rep c
  · simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    simp only [descendField_blochWave hW hs (dualPoint_mem σ hσ s _), blochWave]
    by_cases h1 : F.mkQuot 1 ι = F.mkQuot 1 ι₀
    · obtain ⟨n, hn⟩ := (mkQuot_eq_iff hF 1 ι₀ ι).1 h1.symm
      rw [one_smul] at hn
      have hpos : F.pos ι = F.pos ι₀ + castVec n := by
        rw [hn, hF.pos_translate]
      have hterm : ∀ m : Fin 4 → Fin s, phase σ s m ι₀ *
          (Complex.exp (Complex.I * bilinDot (toComplexVec (dualPoint σ s m))
            (toComplexVec (F.pos ι))) *
            (Pi.single (F.mkQuot 1 ι₀) 1 : F.UnitQuot → ℂ) (F.mkQuot 1 ι)) =
          Complex.exp (Complex.I * bilinDot (toComplexVec (dualPoint σ s m))
            (toComplexVec (castVec n))) := by
        intro m
        rw [h1, Pi.single_eq_same, mul_one, phase, ← Complex.exp_add, hpos]
        congr 1
        simp only [bilinDot, toComplexVec, Pi.add_apply]
        push_cast
        simp only [mul_add, Finset.sum_add_distrib]
        ring
      simp only [hterm]
      rw [sum_char hs hσ]
      by_cases hd : ∀ μ, (s : ℤ) ∣ n μ
      · have hc : F.mkQuot s ι = F.mkQuot s ι₀ := by
          refine ((mkQuot_eq_iff hF s ι₀ ι).2 ?_).symm
          choose t ht using hd
          refine ⟨t, ?_⟩
          rw [hn]
          congr 1
          funext μ
          simp [ht μ]
        simp only [quotIndicator, if_pos hc, if_pos hd]
        field_simp
      · have hc : F.mkQuot s ι ≠ F.mkQuot s ι₀ := by
          intro hc
          obtain ⟨t, ht⟩ := (mkQuot_eq_iff hF s ι₀ ι).1 hc.symm
          apply hd
          intro μ
          have hfree : n = s • t := by
            have e : F.translate n ι₀ = F.translate (s • t) ι₀ := by rw [← hn, ht]
            have e2 := congrArg (F.translate (-(s • t))) e
            rw [translate_neg_translate hF, ← hF.translate_add] at e2
            have e3 := hF.free _ _ e2
            exact (add_neg_eq_zero.1 e3)
          refine ⟨t μ, ?_⟩
          rw [hfree]
          simp
        simp only [quotIndicator, if_neg hc, if_neg hd, mul_zero]
    · have hc : F.mkQuot s ι ≠ F.mkQuot s ι₀ := by
        intro hc
        obtain ⟨t, ht⟩ := (mkQuot_eq_iff hF s ι₀ ι).1 hc.symm
        exact h1 ((mkQuot_eq_iff hF 1 ι₀ ι).2 ⟨s • t, by rw [one_smul]; exact ht⟩).symm
      have hz : ∀ m : Fin 4 → Fin s, phase σ s m ι₀ *
          (Complex.exp (Complex.I * bilinDot (toComplexVec (dualPoint σ s m))
            (toComplexVec (F.pos ι))) *
            (Pi.single (F.mkQuot 1 ι₀) 1 : F.UnitQuot → ℂ) (F.mkQuot 1 ι)) = 0 := by
        intro m
        rw [Pi.single_eq_of_ne h1]
        simp
      simp only [hz, quotIndicator, if_neg hc, Finset.sum_const_zero, mul_zero]
private theorem exists_bilin_quotTraceDefect (hCoord : TorusMatrixCoordinates.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} {ρ R : ℝ}
    (hMeet : IsLocalWith F I I T ρ R) {s : ℕ} (hs : 0 < s) (h4 : 4 * R < s) :
    ∃ B : (F.QuotMod s → ℂ) →ₗ[ℂ] (F.QuotMod s → ℂ) →ₗ[ℂ] ℂ,
      ∀ ζ ζ', B ζ ζ' = quotTraceDefect F I T s ζ ζ' := by
  obtain ⟨hl1, hl2, hl3, -, -⟩ := hCoord F I hF hI T ρ R hMeet s hs h4
  refine ⟨LinearMap.mk₂ ℂ (quotTraceDefect F I T s) ?_ ?_ ?_ ?_, fun ζ ζ' => rfl⟩
  · intro x x' y
    simp only [quotTraceDefect, (hl2 y).map_add, hl1.map_add, mul_add, add_mul, map_add]
    ring
  · intro c x y
    simp only [quotTraceDefect, (hl2 y).map_smul, hl1.map_smul, mul_smul_comm, smul_mul_assoc,
      map_smul, smul_eq_mul]
    ring
  · intro x y y'
    simp only [quotTraceDefect, (hl3 x).map_add, hl1.map_add, mul_add, map_add]
    ring
  · intro c x y
    simp only [quotTraceDefect, (hl3 x).map_smul, hl1.map_smul, mul_smul_comm, map_smul,
      smul_eq_mul]
    ring
private theorem realLogAbsDetSecondDeriv_eq
    (hRealLog : RealLogDet.Claim)
    (hCoord : TorusMatrixCoordinates.Claim)
    (hQuot : Quotients.QuotientTransposeNorm)
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} {ρ R : ℝ}
    (hMeet : IsLocalWith F I I T ρ R) {s : ℕ} (hs : 0 < s) (h4 : 4 * R < s)
    (hu : IsUnit (quotOperator F I T s 0)) {N : ℕ} (e : Fin N ≃ F.QuotMod s)
    (hReal : IsRealOnRealFields F I T) {W : Set (Coordinates.ComplexCoordinates N)} (hW : IsOpen W)
    (hW0 : 0 ∈ W)
    (hdist : ∀ z ∈ W, ‖normalizedDet F I T s (ofCoords e z) - 1‖ < 1)
    (hhol : Coordinates.ComplexCoordinates.LogDetSecondDeriv.IsHolomorphicScalarIn W
      (logDetInCoords F I T e)) :
    ∀ ζ ζ' : F.QuotMod s → ℂ,
      realLogAbsDetSecondDeriv F I T e ζ ζ' =
        logDetSecondDeriv F I T e ζ ζ' := by
  obtain ⟨-, -, -, -, hcoord⟩ := hCoord F I hF hI T ρ R hMeet s hs h4
  have hEntry := (hcoord N e).2.2 hReal
  have : Finite (I.QuotMod s) := (hQuot I I hI hI s hs).1.2.1
  have hev : ∀ᶠ v : Fin N → ℝ in 𝓝 0, ∀ j, |v j| < ρ := by
    refine eventually_all.2 fun j => ?_
    have hlim : Tendsto (fun v : Fin N → ℝ => |v j|) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_apply j).abs.tendsto (0 : Fin N → ℝ)
    exact hlim.eventually_lt_const hMeet.radius_pos
  obtain ⟨-, -, -, r4⟩ := hRealLog (I.QuotMod s) N W
    (fun z => quotOperator F I T s (ofCoords e z)) hW hW0 hu hdist hhol
    (hev.mono fun v hv c' c => hEntry v hv c' c)
  exact fun ζ ζ' => r4 _ _
private theorem toComplexVec_dualPoint_neg (s : ℕ) (m : Fin 4 → Fin s) :
    toComplexVec (dualPoint (-1) s m) = -toComplexVec (dualPoint 1 s m) := by
  funext μ
  simp [toComplexVec, dualPoint]
private theorem dualPoint_add_not_mem {s : ℕ} (hs : 0 < s) {m m' : Fin 4 → Fin s} (h : m ≠ m') :
    dualPoint 1 s m + dualPoint (-1) s m' ∉ InfiniteLattice.latticeSubgroup (2 * Real.pi) := by
  rintro ⟨n, hn⟩
  apply h
  funext μ
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hpi := Real.pi_ne_zero
  have h1 := hn μ
  simp only [Pi.add_apply, dualPoint] at h1
  have h2 : (((m μ : ℕ) : ℝ) - ((m' μ : ℕ) : ℝ)) = (n μ : ℝ) * s := by
    field_simp at h1
    nlinarith [h1]
  have h3 : (((m μ : ℕ) : ℤ) - ((m' μ : ℕ) : ℤ)) = n μ * s := by exact_mod_cast h2
  have h0 : n μ = 0 := by
    by_contra hne
    have hab : (s : ℤ) ≤ |n μ * s| := by
      rw [abs_mul, Nat.abs_cast]
      have : 1 ≤ |n μ| := Int.one_le_abs hne
      nlinarith
    rw [← h3] at hab
    have : |((m μ : ℕ) : ℤ) - ((m' μ : ℕ) : ℤ)| < s := by
      rw [abs_lt]
      constructor <;> omega
    omega
  rw [h0] at h3
  have : ((m μ : ℕ) : ℤ) = ((m' μ : ℕ) : ℤ) := by linarith
  exact Fin.ext (by exact_mod_cast this)
open Classical in
private theorem norm_le_at_indicators (hF : IsPeriodic F) (hW : BlochDecomposition.Facts F)
    {s : ℕ} (hs : 0 < s) (B : (F.QuotMod s → ℂ) →ₗ[ℂ] (F.QuotMod s → ℂ) →ₗ[ℂ] ℂ)
    (hV : VanishesOffAntipodal F s fun ζ ζ' => B ζ ζ') {M : ℝ}
    (hB : ∀ p ∈ dualLattice s, ∀ ε ε' : F.UnitQuot → ℂ,
      ‖B (descendField F s (blochWave F (toComplexVec p) ε))
          (descendField F s (blochWave F (-toComplexVec p) ε'))‖ ≤
        (s : ℝ) ^ 4 * (M * wNorm (F.quotWeight 1) ε * wNorm (F.quotWeight 1) ε'))
    (ι₀ ι₁ : F.Carrier) :
    ‖B (quotIndicator F s ι₀) (quotIndicator F s ι₁)‖ ≤
      M * wNorm (F.quotWeight 1) (Pi.single (F.mkQuot 1 ι₀) 1) *
        wNorm (F.quotWeight 1) (Pi.single (F.mkQuot 1 ι₁) 1) := by
  set ε : F.UnitQuot → ℂ := Pi.single (F.mkQuot 1 ι₀) 1 with hε
  set ε' : F.UnitQuot → ℂ := Pi.single (F.mkQuot 1 ι₁) 1 with hε'
  set X : (Fin 4 → Fin s) → F.QuotMod s → ℂ := fun m =>
    descendField F s (blochWave F (toComplexVec (dualPoint 1 s m)) ε) with hX
  set Y : (Fin 4 → Fin s) → F.QuotMod s → ℂ := fun m =>
    descendField F s (blochWave F (toComplexVec (dualPoint (-1) s m)) ε') with hY
  have e1 : quotIndicator F s ι₀ = ((s : ℂ) ^ 4)⁻¹ • ∑ m : Fin 4 → Fin s, phase 1 s m ι₀ • X m :=
    quotIndicator_eq_mean hF hW hs (σ := 1) (Or.inl rfl) ι₀
  have e2 : quotIndicator F s ι₁ = ((s : ℂ) ^ 4)⁻¹ • ∑ m : Fin 4 → Fin s, phase (-1) s m ι₁ • Y m :=
    quotIndicator_eq_mean hF hW hs (σ := -1) (Or.inr rfl) ι₁
  rw [e1, e2]
  simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
  have hdiag : ∀ m' : Fin 4 → Fin s, (∑ m : Fin 4 → Fin s, phase 1 s m ι₀ * B (X m) (Y m')) =
      phase 1 s m' ι₀ * B (X m') (Y m') := by
    intro m'
    refine Finset.sum_eq_single m' (fun m _ hne => ?_) (fun h => absurd (Finset.mem_univ m') h)
    have h0 : B (X m) (Y m') = 0 :=
      hV _ (dualPoint_mem 1 (Or.inl rfl) s m) _ (dualPoint_mem (-1) (Or.inr rfl) s m') ε ε'
        (dualPoint_add_not_mem hs hne)
    rw [h0, mul_zero]
  simp only [hdiag]
  have hnorm : ∀ (σ : ℝ) (m : Fin 4 → Fin s) (ι : F.Carrier), ‖phase σ s m ι‖ = 1 := by
    intro σ m ι
    rw [phase, show -(Complex.I * bilinDot (toComplexVec (dualPoint σ s m))
        (toComplexVec (F.pos ι))) = ((-(∑ μ, dualPoint σ s m μ * F.pos ι μ) : ℝ) : ℂ) *
          Complex.I by
      simp only [bilinDot, toComplexVec]
      push_cast
      ring]
    exact Complex.norm_exp_ofReal_mul_I _
  set A : ℝ := M * wNorm (F.quotWeight 1) ε * wNorm (F.quotWeight 1) ε' with hA
  have hterm : ∀ m ∈ (Finset.univ : Finset (Fin 4 → Fin s)),
      ‖phase (-1) s m ι₁ * (((s : ℂ) ^ 4)⁻¹ * (phase 1 s m ι₀ * B (X m) (Y m)))‖ ≤
        ((s : ℝ) ^ 4)⁻¹ * ((s : ℝ) ^ 4 * A) := by
    intro m _
    rw [norm_mul, norm_mul, norm_mul, hnorm, hnorm, one_mul, one_mul, norm_inv, norm_pow,
      Complex.norm_natCast]
    have := hB _ (dualPoint_mem 1 (Or.inl rfl) s m) ε ε'
    rw [← toComplexVec_dualPoint_neg] at this
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hsum := norm_sum_le_of_le _ hterm
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin,
    Finset.prod_const, nsmul_eq_mul] at hsum
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc ((s : ℝ) ^ 4)⁻¹ * ‖∑ m : Fin 4 → Fin s, phase (-1) s m ι₁ * (((s : ℂ) ^ 4)⁻¹ *
          (phase 1 s m ι₀ * B (X m) (Y m)))‖
      ≤ ((s : ℝ) ^ 4)⁻¹ * (((s ^ 4 : ℕ) : ℝ) * (((s : ℝ) ^ 4)⁻¹ * ((s : ℝ) ^ 4 * A))) :=
        mul_le_mul_of_nonneg_left (by simpa using hsum) (by positivity)
    _ = A := by
        push_cast
        field_simp
open Classical in
private theorem hasSum_smul_quotIndicator {f : F.Carrier → ℂ} (hf : Summable f) (s : ℕ) :
    HasSum (fun κ => f κ • quotIndicator F s κ) (periodize F s f) := by
  rw [Pi.hasSum]
  intro c
  have e : (fun κ => (f κ • quotIndicator F s κ) c) = Set.indicator {κ | F.mkQuot s κ = c} f := by
    funext κ
    by_cases h : F.mkQuot s κ = c
    · simp [quotIndicator, Set.indicator, h]
    · have h' : ¬ c = F.mkQuot s κ := fun e => h e.symm
      simp [quotIndicator, Set.indicator, h, h']
  have e2 : periodize F s f c = ∑' κ, Set.indicator {κ | F.mkQuot s κ = c} f κ :=
    tsum_subtype {κ | F.mkQuot s κ = c} f
  rw [e, e2]
  exact (hf.indicator _).hasSum
private theorem bilin_periodize (B : (F.QuotMod s → ℂ) →ₗ[ℂ] (F.QuotMod s → ℂ) →ₗ[ℂ] ℂ)
    [Finite (F.QuotMod s)] {f g : F.Carrier → ℂ} (hf : Summable f) (hg : Summable g)
    (hsum : Summable fun x : F.Carrier × F.Carrier =>
      f x.1 * g x.2 * B (quotIndicator F s x.1) (quotIndicator F s x.2)) :
    B (periodize F s f) (periodize F s g) =
      ∑' x : F.Carrier × F.Carrier, f x.1 * g x.2 * B (quotIndicator F s x.1) (quotIndicator F s x.2) := by
  have h1 : ∀ ζ', HasSum (fun κ => f κ * B (quotIndicator F s κ) ζ')
      (B (periodize F s f) ζ') := by
    intro ζ'
    have hc : Continuous (B.flip ζ') := LinearMap.continuous_of_finiteDimensional _
    have := (hasSum_smul_quotIndicator hf s).map (B.flip ζ') hc
    simpa [Function.comp_def] using this
  have h2 : ∀ κ, HasSum (fun κ' => g κ' * B (quotIndicator F s κ) (quotIndicator F s κ'))
      (B (quotIndicator F s κ) (periodize F s g)) := by
    intro κ
    have hc : Continuous (B (quotIndicator F s κ)) := LinearMap.continuous_of_finiteDimensional _
    have := (hasSum_smul_quotIndicator hg s).map (B (quotIndicator F s κ)) hc
    simpa [Function.comp_def] using this
  rw [hsum.tsum_prod, ← (h1 _).tsum_eq]
  refine tsum_congr fun κ => ?_
  rw [← (h2 κ).tsum_eq, ← tsum_mul_left]
  exact tsum_congr fun κ' => by ring
private theorem l1NormVec_le_two_mul_euclid (v : AmbientSpace) :
    TorusMetric.l1NormVec v ≤ 2 * TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.sum_abs_le_two_mul_euclidNormVec <;> assumption
theorem secondDerivConvergence_holds (hLogdet : PeriodicOperators.LogDetSecondDerivs.Claim)
    (hBd : StripBound.Claim)
    (hRealLog : RealLogDet.Claim)
    (hCoord : TorusMatrixCoordinates.Claim)
    (hQuot : Quotients.QuotientTransposeNorm)
    (hKern : OpFunKernels.Claim)
    (hDecay : ExpDecaySymbol.HolomorphicOnStrip)
    (hStrip : OpenStripInverse.Claim)
    (hBy : LogDetTraces.Claim)
    (hConv : QuotTraceLimits.UnitFieldTracesConverge)
    (hWave : BlochDecomposition.Claim) : SecondDerivConvergence := by
  classical
  intro F I hF hI T hT hSym hReal f g hf hg
  obtain ⟨ρ, R, hMeet⟩ := id hT
  obtain ⟨δ, hδ, hinv, ⟨s₁, C₁, c₁, -, -, h1⟩, ⟨O, hO, hsub, a, hol, hform⟩, hrp⟩ :=
    hLogdet F I hF hI T hT hSym
  obtain ⟨s₂, C, c, hC, hc, h2⟩ := hrp hReal
  have : Finite F.UnitQuot := hF.finite_quot
  have := Fintype.ofFinite F.UnitQuot
  have hw : StripBound.IsAdmissibleWidth F I T δ := by
    refine ⟨hinv, fun p hp => ?_, fun d d' => ⟨O, hO, hsub, a d d', hol d d', fun p hp => ?_⟩⟩
    · refine ⟨LinearMap.mk₂ ℂ (fun x y => ∑ d, ∑ d', a d d' p * x d * y d') ?_ ?_ ?_ ?_,
        fun εPlus εMinus => ?_⟩
      · intro x x' y
        simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
      · intro w x y
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      · intro x y y'
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      · intro w x y
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      · show JetQuad.logNumber p (jetAlong F I I T p εPlus εMinus) = _
        rw [hform p hp]
        simp [tsum_fintype]
    · show a d d' p = JetQuad.logNumber p (jetAlong F I I T p _ _)
      rw [hform p hp]
      simp only [tsum_fintype, Pi.single_apply]
      simp
  obtain ⟨-, -, ⟨M₀, hM₀⟩, -⟩ := hBd F I hF hI T hT hSym δ hδ hw
  have hK := (hKern F I I hF hI hI T hT).1
  have hj0 := hinv 0 (fun μ => by simpa using hδ.le) 0 0
  obtain ⟨-, C₀, hC₀, hb⟩ := hK.decays (4 * δ) (by positivity)
  have hL1 : ∀ ι' ι, ‖coeffZero F I I T ι' ι‖ ≤ C₀ * Real.exp (-(2 * δ) *
      TorusMetric.l1NormVec (I.pos ι' - I.pos ι)) := by
    intro ι' ι
    refine (hb ι' ι).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₀.le)
    have := l1NormVec_le_two_mul_euclid (I.pos ι' - I.pos ι)
    nlinarith
  obtain ⟨hForm, hHol⟩ := hDecay I I hI hI (2 * δ) (by positivity) C₀ _ hK.periodic hL1
  have hInvOn : ∀ κ ∈ openImStrip (2 * δ),
      IsInvertibleQuotHom (symbolHom I I (coeffZero F I I T) κ) := by
    intro κ hκ g'
    have hu := hj0.isUnit_f00 κ fun μ => (hκ μ).le
    have hbij := (Module.End.isUnit_iff _).1 hu
    exact hbij.existsUnique g'
  obtain ⟨-, hRper, -, -, hRT, hTR, -, -⟩ :=
    hStrip I hI (2 * δ) (by positivity) _ hK.periodic hForm hHol hInvOn
  obtain ⟨-, hlim⟩ := hConv F I hF hI T ρ R hMeet _ hRper hTR hRT
  have hW := hWave F hF
  obtain ⟨w, hw0, hwle⟩ : ∃ w : ℝ, 0 ≤ w ∧ ∀ d : F.UnitQuot,
      wNorm (F.quotWeight 1) (Pi.single d 1) ≤ w := by
    refine ⟨∑ d, wNorm (F.quotWeight 1) (Pi.single d 1),
      Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _, fun d => ?_⟩
    exact Finset.single_le_sum (f := fun d : F.UnitQuot =>
      wNorm (F.quotWeight 1) (Pi.single d 1)) (fun _ _ => Real.sqrt_nonneg _)
      (Finset.mem_univ d)
  set M : ℝ := |M₀| + C with hM
  have hM0 : 0 ≤ M := by positivity
  obtain ⟨s₄, hs₄⟩ := exists_nat_gt (4 * R)
  set s₃ : ℕ := max (max s₁ s₂) (max s₄ 1) with hs₃
  have hsizes : ∀ s, s₃ ≤ s → s₁ ≤ s ∧ s₂ ≤ s ∧ 4 * R < s ∧ 0 < s := by
    intro s hs
    have a1 : s₁ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
    have a2 : s₂ ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
    have a3 : s₄ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
    have a4 : 1 ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
    exact ⟨a1, a2, lt_of_lt_of_le hs₄ (by exact_mod_cast a3), a4⟩
  have key : ∀ s, s₃ ≤ s → ∃ B : (F.QuotMod s → ℂ) →ₗ[ℂ] (F.QuotMod s → ℂ) →ₗ[ℂ] ℂ,
      (∀ ζ ζ', B ζ ζ' = quotTraceDefect F I T s ζ ζ') ∧
      (∀ (N : ℕ) (e : Fin N ≃ F.QuotMod s) ζ ζ',
        realLogAbsDetSecondDeriv F I T e ζ ζ' = B ζ ζ') ∧
      ∀ ι₀ ι₁, ‖B (quotIndicator F s ι₀) (quotIndicator F s ι₁)‖ ≤ M * w * w := by
    intro s hs
    obtain ⟨a1, a2, a3, a4⟩ := hsizes s hs
    obtain ⟨B, hBτ⟩ := exists_bilin_quotTraceDefect hCoord hF hI hMeet a4 a3
    obtain ⟨hu, hall⟩ := h1 s a1
    have heq : ∀ (N : ℕ) (e : Fin N ≃ F.QuotMod s) ζ ζ',
        realLogAbsDetSecondDeriv F I T e ζ ζ' = B ζ ζ' := by
      intro N e ζ ζ'
      obtain ⟨⟨W, hWo, hW0, hdist, hhol⟩, -, -⟩ := hall N e
      rw [realLogAbsDetSecondDeriv_eq hRealLog hCoord hQuot hF hI hMeet a4 a3 hu e hReal hWo hW0
        hdist hhol, hBy F I hF hI T ρ R hMeet s a4 a3 hu N e, hBτ]
    refine ⟨B, hBτ, heq, ?_⟩
    have : Finite (F.QuotMod s) := (hQuot F F hF hF s a4).1.2.1
    obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (F.QuotMod s)
    obtain ⟨-, -, hv, hclose⟩ := h2 s a2 N e.symm
    have hD : realLogAbsDetSecondDeriv F I T e.symm = fun ζ ζ' => B ζ ζ' := by
      funext ζ ζ'
      exact heq N e.symm ζ ζ'
    rw [hD] at hv hclose
    have hs0 : (0 : ℝ) < s := by exact_mod_cast a4
    intro ι₀ ι₁
    have hb := norm_le_at_indicators hF hW a4 B hv (M := M) ?_ ι₀ ι₁
    · refine hb.trans ?_
      have n1 := hwle (F.mkQuot 1 ι₀)
      have n2 := hwle (F.mkQuot 1 ι₁)
      have p1 : 0 ≤ wNorm (F.quotWeight 1) (Pi.single (F.mkQuot 1 ι₀) (1 : ℂ)) :=
        Real.sqrt_nonneg _
      have p2 : 0 ≤ wNorm (F.quotWeight 1) (Pi.single (F.mkQuot 1 ι₁) (1 : ℂ)) :=
        Real.sqrt_nonneg _
      exact mul_le_mul (mul_le_mul_of_nonneg_left n1 hM0) n2 p2 (by positivity)
    · intro p hp ε ε'
      have hpS : toComplexVec p ∈ imStrip δ := fun μ => by simpa [toComplexVec] using hδ.le
      have hcl := hclose p hp ε ε'
      have hℓ := hM₀ _ hpS ε ε'
      set D := B (descendField F s (blochWave F (toComplexVec p) ε))
        (descendField F s (blochWave F (-toComplexVec p) ε')) with hDdef
      set n₁ := wNorm (F.quotWeight 1) ε with hn₁
      set n₂ := wNorm (F.quotWeight 1) ε' with hn₂
      have q1 : 0 ≤ n₁ := Real.sqrt_nonneg _
      have q2 : 0 ≤ n₂ := Real.sqrt_nonneg _
      have hexp : Real.exp (-c * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have hnn : 0 ≤ n₁ * n₂ := mul_nonneg q1 q2
      have b1 : ‖((s : ℂ) ^ 4)⁻¹ * D‖ ≤ M * n₁ * n₂ := by
        have t1 : ‖((s : ℂ) ^ 4)⁻¹ * D‖ ≤ ‖((s : ℂ) ^ 4)⁻¹ * D -
            JetQuad.logNumber (toComplexVec p)
              (jetAlong F I I T (toComplexVec p) ε ε')‖ +
            ‖JetQuad.logNumber (toComplexVec p)
              (jetAlong F I I T (toComplexVec p) ε ε')‖ := norm_le_norm_sub_add _ _
        have t2 : C * Real.exp (-c * s) * n₁ * n₂ ≤ C * n₁ * n₂ := by
          have := mul_le_mul_of_nonneg_left hexp hC.le
          nlinarith
        have t3 : ‖JetQuad.logNumber (toComplexVec p)
              (jetAlong F I I T (toComplexVec p) ε ε')‖ ≤ |M₀| * n₁ * n₂ := by
          refine (show _ ≤ M₀ * n₁ * n₂ from hℓ).trans ?_
          have := le_abs_self M₀
          nlinarith
        calc _ ≤ _ := t1
          _ ≤ C * n₁ * n₂ + |M₀| * n₁ * n₂ := add_le_add (hcl.trans t2) t3
          _ = M * n₁ * n₂ := by rw [hM]; ring
      have hsC : ((s : ℂ) ^ 4) ≠ 0 := pow_ne_zero _ (by exact_mod_cast a4.ne')
      have b2 : ‖D‖ = (s : ℝ) ^ 4 * ‖((s : ℂ) ^ 4)⁻¹ * D‖ := by
        rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
        field_simp
      rw [b2]
      exact mul_le_mul_of_nonneg_left b1 (by positivity)
  set bound : F.Carrier × F.Carrier → ℝ := fun x => ‖f x.1‖ * ‖g x.2‖ * (M * w * w) with hbound
  have hbs : Summable bound :=
    (Summable.mul_of_nonneg hf.norm hg.norm (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _)).mul_right _
  set G : ℕ → F.Carrier × F.Carrier → ℂ := fun s x => f x.1 * g x.2 *
    quotTraceDefect F I T s (quotIndicator F s x.1) (quotIndicator F s x.2) with hG
  have hGb : ∀ s, s₃ ≤ s → ∀ x, ‖G s x‖ ≤ bound x := by
    intro s hs x
    obtain ⟨B, hB1, -, hB3⟩ := key s hs
    rw [hG, hbound]
    simp only [norm_mul, ← hB1]
    exact mul_le_mul_of_nonneg_left (hB3 _ _) (by positivity)
  have hTend := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) hbs
    (f := G) (g := fun x => f x.1 * g x.2 * kernelTraceDefect F I T
      (periodicInverse I (coeffZero F I I T)) (siteIndicator F x.1) (siteIndicator F x.2))
    (fun x => (hlim x.1 x.2).const_mul _)
    (eventually_atTop.2 ⟨s₃, hGb⟩)
  obtain ⟨l, hl⟩ : ∃ l, Tendsto (fun s => ∑' x, G s x) atTop (𝓝 l) := ⟨_, hTend⟩
  refine ⟨l, fun ε hε => ?_⟩
  obtain ⟨s₅, hs₅⟩ := Metric.tendsto_atTop.1 hl ε hε
  refine ⟨max s₃ s₅, fun s hs N e => ?_⟩
  have a1 : s₃ ≤ s := le_trans (le_max_left _ _) hs
  have a2 : s₅ ≤ s := le_trans (le_max_right _ _) hs
  obtain ⟨B, hB1, hB2, -⟩ := key s a1
  have : Finite (F.QuotMod s) := (hQuot F F hF hF s (hsizes s a1).2.2.2).1.2.1
  rw [hB2, bilin_periodize B hf hg ?_, ← dist_eq_norm]
  · have e : (fun x : F.Carrier × F.Carrier =>
        f x.1 * g x.2 * B (quotIndicator F s x.1) (quotIndicator F s x.2)) = G s := by
      funext x
      simp only [hG, hB1]
    rw [e]
    exact hs₅ s a2
  · have e : (fun x : F.Carrier × F.Carrier =>
        f x.1 * g x.2 * B (quotIndicator F s x.1) (quotIndicator F s x.2)) = G s := by
      funext x
      simp only [hG, hB1]
    rw [e]
    exact Summable.of_norm_bounded hbs (hGb s a1)
end YangMills.Construction.RunningCouplingSlope.SummableFields
end
