import YangMills.Construction.PeriodicOperators.KernelsOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.TracesOfTheCoefficientsOnPlaneWavesProof
import YangMills.Construction.Towers.SymbolsOfTheAveragesOnPlaneWavesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.OpFunKernels
open TorusMetric (euclidNormVec)
theorem symbolHom_apply_eq {I I' : PeriodicData} (hI : IsPeriodic I)
    (Z : I'.Carrier → I.Carrier → ℂ) (k : Fin 4 → ℂ) (f : I.UnitQuot → ℂ) :
    symbolHom I I' Z k f = applyKernel (quotSymbol I I' Z k) f := by apply _root_.YangMills.Construction.Tower.PlaneWaveSmoothingSymbols.symbolHom_eq_applyKernel <;> assumption
theorem blochWave_injective (I : PeriodicData) (k : Fin 4 → ℂ) {f g : I.UnitQuot → ℂ}
    (h : ∀ i, blochWave I k f i = blochWave I k g i) : f = g := by
  funext c
  obtain ⟨i, rfl⟩ := Quot.exists_rep (show I.QuotMod 1 from c)
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) (h i)
theorem euclidNormVec_sub_comm (a b : InfiniteLattice.AmbientSpace) :
    euclidNormVec (a - b) = euclidNormVec (b - a) := by apply _root_.YangMills.SharedProofs.p26380 <;> assumption
theorem bilinDot_zero_left (y : Fin 4 → ℂ) : bilinDot 0 y = 0 := by
  simp [bilinDot]
theorem bilinDot_neg_left (p y : Fin 4 → ℂ) : bilinDot (-p) y = -bilinDot p y := by
  simp [bilinDot, Finset.sum_neg_distrib]
theorem shiftField_blochWave {F : PeriodicData} (hF : IsPeriodic F) (p : Fin 4 → ℂ)
    (e : F.UnitQuot → ℂ) (n : Fin 4 → ℤ) :
    shiftField F n (blochWave F p e) =
      Complex.exp (-(Complex.I * bilinDot p (toComplexVec (castVec n)))) • blochWave F p e := by apply _root_.YangMills.Construction.PeriodicOperators.PlaneWaveTraces.shiftField_blochWave <;> assumption
section Coeffs
variable {F I I' : PeriodicData} {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ R : ℝ}
theorem coeffOne_smul (H : LocalOpFunTaylor.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hT : IsLocalWith F I I' T ρ R) (c : ℂ) (u : F.Carrier → ℂ) (i' : I'.Carrier)
    (i : I.Carrier) :
    coeffOne F I I' T (c • u) i' i = c * coeffOne F I I' T u i' i := by
  obtain ⟨⟨hfin, -, hone, -, -⟩, -⟩ := H F I I' hF hI hI' T ρ R hT u u i' i 0
  have := hfin.to_subtype
  cases nonempty_fintype (nearIndices F (I'.pos i') R)
  rw [hone (c • u), hone u]
  simp only [finsum_eq_sum_of_fintype, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun x _ => by ring
theorem coeffTwo_smul_smul (H : LocalOpFunTaylor.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hT : IsLocalWith F I I' T ρ R) (c d : ℂ) (u v : F.Carrier → ℂ) (i' : I'.Carrier)
    (i : I.Carrier) :
    coeffTwo F I I' T (c • u) (d • v) i' i =
      c * d * coeffTwo F I I' T u v i' i := by
  obtain ⟨⟨hfin, -, -, -, htwo⟩, -⟩ := H F I I' hF hI hI' T ρ R hT u v i' i 0
  have := hfin.to_subtype
  cases nonempty_fintype (nearIndices F (I'.pos i') R)
  rw [htwo.2 (c • u) (d • v), htwo.2 u v]
  simp only [finsum_eq_sum_of_fintype, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring
theorem coeffOne_blochWave_phaseCovariant (H : LocalOpFunTaylor.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hT : IsLocalWith F I I' T ρ R) (q : Fin 4 → ℂ) (e : F.UnitQuot → ℂ) :
    IsPhaseCovariant I I' q (coeffOne F I I' T (blochWave F q e)) := by
  intro n i' i
  obtain ⟨-, -, ⟨-, -, -, h, -⟩, -⟩ := H F I I' hF hI hI' T ρ R hT (blochWave F q e) 0 i' i n
  rw [shiftField_blochWave hF, coeffOne_smul H hF hI hI' hT] at h
  rw [← h, ← mul_assoc, ← Complex.exp_add]
  simp
theorem coeffTwo_blochWave_phaseCovariant (H : LocalOpFunTaylor.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hT : IsLocalWith F I I' T ρ R) (p : Fin 4 → ℂ) (ePlus eMinus : F.UnitQuot → ℂ) :
    IsPhaseCovariant I I' 0
      (coeffTwo F I I' T (blochWave F p ePlus) (blochWave F (-p) eMinus)) := by
  intro n i' i
  obtain ⟨-, -, ⟨-, -, -, -, h⟩, -⟩ :=
    H F I I' hF hI hI' T ρ R hT (blochWave F p ePlus) (blochWave F (-p) eMinus) i' i n
  rw [shiftField_blochWave hF, shiftField_blochWave hF, coeffTwo_smul_smul H hF hI hI' hT] at h
  rw [← Complex.exp_add, bilinDot_neg_left] at h
  simp only [mul_neg, neg_neg, neg_add_cancel, Complex.exp_zero, one_mul] at h
  rw [h, bilinDot_zero_left]
  simp
theorem coeffZero_phaseCovariant (H : LocalOpFunTaylor.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hT : IsLocalWith F I I' T ρ R) :
    IsPhaseCovariant I I' 0 (coeffZero F I I' T) := by
  intro n i' i
  obtain ⟨-, -, ⟨h, -⟩, -⟩ := H F I I' hF hI hI' T ρ R hT 0 0 i' i n
  rw [h, bilinDot_zero_left]
  simp
theorem coeffs_vanishOutsideRadius (H : LocalOpFunTaylor.Claim)
    (hF : IsPeriodic F) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hT : IsLocalWith F I I' T ρ R) (u v : F.Carrier → ℂ) :
    VanishesOutsideRadius I I' R (coeffZero F I I' T) ∧
      VanishesOutsideRadius I I' R (coeffOne F I I' T u) ∧
      VanishesOutsideRadius I I' R (coeffTwo F I I' T u v) := by
  have key : ∀ (i' : I'.Carrier) (i : I.Carrier),
      ¬ euclidNormVec (I'.pos i' - I.pos i) ≤ R →
        coeffZero F I I' T i' i = 0 ∧ coeffOne F I I' T u i' i = 0 ∧
          coeffTwo F I I' T u v i' i = 0 := by
    intro i' i hd
    obtain ⟨-, ⟨-, h⟩, -⟩ := H F I I' hF hI hI' T ρ R hT u v i' i 0
    exact h (by rwa [euclidNormVec_sub_comm])
  exact ⟨fun i' i hd => (key i' i hd).1, fun i' i hd => (key i' i hd).2.1,
    fun i' i hd => (key i' i hd).2.2⟩
end Coeffs
theorem dephasedKernel_zero (I I' : PeriodicData) (Y : I'.Carrier → I.Carrier → ℂ) :
    dephasedKernel I I' 0 Y = Y := by apply _root_.YangMills.Construction.PeriodicOperators.PlaneWaveTraces.dephasedKernel_zero <;> assumption
theorem claim_holds (hC : CovariantFiniteRange.Claim)
    (H : LocalOpFunTaylor.Claim) : Claim := by
  rintro F I I' hF hI hI' T ⟨ρ, R, hT⟩
  have hcov := hC.2 I I' hI hI'
  refine ⟨?_, fun p ePlus eMinus => ?_⟩
  · have h := (hcov 0 R _ (coeffZero_phaseCovariant H hF hI hI' hT)
      (coeffs_vanishOutsideRadius H hF hI hI' hT 0 0).1).1
    rwa [dephasedKernel_zero] at h
  · have hY₁ := coeffOne_blochWave_phaseCovariant H hF hI hI' hT p ePlus
    have hY₂ := coeffOne_blochWave_phaseCovariant H hF hI hI' hT (-p) eMinus
    have hY₃ := coeffTwo_blochWave_phaseCovariant H hF hI hI' hT p ePlus eMinus
    have hv₁ := (coeffs_vanishOutsideRadius H hF hI hI' hT (blochWave F p ePlus) 0).2.1
    have hv₂ := (coeffs_vanishOutsideRadius H hF hI hI' hT (blochWave F (-p) eMinus) 0).2.1
    have hv₃ := (coeffs_vanishOutsideRadius H hF hI hI' hT (blochWave F p ePlus)
      (blochWave F (-p) eMinus)).2.2
    obtain ⟨ho₁, -, -, ha₁⟩ := hcov p R _ hY₁ hv₁
    obtain ⟨ho₂, -, -, ha₂⟩ := hcov (-p) R _ hY₂ hv₂
    obtain ⟨ho₃, -, -, ha₃⟩ := hcov 0 R _ hY₃ hv₃
    let A : ((Fin 4 → ℂ) → QuotHom I I') × ((Fin 4 → ℂ) → QuotHom I I') ×
        ((Fin 4 → ℂ) → QuotHom I I') :=
      (symbolHom I I' (dephasedKernel I I' p
          (coeffOne F I I' T (blochWave F p ePlus))),
        symbolHom I I' (dephasedKernel I I' (-p)
          (coeffOne F I I' T (blochWave F (-p) eMinus))),
        symbolHom I I' (dephasedKernel I I' 0
          (coeffTwo F I I' T (blochWave F p ePlus) (blochWave F (-p) eMinus))))
    have hA : IsActionTriple F I I' T p ePlus eMinus A := by
      intro k f i'
      refine ⟨?_, ?_, ?_⟩
      · simp only [A]
        rw [symbolHom_apply_eq hI]
        exact (ha₁ k f i').2
      · simp only [A]
        rw [symbolHom_apply_eq hI, sub_eq_add_neg]
        exact (ha₂ k f i').2
      · simp only [A]
        rw [symbolHom_apply_eq hI]
        simpa using (ha₃ k f i').2
    have huniq : ∀ B, IsActionTriple F I I' T p ePlus eMinus B → B = A := by
      rintro ⟨B₁, B₂, B₃⟩ hB
      have e₁ : B₁ = A.1 := by
        funext k
        refine LinearMap.ext fun f => blochWave_injective I' (k + p) fun i' => ?_
        exact (hB k f i').1.symm.trans (hA k f i').1
      have e₂ : B₂ = A.2.1 := by
        funext k
        refine LinearMap.ext fun f => blochWave_injective I' (k - p) fun i' => ?_
        exact (hB k f i').2.1.symm.trans (hA k f i').2.1
      have e₃ : B₃ = A.2.2 := by
        funext k
        refine LinearMap.ext fun f => blochWave_injective I' k fun i' => ?_
        exact (hB k f i').2.2.symm.trans (hA k f i').2.2
      rw [e₁, e₂, e₃]
    have hspec : Classical.epsilon (IsActionTriple F I I' T p ePlus eMinus) = A :=
      huniq _ (Classical.epsilon_spec ⟨A, hA⟩)
    refine ⟨⟨A, hA, huniq⟩, ⟨hY₁, ho₁, ?_⟩, ⟨hY₂, ho₂, ?_⟩, ⟨hY₃, ho₃, ?_⟩⟩
    · show (Classical.epsilon (IsActionTriple F I I' T p ePlus eMinus)).1 = _
      rw [hspec]
    · show (Classical.epsilon (IsActionTriple F I I' T p ePlus eMinus)).2.1 = _
      rw [hspec]
    · show (Classical.epsilon (IsActionTriple F I I' T p ePlus eMinus)).2.2 = _
      rw [hspec]
end YangMills.Construction.PeriodicOperators.OpFunKernels
end
