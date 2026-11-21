import YangMills.Construction.PeriodicOperators.CyclicityAndTransposeOfTheTraceNumberProof
import YangMills.Construction.RunningCouplingSlope.PlainMapsAtOneOnTheWhole
import YangMills.Construction.RunningCouplingSlope.TheFlatPlainStepIsLocal
import YangMills.Construction.RunningCouplingSlope.TheNoiseAtOneOnTheWholeIsPositive
import YangMills.Construction.Towers.FormsOfTheFreeOperatorsInCoefficientsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace FullLattice.IdentityNoise
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
section InnerProducts
variable {J : Type} (w : J → ℝ)
private theorem wInner_eq_sum [Fintype J] (f g : J → ℂ) :
    PeriodicOperators.wInner w f g = ∑ i, (w i : ℂ) * (conj (f i) * g i) := by
  simp only [PeriodicOperators.wInner, PeriodicOperators.wPairing, tsum_fintype]
private theorem wInner_add_right [Finite J] (f g g' : J → ℂ) :
    PeriodicOperators.wInner w f (g + g') = PeriodicOperators.wInner w f g + PeriodicOperators.wInner w f g' := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.wInner_add_right <;> assumption
private theorem wInner_smul_right [Finite J] (c : ℂ) (f g : J → ℂ) :
    PeriodicOperators.wInner w f (c • g) = c * PeriodicOperators.wInner w f g := by
  have := Fintype.ofFinite J
  simp only [wInner_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
private theorem wInner_zero_right [Finite J] (f : J → ℂ) : PeriodicOperators.wInner w f 0 = 0 := by
  have := Fintype.ofFinite J
  simp [wInner_eq_sum]
private theorem wInner_self_re_nonneg [Finite J] (hw : ∀ i, 0 < w i) (f : J → ℂ) :
    0 ≤ (PeriodicOperators.wInner w f f).re := by
  have := Fintype.ofFinite J
  rw [wInner_eq_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have := hw i
  positivity
end InnerProducts
private theorem quotWeight_pos {P : PeriodicData} (hP : PeriodicOperators.IsPeriodic P) (c : P.UnitQuot) :
    0 < P.quotWeight 1 c := by apply _root_.YangMills.SharedProofs.p9241 <;> assumption
section RealPoints
variable {ξ : Fin 4 → ℂ}
private theorem toComplexVec_re (hξ : ξ ∈ realDualPoints) : toComplexVec (fun μ => (ξ μ).re) = ξ := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.toComplexVec_re <;> assumption
private theorem mem_strictImStrip_of_real (hξ : ξ ∈ realDualPoints) {δ : ℝ} (hδ : 0 < δ) :
    ξ ∈ strictImStrip δ := by apply _root_.YangMills.Construction.Tower.FreeCoercivity.mem_imStrip_of_real <;> assumption
private theorem wInner_symbolHom_transpose {P P' P'' : PeriodicData} (hP : PeriodicOperators.IsPeriodic P)
    (hP' : PeriodicOperators.IsPeriodic P') {T : P'.Carrier → P.Carrier → ℂ} {S : P.Carrier → P''.Carrier → ℂ}
    (props : SymbolProperties P P' P'' T S 1) (hreal : ∀ y x, (T y x).im = 0)
    (hξ : ξ ∈ realDualPoints) (f : P.UnitQuot → ℂ) (g : P'.UnitQuot → ℂ) :
    PeriodicOperators.wInner (P'.quotWeight 1) g (symbolHom P P' T ξ f) =
      PeriodicOperators.wInner (P.quotWeight 1) (symbolHom P' P (kernelTranspose P P' T) ξ g) f := by
  have := hP.finite_quot
  have := hP'.finite_quot
  have e₁ : symbolHom P P' T ξ f = applyKernel (quotSymbol P P' T ξ) f :=
    linearMapOfEntries_eq_applyKernel _ _
  have e₂ : symbolHom P' P (kernelTranspose P P' T) ξ g =
      applyKernel (quotSymbol P' P (kernelTranspose P P' T) ξ) g :=
    linearMapOfEntries_eq_applyKernel _ _
  rw [e₁, e₂, (props.quotSymbol_kernelTranspose ξ (mem_strictImStrip_of_real hξ one_pos)).2]
  have h := props.wInner_quotTranspose hreal (fun μ => (ξ μ).re) f g
  rw [toComplexVec_re hξ] at h
  exact h.symm
end RealPoints
section SymbolCalculus
variable (hStrip : StripSymbols.Claim)
include hStrip
private theorem comp_at {P P' P'' : PeriodicData} (hP : PeriodicOperators.IsPeriodic P)
    (hP' : PeriodicOperators.IsPeriodic P') (hP'' : PeriodicOperators.IsPeriodic P'')
    {T : P'.Carrier → P.Carrier → ℂ} {S : P.Carrier → P''.Carrier → ℂ}
    (hT : IsPeriodicKernel P P' T) (hS : IsPeriodicKernel P'' P S) {ξ : Fin 4 → ℂ}
    (sT : SymbolSummableAt P P' T ξ) (sS : SymbolSummableAt P'' P S ξ) :
    IsPeriodicKernel P'' P' (compKernel T S) ∧
      SymbolSummableAt P'' P' (compKernel T S) ξ ∧
      symbolHom P'' P' (compKernel T S) ξ = (symbolHom P P' T ξ).comp (symbolHom P'' P S ξ) :=
  (((hStrip.2.1 P P' hP hP').2.1 T ξ hT sT).comp P'' hP'' S hS sS).2
private theorem linComb_at {P P' : PeriodicData} (hP : PeriodicOperators.IsPeriodic P)
    (hP' : PeriodicOperators.IsPeriodic P') {T T' : P'.Carrier → P.Carrier → ℂ}
    (hT : IsPeriodicKernel P P' T) (hT' : IsPeriodicKernel P P' T') {ξ : Fin 4 → ℂ}
    (sT : SymbolSummableAt P P' T ξ) (sT' : SymbolSummableAt P P' T' ξ) (c c' : ℂ) :
    IsPeriodicKernel P P' (StripSymbols.linCombKernel c c' T T') ∧
      SymbolSummableAt P P' (StripSymbols.linCombKernel c c' T T') ξ ∧
      symbolHom P P' (StripSymbols.linCombKernel c c' T T') ξ =
        c • symbolHom P P' T ξ + c' • symbolHom P P' T' ξ :=
  ((hStrip.2.1 P P' hP hP').2.1 T ξ hT sT).linComb T' hT' sT' c c'
private theorem summable_at {P P' : PeriodicData} (hP : PeriodicOperators.IsPeriodic P)
    (hP' : PeriodicOperators.IsPeriodic P') {T : P'.Carrier → P.Carrier → ℂ}
    (hT : Tower.FreeOperators.HasFiniteRangeEveryRate P P' T)
    (ξ : Fin 4 → ℂ) : SymbolSummableAt P P' T ξ :=
  (hStrip.2.1 _ _ hP hP').1.finiteRange _ hT.1 hT.2.1 ξ (mem_univ ξ)
end SymbolCalculus
private theorem symbolHom_idKernel (hCov : CovariantFiniteRange.Claim) {P : PeriodicData}
    (hP : PeriodicOperators.IsPeriodic P) (ξ : Fin 4 → ℂ) (f : P.UnitQuot → ℂ) :
    symbolHom P P (idKernel P) ξ f = f := by
  classical
  have := hP.finite_quot
  have e : symbolHom P P (idKernel P) ξ f = applyKernel (quotSymbol P P (idKernel P) ξ) f :=
    linearMapOfEntries_eq_applyKernel _ _
  rw [e, (hCov.1 P hP).2.2.2 ξ]
  funext c
  show ∑' d, quotOne P c d * f d = f c
  rw [tsum_eq_single c]
  · simp [quotOne]
  · intro d hd
    simp [quotOne, Ne.symm hd]
section Levels
variable {a : ℝ} {L k : ℕ}
private theorem invRadiusDiag_trivial (hMean : MeanMapsAtTrivialField)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {i : ℕ} (hi : i < k) :
    invRadiusDiag (L := L) (k := k) (fun _ => 1) i =
      idKernel (colourEdges L k (i + 1)) := by
  funext y x
  have h := (hMean L hL k hk).2.1 i hi x.2.1 x.2.2
  have hr := (hMean L hL k hk).1 i hi.le
  unfold invRadiusDiag idKernel
  by_cases e : y = x
  · refine (if_pos e).trans (Eq.trans ?_ (if_pos e).symm)
    rw [hr, h, inv_one]
  · exact (if_neg e).trans (if_neg e).symm
private theorem noiseCovariance_conditions (ha : 0 < a) (hLoc : MeanStepAtTrivialFieldFiniteRange)
    (hMean : MeanMapsAtTrivialField) (hCov : CovariantFiniteRange.Claim)
    (hIdx : TowerIndexSets.Claim) (hSym : Symbols.Claim)
    (hStrip : StripSymbols.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) :
    ∀ i : ℕ, i ≤ k →
    IsPeriodicKernel (colourEdges L k i) (colourEdges L k i)
      (noiseCovariance a L k (fun _ => 1) i) ∧
    ∀ ξ ∈ realDualPoints,
      SymbolSummableAt (colourEdges L k i) (colourEdges L k i)
        (noiseCovariance a L k (fun _ => 1) i) ξ ∧
      ∀ v : (colourEdges L k i).UnitQuot → ℂ,
        0 ≤ (PeriodicOperators.wInner ((colourEdges L k i).quotWeight 1) v
          (symbolHom (colourEdges L k i) (colourEdges L k i)
            (noiseCovariance a L k (fun _ => 1) i) ξ v)).re ∧
        (1 ≤ i → a⁻¹ * (PeriodicOperators.wInner ((colourEdges L k i).quotWeight 1) v v).re ≤
          (PeriodicOperators.wInner ((colourEdges L k i).quotWeight 1) v
            (symbolHom (colourEdges L k i) (colourEdges L k i)
              (noiseCovariance a L k (fun _ => 1) i) ξ v)).re)
  | 0, _ => by
    have hP := (hIdx L hL k 0 (Nat.zero_le k)).2.1
    have := hP.finite_quot
    obtain ⟨-, hid, -, -⟩ := hCov.1 _ hP
    have e : StripSymbols.linCombKernel 0 0 (idKernel (colourEdges L k 0))
        (idKernel (colourEdges L k 0)) = noiseCovariance a L k (fun _ => 1) 0 := by
      funext y x
      show 0 * _ + 0 * _ = (0 : ℂ)
      simp
    have sid := fun ξ => ((hStrip.2.1 _ _ hP hP).1.identity ξ).1
    have c := fun ξ => linComb_at hStrip hP hP hid hid (sid ξ) (sid ξ) 0 0
    rw [e] at c
    refine ⟨(c 0).1, fun ξ _ => ⟨(c ξ).2.1, fun v => ⟨?_, fun h => absurd h (by omega)⟩⟩⟩
    rw [(c ξ).2.2]
    simp [wInner_zero_right]
  | i + 1, hi => by
    have hik : i < k := hi
    obtain ⟨hper, hsum⟩ := noiseCovariance_conditions ha hLoc hMean hCov hIdx hSym hStrip hL hk i hik.le
    have hP := (hIdx L hL k i hik.le).2.1
    have hP' := (hIdx L hL k (i + 1) hik).2.1
    have := hP.finite_quot
    have := hP'.finite_quot
    obtain ⟨hS, hSt, hreal⟩ := hLoc L hL k hk i hik
    obtain ⟨-, hid, -, -⟩ := hCov.1 _ hP'
    have sid := fun ξ => ((hStrip.2.1 _ _ hP' hP').1.identity ξ).1
    have eN : noiseCovariance a L k (fun _ => 1) (i + 1) =
        StripSymbols.linCombKernel ((a⁻¹ : ℝ) : ℂ) (((L : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ)
          (idKernel (colourEdges L k (i + 1)))
          (compKernel (compKernel (meanStepKernel L k (fun _ => 1) i)
            (noiseCovariance a L k (fun _ => 1) i))
            (kernelTranspose (colourEdges L k i) (colourEdges L k (i + 1))
              (meanStepKernel L k (fun _ => 1) i))) := by
      rw [noiseCovariance, invRadiusDiag_trivial hMean hL hk hik]
      funext y x
      rfl
    have recursion : ∀ ξ ∈ realDualPoints,
        IsPeriodicKernel (colourEdges L k (i + 1)) (colourEdges L k (i + 1))
          (noiseCovariance a L k (fun _ => 1) (i + 1)) ∧
        SymbolSummableAt (colourEdges L k (i + 1)) (colourEdges L k (i + 1))
          (noiseCovariance a L k (fun _ => 1) (i + 1)) ξ ∧
        symbolHom (colourEdges L k (i + 1)) (colourEdges L k (i + 1))
          (noiseCovariance a L k (fun _ => 1) (i + 1)) ξ =
          ((a⁻¹ : ℝ) : ℂ) • symbolHom (colourEdges L k (i + 1)) (colourEdges L k (i + 1))
              (idKernel (colourEdges L k (i + 1))) ξ +
            (((L : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ) •
              ((symbolHom (colourEdges L k i) (colourEdges L k (i + 1))
                (meanStepKernel L k (fun _ => 1) i) ξ).comp
                (symbolHom (colourEdges L k i) (colourEdges L k i)
                  (noiseCovariance a L k (fun _ => 1) i) ξ)).comp
                (symbolHom (colourEdges L k (i + 1)) (colourEdges L k i)
                  (kernelTranspose (colourEdges L k i) (colourEdges L k (i + 1))
                    (meanStepKernel L k (fun _ => 1) i)) ξ) := by
      intro ξ hξ
      have sS := summable_at hStrip hP hP' hS ξ
      have sSt := summable_at hStrip hP' hP hSt ξ
      have p₁ := comp_at hStrip hP hP' hP hS.1 hper sS (hsum ξ hξ).1
      have p₂ := comp_at hStrip hP hP' hP' p₁.1 hSt.1 p₁.2.1 sSt
      have c := linComb_at hStrip hP' hP' hid p₂.1 (sid ξ) p₂.2.1 ((a⁻¹ : ℝ) : ℂ)
        (((L : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ)
      rw [eN]
      refine ⟨c.1, c.2.1, c.2.2.trans ?_⟩
      rw [p₂.2.2, p₁.2.2]
    have hL0 : (0 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 0 < L)
    have hzero : (0 : Fin 4 → ℂ) ∈ realDualPoints := fun μ => by simp
    refine ⟨(recursion 0 hzero).1, fun ξ hξ => ⟨(recursion ξ hξ).2.1, fun v => ?_⟩⟩
    have hadj := wInner_symbolHom_transpose (ξ := ξ) hP hP'
      (hSym.1 _ _ _ hP hP' hP' _ _ 1 hS.1 (hS.2.2 1 one_pos) hSt.1 (hSt.2.2 1 one_pos)) hreal hξ
    obtain ⟨u, hu⟩ : ∃ u, u = symbolHom (colourEdges L k (i + 1)) (colourEdges L k i)
        (kernelTranspose (colourEdges L k i) (colourEdges L k (i + 1))
          (meanStepKernel L k (fun _ => 1) i)) ξ v := ⟨_, rfl⟩
    have hsum₂ := ((hsum ξ hξ).2 u).1
    have e : PeriodicOperators.wInner ((colourEdges L k (i + 1)).quotWeight 1) v
        (symbolHom (colourEdges L k (i + 1)) (colourEdges L k (i + 1))
          (noiseCovariance a L k (fun _ => 1) (i + 1)) ξ v) =
        ((a⁻¹ : ℝ) : ℂ) * PeriodicOperators.wInner ((colourEdges L k (i + 1)).quotWeight 1) v v +
          (((L : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ) * PeriodicOperators.wInner ((colourEdges L k i).quotWeight 1) u
            (symbolHom (colourEdges L k i) (colourEdges L k i)
              (noiseCovariance a L k (fun _ => 1) i) ξ u) := by
      rw [(recursion ξ hξ).2.2]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply]
      rw [symbolHom_idKernel hCov hP', wInner_add_right, wInner_smul_right, wInner_smul_right,
        hadj, ← hu]
    have hself := wInner_self_re_nonneg _ (quotWeight_pos hP') v
    have hinv : 0 ≤ a⁻¹ := (inv_pos.2 ha).le
    have hL2 : 0 ≤ (L : ℝ) ^ (-2 : ℤ) := (zpow_pos hL0 _).le
    have e' : (PeriodicOperators.wInner ((colourEdges L k (i + 1)).quotWeight 1) v
        (symbolHom (colourEdges L k (i + 1)) (colourEdges L k (i + 1))
          (noiseCovariance a L k (fun _ => 1) (i + 1)) ξ v)).re =
        a⁻¹ * (PeriodicOperators.wInner ((colourEdges L k (i + 1)).quotWeight 1) v v).re +
          (L : ℝ) ^ (-2 : ℤ) * (PeriodicOperators.wInner ((colourEdges L k i).quotWeight 1) u
            (symbolHom (colourEdges L k i) (colourEdges L k i)
              (noiseCovariance a L k (fun _ => 1) i) ξ u)).re := by
      rw [e, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    rw [e']
    have h1 := mul_nonneg hinv hself
    have h2 := mul_nonneg hL2 hsum₂
    exact ⟨by linarith, fun _ => by linarith⟩
end Levels
end FullLattice.IdentityNoise
theorem noiseCovarianceAtIdentityPositive_holds (hLoc : MeanStepAtTrivialFieldFiniteRange)
    (hMean : MeanMapsAtTrivialField)
    (hCov : PeriodicOperators.CovariantFiniteRange.Claim)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim)
    (hSym : PeriodicOperators.Symbols.Claim)
    (hStrip : PeriodicOperators.StripSymbols.Claim) :
    NoiseCovarianceAtIdentityPositive :=
  fun _ ha _ hL _ hk i hi =>
    FullLattice.IdentityNoise.noiseCovariance_conditions ha hLoc hMean hCov hIdx hSym hStrip hL hk i hi
end YangMills.Construction.RunningCouplingSlope
end
