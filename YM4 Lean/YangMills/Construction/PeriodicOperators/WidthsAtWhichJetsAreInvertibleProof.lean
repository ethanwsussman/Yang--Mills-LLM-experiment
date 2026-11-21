import YangMills.Construction.PeriodicOperators.IntegrandOfTheLogarithmicNumberOfAFunctionProof
import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHom
import YangMills.Construction.PeriodicOperators.SymbolOfAnOperatorWithDecayProof
import YangMills.Construction.PeriodicOperators.SymbolsOnStrips
import YangMills.Construction.PeriodicOperators.WidthsAtWhichJetsAreInvertible
import Mathlib
set_option autoImplicit false
open Filter Set MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.InvertibleJetWidths
open InfiniteLattice (AmbientSpace)
open Coordinates (ComplexCoordinates)
open Coordinates.ComplexCoordinates (stdBasisVector)
open Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn)
open StripBound (logDetForm)
open JetQuad (IsInvertibleJet IsJet EqAsJet logNumber logDensity)
section Lines
variable {N : ℕ}
def coordLine (O : Set (ComplexCoordinates N)) (a : ComplexCoordinates N) (j : Fin N) : Set ℂ :=
  {ζ | a + ζ • stdBasisVector j ∈ O}
theorem isOpen_coordLine {O : Set (ComplexCoordinates N)} (hO : IsOpen O) (a : ComplexCoordinates N)
    (j : Fin N) : IsOpen (coordLine O a j) := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.isOpen_coordLine <;> assumption
theorem differentiableOn_coordLine {O : Set (ComplexCoordinates N)} {g : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => g z) (a : ComplexCoordinates N)
    (j : Fin N) :
    DifferentiableOn ℂ (fun ζ : ℂ => g (a + ζ • stdBasisVector j)) (coordLine O a j) := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.differentiableOn_coordLine <;> assumption
theorem isHolomorphicIn_of_coordLines {O : Set (ComplexCoordinates N)}
    {g : ComplexCoordinates N → ℂ} (hO : IsOpen O) (hc : ContinuousOn g O)
    (hl : ∀ a j, DifferentiableOn ℂ (fun ζ : ℂ => g (a + ζ • stdBasisVector j)) (coordLine O a j)) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => g z := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.isHolomorphicIn_of_coordLine <;> assumption
end Lines
section Integrals
variable {N : ℕ}
theorem norm_stdBasisVector (j : Fin N) : ‖(stdBasisVector j : ComplexCoordinates N)‖ = 1 := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.norm_stdBasisVector <;> assumption
variable {C : Set AmbientSpace} {O : Set (ComplexCoordinates N)}
  {Φ : AmbientSpace → ComplexCoordinates N → ℂ}
theorem continuousOn_setIntegral_param (hC : IsCompact C) (hCm : MeasurableSet C) (hO : IsOpen O)
    (hc : ContinuousOn (fun q : AmbientSpace × ComplexCoordinates N => Φ q.1 q.2) (C ×ˢ O)) :
    ContinuousOn (fun p => ∫ x in C, Φ x p) O := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.continuousOn_setIntegral_slice <;> assumption
theorem differentiableAt_setIntegral_coordLine (hC : IsCompact C) (hCm : MeasurableSet C)
    (hO : IsOpen O)
    (hc : ContinuousOn (fun q : AmbientSpace × ComplexCoordinates N => Φ q.1 q.2) (C ×ˢ O))
    (hl : ∀ x ∈ C, ∀ a j,
      DifferentiableOn ℂ (fun ζ : ℂ => Φ x (a + ζ • stdBasisVector j)) (coordLine O a j))
    {p₁ : ComplexCoordinates N} (hp₁ : p₁ ∈ O) (j : Fin N) :
    DifferentiableAt ℂ (fun ζ : ℂ => ∫ x in C, Φ x (p₁ + ζ • stdBasisVector j)) 0 := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.differentiableAt_setIntegral_coordLine <;> assumption
theorem differentiableOn_setIntegral_coordLine (hC : IsCompact C) (hCm : MeasurableSet C)
    (hO : IsOpen O)
    (hc : ContinuousOn (fun q : AmbientSpace × ComplexCoordinates N => Φ q.1 q.2) (C ×ˢ O))
    (hl : ∀ x ∈ C, ∀ a j,
      DifferentiableOn ℂ (fun ζ : ℂ => Φ x (a + ζ • stdBasisVector j)) (coordLine O a j))
    (a : ComplexCoordinates N) (j : Fin N) :
    DifferentiableOn ℂ (fun ζ : ℂ => ∫ x in C, Φ x (a + ζ • stdBasisVector j))
      (coordLine O a j) := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.differentiableOn_setIntegral_coordLine <;> assumption
end Integrals
section Entries
variable {J J' J'' : Type}
theorem linearMapEntry_eq_apply [DecidableEq J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) (c' : J') (c : J) :
    linearMapEntry M c' c = M (Pi.single c 1) c' := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.linearMapEntry_eq_apply <;> assumption
open Classical in
def basisFn (c : J) : J → ℂ := Pi.single c 1
theorem linearMapEntry_comp [Fintype J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ))
    (N : (J'' → ℂ) →ₗ[ℂ] (J → ℂ)) (c' : J') (c : J'') :
    linearMapEntry (M.comp N) c' c = ∑ k, linearMapEntry M c' k * linearMapEntry N k c := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.linearMapEntry_comp <;> assumption
theorem trace_eq_sum_linearMapEntry [Fintype J] (M : (J → ℂ) →ₗ[ℂ] (J → ℂ)) :
    LinearMap.trace ℂ (J → ℂ) M = ∑ i, linearMapEntry M i i := by apply _root_.YangMills.SharedProofs.p9894 <;> assumption
def traceForm (b x y b' z : Module.End ℂ (J → ℂ)) : ℂ :=
  LinearMap.trace ℂ (J → ℂ) (b * x - b * (y * (b' * z)))
theorem traceForm_eq_sum [Fintype J] (b x y b' z : Module.End ℂ (J → ℂ)) :
    traceForm b x y b' z = ∑ i, ((∑ k, linearMapEntry b i k * linearMapEntry x k i) -
      ∑ k, linearMapEntry b i k * ∑ l, linearMapEntry y k l *
        ∑ m, linearMapEntry b' l m * linearMapEntry z m i) := by
  unfold traceForm
  rw [trace_eq_sum_linearMapEntry]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : ∀ M N : Module.End ℂ (J → ℂ), linearMapEntry (M - N) i i =
      linearMapEntry M i i - linearMapEntry N i i := fun M N => by simp [linearMapEntry]
  rw [hsub]
  congr 1
  · exact linearMapEntry_comp b x i i
  · refine (linearMapEntry_comp b _ i i).trans (Finset.sum_congr rfl fun k _ => ?_)
    congr 1
    refine (linearMapEntry_comp y _ k i).trans (Finset.sum_congr rfl fun l _ => ?_)
    congr 1
    exact linearMapEntry_comp b' z l i
theorem ring_inverse_conj {R : Type} [Ring R] {u u' : R} (h₁ : u * u' = 1) (h₂ : u' * u = 1)
    (a : R) : Ring.inverse (u' * a * u) = u' * Ring.inverse a * u := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.ring_inverse_conj <;> assumption
end Entries
section Phases
variable {I : PeriodicData}
def sitePhase (I : PeriodicData) (e : Fin 4 → ℤ) (ι : I.Carrier) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I *
    bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos ι)))
theorem norm_phaseOn (hI : IsPeriodic I) (e : Fin 4 → ℤ) (c : I.UnitQuot) :
    ‖phaseOn I e c‖ = 1 := by apply _root_.YangMills.SharedProofs.p4911 <;> assumption
theorem phaseMul_neg_mul (hI : IsPeriodic I) (e : Fin 4 → ℤ) :
    (phaseMul I (-e) * phaseMul I e : Module.End ℂ (I.UnitQuot → ℂ)) = 1 := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.phaseMul_neg_mul <;> assumption
theorem phaseMul_mul_neg (hI : IsPeriodic I) (e : Fin 4 → ℤ) :
    (phaseMul I e * phaseMul I (-e) : Module.End ℂ (I.UnitQuot → ℂ)) = 1 := by
  simpa using phaseMul_neg_mul hI (-e)
theorem quotHomInverse_phaseMul (hI : IsPeriodic I) (e : Fin 4 → ℤ) :
    quotHomInverse (phaseMul I e) = phaseMul I (-e) := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.quotHomInverse_phaseMul <;> assumption
end Phases
def basisLogDensity (F I : PeriodicData) (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ)
    (c c' : F.UnitQuot) (κ p : Fin 4 → ℂ) : ℂ :=
  logDensity p (jetAlong F I I T p (basisFn c) (basisFn c')) κ
section SeparateHolomorphy
abbrev MomentumPairSpace : Type := (Fin 4 → ℂ) × (Fin 4 → ℂ)
structure IsSeparatelyHolomorphic (U : Set MomentumPairSpace) (h : MomentumPairSpace → ℂ) :
    Prop where
  continuousOn : ContinuousOn h U
  alongFst : ∀ (x : MomentumPairSpace) (j : Fin 4),
    DifferentiableOn ℂ (fun ζ : ℂ => h (x.1 + ζ • stdBasisVector j, x.2))
      {ζ : ℂ | (x.1 + ζ • stdBasisVector j, x.2) ∈ U}
  alongSnd : ∀ (x : MomentumPairSpace) (j : Fin 4),
    DifferentiableOn ℂ (fun ζ : ℂ => h (x.1, x.2 + ζ • stdBasisVector j))
      {ζ : ℂ | (x.1, x.2 + ζ • stdBasisVector j) ∈ U}
variable {U : Set MomentumPairSpace} {h h' : MomentumPairSpace → ℂ}
theorem IsSeparatelyHolomorphic.sub (a : IsSeparatelyHolomorphic U h)
    (b : IsSeparatelyHolomorphic U h') : IsSeparatelyHolomorphic U fun x => h x - h' x :=
  ⟨a.continuousOn.sub b.continuousOn, fun x j => (a.alongFst x j).sub (b.alongFst x j),
    fun x j => (a.alongSnd x j).sub (b.alongSnd x j)⟩
theorem IsSeparatelyHolomorphic.mul (a : IsSeparatelyHolomorphic U h)
    (b : IsSeparatelyHolomorphic U h') : IsSeparatelyHolomorphic U fun x => h x * h' x :=
  ⟨a.continuousOn.mul b.continuousOn, fun x j => (a.alongFst x j).mul (b.alongFst x j),
    fun x j => (a.alongSnd x j).mul (b.alongSnd x j)⟩
theorem IsSeparatelyHolomorphic.const (z : ℂ) : IsSeparatelyHolomorphic U fun _ => z :=
  ⟨continuousOn_const, fun _ _ => differentiableOn_const _, fun _ _ => differentiableOn_const _⟩
theorem IsSeparatelyHolomorphic.add (a : IsSeparatelyHolomorphic U h)
    (b : IsSeparatelyHolomorphic U h') : IsSeparatelyHolomorphic U fun x => h x + h' x :=
  ⟨a.continuousOn.add b.continuousOn, fun x j => (a.alongFst x j).add (b.alongFst x j),
    fun x j => (a.alongSnd x j).add (b.alongSnd x j)⟩
theorem IsSeparatelyHolomorphic.sum {K : Type} (s : Finset K) {g : K → MomentumPairSpace → ℂ}
    (hg : ∀ k, IsSeparatelyHolomorphic U (g k)) :
    IsSeparatelyHolomorphic U fun x => ∑ k ∈ s, g k x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsSeparatelyHolomorphic.const (U := U) 0
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (hg k).add ih
theorem IsSeparatelyHolomorphic.of_differentiable (hd : Differentiable ℂ h) :
    IsSeparatelyHolomorphic U h :=
  ⟨hd.continuous.continuousOn,
    fun x j => (hd.comp (f := fun ζ : ℂ => ((x.1 + ζ • stdBasisVector j, x.2) : MomentumPairSpace))
      (by fun_prop)).differentiableOn,
    fun x j => (hd.comp (f := fun ζ : ℂ => ((x.1, x.2 + ζ • stdBasisVector j) : MomentumPairSpace))
      (by fun_prop)).differentiableOn⟩
def shiftedPairs (O : Set (Fin 4 → ℂ)) : Set MomentumPairSpace := {x | x.1 ∈ O ∧ x.1 - x.2 ∈ O}
variable {O : Set (Fin 4 → ℂ)} {β : (Fin 4 → ℂ) → ℂ}
theorem IsSeparatelyHolomorphic.of_fst
    (hβ : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => β z) :
    IsSeparatelyHolomorphic (shiftedPairs O) fun x => β x.1 := by
  refine ⟨?_, fun x j => ?_, fun x j => ?_⟩
  · exact ((continuousOn_pi.1 hβ.2.1 0).comp continuous_fst.continuousOn fun x hx => hx.1)
  · exact (differentiableOn_coordLine hβ x.1 j).mono fun ζ hζ => hζ.1
  · change DifferentiableOn ℂ (fun _ => β x.1) _
    exact differentiableOn_const _
theorem IsSeparatelyHolomorphic.of_fst_sub_snd
    (hβ : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => β z) :
    IsSeparatelyHolomorphic (shiftedPairs O) fun x => β (x.1 - x.2) := by
  refine ⟨?_, fun x j => ?_, fun x j => ?_⟩
  · exact ((continuousOn_pi.1 hβ.2.1 0).comp
      (continuous_fst.sub continuous_snd).continuousOn fun x hx => hx.2)
  · have e : ∀ ζ : ℂ, x.1 + ζ • stdBasisVector j - x.2 =
        (x.1 - x.2) + ζ • stdBasisVector j := fun ζ => by
      abel
    simp only [e]
    refine (differentiableOn_coordLine hβ (x.1 - x.2) j).mono fun ζ hζ => ?_
    have := hζ.2
    simp only [e] at this
    exact this
  · have e : ∀ ζ : ℂ, x.1 - (x.2 + ζ • stdBasisVector j) =
        (x.1 - x.2) + (-ζ) • stdBasisVector j :=
      fun ζ => by
        rw [neg_smul]
        abel
    simp only [e]
    refine (differentiableOn_coordLine hβ (x.1 - x.2) j).comp (f := fun ζ : ℂ => -ζ)
      (differentiable_neg.differentiableOn) fun ζ hζ => ?_
    have := hζ.2
    simp only [e] at this
    exact this
theorem differentiable_expSum_fst {n : ℕ} (a : Fin n → ℂ)
    (f : Fin n → JetDomains.MomentumLinearForm) :
    Differentiable ℂ fun x : MomentumPairSpace => JetDomains.expSum a f x.1 x.2 := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.differentiable_expSum_fst <;> assumption
theorem differentiable_expSum_sub {n : ℕ} (a : Fin n → ℂ)
    (f : Fin n → JetDomains.MomentumLinearForm) :
    Differentiable ℂ fun x : MomentumPairSpace => JetDomains.expSum a f (x.1 - x.2) x.2 := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.differentiable_expSum_sub <;> assumption
variable {F I : PeriodicData} [Fintype I.UnitQuot] {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
open JetDomains
theorem isSeparatelyHolomorphic_basisLogDensity (h : OpFunJetProperties F I I T)
    (hβ : ∀ i k : I.UnitQuot, ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun κ _ =>
      linearMapEntry (quotHomInverse (symbolHom I I (coeffZero F I I T) κ)) i k)
    (c c' : F.UnitQuot) :
    IsSeparatelyHolomorphic (shiftedPairs O) fun x => basisLogDensity F I T c c' x.1 x.2 := by
  have h11 : ∀ k i : I.UnitQuot, IsSeparatelyHolomorphic (shiftedPairs O)
      fun x : MomentumPairSpace =>
        linearMapEntry ((jetAlong F I I T x.2 (basisFn c) (basisFn c')).f11 x.1) k i :=
    fun k i => by
      obtain ⟨n, f, a, ha⟩ := h.entries_f11 k i
      simp only [ha]
      exact IsSeparatelyHolomorphic.of_differentiable (differentiable_expSum_fst _ f)
  have h01 : ∀ k i : I.UnitQuot, IsSeparatelyHolomorphic (shiftedPairs O)
      fun x : MomentumPairSpace =>
        linearMapEntry ((jetAlong F I I T x.2 (basisFn c) (basisFn c')).f01 x.1) k i :=
    fun k i => by
      obtain ⟨n, f, a, ha⟩ := h.entries_f01 k i
      simp only [ha]
      exact IsSeparatelyHolomorphic.of_differentiable (differentiable_expSum_fst _ f)
  have h10 : ∀ k i : I.UnitQuot, IsSeparatelyHolomorphic (shiftedPairs O)
      fun x : MomentumPairSpace =>
        linearMapEntry ((jetAlong F I I T x.2 (basisFn c) (basisFn c')).f10 (x.1 - x.2)) k i :=
    fun k i => by
      obtain ⟨n, f, a, ha⟩ := h.entries_f10 k i
      simp only [ha]
      exact IsSeparatelyHolomorphic.of_differentiable (differentiable_expSum_sub _ f)
  have e : (fun x : MomentumPairSpace => basisLogDensity F I T c c' x.1 x.2) = fun x =>
      ∑ i, ((∑ k, linearMapEntry (quotHomInverse (symbolHom I I (coeffZero F I I T) x.1)) i k *
          linearMapEntry ((jetAlong F I I T x.2 (basisFn c) (basisFn c')).f11 x.1) k i) -
        ∑ k, linearMapEntry (quotHomInverse (symbolHom I I (coeffZero F I I T) x.1)) i k *
          ∑ l, linearMapEntry
              ((jetAlong F I I T x.2 (basisFn c) (basisFn c')).f10 (x.1 - x.2)) k l *
            ∑ m, linearMapEntry (quotHomInverse (symbolHom I I (coeffZero F I I T)
              (x.1 - x.2))) l m *
              linearMapEntry ((jetAlong F I I T x.2 (basisFn c) (basisFn c')).f01 x.1) m i) := by
    funext x
    exact traceForm_eq_sum _ _ _ _ _
  rw [e]
  refine IsSeparatelyHolomorphic.sum _ fun i =>
    (IsSeparatelyHolomorphic.sum _ fun k => ?_).sub (IsSeparatelyHolomorphic.sum _ fun k => ?_)
  · exact (IsSeparatelyHolomorphic.of_fst (hβ i k)).mul (h11 k i)
  · refine (IsSeparatelyHolomorphic.of_fst (hβ i k)).mul (IsSeparatelyHolomorphic.sum _ fun l => ?_)
    refine (h10 k l).mul (IsSeparatelyHolomorphic.sum _ fun m => ?_)
    exact (IsSeparatelyHolomorphic.of_fst_sub_snd (hβ l m)).mul (h01 m i)
end SeparateHolomorphy
section PeriodBox
def periodBox (r : ℝ) : Set (Fin 4 → ℂ) :=
  {z | ∀ μ, (z μ).re ∈ Icc 0 (2 * Real.pi) ∧ |(z μ).im| ≤ r}
theorem isCompact_periodBox (r : ℝ) : IsCompact (periodBox r) := by
  have e : periodBox r =
      Set.pi univ fun _ : Fin 4 => Icc 0 (2 * Real.pi) ×ℂ Icc (-r) r := by
    ext z
    simp [periodBox, Complex.mem_reProdIm, abs_le]
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_Icc.reProdIm isCompact_Icc
theorem exists_addTwoPiInt_re_mem (z : Fin 4 → ℂ) :
    ∃ (e : Fin 4 → ℤ) (z₀ : Fin 4 → ℂ), z = addTwoPiInt z₀ e ∧
      ∀ μ, (z₀ μ).re ∈ Icc 0 (2 * Real.pi) ∧ (z₀ μ).im = (z μ).im := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.exists_addTwoPiInt_eq <;> assumption
end PeriodBox
section Bounds
variable {I : PeriodicData}
theorem iSup_quotHomNorm_lt_top_iff (hfin : ∀ A : QuotHom I I, quotHomNorm A ≠ ⊤)
    (hbd : HomNorm.NormBoundedIffEntriesBounded I I)
    (S : Set (Fin 4 → ℂ)) (M : (Fin 4 → ℂ) → QuotHom I I) :
    (⨆ κ ∈ S, quotHomNorm (M κ)) < ⊤ ↔ QuotHomFamilyBoundedOn S M := by
  rw [← hbd _ S M]
  constructor
  · intro h
    refine ⟨(⨆ κ ∈ S, quotHomNorm (M κ)).toReal, fun x hx => ?_⟩
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono h.ne (le_iSup₂ (f := fun κ _ => quotHomNorm (M κ)) x hx)
  · rintro ⟨C, hC⟩
    refine lt_of_le_of_lt (iSup₂_le fun x hx => ?_) (ENNReal.ofReal_lt_top (r := C))
    have h := hC x hx
    rw [abs_of_nonneg ENNReal.toReal_nonneg] at h
    calc quotHomNorm (M x) = ENNReal.ofReal (quotHomNorm (M x)).toReal :=
          (ENNReal.ofReal_toReal (hfin _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h
theorem norm_linearMapEntry_phaseMul_conj (hI : IsPeriodic I) (e : Fin 4 → ℤ)
    (A : Module.End ℂ (I.UnitQuot → ℂ)) (c' c : I.UnitQuot) :
    ‖linearMapEntry (phaseMul I (-e) * A * phaseMul I e :
        Module.End ℂ (I.UnitQuot → ℂ)) c' c‖ = ‖linearMapEntry A c' c‖ := by
  classical
  have hu : phaseMul I e (Pi.single c 1) =
      phaseOn I e c • (Pi.single c 1 : I.UnitQuot → ℂ) := by
    funext i
    by_cases h : i = c
    · subst h
      simp [phaseMul]
    · simp [phaseMul, Pi.single_eq_of_ne h]
  rw [linearMapEntry_eq_apply, linearMapEntry_eq_apply]
  simp only [Module.End.mul_apply, hu, map_smul]
  simp [phaseMul, norm_phaseOn hI]
theorem isInvertibleQuotHom_of_isUnit {M : QuotHom I I}
    (h : IsUnit (M : Module.End ℂ (I.UnitQuot → ℂ))) : IsInvertibleQuotHom M := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.isInvertibleQuotHom_of_isUnit <;> assumption
end Bounds
section WiderStrip
def maxAbsIm (κ : Fin 4 → ℂ) : ℝ := ‖fun μ => (κ μ).im‖
theorem continuous_maxAbsIm : Continuous maxAbsIm := by
  unfold maxAbsIm
  fun_prop
theorem maxAbsIm_le_iff {κ : Fin 4 → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    maxAbsIm κ ≤ ρ ↔ κ ∈ imStrip ρ := by
  unfold maxAbsIm
  rw [pi_norm_le_iff_of_nonneg hρ]
  rfl
theorem exists_addTwoPiInt_mem_periodBox {κ : Fin 4 → ℂ} {ρ : ℝ} (hκ : κ ∈ imStrip ρ) :
    ∃ (e : Fin 4 → ℤ) (κ₀ : Fin 4 → ℂ), κ = addTwoPiInt κ₀ e ∧ κ₀ ∈ periodBox ρ ∧
      κ₀ ∈ imStrip ρ := by
  obtain ⟨e, κ₀, h, h₀⟩ := exists_addTwoPiInt_re_mem κ
  refine ⟨e, κ₀, h, fun μ => ⟨(h₀ μ).1, ?_⟩, fun μ => ?_⟩
  · rw [(h₀ μ).2]
    exact hκ μ
  · rw [(h₀ μ).2]
    exact hκ μ
theorem exists_wider_imStrip_ne_zero {D : (Fin 4 → ℂ) → ℂ} (hD : Continuous D)
    (hper : ∀ κ e, D κ ≠ 0 → D (addTwoPiInt κ e) ≠ 0) {r : ℝ} (hr : 0 ≤ r)
    (h0 : ∀ κ ∈ imStrip r, D κ ≠ 0) : ∃ η : ℝ, 0 < η ∧ ∀ κ ∈ imStrip (r + η), D κ ≠ 0 := by
  have hK : IsCompact (periodBox (r + 1) ∩ D ⁻¹' {0}) :=
    (isCompact_periodBox _).inter_right (isClosed_singleton.preimage hD)
  rcases (periodBox (r + 1) ∩ D ⁻¹' {0}).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun κ hκ => ?_⟩
    obtain ⟨e, κ₀, rfl, hb, -⟩ := exists_addTwoPiInt_mem_periodBox hκ
    refine hper _ _ fun hz => ?_
    have : κ₀ ∈ periodBox (r + 1) ∩ D ⁻¹' {0} := ⟨hb, hz⟩
    rw [he] at this
    exact this
  · obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne continuous_maxAbsIm.continuousOn
    have hlt : r < maxAbsIm z := by
      by_contra hnot
      exact h0 z ((maxAbsIm_le_iff hr).1 (not_lt.1 hnot)) hz.2
    have hη : 0 < min 1 ((maxAbsIm z - r) / 2) :=
      lt_min one_pos (by linarith)
    refine ⟨_, hη, fun κ hκ => ?_⟩
    have h1 : min 1 ((maxAbsIm z - r) / 2) ≤ 1 := min_le_left _ _
    have h2 : min 1 ((maxAbsIm z - r) / 2) ≤ (maxAbsIm z - r) / 2 :=
      min_le_right _ _
    obtain ⟨e, κ₀, rfl, hb, hs⟩ := exists_addTwoPiInt_mem_periodBox hκ
    refine hper _ _ fun hzero => ?_
    have hin : κ₀ ∈ periodBox (r + 1) := fun μ =>
      ⟨(hb μ).1, (hb μ).2.trans (by linarith)⟩
    have hle := hmin ⟨hin, hzero⟩
    have hle' : maxAbsIm κ₀ ≤ r + min 1 ((maxAbsIm z - r) / 2) :=
      (maxAbsIm_le_iff (by positivity)).2 hs
    have : maxAbsIm z ≤ maxAbsIm κ₀ := hle
    linarith
end WiderStrip
section Widths
variable {F I : PeriodicData} {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
open JetDomains
theorem zero_mem_imStrip {δ : ℝ} (hδ : 0 < δ) : (0 : Fin 4 → ℂ) ∈ imStrip δ :=
  fun μ => by simpa using hδ.le
theorem imStrip_mono {a b : ℝ} (h : a ≤ b) : imStrip a ⊆ imStrip b :=
  fun _ hκ μ => (hκ μ).trans h
theorem isInvertibleJet_iff (hfin : ∀ A : QuotHom I I, quotHomNorm A ≠ ⊤)
    (hbd : HomNorm.NormBoundedIffEntriesBounded I I)
    (h : OpFunJetProperties F I I T) {δ : ℝ} (hδ : 0 < δ) {p : Fin 4 → ℂ}
    (hp : p ∈ imStrip δ) (εPlus εMinus : F.UnitQuot → ℂ) :
    IsInvertibleJet δ p (jetAlong F I I T p εPlus εMinus) ↔
      SymbolInvertibleBoundedInverse F I T δ := by
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, (iSup_quotHomNorm_lt_top_iff hfin hbd _ _).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h.isJet δ hδ p hp εPlus εMinus, h1, (iSup_quotHomNorm_lt_top_iff hfin hbd _ _).2 h2⟩
theorem continuous_symbolHom_entry (h : OpFunJetProperties F I I T) (c' c : I.UnitQuot) :
    Continuous fun κ => linearMapEntry (symbolHom I I (coeffZero F I I T) κ) c' c := by
  refine continuous_iff_continuousAt.2 fun κ => ?_
  have hδ : 0 < ‖κ‖ + 1 := by positivity
  have hκ : κ ∈ imStrip (2 * (‖κ‖ + 1)) := fun μ => by
    have h1 : |(κ μ).im| ≤ ‖κ μ‖ := Complex.abs_im_le_norm _
    have h2 : ‖κ μ‖ ≤ ‖κ‖ := norm_le_pi_norm κ μ
    linarith
  obtain ⟨O, hO, hsub, hh⟩ :=
    (h.isJet _ hδ 0 (zero_mem_imStrip hδ) 0 0).holo_f00
  exact (continuousOn_pi.1 (hh c' c).2.1 0).continuousAt (hO.mem_nhds (hsub hκ))
theorem symbolHom_addTwoPiInt (hI : IsPeriodic I) (h : OpFunJetProperties F I I T)
    (e : Fin 4 → ℤ) (κ : Fin 4 → ℂ) :
    symbolHom I I (coeffZero F I I T) (addTwoPiInt κ e) =
      (phaseMul I (-e) * symbolHom I I (coeffZero F I I T) κ *
        phaseMul I e : Module.End ℂ (I.UnitQuot → ℂ)) := by
  have hq := (h.quasiPeriodic 0 0 0).1 e κ (mem_univ _)
  have hq' : symbolHom I I (coeffZero F I I T) (addTwoPiInt κ e) =
      (quotHomInverse (phaseMul I e)).comp
        ((symbolHom I I (coeffZero F I I T) κ).comp (phaseMul I e)) := hq
  rw [hq', quotHomInverse_phaseMul hI, mul_assoc]
  rfl
theorem continuous_det_symbolHom [Fintype I.UnitQuot] (h : OpFunJetProperties F I I T) :
    Continuous fun κ => LinearMap.det
      (symbolHom I I (coeffZero F I I T) κ : Module.End ℂ (I.UnitQuot → ℂ)) := by
  classical
  have e : (fun κ => LinearMap.det
      (symbolHom I I (coeffZero F I I T) κ : Module.End ℂ (I.UnitQuot → ℂ))) =
      fun κ => (Matrix.of fun c' c =>
        linearMapEntry (symbolHom I I (coeffZero F I I T) κ) c' c).det := by
    funext κ
    rw [← LinearMap.det_toMatrix']
    congr 1
  rw [e]
  refine Continuous.matrix_det (continuous_matrix fun c' c => ?_)
  exact continuous_symbolHom_entry h c' c
theorem isUnit_end_iff_det_ne_zero [Fintype I.UnitQuot] (M : Module.End ℂ (I.UnitQuot → ℂ)) :
    IsUnit M ↔ LinearMap.det M ≠ 0 := by
  rw [LinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
theorem exists_larger_invertible_width [Fintype I.UnitQuot] (hI : IsPeriodic I)
    (h : OpFunJetProperties F I I T)
    (hInv : EntriesDets.QuotHomFamilyInvOnDual I)
    {δ : ℝ} (hδ : 0 < δ) (hs : SymbolInvertibleBoundedInverse F I T δ) :
    ∃ δPlus : ℝ, δ < δPlus ∧ SymbolInvertibleBoundedInverse F I T δPlus := by
  set M := symbolHom I I (coeffZero F I I T) with hM
  have hu₁ := fun e => phaseMul_mul_neg hI e
  have hu₂ := fun e => phaseMul_neg_mul hI e
  have hper : ∀ (κ : Fin 4 → ℂ) (e : Fin 4 → ℤ),
      LinearMap.det (M κ : Module.End ℂ (I.UnitQuot → ℂ)) ≠ 0 →
      LinearMap.det (M (addTwoPiInt κ e) : Module.End ℂ (I.UnitQuot → ℂ)) ≠ 0 := by
    intro κ e hκ
    rw [← isUnit_end_iff_det_ne_zero] at hκ ⊢
    rw [hM, symbolHom_addTwoPiInt hI h e κ]
    have a : IsUnit (phaseMul I e : Module.End ℂ (I.UnitQuot → ℂ)) :=
      ⟨⟨_, _, hu₁ e, hu₂ e⟩, rfl⟩
    have b : IsUnit (phaseMul I (-e) : Module.End ℂ (I.UnitQuot → ℂ)) :=
      ⟨⟨_, _, hu₂ e, hu₁ e⟩, rfl⟩
    exact (b.mul hκ).mul a
  obtain ⟨η, hη, hwide⟩ :=
    exists_wider_imStrip_ne_zero (continuous_det_symbolHom h) hper (r := 2 * δ) (by positivity)
      fun κ hκ => (isUnit_end_iff_det_ne_zero _).1 (hs.1 κ hκ)
  have hset : 2 * (δ + η / 2) = 2 * δ + η := by ring
  have hunit : ∀ κ ∈ imStrip (2 * (δ + η / 2)), IsUnit (M κ : Module.End ℂ (I.UnitQuot → ℂ)) :=
    fun κ hκ => (isUnit_end_iff_det_ne_zero _).2 (hwide κ (hset ▸ hκ))
  refine ⟨δ + η / 2, by linarith, hunit, fun e => ?_⟩
  have hcont := (hInv (imStrip (2 * (δ + η / 2))) M
    (fun κ hκ => isInvertibleQuotHom_of_isUnit (hunit κ hκ))).1
      ⟨by norm_num, fun e => (continuous_symbolHom_entry h e.1 e.2).continuousOn⟩
  have hsub : periodBox (2 * (δ + η / 2)) ⊆ imStrip (2 * (δ + η / 2)) :=
    fun κ hκ μ => (hκ μ).2
  obtain ⟨C, hC⟩ := (isCompact_periodBox (2 * (δ + η / 2))).exists_bound_of_continuousOn
    ((hcont.2 e).mono hsub)
  refine ⟨C, fun κ hκ => ?_⟩
  obtain ⟨e', κ₀, rfl, hb, -⟩ := exists_addTwoPiInt_mem_periodBox hκ
  have hi : quotHomInverse (M (addTwoPiInt κ₀ e')) =
      (phaseMul I (-e') * quotHomInverse (M κ₀) * phaseMul I e' :
        Module.End ℂ (I.UnitQuot → ℂ)) := by
    rw [hM, symbolHom_addTwoPiInt hI h e' κ₀]
    exact ring_inverse_conj (hu₁ e') (hu₂ e') _
  have := hC κ₀ hb
  simp only [quotHomEntries] at this ⊢
  rw [hi, norm_linearMapEntry_phaseMul_conj hI]
  exact this
end Widths
section Coefficients
variable {F I : PeriodicData} {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
theorem isOpen_openImStrip (ς : ℝ) : IsOpen (openImStrip ς) := by apply _root_.YangMills.Construction.PeriodicOperators.ExpDecaySymbol.isOpen_openImStrip <;> assumption
open JetDomains
open Classical in
theorem exists_holomorphic_logDetForm_coeff [Fintype I.UnitQuot] (hI : IsPeriodic I)
    (hfacts : OpFunJetProperties F I I T) (hCalc : JetCalculus.Claim)
    {δ : ℝ} (hδ : 0 < δ) {O₁ : Set (Fin 4 → ℂ)} (hsub : imStrip (2 * δ) ⊆ O₁)
    (hβ : ∀ i k : I.UnitQuot, ComplexCoordinates.IsHolomorphicIn (N' := 1) O₁ fun κ _ =>
      linearMapEntry (quotHomInverse (symbolHom I I (coeffZero F I I T) κ)) i k)
    (hinv : ∀ p ∈ imStrip δ, ∀ εPlus εMinus : F.UnitQuot → ℂ,
      IsInvertibleJet δ p (jetAlong F I I T p εPlus εMinus)) (c c' : F.UnitQuot) :
    ∃ g : (Fin 4 → ℂ) → ℂ, IsHolomorphicScalarIn (openImStrip (2 * δ)) g ∧
      ∀ p ∈ imStrip δ, g p = logDetForm F I T p (Pi.single c 1) (Pi.single c' 1) := by
  have hgood := isSeparatelyHolomorphic_basisLogDensity hfacts hβ c c'
  let Cube : Set AmbientSpace := Icc (fun _ : Fin 4 => -Real.pi) fun _ => Real.pi
  have hO := isOpen_openImStrip (2 * δ)
  have hpair : ∀ (κ : AmbientSpace) (p : Fin 4 → ℂ), p ∈ openImStrip (2 * δ) →
      ((toComplexVec κ, p) : MomentumPairSpace) ∈ shiftedPairs O₁ := by
    intro κ p hp
    refine ⟨hsub fun μ => ?_, hsub fun μ => ?_⟩
    · simp [toComplexVec]
      positivity
    · have := hp μ
      simp only [Pi.sub_apply, Complex.sub_im, toComplexVec, Complex.ofReal_im, zero_sub,
        abs_neg]
      exact this.le
  have hcv : Continuous toComplexVec := by
    unfold toComplexVec
    fun_prop
  have hcont : ContinuousOn
      (fun q : AmbientSpace × ComplexCoordinates 4 =>
        basisLogDensity F I T c c' (toComplexVec q.1) q.2)
      (Cube ×ˢ openImStrip (2 * δ)) :=
    hgood.continuousOn.comp
      (f := fun q : AmbientSpace × ComplexCoordinates 4 =>
        ((toComplexVec q.1, q.2) : MomentumPairSpace))
      (Continuous.continuousOn (by fun_prop)) fun q hq => hpair q.1 q.2 hq.2
  have hline : ∀ x ∈ Cube, ∀ a j, DifferentiableOn ℂ
      (fun ζ : ℂ => basisLogDensity F I T c c' (toComplexVec x) (a + ζ • stdBasisVector j))
      (coordLine (openImStrip (2 * δ)) a j) := fun x _ a j =>
    (hgood.alongSnd (toComplexVec x, a) j).mono fun ζ hζ => hpair x _ hζ
  have hCc : IsCompact Cube := isCompact_Icc
  have hCm : MeasurableSet Cube := measurableSet_Icc
  refine ⟨fun p => torusAverage fun κ => basisLogDensity F I T c c' (toComplexVec κ) p, ?_,
    fun p hp => ?_⟩
  · have h1 := continuousOn_setIntegral_param
      (Φ := fun κ p => basisLogDensity F I T c c' (toComplexVec κ) p) hCc hCm hO hcont
    have h2 := differentiableOn_setIntegral_coordLine
      (Φ := fun κ p => basisLogDensity F I T c c' (toComplexVec κ) p) hCc hCm hO hcont hline
    exact isHolomorphicIn_of_coordLines hO (continuousOn_const.mul h1)
      fun a j => (h2 a j).const_mul _
  · exact (((hCalc δ p hδ hp).2.2.2.2.2.2.1 I hI).2 _
      (hinv p hp (Pi.single c 1) (Pi.single c' 1))).symm
end Coefficients
theorem claim_holds (hLocal : JetDomains.OpFunJetTheory)
    (hCalc : JetCalculus.Claim)
    (hArgs : JetArgumentsAndEqualJets)
    (hInt : LogDensityBounds.Claim)
    (hLog : LogDetSecondDerivs.Claim)
    (hNorm : HomNorm.Claim)
    (hEnt : EntriesDets.Claim)
    (hStrips : StripSymbols.Claim) : Claim := by
  intro F I hF hI T hT
  have := hF.finite_quot
  have := hI.finite_quot
  let _ : Fintype F.UnitQuot := Fintype.ofFinite _
  let _ : Fintype I.UnitQuot := Fintype.ofFinite _
  have hfacts := hLocal.2.1 F I I hF hI hI T hT
  have hN := hNorm I I hI hI
  have hfin : ∀ A : QuotHom I I, quotHomNorm A ≠ ⊤ := fun A => (hN.1 A).2.ne
  have hbd := hN.2.2.2.2.1
  have hInv := (hEnt.2.2.1 I hI).2.2.1
  have hiff : ∀ {δ : ℝ}, 0 < δ → ∀ {p : Fin 4 → ℂ}, p ∈ imStrip δ →
      ∀ εPlus εMinus : F.UnitQuot → ℂ,
      (IsInvertibleJet δ p (jetAlong F I I T p εPlus εMinus) ↔
        SymbolInvertibleBoundedInverse F I T δ) :=
    fun hδ _ hp ε ε' => isInvertibleJet_iff hfin hbd hfacts hδ hp ε ε'
  have hwidth : ∀ δ : ℝ, 0 < δ → (HasInvertibleJetsAtWidth F I T δ ↔
      SymbolInvertibleBoundedInverse F I T δ) := fun δ hδ =>
    ⟨fun h => (hiff hδ (zero_mem_imStrip hδ) 0 0).1 (h.2 0 (zero_mem_imStrip hδ) 0 0),
      fun hs => ⟨hδ, fun p hp ε ε' => (hiff hδ hp ε ε').2 hs⟩⟩
  refine ⟨fun δ hδ => ⟨?_, ?_, ?_⟩, fun δ hw => ?_⟩
  · by_cases hs : SymbolInvertibleBoundedInverse F I T δ
    · exact Or.inl fun p hp ε ε' => (hiff hδ hp ε ε').2 hs
    · exact Or.inr fun p hp ε ε' h => hs ((hiff hδ hp ε ε').1 h)
  · exact fun h => (hiff hδ (zero_mem_imStrip hδ) 0 0).1 (h 0 (zero_mem_imStrip hδ) 0 0)
  · exact fun hs p hp ε ε' => (hiff hδ hp ε ε').2 hs
  have hδ := hw.1
  have hinv := hw.2
  have hs := (hwidth δ hδ).1 hw
  have hreal : ∀ κ : AmbientSpace,
      IsUnit (symbolHom I I (coeffZero F I I T) (toComplexVec κ) :
        Module.End ℂ (I.UnitQuot → ℂ)) := fun κ => hs.1 _ fun μ => by
    simp [toComplexVec]
    positivity
  have h0 := zero_mem_imStrip hδ
  obtain ⟨-, hJinv⟩ :=
    (hLocal.2.2 I I I hI hI hI δ 0 hδ h0).zeroPart_isJet _ (hinv 0 h0 0 0)
  obtain ⟨O₁, -, hsub, hhol⟩ := hJinv.holo_f00
  have hβ : ∀ i k : I.UnitQuot, ComplexCoordinates.IsHolomorphicIn (N' := 1) O₁ fun κ _ =>
      linearMapEntry (quotHomInverse (symbolHom I I (coeffZero F I I T) κ)) i k := hhol
  have hcoef := fun c c' => exists_holomorphic_logDetForm_coeff hI hfacts hCalc hδ hsub hβ hinv c c'
  have hopen := hStrips.1 (2 * δ) (by positivity)
  have hinterior : interior (imStrip (2 * δ)) = openImStrip (2 * δ) := by
    refine Subset.antisymm (fun x hx => ?_) (interior_maximal hopen.2.2.1 hopen.2.1)
    have hx' : x ∈ StripSymbols.openStripInterior (2 * δ) :=
      ⟨interior (imStrip (2 * δ)), isOpen_interior, singleton_subset_iff.2 hx, interior_subset⟩
    rwa [hopen.1] at hx'
  have hsubO : imStrip δ ⊆ openImStrip (2 * δ) :=
    hopen.2.2.2 δ hδ (by linarith)
  obtain ⟨-, O, -, -, a, -, hexp⟩ := hInt F I hF hI T hT δ hδ hinv
  refine ⟨⟨fun δ' hδ' hle => (hwidth δ' hδ').2
      ⟨fun κ hκ => hs.1 κ (imStrip_mono (by linarith) hκ), fun e => ?_⟩, ?_⟩,
    ?_, hreal, ⟨hinv, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨C, hC⟩ := hs.2 e
    exact ⟨C, fun x hx => hC x (imStrip_mono (by linarith) hx)⟩
  · obtain ⟨δPlus, hlt, hsP⟩ := exists_larger_invertible_width hI hfacts hInv hδ hs
    exact ⟨δPlus, hlt, (hwidth δPlus (hδ.trans hlt)).2 hsP⟩
  · intro p _ εPlus εMinus δ₁ δ₂ S₁ S₂ w₁ hp₁ j₁ e₁ w₂ hp₂ j₂ e₂
    have key : ∀ (δ' : ℝ) (S : JetQuad I I), HasInvertibleJetsAtWidth F I T δ' →
        p ∈ imStrip δ' → IsJet δ' p S → EqAsJet δ' p S (jetAlong F I I T p εPlus εMinus) →
        logNumber p (jetAlong F I I T p εPlus εMinus) = logNumber p S := by
      intro δ' S w hp' hS he
      have hj := hfacts.isJet δ' w.1 p hp' εPlus εMinus
      exact ((hArgs.2.2 δ' p I hI _ S hj hS
        ⟨he.1.symm, he.2.1.symm, he.2.2.1.symm, he.2.2.2.symm⟩).2 (w.2 p hp' εPlus εMinus)).2.2.2
    exact (key δ₁ S₁ w₁ hp₁ j₁ e₁).symm.trans (key δ₂ S₂ w₂ hp₂ j₂ e₂)
  · intro p hp
    refine ⟨LinearMap.mk₂ ℂ (fun ε ε' => ∑ c, ∑ c', a c c' p * ε c * ε' c') ?_ ?_ ?_ ?_,
      fun ε ε' => ?_⟩
    · intro ε₁ ε₂ ε'
      simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
    · intro z ε ε'
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
      ring
    · intro ε ε₁ ε₂
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    · intro z ε ε'
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
      ring
    · have e := hexp p hp ε ε'
      simp only [tsum_fintype] at e
      simpa [logDetForm] using e
  · intro c c'
    obtain ⟨g, hg, hv⟩ := hcoef c c'
    exact ⟨_, isOpen_openImStrip _, hsubO, g, hg, hv⟩
  · rw [hinterior]
    exact hsubO
  · intro c c'
    obtain ⟨g, hg, hv⟩ := hcoef c c'
    exact ⟨g, hinterior ▸ hg, hv⟩
  · obtain ⟨δ₀, -, -, ⟨s₀, C, c, hC, hc, hall⟩, -, -⟩ := hLog F I hF hI T hT hreal
    refine ⟨max s₀ 1, C, c, by positivity, hC, hc, fun s hs' => ?_⟩
    have hs₀ := hall s (le_trans (le_max_left _ _) hs')
    exact ⟨hs₀.1, fun N e => ⟨(hs₀.2 N e).1, (hs₀.2 N e).2.2⟩⟩
end YangMills.Construction.PeriodicOperators.InvertibleJetWidths
end
