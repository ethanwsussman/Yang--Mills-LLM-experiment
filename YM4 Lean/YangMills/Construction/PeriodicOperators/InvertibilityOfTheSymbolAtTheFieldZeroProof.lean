import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.InvertibilityOfTheSymbolAtTheFieldZero
import YangMills.Construction.PeriodicOperators.KernelsOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.WaveSpacesOnATorus
import Mathlib
set_option autoImplicit false
open Filter Topology Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.ZeroFieldInvertibility
open JetQuad (IsInvertibleJet IsJet)
open RiemannSums (DualClasses)
section LinearMaps
variable {ι : Type} [Fintype ι]
open Classical in
theorem linearMapEntry_linearMapOfEntries (K : ι → ι → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by
  have hex : ∃ M : (ι → ℂ) →ₗ[ℂ] (ι → ℂ), linearMapEntry M = K := by
    refine ⟨Matrix.toLin' (Matrix.of K), ?_⟩
    funext i j
    simp [linearMapEntry, Matrix.toLin'_apply]
  exact Classical.epsilon_spec hex
open Classical in
theorem toMatrix'_eq_of_linearMapEntry (M : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) :
    LinearMap.toMatrix' M = Matrix.of (linearMapEntry M) := by
  ext i j
  simp only [LinearMap.toMatrix'_apply, linearMapEntry, Matrix.of_apply]
open Classical in
theorem isUnit_iff_isUnit_det_toMatrix' (M : Module.End ℂ (ι → ℂ)) :
    IsUnit M ↔ IsUnit (LinearMap.toMatrix' M).det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  exact (MulEquiv.isUnit_map (LinearMap.toMatrixAlgEquiv' (R := ℂ) (n := ι)).toMulEquiv).symm
open Classical in
theorem isUnit_iff_det_linearMapEntry_ne_zero (M : Module.End ℂ (ι → ℂ)) :
    IsUnit M ↔ (Matrix.of (linearMapEntry M)).det ≠ 0 := by
  rw [isUnit_iff_isUnit_det_toMatrix', toMatrix'_eq_of_linearMapEntry, isUnit_iff_ne_zero]
open Classical in
theorem isUnit_linearMapOfEntries_iff (K : ι → ι → ℂ) :
    IsUnit (linearMapOfEntries K : Module.End ℂ (ι → ℂ)) ↔ (Matrix.of K).det ≠ 0 := by
  rw [isUnit_iff_det_linearMapEntry_ne_zero, linearMapEntry_linearMapOfEntries]
open Classical in
theorem toMatrix'_ringInverse (M : Module.End ℂ (ι → ℂ)) :
    LinearMap.toMatrix' (Ring.inverse M) = (LinearMap.toMatrix' M)⁻¹ := by
  by_cases hunit : IsUnit M
  · symm
    apply Matrix.inv_eq_left_inv
    rw [← LinearMap.toMatrix'_comp]
    have hcomp : (Ring.inverse M).comp M = LinearMap.id := Ring.inverse_mul_cancel M hunit
    rw [hcomp, LinearMap.toMatrix'_id]
  · rw [Ring.inverse_non_unit M hunit,
      Matrix.nonsing_inv_apply_not_isUnit _
        (fun hdet => hunit ((isUnit_iff_isUnit_det_toMatrix' M).2 hdet))]
    simp
open Classical in
theorem linearMapEntry_ringInverse (M : Module.End ℂ (ι → ℂ)) (i j : ι) :
    linearMapEntry (Ring.inverse M) i j =
      ((Matrix.of (linearMapEntry M)).det)⁻¹ * (Matrix.of (linearMapEntry M)).adjugate i j := by
  have hij := congrFun (congrFun (toMatrix'_ringInverse M) i) j
  rw [toMatrix'_eq_of_linearMapEntry, toMatrix'_eq_of_linearMapEntry, Matrix.inv_def] at hij
  simpa [Ring.inverse_eq_inv] using hij
end LinearMaps
section SeparateHolomorphy
def SepHolomorphicOn (U : Set (Fin 4 → ℂ)) (f : (Fin 4 → ℂ) → ℂ) : Prop :=
  ContinuousOn f U ∧ ∀ z ∈ U, ∀ k : Fin 4, ∀ᶠ w in 𝓝 (0 : ℂ),
    DifferentiableAt ℂ
      (fun w : ℂ => f (z + w • Coordinates.ComplexCoordinates.stdBasisVector k)) w
variable {U : Set (Fin 4 → ℂ)}
theorem sepHolomorphicOn_of_isHolomorphicIn {f : (Fin 4 → ℂ) → ℂ}
    (hf : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U fun z _ => f z) :
    SepHolomorphicOn U f :=
  ⟨continuousOn_pi.1 hf.2.1 0, fun z hz k =>
    (hf.2.2 z hz k).mono fun _ hw => differentiableAt_pi.1 hw 0⟩
theorem SepHolomorphicOn.isHolomorphicIn {f : (Fin 4 → ℂ) → ℂ} (hU : IsOpen U)
    (hf : SepHolomorphicOn U f) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U fun z _ => f z :=
  ⟨hU, continuousOn_pi.2 fun _ => hf.1, fun z hz k =>
    (hf.2 z hz k).mono fun _ hw => differentiableAt_pi.2 fun _ => hw⟩
theorem SepHolomorphicOn.mono {V : Set (Fin 4 → ℂ)} {f : (Fin 4 → ℂ) → ℂ}
    (hf : SepHolomorphicOn U f) (hVU : V ⊆ U) : SepHolomorphicOn V f :=
  ⟨hf.1.mono hVU, fun z hz => hf.2 z (hVU hz)⟩
theorem sepHolomorphicOn_const (c : ℂ) : SepHolomorphicOn U fun _ => c :=
  ⟨continuousOn_const, fun _ _ _ => Eventually.of_forall fun _ => differentiableAt_const _⟩
theorem SepHolomorphicOn.add {f g : (Fin 4 → ℂ) → ℂ} (hf : SepHolomorphicOn U f)
    (hg : SepHolomorphicOn U g) : SepHolomorphicOn U fun z => f z + g z :=
  ⟨hf.1.add hg.1, fun z hz k => by
    filter_upwards [hf.2 z hz k, hg.2 z hz k] with w df dg using df.add dg⟩
theorem SepHolomorphicOn.mul {f g : (Fin 4 → ℂ) → ℂ} (hf : SepHolomorphicOn U f)
    (hg : SepHolomorphicOn U g) : SepHolomorphicOn U fun z => f z * g z :=
  ⟨hf.1.mul hg.1, fun z hz k => by
    filter_upwards [hf.2 z hz k, hg.2 z hz k] with w df dg using df.mul dg⟩
theorem sepHolomorphicOn_sum {α : Type} (s : Finset α) (f : α → (Fin 4 → ℂ) → ℂ)
    (hf : ∀ a ∈ s, SepHolomorphicOn U (f a)) : SepHolomorphicOn U fun z => ∑ a ∈ s, f a z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sepHolomorphicOn_const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))
theorem sepHolomorphicOn_prod {α : Type} (s : Finset α) (f : α → (Fin 4 → ℂ) → ℂ)
    (hf : ∀ a ∈ s, SepHolomorphicOn U (f a)) : SepHolomorphicOn U fun z => ∏ a ∈ s, f a z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sepHolomorphicOn_const 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))
theorem SepHolomorphicOn.inv {f : (Fin 4 → ℂ) → ℂ} (hU : IsOpen U) (hf : SepHolomorphicOn U f)
    (hne : ∀ z ∈ U, f z ≠ 0) : SepHolomorphicOn U fun z => (f z)⁻¹ := by
  refine ⟨hf.1.inv₀ hne, fun z hz k => ?_⟩
  have hlim : Tendsto
      (fun w : ℂ => z + w • Coordinates.ComplexCoordinates.stdBasisVector k) (𝓝 0) (𝓝 z) := by
    have hcont : Continuous
        fun w : ℂ => z + w • Coordinates.ComplexCoordinates.stdBasisVector k := by fun_prop
    simpa using hcont.tendsto 0
  filter_upwards [hf.2 z hz k, hlim (hU.mem_nhds hz)] with w dw hw
  exact dw.inv (hne _ hw)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem sepHolomorphicOn_det (A : (Fin 4 → ℂ) → Matrix ι ι ℂ)
    (hA : ∀ i j, SepHolomorphicOn U fun z => A z i j) :
    SepHolomorphicOn U fun z => (A z).det := by
  simp only [Matrix.det_apply']
  exact sepHolomorphicOn_sum _ _ fun σ _ => (sepHolomorphicOn_const _).mul
    (sepHolomorphicOn_prod _ _ fun i _ => hA _ _)
theorem sepHolomorphicOn_adjugate (A : (Fin 4 → ℂ) → Matrix ι ι ℂ)
    (hA : ∀ i j, SepHolomorphicOn U fun z => A z i j) (i' j' : ι) :
    SepHolomorphicOn U fun z => (A z).adjugate i' j' := by
  simp only [Matrix.adjugate_apply]
  refine sepHolomorphicOn_det (fun z => (A z).updateRow j' (Pi.single i' 1)) fun i j => ?_
  by_cases hi : i = j'
  · simpa [Matrix.updateRow_apply, hi] using sepHolomorphicOn_const _
  · simpa [Matrix.updateRow_apply, hi] using hA i j
end SeparateHolomorphy
section RealBox
theorem re_add_two_pi_mul_int (w : ℂ) (n : ℤ) :
    (w + 2 * Real.pi * (n : ℂ)).re = w.re + 2 * Real.pi * (n : ℝ) := by
  have hcast : (2 * (Real.pi : ℂ) * (n : ℂ)) = ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.add_re, Complex.ofReal_re]
theorem im_add_two_pi_mul_int (w : ℂ) (n : ℤ) : (w + 2 * Real.pi * (n : ℂ)).im = w.im := by
  have hcast : (2 * (Real.pi : ℂ) * (n : ℂ)) = ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.add_im, Complex.ofReal_im, add_zero]
theorem exists_abs_re_addTwoPiInt_le (z : Fin 4 → ℂ) :
    ∃ n : Fin 4 → ℤ, ∀ k, |(addTwoPiInt z n k).re| ≤ Real.pi := by
  have hpos : 0 < 2 * Real.pi := by positivity
  refine ⟨fun k => -round ((z k).re / (2 * Real.pi)), fun k => ?_⟩
  show |(z k + 2 * Real.pi * ((-round ((z k).re / (2 * Real.pi)) : ℤ) : ℂ)).re| ≤ Real.pi
  rw [re_add_two_pi_mul_int]
  have hround := abs_sub_round ((z k).re / (2 * Real.pi))
  have hform : (z k).re + 2 * Real.pi * ((-round ((z k).re / (2 * Real.pi)) : ℤ) : ℝ) =
      2 * Real.pi * ((z k).re / (2 * Real.pi) - round ((z k).re / (2 * Real.pi))) := by
    push_cast
    field_simp
    ring
  rw [hform, abs_mul, abs_of_pos hpos]
  nlinarith [Real.pi_pos]
def realBox : Set (Fin 4 → ℂ) :=
  (fun x : Fin 4 → ℝ => fun k => ((x k : ℝ) : ℂ)) ''
    Set.Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi)
theorem isCompact_realBox : IsCompact realBox :=
  isCompact_Icc.image (continuous_pi fun k => Complex.continuous_ofReal.comp (continuous_apply k))
theorem isUnit_inverse_mul_mul {R : Type} [Ring R] {u x : R} (hu : IsUnit u) (hx : IsUnit x) :
    IsUnit (Ring.inverse u * (x * u)) := by
  obtain ⟨u, rfl⟩ := hu
  rw [Ring.inverse_unit]
  exact u⁻¹.isUnit.mul (hx.mul u.isUnit)
theorem inverse_inverse_mul_mul {R : Type} [Ring R] {u x : R} (hu : IsUnit u) (hx : IsUnit x) :
    Ring.inverse (Ring.inverse u * (x * u)) = Ring.inverse u * (Ring.inverse x * u) := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.ringInverse_inverse_mul_mul <;> assumption
end RealBox
section ImStrip
variable {P : PeriodicData}
theorem exists_isUnit_on_imStrip [Finite P.UnitQuot] {A : (Fin 4 → ℂ) → QuotHom P P}
    (hA : IsHolomorphicNbhd (imStrip 2) A) (hper : IsQuasiPeriodic univ A)
    (hphase : ∀ n, IsUnit (phaseMul P n : Module.End ℂ (P.UnitQuot → ℂ)))
    (hreal : ∀ x : InfiniteLattice.AmbientSpace,
      IsUnit (A (toComplexVec x) : Module.End ℂ (P.UnitQuot → ℂ))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ imStrip (2 * δ), IsUnit (A z : Module.End ℂ (P.UnitQuot → ℂ)) := by
  classical
  have := Fintype.ofFinite P.UnitQuot
  obtain ⟨U, hU, hSU, hent⟩ := hA
  have hsep : ∀ i j, SepHolomorphicOn U fun z => Matrix.of (linearMapEntry (A z)) i j :=
    fun i j => sepHolomorphicOn_of_isHolomorphicIn (hent i j)
  have hdet := sepHolomorphicOn_det (fun z => Matrix.of (linearMapEntry (A z))) hsep
  have hopen : IsOpen (U ∩ (fun z => (Matrix.of (linearMapEntry (A z))).det) ⁻¹' {0}ᶜ) :=
    hdet.1.isOpen_inter_preimage hU isOpen_compl_singleton
  have hbox : realBox ⊆ U ∩ (fun z => (Matrix.of (linearMapEntry (A z))).det) ⁻¹' {0}ᶜ := by
    rintro _ ⟨x, -, rfl⟩
    refine ⟨hSU fun k => ?_, ?_⟩
    · simp
    · exact (isUnit_iff_det_linearMapEntry_ne_zero _).1 (hreal x)
  obtain ⟨r, hr, hthick⟩ := isCompact_realBox.exists_thickening_subset_open hopen hbox
  refine ⟨r / 4, by positivity, fun z hz => ?_⟩
  obtain ⟨n, hn⟩ := exists_abs_re_addTwoPiInt_le z
  have him : ∀ k, (addTwoPiInt z n k).im = (z k).im := fun k => im_add_two_pi_mul_int _ _
  have hmem : addTwoPiInt z n ∈ Metric.thickening r realBox := by
    rw [Metric.mem_thickening_iff]
    refine ⟨fun k => (((addTwoPiInt z n k).re : ℝ) : ℂ),
      ⟨fun k => (addTwoPiInt z n k).re,
        ⟨fun k => (abs_le.1 (hn k)).1, fun k => (abs_le.1 (hn k)).2⟩, rfl⟩,
      (dist_pi_lt_iff hr).2 fun k => ?_⟩
    rw [Complex.dist_of_re_eq (by simp), Real.dist_eq, Complex.ofReal_im, sub_zero, him]
    have := hz k
    linarith
  have hunit : IsUnit (A (addTwoPiInt z n) : Module.End ℂ (P.UnitQuot → ℂ)) :=
    (isUnit_iff_det_linearMapEntry_ne_zero _).2 (hthick hmem).2
  have hret : addTwoPiInt (addTwoPiInt z n) (-n) = z := by
    ext k
    simp [addTwoPiInt]
  have hshift := hper (-n) _ (mem_univ (addTwoPiInt z n))
  rw [hret] at hshift
  rw [hshift]
  exact isUnit_inverse_mul_mul (hphase (-n)) hunit
theorem isHolomorphicNbhd_quotHomInverse {A : (Fin 4 → ℂ) → QuotHom P P} [Finite P.UnitQuot]
    {D : Set (Fin 4 → ℂ)} (hA : IsHolomorphicNbhd D A)
    (hunit : ∀ z ∈ D, IsUnit (A z : Module.End ℂ (P.UnitQuot → ℂ))) :
    IsHolomorphicNbhd D fun z => quotHomInverse (A z) := by
  classical
  have := Fintype.ofFinite P.UnitQuot
  obtain ⟨U, hU, hDU, hent⟩ := hA
  have hsep : ∀ i j, SepHolomorphicOn U fun z => Matrix.of (linearMapEntry (A z)) i j :=
    fun i j => sepHolomorphicOn_of_isHolomorphicIn (hent i j)
  have hdet := sepHolomorphicOn_det (fun z => Matrix.of (linearMapEntry (A z))) hsep
  have hopen : IsOpen (U ∩ (fun z => (Matrix.of (linearMapEntry (A z))).det) ⁻¹' {0}ᶜ) :=
    hdet.1.isOpen_inter_preimage hU isOpen_compl_singleton
  refine ⟨_, hopen, fun z hz => ⟨hDU hz, ?_⟩, fun i j => ?_⟩
  · exact (isUnit_iff_det_linearMapEntry_ne_zero _).1 (hunit z hz)
  · have hsub : U ∩ (fun z => (Matrix.of (linearMapEntry (A z))).det) ⁻¹' {0}ᶜ ⊆ U :=
      inter_subset_left
    have hf := ((hdet.mono hsub).inv hopen fun z hz => hz.2).mul
      ((sepHolomorphicOn_adjugate (fun z => Matrix.of (linearMapEntry (A z))) hsep i j).mono hsub)
    have := hf.isHolomorphicIn hopen
    simpa only [quotHomInverse, linearMapEntry_ringInverse] using this
theorem isHolomorphicNbhd_const (D : Set (Fin 4 → ℂ)) (M : QuotHom P P) :
    IsHolomorphicNbhd D fun _ => M :=
  ⟨univ, isOpen_univ, subset_univ _, fun _ _ =>
    ⟨isOpen_univ, continuousOn_const, fun _ _ _ =>
      Eventually.of_forall fun _ => differentiableAt_const _⟩⟩
theorem isQuasiPeriodic_zero (D : Set (Fin 4 → ℂ)) :
    IsQuasiPeriodic D (0 : (Fin 4 → ℂ) → QuotHom P P) := by
  intro n z _
  simp
theorem isJet_of_fst {δ : ℝ} {p : Fin 4 → ℂ} (hδ : 0 < δ) (hp : p ∈ imStrip δ)
    {A : (Fin 4 → ℂ) → QuotHom P P} (hA : IsHolomorphicNbhd (imStrip (2 * δ)) A)
    (hper : IsQuasiPeriodic (imStrip (2 * δ)) A) : IsJet δ p (⟨A, 0, 0, 0⟩ : JetQuad P P) :=
  { pos_width := hδ
    mem_imStrip := hp
    holo_f00 := hA
    holo_f10 := isHolomorphicNbhd_const _ 0
    holo_f01 := isHolomorphicNbhd_const _ 0
    holo_f11 := isHolomorphicNbhd_const _ 0
    quasiPeriodic_f00 := hper
    quasiPeriodic_f10 := isQuasiPeriodic_zero _
    quasiPeriodic_f01 := isQuasiPeriodic_zero _
    quasiPeriodic_f11 := isQuasiPeriodic_zero _ }
end ImStrip
theorem claim_holds (hL : JetDomains.OpFunJetTheory)
    (hK : OpFunKernels.Claim)
    (hQ : Quotients.QuotientTransposeNorm)
    (hS : Symbols.Claim)
    (hB : BlochDecomposition.Claim) : Claim := by
  intro F P hF hP T hT hreal
  have hfacts := hL.2.1 F P P hF hP hP T hT
  have hop := (hK F P P hF hP hP T hT).1
  have hdecay := hop.decays 1 one_pos
  have hsym := hS.1 P P P hP hP hP _ _ 1 hop.periodic hdecay hop.periodic hdecay
  have := hP.finite_quot
  have hphase : ∀ n, IsUnit (phaseMul P n : Module.End ℂ (P.UnitQuot → ℂ)) := fun n =>
    (hsym.quotSymbol_addTwoPiInt 0 n (hop.summable 0 (mem_univ _))).2.1
  have h0 : (0 : Fin 4 → ℂ) ∈ imStrip 1 := fun k => by simp
  have hjet1 := hfacts.isJet 1 one_pos 0 h0 0 0
  have hhol : IsHolomorphicNbhd (imStrip 2) (symbolHom P P (coeffZero F P P T)) := by
    have h := hjet1.holo_f00
    rwa [mul_one] at h
  have hper : IsQuasiPeriodic univ (symbolHom P P (coeffZero F P P T)) :=
    (hfacts.quasiPeriodic 0 0 0).1
  obtain ⟨δ, hδ, hunit⟩ := exists_isUnit_on_imStrip hhol hper hphase hreal
  refine ⟨⟨δ, hδ, fun p hp εp εm => ?_⟩, fun ρ R _ s hs _ => ?_⟩
  · have hjet := hfacts.isJet δ hδ p hp εp εm
    have hinv : IsJet δ p (⟨fun z => quotHomInverse (symbolHom P P (coeffZero F P P T) z),
        0, 0, 0⟩ : JetQuad P P) := by
      refine isJet_of_fst hδ hp (isHolomorphicNbhd_quotHomInverse hjet.holo_f00 hunit)
        fun n z hz => ?_
      have hzn := hper n z (mem_univ _)
      show quotHomInverse (symbolHom P P (coeffZero F P P T) (addTwoPiInt z n)) = _
      rw [hzn]
      exact inverse_inverse_mul_mul (hphase n) (hunit z hz)
    exact ⟨hjet, hunit, ((hL.2.2 P P P hP hP hP δ p hδ hp).sups_finite _ hinv).1⟩
  · classical
    have := (hQ P P hP hP s hs).1.2.1
    have := (hB P hP).dualClasses_finite s hs
    have := Fintype.ofFinite P.UnitQuot
    have := Fintype.ofFinite (P.QuotMod s)
    have := Fintype.ofFinite (DualClasses s)
    have hsec : IsDualSection s fun q => Quotient.out q := fun q => Quotient.out_eq' q
    have hdet := (hS.2 P hP _ 1 hop.periodic hdecay).det_periodicMatrix s hs _ hsec
    have hval : descendMatrix P P s (periodicValue F P P T s 0) =
        periodicMatrix P P (coeffZero F P P T) s := by
      have hz : liftQuotField F s 0 = 0 := rfl
      simp only [periodicValue, periodicMatrix, hz]
      rfl
    rw [hval, isUnit_linearMapOfEntries_iff, hdet]
    exact Finset.prod_ne_zero_iff.2 fun q _ => (isUnit_linearMapOfEntries_iff _).1 (hreal _)
end YangMills.Construction.PeriodicOperators.ZeroFieldInvertibility
end
