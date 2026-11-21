import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import YangMills.Construction.PeriodicOperators.InvertibilityOfTheSymbolAtTheFieldZero
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.MatricesOfALocalOperatorFunctionOnATorus
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.TraceOfAMomentumShift
import YangMills.Construction.PeriodicOperators.TraceOnTheWaveSpacesProof
import YangMills.Construction.PeriodicOperators.TracesOfTheCoefficientsOnPlaneWaves
import YangMills.Construction.PeriodicOperators.TranslationsOfTheSymbolProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.PlaneWaveTraces
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.PeriodicOperators.JetDomains (IsLiftOf)
open YangMills.Construction.PeriodicOperators.LocalTorusMatrices (ActsViaPeriodization)
theorem toComplexVec_add (a b : AmbientSpace) :
    toComplexVec (a + b) = toComplexVec a + toComplexVec b := by apply _root_.YangMills.Construction.PeriodicOperators.CovariantFiniteRangeProof.toComplexVec_add <;> assumption
theorem toComplexVec_sub (a b : AmbientSpace) :
    toComplexVec (a - b) = toComplexVec a - toComplexVec b := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolTranslation.toComplexVec_sub <;> assumption
theorem bilinDot_add_left (a b y : Fin 4 → ℂ) : bilinDot (a + b) y = bilinDot a y + bilinDot b y := by
  simp [bilinDot, add_mul, Finset.sum_add_distrib]
theorem bilinDot_zero_left (y : Fin 4 → ℂ) : bilinDot 0 y = 0 := by
  simp [bilinDot]
theorem bilinDot_translate (p : Fin 4 → ℂ) (x : AmbientSpace) (n : Fin 4 → ℤ) :
    bilinDot p (toComplexVec (x + castVec (-n))) =
      bilinDot p (toComplexVec x) + -bilinDot p (toComplexVec (castVec n)) := by
  simp only [bilinDot, toComplexVec, castVec, Pi.add_apply, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  push_cast
  ring
theorem euclidNormVec_sub_comm (a b : AmbientSpace) : euclidNormVec (a - b) = euclidNormVec (b - a) := by apply _root_.YangMills.SharedProofs.p26380 <;> assumption
theorem mkQuot_translate_neg (F : PeriodicData) (n : Fin 4 → ℤ) (κ : F.Carrier) :
    F.mkQuot 1 (F.translate (-n) κ) = F.mkQuot 1 κ :=
  (Quot.sound ⟨-n, by rw [one_smul]⟩).symm
theorem shiftField_blochWave {F : PeriodicData} (hF : IsPeriodic F) (p : Fin 4 → ℂ)
    (ε : F.UnitQuot → ℂ) (n : Fin 4 → ℤ) :
    shiftField F n (blochWave F p ε) =
      Complex.exp (-(Complex.I * bilinDot p (toComplexVec (castVec n)))) • blochWave F p ε := by
  funext κ
  simp only [shiftField, blochWave, Pi.smul_apply, smul_eq_mul, mkQuot_translate_neg,
    hF.pos_translate, bilinDot_translate, mul_add, Complex.exp_add, mul_neg]
  ring
theorem dephasedKernel_zero (I I' : PeriodicData) (Y : I'.Carrier → I.Carrier → ℂ) :
    dephasedKernel I I' 0 Y = Y := by
  funext ι' ι
  simp [dephasedKernel, bilinDot_zero_left]
theorem eq_of_isLiftOf {I : PeriodicData} {s : ℕ} {g g' : I.QuotMod s → ℂ} {f : I.Carrier → ℂ}
    (h : IsLiftOf I s g f) (h' : IsLiftOf I s g' f) : g = g' := by apply _root_.YangMills.Construction.PeriodicOperators.WaveSpaceTrace.eq_of_isLiftOf <;> assumption
theorem isLiftOf_of_acts {I : PeriodicData} {s : ℕ} [Finite (I.QuotMod s)]
    {Y : I.Carrier → I.Carrier → ℂ} {q κ : Fin 4 → ℂ} {φ : I.UnitQuot → ℂ} {g : I.QuotMod s → ℂ}
    (hAct : ActsViaPeriodization I I Y s) (hY : ActsOnBlochWaves I I q Y)
    (hg : IsLiftOf I s g (blochWave I κ φ)) :
    IsLiftOf I s (linearMapOfEntries (descendMatrix I I s (periodization I I Y s)) g)
      (blochWave I (κ + q)
        (applyKernel (quotSymbol I I (dephasedKernel I I q Y) κ) φ)) := by
  intro ι'
  have hf : liftQuotField I s g = blochWave I κ φ := funext hg
  have h := (hAct g).2.2 ι'
  rw [hf] at h
  rw [linearMapOfEntries_eq_applyKernel, ← h]
  exact (hY κ φ ι').2
def MapsWaveSpacesBy (I : PeriodicData) (s : ℕ) (A : Module.End ℂ (I.QuotMod s → ℂ))
    (q : AmbientSpace) : Prop :=
  ∀ κ ∈ dualLattice s, ∀ g ∈ blochWaveSubspace I s κ, A g ∈ blochWaveSubspace I s (κ + q)
theorem MapsWaveSpacesBy.mul {I : PeriodicData} {s : ℕ} {A B : Module.End ℂ (I.QuotMod s → ℂ)}
    {a b c : AmbientSpace} (hA : MapsWaveSpacesBy I s A a) (hB : MapsWaveSpacesBy I s B b)
    (hb : b ∈ dualLattice s) (hc : b + a = c) : MapsWaveSpacesBy I s (A * B) c := by
  intro κ hκ g hg
  have h := hA (κ + b) (add_mem hκ hb) (B g) (hB κ hκ g hg)
  rw [add_assoc, hc] at h
  exact h
structure Hypotheses (F I : PeriodicData) (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ)
    (ρ R : ℝ) (s : ℕ) : Prop where
  periodicF : IsPeriodic F
  periodicI : IsPeriodic I
  isLocal : IsLocalWith F I I T ρ R
  side_pos : 0 < s
  side_large : 4 * R < s
  finite_quot : Finite I.UnitQuot
  finite_torus : Finite (I.QuotMod s)
  taylor : LocalOpFunTaylor.Claim
  covariant : CovariantFiniteRange.Claim
  matrices : LocalTorusMatrices.LocalTorusMatricesClaim
  waves : BlochDecomposition.Claim
abbrev zeroFieldMatrix (F I : PeriodicData) (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ)
    (s : ℕ) : Module.End ℂ (I.QuotMod s → ℂ) :=
  linearMapOfEntries (descendMatrix I I s (periodicValue F I I T s 0))
section Kernels
variable {F I : PeriodicData} {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} {ρ R : ℝ} {s : ℕ}
theorem coeffOne_smul (G : Hypotheses F I T ρ R s) (c : ℂ) (ζ : F.Carrier → ℂ) (ι' ι : I.Carrier) :
    coeffOne F I I T (c • ζ) ι' ι = c * coeffOne F I I T ζ ι' ι := by
  obtain ⟨⟨hfin, -, hfirst, -, -⟩, -⟩ :=
    G.taylor F I I G.periodicF G.periodicI G.periodicI T ρ R G.isLocal ζ ζ ι' ι 0
  have := hfin.to_subtype
  cases nonempty_fintype (nearIndices F (I.pos ι') R)
  rw [hfirst (c • ζ), hfirst ζ]
  simp only [finsum_eq_sum_of_fintype, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun κ _ => by ring
theorem coeffTwo_smul (G : Hypotheses F I T ρ R s) (c d : ℂ) (ζ ζ' : F.Carrier → ℂ)
    (ι' ι : I.Carrier) :
    coeffTwo F I I T (c • ζ) (d • ζ') ι' ι = c * d * coeffTwo F I I T ζ ζ' ι' ι := by
  obtain ⟨⟨hfin, -, -, -, hsecond⟩, -⟩ :=
    G.taylor F I I G.periodicF G.periodicI G.periodicI T ρ R G.isLocal ζ ζ' ι' ι 0
  have := hfin.to_subtype
  cases nonempty_fintype (nearIndices F (I.pos ι') R)
  rw [hsecond.2 (c • ζ) (d • ζ'), hsecond.2 ζ ζ']
  simp only [finsum_eq_sum_of_fintype, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun κ' _ => ?_
  ring
theorem coeffZero_phaseCovariant (G : Hypotheses F I T ρ R s) :
    IsPhaseCovariant I I 0 (coeffZero F I I T) := by
  intro n ι' ι
  obtain ⟨-, -, ⟨h, -⟩, -⟩ :=
    G.taylor F I I G.periodicF G.periodicI G.periodicI T ρ R G.isLocal 0 0 ι' ι n
  rw [h, bilinDot_zero_left]
  simp
theorem coeffOne_phaseCovariant (G : Hypotheses F I T ρ R s) (q : Fin 4 → ℂ) (ε : F.UnitQuot → ℂ) :
    IsPhaseCovariant I I q (coeffOne F I I T (blochWave F q ε)) := by
  intro n ι' ι
  obtain ⟨-, -, ⟨-, -, -, h, -⟩, -⟩ :=
    G.taylor F I I G.periodicF G.periodicI G.periodicI T ρ R G.isLocal (blochWave F q ε) 0 ι' ι n
  rw [shiftField_blochWave G.periodicF, coeffOne_smul G] at h
  rw [← h, ← mul_assoc, ← Complex.exp_add]
  simp
theorem coeffTwo_phaseCovariant (G : Hypotheses F I T ρ R s) (a b : Fin 4 → ℂ)
    (ε ε' : F.UnitQuot → ℂ) :
    IsPhaseCovariant I I (a + b) (coeffTwo F I I T (blochWave F a ε) (blochWave F b ε')) := by
  intro n ι' ι
  obtain ⟨-, -, ⟨-, -, -, -, h⟩, -⟩ :=
    G.taylor F I I G.periodicF G.periodicI G.periodicI T ρ R G.isLocal
      (blochWave F a ε) (blochWave F b ε') ι' ι n
  rw [shiftField_blochWave G.periodicF, shiftField_blochWave G.periodicF, coeffTwo_smul G] at h
  rw [← h, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add, bilinDot_add_left]
  have e : Complex.I * (bilinDot a (toComplexVec (castVec n)) + bilinDot b (toComplexVec (castVec n))) +
      -(Complex.I * bilinDot a (toComplexVec (castVec n))) +
      -(Complex.I * bilinDot b (toComplexVec (castVec n))) = 0 := by ring
  rw [e, Complex.exp_zero, one_mul]
theorem coeffZero_vanishes (G : Hypotheses F I T ρ R s) :
    VanishesOutsideRadius I I R (coeffZero F I I T) := by
  intro ι' ι hd
  obtain ⟨-, ⟨-, h⟩, -⟩ :=
    G.taylor F I I G.periodicF G.periodicI G.periodicI T ρ R G.isLocal 0 0 ι' ι 0
  exact (h (by rwa [euclidNormVec_sub_comm])).1
theorem coeffOne_vanishes (G : Hypotheses F I T ρ R s) (ζ : F.Carrier → ℂ) :
    VanishesOutsideRadius I I R (coeffOne F I I T ζ) := by
  intro ι' ι hd
  obtain ⟨-, ⟨-, h⟩, -⟩ :=
    G.taylor F I I G.periodicF G.periodicI G.periodicI T ρ R G.isLocal ζ ζ ι' ι 0
  exact (h (by rwa [euclidNormVec_sub_comm])).2.1
theorem coeffTwo_vanishes (G : Hypotheses F I T ρ R s) (ζ ζ' : F.Carrier → ℂ) :
    VanishesOutsideRadius I I R (coeffTwo F I I T ζ ζ') := by
  intro ι' ι hd
  obtain ⟨-, ⟨-, h⟩, -⟩ :=
    G.taylor F I I G.periodicF G.periodicI G.periodicI T ρ R G.isLocal ζ ζ' ι' ι 0
  exact (h (by rwa [euclidNormVec_sub_comm])).2.2
theorem zeroFieldMatrix_isLiftOf (G : Hypotheses F I T ρ R s) (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ)
    (g : I.QuotMod s → ℂ) (hg : IsLiftOf I s g (blochWave I κ φ)) :
    IsLiftOf I s (zeroFieldMatrix F I T s g)
      (blochWave I κ (symbolHom I I (coeffZero F I I T) κ φ)) := by
  have := G.finite_quot
  have := G.finite_torus
  have hact := ((G.matrices F I I G.periodicF G.periodicI G.periodicI T ρ R G.isLocal s G.side_pos
    G.side_large).1 0 0 (coeffZero F I I T) (Or.inr (Or.inl rfl))).2
  have hY := (G.covariant.2 I I G.periodicI G.periodicI 0 R _ (coeffZero_phaseCovariant G)
    (coeffZero_vanishes G)).2.2.2
  have h := isLiftOf_of_acts hact hY hg
  rw [add_zero, dephasedKernel_zero] at h
  have e : applyKernel (quotSymbol I I (coeffZero F I I T) κ) φ =
      symbolHom I I (coeffZero F I I T) κ φ := (linearMapOfEntries_eq_applyKernel _ _).symm
  rw [e] at h
  exact h
theorem zeroFieldMatrix_mapsWaveSpaces (G : Hypotheses F I T ρ R s) :
    MapsWaveSpacesBy I s (zeroFieldMatrix F I T s) 0 := by
  rintro κ - g ⟨φ, hφ⟩
  rw [add_zero]
  exact ⟨_, zeroFieldMatrix_isLiftOf G _ φ g hφ⟩
theorem inverse_mapsWaveSpaces (G : Hypotheses F I T ρ R s)
    (hU : IsUnit (zeroFieldMatrix F I T s)) :
    MapsWaveSpacesBy I s (Ring.inverse (zeroFieldMatrix F I T s)) 0 := by
  have := G.finite_torus
  intro κ hκ g hg
  rw [add_zero]
  have hmaps : Set.MapsTo (zeroFieldMatrix F I T s) (blochWaveSubspace I s κ)
      (blochWaveSubspace I s κ) := by
    intro h hh
    have := zeroFieldMatrix_mapsWaveSpaces G κ hκ h hh
    rwa [add_zero] at this
  have hinj : Function.Injective ((zeroFieldMatrix F I T s).restrict hmaps) := by
    intro x y e
    exact Subtype.ext (((Module.End.isUnit_iff _).1 hU).1 (congrArg Subtype.val e))
  obtain ⟨⟨h, hh⟩, e⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨g, hg⟩
  have e' : zeroFieldMatrix F I T s h = g := congrArg Subtype.val e
  have e'' : Ring.inverse (zeroFieldMatrix F I T s) g = h := by
    rw [← e']
    exact LinearMap.congr_fun (Ring.inverse_mul_cancel _ hU) h
  rw [e'']
  exact hh
theorem coeffOneMatrix_mapsWaveSpaces (G : Hypotheses F I T ρ R s) {p : AmbientSpace}
    {ε : F.UnitQuot → ℂ} {ζ : F.QuotMod s → ℂ}
    (hζ : IsLiftOf F s ζ (blochWave F (toComplexVec p) ε)) :
    MapsWaveSpacesBy I s (periodicCoeffOneMatrix F I T s ζ) p := by
  have := G.finite_torus
  rintro κ - g ⟨φ, hφ⟩
  have hf : liftQuotField F s ζ = blochWave F (toComplexVec p) ε := funext hζ
  have hact := ((G.matrices F I I G.periodicF G.periodicI G.periodicI T ρ R G.isLocal s G.side_pos
    G.side_large).1 ζ ζ (coeffOne F I I T (liftQuotField F s ζ)) (Or.inr (Or.inr (Or.inl rfl)))).2
  have hY := (G.covariant.2 I I G.periodicI G.periodicI (toComplexVec p) R
    (coeffOne F I I T (liftQuotField F s ζ))
    (by rw [hf]; exact coeffOne_phaseCovariant G _ ε) (coeffOne_vanishes G _)).2.2.2
  have h := isLiftOf_of_acts hact hY hφ
  rw [← toComplexVec_add] at h
  exact ⟨_, h⟩
theorem coeffTwoMatrix_mapsWaveSpaces (G : Hypotheses F I T ρ R s) {p p' : AmbientSpace}
    {ε ε' : F.UnitQuot → ℂ} {ζ ζ' : F.QuotMod s → ℂ}
    (hζ : IsLiftOf F s ζ (blochWave F (toComplexVec p) ε))
    (hζ' : IsLiftOf F s ζ' (blochWave F (toComplexVec p') ε')) :
    MapsWaveSpacesBy I s (periodicCoeffTwoMatrix F I T s ζ ζ') (p + p') := by
  have := G.finite_torus
  rintro κ - g ⟨φ, hφ⟩
  have hf : liftQuotField F s ζ = blochWave F (toComplexVec p) ε := funext hζ
  have hf' : liftQuotField F s ζ' = blochWave F (toComplexVec p') ε' := funext hζ'
  have hact := ((G.matrices F I I G.periodicF G.periodicI G.periodicI T ρ R G.isLocal s G.side_pos
    G.side_large).1 ζ ζ' (coeffTwo F I I T (liftQuotField F s ζ) (liftQuotField F s ζ'))
    (Or.inr (Or.inr (Or.inr rfl)))).2
  have hY := (G.covariant.2 I I G.periodicI G.periodicI (toComplexVec p + toComplexVec p') R
    (coeffTwo F I I T (liftQuotField F s ζ) (liftQuotField F s ζ'))
    (by rw [hf, hf']; exact coeffTwo_phaseCovariant G _ _ ε ε') (coeffTwo_vanishes G _ _)).2.2.2
  have h := isLiftOf_of_acts hact hY hφ
  rw [← toComplexVec_add, ← toComplexVec_add] at h
  exact ⟨_, h⟩
theorem inverse_isLiftOf (G : Hypotheses F I T ρ R s) (hU : IsUnit (zeroFieldMatrix F I T s))
    (hsym : ∀ κ : AmbientSpace, IsUnit (symbolHom I I (coeffZero F I I T) (toComplexVec κ) :
      Module.End ℂ (I.UnitQuot → ℂ)))
    {κ : AmbientSpace} (hκ : κ ∈ dualLattice s) {ψ : I.UnitQuot → ℂ} {g : I.QuotMod s → ℂ}
    (hg : IsLiftOf I s g (blochWave I (toComplexVec κ) ψ)) :
    IsLiftOf I s (Ring.inverse (zeroFieldMatrix F I T s) g)
      (blochWave I (toComplexVec κ)
        (quotHomInverse (symbolHom I I (coeffZero F I I T) (toComplexVec κ)) ψ)) := by
  obtain ⟨h, hh⟩ := (G.waves I G.periodicI).blochWave_descends s G.side_pos κ hκ
    (quotHomInverse (symbolHom I I (coeffZero F I I T) (toComplexVec κ)) ψ)
  have e₁ : symbolHom I I (coeffZero F I I T) (toComplexVec κ)
      (quotHomInverse (symbolHom I I (coeffZero F I I T) (toComplexVec κ)) ψ) = ψ :=
    LinearMap.congr_fun (Ring.mul_inverse_cancel _ (hsym κ)) ψ
  have h₀ := zeroFieldMatrix_isLiftOf G _ _ h hh
  rw [e₁] at h₀
  have e₂ : zeroFieldMatrix F I T s h = g := eq_of_isLiftOf h₀ hg
  have e₃ : Ring.inverse (zeroFieldMatrix F I T s) g = h := by
    rw [← e₂]
    exact LinearMap.congr_fun (Ring.inverse_mul_cancel _ hU) h
  rw [e₃]
  exact hh
end Kernels
def loopIntegrand (F I : PeriodicData) (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ)
    (p : Fin 4 → ℂ) (εPlus εMinus : F.UnitQuot → ℂ) (κ : Fin 4 → ℂ) :
    Module.End ℂ (I.UnitQuot → ℂ) :=
  (quotHomInverse ((jetAlong F I I T p εPlus εMinus).f00 κ)).comp
      ((jetAlong F I I T p εPlus εMinus).f11 κ) -
    (quotHomInverse ((jetAlong F I I T p εPlus εMinus).f00 κ)).comp
      (((jetAlong F I I T p εPlus εMinus).f10 (κ - p)).comp
        ((quotHomInverse ((jetAlong F I I T p εPlus εMinus).f00 (κ - p))).comp
          ((jetAlong F I I T p εPlus εMinus).f01 κ)))
theorem claim_holds (hLocal : JetDomains.OpFunJetTheory)
    (hMatrices : LocalTorusMatrices.LocalTorusMatricesClaim)
    (hTaylor : LocalOpFunTaylor.Claim)
    (hCov : CovariantFiniteRange.Claim)
    (hQuotients : Quotients.QuotientTransposeNorm)
    (hWaves : BlochDecomposition.Claim)
    (hShift : ShiftTrace.TraceVanishes)
    (hInvertible : ZeroFieldInvertibility.Claim)
    (hWaveTrace : WaveSpaceTrace.Claim) : Claim := by
  intro F I hF hI T ρ R hR hsym s hs hsR
  obtain ⟨hC, hCs, -⟩ := (hQuotients I I hI hI s hs).1
  have G : Hypotheses F I T ρ R s :=
    ⟨hF, hI, hR, hs, hsR, hC, hCs, hTaylor, hCov, hMatrices, hWaves⟩
  have hU : IsUnit (zeroFieldMatrix F I T s) :=
    (hInvertible F I hF hI T ⟨ρ, R, hR⟩ hsym).2 ρ R hR s hs hsR
  have hB := inverse_mapsWaveSpaces G hU
  refine ⟨?_, ?_⟩
  · intro p hp p' hp' hpp ε ε' ζ ζ' hζ hζ'
    have hq := add_mem hp hp'
    refine ⟨hShift I hI s hs (p + p') hq hpp _ ?_, hShift I hI s hs (p + p') hq hpp _ ?_⟩
    · exact MapsWaveSpacesBy.mul hB (coeffTwoMatrix_mapsWaveSpaces G hζ hζ') hq (by simp)
    · exact MapsWaveSpacesBy.mul
        (MapsWaveSpacesBy.mul (MapsWaveSpacesBy.mul hB (coeffOneMatrix_mapsWaveSpaces G hζ) hp
          (add_zero p)) hB (zero_mem _) (zero_add p))
        (coeffOneMatrix_mapsWaveSpaces G hζ') hp' (add_comm _ _)
  · intro p hp εPlus εMinus ζPlus ζMinus hPlus hMinus
    rw [← map_sub]
    have hrel := fun (κ : AmbientSpace) (hκ : κ ∈ dualLattice s) (φ : I.UnitQuot → ℂ)
        (g : I.QuotMod s → ℂ) (hg : IsLiftOf I s g (blochWave I (toComplexVec κ) φ)) =>
      ((hLocal.2.1 F I I hF hI hI T ⟨ρ, R, hR⟩).descends ρ R hR s hs hsR κ hκ p hp
        εPlus εMinus φ).2 ζPlus ζMinus g hPlus hMinus hg
    have rPlus : ∀ κ ∈ dualLattice s, ∀ (φ : I.UnitQuot → ℂ) (g : I.QuotMod s → ℂ),
        IsLiftOf I s g (blochWave I (toComplexVec κ) φ) →
        IsLiftOf I s (periodicCoeffOneMatrix F I T s ζPlus g)
          (blochWave I (toComplexVec κ + toComplexVec p)
            ((jetAlong F I I T (toComplexVec p) εPlus εMinus).f10 (toComplexVec κ) φ)) :=
      fun κ hκ φ g hg ι' =>
        (congrFun (linearMapOfEntries_eq_applyKernel _ g) _).trans (hrel κ hκ φ g hg ι').1
    have rMinus : ∀ κ ∈ dualLattice s, ∀ (φ : I.UnitQuot → ℂ) (g : I.QuotMod s → ℂ),
        IsLiftOf I s g (blochWave I (toComplexVec κ) φ) →
        IsLiftOf I s (periodicCoeffOneMatrix F I T s ζMinus g)
          (blochWave I (toComplexVec κ - toComplexVec p)
            ((jetAlong F I I T (toComplexVec p) εPlus εMinus).f01 (toComplexVec κ) φ)) :=
      fun κ hκ φ g hg ι' =>
        (congrFun (linearMapOfEntries_eq_applyKernel _ g) _).trans (hrel κ hκ φ g hg ι').2.1
    have rBoth : ∀ κ ∈ dualLattice s, ∀ (φ : I.UnitQuot → ℂ) (g : I.QuotMod s → ℂ),
        IsLiftOf I s g (blochWave I (toComplexVec κ) φ) →
        IsLiftOf I s (periodicCoeffTwoMatrix F I T s ζPlus ζMinus g)
          (blochWave I (toComplexVec κ)
            ((jetAlong F I I T (toComplexVec p) εPlus εMinus).f11 (toComplexVec κ) φ)) :=
      fun κ hκ φ g hg ι' =>
        (congrFun (linearMapOfEntries_eq_applyKernel _ g) _).trans (hrel κ hκ φ g hg ι').2.2
    refine (hWaveTrace I hI s hs _
      (loopIntegrand F I T (toComplexVec p) εPlus εMinus) ?_).trans rfl
    intro κ hκ φ g hg
    have t₁ := inverse_isLiftOf G hU hsym hκ (rBoth κ hκ φ g hg)
    have g₁ := rMinus κ hκ φ g hg
    rw [← toComplexVec_sub] at g₁
    have hκ' : κ - p ∈ dualLattice s := sub_mem hκ hp
    have g₂ := inverse_isLiftOf G hU hsym hκ' g₁
    have g₃ := rPlus _ hκ' _ _ g₂
    rw [← toComplexVec_add, sub_add_cancel] at g₃
    have g₄ := inverse_isLiftOf G hU hsym hκ g₃
    rw [toComplexVec_sub] at g₄
    intro ι'
    show Ring.inverse (zeroFieldMatrix F I T s)
          (periodicCoeffTwoMatrix F I T s ζPlus ζMinus g) (I.mkQuot s ι') -
        Ring.inverse (zeroFieldMatrix F I T s)
          (periodicCoeffOneMatrix F I T s ζPlus
            (Ring.inverse (zeroFieldMatrix F I T s)
              (periodicCoeffOneMatrix F I T s ζMinus g))) (I.mkQuot s ι') = _
    rw [t₁ ι', g₄ ι']
    simp only [blochWave, ← mul_sub]
    rfl
end YangMills.Construction.PeriodicOperators.PlaneWaveTraces
end
