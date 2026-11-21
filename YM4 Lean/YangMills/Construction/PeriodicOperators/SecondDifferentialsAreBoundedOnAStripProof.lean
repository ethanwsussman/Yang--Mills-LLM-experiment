import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.PeriodicOperators.MomentaOfTheToriWithASide
import YangMills.Construction.PeriodicOperators.SecondDifferentialsAreBoundedOnAStrip
import YangMills.Construction.PeriodicOperators.SecondDifferentialsOfLogarithmsOfDeterminants
import YangMills.Construction.PeriodicOperators.TranslationsOfTheSymbolProof
import YangMills.Construction.PeriodicOperators.WaveSpacesOnATorusProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators.StripBound
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv
  (IsHolomorphicScalarIn asLine)
open YangMills.Construction.PeriodicOperators.JetQuad (IsInvertibleJet IsJet EqAsJet logNumber)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators.LogDetSecondDerivs (IsCloseToLogNumber)
variable {F I : PeriodicData}
private def indexPhase (F : PeriodicData) (e : Fin 4 → ℤ) (ι : F.Carrier) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I *
    bilinDot (toComplexVec (castVec e)) (toComplexVec (F.pos ι)))
private theorem bilinDot_add_right (κ : Fin 4 → ℂ) (y z : AmbientSpace) :
    bilinDot κ (toComplexVec (y + z)) =
      bilinDot κ (toComplexVec y) + bilinDot κ (toComplexVec z) := by apply _root_.YangMills.Construction.PeriodicOperators.BlochDecomposition.bilinDot_add_right <;> assumption
private theorem bilinDot_addTwoPiInt (κ y : Fin 4 → ℂ) (e : Fin 4 → ℤ) :
    bilinDot (addTwoPiInt κ e) y =
      bilinDot κ y + 2 * Real.pi * bilinDot (toComplexVec (castVec e)) y := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolTranslation.bilinDot_addTwoPiInt <;> assumption
private theorem indexPhase_translate (hF : IsPeriodic F) (e n : Fin 4 → ℤ) (ι : F.Carrier) :
    indexPhase F e (F.translate n ι) = indexPhase F e ι := by
  have hint : bilinDot (toComplexVec (castVec e)) (toComplexVec (castVec n)) =
      ((∑ μ, e μ * n μ : ℤ) : ℂ) := by
    simp [bilinDot, toComplexVec, castVec]
  have hone : Complex.exp (2 * Real.pi * Complex.I * ((∑ μ, e μ * n μ : ℤ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨_, by ring⟩
  unfold indexPhase
  rw [hF.pos_translate, bilinDot_add_right, hint, mul_add, Complex.exp_add, hone, mul_one]
private theorem indexPhase_eq_of_mkQuot_eq (hF : IsPeriodic F) (e : Fin 4 → ℤ)
    {ι ι' : F.Carrier} (h : F.mkQuot 1 ι = F.mkQuot 1 ι') :
    indexPhase F e ι = indexPhase F e ι' := by
  let f : F.UnitQuot → ℂ := Quot.lift (indexPhase F e) (by
    rintro a _ ⟨n, rfl⟩
    exact (indexPhase_translate hF e _ a).symm)
  exact congrArg f h
private theorem phaseOn_mkQuot (hF : IsPeriodic F) (e : Fin 4 → ℤ) (ι : F.Carrier) :
    phaseOn F e (F.mkQuot 1 ι) = indexPhase F e ι := by
  have hex : ∃ z, ∀ ι', F.mkQuot 1 ι' = F.mkQuot 1 ι →
      Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (F.pos ι'))) = z :=
    ⟨indexPhase F e ι, fun ι' h => indexPhase_eq_of_mkQuot_eq hF e h⟩
  exact (Classical.epsilon_spec hex ι rfl).symm
private theorem exists_mkQuot_eq (c : F.UnitQuot) : ∃ ι, F.mkQuot 1 ι = c :=
  Quot.exists_rep c
private theorem norm_phaseOn (hF : IsPeriodic F) (e : Fin 4 → ℤ) (c : F.UnitQuot) :
    ‖phaseOn F e c‖ = 1 := by
  obtain ⟨ι, rfl⟩ := exists_mkQuot_eq c
  rw [phaseOn_mkQuot hF]
  have hdot : ∀ a b : AmbientSpace, bilinDot (toComplexVec a) (toComplexVec b) =
      ((∑ μ, a μ * b μ : ℝ) : ℂ) := fun a b => by
    simp [bilinDot, toComplexVec]
  unfold indexPhase
  rw [hdot]
  have : (2 * Real.pi * Complex.I * ((∑ μ, castVec e μ * F.pos ι μ : ℝ) : ℂ)) =
      (((2 * Real.pi * ∑ μ, castVec e μ * F.pos ι μ : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.norm_exp_ofReal_mul_I]
abbrev _root_.YangMills.SharedProofs.p4911 := @norm_phaseOn
private theorem blochWave_addTwoPiInt (hF : IsPeriodic F) (κ : Fin 4 → ℂ)
    (e : Fin 4 → ℤ) (ε : F.UnitQuot → ℂ) :
    blochWave F (addTwoPiInt κ e) ε = blochWave F κ (phaseMul F e ε) := by
  funext ι
  have hph : phaseMul F e ε (F.mkQuot 1 ι) =
      indexPhase F e ι * ε (F.mkQuot 1 ι) := by
    show phaseOn F e _ * _ = _
    rw [phaseOn_mkQuot hF]
  simp only [blochWave]
  rw [hph, bilinDot_addTwoPiInt, mul_add, Complex.exp_add]
  unfold indexPhase
  have : Complex.I * (2 * Real.pi *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (F.pos ι))) =
      2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (F.pos ι)) := by
    ring
  rw [this]
  ring
abbrev _root_.YangMills.SharedProofs.p35841 := @blochWave_addTwoPiInt
private theorem neg_addTwoPiInt (κ : Fin 4 → ℂ) (e : Fin 4 → ℤ) :
    -addTwoPiInt κ e = addTwoPiInt (-κ) (-e) := by
  funext μ
  simp only [addTwoPiInt, Pi.neg_apply, Int.cast_neg]
  ring
private theorem toComplexVec_add_twoPi_smul (y : AmbientSpace) (e : Fin 4 → ℤ) :
    toComplexVec (y + (2 * Real.pi) • castVec e) = addTwoPiInt (toComplexVec y) e := by
  funext μ
  simp only [toComplexVec, addTwoPiInt, castVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring
private theorem addTwoPiInt_im (κ : Fin 4 → ℂ) (e : Fin 4 → ℤ) (μ : Fin 4) :
    (addTwoPiInt κ e μ).im = (κ μ).im := by
  have : addTwoPiInt κ e μ = κ μ + ((2 * Real.pi * (e μ : ℝ) : ℝ) : ℂ) := by
    simp only [addTwoPiInt]
    push_cast
    ring
  rw [this, Complex.add_im, Complex.ofReal_im, add_zero]
private theorem addTwoPiInt_re (κ : Fin 4 → ℂ) (e : Fin 4 → ℤ) (μ : Fin 4) :
    (addTwoPiInt κ e μ).re = (κ μ).re + 2 * Real.pi * (e μ : ℝ) := by
  have : addTwoPiInt κ e μ = κ μ + ((2 * Real.pi * (e μ : ℝ) : ℝ) : ℂ) := by
    simp only [addTwoPiInt]
    push_cast
    ring
  rw [this, Complex.add_re, Complex.ofReal_re]
private theorem addTwoPiInt_mem_imStrip {δ : ℝ} {κ : Fin 4 → ℂ} (h : κ ∈ imStrip δ)
    (e : Fin 4 → ℤ) : addTwoPiInt κ e ∈ imStrip δ := fun μ => by
  rw [addTwoPiInt_im]
  exact h μ
abbrev _root_.YangMills.SharedProofs.p29809 := @addTwoPiInt_mem_imStrip
private theorem toComplexVec_mem_imStrip {δ : ℝ} (hδ : 0 < δ) (y : AmbientSpace) :
    toComplexVec y ∈ imStrip δ := fun μ => by
  simp only [toComplexVec, Complex.ofReal_im, abs_zero]
  exact hδ.le
private theorem continuous_toComplexVec : Continuous toComplexVec := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.continuous_toComplexVec <;> assumption
private theorem continuous_addTwoPiInt (e : Fin 4 → ℤ) :
    Continuous fun κ : Fin 4 → ℂ => addTwoPiInt κ e :=
  continuous_pi fun μ => (continuous_apply μ).add continuous_const
private theorem eqAsJet_symm {δ : ℝ} {p : Fin 4 → ℂ} {T S : JetQuad I I}
    (h : EqAsJet δ p T S) : EqAsJet δ p S T :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩
private theorem logNumber_widthIndependent
    (hArgs : JetArgumentsAndEqualJets) (hI : IsPeriodic I)
    (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) :
    LogNumberWidthIndependent F I T := by
  intro p εPlus εMinus δ₁ δ₂ S₁ S₂ _ _ hi₁ hj₁ he₁ _ _ hi₂ hj₂ he₂
  have e₁ := ((hArgs.2.2 δ₁ p I hI _ S₁ hi₁.isJet hj₁ (eqAsJet_symm he₁)).2 hi₁).2.2.2
  have e₂ := ((hArgs.2.2 δ₂ p I hI _ S₂ hi₂.isJet hj₂ (eqAsJet_symm he₂)).2 hi₂).2.2.2
  exact e₁.symm.trans e₂
private theorem twoPi_smul_castVec_mem_dualLattice {s : ℕ} (hs : 0 < s) (e : Fin 4 → ℤ) :
    (2 * Real.pi) • castVec e ∈ dualLattice s := by
  refine ⟨fun μ => (s : ℤ) * e μ, fun μ => ?_⟩
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  simp only [Pi.smul_apply, castVec, smul_eq_mul]
  push_cast
  field_simp
abbrev _root_.YangMills.SharedProofs.p28269 := @twoPi_smul_castVec_mem_dualLattice
private theorem tendsto_exp_neg_mul_sides {L : ℕ} (hL : 2 ≤ L) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun m : ℕ => Real.exp (-c * ((2 * L ^ m : ℕ) : ℝ))) atTop (𝓝 0) := by
  have hs : Tendsto (fun m : ℕ => ((2 * L ^ m : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun m => ?_) tendsto_id)
    have h1 : m < L ^ m := Nat.lt_pow_self (by omega)
    simp only [id]
    omega
  exact Real.tendsto_exp_atBot.comp (hs.const_mul_atTop_of_neg (neg_lt_zero.2 hc))
private theorem logDetForm_shift_on_dualLattice (hF : IsPeriodic F)
    (T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ) {L n s₀ : ℕ} (hL : 2 ≤ L) {C c : ℝ}
    (hc : 0 < c)
    (hsub : ∀ m, n ≤ m → (dualLattice (2 * L ^ n) : Set AmbientSpace) ⊆ dualLattice (2 * L ^ m))
    (hclose : ∀ s : ℕ, s₀ ≤ s → 0 < s →
      ∃ D, IsCloseToLogNumber F I T s D C c)
    {y : AmbientSpace} (hy : y ∈ dualLattice (2 * L ^ n)) (e : Fin 4 → ℤ)
    (εPlus εMinus : F.UnitQuot → ℂ) :
    logDetForm F I T (addTwoPiInt (toComplexVec y) e) εPlus εMinus =
      logDetForm F I T (toComplexVec y) (phaseMul F e εPlus)
        (phaseMul F (-e) εMinus) := by
  obtain ⟨a, ha⟩ : ∃ a, a = logDetForm F I T (addTwoPiInt (toComplexVec y) e)
      εPlus εMinus := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = logDetForm F I T (toComplexVec y)
      (phaseMul F e εPlus) (phaseMul F (-e) εMinus) := ⟨_, rfl⟩
  rw [← ha, ← hb]
  obtain ⟨A₁, hA₁⟩ : ∃ A, A = wNorm (F.quotWeight 1) εPlus := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A, A = wNorm (F.quotWeight 1) εMinus := ⟨_, rfl⟩
  obtain ⟨B₁, hB₁⟩ : ∃ B, B = wNorm (F.quotWeight 1) (phaseMul F e εPlus) :=
    ⟨_, rfl⟩
  obtain ⟨B₂, hB₂⟩ : ∃ B, B = wNorm (F.quotWeight 1) (phaseMul F (-e) εMinus) :=
    ⟨_, rfl⟩
  have key : ∀ m : ℕ, n ≤ m → s₀ ≤ 2 * L ^ m →
      ‖a - b‖ ≤ C * Real.exp (-c * ((2 * L ^ m : ℕ) : ℝ)) * B₁ * B₂ +
        C * Real.exp (-c * ((2 * L ^ m : ℕ) : ℝ)) * A₁ * A₂ := by
    intro m hm hs
    have hpos : 0 < 2 * L ^ m := by positivity
    obtain ⟨D, hD⟩ := hclose _ hs hpos
    have hy' : y + (2 * Real.pi) • castVec e ∈ dualLattice (2 * L ^ m) :=
      add_mem (hsub m hm hy) (twoPi_smul_castVec_mem_dualLattice hpos e)
    have h₁ := hD _ hy' εPlus εMinus
    have h₂ := hD y (hsub m hm hy) (phaseMul F e εPlus)
      (phaseMul F (-e) εMinus)
    rw [toComplexVec_add_twoPi_smul, blochWave_addTwoPiInt hF, neg_addTwoPiInt,
      blochWave_addTwoPiInt hF] at h₁
    rw [← hA₁, ← hA₂] at h₁
    rw [← hB₁, ← hB₂] at h₂
    have h₃ : logNumber (addTwoPiInt (toComplexVec y) e)
        (jetAlong F I I T (addTwoPiInt (toComplexVec y) e) εPlus εMinus) = a := ha.symm
    have h₄ : logNumber (toComplexVec y) (jetAlong F I I T (toComplexVec y)
        (phaseMul F e εPlus) (phaseMul F (-e) εMinus)) = b := hb.symm
    rw [h₃] at h₁
    rw [h₄] at h₂
    obtain ⟨X, hX⟩ : ∃ X, X = ((((2 * L ^ m : ℕ) : ℂ)) ^ 4)⁻¹ *
      D (LogDetSecondDerivs.descendField F (2 * L ^ m)
          (blochWave F (toComplexVec y) (phaseMul F e εPlus)))
        (LogDetSecondDerivs.descendField F (2 * L ^ m)
          (blochWave F (-toComplexVec y) (phaseMul F (-e) εMinus))) := ⟨_, rfl⟩
    rw [← hX] at h₁ h₂
    have h₅ : a - b = (X - b) - (X - a) := by ring
    rw [h₅]
    exact (norm_sub_le _ _).trans (add_le_add h₂ h₁)
  have hlim : Tendsto (fun m : ℕ => C * Real.exp (-c * ((2 * L ^ m : ℕ) : ℝ)) * B₁ * B₂ +
      C * Real.exp (-c * ((2 * L ^ m : ℕ) : ℝ)) * A₁ * A₂) atTop (𝓝 0) := by
    have he := tendsto_exp_neg_mul_sides hL hc
    have h₁ := ((he.const_mul C).mul_const B₁).mul_const B₂
    have h₂ := ((he.const_mul C).mul_const A₁).mul_const A₂
    simpa using h₁.add h₂
  have hsides : ∀ᶠ m : ℕ in atTop, n ≤ m ∧ s₀ ≤ 2 * L ^ m := by
    filter_upwards [eventually_ge_atTop (max n s₀)] with m hm
    have h1 : m < L ^ m := Nat.lt_pow_self (by omega)
    have h2 : n ≤ m := le_trans (le_max_left _ _) hm
    have h3 : s₀ ≤ m := le_trans (le_max_right _ _) hm
    exact ⟨h2, by omega⟩
  have hle : ‖a - b‖ ≤ 0 :=
    ge_of_tendsto hlim (hsides.mono fun m hm => key m hm.1 hm.2)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)
section OnStrip
open Classical
variable {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} {δ : ℝ}
private theorem logDetForm_eq_sum_coeff [Fintype F.UnitQuot] (hW : IsAdmissibleWidth F I T δ)
    {p : Fin 4 → ℂ} (hp : p ∈ imStrip δ) (εPlus εMinus : F.UnitQuot → ℂ) :
    logDetForm F I T p εPlus εMinus =
      ∑ c, ∑ c', logDetForm F I T p (Pi.single c 1) (Pi.single c' 1) *
        (εPlus c * εMinus c') := by
  obtain ⟨B, hB⟩ := hW.bilinear p hp
  have hsum : ∀ ε : F.UnitQuot → ℂ, ε = ∑ c, ε c • (Pi.single c 1 : F.UnitQuot → ℂ) :=
    fun ε => by
      funext d
      simp [Finset.sum_apply, Pi.single_apply]
  simp only [hB]
  conv_lhs => rw [hsum εPlus, hsum εMinus]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  ring
private theorem logDetForm_smul_smul (hW : IsAdmissibleWidth F I T δ) {p : Fin 4 → ℂ}
    (hp : p ∈ imStrip δ) (a b : ℂ) (ε ε' : F.UnitQuot → ℂ) :
    logDetForm F I T p (a • ε) (b • ε') = a * b * logDetForm F I T p ε ε' := by
  obtain ⟨B, hB⟩ := hW.bilinear p hp
  simp only [hB, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring
private theorem phaseMul_single (e : Fin 4 → ℤ) (c : F.UnitQuot) :
    phaseMul F e (Pi.single c 1) =
      phaseOn F e c • (Pi.single c 1 : F.UnitQuot → ℂ) := by
  funext d
  show phaseOn F e d * (Pi.single c 1 : F.UnitQuot → ℂ) d =
    phaseOn F e c * (Pi.single c 1 : F.UnitQuot → ℂ) d
  by_cases h : d = c
  · rw [h]
  · simp [Pi.single_eq_of_ne h]
private theorem isHolomorphicScalarIn_shift_sub {O : Set (Fin 4 → ℂ)} {g : (Fin 4 → ℂ) → ℂ}
    (hg : IsHolomorphicScalarIn O g) (e : Fin 4 → ℤ) (a : ℂ) :
    IsHolomorphicScalarIn (O ∩ (fun κ => addTwoPiInt κ e) ⁻¹' O)
      fun κ => g (addTwoPiInt κ e) - a * g κ := by
  obtain ⟨hO, hcont, hdiff⟩ := hg
  have hcont' : ContinuousOn g O := (continuous_apply (0 : Fin 1)).comp_continuousOn hcont
  have hG : ContinuousOn (fun κ => g (addTwoPiInt κ e) - a * g κ)
      (O ∩ (fun κ => addTwoPiInt κ e) ⁻¹' O) :=
    (hcont'.comp (continuous_addTwoPiInt e).continuousOn fun κ h => h.2).sub
      (continuousOn_const.mul (hcont'.mono inter_subset_left))
  refine ⟨hO.inter (hO.preimage (continuous_addTwoPiInt e)), continuousOn_pi.2 fun _ => hG,
    fun z hz j => ?_⟩
  filter_upwards [hdiff (addTwoPiInt z e) hz.2 j, hdiff z hz.1 j] with ζ d₁ d₂
  rw [differentiableAt_pi]
  intro i
  have hfun : (fun ζ : ℂ => asLine (fun κ => g (addTwoPiInt κ e) - a * g κ)
        (z + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) i) =
      fun ζ : ℂ => asLine g (addTwoPiInt z e + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) 0 -
        a * asLine g (z + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) 0 := by
    funext ζ'
    have : addTwoPiInt (z + ζ' • Coordinates.ComplexCoordinates.stdBasisVector j) e =
        addTwoPiInt z e + ζ' • Coordinates.ComplexCoordinates.stdBasisVector j := by
      funext μ
      simp only [addTwoPiInt, Pi.add_apply, Pi.smul_apply]
      ring
    simp only [asLine, this]
  rw [hfun]
  exact (differentiableAt_pi.1 d₁ 0).sub ((differentiableAt_pi.1 d₂ 0).const_mul a)
private theorem coeff_addTwoPiInt (hδ : 0 < δ) (hW : IsAdmissibleWidth F I T δ)
    (hMom : DualLatticeDensity.Claim)
    (hreal : ∀ n : ℕ, 1 ≤ n → ∀ y ∈ dualLattice (2 * 13 ^ n), ∀ (e : Fin 4 → ℤ)
      (εPlus εMinus : F.UnitQuot → ℂ),
      logDetForm F I T (addTwoPiInt (toComplexVec y) e) εPlus εMinus =
        logDetForm F I T (toComplexVec y) (phaseMul F e εPlus)
          (phaseMul F (-e) εMinus))
    (e : Fin 4 → ℤ) (c c' : F.UnitQuot) {κ : Fin 4 → ℂ} (hκ : κ ∈ imStrip δ) :
    logDetForm F I T (addTwoPiInt κ e) (Pi.single c 1) (Pi.single c' 1) =
      phaseOn F e c * phaseOn F (-e) c' *
        logDetForm F I T κ (Pi.single c 1) (Pi.single c' 1) := by
  obtain ⟨O, -, hsub, g, hg, hgs⟩ := hW.coefficients_holomorphic c c'
  obtain ⟨a, ha⟩ : ∃ a, a = phaseOn F e c * phaseOn F (-e) c' := ⟨_, rfl⟩
  rw [← ha]
  have hG := isHolomorphicScalarIn_shift_sub hg e a
  have hstrip : imStrip δ ⊆ O ∩ (fun κ => addTwoPiInt κ e) ⁻¹' O :=
    fun z h => ⟨hsub h, hsub (addTwoPiInt_mem_imStrip h e)⟩
  have hGc : ContinuousOn (fun κ => g (addTwoPiInt κ e) - a * g κ)
      (O ∩ (fun κ => addTwoPiInt κ e) ⁻¹' O) :=
    (continuous_apply (0 : Fin 1)).comp_continuousOn hG.2.1
  have hcont : Continuous fun y => g (addTwoPiInt (toComplexVec y) e) -
      a * g (toComplexVec y) :=
    hGc.comp_continuous continuous_toComplexVec fun y => hstrip (toComplexVec_mem_imStrip hδ y)
  have hzero : ∀ n : ℕ, 1 ≤ n → ∀ p ∈ dualLattice (2 * 13 ^ n),
      ‖g (addTwoPiInt (toComplexVec p) e) - a * g (toComplexVec p)‖ ≤ 0 := by
    intro n hn p hp
    have hp' := toComplexVec_mem_imStrip hδ p
    have h₁ := hreal n hn p hp e (Pi.single c 1) (Pi.single c' 1)
    rw [phaseMul_single, phaseMul_single, logDetForm_smul_smul hW hp', ← ha] at h₁
    rw [hgs _ (addTwoPiInt_mem_imStrip hp' e), hgs _ hp', h₁, sub_self, norm_zero]
  obtain ⟨-, -, hid⟩ := hMom 13 ⟨⟨6, by norm_num⟩, le_rfl⟩
  have h₂ : g (addTwoPiInt κ e) - a * g κ = 0 :=
    (hid _ 1 (fun _ => 0) hcont le_rfl (fun _ _ => le_rfl) tendsto_const_nhds hzero).2 δ
      (fun κ => g (addTwoPiInt κ e) - a * g κ) hδ ⟨_, hstrip, hG⟩ (fun _ => rfl) κ hκ
  rw [hgs _ (addTwoPiInt_mem_imStrip hκ e), hgs _ hκ] at h₂
  exact sub_eq_zero.1 h₂
private theorem logDetForm_quasiPeriodic (hF : IsPeriodic F) (hδ : 0 < δ)
    (hW : IsAdmissibleWidth F I T δ) (hMom : DualLatticeDensity.Claim)
    (hreal : ∀ n : ℕ, 1 ≤ n → ∀ y ∈ dualLattice (2 * 13 ^ n), ∀ (e : Fin 4 → ℤ)
      (εPlus εMinus : F.UnitQuot → ℂ),
      logDetForm F I T (addTwoPiInt (toComplexVec y) e) εPlus εMinus =
        logDetForm F I T (toComplexVec y) (phaseMul F e εPlus)
          (phaseMul F (-e) εMinus)) :
    LogDetFormQuasiPeriodic F I T δ := by
  intro p hp εPlus εMinus e
  refine ⟨addTwoPiInt_mem_imStrip hp e, ?_⟩
  have : Finite F.UnitQuot := hF.finite_quot
  have := Fintype.ofFinite F.UnitQuot
  rw [logDetForm_eq_sum_coeff hW (addTwoPiInt_mem_imStrip hp e),
    logDetForm_eq_sum_coeff hW hp (phaseMul F e εPlus)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  rw [coeff_addTwoPiInt hδ hW hMom hreal e c c' hp]
  show _ = _ * (phaseOn F e c * εPlus c * (phaseOn F (-e) c' * εMinus c'))
  ring
private theorem norm_apply_le_wNorm {J : Type} [Fintype J] {w : J → ℝ} (hw : ∀ c, 0 < w c)
    (ε : J → ℂ) (c : J) :
    ‖ε c‖ ≤ (∑ d, (Real.sqrt (w d))⁻¹) * wNorm w ε := by
  have hsq : w c * ‖ε c‖ ^ 2 ≤ ∑' i, w i * ‖ε i‖ ^ 2 := by
    rw [tsum_fintype]
    exact Finset.single_le_sum (f := fun i => w i * ‖ε i‖ ^ 2)
      (fun i _ => mul_nonneg (hw i).le (sq_nonneg _)) (Finset.mem_univ c)
  have hroot : 0 < Real.sqrt (w c) := Real.sqrt_pos.2 (hw c)
  have h₁ : Real.sqrt (w c) * ‖ε c‖ ≤ wNorm w ε := by
    unfold wNorm
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, Real.sq_sqrt (hw c).le]
    exact hsq
  have h₂ : ‖ε c‖ ≤ (Real.sqrt (w c))⁻¹ * wNorm w ε := by
    rw [← div_eq_inv_mul, le_div_iff₀ hroot, mul_comm]
    exact h₁
  have h₃ : (Real.sqrt (w c))⁻¹ ≤ ∑ d, (Real.sqrt (w d))⁻¹ :=
    Finset.single_le_sum (f := fun d => (Real.sqrt (w d))⁻¹)
      (fun i _ => inv_nonneg.2 (Real.sqrt_nonneg _)) (Finset.mem_univ c)
  exact h₂.trans (mul_le_mul_of_nonneg_right h₃ (Real.sqrt_nonneg _))
private theorem wNorm_phaseMul (hF : IsPeriodic F) (e : Fin 4 → ℤ)
    (ε : F.UnitQuot → ℂ) :
    wNorm (F.quotWeight 1) (phaseMul F e ε) =
      wNorm (F.quotWeight 1) ε := by
  unfold wNorm
  congr 1
  refine tsum_congr fun c => ?_
  show F.quotWeight 1 c * ‖phaseOn F e c * ε c‖ ^ 2 = _
  rw [norm_mul, norm_phaseOn hF, one_mul]
private theorem wNorm_smul {J : Type} (w : J → ℝ) (a : ℂ) (ε : J → ℂ) :
    wNorm w (a • ε) = ‖a‖ * wNorm w ε := by
  have h : ∀ i, w i * ‖(a • ε) i‖ ^ 2 = ‖a‖ ^ 2 * (w i * ‖ε i‖ ^ 2) := fun i => by
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    ring
  unfold wNorm
  simp only [h]
  rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
abbrev _root_.YangMills.SharedProofs.p112894 := @wNorm_smul
private theorem exists_coeff_bound_fundamentalCell (hF : IsPeriodic F)
    (hW : IsAdmissibleWidth F I T δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p ∈ imStrip δ, (∀ μ, |(p μ).re| ≤ Real.pi) → ∀ c c' : F.UnitQuot,
      ‖logDetForm F I T p (Pi.single c 1) (Pi.single c' 1)‖ ≤ A := by
  have : Finite F.UnitQuot := hF.finite_quot
  have hK : IsCompact (Set.pi univ fun _ : Fin 4 =>
      Complex.reProdIm (Icc (-Real.pi) Real.pi) (Icc (-δ) δ)) :=
    isCompact_univ_pi fun _ => isCompact_Icc.reProdIm isCompact_Icc
  have hin : ∀ p ∈ (Set.pi univ fun _ : Fin 4 =>
      Complex.reProdIm (Icc (-Real.pi) Real.pi) (Icc (-δ) δ)), p ∈ imStrip δ := fun p hp μ =>
    abs_le.2 (Complex.mem_reProdIm.1 (hp μ (mem_univ μ))).2
  have hb : ∀ q : F.UnitQuot × F.UnitQuot, ∃ C : ℝ, ∀ p ∈ imStrip δ,
      (∀ μ, |(p μ).re| ≤ Real.pi) →
      ‖logDetForm F I T p (Pi.single q.1 1) (Pi.single q.2 1)‖ ≤ C := by
    rintro ⟨c, c'⟩
    obtain ⟨O, -, hsub, g, hg, hgs⟩ := hW.coefficients_holomorphic c c'
    have hg' : ContinuousOn g O := (continuous_apply (0 : Fin 1)).comp_continuousOn hg.2.1
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hg'.mono fun p hp => hsub (hin p hp))
    refine ⟨C, fun p hp hre => ?_⟩
    rw [← hgs p hp]
    refine hC p fun μ _ => Complex.mem_reProdIm.2 ⟨abs_le.1 (hre μ), abs_le.1 (hp μ)⟩
  choose C hC using hb
  obtain ⟨A, hA⟩ := Finite.exists_le C
  exact ⟨max A 0, le_max_right _ _, fun p hp hre c c' =>
    (hC (c, c') p hp hre).trans ((hA _).trans (le_max_left _ _))⟩
private theorem exists_logDetFormBound (hF : IsPeriodic F) (hw : ∀ c, 0 < F.quotWeight 1 c)
    (hW : IsAdmissibleWidth F I T δ) (hper : LogDetFormQuasiPeriodic F I T δ) :
    ∃ M : ℝ, 0 ≤ M ∧ IsLogDetFormBound F I T δ M := by
  have : Finite F.UnitQuot := hF.finite_quot
  have := Fintype.ofFinite F.UnitQuot
  obtain ⟨A, hA0, hA⟩ := exists_coeff_bound_fundamentalCell hF hW
  obtain ⟨W, hWdef⟩ : ∃ W, W = ∑ d, (Real.sqrt (F.quotWeight 1 d))⁻¹ := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hWdef]
    exact Finset.sum_nonneg fun i _ => inv_nonneg.2 (Real.sqrt_nonneg _)
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (Fintype.card F.UnitQuot : ℝ) := ⟨_, rfl⟩
  have hn0 : 0 ≤ n := by
    rw [hn]
    exact Nat.cast_nonneg _
  have hval : ∀ (ε : F.UnitQuot → ℂ) c, ‖ε c‖ ≤ W * wNorm (F.quotWeight 1) ε :=
    fun ε c => by
      rw [hWdef]
      exact norm_apply_le_wNorm hw ε c
  have hcell : ∀ p ∈ imStrip δ, (∀ μ, |(p μ).re| ≤ Real.pi) → ∀ ε ε' : F.UnitQuot → ℂ,
      ‖logDetForm F I T p ε ε'‖ ≤ n * n * (A * W * W) * wNorm (F.quotWeight 1) ε *
        wNorm (F.quotWeight 1) ε' := by
    intro p hp hre ε ε'
    have hnorm0 : ∀ ε : F.UnitQuot → ℂ, 0 ≤ wNorm (F.quotWeight 1) ε :=
      fun _ => Real.sqrt_nonneg _
    have hterm : ∀ c c' : F.UnitQuot,
        ‖logDetForm F I T p (Pi.single c 1) (Pi.single c' 1) * (ε c * ε' c')‖ ≤
          A * ((W * wNorm (F.quotWeight 1) ε) *
            (W * wNorm (F.quotWeight 1) ε')) := fun c c' => by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (hA p hp hre c c')
        (mul_le_mul (hval ε c) (hval ε' c') (norm_nonneg _)
          (mul_nonneg hW0 (hnorm0 ε)))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hA0
    rw [logDetForm_eq_sum_coeff hW hp]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun c _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun c' _ => hterm c c')).trans (le_of_eq ?_))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
    ring
  refine ⟨n * n * (A * W * W), by positivity, fun p hp ε ε' => ?_⟩
  obtain ⟨e, he⟩ : ∃ e : Fin 4 → ℤ, e = fun μ => round ((p μ).re / (2 * Real.pi)) := ⟨_, rfl⟩
  have hp0 : addTwoPiInt p (-e) ∈ imStrip δ := addTwoPiInt_mem_imStrip hp _
  have hpi : 0 < 2 * Real.pi := by positivity
  have hre : ∀ μ, |(addTwoPiInt p (-e) μ).re| ≤ Real.pi := by
    intro μ
    rw [addTwoPiInt_re]
    have h := abs_sub_round ((p μ).re / (2 * Real.pi))
    have heq : (p μ).re + 2 * Real.pi * (((-e) μ : ℤ) : ℝ) =
        2 * Real.pi * ((p μ).re / (2 * Real.pi) - (round ((p μ).re / (2 * Real.pi)) : ℝ)) := by
      rw [he]
      simp only [Pi.neg_apply, Int.cast_neg]
      field_simp
      ring
    rw [heq, abs_mul, abs_of_pos hpi]
    nlinarith
  have hback : addTwoPiInt (addTwoPiInt p (-e)) e = p := by
    funext μ
    simp only [addTwoPiInt, Pi.neg_apply, Int.cast_neg]
    ring
  have h := (hper _ hp0 ε ε' e).2
  rw [hback] at h
  rw [h]
  have hc := hcell _ hp0 hre (phaseMul F e ε) (phaseMul F (-e) ε')
  rwa [wNorm_phaseMul hF, wNorm_phaseMul hF] at hc
private theorem unitBallSup_isLogDetFormBound (hw : ∀ c, 0 < F.quotWeight 1 c)
    (hfin : Finite F.UnitQuot)
    (hW : IsAdmissibleWidth F I T δ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : IsLogDetFormBound F I T δ M) :
    BddAbove (unitBallValues F I T δ) ∧
      IsLogDetFormBound F I T δ (unitBallSup F I T δ) := by
  have := Fintype.ofFinite F.UnitQuot
  have hbdd : BddAbove (unitBallValues F I T δ) := by
    refine ⟨M, ?_⟩
    rintro r ⟨p, hp, ε, ε', h₁, h₂, rfl⟩
    refine (hM p hp ε ε').trans ?_
    have h₀ : 0 ≤ wNorm (F.quotWeight 1) ε := Real.sqrt_nonneg _
    have h₀' : 0 ≤ wNorm (F.quotWeight 1) ε' := Real.sqrt_nonneg _
    calc M * wNorm (F.quotWeight 1) ε * wNorm (F.quotWeight 1) ε'
        ≤ M * 1 * 1 := by gcongr
      _ = M := by ring
  refine ⟨hbdd, fun p hp ε ε' => ?_⟩
  have hzero : ∀ ε : F.UnitQuot → ℂ, wNorm (F.quotWeight 1) ε = 0 → ε = 0 := fun ε h => by
    funext c
    have := norm_apply_le_wNorm hw ε c
    rw [h, mul_zero] at this
    exact norm_le_zero_iff.1 this
  obtain ⟨B, hB⟩ := hW.bilinear p hp
  by_cases h₁ : wNorm (F.quotWeight 1) ε = 0
  · have hz : logDetForm F I T p ε ε' = 0 := by
      rw [hB, hzero ε h₁]
      simp
    rw [hz, h₁]
    simp
  by_cases h₂ : wNorm (F.quotWeight 1) ε' = 0
  · have hz : logDetForm F I T p ε ε' = 0 := by
      rw [hB, hzero ε' h₂]
      simp
    rw [hz, h₂]
    simp
  obtain ⟨n₁, hn₁⟩ : ∃ n, n = wNorm (F.quotWeight 1) ε := ⟨_, rfl⟩
  obtain ⟨n₂, hn₂⟩ : ∃ n, n = wNorm (F.quotWeight 1) ε' := ⟨_, rfl⟩
  rw [← hn₁] at h₁ ⊢
  rw [← hn₂] at h₂ ⊢
  have hp₁ : 0 < n₁ := lt_of_le_of_ne (hn₁ ▸ Real.sqrt_nonneg _) (Ne.symm h₁)
  have hp₂ : 0 < n₂ := lt_of_le_of_ne (hn₂ ▸ Real.sqrt_nonneg _) (Ne.symm h₂)
  have hnorm : ∀ n : ℝ, 0 < n → ‖((n⁻¹ : ℝ) : ℂ)‖ = n⁻¹ := fun n hn => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn)]
  have hu₁ : wNorm (F.quotWeight 1) (((n₁⁻¹ : ℝ) : ℂ) • ε) ≤ 1 := by
    rw [wNorm_smul, hnorm _ hp₁, ← hn₁, inv_mul_cancel₀ h₁]
  have hu₂ : wNorm (F.quotWeight 1) (((n₂⁻¹ : ℝ) : ℂ) • ε') ≤ 1 := by
    rw [wNorm_smul, hnorm _ hp₂, ← hn₂, inv_mul_cancel₀ h₂]
  have hle := le_csSup hbdd ⟨p, hp, _, _, hu₁, hu₂, rfl⟩
  rw [logDetForm_smul_smul hW hp, norm_mul, norm_mul, hnorm _ hp₁, hnorm _ hp₂] at hle
  have hsup : n₁⁻¹ * n₂⁻¹ * ‖logDetForm F I T p ε ε'‖ ≤ unitBallSup F I T δ := hle
  calc ‖logDetForm F I T p ε ε'‖
      = n₁⁻¹ * n₂⁻¹ * ‖logDetForm F I T p ε ε'‖ * n₁ * n₂ := by
        field_simp
    _ ≤ unitBallSup F I T δ * n₁ * n₂ := by gcongr
end OnStrip
theorem claim_holds (hLog : LogDetSecondDerivs.Claim)
    (hArgs : JetArgumentsAndEqualJets)
    (hMom : DualLatticeDensity.Claim)
    (hQuot : Quotients.QuotientTransposeNorm) : Claim := by
  intro F I hF hI T hT hsym δ hδ hW
  obtain ⟨δ₀, -, -, ⟨s₀, C, c, -, hc, hclose⟩, -, -⟩ := hLog F I hF hI T hT hsym
  have hclose' : ∀ s : ℕ, s₀ ≤ s → 0 < s →
      ∃ D, IsCloseToLogNumber F I T s D C c := by
    intro s hs hpos
    have : Finite (F.QuotMod s) := (hQuot F F hF hF s hpos).1.2.1
    obtain ⟨-, hall⟩ := hclose s hs
    exact ⟨_, (hall _ (Finite.equivFin _).symm).2.2⟩
  obtain ⟨hsub, -, -⟩ := hMom 13 ⟨⟨6, by norm_num⟩, le_rfl⟩
  have hreal : ∀ n : ℕ, 1 ≤ n → ∀ y ∈ dualLattice (2 * 13 ^ n), ∀ (e : Fin 4 → ℤ)
      (εPlus εMinus : F.UnitQuot → ℂ),
      logDetForm F I T (addTwoPiInt (toComplexVec y) e) εPlus εMinus =
        logDetForm F I T (toComplexVec y) (phaseMul F e εPlus)
          (phaseMul F (-e) εMinus) := fun n hn y hy e a b =>
    logDetForm_shift_on_dualLattice hF T (by norm_num) hc (fun m hm => hsub n m hn hm)
      hclose' hy e a b
  have hper := logDetForm_quasiPeriodic hF hδ hW hMom hreal
  have hw : ∀ c, 0 < F.quotWeight 1 c := by
    intro c
    obtain ⟨ι, rfl⟩ := exists_mkQuot_eq c
    rw [((hQuot F F hF hF 1 one_pos).2.1 1 (Or.inl rfl)).1.2 ι]
    exact hF.weight_pos _
  obtain ⟨M, hM0, hM⟩ := exists_logDetFormBound hF hw hW hper
  obtain ⟨hb, hs⟩ := unitBallSup_isLogDetFormBound hw hF.finite_quot hW hM0 hM
  exact ⟨logNumber_widthIndependent hArgs hI T, hper, ⟨M, hM⟩, hb, hs⟩
end YangMills.Construction.PeriodicOperators.StripBound
end
