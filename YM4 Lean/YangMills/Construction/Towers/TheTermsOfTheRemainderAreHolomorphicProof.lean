import YangMills.Construction.ComplexAnalysis.BoxIntegralHolomorphic
import YangMills.Construction.PeriodicOperators.BoundsOfTheNumbersOfAJet
import YangMills.Construction.PeriodicOperators.InterpolationOfTheLogarithmicNumberProof
import YangMills.Construction.Towers.InversesOfJetsWithHolomorphicComponents
import YangMills.Construction.Towers.PropertiesOfTheBackgroundsProof
import YangMills.Construction.Towers.SumsProductsAndTransposesOfJetsWithHolomorphicComponents
import YangMills.Construction.Towers.TheBasicJetsAreBounded
import YangMills.Construction.Towers.TheMiddleJetsOfTheRemainderAreInvertible
import YangMills.Construction.Towers.TheOperatorJetsAreBoundedAtOneHeightProof
import YangMills.Construction.Towers.TheSharpFunctionOfTheMassiveJetsProof
import YangMills.Construction.Towers.TheTermsOfTheRemainderAreHolomorphic
import YangMills.Construction.Towers.TraceNumberOfJetsWithHolomorphicComponents
import Mathlib
set_option autoImplicit false
open Filter Set Topology MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.TermsHolomorphic
open Coordinates
open PeriodicOperators
open PeriodicOperators.JetQuad
open ScaledOperatorFunctions
open BackgroundProperties (productOver)
open PeriodicOperators.JetDomains (fstMomentum sndMomentum)
open PeriodicOperators.JetNormsAffine (affinePath)
section ScalarFunctions
variable {N : ℕ} {O : Set (ComplexCoordinates N)} {f g : ComplexCoordinates N → ℂ}
theorem isHolomorphicIn_one_iff :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O (fun p _ => f p) ↔
      IsOpen O ∧ ContinuousOn f O ∧ ∀ a ∈ O, ∀ j : Fin N, ∀ᶠ ζ in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ (fun ζ : ℂ => f (a + ζ • ComplexCoordinates.stdBasisVector j)) ζ := by apply _root_.YangMills.Construction.PeriodicOperators.OpFunComp.isHolomorphicIn_scalar_iff <;> assumption
theorem isHolomorphicIn_sub (hf : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun p _ => f p)
    (hg : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun p _ => g p) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun p _ => f p - g p := by
  have hf' := isHolomorphicIn_one_iff.1 hf
  have hg' := isHolomorphicIn_one_iff.1 hg
  refine isHolomorphicIn_one_iff.2 ⟨hf'.1, hf'.2.1.sub hg'.2.1, fun a ha j => ?_⟩
  filter_upwards [hf'.2.2 a ha j, hg'.2.2 a ha j] with ζ h₁ h₂
  exact h₁.sub h₂
theorem isHolomorphicIn_const_mul (c : ℂ)
    (hf : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun p _ => f p) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun p _ => c * f p := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_const_mul <;> assumption
theorem isHolomorphicIn_const (hO : IsOpen O) (c : ℂ) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun _ _ => c := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_const <;> assumption
theorem isHolomorphicIn_congr_mono {N' : ℕ} {O' : Set (ComplexCoordinates N)}
    {u v : ComplexCoordinates N → ComplexCoordinates N'} (hO' : IsOpen O') (hsub : O' ⊆ O)
    (h : ComplexCoordinates.IsHolomorphicIn O u) (e : ∀ z ∈ O', v z = u z) :
    ComplexCoordinates.IsHolomorphicIn O' v := by
  refine ⟨hO', (h.2.1.mono hsub).congr e, fun a ha j => ?_⟩
  have hc : Continuous fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j := by fun_prop
  have hopen : IsOpen ((fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j) ⁻¹' O') :=
    hO'.preimage hc
  have h0 : (0 : ℂ) ∈ (fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j) ⁻¹' O' := by
    simpa using ha
  filter_upwards [h.2.2 a (hsub ha) j, hopen.mem_nhds h0] with ζ h₁ h₂
  refine h₁.congr_of_eventuallyEq ?_
  filter_upwards [hopen.mem_nhds h₂] with ζ' h₃
  exact e _ h₃
end ScalarFunctions
theorem isHolomorphicIn_intervalIntegral (hBox : ComplexAnalysis.BoxIntegralHolomorphicInParameter)
    {P : Set (ComplexCoordinates 4)} (hP : IsOpen P) (f : ℝ → ComplexCoordinates 4 → ℂ) (m : ℝ)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ P, ‖f t p‖ ≤ m)
    (hc : ∀ p ∈ P, ContinuousOn (fun t => f t p) (Icc (0 : ℝ) 1))
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, ComplexCoordinates.IsHolomorphicIn (N' := 1) P fun p _ => f t p) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) P fun p _ => ∫ t in (0 : ℝ)..1, f t p := by
  have hmem : ∀ s ∈ Icc (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 1), s 0 ∈ Icc (0 : ℝ) 1 :=
    fun s hs => ⟨hs.1 0, hs.2 0⟩
  have key := (hBox 1 4 le_rfl (by norm_num) (fun _ => 0) (fun _ => 1) (fun _ => zero_le_one) P hP
    (fun s p => f (s 0) p) ⟨m, fun s hs p hp => hb _ (hmem s hs) p hp⟩
    (fun p hp => (hc p hp).comp (continuous_apply 0).continuousOn hmem)
    (fun s hs => hh _ (hmem s hs))).2
  have e : ∀ p, (∫ s in Icc (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 1), f (s 0) p) =
      ∫ t in (0 : ℝ)..1, f t p := by
    intro p
    have hmp := MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ
    have hpre : (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Icc (0 : ℝ) 1 =
        Icc (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 1) := by
      ext s
      simp only [mem_preimage, mem_Icc, Pi.le_def, MeasurableEquiv.funUnique_apply]
      constructor
      · rintro ⟨h₁, h₂⟩
        refine ⟨fun i => ?_, fun i => ?_⟩ <;> rw [Subsingleton.elim i default] <;> assumption
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁ _, h₂ _⟩
    have h := hmp.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _)
      (fun t => f t p) (Icc (0 : ℝ) 1)
    rw [hpre] at h
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc, ← h]
    refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
    simp only [MeasurableEquiv.funUnique_apply]
    rw [Subsingleton.elim (default : Fin 1) 0]
  simpa only [e] using key
theorem isOpen_productOver {U : Set (Fin 4 → ℂ)} (hU : IsOpen U) : IsOpen (productOver U) := by
  have hc : Continuous fun z : ComplexCoordinates (4 + 4) => sndMomentum z :=
    continuous_pi fun μ => continuous_apply _
  exact hU.preimage hc
theorem appendSet_univ_prod (U : Set (Fin 4 → ℂ)) :
    appendSet (n := 4) (n' := 4) (univ ×ˢ U) = productOver U := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.appendSet_univ_prod <;> assumption
section MomentumPairs
variable {I I' : PeriodicData} {U O : Set (Fin 4 → ℂ)}
theorem momentumPair_of_productOver (hU : IsOpen U) (hsub : U ⊆ O)
    {A A' : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I I'}
    (hA : ∀ (c' : I'.UnitQuot) (c : I.UnitQuot),
      ComplexCoordinates.IsHolomorphicIn (N := 4 + 4) (N' := 1) (productOver O) fun z _ =>
        linearMapEntry (A' (sndMomentum z) (fstMomentum z)) c' c)
    (e : ∀ p ∈ U, A p = A' p) : IsHolomorphicInMomentumPair (univ ×ˢ U) A := by
  unfold IsHolomorphicInMomentumPair HoldsOnAppended
  rw [appendSet_univ_prod]
  refine ⟨by norm_num, isOpen_productOver hU, fun x => ?_⟩
  refine isHolomorphicIn_congr_mono (isOpen_productOver hU) (fun z hz => hsub hz) (hA x.1 x.2)
    fun z hz => ?_
  funext _
  change linearMapEntry (A (sndMomentum z) (fstMomentum z)) x.1 x.2 = _
  rw [e _ hz]
theorem momentumPair_const (hU : IsOpen U) (M : QuotHom I I') :
    IsHolomorphicInMomentumPair (univ ×ˢ U) (fun _ _ => M) := by
  unfold IsHolomorphicInMomentumPair HoldsOnAppended
  rw [appendSet_univ_prod]
  exact ⟨by norm_num, isOpen_productOver hU, fun x =>
    isHolomorphicIn_const (isOpen_productOver hU) (quotHomEntries M x)⟩
theorem momentumPair_smul {W : Set (ComplexCoordinates 4 × ComplexCoordinates 4)} (a : ℂ)
    {A : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I I'}
    (h : IsHolomorphicInMomentumPair W A) :
    IsHolomorphicInMomentumPair W (fun p κ => a • A p κ) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨h₁, h₂, fun x => ?_⟩
  have h₄ := isHolomorphicIn_const_mul a (h₃ x)
  refine isHolomorphicIn_congr_mono h₂ subset_rfl h₄ fun z _ => ?_
  funext _
  simp [quotHomEntries, linearMapEntry]
theorem componentOpenDomain_const {P : Set (ComplexCoordinates 4)} (hP : IsOpen P)
    (D : ComplexCoordinates 4 → Set (Fin 4 → ℂ)) (M : QuotHom I I') :
    ComponentOpenDomain P D (fun _ _ => M) :=
  ⟨univ ×ˢ P, fun _ hq => hq.2, fun _ hp _ _ => ⟨mem_univ _, hp⟩, momentumPair_const hP M⟩
theorem componentOpenDomain_smul {P : Set (ComplexCoordinates 4)}
    {D : ComplexCoordinates 4 → Set (Fin 4 → ℂ)} (a : ℂ)
    {A : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I I'}
    (h : ComponentOpenDomain P D A) :
    ComponentOpenDomain P D (fun p κ => a • A p κ) := by
  obtain ⟨W, h₁, h₂, h₃⟩ := h
  exact ⟨W, h₁, h₂, momentumPair_smul a h₃⟩
end MomentumPairs
theorem invJet_f00 {I : PeriodicData} (p : Fin 4 → ℂ) (T : JetQuad I I) (κ : Fin 4 → ℂ) :
    (invJet p T).f00 κ = quotHomInverse (T.f00 κ) := by
  by_cases h : IsUnit (T.f00 κ : Module.End ℂ (I.UnitQuot → ℂ))
  · have hN : (normalize p T).f00 κ = 0 := by
      have e : (quotHomInverse (T.f00 κ)).comp (T.f00 κ) = LinearMap.id :=
        Ring.inverse_mul_cancel (T.f00 κ : Module.End ℂ (I.UnitQuot → ℂ)) h
      simp only [JetQuad.normalize, add, smul, mul, one, zeroPartInv, e, Pi.add_apply,
        Pi.smul_apply]
      apply LinearMap.ext
      intro f
      funext c
      simp
    simp [invJet, add, smul, mul, one, zeroPartInv, hN]
  · have e : quotHomInverse (T.f00 κ) = 0 := Ring.inverse_non_unit _ h
    simp [invJet, add, smul, mul, one, zeroPartInv, e]
section TameFamilies
variable {δ : ℝ} {P : Set (ComplexCoordinates 4)} {Θ Θ' : Type} {I I' I'' : PeriodicData}
structure TameSetting (δ : ℝ) (P : Set (ComplexCoordinates 4)) : Prop where
  delta_pos : 0 < δ
  isOpen : IsOpen P
  subset_interior : P ⊆ StripSymbols.openStripInterior δ
  mem_strip : ∀ p ∈ P, p ∈ imStrip δ
  closure : JetClosure.JetOpsClosed
  inv : InvertibleJetInverseHolomorphic
  trace : JetTraceHolomorphy.Claim
  jetCalc : JetCalculus.Claim
  normsAffine : JetNormsAffine.Claim
  quadAlg : QuadAlgebra.Claim
  domains : JetDomains.OpFunJetTheory
  bounds : JetNumberBounds.Claim
def IsTame (δ : ℝ) (P : Set (ComplexCoordinates 4)) (T : Θ → ComplexCoordinates 4 → JetQuad I I') :
    Prop :=
  (∀ θ, JetFamilyHolomorphic δ P (T θ)) ∧
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ θ, ∀ p ∈ P, jetNorm δ p (T θ p) ≤ B
def HasBoundedZeroInverse (δ C : ℝ) (p : Fin 4 → ℂ) (T : JetQuad I I) : Prop :=
  IsInvertibleJet δ p T ∧
    ∀ κ ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse (T.f00 κ)) ≤ ENNReal.ofReal C
theorem TameSetting.one_isJet (F : TameSetting δ P) (hI : IsPeriodic I) {p : Fin 4 → ℂ}
    (hp : p ∈ P) : IsJet δ p (one I) :=
  (F.domains.2.2 I I I hI hI hI δ p F.delta_pos (F.mem_strip p hp)).one_isJet
theorem isTame_comp {T : Θ → ComplexCoordinates 4 → JetQuad I I'} (h : IsTame δ P T)
    (f : Θ' → Θ) : IsTame δ P fun θ' => T (f θ') := by
  obtain ⟨h₁, B, hB, h₂⟩ := h
  exact ⟨fun θ => h₁ _, B, hB, fun θ => h₂ _⟩
theorem isTame_add (F : TameSetting δ P) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T S : Θ → ComplexCoordinates 4 → JetQuad I I'} (hT : IsTame δ P T) (hS : IsTame δ P S) :
    IsTame δ P fun θ p => (T θ p).add (S θ p) := by
  obtain ⟨hT, B, hB, hTB⟩ := hT
  obtain ⟨hS, B', hB', hSB⟩ := hS
  refine ⟨fun θ => (F.closure δ F.delta_pos P F.isOpen F.subset_interior I I' I' hI hI' hI').1
      _ _ (hT θ) (hS θ),
    B + B', ENNReal.add_lt_top.2 ⟨hB, hB'⟩, fun θ p hp => ?_⟩
  exact ((F.quadAlg.2 δ p F.delta_pos (F.mem_strip p hp) I I' hI hI').1 _ _
    ((hT θ).is_jet p hp) ((hS θ).is_jet p hp)).trans (add_le_add (hTB θ p hp) (hSB θ p hp))
theorem isTame_mul (F : TameSetting δ P) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (hI'' : IsPeriodic I'') {T : Θ → ComplexCoordinates 4 → JetQuad I I'}
    {S : Θ → ComplexCoordinates 4 → JetQuad I'' I} (hT : IsTame δ P T) (hS : IsTame δ P S) :
    IsTame δ P fun θ p => mul p (T θ p) (S θ p) := by
  obtain ⟨hT, B, hB, hTB⟩ := hT
  obtain ⟨hS, B', hB', hSB⟩ := hS
  refine ⟨fun θ => (F.closure δ F.delta_pos P F.isOpen F.subset_interior I I' I'' hI hI' hI'').2.1
      _ _ (hT θ) (hS θ),
    B * B', ENNReal.mul_lt_top hB hB', fun θ p hp => ?_⟩
  exact ((F.jetCalc δ p F.delta_pos (F.mem_strip p hp)).1 I' I I'' I'' hI' hI hI'' hI'' _ _
    (one I'') ((hT θ).is_jet p hp) ((hS θ).is_jet p hp) (F.one_isJet hI'' hp)).2.trans
    (mul_le_mul' (hTB θ p hp) (hSB θ p hp))
theorem isTame_transposeAt (F : TameSetting δ P) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : Θ → ComplexCoordinates 4 → JetQuad I I'} (hT : IsTame δ P T) :
    IsTame δ P fun θ p => transposeAt p (T θ p) := by
  obtain ⟨hT, B, hB, hTB⟩ := hT
  refine ⟨fun θ => (F.closure δ F.delta_pos P F.isOpen F.subset_interior I I' I' hI hI' hI').2.2
      _ (hT θ),
    B, hB, fun θ p hp => ?_⟩
  rw [((F.jetCalc δ p F.delta_pos (F.mem_strip p hp)).2.1 I' I I hI' hI hI _ (one I)
    ((hT θ).is_jet p hp) (F.one_isJet hI hp)).2]
  exact hTB θ p hp
theorem jetFamilyHolomorphic_smul (F : TameSetting δ P) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (a : ℂ) {T : ComplexCoordinates 4 → JetQuad I I'}
    (hT : JetFamilyHolomorphic δ P T) :
    JetFamilyHolomorphic δ P fun p => JetQuad.smul a (T p) where
  is_jet := fun p hp =>
    (F.domains.2.2 I I' I hI hI' hI δ p F.delta_pos (F.mem_strip p hp)).smul_isJet a _
      (hT.is_jet p hp)
  open00 := componentOpenDomain_smul a hT.open00
  open10 := componentOpenDomain_smul a hT.open10
  open01 := componentOpenDomain_smul a hT.open01
  open11 := componentOpenDomain_smul a hT.open11
theorem isTame_smul (F : TameSetting δ P) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (a : Θ → ℂ) (M : ℝ) (ha : ∀ θ, ‖a θ‖ ≤ M) {T : Θ → ComplexCoordinates 4 → JetQuad I I'}
    (hT : IsTame δ P T) : IsTame δ P fun θ p => JetQuad.smul (a θ) (T θ p) := by
  obtain ⟨hT, B, hB, hTB⟩ := hT
  refine ⟨fun θ => jetFamilyHolomorphic_smul F hI hI' (a θ) (hT θ), ENNReal.ofReal M * B,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB, fun θ p hp => ?_⟩
  exact ((F.quadAlg.2 δ p F.delta_pos (F.mem_strip p hp) I I' hI hI').2.1 _ _
    ((hT θ).is_jet p hp)).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (ha θ)) (hTB θ p hp))
theorem isTame_one (F : TameSetting δ P) (hI : IsPeriodic I) :
    IsTame δ P (fun (_ : Θ) (_ : ComplexCoordinates 4) => one I) := by
  refine ⟨fun _ => ⟨fun p hp => F.one_isJet hI hp, componentOpenDomain_const F.isOpen _ LinearMap.id,
    componentOpenDomain_const F.isOpen _ 0, componentOpenDomain_const F.isOpen _ 0,
    componentOpenDomain_const F.isOpen _ 0⟩,
    1, ENNReal.one_lt_top, fun _ p hp => ?_⟩
  exact (F.quadAlg.2 δ p F.delta_pos (F.mem_strip p hp) I I hI hI).2.2.1
theorem isTame_invJet (F : TameSetting δ P) (hI : IsPeriodic I) {C : ℝ}
    {T : Θ → ComplexCoordinates 4 → JetQuad I I} (hT : IsTame δ P T)
    (h : ∀ θ, ∀ p ∈ P, HasBoundedZeroInverse δ C p (T θ p)) :
    IsTame δ P fun θ p => invJet p (T θ p) := by
  obtain ⟨hT, B, hB, hTB⟩ := hT
  refine ⟨fun θ => F.inv δ F.delta_pos P F.isOpen F.subset_interior I hI _ (hT θ)
      fun p hp => (h θ p hp).1,
    ENNReal.ofReal C * (1 + ENNReal.ofReal C * B) ^ 2, ?_, fun θ p hp => ?_⟩
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top
      (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB⟩))
  · obtain ⟨-, -, -, h₁, h₂⟩ :=
      (F.jetCalc δ p F.delta_pos (F.mem_strip p hp)).2.2.2.2.1 I hI _ (h θ p hp).1
    have hc : jetNorm δ p (zeroPartInv (T θ p)) ≤ ENNReal.ofReal C := by
      rw [h₂]
      exact iSup₂_le (h θ p hp).2
    refine h₁.trans ?_
    have := hTB θ p hp
    gcongr
theorem isTame_zeroPartInv (F : TameSetting δ P) (hI : IsPeriodic I) {C : ℝ}
    {T : Θ → ComplexCoordinates 4 → JetQuad I I} (hT : IsTame δ P T)
    (h : ∀ θ, ∀ p ∈ P, HasBoundedZeroInverse δ C p (T θ p)) :
    IsTame δ P fun θ p => zeroPartInv (T θ p) := by
  have hinv := (isTame_invJet F hI hT h).1
  refine ⟨fun θ => ⟨fun p hp => ?_, ?_, componentOpenDomain_const F.isOpen _ 0,
    componentOpenDomain_const F.isOpen _ 0, componentOpenDomain_const F.isOpen _ 0⟩,
    ENNReal.ofReal C, ENNReal.ofReal_lt_top, fun θ p hp => ?_⟩
  · exact ((F.domains.2.2 I I I hI hI hI δ p F.delta_pos (F.mem_strip p hp)).zeroPart_isJet _
      (h θ p hp).1).2
  · have e : (fun p => (zeroPartInv (T θ p)).f00) = fun p => (invJet p (T θ p)).f00 := by
      funext p κ
      exact (invJet_f00 p (T θ p) κ).symm
    rw [e]
    exact (hinv θ).open00
  · obtain ⟨-, -, -, -, h₂⟩ :=
      (F.jetCalc δ p F.delta_pos (F.mem_strip p hp)).2.2.2.2.1 I hI _ (h θ p hp).1
    rw [h₂]
    exact iSup₂_le (h θ p hp).2
theorem isTame_traceNumber (F : TameSetting δ P) (hI : IsPeriodic I)
    {T : Θ → ComplexCoordinates 4 → JetQuad I I} (hT : IsTame δ P T) :
    (∃ m : ℝ, ∀ θ, ∀ p ∈ P, ‖traceNumber (T θ p)‖ ≤ m) ∧
      ∀ θ, ComplexCoordinates.IsHolomorphicIn (N' := 1) P fun p _ => traceNumber (T θ p) := by
  obtain ⟨hT, B, hB, hTB⟩ := hT
  refine ⟨⟨((Module.finrank ℂ (I.UnitQuot → ℂ) : ℝ≥0∞) * B).toReal, fun θ p hp => ?_⟩,
    fun θ => ?_⟩
  · have h := ((F.bounds δ p F.delta_pos (F.mem_strip p hp) I hI (T θ p)).1
      ((hT θ).is_jet p hp)).trans (mul_le_mul' le_rfl (hTB θ p hp))
    exact (ENNReal.ofReal_le_iff_le_toReal
      (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hB).ne).1 h
  · exact F.trace δ F.delta_pos P F.isOpen F.subset_interior I hI _ (hT θ)
      (lt_of_le_of_lt (iSup₂_le fun p hp => hTB θ p hp) hB)
end TameFamilies
section FormulaNumbers
variable {δ : ℝ} {P : Set (ComplexCoordinates 4)} {I : PeriodicData}
theorem unitShiftedPath_zero (A W : JetQuad I I) : unitShiftedPath A W 0 = addScalarJet A 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.LogNumberInterpolation.unitShiftedPath_zero <;> assumption
theorem continuousOn_traceNumber_affinePath (F : TameSetting δ P) (hI : IsPeriodic I) {C : ℝ}
    {p : Fin 4 → ℂ} (hp : p ∈ P) {A B : JetQuad I I} (hA : IsJet δ p A) (hB : IsJet δ p B)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, HasBoundedZeroInverse δ C p (affinePath A B t)) :
    (∀ X : JetQuad I I, IsJet δ p X →
      ContinuousOn (fun t => traceNumber (mul p X (invJet p (affinePath A B t))))
        (Icc (0 : ℝ) 1)) ∧
      ContinuousOn (fun t => traceNumber (mul p (invJet p (affinePath A B t)) B))
        (Icc (0 : ℝ) 1) := by
  have h₁ := (F.normsAffine δ p F.delta_pos (F.mem_strip p hp) I I hI hI).2 A B hA hB
    (Icc (0 : ℝ) 1) isCompact_Icc ordConnected_Icc ⟨0, by simp, 1, by simp, zero_ne_one⟩
    (fun t ht => (h t ht).1)
    ⟨ENNReal.ofReal C, ENNReal.ofReal_lt_top, fun t ht => iSup₂_le (h t ht).2⟩
  exact ⟨h₁.2.2.1, h₁.2.2.2.1⟩
theorem logNumber_isHolomorphicIn (F : TameSetting δ P) (hI : IsPeriodic I) {C : ℝ}
    {T : ComplexCoordinates 4 → JetQuad I I} (hT : IsTame δ P fun _ : Unit => T)
    (h : ∀ p ∈ P, HasBoundedZeroInverse δ C p (T p)) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) P fun p _ => logNumber p (T p) := by
  have hc : IsTame δ P fun (_ : Unit) p => zeroPartInv (T p) :=
    isTame_zeroPartInv F hI hT fun _ p hp => h p hp
  have h1 : IsTame δ P fun (_ : Unit) (_ : ComplexCoordinates 4) => one I := isTame_one F hI
  have hN : IsTame δ P fun (_ : Unit) p => normalize p (T p) :=
    isTame_add F hI hI (isTame_mul F hI hI hI hc hT)
      (isTame_smul F hI hI (fun _ => -1) 1 (by simp) h1)
  have hL : IsTame δ P fun (_ : Unit) p => logSeries p (T p) :=
    isTame_add F hI hI hN
      (isTame_smul F hI hI (fun _ => -(1 / 2)) 1 (by norm_num) (isTame_mul F hI hI hI hN hN))
  exact (isTame_traceNumber F hI hL).2 ()
theorem pathRemainder_isHolomorphicIn
    (hBox : ComplexAnalysis.BoxIntegralHolomorphicInParameter)
    (F : TameSetting δ P) (hI : IsPeriodic I) {C : ℝ} {A W : ComplexCoordinates 4 → JetQuad I I}
    (hA : IsTame δ P fun _ : Unit => A) (hW : IsTame δ P fun _ : Unit => W)
    (h₁ : ∀ p ∈ P, ∀ t ∈ Icc (0 : ℝ) 1,
      HasBoundedZeroInverse δ C p (unitShiftedPath (A p) (W p) t))
    (h₂ : ∀ p ∈ P, ∀ t ∈ Icc (0 : ℝ) 1,
      HasBoundedZeroInverse δ C p (addScalarJet ((A p).add (W p)) t)) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) P fun p _ =>
      pathRemainder p (A p) (W p) := by
  have hA' : IsTame δ P fun (_ : Icc (0 : ℝ) 1) => A := isTame_comp hA fun _ => ()
  have hW' : IsTame δ P fun (_ : Icc (0 : ℝ) 1) => W := isTame_comp hW fun _ => ()
  have hone : IsTame δ P fun (_ : Icc (0 : ℝ) 1) (_ : ComplexCoordinates 4) => one I :=
    isTame_one F hI
  have hbound : ∀ θ : Icc (0 : ℝ) 1, ‖((θ : ℝ) : ℂ)‖ ≤ 1 := fun θ => by
    rw [Complex.norm_real, Real.norm_of_nonneg θ.2.1]
    exact θ.2.2
  have hplus : IsTame δ P fun (_ : Icc (0 : ℝ) 1) p => addScalarJet (A p) 1 :=
    isTame_add F hI hI hA' (isTame_smul F hI hI (fun _ => ((1 : ℝ) : ℂ)) 1 (by simp) hone)
  have hfam : IsTame δ P fun (θ : Icc (0 : ℝ) 1) p => unitShiftedPath (A p) (W p) θ :=
    isTame_add F hI hI hplus
      (isTame_smul F hI hI (fun θ : Icc (0 : ℝ) 1 => ((θ : ℝ) : ℂ)) 1 hbound hW')
  have hfamInv : IsTame δ P fun (θ : Icc (0 : ℝ) 1) p =>
      invJet p (unitShiftedPath (A p) (W p) θ) :=
    isTame_invJet F hI hfam fun θ p hp => h₁ p hp θ θ.2
  have hG : IsTame δ P fun (_ : Icc (0 : ℝ) 1) p => unitShiftedInverse p (A p) :=
    isTame_invJet F hI hplus (C := C) fun _ p hp => by
      have h := h₁ p hp 0 (by simp)
      rwa [unitShiftedPath_zero] at h
  have hshift : IsTame δ P fun (θ : Icc (0 : ℝ) 1) p => addScalarJet ((A p).add (W p)) θ :=
    isTame_add F hI hI (isTame_add F hI hI hA' hW')
      (isTame_smul F hI hI (fun θ : Icc (0 : ℝ) 1 => ((θ : ℝ) : ℂ)) 1 hbound hone)
  have hP : IsTame δ P fun (θ : Icc (0 : ℝ) 1) p => perturbedInverse p (A p) (W p) θ :=
    isTame_invJet F hI hshift fun θ p hp => h₂ p hp θ θ.2
  have hGG : IsTame δ P fun (_ : Icc (0 : ℝ) 1) p =>
      mul p (unitShiftedInverse p (A p)) (unitShiftedInverse p (A p)) :=
    isTame_mul F hI hI hI hG hG
  have hGW : IsTame δ P fun (_ : Icc (0 : ℝ) 1) p => mul p (unitShiftedInverse p (A p)) (W p) :=
    isTame_mul F hI hI hI hG hW'
  have hGGW : IsTame δ P fun (_ : Icc (0 : ℝ) 1) p =>
      mul p (mul p (unitShiftedInverse p (A p)) (unitShiftedInverse p (A p))) (W p) :=
    isTame_mul F hI hI hI hGG hW'
  obtain ⟨⟨m₁, hm₁⟩, hh₁⟩ := isTame_traceNumber F hI (isTame_mul F hI hI hI hfamInv hW')
  obtain ⟨⟨m₂, hm₂⟩, hh₂⟩ := isTame_traceNumber F hI (isTame_mul F hI hI hI hGG hP)
  obtain ⟨⟨m₃, hm₃⟩, hh₃⟩ := isTame_traceNumber F hI (isTame_mul F hI hI hI hGW hP)
  obtain ⟨⟨m₄, hm₄⟩, hh₄⟩ := isTame_traceNumber F hI (isTame_mul F hI hI hI hGGW hP)
  have hjet : ∀ {T : Icc (0 : ℝ) 1 → ComplexCoordinates 4 → JetQuad I I}, IsTame δ P T →
      ∀ p ∈ P, IsJet δ p (T ⟨0, by simp⟩ p) := fun hT p hp => (hT.1 _).is_jet p hp
  have first : ComplexCoordinates.IsHolomorphicIn (N' := 1) P fun p _ =>
      ∫ t in (0 : ℝ)..1,
        traceNumber (mul p (invJet p (unitShiftedPath (A p) (W p) t)) (W p)) := by
    refine isHolomorphicIn_intervalIntegral hBox F.isOpen
      (fun t p => traceNumber (mul p (invJet p (unitShiftedPath (A p) (W p) t)) (W p))) m₁
      (fun t ht p hp => hm₁ ⟨t, ht⟩ p hp) (fun p hp => ?_) (fun t ht => hh₁ ⟨t, ht⟩)
    exact (continuousOn_traceNumber_affinePath F hI hp (hjet hplus p hp) (hjet hW' p hp)
      (h₁ p hp)).2
  have second : ComplexCoordinates.IsHolomorphicIn (N' := 1) P fun p _ =>
      ∫ τ in (0 : ℝ)..1, correctionIntegrand p (A p) (W p) τ := by
    have hc : ∀ τ ∈ Icc (0 : ℝ) 1, ‖((1 - τ : ℝ) : ℂ)‖ ≤ 1 := fun τ hτ => by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [hτ.2])]
      linarith [hτ.1]
    refine isHolomorphicIn_intervalIntegral hBox F.isOpen
      (fun τ p => correctionIntegrand p (A p) (W p) τ) (m₂ + m₃ + m₄)
      (fun τ hτ p hp => ?_) (fun p hp => ?_) (fun τ hτ => ?_)
    · have e₂ := hm₂ ⟨τ, hτ⟩ p hp
      have e₃ := hm₃ ⟨τ, hτ⟩ p hp
      have e₄ := hm₄ ⟨τ, hτ⟩ p hp
      have hc₁ := hc τ hτ
      have n₂ := norm_nonneg (traceNumber (mul p (mul p (unitShiftedInverse p (A p))
        (unitShiftedInverse p (A p))) (perturbedInverse p (A p) (W p) τ)))
      have n₄ := norm_nonneg (traceNumber (mul p (mul p (mul p (unitShiftedInverse p (A p))
        (unitShiftedInverse p (A p))) (W p)) (perturbedInverse p (A p) (W p) τ)))
      unfold correctionIntegrand
      refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ e₃)) ?_)
      · rw [norm_mul, norm_pow]
        calc _ ≤ 1 ^ 2 * _ := mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (norm_nonneg _) hc₁ 2) n₂
          _ ≤ m₂ := by simpa using e₂
      · rw [norm_mul]
        calc _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hc₁ n₄
          _ ≤ m₄ := by simpa using e₄
    · have hs : ∀ t ∈ Icc (0 : ℝ) 1,
          HasBoundedZeroInverse δ C p (affinePath ((A p).add (W p)) (one I) t) := h₂ p hp
      have hk := (continuousOn_traceNumber_affinePath F hI hp
        ((isTame_add F hI hI hA hW).1 () |>.is_jet p hp) (F.one_isJet hI hp) hs).1
      have k₂ : ContinuousOn (fun τ => traceNumber (mul p (mul p (unitShiftedInverse p (A p))
          (unitShiftedInverse p (A p))) (perturbedInverse p (A p) (W p) τ))) (Icc (0 : ℝ) 1) :=
        hk _ (hjet hGG p hp)
      have k₃ : ContinuousOn (fun τ => traceNumber (mul p (mul p (unitShiftedInverse p (A p))
          (W p)) (perturbedInverse p (A p) (W p) τ))) (Icc (0 : ℝ) 1) := hk _ (hjet hGW p hp)
      have k₄ : ContinuousOn (fun τ => traceNumber (mul p (mul p (mul p
          (unitShiftedInverse p (A p)) (unitShiftedInverse p (A p))) (W p))
          (perturbedInverse p (A p) (W p) τ))) (Icc (0 : ℝ) 1) :=
        hk _ (hjet hGGW p hp)
      have kc : ContinuousOn (fun τ : ℝ => ((1 - τ : ℝ) : ℂ)) (Icc (0 : ℝ) 1) :=
        (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).continuousOn
      exact (((kc.pow 2).mul k₂).sub k₃).sub (kc.mul k₄)
    · exact isHolomorphicIn_sub
        (isHolomorphicIn_sub (isHolomorphicIn_const_mul _ (hh₂ ⟨τ, hτ⟩)) (hh₃ ⟨τ, hτ⟩))
        (isHolomorphicIn_const_mul _ (hh₄ ⟨τ, hτ⟩))
  exact isHolomorphicIn_sub first second
end FormulaNumbers
section FormulaJets
variable {L k : ℕ} {μPlus μMinus : Fin 4}
theorem stripHalfWidth_pos (h : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) :
    0 < stripHalfWidth := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.SharpLogFn.stripHalfWidth_pos <;> assumption
theorem jetWidth_of_mem {p : Fin 4 → ℂ} (hp : p ∈ momentumPolydisc stripHalfWidth) :
    BackgroundProperties.jetWidth p = stripHalfWidth := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.JetBoundsAtLevel.jetWidth_eq_of_mem <;> assumption
theorem jetAlongResponse_holomorphic {U O : Set (Fin 4 → ℂ)} {I I' : PeriodicData}
    (hU : IsOpen U) (hUm : U ⊆ momentumPolydisc stripHalfWidth)
    (hsub : momentumPolydisc stripHalfWidth ⊆ O)
    (hresp : ∀ p ∈ O, BackgroundProperties.ResponseSymbolSummableAt L k p)
    {T : ((remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ}
    (hJ : BackgroundProperties.JetWellDefined L k μPlus μMinus I I' T)
    (hC : BackgroundProperties.ComponentsHolomorphicOn L k μPlus μMinus O I I' T) :
    JetFamilyHolomorphic stripHalfWidth U fun p => jetAlongResponse L k T p μPlus μMinus where
  is_jet := fun p hp => by
    have h := hJ.isJet p (hresp p (hsub (hUm hp)))
    rwa [jetWidth_of_mem (hUm hp), BackgroundProperties.axisJet_of_mem T (hUm hp)] at h
  open00 := ⟨univ ×ˢ U, fun _ hq => hq.2, fun _ hp _ _ => ⟨mem_univ _, hp⟩,
    momentumPair_of_productOver hU (hUm.trans hsub)
      (A' := fun p => (BackgroundProperties.axisJet L k T p μPlus μMinus).f00) hC.holo_f00
      fun p hp => by rw [BackgroundProperties.axisJet_of_mem T (hUm hp)]⟩
  open10 := ⟨univ ×ˢ U, fun _ hq => hq.2, fun _ hp _ _ => ⟨mem_univ _, hp⟩,
    momentumPair_of_productOver hU (hUm.trans hsub)
      (A' := fun p => (BackgroundProperties.axisJet L k T p μPlus μMinus).f10) hC.holo_f10
      fun p hp => by rw [BackgroundProperties.axisJet_of_mem T (hUm hp)]⟩
  open01 := ⟨univ ×ˢ U, fun _ hq => hq.2, fun _ hp _ _ => ⟨mem_univ _, hp⟩,
    momentumPair_of_productOver hU (hUm.trans hsub)
      (A' := fun p => (BackgroundProperties.axisJet L k T p μPlus μMinus).f01) hC.holo_f01
      fun p hp => by rw [BackgroundProperties.axisJet_of_mem T (hUm hp)]⟩
  open11 := ⟨univ ×ˢ U, fun _ hq => hq.2, fun _ hp _ _ => ⟨mem_univ _, hp⟩,
    momentumPair_of_productOver hU (hUm.trans hsub)
      (A' := fun p => (BackgroundProperties.axisJet L k T p μPlus μMinus).f11) hC.holo_f11
      fun p hp => by rw [BackgroundProperties.axisJet_of_mem T (hUm hp)]⟩
theorem isHolomorphicScalar_of {P : Set (ComplexCoordinates 4)} {f : ComplexCoordinates 4 → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) P fun p _ => f p) :
    ComplexVariables.IsHolomorphicScalar P f := by
  have e : (Equiv.funUnique (Fin 1) ℂ).symm ∘ f = fun p _ => f p := by
    funext p i
    simp [Equiv.funUnique]
  unfold ComplexVariables.IsHolomorphicScalar
  rw [e]
  exact h
end FormulaJets
theorem remainderTermsHolomorphic_holds
    (hSum : JetClosure.JetOpsClosed)
    (hInv : InvertibleJetInverseHolomorphic)
    (hTr : JetTraceHolomorphy.Claim)
    (hBox : ComplexAnalysis.BoxIntegralHolomorphicInParameter)
    (hBack : BackgroundProperties.BackgroundPropertiesHold)
    (hMid : MiddleJetsInvertible.MiddleJetsInvertibleClaim)
    (hBasic : BoundedBasicJets.BasicJetsBounded)
    (hOp : OperatorJetBounds.JetsBoundedAtLevel)
    (hCalc : JetCalculus.Claim)
    (hNorm : JetNormsAffine.Claim)
    (hAlg : QuadAlgebra.Claim)
    (hLoc : JetDomains.OpFunJetTheory)
    (hTow : TowerIndexSets.Claim)
    (hSym : StripSymbols.Claim)
    (hNum : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hBd : JetNumberBounds.Claim) : RemainderTermsHolomorphic := by
  intro L hL k hk μPlus μMinus
  have hδ := stripHalfWidth_pos hNum
  have hUo : IsOpen (openPolydisc stripHalfWidth) := by
    simp only [openPolydisc, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun μ => isOpen_lt (by fun_prop) continuous_const
  have hUm : openPolydisc stripHalfWidth ⊆ momentumPolydisc stripHalfWidth :=
    fun p hp μ => (hp μ).le
  have hUs : ∀ p ∈ openPolydisc stripHalfWidth, p ∈ imStrip stripHalfWidth :=
    fun p hp μ => (Complex.abs_im_le_norm _).trans (hp μ).le
  have hUi : openPolydisc stripHalfWidth ⊆ StripSymbols.openStripInterior stripHalfWidth := by
    rw [(hSym.1 _ hδ).1]
    exact fun p hp μ => (Complex.abs_im_le_norm _).trans_lt (hp μ)
  have F : TameSetting stripHalfWidth (openPolydisc stripHalfWidth) :=
    ⟨hδ, hUo, hUi, hUs, hSum, hInv, hTr, hCalc, hNorm, hAlg, hLoc, hBd⟩
  obtain ⟨hS0, hB0, -⟩ := hTow L hL k 0 (Nat.zero_le _)
  obtain ⟨hSk, hBk, -⟩ := hTow L hL k k le_rfl
  have hAt := hBack L hL k hk
  obtain ⟨O, -, hOsub, hOn⟩ := hAt.exists_nhds μPlus μMinus
  obtain ⟨jD, -, -, -, jK, jΔ, jQ, jR⟩ := hAt.jets_wellDefined μPlus μMinus
  obtain ⟨cD, -, -, -, cK, cΔ, cQ, cR⟩ := hOn.components
  obtain ⟨C₁, hC₁⟩ := hOp L hL k hk μPlus μMinus
  obtain ⟨⟨C₂, -, hC₂⟩, -⟩ := hBasic L hL
  have tD : IsTame stripHalfWidth (openPolydisc stripHalfWidth)
      (fun (_ : Unit) p => covDerivJet L k p μPlus μMinus) :=
    ⟨fun _ => jetAlongResponse_holomorphic hUo hUm hOsub hOn.response_summable jD cD,
      ENNReal.ofReal C₁, ENNReal.ofReal_lt_top, fun _ p hp => (hC₁ p (hUm hp)).1⟩
  have tK : IsTame stripHalfWidth (openPolydisc stripHalfWidth)
      (fun (_ : Unit) p => edgeOperatorJet L k p μPlus μMinus) :=
    ⟨fun _ => jetAlongResponse_holomorphic hUo hUm hOsub hOn.response_summable jK cK,
      ENNReal.ofReal C₁, ENNReal.ofReal_lt_top, fun _ p hp => (hC₁ p (hUm hp)).2.1⟩
  have tΔ : IsTame stripHalfWidth (openPolydisc stripHalfWidth)
      (fun (_ : Unit) p => vertexOperatorJet L k p μPlus μMinus) :=
    ⟨fun _ => jetAlongResponse_holomorphic hUo hUm hOsub hOn.response_summable jΔ cΔ,
      ENNReal.ofReal C₁, ENNReal.ofReal_lt_top, fun _ p hp => (hC₁ p (hUm hp)).2.2⟩
  have tQ : IsTame stripHalfWidth (openPolydisc stripHalfWidth)
      (fun (_ : Unit) p => edgeSmoothingJet L k p μPlus μMinus) :=
    ⟨fun _ => jetAlongResponse_holomorphic hUo hUm hOsub hOn.response_summable jQ cQ,
      ENNReal.ofReal C₂, ENNReal.ofReal_lt_top,
      fun _ p hp => (hC₂ k hk μPlus μMinus p (hUm hp)).edgeSmoothing⟩
  have tR : IsTame stripHalfWidth (openPolydisc stripHalfWidth)
      (fun (_ : Unit) p => vertexSmoothingJet L k p μPlus μMinus) :=
    ⟨fun _ => jetAlongResponse_holomorphic hUo hUm hOsub hOn.response_summable jR cR,
      ENNReal.ofReal C₂, ENNReal.ofReal_lt_top,
      fun _ p hp => (hC₂ k hk μPlus μMinus p (hUm hp)).vertexSmoothing⟩
  have tRR : IsTame stripHalfWidth (openPolydisc stripHalfWidth)
      (fun (_ : Unit) p => vertexCorrectionJet L k p μPlus μMinus) :=
    isTame_mul F hSk hS0 hS0 (isTame_transposeAt F hS0 hSk tR) tR
  have tV : IsTame stripHalfWidth (openPolydisc stripHalfWidth)
      (fun (_ : Unit) p => edgeCorrectionJet L k p μPlus μMinus) :=
    isTame_add F hB0 hB0 (isTame_mul F hBk hB0 hB0 (isTame_transposeAt F hB0 hBk tQ) tQ)
      (isTame_smul F hB0 hB0 (fun _ => -1) 1 (by simp)
        (isTame_mul F hS0 hB0 hB0 (isTame_mul F hS0 hB0 hS0 tD tRR)
          (isTame_transposeAt F hS0 hB0 tD)))
  have tΞ : IsTame stripHalfWidth (openPolydisc stripHalfWidth)
      (fun (_ : Unit) p => edgeMiddleJet L k p μPlus μMinus) := isTame_add F hB0 hB0 tK tV
  have tY : IsTame stripHalfWidth (openPolydisc stripHalfWidth)
      (fun (_ : Unit) p => vertexMiddleJet L k p μPlus μMinus) := isTame_add F hS0 hS0 tΔ tRR
  obtain ⟨C, hC⟩ := hMid
  have hm := fun p (hp : p ∈ openPolydisc stripHalfWidth) =>
    hC L hL k hk p (hUm hp) μPlus μMinus
  have tBC : IsTame stripHalfWidth (openPolydisc stripHalfWidth)
      (fun (_ : Unit) p => edgeConstraintJet L k p μPlus μMinus) :=
    isTame_mul F hB0 hBk hBk
      (isTame_mul F hB0 hBk hB0 tQ
        (isTame_invJet F hB0 tΞ (C := C) fun _ p hp => (hm p hp).2.1))
      (isTame_transposeAt F hB0 hBk tQ)
  have tSC : IsTame stripHalfWidth (openPolydisc stripHalfWidth)
      (fun (_ : Unit) p => vertexConstraintJet L k p μPlus μMinus) :=
    isTame_mul F hS0 hSk hSk
      (isTame_mul F hS0 hSk hS0 tR
        (isTame_invJet F hS0 tY (C := C) fun _ p hp => (hm p hp).2.2.1))
      (isTame_transposeAt F hS0 hSk tR)
  refine ⟨isHolomorphicScalar_of ?_, isHolomorphicScalar_of ?_, isHolomorphicScalar_of ?_,
    isHolomorphicScalar_of ?_⟩
  · exact pathRemainder_isHolomorphicIn hBox F hB0 (C := C)
      (A := fun p => edgeOperatorJet L k p μPlus μMinus)
      (W := fun p => edgeCorrectionJet L k p μPlus μMinus) tK tV
      (fun p hp t ht => ((hm p hp).1 t ht).1) (fun p hp t ht => ((hm p hp).1 t ht).2.2.1)
  · exact pathRemainder_isHolomorphicIn hBox F hS0 (C := C)
      (A := fun p => vertexOperatorJet L k p μPlus μMinus)
      (W := fun p => vertexCorrectionJet L k p μPlus μMinus) tΔ tRR
      (fun p hp t ht => ((hm p hp).1 t ht).2.1) (fun p hp t ht => ((hm p hp).1 t ht).2.2.2)
  · exact logNumber_isHolomorphicIn F hBk (C := C)
      (T := fun p => edgeConstraintJet L k p μPlus μMinus) tBC fun p hp => (hm p hp).2.2.2.1
  · exact logNumber_isHolomorphicIn F hSk (C := C)
      (T := fun p => vertexConstraintJet L k p μPlus μMinus) tSC fun p hp => (hm p hp).2.2.2.2
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.TermsHolomorphic
end
