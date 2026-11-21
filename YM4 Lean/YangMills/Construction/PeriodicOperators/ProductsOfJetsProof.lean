import YangMills.Construction.PeriodicOperators.BoundOfTheKernelOfAMatrixFunctionProof
import YangMills.Construction.PeriodicOperators.IntegrandOfTheLogarithmicNumberOfAFunctionProof
import YangMills.Construction.PeriodicOperators.ProductsOfJets
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetProducts
open JetDomains
open JetQuad (IsJet)
section Scalars
abbrev ScalarHolomorphicOn (D : Set (Fin 4 → ℂ)) (u : (Fin 4 → ℂ) → ℂ) : Prop :=
  Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) D fun κ _ => u κ
theorem scalarHolomorphicOn_iff (D : Set (Fin 4 → ℂ)) (u : (Fin 4 → ℂ) → ℂ) :
    ScalarHolomorphicOn D u ↔
      IsOpen D ∧ ContinuousOn u D ∧ ∀ a ∈ D, ∀ j : Fin 4, ∀ᶠ ζ in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ
          (fun ζ : ℂ => u (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) ζ := by apply _root_.YangMills.Construction.PeriodicOperators.MatrixFunctionKernel.isHolomorphicIn_scalar_iff <;> assumption
variable {D E : Set (Fin 4 → ℂ)} {u v : (Fin 4 → ℂ) → ℂ}
theorem ScalarHolomorphicOn.zero (hD : IsOpen D) : ScalarHolomorphicOn D fun _ => 0 :=
  (scalarHolomorphicOn_iff D _).2 ⟨hD, continuousOn_const,
    fun _ _ _ => Eventually.of_forall fun _ => differentiableAt_const _⟩
theorem ScalarHolomorphicOn.add (hu : ScalarHolomorphicOn D u)
    (hv : ScalarHolomorphicOn D v) : ScalarHolomorphicOn D fun κ => u κ + v κ := by
  obtain ⟨hOpen, hCu, hDu⟩ := (scalarHolomorphicOn_iff D u).1 hu
  obtain ⟨-, hCv, hDv⟩ := (scalarHolomorphicOn_iff D v).1 hv
  refine (scalarHolomorphicOn_iff D _).2 ⟨hOpen, hCu.add hCv, fun a ha j => ?_⟩
  filter_upwards [hDu a ha j, hDv a ha j] with ζ h h' using h.add h'
theorem ScalarHolomorphicOn.mul (hu : ScalarHolomorphicOn D u)
    (hv : ScalarHolomorphicOn D v) : ScalarHolomorphicOn D fun κ => u κ * v κ := by apply _root_.YangMills.Construction.PeriodicOperators.MatrixFunctionKernel.isHolomorphicIn_scalar_mul <;> assumption
theorem ScalarHolomorphicOn.sum {α : Type} (s : Finset α) (f : α → (Fin 4 → ℂ) → ℂ)
    (hD : IsOpen D) (h : ∀ i ∈ s, ScalarHolomorphicOn D (f i)) :
    ScalarHolomorphicOn D fun κ => ∑ i ∈ s, f i κ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ScalarHolomorphicOn.zero hD
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
theorem ScalarHolomorphicOn.mono (hu : ScalarHolomorphicOn E u) (hD : IsOpen D)
    (h : D ⊆ E) : ScalarHolomorphicOn D u := by
  obtain ⟨-, hC, hE⟩ := (scalarHolomorphicOn_iff E u).1 hu
  exact (scalarHolomorphicOn_iff D u).2 ⟨hD, hC.mono h, fun a ha j => hE a (h ha) j⟩
theorem ScalarHolomorphicOn.comp_add_const (q : Fin 4 → ℂ) (hu : ScalarHolomorphicOn E u)
    (hD : IsOpen D) (h : ∀ κ ∈ D, κ + q ∈ E) : ScalarHolomorphicOn D fun κ => u (κ + q) := by
  obtain ⟨-, hC, hE⟩ := (scalarHolomorphicOn_iff E u).1 hu
  refine (scalarHolomorphicOn_iff D _).2
    ⟨hD, hC.comp (continuous_add_const q).continuousOn h, fun a ha j => ?_⟩
  have e : (fun ζ : ℂ => u (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j + q)) =
      fun ζ : ℂ => u (a + q + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) := by
    funext ζ
    rw [add_right_comm]
  rw [e]
  exact hE (a + q) (h a ha) j
end Scalars
section Entries
theorem linearMapEntry_comp {J J' J'' : Type} [Fintype J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ))
    (N : (J'' → ℂ) →ₗ[ℂ] (J → ℂ)) (y : J') (x : J'') :
    linearMapEntry (M.comp N) y x = ∑ d, linearMapEntry M y d * linearMapEntry N d x := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.linearMapEntry_comp <;> assumption
variable {I I' I'' : PeriodicData} {D E : Set (Fin 4 → ℂ)}
theorem entriesHolomorphicOn_add {A B : (Fin 4 → ℂ) → QuotHom I I'}
    (hA : EntriesHolomorphicOn D A) (hB : EntriesHolomorphicOn D B) :
    EntriesHolomorphicOn D fun κ => A κ + B κ :=
  fun y x => ScalarHolomorphicOn.add (hA y x) (hB y x)
theorem entriesHolomorphicOn_comp [Finite I.UnitQuot] {A : (Fin 4 → ℂ) → QuotHom I I'}
    {B : (Fin 4 → ℂ) → QuotHom I'' I} (hD : IsOpen D) (hA : EntriesHolomorphicOn D A)
    (hB : EntriesHolomorphicOn D B) :
    EntriesHolomorphicOn D fun κ => (A κ).comp (B κ) := by
  intro y x
  have := Fintype.ofFinite I.UnitQuot
  simp only [linearMapEntry_comp]
  exact ScalarHolomorphicOn.sum Finset.univ
    (fun d κ => linearMapEntry (A κ) y d * linearMapEntry (B κ) d x) hD
    fun d _ => ScalarHolomorphicOn.mul (hA y d) (hB d x)
theorem entriesHolomorphicOn_mono {A : (Fin 4 → ℂ) → QuotHom I I'}
    (hA : EntriesHolomorphicOn E A) (hD : IsOpen D) (h : D ⊆ E) : EntriesHolomorphicOn D A :=
  fun y x => ScalarHolomorphicOn.mono (hA y x) hD h
theorem entriesHolomorphicOn_comp_add_const (q : Fin 4 → ℂ) {A : (Fin 4 → ℂ) → QuotHom I I'}
    (hA : EntriesHolomorphicOn E A) (hD : IsOpen D) (h : ∀ κ ∈ D, κ + q ∈ E) :
    EntriesHolomorphicOn D fun κ => A (κ + q) :=
  fun y x => ScalarHolomorphicOn.comp_add_const q (hA y x) hD h
theorem entriesHolomorphicOn_comp_sub_const (q : Fin 4 → ℂ) {A : (Fin 4 → ℂ) → QuotHom I I'}
    (hA : EntriesHolomorphicOn E A) (hD : IsOpen D) (h : ∀ κ ∈ D, κ - q ∈ E) :
    EntriesHolomorphicOn D fun κ => A (κ - q) := by
  simp only [sub_eq_add_neg] at h ⊢
  exact entriesHolomorphicOn_comp_add_const (-q) hA hD h
end Entries
section Sets
theorem real_mem_imStrip_two_mul {δ : ℝ} {p κ : Fin 4 → ℂ} (hδ : 0 < δ) (hp : p ∈ imStrip δ)
    (h : κ ∈ realDualPoints) :
    κ ∈ imStrip (2 * δ) ∧ κ + p ∈ imStrip (2 * δ) ∧ κ - p ∈ imStrip (2 * δ) := by
  have hκ : ∀ μ, (κ μ).im = 0 := h
  have hp' : ∀ μ, |(p μ).im| ≤ δ := hp
  refine ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩
  · rw [hκ μ, abs_zero]
    linarith
  · have := hp' μ
    rw [Pi.add_apply, Complex.add_im, hκ μ, zero_add]
    linarith
  · have := hp' μ
    rw [Pi.sub_apply, Complex.sub_im, hκ μ, zero_sub, abs_neg]
    linarith
def mulDomains (p : Fin 4 → ℂ) (U V : Domains) : Domains where
  dom00 := U.dom00 ∩ V.dom00
  dom10 := U.dom10 ∩ V.dom00 ∩ (fun κ => κ + p) ⁻¹' U.dom00 ∩ V.dom10
  dom01 := U.dom01 ∩ V.dom00 ∩ (fun κ => κ - p) ⁻¹' U.dom00 ∩ V.dom01
  dom11 := U.dom11 ∩ V.dom00 ∩ U.dom00 ∩ V.dom11 ∩ (fun κ => κ - p) ⁻¹' U.dom10 ∩ V.dom01 ∩
    (fun κ => κ + p) ⁻¹' U.dom01 ∩ V.dom10
theorem mulDefinedOn_mulDomains (p : Fin 4 → ℂ) (U V : Domains) :
    MulDefinedOn p U V (mulDomains p U V) := by
  refine ⟨fun κ h => h, ?_, ?_, ?_⟩
  · rintro κ ⟨⟨⟨a, b⟩, c⟩, d⟩
    exact ⟨a, b, c, d⟩
  · rintro κ ⟨⟨⟨a, b⟩, c⟩, d⟩
    exact ⟨a, b, c, d⟩
  · rintro κ ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, h⟩
    exact ⟨a, b, c, d, e, f, g, h⟩
theorem areNhds_mulDomains {δ : ℝ} {p : Fin 4 → ℂ} {U V : Domains} (hδ : 0 < δ)
    (hp : p ∈ imStrip δ) (hU : AreNhds δ p U) (hV : AreNhds δ p V) :
    AreNhds δ p (mulDomains p U V) where
  isOpen00 := hU.isOpen00.inter hV.isOpen00
  isOpen10 := ((hU.isOpen10.inter hV.isOpen00).inter
    (hU.isOpen00.preimage (continuous_add_const p))).inter hV.isOpen10
  isOpen01 := ((hU.isOpen01.inter hV.isOpen00).inter
    (hU.isOpen00.preimage (continuous_sub_right p))).inter hV.isOpen01
  isOpen11 := ((((((hU.isOpen11.inter hV.isOpen00).inter hU.isOpen00).inter hV.isOpen11).inter
    (hU.isOpen10.preimage (continuous_sub_right p))).inter hV.isOpen01).inter
    (hU.isOpen01.preimage (continuous_add_const p))).inter hV.isOpen10
  strip_subset := fun _ h => ⟨hU.strip_subset h, hV.strip_subset h⟩
  addShift_subset := fun _ h =>
    ⟨⟨⟨hU.addShift_subset h, hV.strip_subset h.1⟩, hU.strip_subset h.2⟩, hV.addShift_subset h⟩
  subShift_subset := fun _ h =>
    ⟨⟨⟨hU.subShift_subset h, hV.strip_subset h.1⟩, hU.strip_subset h.2⟩, hV.subShift_subset h⟩
  real_subset := by
    intro κ h
    obtain ⟨r, plus, minus⟩ := real_mem_imStrip_two_mul hδ hp h
    have m : κ - p ∈ stripAddShift δ p := ⟨minus, by simpa using r⟩
    have n : κ + p ∈ stripSubShift δ p := ⟨plus, by simpa using r⟩
    exact ⟨⟨⟨⟨⟨⟨⟨hU.real_subset h, hV.strip_subset r⟩, hU.strip_subset r⟩, hV.real_subset h⟩,
      hU.addShift_subset m⟩, hV.subShift_subset ⟨r, minus⟩⟩, hU.subShift_subset n⟩,
      hV.addShift_subset ⟨r, plus⟩⟩
variable {I I' I'' : PeriodicData}
theorem holomorphicOnDomains_mul [Finite I.UnitQuot] {δ : ℝ} {p : Fin 4 → ℂ}
    {U V W : Domains} {T : JetQuad I I'} {S : JetQuad I'' I} (hW : AreNhds δ p W)
    (hF : MulDefinedOn p U V W) (hT : HolomorphicOnDomains U T)
    (hS : HolomorphicOnDomains V S) : HolomorphicOnDomains W (JetQuad.mul p T S) := by
  obtain ⟨f00, f10, f01, f11⟩ := hF
  obtain ⟨t00, t10, t01, t11⟩ := hT
  obtain ⟨s00, s10, s01, s11⟩ := hS
  have o00 := hW.isOpen00
  have o10 := hW.isOpen10
  have o01 := hW.isOpen01
  have o11 := hW.isOpen11
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact entriesHolomorphicOn_comp o00
      (entriesHolomorphicOn_mono t00 o00 fun κ h => (f00 κ h).1)
      (entriesHolomorphicOn_mono s00 o00 fun κ h => (f00 κ h).2)
  · exact entriesHolomorphicOn_add
      (entriesHolomorphicOn_comp o10
        (entriesHolomorphicOn_mono t10 o10 fun κ h => (f10 κ h).1)
        (entriesHolomorphicOn_mono s00 o10 fun κ h => (f10 κ h).2.1))
      (entriesHolomorphicOn_comp o10
        (entriesHolomorphicOn_comp_add_const p t00 o10 fun κ h => (f10 κ h).2.2.1)
        (entriesHolomorphicOn_mono s10 o10 fun κ h => (f10 κ h).2.2.2))
  · exact entriesHolomorphicOn_add
      (entriesHolomorphicOn_comp o01
        (entriesHolomorphicOn_mono t01 o01 fun κ h => (f01 κ h).1)
        (entriesHolomorphicOn_mono s00 o01 fun κ h => (f01 κ h).2.1))
      (entriesHolomorphicOn_comp o01
        (entriesHolomorphicOn_comp_sub_const p t00 o01 fun κ h => (f01 κ h).2.2.1)
        (entriesHolomorphicOn_mono s01 o01 fun κ h => (f01 κ h).2.2.2))
  · exact entriesHolomorphicOn_add (entriesHolomorphicOn_add (entriesHolomorphicOn_add
      (entriesHolomorphicOn_comp o11
        (entriesHolomorphicOn_mono t11 o11 fun κ h => (f11 κ h).1)
        (entriesHolomorphicOn_mono s00 o11 fun κ h => (f11 κ h).2.1))
      (entriesHolomorphicOn_comp o11
        (entriesHolomorphicOn_mono t00 o11 fun κ h => (f11 κ h).2.2.1)
        (entriesHolomorphicOn_mono s11 o11 fun κ h => (f11 κ h).2.2.2.1)))
      (entriesHolomorphicOn_comp o11
        (entriesHolomorphicOn_comp_sub_const p t10 o11 fun κ h => (f11 κ h).2.2.2.2.1)
        (entriesHolomorphicOn_mono s01 o11 fun κ h => (f11 κ h).2.2.2.2.2.1)))
      (entriesHolomorphicOn_comp o11
        (entriesHolomorphicOn_comp_add_const p t01 o11 fun κ h => (f11 κ h).2.2.2.2.2.2.1)
        (entriesHolomorphicOn_mono s10 o11 fun κ h => (f11 κ h).2.2.2.2.2.2.2))
end Sets
section Phases
variable {I I' I'' : PeriodicData}
theorem phaseOn_ne_zero (hI : IsPeriodic I) (e : Fin 4 → ℤ) (c : I.UnitQuot) :
    phaseOn I e c ≠ 0 := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolTranslation.phaseOn_ne_zero <;> assumption
theorem phaseMul_comp_quotHomInverse (hI : IsPeriodic I) (e : Fin 4 → ℤ) :
    (phaseMul I e).comp (quotHomInverse (phaseMul I e)) = LinearMap.id := by
  let inv : (I.UnitQuot → ℂ) →ₗ[ℂ] (I.UnitQuot → ℂ) :=
    { toFun := fun f c => (phaseOn I e c)⁻¹ * f c
      map_add' := fun f g => by
        funext c
        simp [mul_add]
      map_smul' := fun z f => by
        funext c
        simp [mul_left_comm] }
  have unit : IsUnit (phaseMul I e : Module.End ℂ (I.UnitQuot → ℂ)) :=
    ⟨⟨phaseMul I e, inv,
      LinearMap.ext fun f => funext fun c => by
        simp [Module.End.mul_apply, phaseMul, inv, phaseOn_ne_zero hI e c],
      LinearMap.ext fun f => funext fun c => by
        simp [Module.End.mul_apply, phaseMul, inv, phaseOn_ne_zero hI e c]⟩,
      rfl⟩
  exact Ring.mul_inverse_cancel _ unit
theorem comp_conj_comp_conj {A A' : QuotHom I I'} {B B' : QuotHom I'' I}
    {P Q : (I.UnitQuot → ℂ) →ₗ[ℂ] (I.UnitQuot → ℂ)}
    {P' : (I'.UnitQuot → ℂ) →ₗ[ℂ] (I'.UnitQuot → ℂ)}
    {P'' : (I''.UnitQuot → ℂ) →ₗ[ℂ] (I''.UnitQuot → ℂ)} (hP : P.comp Q = LinearMap.id)
    (hA : A' = P'.comp (A.comp P)) (hB : B' = Q.comp (B.comp P'')) :
    A'.comp B' = P'.comp ((A.comp B).comp P'') := by
  subst hA hB
  refine LinearMap.ext fun f => ?_
  have h := LinearMap.congr_fun hP (B (P'' f))
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h ⊢
  rw [h]
theorem addTwoPiInt_add (κ p : Fin 4 → ℂ) (e : Fin 4 → ℤ) :
    addTwoPiInt κ e + p = addTwoPiInt (κ + p) e := by
  funext μ
  simp only [addTwoPiInt, Pi.add_apply]
  ring
theorem addTwoPiInt_sub (κ p : Fin 4 → ℂ) (e : Fin 4 → ℤ) :
    addTwoPiInt κ e - p = addTwoPiInt (κ - p) e := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.addTwoPiInt_sub <;> assumption
end Phases
theorem claim_holds : Claim := by
  intro I I' I'' hI hI' hI'' δ p hδ hp
  have : Finite I.UnitQuot := hI.finite_quot
  refine ⟨?_, ?_⟩
  · intro T S _ _ U V hU hV hT hS
    have hW := areNhds_mulDomains hδ hp hU hV
    exact ⟨mulDomains p U V, hW, mulDefinedOn_mulDomains p U V,
      holomorphicOnDomains_mul hW (mulDefinedOn_mulDomains p U V) hT hS⟩
  · intro T S hT hS
    obtain ⟨a00, o00, s00, h00⟩ := hT.holo_f00
    obtain ⟨a10, o10, s10, h10⟩ := hT.holo_f10
    obtain ⟨a01, o01, s01, h01⟩ := hT.holo_f01
    obtain ⟨a11, o11, s11, h11⟩ := hT.holo_f11
    obtain ⟨b00, q00, r00, k00⟩ := hS.holo_f00
    obtain ⟨b10, q10, r10, k10⟩ := hS.holo_f10
    obtain ⟨b01, q01, r01, k01⟩ := hS.holo_f01
    obtain ⟨b11, q11, r11, k11⟩ := hS.holo_f11
    have hU : AreNhds δ p ⟨a00, a10, a01, a11⟩ :=
      ⟨o00, o10, o01, o11, s00, s10, s01, s11⟩
    have hV : AreNhds δ p ⟨b00, b10, b01, b11⟩ :=
      ⟨q00, q10, q01, q11, r00, r10, r01, r11⟩
    have hW := areNhds_mulDomains hδ hp hU hV
    have hol : HolomorphicOnDomains _ (JetQuad.mul p T S) :=
      holomorphicOnDomains_mul hW (mulDefinedOn_mulDomains p _ _)
        (show HolomorphicOnDomains ⟨a00, a10, a01, a11⟩ T from ⟨h00, h10, h01, h11⟩)
        (show HolomorphicOnDomains ⟨b00, b10, b01, b11⟩ S from ⟨k00, k10, k01, k11⟩)
    refine
      { pos_width := hδ
        mem_imStrip := hp
        holo_f00 := ⟨_, hW.isOpen00, hW.strip_subset, hol.1⟩
        holo_f10 := ⟨_, hW.isOpen10, hW.addShift_subset, hol.2.1⟩
        holo_f01 := ⟨_, hW.isOpen01, hW.subShift_subset, hol.2.2.1⟩
        holo_f11 := ⟨_, hW.isOpen11, hW.real_subset, hol.2.2.2⟩
        quasiPeriodic_f00 := ?_
        quasiPeriodic_f10 := ?_
        quasiPeriodic_f01 := ?_
        quasiPeriodic_f11 := ?_ }
    · intro e κ h
      exact comp_conj_comp_conj (phaseMul_comp_quotHomInverse hI e)
        (hT.quasiPeriodic_f00 e κ h) (hS.quasiPeriodic_f00 e κ h)
    · intro e κ h
      have hE := phaseMul_comp_quotHomInverse hI e
      change (T.f10 (addTwoPiInt κ e)).comp (S.f00 (addTwoPiInt κ e)) +
          (T.f00 (addTwoPiInt κ e + p)).comp (S.f10 (addTwoPiInt κ e)) =
        _
      rw [addTwoPiInt_add,
        comp_conj_comp_conj hE (hT.quasiPeriodic_f10 e κ h) (hS.quasiPeriodic_f00 e κ h.1),
        comp_conj_comp_conj hE (hT.quasiPeriodic_f00 e (κ + p) h.2) (hS.quasiPeriodic_f10 e κ h)]
      change _ = (quotHomInverse (phaseMul I' e)).comp
        (((T.f10 κ).comp (S.f00 κ) + (T.f00 (κ + p)).comp (S.f10 κ)).comp
          (phaseMul I'' e))
      simp only [LinearMap.add_comp, LinearMap.comp_add]
    · intro e κ h
      have hE := phaseMul_comp_quotHomInverse hI e
      change (T.f01 (addTwoPiInt κ e)).comp (S.f00 (addTwoPiInt κ e)) +
          (T.f00 (addTwoPiInt κ e - p)).comp (S.f01 (addTwoPiInt κ e)) =
        _
      rw [addTwoPiInt_sub,
        comp_conj_comp_conj hE (hT.quasiPeriodic_f01 e κ h) (hS.quasiPeriodic_f00 e κ h.1),
        comp_conj_comp_conj hE (hT.quasiPeriodic_f00 e (κ - p) h.2) (hS.quasiPeriodic_f01 e κ h)]
      change _ = (quotHomInverse (phaseMul I' e)).comp
        (((T.f01 κ).comp (S.f00 κ) + (T.f00 (κ - p)).comp (S.f01 κ)).comp
          (phaseMul I'' e))
      simp only [LinearMap.add_comp, LinearMap.comp_add]
    · intro e κ h
      have hE := phaseMul_comp_quotHomInverse hI e
      obtain ⟨r, plus, minus⟩ := real_mem_imStrip_two_mul hδ hp h
      have m : κ - p ∈ stripAddShift δ p := ⟨minus, by simpa using r⟩
      have n : κ + p ∈ stripSubShift δ p := ⟨plus, by simpa using r⟩
      change (T.f11 (addTwoPiInt κ e)).comp (S.f00 (addTwoPiInt κ e)) +
          (T.f00 (addTwoPiInt κ e)).comp (S.f11 (addTwoPiInt κ e)) +
          (T.f10 (addTwoPiInt κ e - p)).comp (S.f01 (addTwoPiInt κ e)) +
          (T.f01 (addTwoPiInt κ e + p)).comp (S.f10 (addTwoPiInt κ e)) =
        _
      rw [addTwoPiInt_add, addTwoPiInt_sub,
        comp_conj_comp_conj hE (hT.quasiPeriodic_f11 e κ h) (hS.quasiPeriodic_f00 e κ r),
        comp_conj_comp_conj hE (hT.quasiPeriodic_f00 e κ r) (hS.quasiPeriodic_f11 e κ h),
        comp_conj_comp_conj hE (hT.quasiPeriodic_f10 e (κ - p) m)
          (hS.quasiPeriodic_f01 e κ ⟨r, minus⟩),
        comp_conj_comp_conj hE (hT.quasiPeriodic_f01 e (κ + p) n)
          (hS.quasiPeriodic_f10 e κ ⟨r, plus⟩)]
      change _ = (quotHomInverse (phaseMul I' e)).comp
        (((T.f11 κ).comp (S.f00 κ) + (T.f00 κ).comp (S.f11 κ) +
            (T.f10 (κ - p)).comp (S.f01 κ) + (T.f01 (κ + p)).comp (S.f10 κ)).comp
          (phaseMul I'' e))
      simp only [LinearMap.add_comp, LinearMap.comp_add]
end YangMills.Construction.PeriodicOperators.JetProducts
end
