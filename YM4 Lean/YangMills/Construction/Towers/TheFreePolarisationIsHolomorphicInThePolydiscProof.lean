import YangMills.Construction.PeriodicOperators.WidthsAtWhichJetsAreInvertible
import YangMills.Construction.Towers.IndexSetsArePeriodic
import YangMills.Construction.Towers.TheDeterminantsWithoutConstraint
import YangMills.Construction.Towers.TheFreePolarisationIsHolomorphicInThePolydisc
import YangMills.Construction.Towers.TheResponseSymbolNearTheStripProof
import YangMills.Construction.Towers.TheTwoOperatorFunctions
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.FreePolarizationHolomorphy
open Coordinates
open PeriodicOperators
open PeriodicOperators.LogDetSecondDerivs (descendField)
open PeriodicOperators.StripBound (IsAdmissibleWidth logDetForm)
open PeriodicOperators.InvertibleJetWidths (CoeffsHolomorphicOnInterior)
open BackgroundFieldResponse (responseKernel)
open BackgroundProperties
section Holomorphic
variable {N : ℕ}
theorem isHolomorphicIn_scalar_mono {O O' : Set (ComplexCoordinates N)} {u : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z) (hs : O' ⊆ O)
    (ho : IsOpen O') : ComplexCoordinates.IsHolomorphicIn (N' := 1) O' fun z _ => u z := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_mono <;> assumption
theorem isHolomorphicIn_scalar_congr {O : Set (ComplexCoordinates N)} {u v : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z) (hvu : EqOn v u O) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => v z := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_congr <;> assumption
theorem isHolomorphicIn_scalar_const {O : Set (ComplexCoordinates N)} (ho : IsOpen O) (c : ℂ) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun _ _ => c := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_const <;> assumption
theorem isHolomorphicIn_scalar_add {O : Set (ComplexCoordinates N)} {u v : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z)
    (h' : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => v z) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z + v z := by apply _root_.YangMills.Construction.PeriodicOperators.OpFunAdd.isHolomorphicIn_add <;> assumption
theorem isHolomorphicIn_scalar_mul {O : Set (ComplexCoordinates N)} {u v : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z)
    (h' : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => v z) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z * v z := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_mul <;> assumption
theorem isHolomorphicIn_scalar_sum {J : Type} (s : Finset J) {O : Set (ComplexCoordinates N)}
    (ho : IsOpen O) {u : J → ComplexCoordinates N → ℂ}
    (h : ∀ i ∈ s, ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u i z) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => ∑ i ∈ s, u i z := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_sum <;> assumption
end Holomorphic
theorem eq_sum_smul_single {C : Type} [Fintype C] [DecidableEq C] (f : C → ℂ) :
    f = ∑ c, f c • (Pi.single c 1 : C → ℂ) := by
  funext c'
  simp [Finset.sum_apply, Pi.single_apply]
theorem isHolomorphicIn_logDetForm {F I : PeriodicData} (hfin : Finite F.UnitQuot)
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} {δ : ℝ} {P : Set (ComplexCoordinates 4)}
    (hW : IsAdmissibleWidth F I T δ)
    (hC : CoeffsHolomorphicOnInterior F I T δ) (hP : IsOpen P) (hsub : P ⊆ imStrip δ)
    {a b : (Fin 4 → ℂ) → F.UnitQuot → ℂ}
    (ha : ∀ c, ComplexCoordinates.IsHolomorphicIn (N' := 1) P fun p _ => a p c)
    (hb : ∀ c, ComplexCoordinates.IsHolomorphicIn (N' := 1) P fun p _ => b p c) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) P fun p _ =>
      logDetForm F I T p (a p) (b p) := by
  classical
  have := Fintype.ofFinite F.UnitQuot
  choose g hg hgeq using hC.2
  have hsum := isHolomorphicIn_scalar_sum Finset.univ hP
    (u := fun c p => ∑ c', a p c * b p c' * g c c' p) fun c _ =>
    isHolomorphicIn_scalar_sum Finset.univ hP fun c' _ =>
      isHolomorphicIn_scalar_mul (isHolomorphicIn_scalar_mul (ha c) (hb c'))
        (isHolomorphicIn_scalar_mono (hg c c') (hsub.trans hC.1) hP)
  refine isHolomorphicIn_scalar_congr hsum fun p hp => ?_
  obtain ⟨B, hB⟩ := hW.bilinear p (hsub hp)
  have hcoef : ∀ c c', g c c' p = B (Pi.single c 1) (Pi.single c' 1) := fun c c' => by
    rw [hgeq c c' p (hsub hp), hB]
  simp only [hcoef]
  rw [hB]
  conv_lhs => rw [eq_sum_smul_single (a p), eq_sum_smul_single (b p)]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  ring
theorem tripleAmplitude_mkQuot {L k : ℕ} (hL : 0 < L) (x j : (colourEdges L k 0).UnitQuot → ℂ)
    (m : (colourEdges L k k).UnitQuot → ℂ) (ι : (fieldPeriodicData L k hL).Carrier) :
    tripleAmplitude L k hL x j m ((fieldPeriodicData L k hL).mkQuot 1 ι) =
      tripleIndexFunction L k hL x j m ι := by apply _root_.YangMills.Construction.Tower.ResponseOfFourierMode.tripleAmplitude_mkQuot <;> assumption
theorem isHolomorphicIn_tripleAmplitude {L k : ℕ} (hL : 0 < L) {P : Set (ComplexCoordinates 4)}
    (hP : IsOpen P) {x : (Fin 4 → ℂ) → (colourEdges L k 0).UnitQuot → ℂ}
    (hx : ∀ c, ComplexCoordinates.IsHolomorphicIn (N' := 1) P fun p _ => x p c)
    (c : (fieldPeriodicData L k hL).UnitQuot) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) P fun p _ => tripleAmplitude L k hL (x p) 0 0 c := by
  induction c using Quot.ind with
  | mk ι =>
    obtain ⟨pl, ι₀⟩ := ι
    cases pl
    · refine isHolomorphicIn_scalar_congr (hx ((colourEdges L k 0).mkQuot 1 ι₀)) fun p _ => ?_
      exact tripleAmplitude_mkQuot hL (x p) 0 0 ⟨.background, ι₀⟩
    · refine isHolomorphicIn_scalar_congr (isHolomorphicIn_scalar_const hP 0) fun p _ => ?_
      exact tripleAmplitude_mkQuot hL (x p) 0 0 ⟨.source, ι₀⟩
    · refine isHolomorphicIn_scalar_congr (isHolomorphicIn_scalar_const hP 0) fun p _ => ?_
      exact tripleAmplitude_mkQuot hL (x p) 0 0 ⟨.coarse, ι₀⟩
theorem waveAmplitude_blochWave (I : PeriodicData) (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ) :
    waveAmplitude I κ (blochWave I κ φ) = φ := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.waveAmplitude_blochWave <;> assumption
theorem smul_blochWave (I : PeriodicData) (κ : Fin 4 → ℂ) (z : ℂ) (φ : I.UnitQuot → ℂ) :
    z • blochWave I κ φ = blochWave I κ (z • φ) := by apply _root_.YangMills.Construction.Tower.ResponseSymbolNearStrip.smul_blochWave <;> assumption
theorem backgroundResponseSymbol_axis_eq {L k : ℕ} (hfin : Finite (colourEdges L k k).UnitQuot) {υ : ℝ}
    (hr : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) υ)
    {q : Fin 4 → ℂ} (hq : q ∈ openImStrip υ) (μ : Fin 4)
    (hq' : q ∈ momentumPolydisc stripHalfWidth)
    (hamp : responseAmplitude L k q μ = responseOnAxis L k q μ) :
    backgroundResponseSymbol L k q (axisPauliElement μ 2) = axisField L k q μ := by
  have hwave : applyKernel (responseKernel L k) (planeWaveOfConstant L k q (axisPauliElement μ 2)) =
      blochWave (colourEdges L k 0) q (responseOnAxis L k q μ) := by
    funext ι'
    refine (hr.applyKernel_blochWave q hq _ ι').2.trans ?_
    rw [responseOnAxis]
    exact congrArg (fun φ => blochWave (colourEdges L k 0) q φ ι')
      (linearMapOfEntries_eq_applyKernel _ _).symm
  rw [backgroundResponseSymbol, hwave, smul_blochWave, waveAmplitude_blochWave, axisField_of_mem hq',
    scaledResponseField, hamp]
theorem isPeriodic_disjSum {I I' : PeriodicData} (h : IsPeriodic I)
    (h' : IsPeriodic I') : IsPeriodic (I.disjSum I') where
  translate_zero ι := by
    cases ι with
    | inl i => exact congrArg Sum.inl (h.translate_zero i)
    | inr i => exact congrArg Sum.inr (h'.translate_zero i)
  translate_add m n ι := by
    cases ι with
    | inl i => exact congrArg Sum.inl (h.translate_add m n i)
    | inr i => exact congrArg Sum.inr (h'.translate_add m n i)
  free n ι hn := by
    cases ι with
    | inl i => exact h.free n i (Sum.inl.inj hn)
    | inr i => exact h'.free n i (Sum.inr.inj hn)
  finite_quot := by
    have := h.finite_quot
    have := h'.finite_quot
    let f : I.UnitQuot ⊕ I'.UnitQuot → (I.disjSum I').UnitQuot := Sum.elim
      (Quot.lift (fun i => (I.disjSum I').mkQuot 1 (Sum.inl i)) (by
        rintro i _ ⟨n, rfl⟩
        exact Quot.sound ⟨n, rfl⟩))
      (Quot.lift (fun i => (I.disjSum I').mkQuot 1 (Sum.inr i)) (by
        rintro i _ ⟨n, rfl⟩
        exact Quot.sound ⟨n, rfl⟩))
    refine Finite.of_surjective f fun c => ?_
    induction c using Quot.ind with
    | mk ι =>
      cases ι with
      | inl i => exact ⟨Sum.inl (I.mkQuot 1 i), rfl⟩
      | inr i => exact ⟨Sum.inr (I'.mkQuot 1 i), rfl⟩
  pos_translate n ι := by
    cases ι with
    | inl i => exact h.pos_translate n i
    | inr i => exact h'.pos_translate n i
  finite_components := by
    have := h.finite_components
    have := h'.finite_components
    exact inferInstanceAs (Finite (I.Component ⊕ I'.Component))
  componentOf_translate n ι := by
    cases ι with
    | inl i => exact congrArg Sum.inl (h.componentOf_translate n i)
    | inr i => exact congrArg Sum.inr (h'.componentOf_translate n i)
  weight_pos p := by
    cases p with
    | inl q => exact h.weight_pos q
    | inr q => exact h'.weight_pos q
theorem isOpen_openPolydisc (δ : ℝ) : IsOpen (openPolydisc δ) := by
  have hinter : openPolydisc δ = ⋂ μ : Fin 4, {p : Fin 4 → ℂ | ‖p μ‖ < δ} := by
    ext p
    simp [openPolydisc]
  rw [hinter]
  exact isOpen_iInter_of_finite fun μ => isOpen_lt (by fun_prop) continuous_const
theorem freePolarizationHolomorphic_holds (hDet : UnconstrainedDeterminants.PolarizationLogDetFormula)
    (hWid : InvertibleJetWidths.Claim) (hBack : BackgroundPropertiesHold)
    (hResp : ResponseOperators.Claim) (hTwo : OperatorFunctions.OperatorFunctionsTheorem)
    (hPer : LocalKernels.IndexSetPeriodicity.Statement)
    (hIdx : TowerIndexSets.Claim) : FreePolarizationHolomorphic := by
  intro L hL hs k hk μPlus μMinus
  have hcommon := (hDet L hL hs k hk).1
  obtain ⟨⟨_, _, _, hv, hg⟩, -⟩ := hTwo L hL hs k hk
  have hF : IsPeriodic (fieldPeriodicData L k hL) :=
    ((hPer L hs k).2 (LocalKernels.fieldIndices L k hL)).1
  have hV : IsPeriodic (vectorIndices L k) :=
    isPeriodic_disjSum (hIdx L hs k 0 (Nat.zero_le k)).2.1 (hIdx L hs k k le_rfl).2.1
  have hG : IsPeriodic (ghostIndices L k) :=
    isPeriodic_disjSum (hIdx L hs k 0 (Nat.zero_le k)).1 (hIdx L hs k k le_rfl).1
  obtain ⟨-, -, -, hWv, hCv, -⟩ :=
    (hWid (fieldPeriodicData L k hL) (vectorIndices L k) hF hV (vectorOpFn L k hL) hv).2 stripHalfWidth
      hcommon.1
  obtain ⟨-, -, -, hWg, hCg, -⟩ :=
    (hWid (fieldPeriodicData L k hL) (ghostIndices L k) hF hG (ghostOpFn L k hL) hg).2 stripHalfWidth
      hcommon.2
  have hpos : 0 < stripHalfWidth := hcommon.1.1
  have hP := isOpen_openPolydisc stripHalfWidth
  have hsubClosed : openPolydisc stripHalfWidth ⊆ momentumPolydisc stripHalfWidth :=
    fun p hp μ => (hp μ).le
  have hsub : openPolydisc stripHalfWidth ⊆ imStrip stripHalfWidth :=
    fun p hp μ => (Complex.abs_im_le_norm (p μ)).trans (hp μ).le
  have hback := hBack L hs k hk
  obtain ⟨δ₀, hδ, hresp⟩ := hResp
  have hδe : stripHalfWidth = δ₀ :=
    Part.mem_unique (stripHalfWidth_mem (Part.dom_iff_mem.2 ⟨_, hδ⟩)) hδ
  obtain ⟨υ, hυ, _, hr, _⟩ := (hresp L hs k hk).exists_rate
  have hfin : Finite (colourEdges L k k).UnitQuot :=
    (hIdx L hs k k le_rfl).2.1.finite_quot
  have hstrip : ∀ q ∈ momentumPolydisc stripHalfWidth, q ∈ openImStrip υ := fun q hq ρ => by
    have := (Complex.abs_im_le_norm (q ρ)).trans (hq ρ)
    rw [hδe] at this hpos
    linarith
  have hneg : ∀ p ∈ momentumPolydisc stripHalfWidth, -p ∈ momentumPolydisc stripHalfWidth :=
    fun p hp ρ => by
      simpa using hp ρ
  have hresponse : ∀ q ∈ momentumPolydisc stripHalfWidth, ∀ μ μ' : Fin 4,
      backgroundResponseSymbol L k q (axisPauliElement μ 2) = axisField L k q μ := fun q hq μ μ' =>
    backgroundResponseSymbol_axis_eq hfin hr (hstrip q hq) μ hq
      (hback.on_polydisc q hq μ μ').1.amplitude_eq
  obtain ⟨O, _, hOsub, hnear⟩ := hback.exists_nhds μPlus μMinus
  have hsubO : openPolydisc stripHalfWidth ⊆ O := hsubClosed.trans hOsub
  have hplus : ∀ c, ComplexCoordinates.IsHolomorphicIn (N' := 1) (openPolydisc stripHalfWidth)
      fun p _ => backgroundResponseSymbol L k p (axisPauliElement μPlus 2) c := fun c =>
    isHolomorphicIn_scalar_congr
      (isHolomorphicIn_scalar_mul (isHolomorphicIn_scalar_const hP ((finestMesh L k : ℝ) : ℂ))
        (isHolomorphicIn_scalar_mono (hnear.amplitude_pos.2.2 c) hsubO hP))
      fun p hp => congrFun (hresponse p (hsubClosed hp) μPlus μMinus) c
  have hminus : ∀ c, ComplexCoordinates.IsHolomorphicIn (N' := 1) (openPolydisc stripHalfWidth)
      fun p _ => backgroundResponseSymbol L k (-p) (axisPauliElement μMinus 2) c := fun c =>
    isHolomorphicIn_scalar_congr
      (isHolomorphicIn_scalar_mul (isHolomorphicIn_scalar_const hP ((finestMesh L k : ℝ) : ℂ))
        (isHolomorphicIn_scalar_mono (hnear.amplitude_neg.2.2 c) hsubO hP))
      fun p hp => congrFun (hresponse (-p) (hneg p (hsubClosed hp)) μMinus μPlus) c
  have hA := isHolomorphicIn_tripleAmplitude hL hP
    (x := fun p => backgroundResponseSymbol L k p (axisPauliElement μPlus 2)) hplus
  have hB := isHolomorphicIn_tripleAmplitude hL hP
    (x := fun p => backgroundResponseSymbol L k (-p) (axisPauliElement μMinus 2)) hminus
  have hvec := isHolomorphicIn_logDetForm hF.finite_quot hWv hCv hP hsub hA hB
  have hgho := isHolomorphicIn_logDetForm hF.finite_quot hWg hCg hP hsub hA hB
  have hall := isHolomorphicIn_scalar_add
    (isHolomorphicIn_scalar_mul (isHolomorphicIn_scalar_const hP (-(1 / 2))) hvec) hgho
  have hfun : (Equiv.funUnique (Fin 1) ℂ).symm ∘ freePolarizationEntry L k hL μPlus μMinus =
      fun p _ => freePolarizationEntry L k hL μPlus μMinus p := by
    funext p i
    simp [Equiv.funUnique]
  unfold ComplexVariables.IsHolomorphicScalar
  rw [hfun]
  exact hall
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.FreePolarizationHolomorphy
end
