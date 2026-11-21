import YangMills.Construction.PeriodicOperators.MatricesOnATorusInCoordinatesProof
import YangMills.Construction.RunningCouplingSlope.FreeInversesOnASideAreLocalProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open PeriodicOperators
variable {P P' P'' : PeriodicData} {Q Q' Q'' : Type}
private theorem exists_decayRate {K : P'.Carrier → P.Carrier → ℂ} (hK : IsPeriodicKernel P P' K) :
    ∃ δ, IsDecayRate P P' K δ := by apply _root_.YangMills.Construction.PeriodicOperators.TorusAction.exists_decayRate <;> assumption
private theorem compKernel_isPeriodicKernel' (hC : CompClaim)
    (hP : IsPeriodic P) (hP' : IsPeriodic P') (hP'' : IsPeriodic P'')
    {K : P'.Carrier → P.Carrier → ℂ} {H : P.Carrier → P''.Carrier → ℂ}
    (hK : IsPeriodicKernel P P' K) (hH : IsPeriodicKernel P'' P H) :
    IsPeriodicKernel P'' P' (compKernel K H) := by apply _root_.YangMills.SharedProofs.p12760 <;> assumption
private theorem periodized_properties (hP : IsPeriodic P) (hP' : IsPeriodic P')
    (hZ : Periodized.Claim)
    {K : P'.Carrier → P.Carrier → ℂ} (hK : IsPeriodicKernel P P' K) :
    Periodized.Properties P P' K := by
  obtain ⟨δ, hδ⟩ := exists_decayRate hK
  exact hZ P P' hP hP' K δ hK hδ
private def quotientLift {s : ℕ} {q : P.Carrier → Q} (h : IsPeriodicQuotient P q s) : P.QuotMod s → Q :=
  Quot.lift q (by
    rintro x _ ⟨m, rfl⟩
    exact (h.eq_iff_exists_translate x _).2 ⟨m, rfl⟩)
private theorem quotientLift_bijective {s : ℕ} {q : P.Carrier → Q} (h : IsPeriodicQuotient P q s) :
    Function.Bijective (quotientLift h) := by
  constructor
  · intro c c'
    induction c using Quot.ind with
    | mk x =>
      induction c' using Quot.ind with
      | mk x' =>
        intro e
        obtain ⟨m, hm⟩ := (h.eq_iff_exists_translate x x').1 e
        exact Quot.sound ⟨m, hm⟩
  · intro y
    obtain ⟨x, rfl⟩ := h.surjective y
    exact ⟨Quot.mk _ x, rfl⟩
private theorem translate_nsmul_injective (hP : IsPeriodic P) {s : ℕ} (hs : 0 < s) (x : P.Carrier) :
    Function.Injective fun m : Fin 4 → ℤ => P.translate (s • m) x := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.translate_nsmul_injective <;> assumption
private theorem readsKernel_comp (hC : CompClaim)
    (hP : IsPeriodic P) (hP' : IsPeriodic P')
    (hP'' : IsPeriodic P'')
    (hZ : Periodized.Claim)
    (hA : TorusAction.Claim) {q : P.Carrier → Q} {q' : P'.Carrier → Q'}
    {q'' : P''.Carrier → Q''} {s : ℕ} (hs : 0 < s) (hq : IsPeriodicQuotient P q s)
    {K : P'.Carrier → P.Carrier → ℂ} {H : P.Carrier → P''.Carrier → ℂ} {A : Q' → Q → ℂ} {B : Q → Q'' → ℂ}
    (hK : IsPeriodicKernel P P' K) (hH : IsPeriodicKernel P'' P H)
    (h : ReadsKernel q q' s K A) (h' : ReadsKernel q'' q s H B) :
    ReadsKernel q'' q' s (compKernel K H) (compKernel A B) := by
  intro x' x''
  have hKH := compKernel_isPeriodicKernel' hC hP hP' hP'' hK hH
  have h1 := (hA P P' hP hP' s hs K hK).2 P'' hP'' H hH
  have h2 := (periodized_properties hP'' hP' hZ hKH).matrix_entries s hs x' x''
  rw [← h2, h1]
  let e := Equiv.ofBijective _ (quotientLift_bijective hq)
  show ∑' y, A (q' x') y * B y (q'' x'') = ∑' c, _
  rw [← e.tsum_eq]
  refine tsum_congr fun c => ?_
  induction c using Quot.ind with
  | mk x =>
    show A (q' x') (q x) * B (q x) (q'' x'') = _
    rw [h, h', (periodized_properties hP hP' hZ hK).matrix_entries s hs x' x |>.symm,
      (periodized_properties hP'' hP hZ hH).matrix_entries s hs x x'' |>.symm]
    rfl
private theorem readsKernel_exists (hP : IsPeriodic P) (hP' : IsPeriodic P')
    (hZ : Periodized.Claim) {q : P.Carrier → Q} {q' : P'.Carrier → Q'}
    {s : ℕ} (hs : 0 < s) (hq : IsPeriodicQuotient P q s) (hq' : IsPeriodicQuotient P' q' s)
    {K : P'.Carrier → P.Carrier → ℂ} (hK : IsPeriodicKernel P P' K) :
    ∃ A : Q' → Q → ℂ, ReadsKernel q q' s K A := by
  let e := Equiv.ofBijective _ (quotientLift_bijective hq)
  let e' := Equiv.ofBijective _ (quotientLift_bijective hq')
  refine ⟨fun y' y => periodicMatrix P P' K s (e'.symm y') (e.symm y), fun x' x => ?_⟩
  have h1 : e'.symm (q' x') = P'.mkQuot s x' := e'.symm_apply_eq.2 rfl
  have h2 : e.symm (q x) = P.mkQuot s x := e.symm_apply_eq.2 rfl
  show periodicMatrix P P' K s (e'.symm (q' x')) (e.symm (q x)) = _
  rw [h1, h2]
  exact (periodized_properties hP hP' hZ hK).matrix_entries s hs x' x
private theorem readsKernel_id [DecidableEq Q] (hP : IsPeriodic P) {q : P.Carrier → Q}
    {s : ℕ} (hs : 0 < s) (hq : IsPeriodicQuotient P q s) :
    ReadsKernel q q s (idKernel P) fun y y' => if y = y' then 1 else 0 := by
  classical
  intro x' x
  unfold periodization idKernel
  show (if q x' = q x then (1 : ℂ) else 0) = _
  by_cases h : q x' = q x
  · rw [if_pos h]
    obtain ⟨m, hm⟩ := (hq.eq_iff_exists_translate x x').1 h.symm
    rw [tsum_eq_single m]
    · rw [if_pos hm]
    · intro m' hne
      rw [if_neg]
      intro e
      exact hne (translate_nsmul_injective hP hs x (e.symm.trans hm))
  · rw [if_neg h]
    symm
    refine (tsum_congr fun m => if_neg fun e => h ?_).trans tsum_zero
    exact ((hq.eq_iff_exists_translate x x').2 ⟨m, e⟩).symm
theorem kernelMatricesOnSide_holds (hC : CompClaim)
    (hZ : Periodized.Claim)
    (hA : TorusAction.Claim) : KernelMatricesOnSide := by
  intro P P' P'' hP hP' hP'' Q Q' Q'' q q' q'' s hs hq hq' hq''
  refine ⟨fun K H A B hK hH h h' => readsKernel_comp hC hP hP' hP'' hZ hA hs hq hK hH h h',
    fun K hK => readsKernel_exists hP hP' hZ hs hq hq' hK, fun {_} => readsKernel_id hP hs hq⟩
end YangMills.Construction.RunningCouplingSlope
end
