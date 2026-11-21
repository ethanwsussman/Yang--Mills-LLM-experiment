import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import YangMills.Construction.PeriodicOperators.TransposesOfProductsOfJets
import YangMills.Construction.Towers.BoundsOfTheDiagonalSymbolsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetTranspose
open JetQuad
section Entries
variable {J J' J'' : Type}
theorem linearMapEntry_ofEntries [Finite J] (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
theorem linearMap_ext_of_entry [Finite J] {M M' : (J → ℂ) →ₗ[ℂ] (J' → ℂ)}
    (h : linearMapEntry M = linearMapEntry M') : M = M' := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMap_ext_of_entry <;> assumption
end Entries
section Matrices
variable {I I' I'' : PeriodicData}
theorem linearMapEntry_quotHomTranspose [Finite I'.UnitQuot] (M : QuotHom I I') :
    linearMapEntry (quotHomTranspose M) =
      wTranspose (I.quotWeight 1) (I'.quotWeight 1) (linearMapEntry M) :=
  linearMapEntry_ofEntries _
theorem quotHomTranspose_add [Finite I'.UnitQuot] (M N : QuotHom I I') :
    quotHomTranspose (M + N) = quotHomTranspose M + quotHomTranspose N := by
  apply linearMap_ext_of_entry
  have hsum : ∀ A B : QuotHom I' I, linearMapEntry (A + B) = fun x y =>
      linearMapEntry A x y + linearMapEntry B x y := fun _ _ => rfl
  have hsum' : linearMapEntry (M + N) = fun y x => linearMapEntry M y x + linearMapEntry N y x :=
    rfl
  rw [hsum, linearMapEntry_quotHomTranspose, linearMapEntry_quotHomTranspose,
    linearMapEntry_quotHomTranspose, hsum']
  funext x y
  simp only [wTranspose]
  ring
theorem quotHomTranspose_comp (hK : TransposeCompDiag)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (hI'' : IsPeriodic I'')
    (M : QuotHom I I') (N : QuotHom I'' I) :
    quotHomTranspose (M.comp N) = (quotHomTranspose N).comp (quotHomTranspose M) := by apply _root_.YangMills.Construction.Tower.DiagonalSymbolBounds.quotHomTranspose_comp <;> assumption
theorem quotHomNorm_quotHomTranspose (hQ : Quotients.QuotientTransposeNorm)
    (hI : IsPeriodic I) (hI' : IsPeriodic I') (M : QuotHom I I') :
    quotHomNorm (quotHomTranspose M) = quotHomNorm M := by apply _root_.YangMills.Construction.Tower.DiagonalSymbolBounds.quotHomNorm_quotHomTranspose <;> assumption
end Matrices
theorem iSup_mem_comp_involutive {α : Type} {D : Set α} (g : α → ℝ≥0∞) (L : α → α)
    (hL : ∀ κ ∈ D, L κ ∈ D) (hLL : ∀ κ, L (L κ) = κ) :
    (⨆ κ ∈ D, g (L κ)) = ⨆ κ ∈ D, g κ := by
  refine le_antisymm (iSup₂_le fun κ h => ?_) (iSup₂_le fun κ h => ?_)
  · exact le_iSup₂_of_le (L κ) (hL κ h) le_rfl
  · exact le_iSup₂_of_le (L κ) (hL κ h) (by rw [hLL])
theorem claim_holds (hA : JetArgumentsAndEqualJets)
    (hQ : Quotients.QuotientTransposeNorm) (hK : TransposeCompDiag) : Claim := by
  intro δ p hδ hp I₁ I₂ I₃ h₁ h₂ h₃ T S _ _
  have hr := (hA.1 δ p hδ hp).2.2
  have := h₁.finite_quot
  have := h₂.finite_quot
  have := h₃.finite_quot
  have tc : ∀ (M : QuotHom I₂ I₁) (N : QuotHom I₃ I₂),
      quotHomTranspose (M.comp N) = (quotHomTranspose N).comp (quotHomTranspose M) :=
    fun M N => quotHomTranspose_comp hK h₂ h₁ h₃ M N
  refine ⟨⟨fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_⟩, ?_⟩
  · exact tc _ _
  · have e1 : -κ - p + p = -κ := by abel
    have e2 : -(κ + p) = -κ - p := by abel
    change quotHomTranspose ((T.f10 (-κ - p)).comp (S.f00 (-κ - p)) +
        (T.f00 (-κ - p + p)).comp (S.f10 (-κ - p))) =
      (quotHomTranspose (S.f10 (-κ - p))).comp (quotHomTranspose (T.f00 (-κ))) +
        (quotHomTranspose (S.f00 (-(κ + p)))).comp (quotHomTranspose (T.f10 (-κ - p)))
    rw [quotHomTranspose_add, tc, tc, e1, e2]
    exact add_comm _ _
  · have e1 : -κ + p - p = -κ := by abel
    have e2 : -(κ - p) = -κ + p := by abel
    change quotHomTranspose ((T.f01 (-κ + p)).comp (S.f00 (-κ + p)) +
        (T.f00 (-κ + p - p)).comp (S.f01 (-κ + p))) =
      (quotHomTranspose (S.f01 (-κ + p))).comp (quotHomTranspose (T.f00 (-κ))) +
        (quotHomTranspose (S.f00 (-(κ - p)))).comp (quotHomTranspose (T.f01 (-κ + p)))
    rw [quotHomTranspose_add, tc, tc, e1, e2]
    exact add_comm _ _
  · have e1 : -(κ - p) - p = -κ := by abel
    have e2 : -(κ + p) + p = -κ := by abel
    change quotHomTranspose ((T.f11 (-κ)).comp (S.f00 (-κ)) + (T.f00 (-κ)).comp (S.f11 (-κ)) +
        (T.f10 (-κ - p)).comp (S.f01 (-κ)) + (T.f01 (-κ + p)).comp (S.f10 (-κ))) =
      (quotHomTranspose (S.f11 (-κ))).comp (quotHomTranspose (T.f00 (-κ))) +
        (quotHomTranspose (S.f00 (-κ))).comp (quotHomTranspose (T.f11 (-κ))) +
        (quotHomTranspose (S.f10 (-(κ - p) - p))).comp (quotHomTranspose (T.f01 (-κ + p))) +
        (quotHomTranspose (S.f01 (-(κ + p) + p))).comp (quotHomTranspose (T.f10 (-κ - p)))
    rw [quotHomTranspose_add, quotHomTranspose_add, quotHomTranspose_add, tc, tc, tc, tc, e1, e2]
    abel
  · have hn : ∀ M : QuotHom I₂ I₁, quotHomNorm (quotHomTranspose M) = quotHomNorm M :=
      fun M => quotHomNorm_quotHomTranspose hQ h₂ h₁ M
    have h00 : (⨆ κ ∈ imStrip (2 * δ), quotHomNorm (T.f00 (-κ))) =
        ⨆ κ ∈ imStrip (2 * δ), quotHomNorm (T.f00 κ) :=
      iSup_mem_comp_involutive (fun κ => quotHomNorm (T.f00 κ)) (fun κ => -κ) hr.comp00 neg_neg
    have h10 : (⨆ κ ∈ stripAddShift δ p, quotHomNorm (T.f10 (-κ - p))) =
        ⨆ κ ∈ stripAddShift δ p, quotHomNorm (T.f10 κ) :=
      iSup_mem_comp_involutive (fun κ => quotHomNorm (T.f10 κ)) (fun κ => -κ - p) hr.comp10
        fun κ => by abel
    have h01 : (⨆ κ ∈ stripSubShift δ p, quotHomNorm (T.f01 (-κ + p))) =
        ⨆ κ ∈ stripSubShift δ p, quotHomNorm (T.f01 κ) :=
      iSup_mem_comp_involutive (fun κ => quotHomNorm (T.f01 κ)) (fun κ => -κ + p) hr.comp01
        fun κ => by abel
    have h11 : (⨆ κ ∈ realDualPoints, quotHomNorm (T.f11 (-κ))) =
        ⨆ κ ∈ realDualPoints, quotHomNorm (T.f11 κ) :=
      iSup_mem_comp_involutive (fun κ => quotHomNorm (T.f11 κ)) (fun κ => -κ) hr.comp11 neg_neg
    change (⨆ κ ∈ imStrip (2 * δ), quotHomNorm (quotHomTranspose (T.f00 (-κ)))) +
        (⨆ κ ∈ stripAddShift δ p, quotHomNorm (quotHomTranspose (T.f10 (-κ - p)))) +
        (⨆ κ ∈ stripSubShift δ p, quotHomNorm (quotHomTranspose (T.f01 (-κ + p)))) +
        (⨆ κ ∈ realDualPoints, quotHomNorm (quotHomTranspose (T.f11 (-κ)))) = jetNorm δ p T
    simp only [hn]
    rw [h00, h10, h01, h11]
    rfl
end YangMills.Construction.PeriodicOperators.JetTranspose
end
