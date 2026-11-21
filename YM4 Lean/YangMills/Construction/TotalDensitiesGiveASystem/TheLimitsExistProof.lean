import YangMills.Construction.SystemOfAdmissibleConstants.LimitsAlongFirstPassageData
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.TheCouplingsGiveTheWindow
import YangMills.Construction.TotalDensitiesGiveASystem.TheLimitsExist
import YangMills.Construction.TotalDensitiesGiveASystem.TheTopAtTheExpansion
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
open YangMills.Construction.RenormalizationStepParameters YangMills.Construction.SystemsWithFiveBounds
open YangMills.Construction.SystemOfAdmissibleConstants YangMills.Construction.LimitTheorem
open YangMills.Construction.TotalDensitySystem
private def pairSequenceTransfer {L L' : ℕ} {P P' : ℕ+ → ℝ → Prop} (h : L = L') (hP : ∀ K β, P K β → P' K β)
    (Q : PairSequence L P) : PairSequence L' P' := by
  subst h
  exact ⟨Q.cutoff, Q.tendsto_cutoff, Q.coupling, fun j => hP _ _ (Q.pair j), Q.state, Q.isLimit⟩
private theorem pairSequenceTransfer_defines {L L' : ℕ} {P P' : ℕ+ → ℝ → Prop} (h : L = L')
    (hP : ∀ K β, P K β → P' K β) (Q : PairSequence L P) (S : CumulantFamily) :
    (pairSequenceTransfer h hP Q).Defines S ↔ Q.Defines S := by
  subst h
  exact Iff.rfl
private theorem pairSequenceTransfer_subseq {L L' : ℕ} {P P' : ℕ+ → ℝ → Prop} (h : L = L')
    (hP : ∀ K β, P K β → P' K β) (Q : PairSequence L P) (φ : ℕ+ → ℕ+) (hφ : Tendsto φ atTop atTop) :
    pairSequenceTransfer h hP (Q.subseq φ hφ) = (pairSequenceTransfer h hP Q).subseq φ hφ := by
  subst h
  rfl
private theorem pairSequenceTransfer_transfer {L L' : ℕ} {P P' : ℕ+ → ℝ → Prop} (h : L = L')
    (hP : ∀ K β, P K β → P' K β) (hP' : ∀ K β, P' K β → P K β) (Q : PairSequence L' P') :
    pairSequenceTransfer h hP (pairSequenceTransfer h.symm hP' Q) = Q := by
  subst h
  rfl
private theorem le_of_zpow_neg_two_le {g top : ℝ} (hg : 0 < g) (ht : 0 < top)
    (h : top ^ (-2 : ℤ) ≤ g ^ (-2 : ℤ)) : g ≤ top := by
  by_contra hlt
  have h2 : top ^ 2 < g ^ 2 := by nlinarith
  have h3 : (g ^ 2)⁻¹ < (top ^ 2)⁻¹ := inv_strictAnti₀ (by positivity) h2
  have e : ∀ u : ℝ, u ^ (-2 : ℤ) = (u ^ 2)⁻¹ := fun u => by
    rw [zpow_neg]; norm_cast
  rw [e, e] at h
  linarith
theorem subsequenceLimitsExist_holds (hG : TrajectoryCouplingsGiveWindow.Statement)
    (hC : SubsequentialLimitsAlongParameterSequence) (hR : topAtAdmissibleParamsStatement) :
    SubsequenceLimitsExist := by
  refine HoldsAtAdmissibleParameters.mono (HoldsAtAdmissibleParameters.and (hG _ hC) hR) fun T y hDr hA => ?_
  obtain ⟨hl, -, -, -, hw⟩ := hA
  obtain ⟨y₁, fl⟩ := hl (2 * T.B) le_rfl
  obtain ⟨c₅, lam, top, -, -, ht, hg₀, hY⟩ := hw (2 * T.B) le_rfl
  have hϑ₁ : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨one_pos, le_rfl⟩
  obtain ⟨Y, hYs, -, K, hK⟩ := hY 0 1 hϑ₁
  refine ⟨max y₁ (top ^ (-2 : ℤ)), fun g hg hy => ?_⟩
  have h₁ : y₁ ≤ g ^ (-2 : ℤ) := le_trans (le_max_left _ _) hy
  have hgt : g ∈ Ioc 0 top := ⟨hg, le_of_zpow_neg_two_le hg ht (le_trans (le_max_right _ _) hy)⟩
  obtain ⟨-, -, hJ, -⟩ := hg₀ g hgt
  have toPassagePoint : ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β →
      IsFirstPassagePoint (T.stepParameters y) (2 * T.B) g K β := fun K β h => by
    have h' : β ∈ SequencePassage.definedPassageWindow
      (TotalDensityFlow.IsDefinedUpTo (T.stepParameters y)) (2 * T.B) g
      (TotalDensityFlow.coupling (T.stepParameters y)) K := h
    rw [(hJ K).1] at h'
    exact h'
  have toTotal : ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePoint (T.stepParameters y) (2 * T.B) g K β →
      IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β := fun K β h => by
    show β ∈ SequencePassage.definedPassageWindow
      (TotalDensityFlow.IsDefinedUpTo (T.stepParameters y)) (2 * T.B) g
      (TotalDensityFlow.coupling (T.stepParameters y)) K
    rw [(hJ K).1]
    exact h
  obtain ⟨D, hDB, c₂, c₃⟩ := fl g hg h₁
  have hwin : ∀ (K : ℕ+) (β : ℝ), IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β →
      β ∈ D.passageWindow K g := fun K β h => by
    show β ∈ SequencePassage.passageWindow D.shift g D.coupling K
    rw [hDB]
    exact toPassagePoint K β h
  have hP : ∀ K β, Y.IsPair g K β → IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β :=
    fun K β h => toTotal K β ((hYs.isPair_iff g hgt K β).1 h)
  have hP' : ∀ K β, IsFirstPassagePair (T.stepParameters y) (2 * T.B) g K β → Y.IsPair g K β :=
    fun K β h => (hYs.isPair_iff g hgt K β).2 (toPassagePoint K β h)
  obtain ⟨-, k₂, k₃, -⟩ := hK g (by rw [hYs.top_eq]; exact hgt)
  refine ⟨fun m K' β hp hK' => c₃ m K' β (fun j => hwin _ _ (hp j)) hK',
    fun K' m β hp hK' hm => c₂ K' m β (fun j => hwin _ _ (hp j)) hK' hm, ?_, fun Q => ?_⟩
  · obtain ⟨Q, S, hQ⟩ := k₂
    exact ⟨pairSequenceTransfer hYs.side_eq hP Q, S, (pairSequenceTransfer_defines _ _ _ _).2 hQ⟩
  · obtain ⟨φ, hφ, S, hS⟩ := k₃ (pairSequenceTransfer hYs.side_eq.symm hP' Q)
    refine ⟨φ, hφ, S, ?_⟩
    have := (pairSequenceTransfer_defines hYs.side_eq hP _ S).2 hS
    rwa [pairSequenceTransfer_subseq, pairSequenceTransfer_transfer] at this
end YangMills.Construction.TotalDensities
end
