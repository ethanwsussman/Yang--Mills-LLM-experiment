import YangMills.Construction.OneLoopLaw.CovarianceOfASymbolProof
import YangMills.Construction.PeriodicOperators.FunctionalDeterminesItsPolarisationSymbol
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators.Tempered.HessianSymbolDetermined
theorem exists_exponent_of_eventuallyForSides {L : ℕ} (hL : 2 ≤ L) {P : ℕ → Prop}
    (h : EventuallyForSides L P) : ∃ k : ℕ, 1 ≤ k ∧ ∀ n, k ≤ n → P n := by apply _root_.YangMills.Construction.OneLoopLaw.SymbolCovariance.eventually_of_eventuallyForSides <;> assumption
theorem imStrip_mono {δ δ' : ℝ} (h : δ' ≤ δ) : imStrip δ' ⊆ imStrip δ :=
  fun _ hz i => (hz i).trans h
theorem eqOn_of_witnesses (hD : YangMills.Construction.PeriodicOperators.DualLatticeDensity.Claim)
    {L : ℕ} (hL : YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L)
    {F : FieldFamily L} {δ δ' : ℝ} {S S' : SymbolArray}
    {e e' : ℕ → ℝ} (w : IsTemperedWitness L F δ S e) (w' : IsTemperedWitness L F δ' S' e')
    (hδ : δ' ≤ δ) (i j : Fin 4) : EqOn (S' i j) (S i j) (imStrip δ') := by
  have hL2 : 2 ≤ L := by
    have := hL.2
    omega
  obtain ⟨k₁, h₁, q₁⟩ := exists_exponent_of_eventuallyForSides hL2 w.err_nonneg
  obtain ⟨k₂, -, q₂⟩ := exists_exponent_of_eventuallyForSides hL2 w'.err_nonneg
  obtain ⟨k₃, -, q₃⟩ := exists_exponent_of_eventuallyForSides hL2 w.approx
  obtain ⟨k₄, -, q₄⟩ := exists_exponent_of_eventuallyForSides hL2 w'.approx
  obtain ⟨U, hU, hanU⟩ := w.analytic
  obtain ⟨U', hU', hanU'⟩ := w'.analytic
  have han := (hanU i j).1
  have han' := (hanU' i j).1
  let D : (Fin 4 → ℂ) → ℂ := fun z => S' i j z - S i j z
  have hsub : imStrip δ' ⊆ U ∩ U' := fun z hz => ⟨hU (imStrip_mono hδ hz), hU' hz⟩
  have hc : ContinuousOn (S i j) U := (continuous_apply (0 : Fin 1)).comp_continuousOn han.2.1
  have hc' : ContinuousOn (S' i j) U' :=
    (continuous_apply (0 : Fin 1)).comp_continuousOn han'.2.1
  have hcontD : ContinuousOn D (U ∩ U') :=
    (hc'.mono inter_subset_right).sub (hc.mono inter_subset_left)
  have hD' : YangMills.Construction.Coordinates.ComplexCoordinates.IsHolomorphicIn (U ∩ U')
      fun (z : YangMills.Construction.Coordinates.ComplexCoordinates 4) (_ : Fin 1) => D z := by
    refine ⟨han.1.inter han'.1, continuousOn_pi.2 fun _ => hcontD, ?_⟩
    intro a ha l
    filter_upwards [han.2.2 a ha.1 l, han'.2.2 a ha.2 l] with ζ h h'
    exact h'.sub h
  have hreal : ∀ y, toComplexVec y ∈ imStrip δ' := fun y i => by
    simpa [toComplexVec] using w'.delta_pos.le
  have hcv : Continuous toComplexVec :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  have hg : Continuous fun y => D (toComplexVec y) :=
    hcontD.comp_continuous hcv fun y => hsub (hreal y)
  let N := max (max k₁ k₂) (max k₃ k₄)
  have hN₁ : k₁ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hN₂ : k₂ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN₃ : k₃ ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hN₄ : k₄ ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
  have hbound : ∀ n, N ≤ n → ∀ p ∈ dualLattice (2 * L ^ n),
      ‖D (toComplexVec p)‖ ≤ e n + e' n := by
    intro n hn p hp
    have a := q₃ n (hN₃.trans hn) p hp 0 0 i j
    have b := q₄ n (hN₄.trans hn) p hp 0 0 i j
    rw [if_pos rfl] at a b
    refine le_trans (le_of_eq ?_) ((norm_sub_le _ _).trans (add_le_add a b))
    congr 1
    simp only [D]
    ring
  have hlim : Tendsto (fun n => e n + e' n) atTop (𝓝 0) := by
    simpa using w.err_tendsto.add w'.err_tendsto
  have key := ((hD L hL).2.2 (fun y => D (toComplexVec y)) N (fun n => e n + e' n) hg
    (h₁.trans hN₁) (fun n hn => add_nonneg (q₁ n (hN₁.trans hn)) (q₂ n (hN₂.trans hn))) hlim
    hbound).2 δ' D w'.delta_pos ⟨U ∩ U', hsub, hD'⟩ (fun _ => rfl)
  intro z hz
  exact sub_eq_zero.1 (key z hz)
theorem claim_holds (hD : YangMills.Construction.PeriodicOperators.DualLatticeDensity.Claim) :
    Claim := by
  intro L hL F _
  have agree : ∀ (δ δ' : ℝ) (S S' : SymbolArray) (e e' : ℕ → ℝ),
      IsTemperedWitness L F δ S e → IsTemperedWitness L F δ' S' e' → δ' ≤ δ →
        ∀ i j, EqOn (S' i j) (S i j) (imStrip δ') :=
    fun _ _ _ _ _ _ w w' h i j => eqOn_of_witnesses hD hL w w' h i j
  refine ⟨agree, ?_⟩
  let Q : (Fin 4 → ℂ) → SymbolArray → Prop :=
    fun z S => ∃ (δ : ℝ) (e : ℕ → ℝ), IsTemperedWitness L F δ S e ∧ z ∈ imStrip δ
  let P : SymbolArray := fun i j z => Classical.epsilon (Q z) i j z
  have sym : IsHessianSymbol L F P := by
    intro δ S e w i j z hz
    have hQ : Q z (Classical.epsilon (Q z)) :=
      Classical.epsilon_spec (p := Q z) ⟨S, δ, e, w, hz⟩
    obtain ⟨δ₁, e₁, w₁, h₁⟩ := hQ
    rcases le_total δ δ₁ with h | h
    · exact (agree δ₁ δ _ S e₁ e w₁ w h i j hz).symm
    · exact agree δ δ₁ S _ e e₁ w w₁ h i j h₁
  refine ⟨P, sym, fun P' hP' i j z hz => ?_⟩
  obtain ⟨δ, S, e, w, hz'⟩ := hz
  exact (hP' δ S e w i j hz').trans (sym δ S e w i j hz').symm
end YangMills.Construction.PeriodicOperators.Tempered.HessianSymbolDetermined
end
