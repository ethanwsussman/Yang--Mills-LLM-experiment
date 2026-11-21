import YangMills.Construction.EuclideanBorel.PVMFromScalarMeasures
import YangMills.Construction.HilbertSpaces.EnergyMomentumMeasureOfACommutingRepresentationProof
import YangMills.Construction.SpectralMeasures.DeterminingFamilies
import YangMills.Construction.SpectralMeasures.ScalarMeasuresOfAUnitaryRepresentation
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanBorel
open YangMills.Construction.FormsOperators (IsStronglyContUnitaryRep Commutes UnitaryMap)
namespace UnitaryRepSpectral
section Exponentials
variable {n : ℕ}
theorem continuous_expChar (v : Space n) : Continuous (expChar v) := by
  unfold expChar
  fun_prop
theorem continuous_expChar_left (y : Space n) :
    Continuous fun v : Space n => expChar v y := by
  unfold expChar
  fun_prop
theorem norm_expChar (v y : Space n) : ‖expChar v y‖ = 1 := by apply _root_.YangMills.Construction.PositiveFormReconstruction.CommutingJointSpectrum.norm_expChar <;> assumption
theorem expChar_add (v v' y : Space n) :
    expChar (v + v') y = expChar v y * expChar v' y := by
  simp only [expChar, inner_add_left, Complex.ofReal_add, mul_add, Complex.exp_add]
theorem expChar_zero (y : Space n) : expChar 0 y = 1 := by
  simp [expChar]
theorem conj_expChar (v y : Space n) :
    conj (expChar v y) = expChar (-v) y := by
  simp only [expChar, inner_neg_left, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, Complex.ofReal_neg, neg_mul, mul_neg]
theorem expChar_injective :
    Function.Injective (expChar : Space n → Space n → ℂ) := by
  intro v v' h
  by_contra hne
  have hw : v - v' ≠ 0 := sub_ne_zero.mpr hne
  set w := v - v' with hwdef
  set y : Space n := (Real.pi / ‖w‖ ^ 2) • w with hy
  have h1 : expChar w y = -1 := by
    have : inner ℝ w y = Real.pi := by
      rw [hy, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    simp only [expChar, this]
    rw [mul_comm]
    exact Complex.exp_pi_mul_I
  have h2 : expChar v y = expChar w y * expChar v' y := by
    rw [← expChar_add, hwdef, sub_add_cancel]
  have h3 : expChar v' y ≠ 0 := by
    intro h0
    have := norm_expChar v' y
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  rw [h, h1] at h2
  have h4 : (2 : ℂ) * expChar v' y = 0 := by linear_combination h2
  exact h3 ((mul_eq_zero.mp h4).resolve_left two_ne_zero)
end Exponentials
section Operators
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
omit [CompleteSpace H] in
theorem isNull_empty {E : BorelSubset n → H →L[ℂ] H} (hE : IsPVM E) :
    IsNull E ⟨∅, MeasurableSet.empty⟩ := by apply _root_.YangMills.Construction.PositiveFormReconstruction.CommutingJointSpectrum.isNull_empty <;> assumption
omit [CompleteSpace H] in
theorem spectralIntegralIs_apply_eq {E : BorelSubset n → H →L[ℂ] H} {f : Space n → ℂ}
    {B B' : H → H} (h : SpectralIntegralIs E f B) (h' : SpectralIntegralIs E f B') (ψ : H) :
    B ψ = B' ψ := by
  have hψ : ψ ∈ sqIntegrableDomain E f := by
    rw [h.1]
    trivial
  rw [← h.2 ⟨ψ, hψ⟩, ← h'.2 ⟨ψ, hψ⟩]
theorem unitaryRep_of_pvm (hC : FunctionalCalculus.Statement) (hn : 1 ≤ n)
    (E : BorelSubset n → H →L[ℂ] H) (hE : IsPVM E) :
    ∃ V : Space n → UnitaryMap H H, IsStronglyContUnitaryRep V ∧
      ∀ v, SpectralIntegralIs E (expChar v) (V v) := by
  have : NeZero n := ⟨by omega⟩
  have meas : ∀ v : Space n, Measurable (expChar v) := fun v =>
    (continuous_expChar v).measurable
  have rules := fun (v v' : Space n) =>
    hC n n H E hE (expChar v) (expChar v') (meas v) (meas v') 0
  have hoff : ∀ p : Space n → Prop, (∀ y, p y) → HoldsOffNull E p := fun p hp =>
    ⟨⟨∅, MeasurableSet.empty⟩, isNull_empty hE, fun y _ => hp y⟩
  have hU : ∀ v, ∃ U : H ≃ₗᵢ[ℂ] H, SpectralIntegralIs E (expChar v) U := fun v => by
    obtain ⟨U, h, -⟩ := (rules v v).2.2.2.2.1.unitary
      (hoff _ (norm_expChar v))
    exact ⟨U, h⟩
  choose V hV using hU
  have hmul : ∀ v v', V v * V v' = V (v + v') := fun v v' => by
    obtain ⟨B, B', hB, hB', hBB, -⟩ := (rules v v').2.2.2.2.1.mul
      ⟨1, hoff _ fun y => (norm_expChar v y).le⟩
      ⟨1, hoff _ fun y => (norm_expChar v' y).le⟩
    have hfun : (fun y => expChar v y * expChar v' y) =
        expChar (v + v') := by
      funext y
      rw [expChar_add]
    rw [hfun] at hBB
    ext1 ψ
    have h1 : (B * B') ψ = V (v + v') ψ := spectralIntegralIs_apply_eq hBB (hV _) ψ
    have h2 : B' ψ = V v' ψ := spectralIntegralIs_apply_eq hB' (hV _) ψ
    have h3 : B (V v' ψ) = V v (V v' ψ) := spectralIntegralIs_apply_eq hB (hV _) _
    rw [← h1]
    change V v (V v' ψ) = B (B' ψ)
    rw [h2, h3]
  refine ⟨V, ⟨?_, hmul, ?_⟩, hV⟩
  · refine mul_left_cancel (a := V 0) ?_
    rw [hmul, add_zero, mul_one]
  · intro ψ
    rw [continuous_iff_seqContinuous]
    intro vs v hv
    obtain ⟨h, hs, ht⟩ := (rules v v).2.2.2.2.2.2.1 (fun j => expChar (vs j)) 1
      (fun j => meas _) zero_le_one
      (hoff _ fun y => ⟨fun j => (norm_expChar _ _).le,
        ((continuous_expChar_left y).tendsto v).comp hv⟩) ψ
    have hval : (fun j => V (vs j) ψ) =
        fun j => spectralIntegral E (expChar (vs j)) ⟨ψ, hs j⟩ :=
      funext fun j => ((hV _).2 ⟨ψ, hs j⟩).symm
    change Tendsto (fun j => V (vs j) ψ) atTop (𝓝 (V v ψ))
    rw [hval, ← (hV v).2 ⟨ψ, h⟩]
    exact ht
theorem pvm_of_unitaryRep (hD : DeterminingFamiliesStatement)
    (hM : PVMOfDiagonalMeasuresTheorem)
    (hS : ScalarMeasures.ExistsFiniteMeasure) (hn : 1 ≤ n)
    (V : Space n → UnitaryMap H H) (hV : IsStronglyContUnitaryRep V) :
    (∃! E : BorelSubset n → H →L[ℂ] H, IsSpectralMeasureOf V E) ∧
      IsSpectralMeasureOf V (spectralMeasureOf V) ∧
      ∀ B : H →L[ℂ] H, (∀ v, Commutes B ((V v).toContinuousLinearEquiv : H →L[ℂ] H)) →
        ∀ Δ, Commutes B (spectralMeasureOf V Δ) := by
  let X : BorelSubset n := ⟨Set.univ, MeasurableSet.univ⟩
  let M : Set (Space n → ℂ) := Set.range expChar
  let c : M → Space n := fun u => Classical.choose u.2
  have hc : ∀ u : M, expChar (c u) = u.1 := fun u => Classical.choose_spec u.2
  have hc' : ∀ v : Space n, c ⟨expChar v, ⟨v, rfl⟩⟩ = v := fun v =>
    expChar_injective (hc _)
  let ϱ : M → H →L[ℂ] H := fun u => ((V (c u)).toContinuousLinearEquiv : H →L[ℂ] H)
  have hbdd : ∀ u ∈ M, IsBoundedMeasurableFn u := by
    rintro _ ⟨v, rfl⟩
    exact ⟨(continuous_expChar v).measurable, 1,
      fun y => (norm_expChar v y).le⟩
  have hstable : IsStarClosedFamilyOn X M :=
    { eq_zero_off := fun u _ y hy => absurd (Set.mem_univ y) hy
      indicator_one_mem := ⟨0, by funext y; simp [X, expChar_zero]⟩
      mul_mem := by
        rintro _ ⟨v, rfl⟩ _ ⟨v', rfl⟩
        exact ⟨v + v', funext (expChar_add v v')⟩
      star_mem := by
        rintro _ ⟨v, rfl⟩
        exact ⟨-v, funext fun y => (conj_expChar v y).symm⟩ }
  have hdet : SeparatesSupportedMeasures X M := fun ν hν _ h =>
    ((hD.1 n hn).2.2 ν hν).2.2.2 fun v => h _ ⟨v, rfl⟩
  have hstar : IsStarHomOnFamily X M ϱ :=
    { map_indicator_one := fun w hw => by
        have h0 : c w = 0 := by
          refine expChar_injective ?_
          rw [hc, hw]
          funext y
          simp [X, expChar_zero]
        ext1 ψ
        change V (c w) ψ = ψ
        rw [h0, hV.map_zero]
        rfl
      map_mul := fun u u' w hw => by
        have h0 : c w = c u + c u' := by
          refine expChar_injective ?_
          rw [hc, hw]
          funext y
          rw [expChar_add, hc, hc]
        ext1 ψ
        change V (c w) ψ = V (c u) (V (c u') ψ)
        rw [h0, ← hV.map_add]
        rfl
      map_star := fun u w hw φ ψ => by
        have h0 : c w = -c u := by
          refine expChar_injective ?_
          rw [hc, hw]
          funext y
          rw [← conj_expChar, hc]
        change ⟪φ, V (c u) ψ⟫_ℂ = ⟪V (c w) φ, ψ⟫_ℂ
        have h1 : V (c u) (V (c w) φ) = φ := by
          have : V (c u) * V (c w) = 1 := by
            rw [hV.map_add, h0, add_neg_cancel, hV.map_zero]
          exact congrArg (fun T : UnitaryMap H H => T φ) this
        rw [← (V (c u)).inner_map_map (V (c w) φ) ψ, h1] }
  have hscal : HasSupportedDiagonalMeasures X M ϱ := fun ψ => by
    obtain ⟨μ, hfin, h⟩ := hS H n hn V hV ψ
    refine ⟨μ, hfin, fun Δ hΔ => ?_, fun u => ?_⟩
    · have hempty : Δ.1 = ∅ := by simpa [X] using hΔ
      simp [hempty]
    · have := h (c u)
      rw [hc u] at this
      exact this
  have hEq : ∀ E : BorelSubset n → H →L[ℂ] H,
      IsPVMRepresenting X M ϱ E ↔ IsSpectralMeasureOf V E := fun E => by
    constructor
    · rintro ⟨hE, -, hu⟩
      refine ⟨hE, fun v => ?_⟩
      have := hu ⟨expChar v, ⟨v, rfl⟩⟩
      have hval : (ϱ ⟨expChar v, ⟨v, rfl⟩⟩ : H → H) = V v := by
        funext ψ
        change V (c _) ψ = V v ψ
        rw [hc']
      rw [hval] at this
      exact this
    · rintro ⟨hE, hv⟩
      refine ⟨hE, ?_, fun u => ?_⟩
      · have hX : Xᶜ = ⟨∅, MeasurableSet.empty⟩ := Subtype.ext (Set.compl_univ)
        unfold IsSupportedOnPVM
        rw [hX]
        exact isNull_empty hE
      · have := hv (c u)
        rw [hc u] at this
        exact this
  obtain ⟨⟨E, hE, huniq⟩, hcomm⟩ := hM n hn H X M ϱ hbdd hstable hdet hstar hscal
  have hex : ∃! E : BorelSubset n → H →L[ℂ] H, IsSpectralMeasureOf V E :=
    ⟨E, (hEq E).1 hE, fun E' h => huniq E' ((hEq E').2 h)⟩
  have hspec := spectralMeasureOf_spec hex.exists
  exact ⟨hex, hspec, fun B hB Δ => hcomm _ ((hEq _).2 hspec) B (fun u => hB (c u)) Δ⟩
end Operators
theorem spectralCorrespondence_holds (hC : FunctionalCalculus.Statement)
    (hD : DeterminingFamiliesStatement)
    (hM : PVMOfDiagonalMeasuresTheorem)
    (hS : ScalarMeasures.ExistsFiniteMeasure) : UnitaryRep.SpectralCorrespondence := by
  intro H _ _ _ n hn
  exact ⟨fun E hE => unitaryRep_of_pvm hC hn E hE,
    fun V hV => pvm_of_unitaryRep hD hM hS hn V hV⟩
end UnitaryRepSpectral
end YangMills.Construction.EuclideanBorel
