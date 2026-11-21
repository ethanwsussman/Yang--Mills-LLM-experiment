import YangMills.Construction.Continuum.CompactSupportAndTensorsOfSeparatedTuplesProof
import YangMills.Construction.Continuum.LeastSupDistanceOfPointsOfPowersOfFourSpace
import YangMills.Construction.Continuum.TheTwoFamiliesOfSeminormsCompared
import YangMills.Construction.Continuum.TwoFamiliesOfSeminormsOnSchwartzFunctionsProof
import YangMills.Construction.Continuum.TwoLinearSubspacesOfSmoothFunctions
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.ConfigSpace.SeminormBounds
variable {n : ℕ}
theorem one_add_pow_le_two_rpow_mul {k p : ℕ} (hkp : k ≤ p) {a : ℝ} (ha : 0 ≤ a) :
    (1 + a) ^ k ≤ (2 : ℝ) ^ ((k : ℝ) / 2) * (1 + a ^ 2) ^ ((p : ℝ) / 2) := by apply _root_.YangMills.Construction.ConfigurationSpace.SeminormFamilies.one_add_pow_le_rpow_weight <;> assumption
theorem decaySeminorm_le_schwartzSeminorm {k q p : ℕ} (h : max k q ≤ p) (φ : Config n → ℂ) :
    decaySeminorm k q φ ≤ ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2)) * schwartzSeminorm p φ := by
  have hk : k ≤ p := (le_max_left _ _).trans h
  have hq : q ≤ p := (le_max_right _ _).trans h
  unfold decaySeminorm
  refine iSup_le fun α => iSup_le fun hα => iSup_le fun x => ?_
  have hx : 0 ≤ euclidNorm x := Real.sqrt_nonneg _
  have hw : (1 + euclidNorm x) ^ k * ‖iteratedPartial α φ x‖ ≤
      (2 : ℝ) ^ ((k : ℝ) / 2) *
        ((1 + euclidNorm x ^ 2) ^ ((p : ℝ) / 2) * ‖iteratedPartial α φ x‖) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (one_add_pow_le_two_rpow_mul hk hx) (norm_nonneg _)
  calc ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖iteratedPartial α φ x‖)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2) *
          ((1 + euclidNorm x ^ 2) ^ ((p : ℝ) / 2) * ‖iteratedPartial α φ x‖)) :=
        ENNReal.ofReal_le_ofReal hw
    _ = ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2)) * ENNReal.ofReal
          ((1 + euclidNorm x ^ 2) ^ ((p : ℝ) / 2) * ‖iteratedPartial α φ x‖) :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2)) * schwartzSeminorm p φ := by
        refine mul_le_mul_right ?_ _
        unfold schwartzSeminorm
        exact le_iSup_of_le x (le_iSup_of_le α (le_iSup_of_le (hα.trans hq) le_rfl))
def PreservesSmoothSupport (D : (Config n → ℂ) → Config n → ℂ) : Prop :=
  (∀ f, ContDiff ℝ ∞ f → ContDiff ℝ ∞ (D f)) ∧ ∀ f, tsupport (D f) ⊆ tsupport f
theorem PreservesSmoothSupport.comp {D E : (Config n → ℂ) → Config n → ℂ}
    (hD : PreservesSmoothSupport D) (hE : PreservesSmoothSupport E) :
    PreservesSmoothSupport (fun f => D (E f)) :=
  ⟨fun f hf => hD.1 _ (hE.1 f hf), fun f => (hD.2 _).trans (hE.2 f)⟩
theorem PreservesSmoothSupport.iterate {D : (Config n → ℂ) → Config n → ℂ}
    (hD : PreservesSmoothSupport D) (m : ℕ) :
    PreservesSmoothSupport (fun f => D^[m] f) := by
  induction m with
  | zero => exact ⟨fun _ h => h, fun _ => subset_rfl⟩
  | succ m ih =>
    have h : (fun f => D^[m + 1] f) = fun f => D (D^[m] f) := by
      funext f
      exact Function.iterate_succ_apply' D m f
    rw [h]
    exact hD.comp ih
theorem preservesSmoothSupport_coordPartial (i : Fin n) (μ : Fin 4) :
    PreservesSmoothSupport (coordPartial i μ) := by
  refine ⟨fun f hf => ?_, fun f => ?_⟩
  · have h : coordPartial i μ f = fun x => fderiv ℝ f x (Pi.single i (Pi.single μ 1)) := by
      funext x
      exact (((hf.differentiable (by simp)) x).hasFDerivAt.hasLineDerivAt _).lineDeriv
    rw [h]
    exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  · refine closure_minimal (fun x hx => ?_) (isClosed_tsupport f)
    by_contra hxf
    have hz : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 hxf
    apply hx
    show lineDeriv ℝ f x _ = 0
    rw [hz.lineDeriv_eq]
    simp [lineDeriv]
theorem preservesSmoothSupport_iteratedPartial (α : MultiIndex n) :
    PreservesSmoothSupport (iteratedPartial α : (Config n → ℂ) → Config n → ℂ) := by
  have inner : ∀ (i : Fin n) (l : List (Fin 4)), PreservesSmoothSupport (fun f : Config n → ℂ =>
      l.foldr (fun μ g => (coordPartial i μ)^[α i μ] g) f) := by
    intro i l
    induction l with
    | nil => exact ⟨fun _ h => h, fun _ => subset_rfl⟩
    | cons a l ih => exact ((preservesSmoothSupport_coordPartial i a).iterate (α i a)).comp ih
  have outer : ∀ l : List (Fin n), PreservesSmoothSupport (fun f : Config n → ℂ =>
      l.foldr (fun i h => (List.finRange 4).foldr
        (fun μ g => (coordPartial i μ)^[α i μ] g) h) f) := by
    intro l
    induction l with
    | nil => exact ⟨fun _ h => h, fun _ => subset_rfl⟩
    | cons a l ih => exact (inner a _).comp ih
  exact outer _
theorem continuous_euclidNorm : Continuous (euclidNorm : Config n → ℝ) := by apply _root_.YangMills.Construction.ConfigSpace.TensorSupport.continuous_euclidNorm <;> assumption
theorem testFnOffDiag_subset_flatSchwartzSet
    (hc : (diagonalSet n)ᶜ = TestFunctions.injectiveTuples (Fin 4 → ℝ) n) :
    testFnOffDiag n ⊆ flatSchwartzSet n := by
  rintro f ⟨hf, hcs, hsub⟩
  refine ⟨⟨hf, fun k α => ?_⟩, fun α x hx => ?_⟩
  · have hreg := preservesSmoothSupport_iteratedPartial α
    have hd : ContDiff ℝ ∞ (iteratedPartial α f) := hreg.1 f hf
    have hdc : HasCompactSupport (iteratedPartial α f) :=
      IsCompact.of_isClosed_subset hcs (isClosed_tsupport _) (hreg.2 f)
    have hcont : Continuous fun x : Config n =>
        (1 + euclidNorm x) ^ k * ‖iteratedPartial α f x‖ :=
      ((continuous_const.add continuous_euclidNorm).pow k).mul hd.continuous.norm
    have hsupp : HasCompactSupport fun x : Config n =>
        (1 + euclidNorm x) ^ k * ‖iteratedPartial α f x‖ :=
      HasCompactSupport.mul_left hdc.norm
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
    refine lt_of_le_of_lt (iSup_le fun x => ENNReal.ofReal_le_ofReal ?_)
      (ENNReal.ofReal_lt_top (r := C))
    exact (le_abs_self _).trans (hC x)
  · have hxs : x ∉ tsupport f := fun h => by
      have h' : x ∈ (diagonalSet n)ᶜ := hc ▸ hsub h
      exact h' hx
    have hxd : x ∉ tsupport (iteratedPartial α f) :=
      fun h => hxs ((preservesSmoothSupport_iteratedPartial α).2 f h)
    exact image_eq_zero_of_notMem_tsupport hxd
theorem seminormComparison_holds (hLinear : SmoothSubspacesStatement)
    (hLeast : MinSeparation.mainClaim) : seminormComparison := by
  intro n hn
  obtain ⟨-, ⟨hSub, M, hM⟩, -, N, hN⟩ := hLinear n hn
  have hc : (diagonalSet n)ᶜ = TestFunctions.injectiveTuples (Fin 4 → ℝ) n := by
    obtain rfl | h2 : n = 1 ∨ 2 ≤ n := by omega
    · exact hLeast.2.2.1
    · exact (hLeast.1 n h2).2.2.1
  refine ⟨fun k q p h φ _ => decaySeminorm_le_schwartzSeminorm h φ, ⟨fun φ hφ => hφ.1, M ⊓ N, ?_⟩,
    testFnOffDiag_subset_flatSchwartzSet hc⟩
  ext φ
  rw [Submodule.coe_inf, hM, hN]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨h₁, fun α x hx => h₃ x hx α⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, hSub h₁, fun x hx α => h₂ α x hx⟩
end YangMills.Construction.ConfigSpace.SeminormBounds
end
