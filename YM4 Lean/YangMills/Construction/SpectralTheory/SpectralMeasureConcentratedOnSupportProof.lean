import YangMills.Construction.SpectralTheory.SpectralMeasureConcentratedOnSupport
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.SpectralTheory
namespace YangMills.Construction.SpectralSupport
variable {n : ℕ} [NeZero n] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
theorem diagonalMeasure_univ_eq (P : ProjectionMeasure n H) (v : H) :
    P.spectralValueMeasure v univ = ENNReal.ofReal (‖v‖ ^ 2) := by
  have hv := P.spectralValueMeasure_apply v ⟨univ, MeasurableSet.univ⟩
  rw [P.map_univ] at hv
  simpa using hv
theorem eq_zero_iff_forall_diagonalMeasure (P : ProjectionMeasure n H) (S : BorelSets n) :
    P S = 0 ↔ ∀ v : H, P.spectralValueMeasure v S.1 = 0 := by
  constructor
  · intro hS v
    rw [P.spectralValueMeasure_apply, hS]
    simp
  · intro hS
    refine ContinuousLinearMap.ext fun v => ?_
    have hv := hS v
    rw [P.spectralValueMeasure_apply, ENNReal.ofReal_eq_zero] at hv
    have hsq : ‖P S v‖ ^ 2 = 0 := le_antisymm hv (by positivity)
    simpa using hsq
theorem eq_zero_iff_forall_diagonal (P : ProjectionMeasure n H) (S : BorelSets n) :
    P S = 0 ↔ ∀ v : H, P.spectralValue v S = 0 := by
  constructor
  · intro hS v
    simp [ProjectionMeasure.spectralValue, hS]
  · intro hS
    refine ContinuousLinearMap.ext fun v => ?_
    have hv := hS v
    rw [P.spectralValue_eq_norm_sq] at hv
    have hsq : ‖P S v‖ ^ 2 = 0 := by exact_mod_cast hv
    simpa using hsq
theorem isNullOn_mono (P : ProjectionMeasure n H) (S T : BorelSets n)
    (hTS : T.1 ⊆ S.1) (hS : P.VanishesOn S) : P.VanishesOn T :=
  (eq_zero_iff_forall_diagonalMeasure P T).2 fun v =>
    measure_mono_null hTS ((eq_zero_iff_forall_diagonalMeasure P S).1 hS v)
theorem isNullOn_countable_iUnion (P : ProjectionMeasure n H) (ι : Type) [Countable ι]
    (S : ι → BorelSets n) (hS : ∀ i, P.VanishesOn (S i)) :
    P.VanishesOn ⟨⋃ i, (S i).1, MeasurableSet.iUnion fun i => (S i).2⟩ :=
  (eq_zero_iff_forall_diagonalMeasure P _).2 fun v =>
    measure_iUnion_null fun i => (eq_zero_iff_forall_diagonalMeasure P (S i)).1 (hS i) v
theorem isNullOn_of_val_eq (P : ProjectionMeasure n H) {S T : BorelSets n} (hST : S.1 = T.1)
    (hS : P.VanishesOn S) : P.VanishesOn T := by
  have hEq : S = T := Subtype.ext hST
  rwa [← hEq]
theorem isNullOn_compl_spectralSupport (P : ProjectionMeasure n H) :
    P.VanishesOn ⟨P.supportᶜ, (ProjectionMeasure.isClosed_support P).measurableSet.compl⟩ := by
  set F : Set (Set (Fin n → ℝ)) := {U | ∃ hU : IsOpen U, P.VanishesOn ⟨U, hU.measurableSet⟩} with hF
  obtain ⟨C, hCc, hCF, hCU⟩ := TopologicalSpace.isOpen_sUnion_countable F fun s hs => hs.1
  have : Countable C := hCc.to_subtype
  have hopen : ∀ c : C, IsOpen c.1 := fun c => (hCF c.2).1
  have hnull := isNullOn_countable_iUnion P C (fun c => ⟨c.1, (hopen c).measurableSet⟩)
    fun c => (hCF c.2).2
  refine isNullOn_of_val_eq P ?_ hnull
  change ⋃ c : C, c.1 = P.supportᶜ
  rw [← sUnion_eq_iUnion, hCU, ProjectionMeasure.support, compl_compl]
theorem isGreatest_compl_spectralSupport_of (P : ProjectionMeasure n H) :
    IsGreatest {U | ∃ hU : IsOpen U, P.VanishesOn ⟨U, hU.measurableSet⟩} P.supportᶜ := by
  refine ⟨⟨(ProjectionMeasure.isClosed_support P).isOpen_compl,
    isNullOn_compl_spectralSupport P⟩, fun U hU => ?_⟩
  rw [ProjectionMeasure.support, compl_compl]
  exact subset_sUnion_of_mem hU
theorem spectralSupport_subset_iff_compl (P : ProjectionMeasure n H) (K : Set (Fin n → ℝ))
    (hK : IsClosed K) : P.support ⊆ K ↔ P ⟨Kᶜ, hK.isOpen_compl.measurableSet⟩ = 0 := by
  constructor
  · intro hsub
    exact isNullOn_mono P _ _ (compl_subset_compl.2 hsub) (isNullOn_compl_spectralSupport P)
  · intro hK0
    have hle := (isGreatest_compl_spectralSupport_of P).2
      (show Kᶜ ∈ _ from ⟨hK.isOpen_compl, hK0⟩)
    exact compl_subset_compl.1 hle
theorem concentratedOnSupportTheorem_proof : ConcentratedOnSupportTheorem := by
  intro n _ H _ _ _ P
  exact
    { isFiniteMeasure := fun v => ⟨by rw [diagonalMeasure_univ_eq]; exact ENNReal.ofReal_lt_top⟩
      spectralValueMeasure_univ := diagonalMeasure_univ_eq P
      eq_zero_iff := eq_zero_iff_forall_diagonal P
      vanishesOn_of_subset := isNullOn_mono P
      vanishesOn_iUnion := isNullOn_countable_iUnion P
      isConcentratedOn_support := isNullOn_compl_spectralSupport P
      isGreatest_compl_support := isGreatest_compl_spectralSupport_of P
      support_subset_iff := spectralSupport_subset_iff_compl P }
end YangMills.Construction.SpectralSupport
