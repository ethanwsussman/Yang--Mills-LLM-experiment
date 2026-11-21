import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.PeriodicOperators.MatricesOnATorusInCoordinatesProof
import YangMills.Construction.PeriodicOperators.NumbersOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.ProductOfLocalOperatorFunctions
import Mathlib
set_option autoImplicit false
open Filter Topology Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
namespace OpFunComp
theorem euclidNormVec_add_le (u v : Fin 4 → ℝ) :
    euclidNormVec (u + v) ≤ euclidNormVec u + euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem isOpen_openPolydisk (l : ℕ) (r : ℝ) :
    IsOpen (openPolydisk (0 : Coordinates.ComplexCoordinates l) r) := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.isOpen_openPolydisk_zero <;> assumption
theorem isHolomorphicIn_scalar_iff {l : ℕ} {O : Set (Coordinates.ComplexCoordinates l)}
    {h : Coordinates.ComplexCoordinates l → ℂ} :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O (fun z _ => h z) ↔
      IsOpen O ∧ ContinuousOn h O ∧ ∀ a ∈ O, ∀ j : Fin l, ∀ᶠ ζ in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ
          (fun ζ : ℂ => h (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) ζ := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.isHolomorphicScalarIn_iff <;> assumption
theorem isHolomorphicIn_linearMap {l l' : ℕ}
    (L : Coordinates.ComplexCoordinates l' →ₗ[ℂ] Coordinates.ComplexCoordinates l) (r : ℝ) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn
      (openPolydisk (0 : Coordinates.ComplexCoordinates l') r) L := by
  refine ⟨isOpen_openPolydisk _ _, (LinearMap.continuous_of_finiteDimensional L).continuousOn,
    fun a _ j => Eventually.of_forall fun ζ => ?_⟩
  have hline : DifferentiableAt ℂ
      (fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) ζ := by fun_prop
  exact (LinearMap.toContinuousLinearMap L).differentiableAt.comp ζ hline
section Values
variable {F : PeriodicData}
def restrictCoords {A B : Set F.Carrier} {l l' : ℕ} (hAB : A ⊆ B) (e : Fin l ≃ A)
    (e' : Fin l' ≃ B) :
    Coordinates.ComplexCoordinates l' →ₗ[ℂ] Coordinates.ComplexCoordinates l :=
  LinearMap.funLeft ℂ ℂ fun j => e'.symm ⟨e j, hAB (e j).2⟩
theorem restrictCoords_fieldValues {A B : Set F.Carrier} {l l' : ℕ} (hAB : A ⊆ B)
    (e : Fin l ≃ A) (e' : Fin l' ≃ B) (ζ : F.Carrier → ℂ) :
    restrictCoords hAB e e' (fieldValues e' ζ) = fieldValues e ζ := by
  funext j
  show ζ ((e' (e'.symm ⟨e j, hAB (e j).2⟩) : B) : F.Carrier) = ζ (e j)
  rw [Equiv.apply_symm_apply]
def HoloInValues {A : Set F.Carrier} {l : ℕ} (e : Fin l ≃ A) (ρ : ℝ)
    (g : (F.Carrier → ℂ) → ℂ) : Prop :=
  ∃ h : Coordinates.ComplexCoordinates l → ℂ,
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1)
      (openPolydisk (0 : Coordinates.ComplexCoordinates l) ρ) (fun z _ => h z) ∧
    ∀ ζ, IsSupBelow F ζ ρ → g ζ = h (fieldValues e ζ)
variable {A : Set F.Carrier} {l : ℕ} {e : Fin l ≃ A} {ρ : ℝ}
theorem HoloInValues.zero : HoloInValues e ρ fun _ => 0 :=
  ⟨fun _ => 0, isHolomorphicIn_scalar_iff.2 ⟨isOpen_openPolydisk _ _, continuousOn_const,
    fun _ _ _ => Eventually.of_forall fun _ => differentiableAt_const _⟩, fun _ _ => rfl⟩
theorem HoloInValues.add {g g' : (F.Carrier → ℂ) → ℂ} (hg : HoloInValues e ρ g)
    (hg' : HoloInValues e ρ g') : HoloInValues e ρ fun ζ => g ζ + g' ζ := by
  obtain ⟨h, hol, hh⟩ := hg
  obtain ⟨h', hol', hh'⟩ := hg'
  rw [isHolomorphicIn_scalar_iff] at hol hol'
  refine ⟨fun z => h z + h' z,
    isHolomorphicIn_scalar_iff.2 ⟨hol.1, hol.2.1.add hol'.2.1, fun a ha j => ?_⟩,
    fun ζ hζ => by
      show g ζ + g' ζ = h _ + h' _
      rw [hh ζ hζ, hh' ζ hζ]⟩
  exact ((hol.2.2 a ha j).and (hol'.2.2 a ha j)).mono fun ζ hz => hz.1.add hz.2
theorem HoloInValues.mul {g g' : (F.Carrier → ℂ) → ℂ} (hg : HoloInValues e ρ g)
    (hg' : HoloInValues e ρ g') : HoloInValues e ρ fun ζ => g ζ * g' ζ := by
  obtain ⟨h, hol, hh⟩ := hg
  obtain ⟨h', hol', hh'⟩ := hg'
  rw [isHolomorphicIn_scalar_iff] at hol hol'
  refine ⟨fun z => h z * h' z,
    isHolomorphicIn_scalar_iff.2 ⟨hol.1, hol.2.1.mul hol'.2.1, fun a ha j => ?_⟩,
    fun ζ hζ => by
      show g ζ * g' ζ = h _ * h' _
      rw [hh ζ hζ, hh' ζ hζ]⟩
  exact ((hol.2.2 a ha j).and (hol'.2.2 a ha j)).mono fun ζ hz => hz.1.mul hz.2
theorem HoloInValues.sum {α : Type} (s : Finset α) {g : α → (F.Carrier → ℂ) → ℂ}
    (hg : ∀ a ∈ s, HoloInValues e ρ (g a)) :
    HoloInValues e ρ fun ζ => ∑ a ∈ s, g a ζ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HoloInValues.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hg b (Finset.mem_insert_of_mem hb))
theorem HoloInValues.widen
    (hHolo : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {B : Set F.Carrier} {l' : ℕ} (hAB : A ⊆ B) (e' : Fin l' ≃ B) {g : (F.Carrier → ℂ) → ℂ}
    (hg : HoloInValues e ρ g) : HoloInValues e' ρ g := by
  obtain ⟨h, hol, hh⟩ := hg
  have hmaps : MapsTo (restrictCoords hAB e e')
      (openPolydisk (0 : Coordinates.ComplexCoordinates l') ρ)
      (openPolydisk (0 : Coordinates.ComplexCoordinates l) ρ) := by
    intro z hz j
    have h1 : ‖z (e'.symm ⟨e j, hAB (e j).2⟩) - (0 : Coordinates.ComplexCoordinates l') _‖ < ρ :=
      hz _
    show ‖z (e'.symm ⟨e j, hAB (e j).2⟩) - (0 : Coordinates.ComplexCoordinates l) j‖ < ρ
    simpa using h1
  refine ⟨fun z => h (restrictCoords hAB e e' z), ?_, fun ζ hζ => ?_⟩
  · exact ((hHolo.1 l _ hol.1).1 1 _ hol).2.2.2.1 l' _ _ (isHolomorphicIn_linearMap _ ρ) hmaps
  · rw [hh ζ hζ]
    exact congrArg h (restrictCoords_fieldValues hAB e e' ζ).symm
end Values
section Composition
variable {F I I' I'' : PeriodicData} {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ}
  {S : (F.Carrier → ℂ) → I.Carrier → I''.Carrier → ℂ} {ρ R R' : ℝ}
theorem isLocalWith_opFunComp
    (hHolo : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hI : IsPeriodic I)
    (hFinF : ∀ (y : InfiniteLattice.AmbientSpace) (ς : ℝ), (nearIndices F y ς).Finite)
    (hFinI : ∀ (y : InfiniteLattice.AmbientSpace) (ς : ℝ), (nearIndices I y ς).Finite)
    (hT : IsLocalWith F I I' T ρ R) (hS : IsLocalWith F I'' I S ρ R')
    (hR' : 0 ≤ R') :
    IsLocalWith F I'' I' (opFunComp T S) ρ (R + R') where
  radius_pos := hT.radius_pos
  vanish_far := by
    intro ζ hζ ι' ι'' hn
    have h0 : ∀ ι, T ζ ι' ι * S ζ ι ι'' = 0 := by
      intro ι
      by_contra hne
      have h1 : euclidNormVec (I.pos ι - I'.pos ι') ≤ R := by
        by_contra h
        exact hne (by rw [hT.vanish_far ζ hζ ι' ι h, zero_mul])
      have h2 : euclidNormVec (I''.pos ι'' - I.pos ι) ≤ R' := by
        by_contra h
        exact hne (by rw [hS.vanish_far ζ hζ ι ι'' h, mul_zero])
      apply hn
      have h3 := euclidNormVec_add_le (I''.pos ι'' - I.pos ι) (I.pos ι - I'.pos ι')
      rw [sub_add_sub_cancel] at h3
      linarith
    show ∑' ι, T ζ ι' ι * S ζ ι ι'' = 0
    simp only [h0, tsum_zero]
  holo_entry := by
    intro ι' ι''
    have := (hFinF (I'.pos ι') (R + R')).to_subtype
    obtain ⟨l, ⟨e⟩⟩ := Finite.exists_equiv_fin (nearIndices F (I'.pos ι') (R + R'))
    have hsum : HoloInValues e.symm ρ fun ζ =>
        ∑ ι ∈ (hFinI (I'.pos ι') R).toFinset, T ζ ι' ι * S ζ ι ι'' := by
      refine HoloInValues.sum _ fun ι hι => ?_
      have hιS : ι ∈ nearIndices I (I'.pos ι') R := (Set.Finite.mem_toFinset _).1 hι
      have hιR : euclidNormVec (I.pos ι - I'.pos ι') ≤ R := hιS
      obtain ⟨l₁, e₁, h₁, hol₁, hh₁⟩ := hT.holo_entry ι' ι
      obtain ⟨l₂, e₂, h₂, hol₂, hh₂⟩ := hS.holo_entry ι ι''
      have hsub₁ : nearIndices F (I'.pos ι') R ⊆ nearIndices F (I'.pos ι') (R + R') :=
        fun κ hκ => by
          have hκ' : euclidNormVec (F.pos κ - I'.pos ι') ≤ R := hκ
          show euclidNormVec (F.pos κ - I'.pos ι') ≤ R + R'
          linarith
      have hsub₂ : nearIndices F (I.pos ι) R' ⊆ nearIndices F (I'.pos ι') (R + R') :=
        fun κ hκ => by
          have hκ' : euclidNormVec (F.pos κ - I.pos ι) ≤ R' := hκ
          show euclidNormVec (F.pos κ - I'.pos ι') ≤ R + R'
          have h3 := euclidNormVec_add_le (F.pos κ - I.pos ι) (I.pos ι - I'.pos ι')
          rw [sub_add_sub_cancel] at h3
          linarith
      have f₁ : HoloInValues e₁ ρ fun ζ => T ζ ι' ι := ⟨h₁, hol₁, hh₁⟩
      have f₂ : HoloInValues e₂ ρ fun ζ => S ζ ι ι'' := ⟨h₂, hol₂, hh₂⟩
      exact (f₁.widen hHolo hsub₁ e.symm).mul (f₂.widen hHolo hsub₂ e.symm)
    obtain ⟨h, hol, hh⟩ := hsum
    refine ⟨l, e.symm, h, hol, fun ζ hζ => ?_⟩
    rw [← hh ζ hζ]
    show ∑' ι, T ζ ι' ι * S ζ ι ι'' = _
    refine tsum_eq_sum fun ι hι => ?_
    have hn : ¬ euclidNormVec (I.pos ι - I'.pos ι') ≤ R := fun h =>
      hι ((Set.Finite.mem_toFinset _).2 (show ι ∈ nearIndices I (I'.pos ι') R from h))
    rw [hT.vanish_far ζ hζ ι' ι hn, zero_mul]
  shift_covariant := by
    intro ζ hζ n ι' ι''
    let E : I.Carrier ≃ I.Carrier :=
      { toFun := I.translate n
        invFun := I.translate (-n)
        left_inv := fun ι => by rw [← hI.translate_add, add_neg_cancel, hI.translate_zero]
        right_inv := fun ι => by rw [← hI.translate_add, neg_add_cancel, hI.translate_zero] }
    show ∑' κ, T (shiftField F n ζ) (I'.translate n ι') κ *
        S (shiftField F n ζ) κ (I''.translate n ι'') = ∑' κ, T ζ ι' κ * S ζ κ ι''
    rw [← E.tsum_eq]
    refine tsum_congr fun κ => ?_
    show T (shiftField F n ζ) (I'.translate n ι') (I.translate n κ) *
        S (shiftField F n ζ) (I.translate n κ) (I''.translate n ι'') = _
    rw [hT.shift_covariant ζ hζ n ι' κ, hS.shift_covariant ζ hζ n κ ι'']
end Composition
theorem localClosed_holds (hKernels : CovariantFiniteRange.Claim)
    (hNumbers : ParameterIndependence.Claim)
    (hHolo : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) : LocalClosed := by
  intro F I I' I'' hF hI hI' hI'' T S hT hS
  obtain ⟨ρ, R, hT⟩ := hT
  obtain ⟨ρ', R', hS⟩ := hS
  have hρ : 0 < min ρ ρ' := lt_min hT.radius_pos hS.radius_pos
  have hT' := (hNumbers F I I' hF hI hI' T ρ R ρ R hT hT).1.1 (min ρ ρ') R hρ
    (min_le_left _ _) le_rfl
  have hS' := (hNumbers F I'' I hF hI'' hI S ρ' R' ρ' R' hS hS).1.1 (min ρ ρ') (max R' 0) hρ
    (min_le_right _ _) (le_max_left _ _)
  exact ⟨min ρ ρ', R + max R' 0,
    isLocalWith_opFunComp hHolo hI (hKernels.1 F hF).1 (hKernels.1 I hI).1 hT' hS'
      (le_max_right _ _)⟩
end OpFunComp
end YangMills.Construction.PeriodicOperators
end
