import YangMills.Construction.PeriodicOperators.HolomorphicExtensionOfTheOperationsProof
import YangMills.Construction.PeriodicOperators.PeriodicOperatorsOfFiniteRangeAsLocalOperatorFunctionsProof
import YangMills.Construction.Towers.EntriesOfTheActionAndOfTheCovariantDifferenceProof
import YangMills.Construction.Towers.EntriesOfTheIteratedMaps
import YangMills.Construction.Towers.IteratedMapsReadTheBlocksProof
import YangMills.Construction.Towers.QuotientOfATowerCarriesConfigurationsProof
import YangMills.Construction.Towers.TheEntriesOfTheAveragesAtElementaryFunctions
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IteratedKernelEntries
open PeriodicOperators
open Coordinates Matrices
section EvaluationMaps
open ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
def HolomorphicOnPolydisk (l : ℕ) (ρ : ℝ) (h : ComplexCoordinates l → ℂ) : Prop :=
  ComplexCoordinates.IsHolomorphicIn (N' := 1) (openPolydisk 0 ρ) (fun z _ => h z)
theorem isOpen_openPolydisk_zero (l : ℕ) (ρ : ℝ) :
    IsOpen (openPolydisk (0 : ComplexCoordinates l) ρ) := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.isOpen_openPolydisk_zero <;> assumption
theorem holomorphicOnPolydisk_iff {l : ℕ} {ρ : ℝ} {h : ComplexCoordinates l → ℂ} :
    HolomorphicOnPolydisk l ρ h ↔ ContinuousOn h (openPolydisk 0 ρ) ∧
      ∀ a ∈ openPolydisk (0 : ComplexCoordinates l) ρ, ∀ j : Fin l, ∀ᶠ ζ in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ (fun ζ : ℂ => h (a + ζ • ComplexCoordinates.stdBasisVector j)) ζ := by apply _root_.YangMills.DeltaSharedProofs.p501307 <;> assumption
theorem holomorphicOnPolydisk_const (l : ℕ) (ρ : ℝ) (c : ℂ) :
    HolomorphicOnPolydisk l ρ fun _ => c := by apply _root_.YangMills.Construction.PeriodicOperators.ConstantOpFun.isHolomorphicIn_const <;> assumption
theorem HolomorphicOnPolydisk.add {l : ℕ} {ρ : ℝ} {h h' : ComplexCoordinates l → ℂ}
    (H : HolomorphicOnPolydisk l ρ h) (H' : HolomorphicOnPolydisk l ρ h') :
    HolomorphicOnPolydisk l ρ fun z => h z + h' z := by apply _root_.YangMills.DeltaSharedProofs.p500673 <;> assumption
theorem HolomorphicOnPolydisk.mul {l : ℕ} {ρ : ℝ} {h h' : ComplexCoordinates l → ℂ}
    (H : HolomorphicOnPolydisk l ρ h) (H' : HolomorphicOnPolydisk l ρ h') :
    HolomorphicOnPolydisk l ρ fun z => h z * h' z := by apply _root_.YangMills.DeltaSharedProofs.p501019 <;> assumption
theorem HolomorphicOnPolydisk.mono_radius {l : ℕ} {ρ ρ' : ℝ} {h : ComplexCoordinates l → ℂ}
    (H : HolomorphicOnPolydisk l ρ h) (hρ : ρ' ≤ ρ) : HolomorphicOnPolydisk l ρ' h := by
  obtain ⟨c, d⟩ := holomorphicOnPolydisk_iff.1 H
  have hsub : openPolydisk (0 : ComplexCoordinates l) ρ' ⊆ openPolydisk 0 ρ :=
    fun z hz j => (hz j).trans_le hρ
  exact holomorphicOnPolydisk_iff.2 ⟨c.mono hsub, fun a ha j => d a (hsub ha) j⟩
theorem HolomorphicOnPolydisk.comp_injective {l l' : ℕ} {ρ : ℝ} {h : ComplexCoordinates l → ℂ}
    (H : HolomorphicOnPolydisk l ρ h) {ι : Fin l → Fin l'} (hι : Function.Injective ι) :
    HolomorphicOnPolydisk l' ρ fun z => h fun i => z (ι i) := by
  obtain ⟨c, d⟩ := holomorphicOnPolydisk_iff.1 H
  have hmaps : MapsTo (fun (z : ComplexCoordinates l') (i : Fin l) => z (ι i)) (openPolydisk 0 ρ)
      (openPolydisk 0 ρ) := fun z hz i => hz (ι i)
  have hcont : Continuous fun (z : ComplexCoordinates l') (i : Fin l) => z (ι i) := by fun_prop
  refine holomorphicOnPolydisk_iff.2 ⟨c.comp hcont.continuousOn hmaps, fun a ha j => ?_⟩
  by_cases hj : ∃ i, ι i = j
  · obtain ⟨i, rfl⟩ := hj
    have hEq : ∀ ζ : ℂ, (fun i' => (a + ζ • ComplexCoordinates.stdBasisVector (ι i)) (ι i')) =
        (fun i' => a (ι i')) + ζ • ComplexCoordinates.stdBasisVector i := by
      intro ζ
      funext i'
      simp [ComplexCoordinates.stdBasisVector, Pi.single_apply, hι.eq_iff]
    simp only [hEq]
    exact d _ (hmaps ha) i
  · have hEq : ∀ ζ : ℂ, (fun i' => (a + ζ • ComplexCoordinates.stdBasisVector j) (ι i')) =
        fun i' => a (ι i') := by
      intro ζ
      funext i'
      have hne : ι i' ≠ j := fun h' => hj ⟨i', h'⟩
      simp [ComplexCoordinates.stdBasisVector, hne]
    simp only [hEq]
    exact Eventually.of_forall fun _ => differentiableAt_const _
variable {F : PeriodicData} {ρ : ℝ} {S S' : Set F.Carrier} {g g' : (F.Carrier → ℂ) → ℂ}
theorem exists_equiv_fin_of_finite (hS : S.Finite) : ∃ l : ℕ, Nonempty (Fin l ≃ S) := by
  have : Finite S := hS.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  exact ⟨n, ⟨e.symm⟩⟩
theorem readsHol_along_equiv (H : HolomorphicInValuesBelow F ρ S g) (hS : S ⊆ S') {l' : ℕ}
    (e' : Fin l' ≃ S') : ∃ h' : ComplexCoordinates l' → ℂ, HolomorphicOnPolydisk l' ρ h' ∧
      ∀ ζ, IsSupBelow F ζ ρ → g ζ = h' (fieldValues e' ζ) := by
  obtain ⟨l, e, h, hh, hg⟩ := H
  let ι : Fin l → Fin l' := fun i => e'.symm ⟨e i, hS (e i).2⟩
  have hι : Function.Injective ι := by
    intro i i' hii
    have hsame := e'.symm.injective hii
    exact e.injective (Subtype.ext (Subtype.mk.inj hsame))
  refine ⟨_, HolomorphicOnPolydisk.comp_injective hh hι, fun ζ hζ => ?_⟩
  rw [hg ζ hζ]
  congr 1
  funext i
  simp [fieldValues, ι]
theorem readsHol_mono (H : HolomorphicInValuesBelow F ρ S g) (hS : S ⊆ S') (hf : S'.Finite) :
    HolomorphicInValuesBelow F ρ S' g := by
  obtain ⟨l, ⟨e⟩⟩ := exists_equiv_fin_of_finite hf
  obtain ⟨h, hh, hg⟩ := readsHol_along_equiv H hS e
  exact ⟨l, e, h, hh, hg⟩
theorem readsHol_const (hf : S.Finite) (ρ : ℝ) (c : ℂ) :
    HolomorphicInValuesBelow F ρ S fun _ => c := by
  obtain ⟨l, ⟨e⟩⟩ := exists_equiv_fin_of_finite hf
  exact ⟨l, e, fun _ => c, holomorphicOnPolydisk_const l ρ c, fun _ _ => rfl⟩
theorem readsHol_add (H : HolomorphicInValuesBelow F ρ S g)
    (H' : HolomorphicInValuesBelow F ρ S g') :
    HolomorphicInValuesBelow F ρ S fun ζ => g ζ + g' ζ := by
  obtain ⟨l, e, h, hh, hg⟩ := H
  obtain ⟨h', hh', hg'⟩ := readsHol_along_equiv H' subset_rfl e
  refine ⟨l, e, fun z => h z + h' z, HolomorphicOnPolydisk.add hh hh', fun ζ hζ => ?_⟩
  show g ζ + g' ζ = _
  rw [hg ζ hζ, hg' ζ hζ]
theorem readsHol_mul (H : HolomorphicInValuesBelow F ρ S g)
    (H' : HolomorphicInValuesBelow F ρ S g') :
    HolomorphicInValuesBelow F ρ S fun ζ => g ζ * g' ζ := by
  obtain ⟨l, e, h, hh, hg⟩ := H
  obtain ⟨h', hh', hg'⟩ := readsHol_along_equiv H' subset_rfl e
  refine ⟨l, e, fun z => h z * h' z, HolomorphicOnPolydisk.mul hh hh', fun ζ hζ => ?_⟩
  show g ζ * g' ζ = _
  rw [hg ζ hζ, hg' ζ hζ]
theorem readsHol_sum {α : Type} (hf : S.Finite) (I : Finset α) {G : α → (F.Carrier → ℂ) → ℂ}
    (H : ∀ i ∈ I, HolomorphicInValuesBelow F ρ S (G i)) :
    HolomorphicInValuesBelow F ρ S fun ζ => ∑ i ∈ I, G i ζ := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using readsHol_const hf ρ 0
  | insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact readsHol_add (H i (Finset.mem_insert_self i I))
      (ih fun i' h' => H i' (Finset.mem_insert_of_mem h'))
theorem readsHol_congr (H : HolomorphicInValuesBelow F ρ S g)
    (hg : ∀ ζ, IsSupBelow F ζ ρ → g' ζ = g ζ) : HolomorphicInValuesBelow F ρ S g' := by
  obtain ⟨l, e, h, hh, hgh⟩ := H
  exact ⟨l, e, h, hh, fun ζ hζ => by rw [hg ζ hζ, hgh ζ hζ]⟩
theorem readsHol_radius {ρ' : ℝ} (H : HolomorphicInValuesBelow F ρ S g) (hρ : ρ' ≤ ρ) :
    HolomorphicInValuesBelow F ρ' S g := by
  obtain ⟨l, e, h, hh, hg⟩ := H
  refine ⟨l, e, h, HolomorphicOnPolydisk.mono_radius hh hρ, fun ζ hζ => hg ζ ?_⟩
  obtain ⟨r, hr, hb⟩ := hζ
  exact ⟨r, hr.trans_le hρ, hb⟩
end EvaluationMaps
section Coefficients
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliSum_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_pauliSum (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ v, x v • ComplexMatrix2.pauliFamily v) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem pauliSum_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem pauliCoeff_finsetSum {α : Type} (I : Finset α) (c : α → ℂ) (X : α → ComplexMatrix2)
    (hX : ∀ i ∈ I, X i ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (∑ i ∈ I, c i • X i) = ∑ i ∈ I, c i * pauliCoeff a (X i) := by
  have hEq : ∑ i ∈ I, c i • X i =
      ∑ v, (∑ i ∈ I, c i * pauliCoeff v (X i)) • ComplexMatrix2.pauliFamily v := by
    simp only [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.smul_sum, pauliSum_pauliCoeff (hX i hi)]
  rw [hEq, pauliCoeff_pauliSum]
theorem pauliCoeff_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
end Coefficients
section Geometry
variable {a : ℝ}
theorem finite_points_near (ha : 0 < a) (x : InfiniteLattice.AmbientSpace) (r : ℝ) :
    {s : InfiniteLattice.LatticePoint a |
      ∀ i, |(s : InfiniteLattice.AmbientSpace) i - x i| < r}.Finite := by
  have hbox : (Set.pi univ fun i => Set.Icc ⌊(x i - r) / a⌋ ⌈(x i + r) / a⌉ :
      Set (Fin 4 → ℤ)).Finite := Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine Set.Finite.of_finite_image
    ((hbox.image fun (n : Fin 4 → ℤ) (i : Fin 4) => (n i : ℝ) * a).subset ?_)
    Subtype.val_injective.injOn
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨n, hn⟩ := s.2
  refine ⟨n, fun i _ => ⟨?_, ?_⟩, funext fun i => (hn i).symm⟩
  · have h := abs_lt.1 (hs i)
    rw [hn i] at h
    have hle : (x i - r) / a ≤ (n i : ℝ) := by
      rw [div_le_iff₀ ha]
      linarith [h.1]
    exact Int.cast_le.1 ((Int.floor_le _).trans hle)
  · have h := abs_lt.1 (hs i)
    rw [hn i] at h
    have hle : (n i : ℝ) ≤ (x i + r) / a := by
      rw [le_div_iff₀ ha]
      linarith [h.2]
    exact Int.cast_le.1 (hle.trans (Int.le_ceil _))
theorem finite_links_near (ha : 0 < a) (x : InfiniteLattice.AmbientSpace) (r : ℝ) :
    {b : InfiniteLattice.Link a | ∀ i, |(b.initial : InfiniteLattice.AmbientSpace) i - x i| < r ∧
      |(b.terminal : InfiniteLattice.AmbientSpace) i - x i| < r}.Finite := by
  have hs := finite_points_near ha x r
  refine Set.Finite.of_finite_image ((hs.prod hs).subset ?_)
    (f := fun b : InfiniteLattice.Link a => (b.initial, b.terminal)) ?_
  · rintro _ ⟨b, hb, rfl⟩
    exact ⟨fun i => (hb i).1, fun i => (hb i).2⟩
  · rintro b - b' - e
    simp only [Prod.mk.injEq] at e
    exact InfiniteLattice.Link.ext e.1 e.2
theorem abs_terminal_sub_initial_le (ha : 0 < a) (b : InfiniteLattice.Link a) (i : Fin 4) :
    |(b.terminal : InfiniteLattice.AmbientSpace) i -
      (b.initial : InfiniteLattice.AmbientSpace) i| ≤ a := by
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · have e := congrArg
      (fun s : InfiniteLattice.LatticePoint a => (s : InfiniteLattice.AmbientSpace) i) h
    simp only [AddSubgroup.coe_sub, Pi.sub_apply, InfiniteLattice.axisStep] at e
    rw [e, Pi.single_apply]
    split_ifs <;> simp [abs_of_pos ha, ha.le]
  · have e := congrArg
      (fun s : InfiniteLattice.LatticePoint a => (s : InfiniteLattice.AmbientSpace) i) h
    simp only [AddSubgroup.coe_sub, AddSubgroup.coe_neg, Pi.sub_apply, Pi.neg_apply,
      InfiniteLattice.axisStep] at e
    rw [e, Pi.single_apply]
    split_ifs <;> simp [abs_of_pos ha, ha.le]
theorem abs_sub_centre_lt_of_mem_cubeOfOrder {a' : ℝ} (ha' : 0 < a') {L n : ℕ}
    {y : InfiniteLattice.LatticePoint a} {x : InfiniteLattice.AmbientSpace}
    (hx : x ∈ cubeOfOrder L a' n y) (i : Fin 4) :
    |x i - (y : InfiniteLattice.AmbientSpace) i| < (L : ℝ) ^ n * a' / 2 := by
  obtain ⟨ν, hν, rfl⟩ := hx
  have hEq : ((y : InfiniteLattice.AmbientSpace) + ∑ μ, Pi.single μ ((ν μ : ℝ) * a')) i -
      (y : InfiniteLattice.AmbientSpace) i = (ν i : ℝ) * a' := by
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hEq, abs_mul, abs_of_pos ha']
  have h₁ : (2 : ℝ) * |(ν i : ℝ)| ≤ (L : ℝ) ^ n - 1 := by
    have hν' := hν i
    have h' : ((2 * |ν i| : ℤ) : ℝ) ≤ (((L : ℤ) ^ n - 1 : ℤ) : ℝ) := Int.cast_le.2 hν'
    push_cast at h'
    exact h'
  nlinarith
end Geometry
section OneLattice
variable {a a' : ℝ}
theorem extendOddly_of_pos (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.FullSpace.Translations.extendOddly_of_pos <;> assumption
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (b : InfiniteLattice.Link a) : extendOddly f b.opposite = -extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
end OneLattice
section Spacing
variable {L k j : ℕ}
theorem meshAt_pos (hL : 0 < L) : 0 < meshAt L k j :=
  zpow_pos (by exact_mod_cast hL) _
theorem meshAt_succ (hL : 0 < L) : meshAt L k (j + 1) = (L : ℝ) * meshAt L k j := by apply _root_.YangMills.Construction.Tower.FieldProjection.meshAt_succ <;> assumption
theorem meshAt_eq_pow_mul (hL : 0 < L) : meshAt L k j = (L : ℝ) ^ j * meshAt L k 0 := by
  induction j with
  | zero => simp
  | succ j ih => rw [meshAt_succ hL, ih, pow_succ]; ring
theorem meshAt_self (hL : 0 < L) : meshAt L k k = 1 := by
  simp [meshAt]
theorem basisForm_apply_of_pos (a : Fin 3) (b : PositiveEdge (meshAt L k j))
    {c : Edge L k j} (hc : c.IsPositivelyOriented) :
    (basisForm a b : Edge L k j → ComplexMatrix2) c =
      open Classical in if c = b.1 then ComplexMatrix2.pauliFamily a else 0 := by
  simp [basisForm, extendOddly, hc]
theorem basisForm_mem (hL : 0 < L) (a : Fin 3) (b : PositiveEdge (meshAt L k j)) :
    (basisForm a b : Edge L k j → ComplexMatrix2) ∈ complexEdgeForms (meshAt L k j) := by
  refine ⟨fun c hc => ?_, fun c => extendOddly_opposite (meshAt_pos hL) _ c⟩
  rw [basisForm_apply_of_pos a b hc]
  split_ifs
  · exact pauliFamily_mem_traceless a
  · exact ComplexMatrix2.traceless.zero_mem
end Spacing
section Expansions
theorem map_finsetSum_smul {E α : Type} [AddCommGroup E] [Module ℂ E] (P : Submodule ℂ E)
    (T : E → ComplexMatrix2)
    (hT : ∀ B ∈ P, ∀ B' ∈ P, ∀ z : ℂ, T (B + B') = T B + T B' ∧ T (z • B) = z • T B)
    (I : Finset α) (e : α → E) (he : ∀ i, e i ∈ P) (c : α → ℂ) :
    T (∑ i ∈ I, c i • e i) = ∑ i ∈ I, c i • T (e i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have h := (hT 0 P.zero_mem 0 P.zero_mem 0).2
    simpa using h
  | insert i I hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hm : ∑ i ∈ I, c i • e i ∈ P := P.sum_mem fun i _ => P.smul_mem _ (he i)
    rw [(hT _ (P.smul_mem _ (he i)) _ hm 0).1, (hT _ (he i) _ (he i) (c i)).2, ih]
variable {L k j : ℕ}
theorem eq_sum_basisForm (hL : 0 < L) (T : (Edge L k j → ComplexMatrix2) → ComplexMatrix2)
    (hT : ∀ B ∈ complexEdgeForms (meshAt L k j), ∀ B' ∈ complexEdgeForms (meshAt L k j),
      ∀ z : ℂ, T (B + B') = T B + T B' ∧ T (z • B) = z • T B)
    (R : Finset (PositiveEdge (meshAt L k j)))
    (hR : ∀ B ∈ complexEdgeForms (meshAt L k j), ∀ B' ∈ complexEdgeForms (meshAt L k j),
      (∀ b ∈ R, B b.1 = B' b.1) → T B = T B')
    {B : Edge L k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    T B = ∑ p ∈ (Finset.univ : Finset (Fin 3)) ×ˢ R,
      pauliCoeff p.1 (B p.2.1) • T (basisForm p.1 p.2) := by
  classical
  rw [← map_finsetSum_smul (complexEdgeForms (meshAt L k j)) T hT _
    (fun p : Fin 3 × PositiveEdge (meshAt L k j) => basisForm p.1 p.2)
    (fun p => basisForm_mem hL p.1 p.2)]
  refine hR _ hB _ (Submodule.sum_mem _ fun p _ =>
    Submodule.smul_mem _ _ (basisForm_mem hL p.1 p.2)) fun b hb => ?_
  rw [Finset.sum_apply, Finset.sum_product]
  simp only [Pi.smul_apply, basisForm_apply_of_pos _ _ b.2]
  rw [Finset.sum_comm, Finset.sum_eq_single b]
  · simp only [if_true]
    exact (pauliSum_pauliCoeff (hB.1 b.1 b.2)).symm
  · intro b' _ hne
    have hne' : b.1 ≠ b'.1 := fun e => hne (Subtype.ext e).symm
    simp [hne']
  · exact fun h => absurd hb h
def tracelessVertexFunctions (σ : Type) : Submodule ℂ (σ → ComplexMatrix2) where
  carrier := {l | ∀ x, l x ∈ ComplexMatrix2.traceless}
  add_mem' := fun h h' x => ComplexMatrix2.traceless.add_mem (h x) (h' x)
  zero_mem' := fun _ => ComplexMatrix2.traceless.zero_mem
  smul_mem' := fun c _ h x => ComplexMatrix2.traceless.smul_mem c (h x)
open ElementaryEntries (singleSiteFunction)
theorem singleSiteFunction_mem {σ : Type} (a : Fin 3) (x : σ) :
    singleSiteFunction a x ∈ tracelessVertexFunctions σ := by
  intro y
  simp only [singleSiteFunction]
  split_ifs
  · exact pauliFamily_mem_traceless a
  · exact ComplexMatrix2.traceless.zero_mem
theorem eq_sum_singleSiteFunction {σ : Type} (T : (σ → ComplexMatrix2) → ComplexMatrix2)
    (hT : ∀ l ∈ tracelessVertexFunctions σ, ∀ l' ∈ tracelessVertexFunctions σ, ∀ z : ℂ,
      T (l + l') = T l + T l' ∧ T (z • l) = z • T l)
    (R : Finset σ)
    (hR : ∀ l ∈ tracelessVertexFunctions σ, ∀ l' ∈ tracelessVertexFunctions σ,
      (∀ x ∈ R, l x = l' x) → T l = T l')
    {l : σ → ComplexMatrix2} (hl : l ∈ tracelessVertexFunctions σ) :
    T l = ∑ p ∈ (Finset.univ : Finset (Fin 3)) ×ˢ R,
      pauliCoeff p.1 (l p.2) • T (singleSiteFunction p.1 p.2) := by
  classical
  rw [← map_finsetSum_smul (tracelessVertexFunctions σ) T hT _
    (fun p : Fin 3 × σ => singleSiteFunction p.1 p.2)
    (fun p => singleSiteFunction_mem p.1 p.2)]
  refine hR _ hl _ (Submodule.sum_mem _ fun p _ =>
    Submodule.smul_mem _ _ (singleSiteFunction_mem p.1 p.2)) fun x hx => ?_
  rw [Finset.sum_apply, Finset.sum_product]
  simp only [Pi.smul_apply, singleSiteFunction]
  rw [Finset.sum_comm, Finset.sum_eq_single x]
  · simp only [if_true]
    exact (pauliSum_pauliCoeff (hl x)).symm
  · intro x' _ hne
    simp [hne.symm]
  · exact fun h => absurd hx h
end Expansions
section Maps
open _root_.YangMills.Construction.Tower.SupportOfMeans (DefinedAlike DependsOnlyOn)
open _root_.YangMills.Construction.Tower.SupportOfMeans.Unbounded (baseFields endpointBlocks
  supportEdges HasEndpointsIn meanAt)
open _root_.YangMills.Construction.Tower.AsDifferentials (IsLinearOn)
open _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials (iterRatio iterLogRatio
  iterMean)
variable {L k : ℕ}
def verticesBelow (j : ℕ) (y : Vertex L k j) : Set (Vertex L k 0) :=
  {x | (x : InfiniteLattice.AmbientSpace) ∈ cubeOfOrder L (meshAt L k 0) j y}
def edgesBelow (j : ℕ) (y : Vertex L k j) : Set (Edge L k 0) :=
  {b | b.IsPositivelyOriented ∧ b.initial ∈ verticesBelow j y ∧ b.terminal ∈ verticesBelow j y}
theorem verticesBelow_subset_succ (h₄ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {j : ℕ} (hj : j < k)
    {y : Vertex L k (j + 1)} {x : Vertex L k j}
    (hx : (x : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y) :
    verticesBelow j x ⊆ verticesBelow (j + 1) y := by apply _root_.YangMills.Construction.Tower.FullSpace.ReadsCubes.verticesOfOrder_subset_succ <;> assumption
theorem contourLogDrift_congr (h₄ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {j : ℕ} (hj : j < k)
    (V C C' : Edge L k j → ComplexMatrix2) (y : Vertex L k (j + 1))
    (h : ∀ b : Edge L k j, b.IsPositivelyOriented →
      (b.initial : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y →
      (b.terminal : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y → C b = C' b) :
    contourLogDrift V C y = contourLogDrift V C' y := by apply _root_.YangMills.Construction.Tower.FullSpace.ReadsCubes.contourLogDrift_congr <;> assumption
theorem adjointCubeAverage_congr {j : ℕ} (V : Edge L k j → ComplexMatrix2)
    {l l' : Vertex L k j → ComplexMatrix2} (y : Vertex L k (j + 1))
    (h : ∀ x ∈ cubeVertices L (meshAt L k j) y, l x = l' x) :
    adjointCubeAverage V l y = adjointCubeAverage V l' y := by
  simp only [adjointCubeAverage]
  refine congrArg _ (finsum_mem_congr rfl fun x hx => ?_)
  rw [h x hx]
theorem adjointCubeAverage_zero {j : ℕ} (V : Edge L k j → ComplexMatrix2) :
    adjointCubeAverage V (0 : Vertex L k j → ComplexMatrix2) = 0 := by
  funext y
  simp [adjointCubeAverage, ComplexMatrix2.conjugateBy]
section Iterates
variable (h₄ : BlockPathContourPivotStatement)
  (hRel : CovariantIterRelations)
  (hLin : CovariantStepComplexLinear)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
  (hD : _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials.Requirements L k)
  (hR : _root_.YangMills.Construction.Tower.SupportOfMeans.Unbounded.SideRequirements L k)
  {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
include hRel hL hU in
theorem complexIterDeriv_zero_level {B : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) : complexIterDeriv L k 0 U B = B := by apply _root_.YangMills.Construction.Tower.FullSpace.ReadsCubes.complexIterDeriv_zero_level <;> assumption
include hRel hL hD hR hU in
theorem complexIterDeriv_congr {j : ℕ} (hj : j ≤ k) {c : Edge L k j}
    (hc : c.IsPositivelyOriented) {B B' : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) (hB' : B' ∈ complexEdgeForms (meshAt L k 0))
    (h : ∀ b ∈ supportEdges c, B b = B' b) :
    complexIterDeriv L k j U B c = complexIterDeriv L k j U B' c := by apply _root_.YangMills.Construction.Tower.FullSpace.ReadsCubes.complexIterDeriv_congr <;> assumption
include h₄ hRel hL hk hD hR hU in
theorem iterContourLogDrift_congr : ∀ j ≤ k, ∀ (y : Vertex L k j)
    (B B' : Edge L k 0 → ComplexMatrix2), B ∈ complexEdgeForms (meshAt L k 0) →
    B' ∈ complexEdgeForms (meshAt L k 0) → (∀ b ∈ edgesBelow j y, B b = B' b) →
      iterContourLogDrift L k U j B y = iterContourLogDrift L k U j B' y := by
  intro j
  induction j with
  | zero =>
    intro _ y B B' _ _ _
    rfl
  | succ j ih =>
    intro hj y B B' hB hB' h
    have hj' : j < k := by omega
    simp only [iterContourLogDrift, Pi.add_apply]
    refine congrArg₂ (· + ·) ?_ ?_
    · simp only [adjointCubeAverage]
      refine congrArg _ (finsum_mem_congr rfl fun x hx => ?_)
      have inc := verticesBelow_subset_succ h₄ hL hk hj' (y := y) (x := x) hx
      rw [ih (by omega) x B B' hB hB' fun b hb => h b ⟨hb.1, inc hb.2.1, inc hb.2.2⟩]
    · refine contourLogDrift_congr h₄ hL hk hj' _ _ _ y fun c hc ht hh => ?_
      refine complexIterDeriv_congr hRel hL hD hR hU (by omega) hc hB hB' fun b hb => h b ?_
      have inc₁ := verticesBelow_subset_succ h₄ hL hk hj' (y := y) (x := c.initial) ht
      have inc₂ := verticesBelow_subset_succ h₄ hL hk hj' (y := y) (x := c.terminal) hh
      refine ⟨hb.1, ?_, ?_⟩
      · rcases hb.2.1 with h' | h'
        · exact inc₁ h'
        · exact inc₂ h'
      · rcases hb.2.2 with h' | h'
        · exact inc₁ h'
        · exact inc₂ h'
include hRel hL hD hU in
theorem complexIterDeriv_mem {j : ℕ} (hj : j ≤ k) {B : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) :
    complexIterDeriv L k j U B ∈ complexEdgeForms (meshAt L k j) := by
  have hL0 : 0 < L := by
    have h13 := hL.2
    omega
  cases j with
  | zero =>
    rw [complexIterDeriv_zero_level hRel hL hU hB]
    exact hB
  | succ i =>
    have hS := hD.1 i (by omega) _ (hU.2 i (by omega)) U hU
    refine ⟨fun c hc => hS.mem_iter c hc B hB, fun c => ?_⟩
    unfold complexIterDeriv holLeftDifferential
    exact extendOddly_opposite (meshAt_pos hL0) _ c
include hRel hL hD hU in
theorem complexIterDeriv_linear {j : ℕ} (hj : j ≤ k) :
    IsLinearOn (complexEdgeForms (meshAt L k 0)) (complexIterDeriv L k j U) := by
  cases j with
  | zero =>
    intro B hB B' hB' z
    rw [complexIterDeriv_zero_level hRel hL hU hB, complexIterDeriv_zero_level hRel hL hU hB',
      complexIterDeriv_zero_level hRel hL hU (Submodule.add_mem _ hB hB'),
      complexIterDeriv_zero_level hRel hL hU (Submodule.smul_mem _ z hB)]
    exact ⟨rfl, rfl⟩
  | succ i => exact (hD.1 i (by omega) _ (hU.2 i (by omega)) U hU).linear_iter
include hLin hL in
theorem adjointCubeAverage_linear {j : ℕ} (hj : j < k) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j) {l l' : Vertex L k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (hl' : ∀ x, l' x ∈ ComplexMatrix2.traceless)
    (z : ℂ) :
    adjointCubeAverage V (l + l') = adjointCubeAverage V l + adjointCubeAverage V l' ∧
      adjointCubeAverage V (z • l) = z • adjointCubeAverage V l := by
  have h := (hLin L hL k j hj V hV).2.2.2
  constructor
  · simpa using (h l l' hl hl' 1).2
  · have e := (h l 0 hl (fun _ => ComplexMatrix2.traceless.zero_mem) z).2
    rw [adjointCubeAverage_zero] at e
    simpa using e
include hRel hLin hL hD hU in
theorem iterContourLogDrift_traceless_linear : ∀ j ≤ k,
    (∀ B ∈ complexEdgeForms (meshAt L k 0), ∀ y,
      iterContourLogDrift L k U j B y ∈ ComplexMatrix2.traceless) ∧
      IsLinearOn (complexEdgeForms (meshAt L k 0)) (iterContourLogDrift L k U j) := by
  intro j
  induction j with
  | zero =>
    refine fun _ => ⟨fun _ _ _ => ComplexMatrix2.traceless.zero_mem, fun B _ B' _ z => ?_⟩
    simp [iterContourLogDrift]
  | succ j ih =>
    intro hj
    have hj' : j < k := hj
    obtain ⟨ih₁, ih₂⟩ := ih hj'.le
    have hV := hU.2 j hj'
    have hS := hD.1 j hj' _ hV U hU
    have hQ := complexIterDeriv_linear hRel hL hD hU hj'.le
    have hm := fun {B} => complexIterDeriv_mem hRel hL hD hU hj'.le (B := B)
    refine ⟨fun B hB y => ComplexMatrix2.traceless.add_mem ?_ (hS.mem_contour y _ (hm hB)),
      fun B hB B' hB' z => ⟨?_, ?_⟩⟩
    · exact ((hLin L hL k j hj' _ hV).2.2.1 _ (ih₁ B hB)).2 y
    · simp only [iterContourLogDrift]
      rw [(ih₂ B hB B' hB' 0).1, (hQ B hB B' hB' 0).1,
        (adjointCubeAverage_linear hLin hL hj' hV (ih₁ B hB) (ih₁ B' hB') 0).1,
        (hS.linear_contour _ (hm hB) _ (hm hB') 0).1]
      abel
    · simp only [iterContourLogDrift]
      rw [(ih₂ B hB B' hB' z).2, (hQ B hB B' hB' z).2,
        (adjointCubeAverage_linear hLin hL hj' hV (ih₁ B hB) (ih₁ B hB) z).2,
        (hS.linear_contour _ (hm hB) _ (hm hB) z).2, smul_add]
include hLin hL hU in
theorem iterAdjointCubeAverage_mem_traceless : ∀ j ≤ k, ∀ l : Vertex L k 0 → ComplexMatrix2,
    (∀ x, l x ∈ ComplexMatrix2.traceless) → ∀ y,
      iterAdjointCubeAverage L k U j l y ∈ ComplexMatrix2.traceless := by
  intro j
  induction j with
  | zero => exact fun _ l hl y => hl y
  | succ j ih =>
    intro hj l hl y
    have hj' : j < k := hj
    exact ((hLin L hL k j hj' _ (hU.2 j hj')).2.2.1 _ (ih hj'.le l hl)).2 y
end Iterates
end Maps
section Kernels
open ElementaryEntries (singleSiteFunction)
variable {L k : ℕ}
theorem applyKernel_single {N N' : Type} [DecidableEq N] (T : KernelMatrix N N') (ι : N)
    (ι' : N') : applyKernel T (Pi.single ι 1) ι' = T ι' ι := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applyKernel_single <;> assumption
theorem ofPauliCoeffs_single {σ : Type} [DecidableEq σ] (a : Fin 3) (x y : σ) :
    ofPauliCoeffs (Pi.single (a, x) (1 : ℂ)) y =
      if y = x then ComplexMatrix2.pauliFamily a else 0 := by
  simp only [ofPauliCoeffs]
  by_cases h : y = x
  · subst h
    rw [Finset.sum_eq_single a]
    · simp
    · intro a' _ ha
      have hne : (a', y) ≠ (a, y) := fun e => ha (congrArg Prod.fst e)
      simp [Pi.single_eq_of_ne hne]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun a' _ => ?_
    have hne : (a', y) ≠ (a, x) := fun e => h (congrArg Prod.snd e)
    simp [Pi.single_eq_of_ne hne]
open Classical in
theorem vertexCoordinates_ofCoeffs_single {σ : Type} (a : Fin 3) (x : σ) :
    (vertexCoordinate σ).ofCoeffs (Pi.single (a, x) 1) = singleSiteFunction a x := by
  funext y
  exact ofPauliCoeffs_single a x y
theorem edgePauliCoordinates_ofCoeffs_eq {j : ℕ} (c : (edgePauliCoordinates L k j).Index → ℂ) :
    (edgePauliCoordinates L k j).ofCoeffs c = extendOddly (a := meshAt L k j) fun b =>
      open Classical in if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0 := rfl
open Classical in
theorem edgePauliCoordinates_ofCoeffs_single {j : ℕ} (a : Fin 3) (b : PositiveEdge (meshAt L k j)) :
    (edgePauliCoordinates L k j).ofCoeffs (Pi.single (a, b) 1) = basisForm a b := by
  rw [edgePauliCoordinates_ofCoeffs_eq]
  unfold basisForm
  congr 1
  funext c
  by_cases hc : c.IsPositivelyOriented
  · rw [dif_pos hc]
    refine (@ofPauliCoeffs_single (PositiveEdge (meshAt L k j))
      (fun _ _ => Classical.propDecidable _) a b ⟨c, hc⟩).trans ?_
    by_cases h : c = b.1
    · rw [if_pos h, if_pos (Subtype.ext h)]
    · rw [if_neg h, if_neg fun e => h (congrArg Subtype.val e)]
  · rw [dif_neg hc, if_neg]
    rintro rfl
    exact hc b.2
theorem kernel_apply_of_represents {r r' : PauliComponentsOfSymmetricKernel}
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    {T : KernelMatrix r.Index r'.Index} (h : Represents T (r.mapOnCoeffs r' m)) (ι' : r'.Index)
    (ι : r.Index) : open Classical in
    T ι' ι = r'.coeffs (m (r.ofCoeffs (Pi.single ι 1))) ι' := by
  classical
  have e := congrFun (h (Pi.single ι 1)).2 ι'
  rw [applyKernel_single] at e
  exact e
theorem iterAverageKernel_apply
    (hK : _root_.YangMills.Construction.Tower.ThreeMapKernels.OnFullSpace L k)
    {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k) (a' a : Fin 3)
    (y : Vertex L k k) (x : Vertex L k 0) :
    iterAverageKernel L k U (a', y) (a, x) =
      pauliCoeff a' (iterAdjointCubeAverage L k U k (singleSiteFunction a x) y) := by
  classical
  have e := kernel_apply_of_represents (hK.2.2.2 U hU).2.represents (a', y) (a, x)
  rw [vertexCoordinates_ofCoeffs_single] at e
  exact e
theorem iterCovariantKernel_apply
    (hK : _root_.YangMills.Construction.Tower.ThreeMapKernels.OnFullSpace L k)
    {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k) (a' a : Fin 3)
    (c : PositiveEdge (meshAt L k k)) (b : PositiveEdge (meshAt L k 0)) :
    iterCovariantKernel L k U (a', c) (a, b) =
      pauliCoeff a' (iterCovariantDeriv L k U k (basisForm a b) c.1) := by
  classical
  have e := kernel_apply_of_represents (hK.2.2.2 U hU).1.represents (a', c) (a, b)
  rw [edgePauliCoordinates_ofCoeffs_single] at e
  exact e
theorem edgePauliCoordinates_ofCoeffs_mem (hL : 0 < L) (f : (edgePauliCoordinates L k 0).Index → ℂ) :
    (edgePauliCoordinates L k 0).ofCoeffs f ∈ complexEdgeForms (meshAt L k 0) := by
  rw [edgePauliCoordinates_ofCoeffs_eq]
  refine ⟨fun b hb => ?_, fun b => extendOddly_opposite (meshAt_pos hL) _ b⟩
  rw [extendOddly_of_pos _ hb, dif_pos hb]
  exact pauliSum_mem_traceless _
theorem pauliCoeff_edgeRepresentation_ofCoeffs (f : (edgePauliCoordinates L k 0).Index → ℂ) (a : Fin 3)
    (b : PositiveEdge (meshAt L k 0)) :
    pauliCoeff a ((edgePauliCoordinates L k 0).ofCoeffs f b.1) = f (a, b) := by
  rw [edgePauliCoordinates_ofCoeffs_eq, extendOddly_of_pos _ b.2, dif_pos b.2]
  exact pauliCoeff_pauliSum (fun a' => f (a', b)) a
theorem finite_edgesBelow (hL : 0 < L) (j : ℕ) (y : Vertex L k j) :
    {p : PositiveEdge (meshAt L k 0) | p.1 ∈ edgesBelow j y}.Finite := by
  refine ((finite_links_near (meshAt_pos hL) (y : InfiniteLattice.AmbientSpace)
    ((L : ℝ) ^ j * meshAt L k 0 / 2)).preimage Subtype.val_injective.injOn).subset ?_
  rintro p ⟨-, h₁, h₂⟩
  exact fun i => ⟨abs_sub_centre_lt_of_mem_cubeOfOrder (meshAt_pos hL) h₁ i,
    abs_sub_centre_lt_of_mem_cubeOfOrder (meshAt_pos hL) h₂ i⟩
variable (h₄ : BlockPathContourPivotStatement)
  (hRel : CovariantIterRelations)
  (hLin : CovariantStepComplexLinear)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
  (hD : _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials.Requirements L k)
  (hR : _root_.YangMills.Construction.Tower.SupportOfMeans.Unbounded.SideRequirements L k)
  (hK : _root_.YangMills.Construction.Tower.ThreeMapKernels.OnFullSpace L k)
  {U : Edge L k 0 → ComplexMatrix2} (hU : U ∈ smallIterateFields L k)
include h₄ hRel hLin hL hk hD hR hK hU in
theorem driftKernel_apply (a' a : Fin 3) (y : Vertex L k k)
    (b : PositiveEdge (meshAt L k 0)) :
    driftKernel L k U (a', y) (a, b) =
      pauliCoeff a' (iterContourLogDrift L k U k (basisForm a b) y) := by
  classical
  have hL0 : 0 < L := by
    have h13 := hL.2
    omega
  obtain ⟨hval, hlin⟩ := iterContourLogDrift_traceless_linear hRel hLin hL hD hU k le_rfl
  have hcongr := iterContourLogDrift_congr h₄ hRel hL hk hD hR hU k le_rfl
  let T : KernelMatrix (edgePauliCoordinates L k 0).Index (vertexCoordinate (Vertex L k k)).Index :=
    fun ι' ι => pauliCoeff ι'.1 (iterContourLogDrift L k U k (basisForm ι.1 ι.2) ι'.2)
  let R : Vertex L k k → Finset (PositiveEdge (meshAt L k 0)) :=
    fun y => (finite_edgesBelow hL0 k y).toFinset
  have hzero : ∀ (ι' : (vertexCoordinate (Vertex L k k)).Index) (ι : (edgePauliCoordinates L k 0).Index),
      ι ∉ (Finset.univ : Finset (Fin 3)) ×ˢ R ι'.2 → T ι' ι = 0 := by
    rintro ⟨a', y⟩ ⟨a, b⟩ hι
    have hb : b ∉ R y := fun h => hι (Finset.mem_product.2 ⟨Finset.mem_univ _, h⟩)
    have hb' : b.1 ∉ edgesBelow k y := fun h => hb ((finite_edgesBelow hL0 k y).mem_toFinset.2 h)
    have e := hcongr y (basisForm a b) 0 (basisForm_mem hL0 a b)
      (Submodule.zero_mem _) fun c hc => by
        rw [basisForm_apply_of_pos a b hc.1, if_neg fun e' : c = b.1 => hb' (e' ▸ hc)]
        rfl
    have hz : iterContourLogDrift L k U k 0 = 0 := by
      have h0 := (hlin 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 0).2
      simpa using h0
    show pauliCoeff a' (iterContourLogDrift L k U k (basisForm a b) y) = 0
    rw [e, hz]
    exact pauliCoeff_zero a'
  let M : (Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) → Fin 3 × Vertex L k k → ℂ :=
    (edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (Vertex L k k))
      (iterContourLogDrift L k U k)
  have hrep : Represents T M := by
    intro f
    have hB := edgePauliCoordinates_ofCoeffs_mem (k := k) hL0 f
    have hexp : ∀ ι' : Fin 3 × Vertex L k k,
        M f ι' = ∑ p ∈ (Finset.univ : Finset (Fin 3)) ×ˢ R ι'.2, T ι' p * f p := by
      rintro ⟨a', y⟩
      have E := eq_sum_basisForm hL0 (fun B => iterContourLogDrift L k U k B y)
        (fun B hB B' hB' z =>
          ⟨congrFun (hlin B hB B' hB' z).1 y, congrFun (hlin B hB B' hB' z).2 y⟩)
        (R y)
        (fun B hB B' hB' h => hcongr y B B' hB hB' fun c hc =>
          h ⟨c, hc.1⟩ ((finite_edgesBelow hL0 k y).mem_toFinset.2 hc)) hB
      show pauliCoeff a' (iterContourLogDrift L k U k ((edgePauliCoordinates L k 0).ofCoeffs f) y) = _
      rw [E, pauliCoeff_finsetSum _ _ _ fun p _ => hval _ (basisForm_mem hL0 p.1 p.2) y]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [pauliCoeff_edgeRepresentation_ofCoeffs f p.1 p.2, mul_comm]
      rfl
    refine ⟨fun ι' => ?_, funext fun ι' => ?_⟩
    · refine summable_of_ne_finset_zero (s := (Finset.univ : Finset (Fin 3)) ×ˢ R ι'.2)
        fun ι hι => ?_
      rw [hzero ι' ι hι]
      simp
    · have hs : (∑' ι : Fin 3 × PositiveEdge (meshAt L k 0), T ι' ι * f ι) =
          ∑ p ∈ (Finset.univ : Finset (Fin 3)) ×ˢ R ι'.2, T ι' p * f p :=
        tsum_eq_sum fun ι hι => by rw [hzero ι' ι hι, zero_mul]
      exact hs.trans (hexp ι').symm
  have hspec : Represents (kernelOfMap M) M :=
    Classical.epsilon_spec (p := fun T' => Represents T' M) ⟨T, hrep⟩
  have e : driftKernel L k U = T :=
    (hK.1 0 k (Nat.zero_le _) le_rfl).2.2.1 M _ _ hspec hrep
  rw [e]
end Kernels
section SeriesExpansions
open ElementaryEntries (singleSiteFunction EdgeEntries)
open FieldValueFunctions (backgroundCoords)
open _root_.YangMills.Construction.Tower.SupportOfMeans.Unbounded (supportEdges endpointBlocks)
variable {L k : ℕ}
theorem finite_backgroundCoords (hL : 0 < L) {S : Set (Edge L k 0)} (hS : S.Finite) :
    (backgroundCoords L k hL S).Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldValueFunctions.LocalComponents.backgroundCoords_finite <;> assumption
theorem backgroundCoords_mono (hL : 0 < L) {S S' : Set (Edge L k 0)} (h : S ⊆ S') :
    backgroundCoords L k hL S ⊆ backgroundCoords L k hL S' := by
  rintro _ ⟨a, b, hb, rfl⟩
  exact ⟨a, b, h hb, rfl⟩
theorem finite_edgesNear (hL : 0 < L) (x : InfiniteLattice.AmbientSpace) (r : ℝ) :
    (edgesNear L k x r).Finite :=
  finite_links_near (meshAt_pos hL) x r
theorem edgesNear_mono {x x' : InfiniteLattice.AmbientSpace} {r r' : ℝ}
    (h : ∀ i, |x i - x' i| + r ≤ r') : edgesNear L k x r ⊆ edgesNear L k x' r' := by
  intro b hb i
  obtain ⟨h₁, h₂⟩ := hb i
  exact ⟨by linarith [abs_sub_le ((b.initial : InfiniteLattice.AmbientSpace) i) (x i) (x' i), h i],
    by linarith [abs_sub_le ((b.terminal : InfiniteLattice.AmbientSpace) i) (x i) (x' i), h i]⟩
theorem abs_sub_initial_lt_of_mem_endpointBlocks (hL : 0 < L) {u : ℕ} (c : Edge L k u)
    {p : InfiniteLattice.AmbientSpace} (hp : p ∈ endpointBlocks c) (i : Fin 4) :
    |p i - (c.initial : InfiniteLattice.AmbientSpace) i| < 3 / 2 * meshAt L k u := by
  have e : (L : ℝ) ^ u * meshAt L k 0 = meshAt L k u := (meshAt_eq_pow_mul hL).symm
  have hu := meshAt_pos (k := k) (j := u) hL
  rcases hp with hp | hp
  · have h := abs_sub_centre_lt_of_mem_cubeOfOrder (meshAt_pos hL) hp i
    rw [e] at h
    linarith
  · have h := abs_sub_centre_lt_of_mem_cubeOfOrder (meshAt_pos hL) hp i
    rw [e] at h
    linarith [abs_sub_le (p i) ((c.terminal : InfiniteLattice.AmbientSpace) i)
      ((c.initial : InfiniteLattice.AmbientSpace) i), abs_terminal_sub_initial_le hu c i]
theorem supportEdges_subset_edgesNear (hL : 0 < L) {u : ℕ} (c : Edge L k u) :
    supportEdges c ⊆ edgesNear L k c.initial (3 / 2 * meshAt L k u) :=
  fun _ hb i => ⟨abs_sub_initial_lt_of_mem_endpointBlocks hL c hb.2.1 i,
    abs_sub_initial_lt_of_mem_endpointBlocks hL c hb.2.2 i⟩
theorem abs_sub_lt_of_mem_cube (hL : 0 < L) {j : ℕ} {y : Vertex L k (j + 1)}
    {x : InfiniteLattice.AmbientSpace} (hx : x ∈ cube L (meshAt L k j) y) (i : Fin 4) :
    |x i - (y : InfiniteLattice.AmbientSpace) i| < meshAt L k (j + 1) / 2 := by
  have h := abs_sub_centre_lt_of_mem_cubeOfOrder (meshAt_pos hL) hx i
  rwa [pow_one, ← meshAt_succ hL] at h
def axisZeroLink {a : ℝ} (y : InfiniteLattice.LatticePoint a) : InfiniteLattice.Link a :=
  InfiniteLattice.Link.forwardFrom y 0
theorem axisZeroLink_isPositivelyOriented {a : ℝ} (y : InfiniteLattice.LatticePoint a) :
    (axisZeroLink y).IsPositivelyOriented :=
  ⟨0, add_sub_cancel_left _ _⟩
abbrev coeffField (hL : 0 < L) (f : (fieldPeriodicData L k hL).Carrier → ℂ) :
    Edge L k 0 → ComplexMatrix2 :=
  FieldValueFunctions.gaugeFieldOfCoeffs hL f
structure RowLocality (hL : 0 < L) (ρ : ℝ) (j : ℕ) (y : Vertex L k j) : Prop where
  averageEntry : ∀ (a' a : Fin 3) (x : Vertex L k 0),
    HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
    (backgroundCoords L k hL (edgesNear L k y (2 * meshAt L k j)))
    fun f => pauliCoeff a' (iterAdjointCubeAverage L k (coeffField hL f) j
      (singleSiteFunction a x) y)
  driftRow : ∀ (a' a : Fin 3) (b : PositiveEdge (meshAt L k 0)),
    HolomorphicInValuesBelow (fieldPeriodicData L k hL) ρ
    (backgroundCoords L k hL (edgesNear L k y (2 * meshAt L k j)))
    fun f => pauliCoeff a' (iterContourLogDrift L k (coeffField hL f) j
      (basisForm a b) y)
section Step
variable (h₄ : BlockPathContourPivotStatement)
  (hRel : CovariantIterRelations)
  (hLin : CovariantStepComplexLinear)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
  (hD : _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials.Requirements L k)
  (hL0 : 0 < L) {ρ : ℝ}
  (hSm : ∀ f, IsSupBelow (fieldPeriodicData L k hL0) f ρ →
    coeffField hL0 f ∈ smallIterateFields L k)
  (hE : ∀ i < k, ∀ c : Edge L k (i + 1), c.IsPositivelyOriented → EdgeEntries L k hL0 ρ c)
include hRel hL hSm hE in
theorem complexIterDeriv_entries_holomorphic {j : ℕ} (hj : j ≤ k)
    (b' : PositiveEdge (meshAt L k j)) (a'' a : Fin 3) (b : PositiveEdge (meshAt L k 0)) :
    HolomorphicInValuesBelow (fieldPeriodicData L k hL0) ρ
      (backgroundCoords L k hL0 (edgesNear L k b'.1.initial (3 / 2 * meshAt L k j)))
      fun f => pauliCoeff a'' (complexIterDeriv L k j (coeffField hL0 f)
        (basisForm a b) b'.1) := by
  have hf := finite_backgroundCoords hL0
    (finite_edgesNear (k := k) hL0 b'.1.initial (3 / 2 * meshAt L k j))
  cases j with
  | zero =>
    refine readsHol_congr (readsHol_const hf ρ (pauliCoeff a'' (basisForm a b b'.1)))
      fun f hf' => ?_
    rw [complexIterDeriv_zero_level hRel hL (hSm f hf') (basisForm_mem hL0 a b)]
  | succ i =>
    exact readsHol_mono ((hE i hj b'.1 b'.2).iterDeriv_entries a'' a b)
      (backgroundCoords_mono hL0 (supportEdges_subset_edgesNear hL0 b'.1)) hf
include hLin hL hSm hE in
theorem readsHol_adjointCubeAverage {j : ℕ} (hj : j < k) (y : Vertex L k (j + 1))
    {S : Set (fieldPeriodicData L k hL0).Carrier} (hS : S.Finite)
    (hb : backgroundCoords L k hL0 (supportEdges (axisZeroLink y)) ⊆ S)
    (G : ((fieldPeriodicData L k hL0).Carrier → ℂ) → Vertex L k j → ComplexMatrix2)
    (hG : ∀ f, IsSupBelow (fieldPeriodicData L k hL0) f ρ → ∀ x,
      G f x ∈ ComplexMatrix2.traceless)
    (hH : ∀ (a'' : Fin 3), ∀ x ∈ cubeVertices L (meshAt L k j) y,
      HolomorphicInValuesBelow (fieldPeriodicData L k hL0) ρ S fun f => pauliCoeff a'' (G f x))
    (a' : Fin 3) :
    HolomorphicInValuesBelow (fieldPeriodicData L k hL0) ρ S fun f => pauliCoeff a'
      (adjointCubeAverage (complexIter L k j (coeffField hL0 f)) (G f) y) := by
  classical
  have hfin : (cubeVertices L (meshAt L k j) y).Finite := by
    refine ((finite_points_near (meshAt_pos hL0) (y : InfiniteLattice.AmbientSpace)
      (meshAt L k (j + 1) / 2)).subset ?_)
    exact fun x hx i => abs_sub_lt_of_mem_cube hL0 hx i
  have hc := hE j hj (axisZeroLink y) (axisZeroLink_isPositivelyOriented y)
  refine readsHol_congr (readsHol_sum hS ((Finset.univ : Finset (Fin 3)) ×ˢ hfin.toFinset)
    (G := fun p f => pauliCoeff p.1 (G f p.2) * pauliCoeff a'
      (adjointCubeAverage (complexIter L k j (coeffField hL0 f))
        (singleSiteFunction p.1 p.2) y)) fun p hp => readsHol_mul
      (hH p.1 p.2 (hfin.mem_toFinset.1 (Finset.mem_product.1 hp).2))
      (readsHol_mono (hc.cubeAverage_entries a' p.1 p.2) hb hS)) fun f hf => ?_
  have hV := (hSm f hf).2 j hj
  have E := eq_sum_singleSiteFunction
    (fun l => adjointCubeAverage (complexIter L k j (coeffField hL0 f)) l y)
    (fun l hl l' hl' z =>
      ⟨congrFun (adjointCubeAverage_linear hLin hL hj hV hl hl' z).1 y,
        congrFun (adjointCubeAverage_linear hLin hL hj hV hl hl' z).2 y⟩)
    hfin.toFinset
    (fun l _ l' _ h => adjointCubeAverage_congr _ y fun x hx => h x (hfin.mem_toFinset.2 hx))
    (l := G f) (hG f hf)
  rw [E, pauliCoeff_finsetSum _ _ _ fun p _ =>
    ((hLin L hL k j hj _ hV).2.2.1 _ (singleSiteFunction_mem p.1 p.2)).2 y]
include h₄ hL hk hD hSm hE in
theorem readsHol_contourLogDrift {j : ℕ} (hj : j < k) (y : Vertex L k (j + 1))
    {S : Set (fieldPeriodicData L k hL0).Carrier} (hS : S.Finite)
    (hb : backgroundCoords L k hL0 (supportEdges (axisZeroLink y)) ⊆ S)
    (C : ((fieldPeriodicData L k hL0).Carrier → ℂ) → Edge L k j → ComplexMatrix2)
    (hC : ∀ f, IsSupBelow (fieldPeriodicData L k hL0) f ρ →
      C f ∈ complexEdgeForms (meshAt L k j))
    (hH : ∀ (a'' : Fin 3) (b' : PositiveEdge (meshAt L k j)),
      (b'.1.initial : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y →
      (b'.1.terminal : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y →
      HolomorphicInValuesBelow (fieldPeriodicData L k hL0) ρ S
        fun f => pauliCoeff a'' (C f b'.1))
    (a' : Fin 3) :
    HolomorphicInValuesBelow (fieldPeriodicData L k hL0) ρ S fun f => pauliCoeff a'
      (contourLogDrift (complexIter L k j (coeffField hL0 f)) (C f) y) := by
  classical
  have hfin : {p : PositiveEdge (meshAt L k j) |
      (p.1.initial : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y ∧
      (p.1.terminal : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y}.Finite := by
    refine ((finite_links_near (meshAt_pos hL0) (y : InfiniteLattice.AmbientSpace)
      (meshAt L k (j + 1) / 2)).preimage Subtype.val_injective.injOn).subset ?_
    exact fun p hp i => ⟨abs_sub_lt_of_mem_cube hL0 hp.1 i, abs_sub_lt_of_mem_cube hL0 hp.2 i⟩
  have hc := hE j hj (axisZeroLink y) (axisZeroLink_isPositivelyOriented y)
  refine readsHol_congr (readsHol_sum hS ((Finset.univ : Finset (Fin 3)) ×ˢ hfin.toFinset)
    (G := fun p f => pauliCoeff p.1 (C f p.2.1) * pauliCoeff a'
      (contourLogDrift (complexIter L k j (coeffField hL0 f))
        (basisForm p.1 p.2) y)) fun p hp => readsHol_mul
      (hH p.1 p.2 (hfin.mem_toFinset.1 (Finset.mem_product.1 hp).2).1
        (hfin.mem_toFinset.1 (Finset.mem_product.1 hp).2).2)
      (readsHol_mono (hc.contourDrift_entries a' p.1 p.2) hb hS)) fun f hf => ?_
  have hU := hSm f hf
  have hV := hU.2 j hj
  have hs := hD.1 j hj _ hV _ hU
  have E := eq_sum_basisForm hL0
    (fun B => contourLogDrift (complexIter L k j (coeffField hL0 f)) B y)
    (fun B hB B' hB' z => ⟨congrFun (hs.linear_contour B hB B' hB' z).1 y,
      congrFun (hs.linear_contour B hB B' hB' z).2 y⟩)
    hfin.toFinset
    (fun B hB B' hB' h => contourLogDrift_congr h₄ hL hk hj _ _ _ y fun b hp ht hh =>
      h ⟨b, hp⟩ (hfin.mem_toFinset.2 ⟨ht, hh⟩)) (hC f hf)
  rw [E, pauliCoeff_finsetSum _ _ _ fun p _ =>
    hs.mem_contour y _ (basisForm_mem hL0 p.1 p.2)]
include h₄ hRel hLin hL hk hD hSm hE in
theorem rowLocality_succ {j : ℕ} (hj : j < k) (ih : ∀ x : Vertex L k j, RowLocality hL0 ρ j x)
    (y : Vertex L k (j + 1)) : RowLocality hL0 ρ (j + 1) y := by
  have hpos := meshAt_pos (k := k) (j := j) hL0
  have h13 : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  have hs : 13 * meshAt L k j ≤ meshAt L k (j + 1) := by
    rw [meshAt_succ hL0]
    exact mul_le_mul_of_nonneg_right h13 hpos.le
  have hSf := finite_backgroundCoords hL0
    (finite_edgesNear (k := k) hL0 y (2 * meshAt L k (j + 1)))
  have hb : backgroundCoords L k hL0 (supportEdges (axisZeroLink y)) ⊆
      backgroundCoords L k hL0 (edgesNear L k y (2 * meshAt L k (j + 1))) := by
    refine backgroundCoords_mono hL0 ((supportEdges_subset_edgesNear hL0 _).trans
      (edgesNear_mono fun i => ?_))
    have e : ((axisZeroLink y).initial : InfiniteLattice.AmbientSpace) i =
        (y : InfiniteLattice.AmbientSpace) i := rfl
    rw [e, sub_self, abs_zero]
    linarith
  have hnear : ∀ x : InfiniteLattice.AmbientSpace, x ∈ cube L (meshAt L k j) y → ∀ r : ℝ,
      r ≤ 3 / 2 * meshAt L k (j + 1) → backgroundCoords L k hL0 (edgesNear L k x r) ⊆
        backgroundCoords L k hL0 (edgesNear L k y (2 * meshAt L k (j + 1))) :=
    fun x hx r hr => backgroundCoords_mono hL0 (edgesNear_mono fun i => by
      linarith [abs_sub_lt_of_mem_cube hL0 hx i])
  refine ⟨fun a' a x₀ => ?_, fun a' a b => ?_⟩
  · exact readsHol_adjointCubeAverage hLin hL hL0 hSm hE hj y hSf hb
      (fun f => iterAdjointCubeAverage L k (coeffField hL0 f) j (singleSiteFunction a x₀))
      (fun f hf => iterAdjointCubeAverage_mem_traceless hLin hL (hSm f hf) j hj.le _
        (singleSiteFunction_mem a x₀))
      (fun a'' x hx => readsHol_mono ((ih x).averageEntry a'' a x₀)
        (hnear x hx _ (by linarith)) hSf) a'
  · have hB := basisForm_mem (k := k) (j := 0) hL0 a b
    refine readsHol_congr (readsHol_add
      (readsHol_adjointCubeAverage hLin hL hL0 hSm hE hj y hSf hb
        (fun f => iterContourLogDrift L k (coeffField hL0 f) j (basisForm a b))
        (fun f hf =>
          (iterContourLogDrift_traceless_linear hRel hLin hL hD (hSm f hf) j hj.le).1 _ hB)
        (fun a'' x hx => readsHol_mono ((ih x).driftRow a'' a b)
          (hnear x hx _ (by linarith)) hSf) a')
      (readsHol_contourLogDrift h₄ hL hk hD hL0 hSm hE hj y hSf hb
        (fun f => complexIterDeriv L k j (coeffField hL0 f) (basisForm a b))
        (fun f hf => complexIterDeriv_mem hRel hL hD (hSm f hf) hj.le hB)
        (fun a'' b' ht _ => readsHol_mono
          (complexIterDeriv_entries_holomorphic hRel hL hL0 hSm hE hj.le b' a'' a b)
          (hnear _ ht _ (by linarith)) hSf) a')) fun f hf => ?_
    have hU := hSm f hf
    have hV := hU.2 j hj
    have hv₁ := ((hLin L hL k j hj _ hV).2.2.1 _
      ((iterContourLogDrift_traceless_linear hRel hLin hL hD hU j hj.le).1 _ hB)).2 y
    have hv₂ := (hD.1 j hj _ hV _ hU).mem_contour y _
      (complexIterDeriv_mem hRel hL hD hU hj.le hB)
    simp only [iterContourLogDrift, Pi.add_apply]
    exact pauliCoeff_add hv₁ hv₂ a'
include h₄ hRel hLin hL hk hD hSm hE in
theorem rowLocality_all : ∀ j ≤ k, ∀ y : Vertex L k j, RowLocality hL0 ρ j y := by
  intro j
  induction j with
  | zero =>
    intro _ y
    have hf := finite_backgroundCoords hL0
      (finite_edgesNear (k := k) hL0 y (2 * meshAt L k 0))
    exact ⟨fun a' a x => readsHol_congr (readsHol_const hf ρ
        (pauliCoeff a' (singleSiteFunction a x y))) fun _ _ => rfl,
      fun a' a b => readsHol_congr (readsHol_const hf ρ (pauliCoeff a' 0)) fun _ _ => rfl⟩
  | succ j ih =>
    intro hj y
    exact rowLocality_succ h₄ hRel hLin hL hk hD hL0 hSm hE hj (ih (by omega)) y
end Step
end SeriesExpansions
section Top
open ElementaryEntries (singleSiteFunction EdgeEntries)
open FieldValueFunctions (backgroundCoords averageKernelFn covariantAverageFn)
open _root_.YangMills.Construction.Tower.SupportOfMeans.Unbounded (supportEdges)
open ReadsCubes (IsFinitelySupportedForm LocalAt)
variable {L k : ℕ}
theorem conj_mem_traceless (X : ComplexMatrix2) {Y : ComplexMatrix2}
    (hY : Y ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy X Y ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.PeriodicLattice.conjugateBy_mem_traceless <;> assumption
theorem covDiff_zero {a : ℝ} (V : InfiniteLattice.Link a → ComplexMatrix2) :
    covDiff V (0 : InfiniteLattice.LatticePoint a → ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.CovariantIterRelationsProof.covDiff_zero <;> assumption
theorem iterAdjointCubeAverage_zero (U : Edge L k 0 → ComplexMatrix2) (j : ℕ) :
    iterAdjointCubeAverage L k U j 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [iterAdjointCubeAverage]
    rw [ih, adjointCubeAverage_zero]
theorem basisForm_finitelySupported (hL : 0 < L) (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) :
    IsFinitelySupportedForm (basisForm a b : Edge L k 0 → ComplexMatrix2) := by
  refine ⟨basisForm_mem hL a b, (Set.finite_singleton b).subset fun p hp => ?_⟩
  by_contra hne
  apply hp
  have hne' : p.1 ≠ b.1 := fun e => hne (Subtype.ext e)
  change (basisForm a b : Edge L k 0 → ComplexMatrix2) p.1 = 0
  rw [basisForm_apply_of_pos a b p.2, if_neg hne']
theorem zero_finitelySupported : IsFinitelySupportedForm (0 : Edge L k 0 → ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.FullSpace.ReadsCubes.isFinitelySupportedForm_zero <;> assumption
variable (h₄ : BlockPathContourPivotStatement)
  (hRel : CovariantIterRelations)
  (hLin : CovariantStepComplexLinear)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
  (hD : _root_.YangMills.Construction.Tower.FullSpace.AsDifferentials.Requirements L k)
  (hL0 : 0 < L) {ρ : ℝ}
  (hSm : ∀ f, IsSupBelow (fieldPeriodicData L k hL0) f ρ →
    coeffField hL0 f ∈ smallIterateFields L k)
  (hE : ∀ i < k, ∀ c : Edge L k (i + 1), c.IsPositivelyOriented → EdgeEntries L k hL0 ρ c)
include hRel hLin hL hD in
theorem iterCovariantDeriv_zero {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) : iterCovariantDeriv L k U k 0 = 0 := by
  have z₀ := Submodule.zero_mem (complexEdgeForms (meshAt L k 0))
  have e₁ : complexIterDeriv L k k U 0 = 0 := by
    simpa using (complexIterDeriv_linear hRel hL hD hU le_rfl 0 z₀ 0 z₀ 0).2
  have e₂ : iterContourLogDrift L k U k 0 = 0 := by
    simpa using
      ((iterContourLogDrift_traceless_linear hRel hLin hL hD hU k le_rfl).2 0 z₀ 0 z₀ 0).2
  rw [(hRel L hL k k le_rfl U hU).1 0 z₀, e₁, e₂, covDiff_zero, add_zero]
include h₄ hRel hLin hL hk hD hSm hE in
theorem iterCovariantDeriv_entries_holomorphic {i : ℕ} (hki : k = i + 1)
    (c : PositiveEdge (meshAt L k k)) (a' a : Fin 3) (b : PositiveEdge (meshAt L k 0)) :
    HolomorphicInValuesBelow (fieldPeriodicData L k hL0) ρ
      (backgroundCoords L k hL0 (edgesNear L k c.1.initial 3))
      fun f => pauliCoeff a' (iterCovariantDeriv L k (coeffField hL0 f) k
        (basisForm a b) c.1) := by
  classical
  subst hki
  have hone : meshAt L (i + 1) (i + 1) = 1 := meshAt_self hL0
  have hSf := finite_backgroundCoords hL0 (finite_edgesNear (k := i + 1) hL0 c.1.initial 3)
  have Eh := hE i (Nat.lt_succ_self i) c.1 c.2
  have hb : backgroundCoords L (i + 1) hL0 (supportEdges c.1) ⊆
      backgroundCoords L (i + 1) hL0 (edgesNear L (i + 1) c.1.initial 3) := by
    refine backgroundCoords_mono hL0 ((supportEdges_subset_edgesNear hL0 c.1).trans
      (edgesNear_mono fun i' => ?_))
    rw [sub_self, abs_zero, hone]
    norm_num
  have hrows := rowLocality_all h₄ hRel hLin hL hk hD hL0 hSm hE (i + 1) le_rfl
  let R : Finset (Vertex L (i + 1) (i + 1)) := {c.1.initial, c.1.terminal}
  have hnear : ∀ x ∈ R, backgroundCoords L (i + 1) hL0
      (edgesNear L (i + 1) x (2 * meshAt L (i + 1) (i + 1))) ⊆
      backgroundCoords L (i + 1) hL0 (edgesNear L (i + 1) c.1.initial 3) := by
    intro x hx
    refine backgroundCoords_mono hL0 (edgesNear_mono fun i' => ?_)
    have hclose : |(x : InfiniteLattice.AmbientSpace) i' -
        (c.1.initial : InfiniteLattice.AmbientSpace) i'| ≤ meshAt L (i + 1) (i + 1) := by
      rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [sub_self, abs_zero]
        exact (meshAt_pos hL0).le
      · rw [Finset.mem_singleton.1 hx]
        exact abs_terminal_sub_initial_le (meshAt_pos hL0) c.1 i'
    linarith
  refine readsHol_congr (readsHol_add (readsHol_mono (Eh.iterDeriv_entries a' a b) hb hSf)
    (readsHol_sum hSf ((Finset.univ : Finset (Fin 3)) ×ˢ R)
      (G := fun p f => pauliCoeff p.1 (iterContourLogDrift L (i + 1)
          (coeffField hL0 f) (i + 1) (basisForm a b) p.2) *
        pauliCoeff a' (covDiff
          (complexIter L (i + 1) (i + 1) (coeffField hL0 f))
          (singleSiteFunction p.1 p.2) c.1)) fun p hp => readsHol_mul
      (readsHol_mono ((hrows p.2).driftRow p.1 a b) (hnear p.2 (Finset.mem_product.1 hp).2) hSf)
      (readsHol_mono (Eh.covDiff_entries a' p.1 p.2) hb hSf))) fun f hf => ?_
  have hU := hSm f hf
  have hB := basisForm_mem (k := i + 1) (j := 0) hL0 a b
  have hl := (iterContourLogDrift_traceless_linear hRel hLin hL hD hU (i + 1) le_rfl).1 _ hB
  set V := complexIter L (i + 1) (i + 1) (coeffField hL0 f) with hVdef
  have hform : ∀ l : Vertex L (i + 1) (i + 1) → ComplexMatrix2, covDiff V l c.1 =
      ComplexMatrix2.conjugateBy (V c.1) (l c.1.terminal) - l c.1.initial := fun l =>
    extendOddly_of_pos _ c.2
  have hval : ∀ l ∈ tracelessVertexFunctions (Vertex L (i + 1) (i + 1)),
      covDiff V l c.1 ∈ ComplexMatrix2.traceless := fun l hl' => by
    rw [hform]
    exact ComplexMatrix2.traceless.sub_mem (conj_mem_traceless _ (hl' _)) (hl' _)
  have E := eq_sum_singleSiteFunction (fun l => covDiff V l c.1)
    (fun l _ l' _ z => by
      simp only [hform, Pi.add_apply, Pi.smul_apply]
      constructor
      · simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul]
        abel
      · simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul, smul_sub])
    R
    (fun l _ l' _ h => by
      simp only [hform]
      rw [h c.1.initial (Finset.mem_insert_self _ _),
        h c.1.terminal (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))])
    (l := iterContourLogDrift L (i + 1) (coeffField hL0 f) (i + 1) (basisForm a b)) hl
  rw [(hRel L hL (i + 1) (i + 1) le_rfl _ hU).1 _ hB, Pi.add_apply,
    pauliCoeff_add ((hD.1 i (Nat.lt_succ_self i) _ (hU.2 i (Nat.lt_succ_self i)) _ hU).mem_iter
      c.1 c.2 _ hB) (hval _ hl) a', E,
    pauliCoeff_finsetSum _ _ _ fun p _ => hval _ (singleSiteFunction_mem p.1 p.2)]
end Top
theorem claim_holds
    (h₁ : _root_.YangMills.Construction.Tower.SupportOfMeans.SupportOfMeansHolds)
    (h₂ : ElementaryEntries.EntriesHolomorphic)
    (h₃ : ReadsCubes.Statement)
    (h₄ : SmallIterates.SmallIteratesNearOne)
    (h₅ : _root_.YangMills.Construction.Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (h₆ : CovariantIterRelations)
    (h₇ : BlockPathContourPivotStatement)
    (h₈ : _root_.YangMills.Construction.Tower.ThreeMapKernels.Claim)
    (h₉ : CovariantStepComplexLinear) : Claim := by
  classical
  intro L hL0 hL k hk
  obtain ⟨ρ₁, hρ₁, hEl, -⟩ := h₂ L hL0 hL k hk
  obtain ⟨ρ₂, hρ₂, hSm₂⟩ := (h₄ L hL0 hL k hk).2
  have hD := (h₅ L hL k hk).2
  have hR := (h₁ L hL k hk).2
  have hK := (h₈ L hL k hk).2
  have hRead := (h₃ L hL k hk).1
  have hm₁ : min ρ₁ ρ₂ ≤ ρ₁ := min_le_left _ _
  have hm₂ : min ρ₁ ρ₂ ≤ ρ₂ := min_le_right _ _
  have hSm : ∀ f, IsSupBelow (fieldPeriodicData L k hL0) f (min ρ₁ ρ₂) →
      coeffField hL0 f ∈ smallIterateFields L k := fun f hf => by
    obtain ⟨r, hr, hb⟩ := hf
    exact hSm₂ f ⟨r, hr.trans_le hm₂, hb⟩
  have hE : ∀ i < k, ∀ c : Edge L k (i + 1), c.IsPositivelyOriented →
      ElementaryEntries.EdgeEntries L k hL0 (min ρ₁ ρ₂) c :=
    fun i hi c hc =>
      ⟨fun a' a b => readsHol_radius ((hEl i hi c hc).iterDeriv_entries a' a b) hm₁,
        fun a' a x => readsHol_radius ((hEl i hi c hc).covDiff_entries a' a x) hm₁,
        fun a' a x => readsHol_radius ((hEl i hi c hc).cubeAverage_entries a' a x) hm₁,
        fun a' a b => readsHol_radius ((hEl i hi c hc).contourDrift_entries a' a b) hm₁⟩
  have hrows := rowLocality_all h₇ h₆ h₉ hL hk hD hL0 hSm hE k le_rfl
  have hone : 2 * meshAt L k k = 2 := by rw [meshAt_self hL0, mul_one]
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun y a' => ⟨?_, ?_, ?_⟩, fun c a' => ⟨?_, ?_⟩⟩
  · rintro ⟨a, b⟩
    have h := (hrows y).driftRow a' a b
    rw [hone] at h
    exact readsHol_congr h fun f hf =>
      driftKernel_apply h₇ h₆ h₉ hL hk hD hR hK (hSm f hf) a' a y b
  · rintro ⟨a, x⟩
    have h := (hrows y).averageEntry a' a x
    rw [hone] at h
    exact readsHol_congr h fun f hf => iterAverageKernel_apply hK (hSm f hf) a' a y x
  · intro a x hx f hf
    have hU := hSm f hf
    show FieldValueFunctions.averageKernelFn L k hL0 f (a', y) (a, x) = 0
    refine (iterAverageKernel_apply hK hU a' a y x).trans ?_
    have e := (hRead _ hU).cubeAverage_local y
      (ElementaryEntries.singleSiteFunction a x) 0 fun x' hx' => by
        have hne : x' ≠ x := fun e => hx (e ▸ hx')
        simp [ElementaryEntries.singleSiteFunction, hne]
    rw [e, iterAdjointCubeAverage_zero]
    exact pauliCoeff_zero a'
  · rintro ⟨a, b⟩
    obtain ⟨i, hi⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    exact readsHol_congr
      (iterCovariantDeriv_entries_holomorphic h₇ h₆ h₉ hL hk hD hL0 hSm hE hi c a' a b)
      fun f hf => iterCovariantKernel_apply hK (hSm f hf) a' a c b
  · intro a b hb f hf
    have hU := hSm f hf
    show FieldValueFunctions.covariantAverageFn L k hL0 f (a', c) (a, b) = 0
    refine (iterCovariantKernel_apply hK hU a' a c b).trans ?_
    have e := (hRead _ hU).iterCovariantDeriv_local c (basisForm a b) 0
      (basisForm_finitelySupported hL0 a b) zero_finitelySupported fun b' hb' => by
        have hne : b' ≠ b.1 := fun e => hb (e ▸ hb')
        rw [basisForm_apply_of_pos a b hb'.1, if_neg hne]
        rfl
    rw [e, iterCovariantDeriv_zero h₆ h₉ hL hD hU]
    exact pauliCoeff_zero a'
end YangMills.Construction.Tower.FullSpace.IteratedKernelEntries
end
