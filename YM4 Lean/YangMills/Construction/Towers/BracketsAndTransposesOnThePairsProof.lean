import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyProof
import YangMills.Construction.PeriodicOperators.SymmetricKernelOfAQuadraticFormProof
import YangMills.Construction.Towers.BracketsAndTransposesOnThePairs
import YangMills.Construction.Towers.LocalKernelsAndMatricesOfLinearMaps
import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnASideProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels.PairBrackets
open Periodisation Tower Matrices
open PeriodicOperators (KernelMatrix applyKernel HasFiniteSupport)
open OneLoop (pauliCoordinateEquiv)
theorem pauliCoeff_coe (X : ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X : ComplexMatrix2) = pauliCoordinateEquiv X a := by
  unfold pauliCoeff
  rw [dif_pos X.2]
theorem sum_smul_pauliFamily_mem_traceless (c : Fin 3 → ℂ) :
    (∑ a, c a • ComplexMatrix2.pauliFamily a) ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem pauliCoeff_sum_smul (c : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, c b • ComplexMatrix2.pauliFamily b) = c a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem pauliCoeff_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.ComplexFieldRescaledRelations.pauliCoeff_add <;> assumption
theorem pauliCoeff_smul (c : ℂ) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (a : Fin 3) : pauliCoeff a (c • X) = c * pauliCoeff a X := by
  have h := pauliCoeff_coe (c • (⟨X, hX⟩ : ComplexMatrix2.traceless)) a
  rw [map_smul, Pi.smul_apply, ← pauliCoeff_coe, smul_eq_mul] at h
  exact h
theorem halfTrace_mul_eq_sum (hP : OneLoop.PauliMatrixRelations) {X Y : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (hY : Y ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.halfTrace (X * Y) = ∑ a, pauliCoeff a X * pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p22145 <;> assumption
theorem tsum_toPauliCoeffs_mul (hP : OneLoop.PauliMatrixRelations) {σ : Type}
    (u v : σ → ComplexMatrix2) (hu : ∀ s, u s ∈ ComplexMatrix2.traceless)
    (hv : ∀ s, v s ∈ ComplexMatrix2.traceless)
    (hfin : (Function.support u).Finite ∨ (Function.support v).Finite) :
    ∑' ι : Fin 3 × σ, toPauliCoeffs u ι * toPauliCoeffs v ι = traceFinsumPairing u v := by
  have hF : ∃ F : Finset σ, ∀ s, s ∉ F → u s = 0 ∨ v s = 0 := by
    rcases hfin with h | h
    · exact ⟨h.toFinset, fun s hs => Or.inl (by simpa using hs)⟩
    · exact ⟨h.toFinset, fun s hs => Or.inr (by simpa using hs)⟩
  obtain ⟨F, hF⟩ := hF
  have hzero : ∀ s, s ∉ F → ∀ a, pauliCoeff a (u s) * pauliCoeff a (v s) = 0 := by
    intro s hs a
    rcases hF s hs with h | h <;> simp [h, pauliCoeff_zero]
  unfold traceFinsumPairing
  rw [finsum_eq_sum_of_support_subset (s := F)]
  · rw [tsum_eq_sum (s := Finset.univ ×ˢ F)]
    · rw [Finset.sum_product_right]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [halfTrace_mul_eq_sum hP (hu s) (hv s)]
      rfl
    · rintro ⟨a, s⟩ hs
      exact hzero s (fun h => hs (by simp [h])) a
  · intro s hs
    by_contra hsF
    have hsF' : s ∉ F := by simpa using hsF
    refine hs ?_
    show ComplexMatrix2.halfTrace (u s * v s) = 0
    rw [halfTrace_mul_eq_sum hP (hu s) (hv s)]
    exact Finset.sum_eq_zero fun a _ => hzero s hsF' a
theorem finite_support_toPauliCoeffs_iff {σ : Type} (u : σ → ComplexMatrix2)
    (hu : ∀ s, u s ∈ ComplexMatrix2.traceless) :
    (Function.support (toPauliCoeffs u)).Finite ↔ (Function.support u).Finite := by
  constructor
  · intro h
    refine (h.image Prod.snd).subset fun s hs => ?_
    by_contra hs'
    refine hs ?_
    rw [← sum_pauliCoeff_smul (hu s)]
    refine Finset.sum_eq_zero fun a _ => ?_
    have : toPauliCoeffs u (a, s) = 0 := by
      by_contra hne
      exact hs' ⟨(a, s), hne, rfl⟩
    have h0 : pauliCoeff a (u s) = 0 := this
    rw [h0, zero_smul]
  · intro h
    refine ((Set.finite_univ (α := Fin 3)).prod h).subset ?_
    rintro ⟨a, s⟩ hs
    refine ⟨Set.mem_univ a, fun h0 => hs ?_⟩
    show pauliCoeff a (u s) = 0
    rw [h0, pauliCoeff_zero]
theorem exists_linearEquiv_coeffs {J σ ι : Type} (W : Submodule ℂ (ι → ComplexMatrix2))
    (ρ : J ≃ Fin 3 × σ) (val : (ι → ComplexMatrix2) → σ → ComplexMatrix2)
    (hadd : ∀ f g, val (f + g) = val f + val g)
    (hsmul : ∀ (c : ℂ) f, val (c • f) = c • val f)
    (hmem : ∀ f ∈ W, ∀ s, val f s ∈ ComplexMatrix2.traceless)
    (hinj : ∀ f ∈ W, ∀ g ∈ W, val f = val g → f = g)
    (hsurj : ∀ w : σ → ComplexMatrix2, (∀ s, w s ∈ ComplexMatrix2.traceless) →
      ∃ f ∈ W, val f = w) :
    ∃ Φ : W ≃ₗ[ℂ] (J → ℂ), ∀ f : W, Φ f = fun j => toPauliCoeffs (val f) (ρ j) := by
  let l : W →ₗ[ℂ] (J → ℂ) :=
    { toFun := fun f j => toPauliCoeffs (val f) (ρ j)
      map_add' := fun f g => by
        funext j
        show pauliCoeff _ (val ((f : ι → ComplexMatrix2) + g) _) = _
        rw [hadd]
        exact pauliCoeff_add (hmem f f.2 _) (hmem g g.2 _) _
      map_smul' := fun c f => by
        funext j
        show pauliCoeff _ (val (c • (f : ι → ComplexMatrix2)) _) = _
        rw [hsmul]
        exact pauliCoeff_smul c (hmem f f.2 _) _ }
  have hl : Function.Bijective l := by
    constructor
    · intro f g hfg
      refine Subtype.ext (hinj f f.2 g g.2 (funext fun s => ?_))
      rw [← sum_pauliCoeff_smul (hmem f f.2 s), ← sum_pauliCoeff_smul (hmem g g.2 s)]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h := congrFun hfg (ρ.symm (a, s))
      have h' : toPauliCoeffs (val f) (ρ (ρ.symm (a, s))) =
        toPauliCoeffs (val g) (ρ (ρ.symm (a, s))) := h
      rw [Equiv.apply_symm_apply] at h'
      have h'' : pauliCoeff a (val f s) = pauliCoeff a (val g s) := h'
      rw [h'']
    · intro g
      obtain ⟨f, hf, hw⟩ := hsurj (ofPauliCoeffs fun x => g (ρ.symm x))
        (fun s => sum_smul_pauliFamily_mem_traceless fun a => g (ρ.symm (a, s)))
      refine ⟨⟨f, hf⟩, funext fun j => ?_⟩
      show toPauliCoeffs (val f) (ρ j) = g j
      rw [hw]
      show pauliCoeff (ρ j).1
        (∑ a, g (ρ.symm (a, (ρ j).2)) • ComplexMatrix2.pauliFamily a) = g j
      rw [pauliCoeff_sum_smul]
      simp
  exact ⟨LinearEquiv.ofBijective l hl, fun f => rfl⟩
section Links
variable {a : ℝ}
theorem isPositivelyOriented_or_opposite (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem not_isPositivelyOriented_opposite (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
theorem exists_form_of_values (ha : 0 < a) (w : FullSpace.PositiveEdge a → ComplexMatrix2)
    (hw : ∀ b, w b ∈ ComplexMatrix2.traceless) :
    ∃ B ∈ FullSpace.complexEdgeForms a, FullSpace.restrictToPositiveEdges B = w := by
  classical
  let B : InfiniteLattice.Link a → ComplexMatrix2 := fun b =>
    if h : b.IsPositivelyOriented then w ⟨b, h⟩
    else -w ⟨b.opposite, (isPositivelyOriented_or_opposite b).resolve_left h⟩
  have hpos : ∀ b (h : b.IsPositivelyOriented), B b = w ⟨b, h⟩ := fun b h => dif_pos h
  have hneg : ∀ b (h : ¬ b.IsPositivelyOriented),
      B b = -w ⟨b.opposite, (isPositivelyOriented_or_opposite b).resolve_left h⟩ :=
    fun b h => dif_neg h
  refine ⟨B, ⟨fun b hb => ?_, fun b => ?_⟩, funext fun b => hpos b.1 b.2⟩
  · rw [hpos b hb]
    exact hw _
  · by_cases h : b.IsPositivelyOriented
    · rw [hneg b.opposite (not_isPositivelyOriented_opposite ha h), hpos b h]
      rfl
    · have h' := (isPositivelyOriented_or_opposite b).resolve_left h
      rw [hpos b.opposite h', hneg b h, neg_neg]
theorem form_eq_of_restrict_eq {B B' : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : B ∈ FullSpace.complexEdgeForms a) (hB' : B' ∈ FullSpace.complexEdgeForms a)
    (h : FullSpace.restrictToPositiveEdges B = FullSpace.restrictToPositiveEdges B') :
    B = B' := by
  have hpos : ∀ b (hb : b.IsPositivelyOriented), B b = B' b := fun b hb => congrFun h ⟨b, hb⟩
  funext b
  rcases isPositivelyOriented_or_opposite b with hb | hb
  · exact hpos b hb
  · have h₁ : B b.opposite = -B b := hB.2 b
    have h₂ : B' b.opposite = -B' b := hB'.2 b
    have h₃ := hpos b.opposite hb
    rw [h₁, h₂] at h₃
    exact neg_injective h₃
end Links
section ColourCells
variable {k : ℕ} (L : ℕ)
def colourCellEquiv (A : CellClass k) : Fin 3 × Cell L k A.level A.cellType ≃ Idx L A.colourPairs where
  toFun x := ⟨(), x⟩
  invFun ι := ι.2
  left_inv _ := rfl
  right_inv _ := rfl
theorem weightOf_colourPairs (A : CellClass k) (ι : Idx L A.colourPairs) :
    (A.colourPairs.toPeriodicData L).weightOf ι = 1 := rfl
theorem weightedBracket_eq_tsum (A : CellClass k) (u v : Idx L A.colourPairs → ℂ) :
    weightedBracket L A.colourPairs u v =
      ∑' x, u (colourCellEquiv L A x) * v (colourCellEquiv L A x) := by
  unfold weightedBracket PeriodicOperators.wPairing
  rw [← (colourCellEquiv L A).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [weightOf_colourPairs]
  simp
theorem weightedBracket_indicator (A : CellClass k) (u δ : Idx L A.colourPairs → ℂ)
    (ι : Idx L A.colourPairs) (h₁ : δ ι = 1) (h₀ : ∀ j, j ≠ ι → δ j = 0) :
    weightedBracket L A.colourPairs u δ = u ι := by
  unfold weightedBracket PeriodicOperators.wPairing
  rw [tsum_eq_single ι]
  · rw [weightOf_colourPairs, h₁]
    simp
  · intro j hj
    rw [h₀ j hj]
    simp
theorem cellFn_mem_traceless (A : CellClass k) (hA : A.cellType ≠ .face)
    (f : (CellClass.fullSpace L A).complexSubmodule) (c : Cell L k A.level A.cellType) :
    CellClass.cellFn L A f c ∈ ComplexMatrix2.traceless := by
  rcases A with ⟨j, hj, _ | _ | _⟩
  · exact f.2 c (mem_univ c)
  · exact f.2.1 c.1 c.2
  · exact absurd rfl hA
theorem pair_eq_traceFinsumPairing (A : CellClass k) (hA : A.cellType ≠ .face)
    (f g : (CellClass.fullSpace L A).index → ComplexMatrix2) :
    (CellClass.fullSpace L A).pair f g =
      traceFinsumPairing (CellClass.cellFn L A f) (CellClass.cellFn L A g) := by
  rcases A with ⟨j, hj, _ | _ | _⟩
  · rfl
  · rfl
  · exact absurd rfl hA
theorem isFinitelySupported_iff (A : CellClass k) (hA : A.cellType ≠ .face)
    (f : (CellClass.fullSpace L A).index → ComplexMatrix2) :
    (CellClass.fullSpace L A).IsFinitelySupported f ↔
      (Function.support (CellClass.cellFn L A f)).Finite := by
  rcases A with ⟨j, hj, _ | _ | _⟩
  · exact Iff.rfl
  · exact Iff.rfl
  · exact absurd rfl hA
theorem exists_linearEquiv_coeffsOn (hL : 0 < L) (A : CellClass k) (hA : A.cellType ≠ .face) :
    ∃ Φ : (CellClass.fullSpace L A).complexSubmodule ≃ₗ[ℂ] (Idx L A.colourPairs → ℂ),
      ∀ f, Φ f = CellClass.coeffsOn L A f := by
  rcases A with ⟨j, hj, _ | _ | _⟩
  · exact exists_linearEquiv_coeffs (GroupLieProduct.tracelessFunctions (FullSpace.Vertex L k j))
      (colourCellEquiv L ⟨j, hj, .vertex⟩).symm (fun f => f) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun f hf s => hf s (mem_univ s)) (fun f _ g _ h => h)
      (fun w hw => ⟨w, fun s _ => hw s, rfl⟩)
  · have ha : 0 < meshAt L k j := zpow_pos (by exact_mod_cast hL) _
    exact exists_linearEquiv_coeffs (FullSpace.complexEdgeForms (meshAt L k j))
      (colourCellEquiv L ⟨j, hj, .edge⟩).symm FullSpace.restrictToPositiveEdges
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun f hf s => hf.1 s.1 s.2) (fun f hf g hg h => form_eq_of_restrict_eq hf hg h)
      (fun w hw => exists_form_of_values ha w hw)
  · exact absurd rfl hA
theorem hasFiniteSupport_coeffsOn_iff (A : CellClass k) (hA : A.cellType ≠ .face)
    (f : (CellClass.fullSpace L A).complexSubmodule) :
    HasFiniteSupport (CellClass.coeffsOn L A f) ↔
      (CellClass.fullSpace L A).IsFinitelySupported f := by
  rw [isFinitelySupported_iff L A hA,
    ← finite_support_toPauliCoeffs_iff _ (cellFn_mem_traceless L A hA f)]
  have h : Function.support (CellClass.coeffsOn L A f) = (colourCellEquiv L A).symm ⁻¹'
      Function.support (toPauliCoeffs (CellClass.cellFn L A f)) := rfl
  unfold HasFiniteSupport
  rw [h]
  exact ⟨fun h' => Set.Finite.of_preimage h' (colourCellEquiv L A).symm.surjective,
    fun h' => h'.preimage (colourCellEquiv L A).symm.injective.injOn⟩
theorem weightedBracket_coeffsOn (hP : OneLoop.PauliMatrixRelations) (A : CellClass k)
    (hA : A.cellType ≠ .face) (f g : (CellClass.fullSpace L A).complexSubmodule)
    (h : (CellClass.fullSpace L A).IsFinitelySupported f ∨
      (CellClass.fullSpace L A).IsFinitelySupported g) :
    weightedBracket L A.colourPairs (CellClass.coeffsOn L A f) (CellClass.coeffsOn L A g) =
      (CellClass.fullSpace L A).pair f g := by
  rw [weightedBracket_eq_tsum, pair_eq_traceFinsumPairing L A hA]
  exact tsum_toPauliCoeffs_mul hP _ _ (cellFn_mem_traceless L A hA f)
    (cellFn_mem_traceless L A hA g)
    (h.imp (isFinitelySupported_iff L A hA f).1 (isFinitelySupported_iff L A hA g).1)
theorem transposeMap_unique (hL : 0 < L) (hP : OneLoop.PauliMatrixRelations)
    (A A' : CellClass k) (hA : A.cellType ≠ .face)
    (m : (CellClass.fullSpace L A).complexSubmodule →ₗ[ℂ]
      (CellClass.fullSpace L A').complexSubmodule)
    (m₁ m₂ : (CellClass.fullSpace L A').complexSubmodule →ₗ[ℂ]
      (CellClass.fullSpace L A).complexSubmodule)
    (h₁ : PairedFunctionSpace.IsTransposeMap m m₁)
    (h₂ : PairedFunctionSpace.IsTransposeMap m m₂) : m₁ = m₂ := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_linearEquiv_coeffsOn L hL A hA
  refine LinearMap.ext fun g => Φ.injective ?_
  rw [hΦ, hΦ]
  funext ι
  let δ : Idx L A.colourPairs → ℂ := fun j => if j = ι then 1 else 0
  have hread : CellClass.coeffsOn L A (Φ.symm δ) = δ := by
    rw [← hΦ, LinearEquiv.apply_symm_apply]
  have hδ : HasFiniteSupport δ := by
    refine (Set.finite_singleton ι).subset fun j hj => ?_
    by_contra hne
    exact hj (if_neg hne)
  have hfs : (CellClass.fullSpace L A).IsFinitelySupported (Φ.symm δ) :=
    (hasFiniteSupport_coeffsOn_iff L A hA _).1 (by rw [hread]; exact hδ)
  have e : ∀ h : (CellClass.fullSpace L A).complexSubmodule, CellClass.coeffsOn L A h ι =
      (CellClass.fullSpace L A).pair h (Φ.symm δ) := fun h => by
    rw [← weightedBracket_coeffsOn L hP A hA h _ (Or.inr hfs), hread]
    exact (weightedBracket_indicator L A _ δ ι (if_pos rfl) fun j hj => if_neg hj).symm
  rw [e, e, h₁ g _ hfs, h₂ g _ hfs]
end ColourCells
def kernelLinearMap {J J' : Type} (T : KernelMatrix J J')
    (h : ∀ (f : J → ℂ) (ι' : J'), (Function.support fun ι => T ι' ι * f ι).Finite) :
    (J → ℂ) →ₗ[ℂ] (J' → ℂ) where
  toFun := applyKernel T
  map_add' f g := by
    funext ι'
    show ∑' ι, T ι' ι * (f ι + g ι) = ∑' ι, T ι' ι * f ι + ∑' ι, T ι' ι * g ι
    rw [← (summable_of_hasFiniteSupport (h f ι')).tsum_add
      (summable_of_hasFiniteSupport (h g ι'))]
    exact tsum_congr fun ι => mul_add _ _ _
  map_smul' c f := by
    funext ι'
    show ∑' ι, T ι' ι * (c * f ι) = c * ∑' ι, T ι' ι * f ι
    rw [← tsum_mul_left]
    exact tsum_congr fun ι => by ring
theorem bracketsAndTransposes_holds (hK : KernelsAndLinearMapMatrices)
    (hP : OneLoop.PauliMatrixRelations) : BracketsAndTransposes := by
  intro L hL k N hN A A' hA hA'
  have hEv := (hK L hL k N hN).1
  have hL0 : 0 < L := by
    have := hL.2
    omega
  refine ⟨fun f g h => weightedBracket_coeffsOn L hP A hA f g h, fun R hR T hT => ?_⟩
  obtain ⟨hfin, hcarry, hloc, hadj⟩ := hEv A.colourPairs A'.colourPairs R hR T hT
  obtain ⟨hfin', -, -, -⟩ := hEv A'.colourPairs A.colourPairs R hR _ hloc
  obtain ⟨Φ, hΦ⟩ := exists_linearEquiv_coeffsOn L hL0 A hA
  obtain ⟨Φ', hΦ'⟩ := exists_linearEquiv_coeffsOn L hL0 A' hA'
  let K := kernelLinearMap T hfin
  let K' := kernelLinearMap (kernelT L A.colourPairs A'.colourPairs T) hfin'
  let m := Φ'.symm.toLinearMap ∘ₗ K ∘ₗ Φ.toLinearMap
  let m' := Φ.symm.toLinearMap ∘ₗ K' ∘ₗ Φ'.toLinearMap
  have hm : ∀ f, CellClass.coeffsOn L A' (m f) = applyKernel T (CellClass.coeffsOn L A f) := by
    intro f
    rw [← hΦ', ← hΦ]
    show Φ' (Φ'.symm (K (Φ f))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hm' : ∀ g, CellClass.coeffsOn L A (m' g) =
      applyKernel (kernelT L A.colourPairs A'.colourPairs T) (CellClass.coeffsOn L A' g) := by
    intro g
    rw [← hΦ, ← hΦ']
    show Φ (Φ.symm (K' (Φ' g))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hcar : PairedFunctionSpace.PreservesFiniteSupport m := by
    intro f hf
    rw [← hasFiniteSupport_coeffsOn_iff L A' hA' (m f), hm]
    exact hcarry _ ((hasFiniteSupport_coeffsOn_iff L A hA f).2 hf)
  have htr : PairedFunctionSpace.IsTransposeMap m m' := by
    intro g f hf
    rw [← weightedBracket_coeffsOn L hP A hA (m' g) f (Or.inr hf),
      ← weightedBracket_coeffsOn L hP A' hA' g (m f) (Or.inr (hcar f hf)), hm', hm]
    exact hadj _ _ ((hasFiniteSupport_coeffsOn_iff L A hA f).2 hf)
  have hspec : PairedFunctionSpace.IsTransposeMap m (PairedFunctionSpace.transposeMap m) :=
    Classical.epsilon_spec (p := PairedFunctionSpace.IsTransposeMap m) ⟨m', htr⟩
  exact ⟨m, m', fun f => ⟨(m f).2, hm f⟩, fun g => ⟨(m' g).2, hm' g⟩, hcar, htr,
    transposeMap_unique L hL0 hP A A' hA m m' _ htr hspec⟩
end YangMills.Construction.LocalKernels.PairBrackets
end
