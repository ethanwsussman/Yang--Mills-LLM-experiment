import YangMills.Construction.Towers.BracketsAndTransposesOnThePairsProof
import YangMills.Construction.Towers.CellsAndClassesOfThePeriodicExtension
import YangMills.Construction.Towers.LocalLinearMapsWithAPeriodicCounterpart
import YangMills.Construction.Towers.SumsProductsAndTransposesOfDescendingKernels
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels.Periodisation.PeriodicCounterpart
open Matrices (ComplexMatrix2)
open PeriodicOperators (KernelMatrix applyKernel)
open OneLoop (pauliCoordinateEquiv)
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, Tower.pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem halfTrace_mul_eq_sum (hP : OneLoop.PauliMatrixRelations) {X Y : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (hY : Y ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.halfTrace (X * Y) = ∑ a, Tower.pauliCoeff a X * Tower.pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p22145 <;> assumption
theorem exists_coeffs_linearEquiv {J σ ι : Type} (W : Submodule ℂ (ι → ComplexMatrix2))
    (ρ : J ≃ Fin 3 × σ) (val : (ι → ComplexMatrix2) → σ → ComplexMatrix2)
    (hadd : ∀ f g, val (f + g) = val f + val g)
    (hsmul : ∀ (c : ℂ) f, val (c • f) = c • val f)
    (hmem : ∀ f ∈ W, ∀ s, val f s ∈ ComplexMatrix2.traceless)
    (hinj : ∀ f ∈ W, ∀ g ∈ W, val f = val g → f = g)
    (hsurj : ∀ w : σ → ComplexMatrix2, (∀ s, w s ∈ ComplexMatrix2.traceless) →
      ∃ f ∈ W, val f = w) :
    ∃ Φ : W ≃ₗ[ℂ] (J → ℂ), ∀ f : W, Φ f = fun j => Tower.toPauliCoeffs (val f) (ρ j) := by apply _root_.YangMills.Construction.LocalKernels.PairBrackets.exists_linearEquiv_coeffs <;> assumption
section QuotientEdges
variable {L n k j : ℕ}
theorem edge_isPositivelyOriented_or_opposite (b : Tower.Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem edge_not_isPositivelyOriented_opposite (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j ≤ k)
    (b : Tower.Edge L n k j) (hb : b.IsPositivelyOriented) :
    ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
theorem exists_quotient_form
    (hnb : ∀ b : Tower.Edge L n k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (w : Tower.PositiveEdge L n k j → ComplexMatrix2) (hw : ∀ b, w b ∈ ComplexMatrix2.traceless) :
    ∃ B ∈ Tower.complexEdgeForms L n k j, Tower.restrictToPositiveEdges B = w := by
  classical
  let B : Tower.Edge L n k j → ComplexMatrix2 := fun b =>
    if h : b.IsPositivelyOriented then w ⟨b, h⟩
    else -w ⟨b.opposite, (edge_isPositivelyOriented_or_opposite b).resolve_left h⟩
  have hpos : ∀ b (h : b.IsPositivelyOriented), B b = w ⟨b, h⟩ := fun b h => dif_pos h
  have hneg : ∀ b (h : ¬ b.IsPositivelyOriented),
      B b = -w ⟨b.opposite, (edge_isPositivelyOriented_or_opposite b).resolve_left h⟩ :=
    fun b h => dif_neg h
  refine ⟨B, ⟨fun b hb => ?_, fun b => ?_⟩, funext fun b => hpos b.1 b.2⟩
  · rw [hpos b hb]
    exact hw _
  · by_cases h : b.IsPositivelyOriented
    · rw [hneg b.opposite (hnb b h), hpos b h]
      rfl
    · have h' := (edge_isPositivelyOriented_or_opposite b).resolve_left h
      rw [hpos b.opposite h', hneg b h, neg_neg]
theorem quotient_form_eq_of_restrict {B B' : Tower.Edge L n k j → ComplexMatrix2}
    (hB : B ∈ Tower.complexEdgeForms L n k j) (hB' : B' ∈ Tower.complexEdgeForms L n k j)
    (h : Tower.restrictToPositiveEdges B = Tower.restrictToPositiveEdges B') : B = B' := by
  have hpos : ∀ b (hb : b.IsPositivelyOriented), B b = B' b := fun b hb => congrFun h ⟨b, hb⟩
  funext b
  rcases edge_isPositivelyOriented_or_opposite b with hb | hb
  · exact hpos b hb
  · have h₁ : B b.opposite = -B b := hB.2 b
    have h₂ : B' b.opposite = -B' b := hB'.2 b
    have h₃ := hpos b.opposite hb
    rw [h₁, h₂] at h₃
    exact neg_injective h₃
end QuotientEdges
section ColourPairs
variable {k : ℕ} (L n : ℕ)
def colourCellEquiv (A : CellClass k) :
    Fin 3 × Cell L k A.level A.cellType ≃ Idx L A.colourPairs where
  toFun x := ⟨(), x⟩
  invFun ι := ι.2
  left_inv _ := rfl
  right_inv _ := rfl
theorem cellFn_mem_traceless (A : CellClass k) (hA : A.cellType ≠ .face)
    (f : (CellClass.fullSpace L A).complexSubmodule) (c : Cell L k A.level A.cellType) :
    CellClass.cellFn L A f c ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.LocalKernels.PairBrackets.cellFn_mem_traceless <;> assumption
theorem quotCellFn_mem_traceless (A : CellClass k) (hA : A.cellType ≠ .face)
    (f : (CellClass.quotSpace L n A).complexSubmodule) (c : QuotientCell L n k A.level A.cellType) :
    CellClass.quotCellFn L n A f c ∈ ComplexMatrix2.traceless := by
  rcases A with ⟨j, hj, _ | _ | _⟩
  · exact f.2 c (mem_univ c)
  · exact f.2.1 c.1 c.2
  · exact absurd rfl hA
theorem exists_coeffsOn_linearEquiv (hL : 0 < L) (A : CellClass k) (hA : A.cellType ≠ .face) :
    ∃ Φ : (CellClass.fullSpace L A).complexSubmodule ≃ₗ[ℂ] (Idx L A.colourPairs → ℂ),
      ∀ f, Φ f = CellClass.coeffsOn L A f := by apply _root_.YangMills.Construction.LocalKernels.PairBrackets.exists_linearEquiv_coeffsOn <;> assumption
def imageCarrierEquiv (A : CellClass k)
    (hs : Function.Surjective (Cell.proj n :
      Cell L k A.level A.cellType → QuotientCell L n k A.level A.cellType)) :
    A.colourPairs.ImageCarrier L n ≃ Fin 3 × QuotientCell L n k A.level A.cellType where
  toFun κ := κ.2.1
  invFun x := ⟨(), ⟨x, ⟨(x.1, (hs x.2).choose), Prod.ext rfl (hs x.2).choose_spec⟩⟩⟩
  left_inv κ := by rcases κ with ⟨⟨⟩, p, hp⟩; rfl
  right_inv _ := rfl
theorem exists_quotCoeffsOn_linearEquiv (A : CellClass k) (hA : A.cellType ≠ .face)
    (hs : Function.Surjective (Cell.proj n :
      Cell L k A.level A.cellType → QuotientCell L n k A.level A.cellType))
    (hnb : ∀ b : Tower.Edge L n k A.level, b.IsPositivelyOriented →
      ¬ b.opposite.IsPositivelyOriented) :
    ∃ Ψ : (CellClass.quotSpace L n A).complexSubmodule ≃ₗ[ℂ] (A.colourPairs.ImageCarrier L n → ℂ),
      ∀ f, Ψ f = CellClass.quotCoeffsOn L n A f := by
  rcases A with ⟨j, hj, _ | _ | _⟩
  · exact exists_coeffs_linearEquiv
      (Matrices.GroupLieProduct.tracelessFunctions (Tower.Vertex L n k j))
      (imageCarrierEquiv L n ⟨j, hj, .vertex⟩ hs) (fun f => f) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun f hf s => hf s (mem_univ s)) (fun f _ g _ h => h)
      (fun w hw => ⟨w, fun s _ => hw s, rfl⟩)
  · exact exists_coeffs_linearEquiv (Tower.complexEdgeForms L n k j)
      (imageCarrierEquiv L n ⟨j, hj, .edge⟩ hs) Tower.restrictToPositiveEdges
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun f hf s => hf.1 s.1 s.2) (fun f hf g hg h => quotient_form_eq_of_restrict hf hg h)
      (fun w hw => exists_quotient_form hnb w hw)
  · exact absurd rfl hA
theorem quotSpace_pair_eq (A : CellClass k) (hA : A.cellType ≠ .face)
    (f g : (CellClass.quotSpace L n A).index → ComplexMatrix2) :
    (CellClass.quotSpace L n A).pair f g =
      Tower.traceFinsumPairing (CellClass.quotCellFn L n A f) (CellClass.quotCellFn L n A g) := by
  rcases A with ⟨j, hj, _ | _ | _⟩
  · rfl
  · rfl
  · exact absurd rfl hA
theorem quotSpace_isFinitelySupported (A : CellClass k) (hA : A.cellType ≠ .face)
    (hfin : Finite (QuotientCell L n k A.level A.cellType))
    (f : (CellClass.quotSpace L n A).index → ComplexMatrix2) :
    (CellClass.quotSpace L n A).IsFinitelySupported f := by
  rcases A with ⟨j, hj, _ | _ | _⟩
  · have : Finite (Tower.Vertex L n k j) := hfin
    exact Set.toFinite _
  · have : Finite (Tower.PositiveEdge L n k j) := hfin
    exact Set.toFinite _
  · exact absurd rfl hA
theorem tsum_coeffs_mul_eq_pairing (hP : OneLoop.PauliMatrixRelations) {σ : Type} [Finite σ]
    (u v : σ → ComplexMatrix2) (hu : ∀ s, u s ∈ ComplexMatrix2.traceless)
    (hv : ∀ s, v s ∈ ComplexMatrix2.traceless) :
    ∑' ι : Fin 3 × σ, Tower.toPauliCoeffs u ι * Tower.toPauliCoeffs v ι =
      Tower.traceFinsumPairing u v := by
  have := Fintype.ofFinite σ
  unfold Tower.traceFinsumPairing
  rw [finsum_eq_sum_of_fintype, tsum_fintype, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [halfTrace_mul_eq_sum hP (hu s) (hv s)]
  rfl
theorem quotBracket_quotCoeffsOn (hP : OneLoop.PauliMatrixRelations) (A : CellClass k)
    (hA : A.cellType ≠ .face)
    (hs : Function.Surjective (Cell.proj n :
      Cell L k A.level A.cellType → QuotientCell L n k A.level A.cellType))
    (hfin : Finite (QuotientCell L n k A.level A.cellType))
    (f g : (CellClass.quotSpace L n A).complexSubmodule) :
    quotBracket L n A.colourPairs (CellClass.quotCoeffsOn L n A f)
        (CellClass.quotCoeffsOn L n A g) =
      (CellClass.quotSpace L n A).pair f g := by
  rw [quotSpace_pair_eq L n A hA]
  rw [← tsum_coeffs_mul_eq_pairing hP _ _ (quotCellFn_mem_traceless L n A hA f)
    (quotCellFn_mem_traceless L n A hA g)]
  unfold quotBracket PeriodicOperators.wPairing
  rw [← (imageCarrierEquiv L n A hs).symm.tsum_eq]
  refine tsum_congr fun x => ?_
  show ((1 : ℝ) : ℂ) * _ = _
  simp only [Complex.ofReal_one, one_mul]
  rfl
theorem quotBracket_single (A : CellClass k) (u δ : A.colourPairs.ImageCarrier L n → ℂ)
    (κ : A.colourPairs.ImageCarrier L n) (h₁ : δ κ = 1) (h₀ : ∀ j, j ≠ κ → δ j = 0) :
    quotBracket L n A.colourPairs u δ = u κ := by
  unfold quotBracket PeriodicOperators.wPairing
  rw [tsum_eq_single κ]
  · show ((1 : ℝ) : ℂ) * _ = _
    rw [h₁]
    simp
  · intro j hj
    rw [h₀ j hj]
    simp
theorem quotBracket_quotMatrixT (A A' : CellClass k)
    (hfin : Finite (A.colourPairs.ImageCarrier L n))
    (hfin' : Finite (A'.colourPairs.ImageCarrier L n))
    (M : KernelMatrix (A.colourPairs.ImageCarrier L n) (A'.colourPairs.ImageCarrier L n))
    (g : A'.colourPairs.ImageCarrier L n → ℂ) (f : A.colourPairs.ImageCarrier L n → ℂ) :
    quotBracket L n A.colourPairs (applyKernel (quotMatrixT L n A.colourPairs A'.colourPairs M) g) f =
      quotBracket L n A'.colourPairs g (applyKernel M f) := by
  have := Fintype.ofFinite (A.colourPairs.ImageCarrier L n)
  have := Fintype.ofFinite (A'.colourPairs.ImageCarrier L n)
  have hw : ∀ κ, A.colourPairs.imageWeight L n κ = 1 := fun _ => rfl
  have hw' : ∀ κ, A'.colourPairs.imageWeight L n κ = 1 := fun _ => rfl
  unfold quotBracket PeriodicOperators.wPairing quotMatrixT PeriodicOperators.wTranspose
    applyKernel
  simp only [tsum_fintype, hw, hw', Complex.ofReal_one, one_mul, div_one, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring
theorem transposeMap_unique (hP : OneLoop.PauliMatrixRelations)
    (A A' : CellClass k) (hA : A.cellType ≠ .face)
    (hs : Function.Surjective (Cell.proj n :
      Cell L k A.level A.cellType → QuotientCell L n k A.level A.cellType))
    (hfin : Finite (QuotientCell L n k A.level A.cellType))
    (Ψ : (CellClass.quotSpace L n A).complexSubmodule ≃ₗ[ℂ] (A.colourPairs.ImageCarrier L n → ℂ))
    (hΨ : ∀ f, Ψ f = CellClass.quotCoeffsOn L n A f)
    (m : (CellClass.quotSpace L n A).complexSubmodule →ₗ[ℂ]
      (CellClass.quotSpace L n A').complexSubmodule)
    (m₁ m₂ : (CellClass.quotSpace L n A').complexSubmodule →ₗ[ℂ]
      (CellClass.quotSpace L n A).complexSubmodule)
    (h₁ : Tower.PairedFunctionSpace.IsTransposeMap m m₁)
    (h₂ : Tower.PairedFunctionSpace.IsTransposeMap m m₂) : m₁ = m₂ := by
  classical
  refine LinearMap.ext fun g => Ψ.injective ?_
  rw [hΨ, hΨ]
  funext κ
  let δ : A.colourPairs.ImageCarrier L n → ℂ := fun j => if j = κ then 1 else 0
  have hread : CellClass.quotCoeffsOn L n A (Ψ.symm δ) = δ := by
    rw [← hΨ, LinearEquiv.apply_symm_apply]
  have e : ∀ h : (CellClass.quotSpace L n A).complexSubmodule,
      CellClass.quotCoeffsOn L n A h κ = (CellClass.quotSpace L n A).pair h (Ψ.symm δ) :=
    fun h => by
      rw [← quotBracket_quotCoeffsOn L n hP A hA hs hfin h _, hread]
      exact (quotBracket_single L n A _ δ κ (if_pos rfl) fun j hj => if_neg hj).symm
  have hfs := quotSpace_isFinitelySupported L n A hA hfin (Ψ.symm δ)
  rw [e, e, h₁ g _ hfs, h₂ g _ hfs]
end ColourPairs
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
theorem exists_kernel_of_local {J J' : Type} (W : (J → ℂ) →ₗ[ℂ] (J' → ℂ))
    (near : J' → J → Prop) (hfin : ∀ ι', {ι | near ι' ι}.Finite)
    (hread : ∀ (f g : J → ℂ) (ι' : J'), (∀ ι, near ι' ι → f ι = g ι) → W f ι' = W g ι') :
    ∃ T : KernelMatrix J J', (∀ ι' ι, ¬ near ι' ι → T ι' ι = 0) ∧
      ∀ f, applyKernel T f = W f := by
  classical
  let e : J → J → ℂ := fun ι j => if j = ι then 1 else 0
  let T : KernelMatrix J J' := fun ι' ι => W (e ι) ι'
  have hT : ∀ ι' ι, ¬ near ι' ι → T ι' ι = 0 := by
    intro ι' ι h
    have h₀ := hread (e ι) 0 ι' fun j hj => if_neg fun hji : j = ι => h (hji ▸ hj)
    rw [map_zero] at h₀
    exact h₀
  refine ⟨T, hT, fun f => ?_⟩
  funext ι'
  let F : Finset J := (hfin ι').toFinset
  let g : J → ℂ := ∑ ι ∈ F, f ι • e ι
  have hg : ∀ j, near ι' j → f j = g j := by
    intro j hj
    have hjF : j ∈ F := (hfin ι').mem_toFinset.2 hj
    simp only [g, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij.symm]
    · intro h
      exact absurd hjF h
  rw [hread f g ι' hg]
  show ∑' ι, T ι' ι * f ι = _
  rw [tsum_eq_sum (s := F)]
  · simp only [g, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun ι _ => mul_comm _ _
  · intro ι hι
    have h : ¬ near ι' ι := fun h => hι ((hfin ι').mem_toFinset.2 h)
    rw [hT ι' ι h, zero_mul]
section Maps
variable {k : ℕ} (L n : ℕ) (A A' : CellClass k)
def fullLinearMap {R : ℝ} {m : ((CellClass.fullSpace L A).index → ComplexMatrix2) →
      (CellClass.fullSpace L A').index → ComplexMatrix2}
    (h : IsLocalLinearFull L A A' R m) :
    (CellClass.fullSpace L A).complexSubmodule →ₗ[ℂ] (CellClass.fullSpace L A').complexSubmodule where
  toFun f := ⟨m f, h.map_mem f f.2⟩
  map_add' f g := Subtype.ext (h.map_add f f.2 g g.2)
  map_smul' c f := Subtype.ext (h.map_smul c f f.2)
def quotLinearMap {m : ((CellClass.quotSpace L n A).index → ComplexMatrix2) →
      (CellClass.quotSpace L n A').index → ComplexMatrix2}
    (h : IsLinearPeriodic L n A A' m) :
    (CellClass.quotSpace L n A).complexSubmodule →ₗ[ℂ]
      (CellClass.quotSpace L n A').complexSubmodule where
  toFun f := ⟨m f, h.map_mem f f.2⟩
  map_add' f g := Subtype.ext (h.map_add f f.2 g g.2)
  map_smul' c f := Subtype.ext (h.map_smul c f f.2)
theorem coeffsOn_eq_lift (u : (CellClass.fullSpace L A).index → ComplexMatrix2)
    (v : (CellClass.quotSpace L n A).index → ComplexMatrix2)
    (h : ∀ c : Cell L k A.level A.cellType,
      CellClass.cellFn L A u c = CellClass.quotCellFn L n A v (Cell.proj n c)) :
    CellClass.coeffsOn L A u = A.colourPairs.lift L n (CellClass.quotCoeffsOn L n A v) := by
  funext ι
  obtain ⟨x, rfl⟩ := (colourCellEquiv L A).surjective ι
  show Tower.pauliCoeff x.1 (CellClass.cellFn L A u x.2) =
    Tower.pauliCoeff x.1 (CellClass.quotCellFn L n A v (Cell.proj n x.2))
  rw [h]
theorem periodicExtension_mem_and_cellFn (hq : Tower.EdgeProjectionProperties)
    (hc : PeriodicLiftCells.CellsAndClassesHold) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) (A : CellClass k) :
    (∀ f ∈ (CellClass.quotSpace L n A).complexSubmodule,
      CellClass.periodicExtension L n A f ∈ (CellClass.fullSpace L A).complexSubmodule) ∧
    ∀ (f : (CellClass.quotSpace L n A).index → ComplexMatrix2) (c : Cell L k A.level A.cellType),
      CellClass.cellFn L A (CellClass.periodicExtension L n A f) c =
        CellClass.quotCellFn L n A f (Cell.proj n c) := by
  obtain ⟨j, hj, kind⟩ := A
  cases kind with
  | vertex =>
    refine ⟨fun f hf => ?_, fun f c => rfl⟩
    exact Submodule.mem_pi.2 fun x _ => Submodule.mem_pi.1 hf _ (Set.mem_univ _)
  | face =>
    refine ⟨fun f hf => ?_, fun f c => rfl⟩
    exact Submodule.mem_pi.2 fun x _ => Submodule.mem_pi.1 hf _ (Set.mem_univ _)
  | edge =>
    refine ⟨fun f hf => ?_, fun f c => ?_⟩
    · have h1 := (hq L n k j hL hn hj).1
      have hf' : PeriodicLattice.IsBondForm PeriodicLattice.complexLieAlgebra f := hf
      refine And.intro (fun b hb => hf'.1 _ ((h1 b).2.2.1 hb)) fun b => ?_
      change f (Tower.FullSpace.projEdge L n k j b.opposite) =
        -f (Tower.FullSpace.projEdge L n k j b)
      rw [← (h1 b).2.2.2]
      exact hf'.2 _
    · have h2 := ((hc L hL k n hn).1 j hj).2.2.1 c
      change f (Tower.FullSpace.projEdge L n k j c.1) = f (projPositiveEdge L n k j c).1
      rw [h2]
theorem finite_within_radius (hEv : LocalKernelFacts (k := k) L) (R : ℝ) (hR : 0 ≤ R)
    (ι' : Idx L A'.colourPairs) :
    {ι : Idx L A.colourPairs | TorusMetric.supNormVec
      ((A.colourPairs.toPeriodicData L).pos ι - (A'.colourPairs.toPeriodicData L).pos ι') ≤ R}.Finite := by
  classical
  let T₀ : KernelMatrix (Idx L A.colourPairs) (Idx L A'.colourPairs) := fun ι' ι =>
    if TorusMetric.supNormVec
      ((A.colourPairs.toPeriodicData L).pos ι - (A'.colourPairs.toPeriodicData L).pos ι') ≤ R
    then 1 else 0
  have hloc : IsRLocal L A.colourPairs A'.colourPairs R T₀ := fun ι' ι h => if_neg h
  refine ((hEv A.colourPairs A'.colourPairs R hR T₀ hloc).1 (fun _ => 1) ι').subset fun ι hι => ?_
  have hι' : TorusMetric.supNormVec
      ((A.colourPairs.toPeriodicData L).pos ι - (A'.colourPairs.toPeriodicData L).pos ι') ≤ R := hι
  simp [T₀, hι']
theorem cellFn_eq_of_coeffsOn (hA : A.cellType ≠ .face)
    (f g : (CellClass.fullSpace L A).complexSubmodule) (c : Cell L k A.level A.cellType)
    (h : ∀ a, CellClass.coeffsOn L A f (colourCellEquiv L A (a, c)) =
      CellClass.coeffsOn L A g (colourCellEquiv L A (a, c))) :
    CellClass.cellFn L A f c = CellClass.cellFn L A g c := by
  rw [← sum_pauliCoeff_smul (cellFn_mem_traceless L A hA f c),
    ← sum_pauliCoeff_smul (cellFn_mem_traceless L A hA g c)]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h' : Tower.pauliCoeff a (CellClass.cellFn L A f c) =
      Tower.pauliCoeff a (CellClass.cellFn L A g c) := h a
  rw [h']
end Maps
theorem localLinearMapsPeriodize (hLat : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hP : OneLoop.PauliMatrixRelations)
    (hC : PeriodicLiftCells.CellsAndClassesHold)
    (hK : KernelsAndLinearMapMatrices)
    (hq : Tower.EdgeProjectionProperties)
    (hS : DescendingKernelAlgebra) : LocalLinearMapsPeriodize := by
  intro L hL k n hn A A' hA hA' R hR hR2 mW mT hm
  obtain ⟨hW, hT, hcar⟩ := hm
  have hL0 : 0 < L := by
    have := hL.2
    omega
  obtain ⟨hEv, hLM⟩ := hK L hL k n hn
  have hsurj : ∀ B : CellClass k, Function.Surjective (Cell.proj n :
      Cell L k B.level B.cellType → QuotientCell L n k B.level B.cellType) := fun B =>
    (((hC L hL k n hn).1 B.level B.level_le).1 B.cellType).1
  have himg : ∀ B : CellClass k, Finite (B.colourPairs.ImageCarrier L n) := fun B =>
    ((hC L hL k n hn).2 B.colourPairs).1
  have hcell : ∀ B : CellClass k, Finite (QuotientCell L n k B.level B.cellType) := fun B => by
    have := himg B
    have : Finite (Fin 3 × QuotientCell L n k B.level B.cellType) :=
      Finite.of_equiv _ (imageCarrierEquiv L n B (hsurj B))
    exact Finite.of_surjective (Prod.snd : Fin 3 × QuotientCell L n k B.level B.cellType → _)
      fun c => ⟨(0, c), rfl⟩
  have hnb : ∀ B : CellClass k, ∀ b : Tower.Edge L n k B.level, b.IsPositivelyOriented →
      ¬ b.opposite.IsPositivelyOriented := fun B b hb =>
    edge_not_isPositivelyOriented_opposite hLat hL hn B.level_le b hb
  obtain ⟨Φ, hΦ⟩ := exists_coeffsOn_linearEquiv L hL0 A hA
  obtain ⟨Φ', hΦ'⟩ := exists_coeffsOn_linearEquiv L hL0 A' hA'
  obtain ⟨Ψ, hΨ⟩ := exists_quotCoeffsOn_linearEquiv L n A hA (hsurj A) (hnb A)
  obtain ⟨Ψ', hΨ'⟩ := exists_quotCoeffsOn_linearEquiv L n A' hA' (hsurj A') (hnb A')
  let wl := fullLinearMap L A A' hW
  let W : (Idx L A.colourPairs → ℂ) →ₗ[ℂ] (Idx L A'.colourPairs → ℂ) :=
    Φ'.toLinearMap ∘ₗ wl ∘ₗ Φ.symm.toLinearMap
  obtain ⟨T, hTloc, hTW⟩ := exists_kernel_of_local W
    (fun ι' ι => TorusMetric.supNormVec
      ((A.colourPairs.toPeriodicData L).pos ι - (A'.colourPairs.toPeriodicData L).pos ι') ≤ R)
    (finite_within_radius L A A' hEv R hR)
    (by
      intro f g ι' hfg
      obtain ⟨x, rfl⟩ := (colourCellEquiv L A').surjective ι'
      have hv : CellClass.cellFn L A' (mW (Φ.symm f)) x.2 =
          CellClass.cellFn L A' (mW (Φ.symm g)) x.2 :=
        hW.local_dependence _ (Φ.symm f).2 _ (Φ.symm g).2 x.2 fun c hc =>
          cellFn_eq_of_coeffsOn L A hA (Φ.symm f) (Φ.symm g) c fun a => by
            rw [← hΦ, ← hΦ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
            exact hfg _ hc
      show Φ' (wl (Φ.symm f)) _ = Φ' (wl (Φ.symm g)) _
      rw [hΦ', hΦ']
      show Tower.pauliCoeff x.1 (CellClass.cellFn L A' (mW (Φ.symm f)) x.2) =
        Tower.pauliCoeff x.1 (CellClass.cellFn L A' (mW (Φ.symm g)) x.2)
      rw [hv])
  have hlocal : IsRLocal L A.colourPairs A'.colourPairs R T := fun ι' ι h => hTloc ι' ι h
  have hgiven : ∀ F : (CellClass.fullSpace L A).complexSubmodule,
      CellClass.coeffsOn L A' (mW F) = applyKernel T (CellClass.coeffsOn L A F) := by
    intro F
    rw [hTW, ← hΦ F]
    show _ = Φ' (wl (Φ.symm (Φ F)))
    rw [LinearEquiv.symm_apply_apply, hΦ']
    rfl
  let tl := quotLinearMap L n A A' hT
  obtain ⟨M, hM, -⟩ := hLM A.colourPairs A'.colourPairs
    (Ψ'.toLinearMap ∘ₗ tl ∘ₗ Ψ.symm.toLinearMap)
  have hMread : ∀ f : (CellClass.quotSpace L n A).complexSubmodule,
      CellClass.quotCoeffsOn L n A' (tl f) =
        applyKernel M (CellClass.quotCoeffsOn L n A f) := by
    intro f
    have h := hM (Ψ f) (mem_univ _)
    rw [← hΨ f, ← h]
    show _ = Ψ' (tl (Ψ.symm (Ψ f)))
    rw [LinearEquiv.symm_apply_apply, hΨ']
  have hdesc : KernelDescends L n A.colourPairs A'.colourPairs T M := by
    refine ⟨⟨R, hR, hlocal⟩, fun g => ?_⟩
    have hg : CellClass.quotCoeffsOn L n A (Ψ.symm g) = g := by
      rw [← hΨ, LinearEquiv.apply_symm_apply]
    have hE := periodicExtension_mem_and_cellFn L n hq hC hL hn A
    have hext := hE.1 _ (Ψ.symm g).2
    have h₁ := coeffsOn_eq_lift L n A (CellClass.periodicExtension L n A (Ψ.symm g)) (Ψ.symm g)
      (hE.2 _)
    have h₂ := coeffsOn_eq_lift L n A' (mW (CellClass.periodicExtension L n A (Ψ.symm g)))
      (mT (Ψ.symm g)) (hcar _ (Ψ.symm g).2)
    have h₃ := hgiven ⟨_, hext⟩
    have h₄ := hMread (Ψ.symm g)
    rw [hg] at h₁ h₄
    rw [← h₁, ← h₄]
    exact h₃.symm.trans h₂
  have hz : KernelDescends L n A.colourPairs A.colourPairs (fun _ _ => 0) (fun _ _ => 0) := by
    refine ⟨⟨R, hR, fun _ _ _ => rfl⟩, fun f => ?_⟩
    funext ι
    simp [applyKernel, WeightedIndexSet.lift]
  have hdesc' := ((hS L hL k n hn A.colourPairs A'.colourPairs A.colourPairs R hR T T
    (fun _ _ => 0) M M (fun _ _ => 0) hlocal hlocal (fun _ _ _ => rfl) hdesc hdesc hz).2.2.2.2.2
    hR2).2.2
  have := himg A
  have := himg A'
  let Mt := quotMatrixT L n A.colourPairs A'.colourPairs M
  let m' : (CellClass.quotSpace L n A').complexSubmodule →ₗ[ℂ]
      (CellClass.quotSpace L n A).complexSubmodule :=
    Ψ.symm.toLinearMap ∘ₗ kernelLinearMap Mt (fun _ _ => Set.toFinite _) ∘ₗ Ψ'.toLinearMap
  have hm'read : ∀ g, CellClass.quotCoeffsOn L n A (m' g) =
      applyKernel Mt (CellClass.quotCoeffsOn L n A' g) := by
    intro g
    rw [← hΨ, ← hΨ']
    show Ψ (Ψ.symm (applyKernel Mt (Ψ' g))) = _
    rw [LinearEquiv.apply_symm_apply]
  have htr : Tower.PairedFunctionSpace.IsTransposeMap tl m' := by
    intro g f _
    rw [← quotBracket_quotCoeffsOn L n hP A hA (hsurj A) (hcell A) (m' g) f,
      ← quotBracket_quotCoeffsOn L n hP A' hA' (hsurj A') (hcell A') g (tl f), hm'read, hMread]
    exact quotBracket_quotMatrixT L n A A' (himg A) (himg A') M _ _
  have hspec : Tower.PairedFunctionSpace.IsTransposeMap tl
      (Tower.PairedFunctionSpace.transposeMap tl) :=
    Classical.epsilon_spec (p := Tower.PairedFunctionSpace.IsTransposeMap tl) ⟨m', htr⟩
  have heq : Tower.PairedFunctionSpace.transposeMap tl = m' :=
    transposeMap_unique L n hP A A' hA (hsurj A) (hcell A) Ψ hΨ tl _ _ hspec htr
  refine ⟨T, tl, hlocal, fun F => ⟨hW.map_mem F F.2, hgiven F⟩, fun f => rfl, ⟨M, hMread, hdesc⟩,
    ⟨Mt, fun g => ?_, hdesc'⟩⟩
  rw [heq]
  exact hm'read g
end YangMills.Construction.LocalKernels.Periodisation.PeriodicCounterpart
end
