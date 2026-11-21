import YangMills.Construction.Towers.CommutatorTermAtAPeriodicExtensionDescendsProof
import YangMills.Construction.Towers.IteratedAveragesOfAPeriodicExtension
import YangMills.Construction.Towers.SecondDifferentialOfTheActionDescendsProof
import YangMills.Construction.Towers.SecondOrderKernelAtAPeriodicExtensionDescends
import YangMills.Construction.Towers.SecondOrderTermAtTheSideInfinityIsLocal
import YangMills.Construction.Towers.SecondOrderTermOfAPeriodicExtension
import YangMills.Construction.Towers.SecondOrderTermsAtAPeriodicExtension
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.LocalKernels.KernelDescent
open Periodisation Tower Matrices
open Tower.AsDifferentials (boundedSubmodule complexQuadraticTerm quadraticTermAt)
open PeriodicOperators (KernelMatrix)
private theorem pauliCombination_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
private theorem pauliCoeff_pauliCombination (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
private theorem pauliCombination_pauliCoeff {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
private theorem pauliCoeff_add (a : Fin 3) {X Y : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p106 <;> assumption
private theorem pauliCoeff_smul (a : Fin 3) (z : ℂ) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (z • X) = z * pauliCoeff a X := by apply _root_.YangMills.SharedProofs.p5172 <;> assumption
private theorem wPairing_toPauliCoeffs (hP : OneLoop.PauliMatrixRelations)
    {σ J : Type} (e : J ≃ Fin 3 × σ) (w : J → ℝ) (hw : ∀ i, w i = 1) (f g : σ → ComplexMatrix2)
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) (hg : ∀ x, g x ∈ ComplexMatrix2.traceless)
    (hfin : HasFiniteSupp f ∨ HasFiniteSupp g) :
    PeriodicOperators.wPairing w (fun i => toPauliCoeffs f (e i))
        (fun i => toPauliCoeffs g (e i)) = traceFinsumPairing f g := by apply _root_.YangMills.SharedProofs.p12066 <;> assumption
section OddForms
variable {β : Type} {pos : β → Prop} (rev : β → β)
def oddFormOfCoeffs (c : Fin 3 × {b // pos b} → ℂ) : β → ComplexMatrix2 :=
  open Classical in fun b =>
    if h : pos b then ofPauliCoeffs c ⟨b, h⟩
    else if h' : pos (rev b) then -ofPauliCoeffs c ⟨rev b, h'⟩ else 0
variable {rev}
theorem oddFormOfCoeffs_of_pos (c : Fin 3 × {b // pos b} → ℂ) {b : β} (h : pos b) :
    oddFormOfCoeffs rev c b = ofPauliCoeffs c ⟨b, h⟩ := dif_pos h
theorem oddFormOfCoeffs_mem_traceless (c : Fin 3 × {b // pos b} → ℂ) {b : β} (h : pos b) :
    oddFormOfCoeffs rev c b ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.LocalKernels.BracketAtPeriodicLift.antisymmExtend_mem <;> assumption
theorem toPauliCoeffs_oddFormOfCoeffs (c : Fin 3 × {b // pos b} → ℂ) :
    toPauliCoeffs (fun b : {b // pos b} => oddFormOfCoeffs rev c b.1) = c := by apply _root_.YangMills.Construction.LocalKernels.BracketAtPeriodicLift.toPauliCoeffs_antisymmExtend <;> assumption
theorem oddFormOfCoeffs_opposite (hrr : ∀ b, rev (rev b) = b)
    (hx : ∀ b, Xor (pos b) (pos (rev b))) (c : Fin 3 × {b // pos b} → ℂ) (b : β) :
    oddFormOfCoeffs rev c (rev b) = -oddFormOfCoeffs rev c b := by apply _root_.YangMills.Construction.LocalKernels.BracketAtPeriodicLift.antisymmExtend_rev <;> assumption
theorem oddFormOfCoeffs_toPauliCoeffs (hrr : ∀ b, rev (rev b) = b)
    (hx : ∀ b, Xor (pos b) (pos (rev b))) {B : β → ComplexMatrix2}
    (hm : ∀ b, pos b → B b ∈ ComplexMatrix2.traceless) (hr : ∀ b, B (rev b) = -B b) :
    oddFormOfCoeffs rev (toPauliCoeffs fun b : {b // pos b} => B b.1) = B := by apply _root_.YangMills.Construction.LocalKernels.BracketAtPeriodicLift.antisymmExtend_toPauliCoeffs <;> assumption
theorem oddFormOfCoeffs_add (c c' : Fin 3 × {b // pos b} → ℂ) :
    oddFormOfCoeffs rev (c + c') = oddFormOfCoeffs rev c + oddFormOfCoeffs rev c' := by apply _root_.YangMills.Construction.LocalKernels.BracketAtPeriodicLift.antisymmExtend_add <;> assumption
theorem oddFormOfCoeffs_smul (z : ℂ) (c : Fin 3 × {b // pos b} → ℂ) :
    oddFormOfCoeffs rev (z • c) = z • oddFormOfCoeffs rev c := by apply _root_.YangMills.Construction.LocalKernels.BracketAtPeriodicLift.antisymmExtend_smul <;> assumption
theorem oddFormOfCoeffs_bounded {c : Fin 3 × {b // pos b} → ℂ} (hc : ∃ C : ℝ, ∀ p, ‖c p‖ ≤ C) :
    ∃ C : ℝ, ∀ b, ComplexMatrix2.operatorNorm (oddFormOfCoeffs rev c b) ≤ C := by
  obtain ⟨C, hC⟩ := hc
  have h0 : ∀ b, ‖ofPauliCoeffs c b‖ ≤ ∑ a, C * ‖ComplexMatrix2.pauliFamily a‖ := by
    intro b
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (norm_smul_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  refine ⟨max (∑ a, C * ‖ComplexMatrix2.pauliFamily a‖) 0, fun b => ?_⟩
  by_cases h : pos b
  · rw [oddFormOfCoeffs_of_pos c h]
    exact (h0 _).trans (le_max_left _ _)
  · by_cases h' : pos (rev b)
    · have e : oddFormOfCoeffs rev c b = -ofPauliCoeffs c ⟨rev b, h'⟩ := by
        unfold oddFormOfCoeffs
        rw [dif_neg h, dif_pos h']
      rw [e]
      show ‖-ofPauliCoeffs c ⟨rev b, h'⟩‖ ≤ _
      rw [norm_neg]
      exact (h0 _).trans (le_max_left _ _)
    · have e : oddFormOfCoeffs rev c b = 0 := by
        unfold oddFormOfCoeffs
        rw [dif_neg h, dif_neg h']
      rw [e]
      show ‖(0 : ComplexMatrix2)‖ ≤ _
      rw [norm_zero]
      exact le_max_right _ _
end OddForms
section BilinearTerms
variable {β γ : Type} {P : Submodule ℂ (β → ComplexMatrix2)} {v : γ → (β → ComplexMatrix2) → ComplexMatrix2}
  {Q : (β → ComplexMatrix2) → γ → ComplexMatrix2}
private theorem quadraticTermAt_add_left {B₁ B₂ B' : β → ComplexMatrix2}
    (h₁ : B₁ ∈ boundedSubmodule P) (h₂ : B₂ ∈ boundedSubmodule P) (h' : B' ∈ boundedSubmodule P) :
    quadraticTermAt P v Q (B₁ + B₂) B' =
      quadraticTermAt P v Q B₁ B' + quadraticTermAt P v Q B₂ B' := by
  unfold quadraticTermAt
  rw [dif_pos ⟨add_mem h₁ h₂, h'⟩, dif_pos ⟨h₁, h'⟩, dif_pos ⟨h₂, h'⟩]
  have e : (⟨B₁ + B₂, add_mem h₁ h₂⟩ : boundedSubmodule P) = ⟨B₁, h₁⟩ + ⟨B₂, h₂⟩ := rfl
  rw [e, map_add, LinearMap.add_apply]
private theorem quadraticTermAt_smul_left (z : ℂ) {B B' : β → ComplexMatrix2}
    (h : B ∈ boundedSubmodule P) (h' : B' ∈ boundedSubmodule P) :
    quadraticTermAt P v Q (z • B) B' = z • quadraticTermAt P v Q B B' := by
  unfold quadraticTermAt
  rw [dif_pos ⟨Submodule.smul_mem _ z h, h'⟩, dif_pos ⟨h, h'⟩]
  have e : (⟨z • B, Submodule.smul_mem _ z h⟩ : boundedSubmodule P) = z • ⟨B, h⟩ := rfl
  rw [e, map_smul, LinearMap.smul_apply]
private theorem quadraticTermAt_add_right {B B₁ B₂ : β → ComplexMatrix2}
    (h : B ∈ boundedSubmodule P) (h₁ : B₁ ∈ boundedSubmodule P) (h₂ : B₂ ∈ boundedSubmodule P) :
    quadraticTermAt P v Q B (B₁ + B₂) =
      quadraticTermAt P v Q B B₁ + quadraticTermAt P v Q B B₂ := by
  unfold quadraticTermAt
  rw [dif_pos ⟨h, add_mem h₁ h₂⟩, dif_pos ⟨h, h₁⟩, dif_pos ⟨h, h₂⟩]
  have e : (⟨B₁ + B₂, add_mem h₁ h₂⟩ : boundedSubmodule P) = ⟨B₁, h₁⟩ + ⟨B₂, h₂⟩ := rfl
  rw [e, map_add]
private theorem quadraticTermAt_smul_right (z : ℂ) {B B' : β → ComplexMatrix2}
    (h : B ∈ boundedSubmodule P) (h' : B' ∈ boundedSubmodule P) :
    quadraticTermAt P v Q B (z • B') = z • quadraticTermAt P v Q B B' := by
  unfold quadraticTermAt
  rw [dif_pos ⟨h, Submodule.smul_mem _ z h'⟩, dif_pos ⟨h, h'⟩]
  have e : (⟨z • B', Submodule.smul_mem _ z h'⟩ : boundedSubmodule P) = z • ⟨B', h'⟩ := rfl
  rw [e, map_smul]
private theorem toPauliCoeffs_add {σ : Type} {X Y : σ → ComplexMatrix2}
    (hX : ∀ x, X x ∈ ComplexMatrix2.traceless) (hY : ∀ x, Y x ∈ ComplexMatrix2.traceless)
    (p : Fin 3 × σ) : toPauliCoeffs (X + Y) p = toPauliCoeffs X p + toPauliCoeffs Y p :=
  pauliCoeff_add p.1 (hX p.2) (hY p.2)
private theorem toPauliCoeffs_smul {σ : Type} (z : ℂ) {X : σ → ComplexMatrix2}
    (hX : ∀ x, X x ∈ ComplexMatrix2.traceless) (p : Fin 3 × σ) :
    toPauliCoeffs (z • X) p = z * toPauliCoeffs X p :=
  pauliCoeff_smul p.1 z (hX p.2)
end BilinearTerms
section TwoSides
variable {L m k j : ℕ}
def fullPairsEquiv (L k j : ℕ) (h : j ≤ k) :
    Idx L (CellClass.edgeClass k j h).colourPairs ≃ Fin 3 × PeriodicOperators.PosEdge L k j where
  toFun ι := ι.2
  invFun p := ⟨(), p⟩
  left_inv ι := by rcases ι with ⟨⟨⟩, p⟩; rfl
  right_inv _ := rfl
abbrev ProjSurjective (L m k j : ℕ) : Prop :=
  Function.Surjective (Cell.proj m : Cell L k j .edge → QuotientCell L m k j .edge)
theorem mem_colourPairs_image (h : j ≤ k) (hs : ProjSurjective L m k j)
    (p : Fin 3 × Tower.PositiveEdge L m k j) :
    p ∈ (CellClass.edgeClass k j h).colourComponent.image L m := by apply _root_.YangMills.Construction.LocalKernels.HessianAtLifts.mem_colourPairs_image <;> assumption
def quotPairsEquiv (h : j ≤ k) (hs : ProjSurjective L m k j) :
    (CellClass.edgeClass k j h).colourPairs.ImageCarrier L m ≃
      Fin 3 × Tower.PositiveEdge L m k j where
  toFun κ := κ.2.1
  invFun p := ⟨(), ⟨p, mem_colourPairs_image h hs p⟩⟩
  left_inv κ := by rcases κ with ⟨⟨⟩, p, hp⟩; rfl
  right_inv _ := rfl
def fullFormOf (h : j ≤ k) (f : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    FullSpace.Edge L k j → ComplexMatrix2 :=
  oddFormOfCoeffs (pos := fun b => b.IsPositivelyOriented) InfiniteLattice.Link.opposite
    fun p => f ((fullPairsEquiv L k j h).symm p)
def quotFormOf (h : j ≤ k) (hs : ProjSurjective L m k j)
    (f : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L m → ℂ) :
    Edge L m k j → ComplexMatrix2 :=
  oddFormOfCoeffs (pos := fun b => b.IsPositivelyOriented) PeriodicLattice.Bond.opposite
    fun p => f ((quotPairsEquiv h hs).symm p)
theorem link_opposite_opposite {a : ℝ} (b : InfiniteLattice.Link a) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_opposite <;> assumption
theorem link_xor_opposite {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.xor_isPositivelyOriented_opposite <;> assumption
theorem fullFormOf_mem (ha : 0 < meshAt L k j) (h : j ≤ k)
    (f : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    fullFormOf h f ∈ FullSpace.complexEdgeForms (meshAt L k j) :=
  ⟨fun _ hb => oddFormOfCoeffs_mem_traceless _ hb,
    oddFormOfCoeffs_opposite link_opposite_opposite (link_xor_opposite ha) _⟩
theorem quotFormOf_mem (hx : ∀ b : Edge L m k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (h : j ≤ k) (hs : ProjSurjective L m k j)
    (f : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L m → ℂ) :
    quotFormOf h hs f ∈ complexEdgeForms L m k j :=
  ⟨fun _ hb => oddFormOfCoeffs_mem_traceless _ hb,
    oddFormOfCoeffs_opposite PeriodicLattice.Bond.opposite_opposite hx _⟩
theorem fullFormOf_coeffsOn (ha : 0 < meshAt L k j) (h : j ≤ k)
    {B : FullSpace.Edge L k j → ComplexMatrix2} (hB : B ∈ FullSpace.complexEdgeForms (meshAt L k j)) :
    fullFormOf h (CellClass.coeffsOn L (CellClass.edgeClass k j h) B) = B :=
  oddFormOfCoeffs_toPauliCoeffs link_opposite_opposite (link_xor_opposite ha) hB.1 hB.2
theorem quotFormOf_quotCoeffsOn
    (hx : ∀ b : Edge L m k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (h : j ≤ k) (hs : ProjSurjective L m k j) {B : Edge L m k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L m k j) :
    quotFormOf h hs (CellClass.quotCoeffsOn L m (CellClass.edgeClass k j h) B) = B :=
  oddFormOfCoeffs_toPauliCoeffs PeriodicLattice.Bond.opposite_opposite hx hB.1 hB.2
theorem coeffsOn_fullFormOf (h : j ≤ k) (f : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    CellClass.coeffsOn L (CellClass.edgeClass k j h) (fullFormOf h f) = f := by
  funext ι
  have e := congrFun (toPauliCoeffs_oddFormOfCoeffs
    (pos := fun b : FullSpace.Edge L k j => b.IsPositivelyOriented)
    (rev := InfiniteLattice.Link.opposite) fun p => f ((fullPairsEquiv L k j h).symm p))
    (fullPairsEquiv L k j h ι)
  rw [Equiv.symm_apply_apply] at e
  exact e
theorem quotCoeffsOn_quotFormOf (h : j ≤ k) (hs : ProjSurjective L m k j)
    (f : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L m → ℂ) :
    CellClass.quotCoeffsOn L m (CellClass.edgeClass k j h) (quotFormOf h hs f) = f := by
  funext κ
  have e := congrFun (toPauliCoeffs_oddFormOfCoeffs
    (pos := fun b : Edge L m k j => b.IsPositivelyOriented)
    (rev := PeriodicLattice.Bond.opposite) fun p => f ((quotPairsEquiv h hs).symm p))
    (quotPairsEquiv h hs κ)
  rw [Equiv.symm_apply_apply] at e
  exact e
theorem fullFormOf_add (h : j ≤ k) (f g : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    fullFormOf h (f + g) = fullFormOf h f + fullFormOf h g :=
  oddFormOfCoeffs_add (fun p => f ((fullPairsEquiv L k j h).symm p))
    (fun p => g ((fullPairsEquiv L k j h).symm p))
theorem fullFormOf_smul (h : j ≤ k) (z : ℂ) (f : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    fullFormOf h (z • f) = z • fullFormOf h f :=
  oddFormOfCoeffs_smul z fun p => f ((fullPairsEquiv L k j h).symm p)
theorem quotFormOf_add (h : j ≤ k) (hs : ProjSurjective L m k j)
    (f g : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L m → ℂ) :
    quotFormOf h hs (f + g) = quotFormOf h hs f + quotFormOf h hs g :=
  oddFormOfCoeffs_add (fun p => f ((quotPairsEquiv h hs).symm p))
    (fun p => g ((quotPairsEquiv h hs).symm p))
theorem quotFormOf_smul (h : j ≤ k) (hs : ProjSurjective L m k j) (z : ℂ)
    (f : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L m → ℂ) :
    quotFormOf h hs (z • f) = z • quotFormOf h hs f :=
  oddFormOfCoeffs_smul z fun p => f ((quotPairsEquiv h hs).symm p)
theorem fullFormOf_bounded (ha : 0 < meshAt L k j) (h : j ≤ k)
    {f : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ} (hf : IsBoundedFn f) :
    fullFormOf h f ∈ boundedSubmodule (FullSpace.complexEdgeForms (meshAt L k j)) := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨fullFormOf_mem ha h f, oddFormOfCoeffs_bounded ⟨C, fun p => hC _⟩⟩
theorem quotFormOf_bounded
    (hx : ∀ b : Edge L m k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (h : j ≤ k) (hs : ProjSurjective L m k j)
    (hfin : Finite ((CellClass.edgeClass k j h).colourPairs.ImageCarrier L m))
    (f : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L m → ℂ) :
    quotFormOf h hs f ∈ boundedSubmodule (complexEdgeForms L m k j) := by
  obtain ⟨C, hC⟩ := (Set.finite_range fun i => ‖f i‖).bddAbove
  exact ⟨quotFormOf_mem hx h hs f, oddFormOfCoeffs_bounded ⟨C, fun p => hC (mem_range_self _)⟩⟩
private theorem isBoundedFn_of_hasFiniteSupport {J : Type} {f : J → ℂ}
    (hf : PeriodicOperators.HasFiniteSupport f) : IsBoundedFn f := by apply _root_.YangMills.Construction.LocalKernels.LocalBilinearKernels.isBoundedFn_of_hasFiniteSupport <;> assumption
theorem coeffsOn_hasFiniteSupport (h : j ≤ k) {B : FullSpace.Edge L k j → ComplexMatrix2}
    (hB : HasFiniteSupp (FullSpace.restrictToPositiveEdges B)) :
    PeriodicOperators.HasFiniteSupport (CellClass.coeffsOn L (CellClass.edgeClass k j h) B) := by apply _root_.YangMills.Construction.LocalKernels.HessianAtLifts.coeffsOn_hasFiniteSupport <;> assumption
theorem fullFormOf_hasFiniteSupp (h : j ≤ k) {f : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ}
    (hf : PeriodicOperators.HasFiniteSupport f) :
    HasFiniteSupp (FullSpace.restrictToPositiveEdges (fullFormOf h f)) := by
  have hfin := hf.image fun ι => (fullPairsEquiv L k j h ι).2
  refine hfin.subset fun b hb => ?_
  by_contra hn
  refine hb ?_
  show oddFormOfCoeffs _ _ b.1 = 0
  rw [oddFormOfCoeffs_of_pos _ b.2]
  refine Finset.sum_eq_zero fun a _ => ?_
  have e : f ((fullPairsEquiv L k j h).symm (a, b)) = 0 := by
    by_contra h1
    exact hn ⟨_, h1, by simp⟩
  show f ((fullPairsEquiv L k j h).symm (a, b)) • ComplexMatrix2.pauliFamily a = 0
  rw [e, zero_smul]
private theorem toPauliCoeffs_ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
theorem toPauliCoeffs_ofCoeffs (h : j ≤ k) (g : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ)
    (ι : Idx L (CellClass.edgeClass k j h).colourPairs) :
    toPauliCoeffs (σ := PeriodicOperators.PosEdge L k j)
      (CellClass.ofCoeffs L (CellClass.edgeClass k j h) g) (fullPairsEquiv L k j h ι) = g ι := by
  rcases ι with ⟨⟨⟩, p⟩
  exact congrFun (toPauliCoeffs_ofPauliCoeffs (fun q => g ⟨(), q⟩)) p
theorem toPauliCoeffs_ofQuotCoeffs (h : j ≤ k) (hs : ProjSurjective L m k j)
    (g : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L m → ℂ)
    (κ : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L m) :
    toPauliCoeffs (σ := Tower.PositiveEdge L m k j)
      (CellClass.ofQuotCoeffs L m (CellClass.edgeClass k j h) g) (quotPairsEquiv h hs κ) = g κ := by
  rcases κ with ⟨⟨⟩, p, hp⟩
  refine (congrFun (toPauliCoeffs_ofPauliCoeffs _) p).trans ?_
  exact dif_pos hp
theorem traceFinsumPairing_ofCoeffs (hP : OneLoop.PauliMatrixRelations) (h : j ≤ k)
    {B : FullSpace.Edge L k j → ComplexMatrix2} (hB : B ∈ FullSpace.complexEdgeForms (meshAt L k j))
    (hf : HasFiniteSupp (FullSpace.restrictToPositiveEdges B))
    (g : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    traceFinsumPairing (FullSpace.restrictToPositiveEdges B)
        (CellClass.ofCoeffs L (CellClass.edgeClass k j h) g) =
      weightedBracket L (CellClass.edgeClass k j h).colourPairs
        (CellClass.coeffsOn L (CellClass.edgeClass k j h) B) g := by
  have e := wPairing_toPauliCoeffs hP (fullPairsEquiv L k j h)
    (((CellClass.edgeClass k j h).colourPairs.toPeriodicData L).weightOf) (fun _ => rfl)
    (FullSpace.restrictToPositiveEdges B) (CellClass.ofCoeffs L (CellClass.edgeClass k j h) g)
    (fun b => hB.1 _ b.2) (fun _ => pauliCombination_mem_traceless _) (Or.inl hf)
  have e₁ : (fun i => toPauliCoeffs (σ := PeriodicOperators.PosEdge L k j)
      (CellClass.ofCoeffs L (CellClass.edgeClass k j h) g) (fullPairsEquiv L k j h i)) = g :=
    funext (toPauliCoeffs_ofCoeffs h g)
  rw [e₁] at e
  exact e.symm
theorem traceFinsumPairing_ofQuotCoeffs (hP : OneLoop.PauliMatrixRelations) (h : j ≤ k)
    (hs : ProjSurjective L m k j) (hfin : Finite (Tower.PositiveEdge L m k j))
    {B : Edge L m k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L m k j)
    (g : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L m → ℂ) :
    traceFinsumPairing (restrictToPositiveEdges B)
        (CellClass.ofQuotCoeffs L m (CellClass.edgeClass k j h) g) =
      quotBracket L m (CellClass.edgeClass k j h).colourPairs
        (CellClass.quotCoeffsOn L m (CellClass.edgeClass k j h) B) g := by
  have e := wPairing_toPauliCoeffs hP (quotPairsEquiv h hs)
    ((CellClass.edgeClass k j h).colourPairs.imageWeight L m) (fun _ => rfl)
    (restrictToPositiveEdges B) (CellClass.ofQuotCoeffs L m (CellClass.edgeClass k j h) g)
    (fun b => hB.1 _ b.2) (fun _ => pauliCombination_mem_traceless _) (Or.inl (Set.toFinite _))
  have e₁ : (fun i => toPauliCoeffs (σ := Tower.PositiveEdge L m k j)
      (CellClass.ofQuotCoeffs L m (CellClass.edgeClass k j h) g) (quotPairsEquiv h hs i)) = g :=
    funext (toPauliCoeffs_ofQuotCoeffs h hs g)
  rw [e₁] at e
  exact e.symm
theorem traceFinsumPairing_eq_quotBracket (hP : OneLoop.PauliMatrixRelations) (h : j ≤ k)
    (hs : ProjSurjective L m k j) (hfin : Finite (Tower.PositiveEdge L m k j))
    {B : Edge L m k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L m k j)
    (X : Tower.PositiveEdge L m k j → ComplexMatrix2) (hX : ∀ c, X c ∈ ComplexMatrix2.traceless) :
    traceFinsumPairing (restrictToPositiveEdges B) X =
      quotBracket L m (CellClass.edgeClass k j h).colourPairs
        (CellClass.quotCoeffsOn L m (CellClass.edgeClass k j h) B)
        fun κ => toPauliCoeffs X (quotPairsEquiv h hs κ) :=
  (wPairing_toPauliCoeffs hP (quotPairsEquiv h hs)
    ((CellClass.edgeClass k j h).colourPairs.imageWeight L m) (fun _ => rfl)
    (restrictToPositiveEdges B) X (fun b => hB.1 _ b.2) hX (Or.inl (Set.toFinite _))).symm
theorem traceFinsumPairing_lift_eq_weightedBracket (hP : OneLoop.PauliMatrixRelations) (h : j ≤ k)
    (hq : ∀ b : PeriodicOperators.PosEdge L k j,
      (projPositiveEdge L m k j b).1 = FullSpace.projEdge L m k j b.1)
    {B : Edge L m k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L m k j)
    (X : PeriodicOperators.PosEdge L k j → ComplexMatrix2)
    (hX : ∀ c, X c ∈ ComplexMatrix2.traceless) (hfin : HasFiniteSupp X) :
    traceFinsumPairing (FullSpace.restrictToPositiveEdges (liftGaugeField L m k j B)) X =
      weightedBracket L (CellClass.edgeClass k j h).colourPairs
        ((CellClass.edgeClass k j h).colourPairs.lift L m
          (CellClass.quotCoeffsOn L m (CellClass.edgeClass k j h) B))
        fun ι => toPauliCoeffs X (fullPairsEquiv L k j h ι) := by
  have e := wPairing_toPauliCoeffs hP (fullPairsEquiv L k j h)
    (((CellClass.edgeClass k j h).colourPairs.toPeriodicData L).weightOf) (fun _ => rfl)
    (FullSpace.restrictToPositiveEdges (liftGaugeField L m k j B)) X
    (fun b => by
      show B (FullSpace.projEdge L m k j b.1) ∈ ComplexMatrix2.traceless
      rw [← hq b]
      exact hB.1 _ (projPositiveEdge L m k j b).2) hX (Or.inr hfin)
  have e₁ : (fun i => toPauliCoeffs (FullSpace.restrictToPositiveEdges
        (liftGaugeField L m k j B)) (fullPairsEquiv L k j h i)) =
      (CellClass.edgeClass k j h).colourPairs.lift L m
        (CellClass.quotCoeffsOn L m (CellClass.edgeClass k j h) B) := by
    funext ι
    rcases ι with ⟨⟨⟩, a, c⟩
    show pauliCoeff a (B (FullSpace.projEdge L m k j c.1)) =
      pauliCoeff a (B (projPositiveEdge L m k j c).1)
    rw [hq c]
  rw [e₁] at e
  exact e.symm
theorem fullFormOf_lift (ha : 0 < meshAt L k j)
    (hx : ∀ b : Edge L m k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (h : j ≤ k) (hs : ProjSurjective L m k j) (hB : ProjEdgesCompatible L m k j)
    (f : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L m → ℂ) :
    fullFormOf h ((CellClass.edgeClass k j h).colourPairs.lift L m f) =
      liftGaugeField L m k j (quotFormOf h hs f) := by
  have hrev : ∀ b : FullSpace.Edge L k j,
      FullSpace.projEdge L m k j b.opposite = (FullSpace.projEdge L m k j b).opposite := fun b =>
    PeriodicLattice.Bond.ext ((hB.1 b.opposite).1.trans (hB.1 b).2.symm)
      ((hB.1 b.opposite).2.trans (hB.1 b).1.symm)
  have hform : liftGaugeField L m k j (quotFormOf h hs f) ∈
      FullSpace.complexEdgeForms (meshAt L k j) := by
    refine ⟨fun b hb => ?_, fun b => ?_⟩
    · show quotFormOf h hs f (FullSpace.projEdge L m k j b) ∈ ComplexMatrix2.traceless
      rw [← hB.2.1 ⟨b, hb⟩]
      exact oddFormOfCoeffs_mem_traceless _ (projPositiveEdge L m k j ⟨b, hb⟩).2
    · show quotFormOf h hs f (FullSpace.projEdge L m k j b.opposite) =
        -quotFormOf h hs f (FullSpace.projEdge L m k j b)
      rw [hrev]
      exact oddFormOfCoeffs_opposite PeriodicLattice.Bond.opposite_opposite hx _ _
  have hread : CellClass.coeffsOn L (CellClass.edgeClass k j h)
      (liftGaugeField L m k j (quotFormOf h hs f)) =
      (CellClass.edgeClass k j h).colourPairs.lift L m f := by
    funext ι
    rcases ι with ⟨⟨⟩, a, c⟩
    show pauliCoeff a (quotFormOf h hs f (FullSpace.projEdge L m k j c.1)) =
      f ((CellClass.edgeClass k j h).colourPairs.proj L m ⟨(), (a, c)⟩)
    rw [← hB.2.1 c]
    exact congrFun (quotCoeffsOn_quotFormOf h hs f)
      ((CellClass.edgeClass k j h).colourPairs.proj L m ⟨(), (a, c)⟩)
  rw [← hread]
  exact fullFormOf_coeffsOn ha h hform
end TwoSides
section QuadraticOnPairs
variable {L m k : ℕ}
def fullQuadraticMap (L k : ℕ) (W : FullSpace.Edge L k 0 → ComplexMatrix2)
    (f f' : Idx L (edgesAtZero k).colourPairs → ℂ) :
    Idx L (CellClass.edgeClass k k le_rfl).colourPairs → ℂ := fun ι =>
  toPauliCoeffs (FullSpace.AsDifferentials.complexQuadraticTerm L k W
      (fullFormOf (Nat.zero_le k) f) (fullFormOf (Nat.zero_le k) f'))
    (fullPairsEquiv L k k le_rfl ι)
def quotQuadraticValue (U : Edge L m k 0 → ComplexMatrix2) (hs₀ : ProjSurjective L m k 0)
    (hsk : ProjSurjective L m k k) (f f' : (edgesAtZero k).colourPairs.ImageCarrier L m → ℂ) :
    (CellClass.edgeClass k k le_rfl).colourPairs.ImageCarrier L m → ℂ := fun κ =>
  toPauliCoeffs (complexQuadraticTerm L m k U
      (quotFormOf (Nat.zero_le k) hs₀ f) (quotFormOf (Nat.zero_le k) hs₀ f'))
    (quotPairsEquiv le_rfl hsk κ)
def quotQuadraticMap (U : Edge L m k 0 → ComplexMatrix2) (hs₀ : ProjSurjective L m k 0)
    (hsk : ProjSurjective L m k k)
    (hb : ∀ f, quotFormOf (Nat.zero_le k) hs₀ f ∈ boundedSubmodule (complexEdgeForms L m k 0))
    (hq : ∀ B ∈ boundedSubmodule (complexEdgeForms L m k 0),
      ∀ B' ∈ boundedSubmodule (complexEdgeForms L m k 0),
      ∀ c, complexQuadraticTerm L m k U B B' c ∈ ComplexMatrix2.traceless) :
    ((edgesAtZero k).colourPairs.ImageCarrier L m → ℂ) →ₗ[ℂ]
      ((edgesAtZero k).colourPairs.ImageCarrier L m → ℂ) →ₗ[ℂ]
        ((CellClass.edgeClass k k le_rfl).colourPairs.ImageCarrier L m → ℂ) :=
  LinearMap.mk₂ ℂ (quotQuadraticValue U hs₀ hsk)
    (fun f g f' => by
      funext κ
      show toPauliCoeffs (complexQuadraticTerm L m k U
        (quotFormOf (Nat.zero_le k) hs₀ (f + g)) (quotFormOf (Nat.zero_le k) hs₀ f')) _ = _
      rw [quotFormOf_add]
      have e : complexQuadraticTerm L m k U
          (quotFormOf (Nat.zero_le k) hs₀ f + quotFormOf (Nat.zero_le k) hs₀ g)
          (quotFormOf (Nat.zero_le k) hs₀ f') =
          complexQuadraticTerm L m k U (quotFormOf (Nat.zero_le k) hs₀ f)
            (quotFormOf (Nat.zero_le k) hs₀ f') +
          complexQuadraticTerm L m k U (quotFormOf (Nat.zero_le k) hs₀ g)
            (quotFormOf (Nat.zero_le k) hs₀ f') :=
        quadraticTermAt_add_left (hb f) (hb g) (hb f')
      rw [e]
      exact toPauliCoeffs_add (hq _ (hb f) _ (hb f')) (hq _ (hb g) _ (hb f')) _)
    (fun z f f' => by
      funext κ
      show toPauliCoeffs (complexQuadraticTerm L m k U
        (quotFormOf (Nat.zero_le k) hs₀ (z • f)) (quotFormOf (Nat.zero_le k) hs₀ f')) _ = _
      rw [quotFormOf_smul]
      have e : complexQuadraticTerm L m k U (z • quotFormOf (Nat.zero_le k) hs₀ f)
          (quotFormOf (Nat.zero_le k) hs₀ f') =
          z • complexQuadraticTerm L m k U (quotFormOf (Nat.zero_le k) hs₀ f)
            (quotFormOf (Nat.zero_le k) hs₀ f') :=
        quadraticTermAt_smul_left z (hb f) (hb f')
      rw [e]
      exact toPauliCoeffs_smul z (hq _ (hb f) _ (hb f')) _)
    (fun f f' g' => by
      funext κ
      show toPauliCoeffs (complexQuadraticTerm L m k U
        (quotFormOf (Nat.zero_le k) hs₀ f) (quotFormOf (Nat.zero_le k) hs₀ (f' + g'))) _ = _
      rw [quotFormOf_add]
      have e : complexQuadraticTerm L m k U (quotFormOf (Nat.zero_le k) hs₀ f)
          (quotFormOf (Nat.zero_le k) hs₀ f' + quotFormOf (Nat.zero_le k) hs₀ g') =
          complexQuadraticTerm L m k U (quotFormOf (Nat.zero_le k) hs₀ f)
            (quotFormOf (Nat.zero_le k) hs₀ f') +
          complexQuadraticTerm L m k U (quotFormOf (Nat.zero_le k) hs₀ f)
            (quotFormOf (Nat.zero_le k) hs₀ g') :=
        quadraticTermAt_add_right (hb f) (hb f') (hb g')
      rw [e]
      exact toPauliCoeffs_add (hq _ (hb f) _ (hb f')) (hq _ (hb f) _ (hb g')) _)
    (fun z f f' => by
      funext κ
      show toPauliCoeffs (complexQuadraticTerm L m k U
        (quotFormOf (Nat.zero_le k) hs₀ f) (quotFormOf (Nat.zero_le k) hs₀ (z • f'))) _ = _
      rw [quotFormOf_smul]
      have e : complexQuadraticTerm L m k U (quotFormOf (Nat.zero_le k) hs₀ f)
          (z • quotFormOf (Nat.zero_le k) hs₀ f') =
          z • complexQuadraticTerm L m k U (quotFormOf (Nat.zero_le k) hs₀ f)
            (quotFormOf (Nat.zero_le k) hs₀ f') :=
        quadraticTermAt_smul_right z (hb f) (hb f')
      rw [e]
      exact toPauliCoeffs_smul z (hq _ (hb f) _ (hb f')) _)
theorem fullFormOf_congr {j : ℕ} (h : j ≤ k)
    {f g : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ}
    (b : PeriodicOperators.PosEdge L k j)
    (e : ∀ a, f ((fullPairsEquiv L k j h).symm (a, b)) = g ((fullPairsEquiv L k j h).symm (a, b))) :
    fullFormOf h f b.1 = fullFormOf h g b.1 := by
  unfold fullFormOf
  rw [oddFormOfCoeffs_of_pos _ b.2, oddFormOfCoeffs_of_pos _ b.2]
  exact Finset.sum_congr rfl fun a _ => congrArg (· • ComplexMatrix2.pauliFamily a) (e a)
theorem fullQuadraticMap_isLocal (ha : 0 < meshAt L k 0) (W : FullSpace.Edge L k 0 → ComplexMatrix2)
    (hq : ∀ B ∈ boundedSubmodule (FullSpace.complexEdgeForms (meshAt L k 0)),
      ∀ B' ∈ boundedSubmodule (FullSpace.complexEdgeForms (meshAt L k 0)), ∀ c,
        FullSpace.AsDifferentials.complexQuadraticTerm L k W B B' c ∈ ComplexMatrix2.traceless)
    (hl : ∀ B ∈ boundedSubmodule (FullSpace.complexEdgeForms (meshAt L k 0)),
      ∀ B' ∈ boundedSubmodule (FullSpace.complexEdgeForms (meshAt L k 0)),
      ∀ C ∈ boundedSubmodule (FullSpace.complexEdgeForms (meshAt L k 0)),
      ∀ C' ∈ boundedSubmodule (FullSpace.complexEdgeForms (meshAt L k 0)),
      ∀ c : PeriodicOperators.PosEdge L k k,
        (∀ b : PeriodicOperators.PosEdge L k 0,
          TorusMetric.supNormVec (b.1.initial.1 - c.1.initial.1) ≤ 3 →
            B b.1 = C b.1 ∧ B' b.1 = C' b.1) →
        FullSpace.AsDifferentials.complexQuadraticTerm L k W B B' c =
          FullSpace.AsDifferentials.complexQuadraticTerm L k W C C' c) :
    IsLocalBilinear ((edgesAtZero k).colourPairs.toPeriodicData L)
      ((edgesAtZero k).colourPairs.toPeriodicData L)
      ((CellClass.edgeClass k k le_rfl).colourPairs.toPeriodicData L) 3 (fullQuadraticMap L k W) := by
  have hb : ∀ {f : Idx L (edgesAtZero k).colourPairs → ℂ}, IsBoundedFn f →
      fullFormOf (Nat.zero_le k) f ∈ boundedSubmodule (FullSpace.complexEdgeForms (meshAt L k 0)) :=
    fun hf => fullFormOf_bounded ha _ hf
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro f g f' hf hg hf'
    funext ι
    show toPauliCoeffs (FullSpace.AsDifferentials.complexQuadraticTerm L k W
      (fullFormOf (Nat.zero_le k) (f + g)) (fullFormOf (Nat.zero_le k) f')) _ = _
    rw [fullFormOf_add]
    have e : FullSpace.AsDifferentials.complexQuadraticTerm L k W
        (fullFormOf (Nat.zero_le k) f + fullFormOf (Nat.zero_le k) g)
        (fullFormOf (Nat.zero_le k) f') =
        FullSpace.AsDifferentials.complexQuadraticTerm L k W
          (fullFormOf (Nat.zero_le k) f) (fullFormOf (Nat.zero_le k) f') +
        FullSpace.AsDifferentials.complexQuadraticTerm L k W
          (fullFormOf (Nat.zero_le k) g) (fullFormOf (Nat.zero_le k) f') :=
      quadraticTermAt_add_left (hb hf) (hb hg) (hb hf')
    rw [e]
    exact toPauliCoeffs_add (hq _ (hb hf) _ (hb hf')) (hq _ (hb hg) _ (hb hf')) _
  · intro z f f' hf hf'
    funext ι
    show toPauliCoeffs (FullSpace.AsDifferentials.complexQuadraticTerm L k W
      (fullFormOf (Nat.zero_le k) (z • f)) (fullFormOf (Nat.zero_le k) f')) _ = _
    rw [fullFormOf_smul]
    have e : FullSpace.AsDifferentials.complexQuadraticTerm L k W
        (z • fullFormOf (Nat.zero_le k) f) (fullFormOf (Nat.zero_le k) f') =
        z • FullSpace.AsDifferentials.complexQuadraticTerm L k W
          (fullFormOf (Nat.zero_le k) f) (fullFormOf (Nat.zero_le k) f') :=
      quadraticTermAt_smul_left z (hb hf) (hb hf')
    rw [e]
    exact toPauliCoeffs_smul z (hq _ (hb hf) _ (hb hf')) _
  · intro f f' g' hf hf' hg'
    funext ι
    show toPauliCoeffs (FullSpace.AsDifferentials.complexQuadraticTerm L k W
      (fullFormOf (Nat.zero_le k) f) (fullFormOf (Nat.zero_le k) (f' + g'))) _ = _
    rw [fullFormOf_add]
    have e : FullSpace.AsDifferentials.complexQuadraticTerm L k W
        (fullFormOf (Nat.zero_le k) f)
        (fullFormOf (Nat.zero_le k) f' + fullFormOf (Nat.zero_le k) g') =
        FullSpace.AsDifferentials.complexQuadraticTerm L k W
          (fullFormOf (Nat.zero_le k) f) (fullFormOf (Nat.zero_le k) f') +
        FullSpace.AsDifferentials.complexQuadraticTerm L k W
          (fullFormOf (Nat.zero_le k) f) (fullFormOf (Nat.zero_le k) g') :=
      quadraticTermAt_add_right (hb hf) (hb hf') (hb hg')
    rw [e]
    exact toPauliCoeffs_add (hq _ (hb hf) _ (hb hf')) (hq _ (hb hf) _ (hb hg')) _
  · intro z f f' hf hf'
    funext ι
    show toPauliCoeffs (FullSpace.AsDifferentials.complexQuadraticTerm L k W
      (fullFormOf (Nat.zero_le k) f) (fullFormOf (Nat.zero_le k) (z • f'))) _ = _
    rw [fullFormOf_smul]
    have e : FullSpace.AsDifferentials.complexQuadraticTerm L k W
        (fullFormOf (Nat.zero_le k) f) (z • fullFormOf (Nat.zero_le k) f') =
        z • FullSpace.AsDifferentials.complexQuadraticTerm L k W
          (fullFormOf (Nat.zero_le k) f) (fullFormOf (Nat.zero_le k) f') :=
      quadraticTermAt_smul_right z (hb hf) (hb hf')
    rw [e]
    exact toPauliCoeffs_smul z (hq _ (hb hf) _ (hb hf')) _
  · intro f g f' g' hf hg hf' hg' ι h₁ h₂
    have e := hl _ (hb hf) _ (hb hf') _ (hb hg) _ (hb hg') (fullPairsEquiv L k k le_rfl ι).2
      fun b hbd => ⟨fullFormOf_congr _ b fun a => h₁ ⟨(), (a, b)⟩ hbd,
        fullFormOf_congr _ b fun a => h₂ ⟨(), (a, b)⟩ hbd⟩
    show pauliCoeff _ _ = pauliCoeff _ _
    exact congrArg _ e
theorem isQuadraticKernel_iff (hP : OneLoop.PauliMatrixRelations) (ha : 0 < meshAt L k 0)
    (hqb : ∀ b : PeriodicOperators.PosEdge L k k,
      (projPositiveEdge L m k k b).1 = FullSpace.projEdge L m k k b.1)
    {U : Edge L m k 0 → ComplexMatrix2} {μ : Edge L m k k → ComplexMatrix2}
    (hμ : μ ∈ complexEdgeForms L m k k) (hform : QuadraticTermsFormed L m k U)
    (T : KernelMatrix (Idx L (edgesAtZero k).colourPairs) (Idx L (edgesAtZero k).colourPairs)) :
    IsQuadraticKernel L m k U μ T ↔
      IsBilinearKernel L m (edgesAtZero k).colourPairs (edgesAtZero k).colourPairs
        (CellClass.edgeClass k k le_rfl).colourPairs
        (fullQuadraticMap L k (liftGaugeField L m k 0 U))
        (CellClass.quotCoeffsOn L m (CellClass.edgeClass k k le_rfl) μ) T := by
  have key : ∀ f f' : Idx L (edgesAtZero k).colourPairs → ℂ,
      PeriodicOperators.HasFiniteSupport f → PeriodicOperators.HasFiniteSupport f' →
      traceFinsumPairing (FullSpace.restrictToPositiveEdges (liftGaugeField L m k k μ))
        (FullSpace.AsDifferentials.complexQuadraticTerm L k (liftGaugeField L m k 0 U)
          (fullFormOf (Nat.zero_le k) f) (fullFormOf (Nat.zero_le k) f')) =
      weightedBracket L (CellClass.edgeClass k k le_rfl).colourPairs
        ((CellClass.edgeClass k k le_rfl).colourPairs.lift L m
          (CellClass.quotCoeffsOn L m (CellClass.edgeClass k k le_rfl) μ))
        (fullQuadraticMap L k (liftGaugeField L m k 0 U) f f') := fun f f' hf hf' =>
    traceFinsumPairing_lift_eq_weightedBracket hP le_rfl hqb hμ _
      (hform.2.1 _ (fullFormOf_bounded ha _ (isBoundedFn_of_hasFiniteSupport hf)) _
        (fullFormOf_bounded ha _ (isBoundedFn_of_hasFiniteSupport hf')))
      (hform.2.2 _ (fullFormOf_mem ha _ f) (fullFormOf_hasFiniteSupp _ hf) _
        (fullFormOf_mem ha _ f') (fullFormOf_hasFiniteSupp _ hf'))
  constructor
  · intro hT f f' hf hf'
    have h₁ := hT _ (fullFormOf_mem ha (Nat.zero_le k) f) (fullFormOf_hasFiniteSupp _ hf) _
      (fullFormOf_mem ha (Nat.zero_le k) f') (fullFormOf_hasFiniteSupp _ hf')
    rw [traceFinsumPairing_ofCoeffs hP (Nat.zero_le k) (fullFormOf_mem ha _ f)
        (fullFormOf_hasFiniteSupp _ hf),
      coeffsOn_fullFormOf (h := Nat.zero_le k), coeffsOn_fullFormOf (h := Nat.zero_le k)] at h₁
    exact h₁.trans (key f f' hf hf')
  · intro hT B hB hf B' hB' hf'
    have h₁ := hT _ _ (coeffsOn_hasFiniteSupport (Nat.zero_le k) hf)
      (coeffsOn_hasFiniteSupport (Nat.zero_le k) hf')
    have h₂ := key _ _ (coeffsOn_hasFiniteSupport (Nat.zero_le k) hf)
      (coeffsOn_hasFiniteSupport (Nat.zero_le k) hf')
    rw [fullFormOf_coeffsOn ha (Nat.zero_le k) hB, fullFormOf_coeffsOn ha (Nat.zero_le k) hB'] at h₂
    rw [traceFinsumPairing_ofCoeffs hP (Nat.zero_le k) hB hf]
    exact h₁.trans h₂.symm
theorem isQuadraticMatrix_iff (hP : OneLoop.PauliMatrixRelations)
    (hx : ∀ b : Edge L m k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hs₀ : ProjSurjective L m k 0) (hsk : ProjSurjective L m k k)
    (hf₀ : Finite (Tower.PositiveEdge L m k 0))
    (hfk : Finite (Tower.PositiveEdge L m k k))
    {U : Edge L m k 0 → ComplexMatrix2} {μ : Edge L m k k → ComplexMatrix2}
    (hμ : μ ∈ complexEdgeForms L m k k)
    (hb : ∀ f, quotFormOf (Nat.zero_le k) hs₀ f ∈ boundedSubmodule (complexEdgeForms L m k 0))
    (hq : ∀ B ∈ boundedSubmodule (complexEdgeForms L m k 0),
      ∀ B' ∈ boundedSubmodule (complexEdgeForms L m k 0),
      ∀ c, complexQuadraticTerm L m k U B B' c ∈ ComplexMatrix2.traceless)
    (M : KernelMatrix ((edgesAtZero k).colourPairs.ImageCarrier L m)
      ((edgesAtZero k).colourPairs.ImageCarrier L m)) :
    IsQuadraticMatrix L m k U μ M ↔
      IsBilinearMatrix L m (edgesAtZero k).colourPairs (edgesAtZero k).colourPairs
        (CellClass.edgeClass k k le_rfl).colourPairs (quotQuadraticMap U hs₀ hsk hb hq)
        (CellClass.quotCoeffsOn L m (CellClass.edgeClass k k le_rfl) μ) M := by
  have key : ∀ f f' : (edgesAtZero k).colourPairs.ImageCarrier L m → ℂ,
      traceFinsumPairing (restrictToPositiveEdges μ) (complexQuadraticTerm L m k U
        (quotFormOf (Nat.zero_le k) hs₀ f) (quotFormOf (Nat.zero_le k) hs₀ f')) =
      quotBracket L m (CellClass.edgeClass k k le_rfl).colourPairs
        (CellClass.quotCoeffsOn L m (CellClass.edgeClass k k le_rfl) μ)
        (quotQuadraticMap U hs₀ hsk hb hq f f') := fun f f' =>
    traceFinsumPairing_eq_quotBracket hP le_rfl hsk hfk hμ _ (hq _ (hb f) _ (hb f'))
  constructor
  · intro hM f f'
    have h₁ := hM _ (quotFormOf_mem hx (Nat.zero_le k) hs₀ f) _
      (quotFormOf_mem hx (Nat.zero_le k) hs₀ f')
    rw [traceFinsumPairing_ofQuotCoeffs hP (Nat.zero_le k) hs₀ hf₀ (quotFormOf_mem hx _ hs₀ f),
      quotCoeffsOn_quotFormOf (h := Nat.zero_le k),
      quotCoeffsOn_quotFormOf (h := Nat.zero_le k)] at h₁
    exact h₁.trans (key f f')
  · intro hM B hB B' hB'
    have h₁ := hM (CellClass.quotCoeffsOn L m (edgesAtZero k) B)
      (CellClass.quotCoeffsOn L m (edgesAtZero k) B')
    have h₂ := key (CellClass.quotCoeffsOn L m (edgesAtZero k) B)
      (CellClass.quotCoeffsOn L m (edgesAtZero k) B')
    rw [quotFormOf_quotCoeffsOn hx (Nat.zero_le k) hs₀ hB,
      quotFormOf_quotCoeffsOn hx (Nat.zero_le k) hs₀ hB'] at h₂
    rw [traceFinsumPairing_ofQuotCoeffs hP (Nat.zero_le k) hs₀ hf₀ hB]
    exact h₁.trans h₂.symm
end QuadraticOnPairs
theorem quadraticKernelAtExtensionDescends_holds (hBil : LocalBilinearKernels.Claim)
    (hCells : PeriodicLiftCells.CellsAndClassesHold)
    (hIter : IterMeansOfLift.Claim)
    (hTerms : QuadraticTermsFormedAtLift)
    (hLocal : QuadraticTermIsLocal)
    (hPer : QuadraticTermOfLift)
    (hP : OneLoop.PauliMatrixRelations)
    (hXor : PeriodicLattice.LevelBondOrientationDichotomy) :
    QuadraticKernelAtExtensionDescends := by
  intro L hL k m hm hk U hU hsm μ hμ
  have hCl := hCells L hL k m hm
  have hc₀ := hCl.1 0 (Nat.zero_le k)
  have hck := hCl.1 k le_rfl
  have hs₀ : ProjSurjective L m k 0 := (hc₀.1 .edge).1
  have hsk : ProjSurjective L m k k := (hck.1 .edge).1
  have hF₀ : Finite ((edgesAtZero k).colourPairs.ImageCarrier L m) := (hCl.2 _).1
  have hFk : Finite ((CellClass.edgeClass k k le_rfl).colourPairs.ImageCarrier L m) := (hCl.2 _).1
  have hf₀ : Finite (Tower.PositiveEdge L m k 0) := by
    have := Finite.of_equiv _ (quotPairsEquiv (Nat.zero_le k) hs₀)
    exact Finite.of_injective (fun b => ((0 : Fin 3), b)) fun _ _ e => (Prod.ext_iff.1 e).2
  have hfk : Finite (Tower.PositiveEdge L m k k) := by
    have := Finite.of_equiv _ (quotPairsEquiv le_rfl hsk)
    exact Finite.of_injective (fun b => ((0 : Fin 3), b)) fun _ _ e => (Prod.ext_iff.1 e).2
  have hx : ∀ b : Edge L m k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    hXor L m k hL hm hk 0 (Nat.zero_le k)
  have hL0 : (0 : ℝ) < (L : ℝ) := by
    have : 0 < L := by
      have := hL.2
      omega
    exact_mod_cast this
  have ha : 0 < meshAt L k 0 := zpow_pos hL0 _
  have hform := hTerms L hL k m hm hk U hU hsm
  have hW := (hIter L hL k m hm hk U hU).1.1 hsm
  have hb := quotFormOf_bounded hx (Nat.zero_le k) hs₀ hF₀
  have hloc := fullQuadraticMap_isLocal ha (liftGaugeField L m k 0 U) hform.2.1
    (hLocal L hL k hk _ hW)
  have h12 : 4 * (3 : ℝ) < (periodSide L m : ℝ) := by
    have h₁ : L ≤ L ^ m := Nat.le_self_pow (Nat.pos_iff_ne_zero.1 hm) L
    have h₂ : 12 < periodSide L m := by
      have := hL.2
      unfold periodSide
      omega
    calc (4 : ℝ) * 3 = ((12 : ℕ) : ℝ) := by norm_num
      _ < _ := by exact_mod_cast h₂
  have hper : ∀ (f : (edgesAtZero k).colourPairs.ImageCarrier L m → ℂ)
      (f' : (edgesAtZero k).colourPairs.ImageCarrier L m → ℂ),
      fullQuadraticMap L k (liftGaugeField L m k 0 U)
          ((edgesAtZero k).colourPairs.lift L m f)
          ((edgesAtZero k).colourPairs.lift L m f') =
        (CellClass.edgeClass k k le_rfl).colourPairs.lift L m
          (quotQuadraticMap U hs₀ hsk hb hform.1 f f') := by
    intro f f'
    funext ι
    rcases ι with ⟨⟨⟩, a, c⟩
    show pauliCoeff a (FullSpace.AsDifferentials.complexQuadraticTerm L k
        (liftGaugeField L m k 0 U)
        (fullFormOf (Nat.zero_le k) ((edgesAtZero k).colourPairs.lift L m f))
        (fullFormOf (Nat.zero_le k) ((edgesAtZero k).colourPairs.lift L m f')) c) =
      pauliCoeff a (complexQuadraticTerm L m k U (quotFormOf (Nat.zero_le k) hs₀ f)
        (quotFormOf (Nat.zero_le k) hs₀ f') (projPositiveEdge L m k k c))
    rw [fullFormOf_lift ha hx (Nat.zero_le k) hs₀ hc₀.2 f,
      fullFormOf_lift ha hx (Nat.zero_le k) hs₀ hc₀.2 f',
      hPer L hL k m hm hk U hU hsm _ (quotFormOf_mem hx _ hs₀ f) _ (quotFormOf_mem hx _ hs₀ f') c]
  obtain ⟨-, hTu, hMu, hall⟩ := hBil L hL k m hm (edgesAtZero k).colourPairs
    (edgesAtZero k).colourPairs (CellClass.edgeClass k k le_rfl).colourPairs 3 (by norm_num) h12 _
    (quotQuadraticMap U hs₀ hsk hb hform.1)
    (CellClass.quotCoeffsOn L m (CellClass.edgeClass k k le_rfl) μ) hloc hper
  refine ⟨?_, ?_, fun T M hT hM => ?_⟩
  · exact (existsUnique_congr fun T => isQuadraticKernel_iff hP ha hck.2.2.1 hμ hform T).2 hTu
  · exact (existsUnique_congr fun M =>
      isQuadraticMatrix_iff hP hx hs₀ hsk hf₀ hfk hμ hb hform.1 M).2 hMu
  · obtain ⟨h₁, h₂, h₃⟩ := hall T M ((isQuadraticKernel_iff hP ha hck.2.2.1 hμ hform T).1 hT)
      ((isQuadraticMatrix_iff hP hx hs₀ hsk hf₀ hfk hμ hb hform.1 M).1 hM)
    refine ⟨?_, h₂, h₃⟩
    have e : (2 : ℝ) * 3 = 6 := by norm_num
    rwa [e] at h₁
end YangMills.Construction.LocalKernels.KernelDescent
end
