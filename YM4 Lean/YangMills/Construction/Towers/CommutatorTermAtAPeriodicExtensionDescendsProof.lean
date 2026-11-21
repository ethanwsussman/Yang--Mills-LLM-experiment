import YangMills.Construction.Lattice.LatticesOfATorusAndTheProductTopologyOfConfigurations
import YangMills.Construction.PeriodicOperators.SymmetricKernelOfAQuadraticFormProof
import YangMills.Construction.Towers.CellsAndClassesOfThePeriodicExtension
import YangMills.Construction.Towers.CommutatorTermAtAPeriodicExtensionDescends
import YangMills.Construction.Towers.KernelsOfPeriodicLocalBilinearMaps
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.Towers.SaddleOperatorsOfTheScaledPictureOnTheWholeProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels.BracketAtPeriodicLift
open YangMills.Construction.LocalKernels.Periodisation YangMills.Construction.Tower
open YangMills.Construction.Matrices (ComplexMatrix2)
open YangMills.Construction.PeriodicOperators (KernelMatrix applyKernel)
private theorem sum_smul_pauliFamily_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
private theorem pauliCoeff_sum_smul (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
private theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
private theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
private theorem pauliCoeff_add (a : Fin 3) {X Y : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p106 <;> assumption
private theorem pauliCoeff_smul (a : Fin 3) (z : ℂ) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) : pauliCoeff a (z • X) = z * pauliCoeff a X := by apply _root_.YangMills.SharedProofs.p5172 <;> assumption
private theorem halfTrace_mul_eq_sum (hP : OneLoop.PauliMatrixRelations) {X Y : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (hY : Y ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.halfTrace (X * Y) = ∑ a, pauliCoeff a X * pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p22145 <;> assumption
private theorem wPairing_toPauliCoeffs (hP : OneLoop.PauliMatrixRelations)
    {σ J : Type} (e : J ≃ Fin 3 × σ) (w : J → ℝ) (hw : ∀ i, w i = 1) (f g : σ → ComplexMatrix2)
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) (hg : ∀ x, g x ∈ ComplexMatrix2.traceless)
    (hfin : HasFiniteSupp f ∨ HasFiniteSupp g) :
    PeriodicOperators.wPairing w (fun i => toPauliCoeffs f (e i))
        (fun i => toPauliCoeffs g (e i)) = traceFinsumPairing f g := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : Finset σ, ∀ x ∉ F, f x = 0 ∨ g x = 0 := by
    rcases hfin with h | h
    · refine ⟨h.toFinset, fun x hx => Or.inl ?_⟩
      by_contra hne
      exact hx (h.mem_toFinset.2 hne)
    · refine ⟨h.toFinset, fun x hx => Or.inr ?_⟩
      by_contra hne
      exact hx (h.mem_toFinset.2 hne)
  set φ : Fin 3 × σ → ℂ := fun p => toPauliCoeffs f p * toPauliCoeffs g p with hφ
  have hz : ∀ p ∉ (Finset.univ : Finset (Fin 3)) ×ˢ F, φ p = 0 := by
    intro p hp
    have hx : p.2 ∉ F := fun h => hp (Finset.mem_product.2 ⟨Finset.mem_univ _, h⟩)
    rcases hF _ hx with h | h
    · simp [hφ, toPauliCoeffs, h, pauliCoeff_zero]
    · simp [hφ, toPauliCoeffs, h, pauliCoeff_zero]
  have h1 : traceFinsumPairing f g = ∑ x ∈ F, ComplexMatrix2.halfTrace (f x * g x) := by
    unfold traceFinsumPairing
    refine finsum_eq_sum_of_support_subset _ fun x hx => ?_
    by_contra hn
    have hx' : ComplexMatrix2.halfTrace (f x * g x) ≠ 0 := hx
    rcases hF x hn with h | h
    · exact hx' (by simp [h, ComplexMatrix2.halfTrace])
    · exact hx' (by simp [h, ComplexMatrix2.halfTrace])
  have h2 : PeriodicOperators.wPairing w (fun i => toPauliCoeffs f (e i))
      (fun i => toPauliCoeffs g (e i)) = ∑ p ∈ (Finset.univ : Finset (Fin 3)) ×ˢ F, φ p := by
    unfold PeriodicOperators.wPairing
    have e₁ : (fun i => (w i : ℂ) * (toPauliCoeffs f (e i) * toPauliCoeffs g (e i))) =
        fun i => φ (e i) := by
      funext i
      simp [hφ, hw]
    rw [e₁, e.tsum_eq φ]
    exact tsum_eq_sum hz
  rw [h1, h2, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [halfTrace_mul_eq_sum hP (hf x) (hg x)]
  rfl
abbrev _root_.YangMills.SharedProofs.p12066 := @wPairing_toPauliCoeffs
private theorem toPauliCoeffs_ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
private theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
private theorem ofPauliCoeffs_toPauliCoeffs {σ : Type} {f : σ → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) : ofPauliCoeffs (toPauliCoeffs f) = f := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldMeans.ofPauliCoeffs_toPauliCoeffs <;> assumption
private theorem ofPauliCoeffs_add {σ : Type} (c c' : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (c + c') = ofPauliCoeffs c + ofPauliCoeffs c' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_add <;> assumption
private theorem ofPauliCoeffs_smul {σ : Type} (z : ℂ) (c : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (z • c) = z • ofPauliCoeffs c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_smul <;> assumption
private theorem hasFiniteSupp_ofPauliCoeffs {σ : Type} {c : Fin 3 × σ → ℂ}
    (hc : (Function.support c).Finite) : HasFiniteSupp (ofPauliCoeffs c) := by
  refine (hc.image Prod.snd).subset fun x hx => ?_
  by_contra hn
  refine hx (Finset.sum_eq_zero fun a _ => ?_)
  have e : c (a, x) = 0 := by
    by_contra h1
    exact hn ⟨(a, x), h1, rfl⟩
  rw [e, zero_smul]
abbrev _root_.YangMills.DeltaSharedProofs.p502039 := @hasFiniteSupp_ofPauliCoeffs
private theorem toPauliCoeffs_support_finite {σ : Type} {f : σ → ComplexMatrix2}
    (hf : HasFiniteSupp f) : (Function.support (toPauliCoeffs f)).Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.SaddleScalingProof.toPauliCoeffs_support_finite <;> assumption
private theorem toPauliCoeffs_add {σ : Type} {X Y : σ → ComplexMatrix2}
    (hX : ∀ x, X x ∈ ComplexMatrix2.traceless) (hY : ∀ x, Y x ∈ ComplexMatrix2.traceless)
    (p : Fin 3 × σ) : toPauliCoeffs (X + Y) p = toPauliCoeffs X p + toPauliCoeffs Y p :=
  pauliCoeff_add p.1 (hX p.2) (hY p.2)
private theorem toPauliCoeffs_smul {σ : Type} (z : ℂ) {X : σ → ComplexMatrix2}
    (hX : ∀ x, X x ∈ ComplexMatrix2.traceless) (p : Fin 3 × σ) :
    toPauliCoeffs (z • X) p = z * toPauliCoeffs X p :=
  pauliCoeff_smul p.1 z (hX p.2)
section Generic
variable {β : Type} {pos : β → Prop} (rev : β → β)
def antisymmExtend (c : Fin 3 × {b // pos b} → ℂ) : β → ComplexMatrix2 :=
  open Classical in fun b =>
    if h : pos b then ofPauliCoeffs c ⟨b, h⟩
    else if h' : pos (rev b) then -ofPauliCoeffs c ⟨rev b, h'⟩ else 0
variable {rev}
theorem antisymmExtend_of_pos (c : Fin 3 × {b // pos b} → ℂ) {b : β} (h : pos b) :
    antisymmExtend rev c b = ofPauliCoeffs c ⟨b, h⟩ := dif_pos h
theorem antisymmExtend_mem (c : Fin 3 × {b // pos b} → ℂ) {b : β} (h : pos b) :
    antisymmExtend rev c b ∈ ComplexMatrix2.traceless := by
  rw [antisymmExtend_of_pos c h]
  exact sum_smul_pauliFamily_mem_traceless _
theorem toPauliCoeffs_antisymmExtend (c : Fin 3 × {b // pos b} → ℂ) :
    toPauliCoeffs (fun b : {b // pos b} => antisymmExtend rev c b.1) = c := by
  funext p
  show pauliCoeff p.1 (antisymmExtend rev c p.2.1) = c p
  rw [antisymmExtend_of_pos c p.2.2]
  exact pauliCoeff_sum_smul (fun a => c (a, p.2)) p.1
theorem antisymmExtend_rev (hrr : ∀ b, rev (rev b) = b) (hx : ∀ b, Xor (pos b) (pos (rev b)))
    (c : Fin 3 × {b // pos b} → ℂ) (b : β) :
    antisymmExtend rev c (rev b) = -antisymmExtend rev c b := by
  rcases hx b with ⟨h, h'⟩ | ⟨h, h'⟩
  · have e : antisymmExtend rev c (rev b) = -ofPauliCoeffs c ⟨rev (rev b), by rwa [hrr]⟩ := by
      unfold antisymmExtend
      rw [dif_neg h', dif_pos (by rwa [hrr])]
    rw [e, antisymmExtend_of_pos c h]
    congr 2
    exact Subtype.ext (hrr b)
  · have e : antisymmExtend rev c b = -ofPauliCoeffs c ⟨rev b, h⟩ := by
      unfold antisymmExtend
      rw [dif_neg h', dif_pos h]
    rw [e, antisymmExtend_of_pos c h, neg_neg]
theorem antisymmExtend_toPauliCoeffs (hrr : ∀ b, rev (rev b) = b)
    (hx : ∀ b, Xor (pos b) (pos (rev b))) {B : β → ComplexMatrix2}
    (hm : ∀ b, pos b → B b ∈ ComplexMatrix2.traceless) (hr : ∀ b, B (rev b) = -B b) :
    antisymmExtend rev (toPauliCoeffs fun b : {b // pos b} => B b.1) = B := by
  have hp : ∀ b, pos b →
      antisymmExtend rev (toPauliCoeffs fun b : {b // pos b} => B b.1) b = B b := by
    intro b h
    rw [antisymmExtend_of_pos _ h]
    exact sum_pauliCoeff_smul (hm b h)
  funext b
  rcases hx b with ⟨h, -⟩ | ⟨h, h'⟩
  · exact hp b h
  · have e := antisymmExtend_rev hrr hx (toPauliCoeffs fun b : {b // pos b} => B b.1) b
    rw [hp _ h, hr b] at e
    exact (neg_injective e).symm
theorem antisymmExtend_add (c c' : Fin 3 × {b // pos b} → ℂ) :
    antisymmExtend rev (c + c') = antisymmExtend rev c + antisymmExtend rev c' := by
  have e : ∀ b, ofPauliCoeffs (c + c') b = ofPauliCoeffs c b + ofPauliCoeffs c' b := by
    intro b
    simp only [ofPauliCoeffs, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  funext b
  simp only [antisymmExtend, Pi.add_apply]
  split_ifs
  · exact e _
  · rw [e]
    abel
  · simp
theorem antisymmExtend_smul (z : ℂ) (c : Fin 3 × {b // pos b} → ℂ) :
    antisymmExtend rev (z • c) = z • antisymmExtend rev c := by
  have e : ∀ b, ofPauliCoeffs (z • c) b = z • ofPauliCoeffs c b := by
    intro b
    simp only [ofPauliCoeffs, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  funext b
  simp only [antisymmExtend, Pi.smul_apply]
  split_ifs
  · exact e _
  · rw [e, smul_neg]
  · simp
end Generic
def bracketValue (g X Y Z : ComplexMatrix2) : ComplexMatrix2 :=
  (Complex.I / 2) • ⁅X + ComplexMatrix2.conjugateBy g Y, Z⁆
theorem bracketValue_mem (g X Y Z : ComplexMatrix2) :
    bracketValue g X Y Z ∈ ComplexMatrix2.traceless := by
  refine Submodule.smul_mem _ _ ?_
  show ComplexMatrix2.fullTrace _ = 0
  rw [Ring.lie_def, ComplexMatrix2.fullTrace, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
theorem bracketValue_zero (g X Y : ComplexMatrix2) : bracketValue g X Y 0 = 0 := by
  simp [bracketValue, Ring.lie_def]
theorem bracketValue_add_left (g X X' Y Y' Z : ComplexMatrix2) :
    bracketValue g (X + X') (Y + Y') Z = bracketValue g X Y Z + bracketValue g X' Y' Z := by
  unfold bracketValue ComplexMatrix2.conjugateBy
  rw [← smul_add]
  congr 1
  simp only [Ring.lie_def, mul_add, add_mul]
  abel
theorem bracketValue_smul_left (z : ℂ) (g X Y Z : ComplexMatrix2) :
    bracketValue g (z • X) (z • Y) Z = z • bracketValue g X Y Z := by
  unfold bracketValue ComplexMatrix2.conjugateBy
  rw [smul_comm]
  congr 1
  simp only [Ring.lie_def, mul_add, add_mul, smul_add, smul_sub, mul_smul_comm, smul_mul_assoc]
theorem bracketValue_add_right (g X Y Z Z' : ComplexMatrix2) :
    bracketValue g X Y (Z + Z') = bracketValue g X Y Z + bracketValue g X Y Z' := by
  unfold bracketValue
  rw [← smul_add]
  congr 1
  simp only [Ring.lie_def, mul_add, add_mul]
  abel
theorem bracketValue_smul_right (z : ℂ) (g X Y Z : ComplexMatrix2) :
    bracketValue g X Y (z • Z) = z • bracketValue g X Y Z := by
  unfold bracketValue
  rw [smul_comm]
  congr 1
  simp only [Ring.lie_def, smul_sub, mul_smul_comm, smul_mul_assoc]
section Cells
variable {L n k : ℕ}
def idxEquiv (L : ℕ) (A : CellClass k) :
    Idx L A.colourPairs ≃ Fin 3 × Cell L k A.level A.cellType where
  toFun ι := ι.2
  invFun p := ⟨(), p⟩
  left_inv ι := by rcases ι with ⟨⟨⟩, p⟩; rfl
  right_inv _ := rfl
abbrev ProjSurjective (L n : ℕ) (A : CellClass k) : Prop :=
  Function.Surjective
    (Cell.proj n : Cell L k A.level A.cellType → QuotientCell L n k A.level A.cellType)
theorem mem_pairPart_image {A : CellClass k} (hs : ProjSurjective L n A)
    (p : Fin 3 × QuotientCell L n k A.level A.cellType) : p ∈ A.colourComponent.image L n := by
  obtain ⟨b, hb⟩ := hs p.2
  exact ⟨(p.1, b), Prod.ext rfl hb⟩
def quotIdxEquiv {A : CellClass k} (hs : ProjSurjective L n A) :
    A.colourPairs.ImageCarrier L n ≃ Fin 3 × QuotientCell L n k A.level A.cellType where
  toFun κ := κ.2.1
  invFun p := ⟨(), ⟨p, mem_pairPart_image hs p⟩⟩
  left_inv κ := by rcases κ with ⟨⟨⟩, p, hp⟩; rfl
  right_inv _ := rfl
theorem toPauliCoeffs_ofCoeffs (A : CellClass k) (g : Idx L A.colourPairs → ℂ)
    (ι : Idx L A.colourPairs) :
    toPauliCoeffs (CellClass.ofCoeffs L A g) (idxEquiv L A ι) = g ι := by
  rcases ι with ⟨⟨⟩, p⟩
  exact congrFun (toPauliCoeffs_ofPauliCoeffs (fun q => g ⟨(), q⟩)) p
theorem toPauliCoeffs_ofQuotCoeffs {A : CellClass k} (hs : ProjSurjective L n A)
    (g : A.colourPairs.ImageCarrier L n → ℂ) (κ : A.colourPairs.ImageCarrier L n) :
    toPauliCoeffs (CellClass.ofQuotCoeffs L n A g) (quotIdxEquiv hs κ) = g κ := by
  rcases κ with ⟨⟨⟩, p, hp⟩
  refine (congrFun (toPauliCoeffs_ofPauliCoeffs _) p).trans ?_
  exact dif_pos hp
theorem traceFinsumPairing_ofCoeffs (hP : OneLoop.PauliMatrixRelations) (A : CellClass k)
    {f : Cell L k A.level A.cellType → ComplexMatrix2} (hf : ∀ x, f x ∈ ComplexMatrix2.traceless)
    (hfin : HasFiniteSupp f) (g : Idx L A.colourPairs → ℂ) :
    traceFinsumPairing f (CellClass.ofCoeffs L A g) =
      weightedBracket L A.colourPairs (fun ι => toPauliCoeffs f (idxEquiv L A ι)) g := by
  have e := wPairing_toPauliCoeffs hP (idxEquiv L A) ((A.colourPairs.toPeriodicData L).weightOf)
    (fun _ => rfl) f (CellClass.ofCoeffs L A g) hf (fun _ => sum_smul_pauliFamily_mem_traceless _)
    (Or.inl hfin)
  have e₁ : (fun i => toPauliCoeffs (CellClass.ofCoeffs L A g) (idxEquiv L A i)) = g :=
    funext (toPauliCoeffs_ofCoeffs A g)
  rw [e₁] at e
  exact e.symm
theorem traceFinsumPairing_ofQuotCoeffs (hP : OneLoop.PauliMatrixRelations)
    {A : CellClass k} (hs : ProjSurjective L n A)
    {f : QuotientCell L n k A.level A.cellType → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) (hfin : HasFiniteSupp f)
    (g : A.colourPairs.ImageCarrier L n → ℂ) :
    traceFinsumPairing f (CellClass.ofQuotCoeffs L n A g) =
      quotBracket L n A.colourPairs (fun κ => toPauliCoeffs f (quotIdxEquiv hs κ)) g := by
  have e := wPairing_toPauliCoeffs hP (quotIdxEquiv hs) (A.colourPairs.imageWeight L n)
    (fun _ => rfl) f (CellClass.ofQuotCoeffs L n A g) hf
    (fun _ => sum_smul_pauliFamily_mem_traceless _) (Or.inl hfin)
  have e₁ : (fun i => toPauliCoeffs (CellClass.ofQuotCoeffs L n A g) (quotIdxEquiv hs i)) = g :=
    funext (toPauliCoeffs_ofQuotCoeffs hs g)
  rw [e₁] at e
  exact e.symm
theorem hasFiniteSupp_ofCoeffs (A : CellClass k) {g : Idx L A.colourPairs → ℂ}
    (hg : PeriodicOperators.HasFiniteSupport g) : HasFiniteSupp (CellClass.ofCoeffs L A g) :=
  hasFiniteSupp_ofPauliCoeffs ((hg.image (idxEquiv L A)).subset fun p hp => ⟨⟨(), p⟩, hp, rfl⟩)
theorem hasFiniteSupport_coeffs (A : CellClass k) {f : Cell L k A.level A.cellType → ComplexMatrix2}
    (hf : HasFiniteSupp f) :
    PeriodicOperators.HasFiniteSupport (fun ι => toPauliCoeffs f (idxEquiv L A ι)) :=
  ((toPauliCoeffs_support_finite hf).image (idxEquiv L A).symm).subset fun ι hι =>
    ⟨idxEquiv L A ι, hι, (idxEquiv L A).symm_apply_apply ι⟩
end Cells
section Sides
variable {L n k j : ℕ}
abbrev fullVertexField (h : j ≤ k) (f : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ) :
    Tower.FullSpace.Vertex L k j → ComplexMatrix2 :=
  CellClass.ofCoeffs L (CellClass.vertexClass k j h) f
abbrev quotVertexField (h : j ≤ k)
    (f : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    Tower.Vertex L n k j → ComplexMatrix2 :=
  CellClass.ofQuotCoeffs L n (CellClass.vertexClass k j h) f
theorem quotVertexField_eq (h : j ≤ k) (hs : ProjSurjective L n (CellClass.vertexClass k j h))
    (f : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    quotVertexField h f = ofPauliCoeffs fun p => f ((quotIdxEquiv hs).symm p) := by
  unfold quotVertexField CellClass.ofQuotCoeffs
  congr 1
  funext ι
  exact dif_pos (mem_pairPart_image hs ι)
theorem fullVertexField_mem (h : j ≤ k) (f : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ) :
    fullVertexField h f ∈ Matrices.GroupLieProduct.tracelessFunctions (Tower.FullSpace.Vertex L k j) :=
  fun x _ => ofPauliCoeffs_mem _ x
theorem quotVertexField_mem (h : j ≤ k)
    (f : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    quotVertexField h f ∈ Matrices.GroupLieProduct.tracelessFunctions (Tower.Vertex L n k j) :=
  fun x _ => ofPauliCoeffs_mem _ x
theorem coeffsOn_fullVertexField (h : j ≤ k)
    (f : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ) :
    CellClass.coeffsOn L (CellClass.vertexClass k j h) (fullVertexField h f) = f :=
  funext (toPauliCoeffs_ofCoeffs _ f)
theorem quotCoeffsOn_quotVertexField (h : j ≤ k)
    (hs : ProjSurjective L n (CellClass.vertexClass k j h))
    (f : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    CellClass.quotCoeffsOn L n (CellClass.vertexClass k j h) (quotVertexField h f) = f :=
  funext (toPauliCoeffs_ofQuotCoeffs hs f)
theorem fullVertexField_coeffsOn (h : j ≤ k) {l : Tower.FullSpace.Vertex L k j → ComplexMatrix2}
    (hl : l ∈ Matrices.GroupLieProduct.tracelessFunctions (Tower.FullSpace.Vertex L k j)) :
    fullVertexField h (CellClass.coeffsOn L (CellClass.vertexClass k j h) l) = l :=
  ofPauliCoeffs_toPauliCoeffs fun x => hl x (mem_univ _)
theorem quotVertexField_quotCoeffsOn (h : j ≤ k)
    (hs : ProjSurjective L n (CellClass.vertexClass k j h)) {l : Tower.Vertex L n k j → ComplexMatrix2}
    (hl : l ∈ Matrices.GroupLieProduct.tracelessFunctions (Tower.Vertex L n k j)) :
    quotVertexField h (CellClass.quotCoeffsOn L n (CellClass.vertexClass k j h) l) = l := by
  rw [quotVertexField_eq h hs]
  exact ofPauliCoeffs_toPauliCoeffs fun x => hl x (mem_univ _)
theorem fullVertexField_add (h : j ≤ k)
    (f g : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ) :
    fullVertexField h (f + g) = fullVertexField h f + fullVertexField h g :=
  ofPauliCoeffs_add (fun ι => f ⟨(), ι⟩) (fun ι => g ⟨(), ι⟩)
theorem fullVertexField_smul (h : j ≤ k) (z : ℂ)
    (f : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ) :
    fullVertexField h (z • f) = z • fullVertexField h f :=
  ofPauliCoeffs_smul z fun ι => f ⟨(), ι⟩
theorem quotVertexField_add (h : j ≤ k) (hs : ProjSurjective L n (CellClass.vertexClass k j h))
    (f g : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    quotVertexField h (f + g) = quotVertexField h f + quotVertexField h g := by
  rw [quotVertexField_eq h hs, quotVertexField_eq h hs, quotVertexField_eq h hs]
  exact ofPauliCoeffs_add (fun p => f ((quotIdxEquiv hs).symm p))
    (fun p => g ((quotIdxEquiv hs).symm p))
theorem quotVertexField_smul (h : j ≤ k) (hs : ProjSurjective L n (CellClass.vertexClass k j h))
    (z : ℂ) (f : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    quotVertexField h (z • f) = z • quotVertexField h f := by
  rw [quotVertexField_eq h hs, quotVertexField_eq h hs]
  exact ofPauliCoeffs_smul z fun p => f ((quotIdxEquiv hs).symm p)
theorem fullVertexField_lift (h : j ≤ k) (hs : ProjSurjective L n (CellClass.vertexClass k j h))
    (f : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ)
    (x : Tower.FullSpace.Vertex L k j) :
    fullVertexField h ((CellClass.vertexClass k j h).colourPairs.lift L n f) x =
      quotVertexField h f (Tower.FullSpace.projVertex L n k j x) := by
  rw [quotVertexField_eq h hs]
  rfl
def fullEdgeForm (h : j ≤ k) (f : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    Tower.FullSpace.Edge L k j → ComplexMatrix2 :=
  antisymmExtend (pos := fun b => b.IsPositivelyOriented) InfiniteLattice.Link.opposite
    fun p => f ((idxEquiv L (CellClass.edgeClass k j h)).symm p)
def quotEdgeForm (h : j ≤ k) (hs : ProjSurjective L n (CellClass.edgeClass k j h))
    (f : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    Tower.Edge L n k j → ComplexMatrix2 :=
  antisymmExtend (pos := fun b => b.IsPositivelyOriented) PeriodicLattice.Bond.opposite
    fun p => f ((quotIdxEquiv hs).symm p)
theorem link_opposite_opposite {a : ℝ} (b : InfiniteLattice.Link a) :
    b.opposite.opposite = b := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_opposite <;> assumption
theorem link_xor_opposite {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.xor_isPositivelyOriented_opposite <;> assumption
theorem fullEdgeForm_mem (ha : 0 < meshAt L k j) (h : j ≤ k)
    (f : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    fullEdgeForm h f ∈ Tower.FullSpace.complexEdgeForms (meshAt L k j) :=
  ⟨fun _ hb => antisymmExtend_mem _ hb,
    antisymmExtend_rev link_opposite_opposite (link_xor_opposite ha) _⟩
theorem quotEdgeForm_mem
    (hx : ∀ b : Tower.Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (h : j ≤ k) (hs : ProjSurjective L n (CellClass.edgeClass k j h))
    (f : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    quotEdgeForm h hs f ∈ complexEdgeForms L n k j :=
  ⟨fun _ hb => antisymmExtend_mem _ hb,
    antisymmExtend_rev PeriodicLattice.Bond.opposite_opposite hx _⟩
theorem fullEdgeForm_coeffsOn (ha : 0 < meshAt L k j) (h : j ≤ k)
    {B : Tower.FullSpace.Edge L k j → ComplexMatrix2}
    (hB : B ∈ Tower.FullSpace.complexEdgeForms (meshAt L k j)) :
    fullEdgeForm h (CellClass.coeffsOn L (CellClass.edgeClass k j h) B) = B :=
  antisymmExtend_toPauliCoeffs link_opposite_opposite (link_xor_opposite ha) hB.1 hB.2
theorem quotEdgeForm_quotCoeffsOn
    (hx : ∀ b : Tower.Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (h : j ≤ k) (hs : ProjSurjective L n (CellClass.edgeClass k j h))
    {B : Tower.Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) :
    quotEdgeForm h hs (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) B) = B :=
  antisymmExtend_toPauliCoeffs PeriodicLattice.Bond.opposite_opposite hx hB.1 hB.2
theorem coeffsOn_fullEdgeForm (h : j ≤ k) (f : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    CellClass.coeffsOn L (CellClass.edgeClass k j h) (fullEdgeForm h f) = f := by
  funext ι
  have e := congrFun (toPauliCoeffs_antisymmExtend
    (pos := fun b : Tower.FullSpace.Edge L k j => b.IsPositivelyOriented)
    (rev := InfiniteLattice.Link.opposite)
    fun p => f ((idxEquiv L (CellClass.edgeClass k j h)).symm p))
    (idxEquiv L (CellClass.edgeClass k j h) ι)
  rw [Equiv.symm_apply_apply] at e
  exact e
theorem quotCoeffsOn_quotEdgeForm (h : j ≤ k) (hs : ProjSurjective L n (CellClass.edgeClass k j h))
    (f : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) (quotEdgeForm h hs f) = f := by
  funext κ
  have e := congrFun (toPauliCoeffs_antisymmExtend
    (pos := fun b : Tower.Edge L n k j => b.IsPositivelyOriented)
    (rev := PeriodicLattice.Bond.opposite) fun p => f ((quotIdxEquiv hs).symm p))
    (quotIdxEquiv hs κ)
  rw [Equiv.symm_apply_apply] at e
  exact e
theorem fullEdgeForm_add (h : j ≤ k) (f g : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    fullEdgeForm h (f + g) = fullEdgeForm h f + fullEdgeForm h g :=
  antisymmExtend_add (fun p => f ((idxEquiv L (CellClass.edgeClass k j h)).symm p))
    (fun p => g ((idxEquiv L (CellClass.edgeClass k j h)).symm p))
theorem fullEdgeForm_smul (h : j ≤ k) (z : ℂ)
    (f : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    fullEdgeForm h (z • f) = z • fullEdgeForm h f :=
  antisymmExtend_smul z fun p => f ((idxEquiv L (CellClass.edgeClass k j h)).symm p)
theorem quotEdgeForm_add (h : j ≤ k) (hs : ProjSurjective L n (CellClass.edgeClass k j h))
    (f g : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    quotEdgeForm h hs (f + g) = quotEdgeForm h hs f + quotEdgeForm h hs g :=
  antisymmExtend_add (fun p => f ((quotIdxEquiv hs).symm p)) (fun p => g ((quotIdxEquiv hs).symm p))
theorem quotEdgeForm_smul (h : j ≤ k) (hs : ProjSurjective L n (CellClass.edgeClass k j h)) (z : ℂ)
    (f : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    quotEdgeForm h hs (z • f) = z • quotEdgeForm h hs f :=
  antisymmExtend_smul z fun p => f ((quotIdxEquiv hs).symm p)
theorem hasFiniteSupp_fullEdgeForm (h : j ≤ k)
    {f : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ}
    (hf : PeriodicOperators.HasFiniteSupport f) :
    HasFiniteSupp (Tower.FullSpace.restrictToPositiveEdges (fullEdgeForm h f)) := by
  have e : Tower.FullSpace.restrictToPositiveEdges (fullEdgeForm h f) =
      CellClass.ofCoeffs L (CellClass.edgeClass k j h) f :=
    funext fun b => antisymmExtend_of_pos _ b.2
  rw [e]
  exact hasFiniteSupp_ofCoeffs _ hf
theorem traceFinsumPairing_quot_right (hP : OneLoop.PauliMatrixRelations) (h : j ≤ k)
    (hs : ProjSurjective L n (CellClass.edgeClass k j h))
    (hfin : Finite (Tower.PositiveEdge L n k j))
    {B : Tower.Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j)
    (X : Tower.PositiveEdge L n k j → ComplexMatrix2)
    (hX : ∀ c, X c ∈ ComplexMatrix2.traceless) :
    traceFinsumPairing (restrictToPositiveEdges B) X =
      quotBracket L n (CellClass.edgeClass k j h).colourPairs
        (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) B)
        fun κ => toPauliCoeffs X (quotIdxEquiv hs κ) := by
  have hB' : HasFiniteSupp (restrictToPositiveEdges B) := Set.toFinite _
  exact (wPairing_toPauliCoeffs hP (quotIdxEquiv hs)
    ((CellClass.edgeClass k j h).colourPairs.imageWeight L n) (fun _ => rfl)
    (restrictToPositiveEdges B) X (fun b => hB.1 _ b.2) hX (Or.inl hB')).symm
theorem traceFinsumPairing_lift_right (hP : OneLoop.PauliMatrixRelations) (h : j ≤ k)
    (hq : ∀ b : PeriodicOperators.PosEdge L k j,
      (projPositiveEdge L n k j b).1 = Tower.FullSpace.projEdge L n k j b.1)
    {B : Tower.Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j)
    (X : PeriodicOperators.PosEdge L k j → ComplexMatrix2)
    (hX : ∀ c, X c ∈ ComplexMatrix2.traceless) (hfin : HasFiniteSupp X) :
    traceFinsumPairing (Tower.FullSpace.restrictToPositiveEdges (liftGaugeField L n k j B)) X =
      weightedBracket L (CellClass.edgeClass k j h).colourPairs
        ((CellClass.edgeClass k j h).colourPairs.lift L n
          (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) B))
        fun ι => toPauliCoeffs X (idxEquiv L (CellClass.edgeClass k j h) ι) := by
  have e := wPairing_toPauliCoeffs hP (idxEquiv L (CellClass.edgeClass k j h))
    (((CellClass.edgeClass k j h).colourPairs.toPeriodicData L).weightOf) (fun _ => rfl)
    (Tower.FullSpace.restrictToPositiveEdges (liftGaugeField L n k j B)) X
    (fun b => by
      show B (Tower.FullSpace.projEdge L n k j b.1) ∈ ComplexMatrix2.traceless
      rw [← hq b]
      exact hB.1 _ (projPositiveEdge L n k j b).2) hX (Or.inr hfin)
  have e₁ : (fun i => toPauliCoeffs (Tower.FullSpace.restrictToPositiveEdges
        (liftGaugeField L n k j B))
        (idxEquiv L (CellClass.edgeClass k j h) i)) =
      (CellClass.edgeClass k j h).colourPairs.lift L n
        (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) B) := by
    funext ι
    rcases ι with ⟨⟨⟩, a, c⟩
    show pauliCoeff a (B (Tower.FullSpace.projEdge L n k j c.1)) =
      pauliCoeff a (B (projPositiveEdge L n k j c).1)
    rw [hq c]
  exact e.symm.trans
    (congrArg (fun g => weightedBracket L (CellClass.edgeClass k j h).colourPairs g _) e₁)
theorem fullEdgeForm_lift (ha : 0 < meshAt L k j)
    (hx : ∀ b : Tower.Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (h : j ≤ k) (hs : ProjSurjective L n (CellClass.edgeClass k j h))
    (hB : ProjEdgesCompatible L n k j)
    (f : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    fullEdgeForm h ((CellClass.edgeClass k j h).colourPairs.lift L n f) =
      liftGaugeField L n k j (quotEdgeForm h hs f) := by
  have hrev : ∀ b : Tower.FullSpace.Edge L k j,
      Tower.FullSpace.projEdge L n k j b.opposite =
        (Tower.FullSpace.projEdge L n k j b).opposite := fun b =>
    PeriodicLattice.Bond.ext ((hB.1 b.opposite).1.trans (hB.1 b).2.symm)
      ((hB.1 b.opposite).2.trans (hB.1 b).1.symm)
  have hform : liftGaugeField L n k j (quotEdgeForm h hs f) ∈
      Tower.FullSpace.complexEdgeForms (meshAt L k j) := by
    refine ⟨fun b hb => ?_, fun b => ?_⟩
    · show quotEdgeForm h hs f (Tower.FullSpace.projEdge L n k j b) ∈ ComplexMatrix2.traceless
      rw [← hB.2.1 ⟨b, hb⟩]
      exact antisymmExtend_mem _ (projPositiveEdge L n k j ⟨b, hb⟩).2
    · show quotEdgeForm h hs f (Tower.FullSpace.projEdge L n k j b.opposite) =
        -quotEdgeForm h hs f (Tower.FullSpace.projEdge L n k j b)
      rw [hrev]
      exact antisymmExtend_rev PeriodicLattice.Bond.opposite_opposite hx _ _
  have hread : CellClass.coeffsOn L (CellClass.edgeClass k j h)
      (liftGaugeField L n k j (quotEdgeForm h hs f)) =
      (CellClass.edgeClass k j h).colourPairs.lift L n f := by
    funext ι
    rcases ι with ⟨⟨⟩, a, c⟩
    show pauliCoeff a (quotEdgeForm h hs f (Tower.FullSpace.projEdge L n k j c.1)) =
      f ((CellClass.edgeClass k j h).colourPairs.proj L n ⟨(), (a, c)⟩)
    rw [← hB.2.1 c]
    exact congrFun (quotCoeffsOn_quotEdgeForm h hs f)
      ((CellClass.edgeClass k j h).colourPairs.proj L n ⟨(), (a, c)⟩)
  rw [← hread]
  exact fullEdgeForm_coeffsOn ha h hform
theorem fullEdgeForm_congr (h : j ≤ k) {f g : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ}
    (b : PeriodicOperators.PosEdge L k j)
    (e : ∀ a : Fin 3, f ⟨(), (a, b)⟩ = g ⟨(), (a, b)⟩) :
    fullEdgeForm h f b.1 = fullEdgeForm h g b.1 := by
  unfold fullEdgeForm
  rw [antisymmExtend_of_pos _ b.2, antisymmExtend_of_pos _ b.2]
  exact Finset.sum_congr rfl fun a _ => congrArg (· • ComplexMatrix2.pauliFamily a) (e a)
def fullBracketTerm (h : j ≤ k) (W : Tower.FullSpace.Edge L k j → ComplexMatrix2)
    (f : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ)
    (f' : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    PeriodicOperators.PosEdge L k j → ComplexMatrix2 :=
  fun c => bracketValue (W c.1) (fullVertexField h f c.1.initial)
    (fullVertexField h f c.1.terminal) (fullEdgeForm h f' c.1)
def fullBracketMap (h : j ≤ k) (W : Tower.FullSpace.Edge L k j → ComplexMatrix2)
    (f : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ)
    (f' : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    Idx L (CellClass.edgeClass k j h).colourPairs → ℂ :=
  fun ι => toPauliCoeffs (fullBracketTerm h W f f') (idxEquiv L (CellClass.edgeClass k j h) ι)
def quotBracketTerm (h : j ≤ k) (hs : ProjSurjective L n (CellClass.edgeClass k j h))
    (V : Tower.Edge L n k j → ComplexMatrix2)
    (f : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ)
    (f' : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    Tower.PositiveEdge L n k j → ComplexMatrix2 :=
  fun c => bracketValue (V c.1) (quotVertexField h f c.1.source)
    (quotVertexField h f c.1.target) (quotEdgeForm h hs f' c.1)
theorem fullBracketTerm_add_left (h : j ≤ k) (W : Tower.FullSpace.Edge L k j → ComplexMatrix2)
    (f g : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ)
    (f' : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    fullBracketTerm h W (f + g) f' = fullBracketTerm h W f f' + fullBracketTerm h W g f' := by
  funext c
  show bracketValue _ (fullVertexField h (f + g) _) (fullVertexField h (f + g) _) _ = _
  rw [fullVertexField_add]
  exact bracketValue_add_left _ _ _ _ _ _
theorem fullBracketTerm_smul_left (h : j ≤ k) (W : Tower.FullSpace.Edge L k j → ComplexMatrix2)
    (z : ℂ) (f : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ)
    (f' : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    fullBracketTerm h W (z • f) f' = z • fullBracketTerm h W f f' := by
  funext c
  show bracketValue _ (fullVertexField h (z • f) _) (fullVertexField h (z • f) _) _ = _
  rw [fullVertexField_smul]
  exact bracketValue_smul_left _ _ _ _ _
theorem fullBracketTerm_add_right (h : j ≤ k) (W : Tower.FullSpace.Edge L k j → ComplexMatrix2)
    (f : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ)
    (f' g' : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    fullBracketTerm h W f (f' + g') = fullBracketTerm h W f f' + fullBracketTerm h W f g' := by
  funext c
  show bracketValue _ _ _ (fullEdgeForm h (f' + g') _) = _
  rw [fullEdgeForm_add]
  exact bracketValue_add_right _ _ _ _ _
theorem fullBracketTerm_smul_right (h : j ≤ k) (W : Tower.FullSpace.Edge L k j → ComplexMatrix2)
    (z : ℂ) (f : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ)
    (f' : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    fullBracketTerm h W f (z • f') = z • fullBracketTerm h W f f' := by
  funext c
  show bracketValue _ _ _ (fullEdgeForm h (z • f') _) = _
  rw [fullEdgeForm_smul]
  exact bracketValue_smul_right _ _ _ _ _
theorem quotBracketTerm_add_left (h : j ≤ k)
    (hss : ProjSurjective L n (CellClass.vertexClass k j h))
    (hs : ProjSurjective L n (CellClass.edgeClass k j h)) (V : Tower.Edge L n k j → ComplexMatrix2)
    (f g : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ)
    (f' : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    quotBracketTerm h hs V (f + g) f' = quotBracketTerm h hs V f f' + quotBracketTerm h hs V g f' := by
  funext c
  show bracketValue _ (quotVertexField h (f + g) _) (quotVertexField h (f + g) _) _ = _
  rw [quotVertexField_add h hss]
  exact bracketValue_add_left _ _ _ _ _ _
theorem quotBracketTerm_smul_left (h : j ≤ k)
    (hss : ProjSurjective L n (CellClass.vertexClass k j h))
    (hs : ProjSurjective L n (CellClass.edgeClass k j h)) (V : Tower.Edge L n k j → ComplexMatrix2)
    (z : ℂ) (f : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ)
    (f' : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    quotBracketTerm h hs V (z • f) f' = z • quotBracketTerm h hs V f f' := by
  funext c
  show bracketValue _ (quotVertexField h (z • f) _) (quotVertexField h (z • f) _) _ = _
  rw [quotVertexField_smul h hss]
  exact bracketValue_smul_left _ _ _ _ _
theorem quotBracketTerm_add_right (h : j ≤ k) (hs : ProjSurjective L n (CellClass.edgeClass k j h))
    (V : Tower.Edge L n k j → ComplexMatrix2)
    (f : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ)
    (f' g' : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    quotBracketTerm h hs V f (f' + g') =
      quotBracketTerm h hs V f f' + quotBracketTerm h hs V f g' := by
  funext c
  show bracketValue _ _ _ (quotEdgeForm h hs (f' + g') _) = _
  rw [quotEdgeForm_add]
  exact bracketValue_add_right _ _ _ _ _
theorem quotBracketTerm_smul_right (h : j ≤ k) (hs : ProjSurjective L n (CellClass.edgeClass k j h))
    (V : Tower.Edge L n k j → ComplexMatrix2) (z : ℂ)
    (f : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ)
    (f' : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    quotBracketTerm h hs V f (z • f') = z • quotBracketTerm h hs V f f' := by
  funext c
  show bracketValue _ _ _ (quotEdgeForm h hs (z • f') _) = _
  rw [quotEdgeForm_smul]
  exact bracketValue_smul_right _ _ _ _ _
def quotBracketMap (h : j ≤ k) (hss : ProjSurjective L n (CellClass.vertexClass k j h))
    (hs : ProjSurjective L n (CellClass.edgeClass k j h)) (V : Tower.Edge L n k j → ComplexMatrix2) :
    ((CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ) →ₗ[ℂ]
      ((CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) →ₗ[ℂ]
        ((CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :=
  LinearMap.mk₂ ℂ (fun f f' κ => toPauliCoeffs (quotBracketTerm h hs V f f') (quotIdxEquiv hs κ))
    (fun f g f' => by
      funext κ
      show toPauliCoeffs (quotBracketTerm h hs V (f + g) f') _ = _
      rw [quotBracketTerm_add_left h hss]
      exact toPauliCoeffs_add (fun _ => bracketValue_mem _ _ _ _)
        (fun _ => bracketValue_mem _ _ _ _) _)
    (fun z f f' => by
      funext κ
      show toPauliCoeffs (quotBracketTerm h hs V (z • f) f') _ = _
      rw [quotBracketTerm_smul_left h hss]
      exact toPauliCoeffs_smul z (fun _ => bracketValue_mem _ _ _ _) _)
    (fun f f' g' => by
      funext κ
      show toPauliCoeffs (quotBracketTerm h hs V f (f' + g')) _ = _
      rw [quotBracketTerm_add_right]
      exact toPauliCoeffs_add (fun _ => bracketValue_mem _ _ _ _)
        (fun _ => bracketValue_mem _ _ _ _) _)
    (fun z f f' => by
      funext κ
      show toPauliCoeffs (quotBracketTerm h hs V f (z • f')) _ = _
      rw [quotBracketTerm_smul_right]
      exact toPauliCoeffs_smul z (fun _ => bracketValue_mem _ _ _ _) _)
theorem fullVertexField_congr (h : j ≤ k)
    {f g : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ}
    (x : Tower.FullSpace.Vertex L k j) (e : ∀ a : Fin 3, f ⟨(), (a, x)⟩ = g ⟨(), (a, x)⟩) :
    fullVertexField h f x = fullVertexField h g x := by
  show ∑ a, f ⟨(), (a, x)⟩ • ComplexMatrix2.pauliFamily a =
    ∑ a, g ⟨(), (a, x)⟩ • ComplexMatrix2.pauliFamily a
  exact Finset.sum_congr rfl fun a _ => congrArg (· • ComplexMatrix2.pauliFamily a) (e a)
theorem fullBracketTerm_congr (h : j ≤ k) (W : Tower.FullSpace.Edge L k j → ComplexMatrix2)
    {f g : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ}
    {f' g' : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ}
    (c : PeriodicOperators.PosEdge L k j)
    (ht : fullVertexField h f c.1.initial = fullVertexField h g c.1.initial)
    (hh : fullVertexField h f c.1.terminal = fullVertexField h g c.1.terminal)
    (hb : fullEdgeForm h f' c.1 = fullEdgeForm h g' c.1) :
    fullBracketTerm h W f f' c = fullBracketTerm h W g g' c := by
  unfold fullBracketTerm
  rw [ht, hh, hb]
theorem supNormVec_terminal_sub_initial_le {a : ℝ} (ha : 0 ≤ a) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : TorusMetric.supNormVec (b.terminal.1 - b.initial.1) ≤ a := by
  obtain ⟨μ, hμ⟩ := hb
  have e : b.terminal.1 - b.initial.1 = Pi.single μ a := congrArg Subtype.val hμ
  rw [e]
  refine Finset.sup'_le _ _ fun ν _ => ?_
  by_cases hν : ν = μ
  · subst hν
    simp [abs_of_nonneg ha]
  · simp [Pi.single_eq_of_ne hν, ha]
theorem supNormVec_zero_le_one : TorusMetric.supNormVec (0 : Fin 4 → ℝ) ≤ 1 :=
  Finset.sup'_le _ _ fun _ _ => by simp
theorem isLocalBilinear_fullBracketMap (ha : meshAt L k j ≤ 1) (ha₀ : 0 < meshAt L k j)
    (h : j ≤ k) (W : Tower.FullSpace.Edge L k j → ComplexMatrix2) :
    IsLocalBilinear ((CellClass.vertexClass k j h).colourPairs.toPeriodicData L)
      ((CellClass.edgeClass k j h).colourPairs.toPeriodicData L)
      ((CellClass.edgeClass k j h).colourPairs.toPeriodicData L) 1
      (fullBracketMap h W) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro f g f' _ _ _
    funext ι
    show toPauliCoeffs (fullBracketTerm h W (f + g) f') _ = _
    rw [fullBracketTerm_add_left]
    exact toPauliCoeffs_add (fun _ => bracketValue_mem _ _ _ _)
      (fun _ => bracketValue_mem _ _ _ _) _
  · intro z f f' _ _
    funext ι
    show toPauliCoeffs (fullBracketTerm h W (z • f) f') _ = _
    rw [fullBracketTerm_smul_left]
    exact toPauliCoeffs_smul z (fun _ => bracketValue_mem _ _ _ _) _
  · intro f f' g' _ _ _
    funext ι
    show toPauliCoeffs (fullBracketTerm h W f (f' + g')) _ = _
    rw [fullBracketTerm_add_right]
    exact toPauliCoeffs_add (fun _ => bracketValue_mem _ _ _ _)
      (fun _ => bracketValue_mem _ _ _ _) _
  · intro z f f' _ _
    funext ι
    show toPauliCoeffs (fullBracketTerm h W f (z • f')) _ = _
    rw [fullBracketTerm_smul_right]
    exact toPauliCoeffs_smul z (fun _ => bracketValue_mem _ _ _ _) _
  · intro f g f' g' _ _ _ _ ι h₁ h₂
    rcases ι with ⟨⟨⟩, a, c⟩
    have ht : fullVertexField h f c.1.initial = fullVertexField h g c.1.initial :=
      fullVertexField_congr h _ fun a' => h₁ ⟨(), (a', c.1.initial)⟩ (by
        show TorusMetric.supNormVec (c.1.initial.1 - c.1.initial.1) ≤ 1
        rw [sub_self]
        exact supNormVec_zero_le_one)
    have hh : fullVertexField h f c.1.terminal = fullVertexField h g c.1.terminal :=
      fullVertexField_congr h _ fun a' => h₁ ⟨(), (a', c.1.terminal)⟩
        ((supNormVec_terminal_sub_initial_le ha₀.le c.2).trans ha)
    have hb : fullEdgeForm h f' c.1 = fullEdgeForm h g' c.1 :=
      fullEdgeForm_congr h c fun a' => h₂ ⟨(), (a', c)⟩ (by
        show TorusMetric.supNormVec (c.1.initial.1 - c.1.initial.1) ≤ 1
        rw [sub_self]
        exact supNormVec_zero_le_one)
    exact congrArg (pauliCoeff a) (fullBracketTerm_congr h W c ht hh hb)
theorem restrictToPositiveEdges_full_levelBracketTerm (h : j ≤ k)
    (W : Tower.FullSpace.Edge L k j → ComplexMatrix2)
    (f : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ)
    (f' : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ) :
    Tower.FullSpace.restrictToPositiveEdges
        (Tower.FullSpace.levelBracketTerm W (fullVertexField h f) (fullEdgeForm h f')) =
      fullBracketTerm h W f f' :=
  funext fun c => if_pos c.2
theorem restrictToPositiveEdges_quot_levelBracketTerm (h : j ≤ k)
    (hs : ProjSurjective L n (CellClass.edgeClass k j h)) (V : Tower.Edge L n k j → ComplexMatrix2)
    (f : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ)
    (f' : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    restrictToPositiveEdges (levelBracketTerm V (quotVertexField h f) (quotEdgeForm h hs f')) =
      quotBracketTerm h hs V f f' :=
  funext fun c => if_pos c.2
theorem hasFiniteSupp_fullBracketTerm (h : j ≤ k) (W : Tower.FullSpace.Edge L k j → ComplexMatrix2)
    (f : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ)
    {f' : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ}
    (hf' : PeriodicOperators.HasFiniteSupport f') :
    HasFiniteSupp (fullBracketTerm h W f f') := by
  refine (hasFiniteSupp_fullEdgeForm h hf').subset fun c hc => ?_
  intro h0
  refine hc ?_
  have h0' : fullEdgeForm h f' c.1 = 0 := h0
  show bracketValue _ _ _ (fullEdgeForm h f' c.1) = 0
  rw [h0', bracketValue_zero]
theorem traceFinsumPairing_fullVertex (hP : OneLoop.PauliMatrixRelations) (h : j ≤ k)
    {l : Tower.FullSpace.Vertex L k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (hfin : HasFiniteSupp l)
    (g : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ) :
    traceFinsumPairing l (CellClass.ofCoeffs L (CellClass.vertexClass k j h) g) =
      weightedBracket L (CellClass.vertexClass k j h).colourPairs
        (CellClass.coeffsOn L (CellClass.vertexClass k j h) l) g :=
  traceFinsumPairing_ofCoeffs hP (CellClass.vertexClass k j h) (f := l) hl hfin g
theorem traceFinsumPairing_quotVertex (hP : OneLoop.PauliMatrixRelations) (h : j ≤ k)
    (hss : ProjSurjective L n (CellClass.vertexClass k j h))
    {l : Tower.Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (hfin : HasFiniteSupp l)
    (g : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ) :
    traceFinsumPairing l (CellClass.ofQuotCoeffs L n (CellClass.vertexClass k j h) g) =
      quotBracket L n (CellClass.vertexClass k j h).colourPairs
        (CellClass.quotCoeffsOn L n (CellClass.vertexClass k j h) l) g :=
  traceFinsumPairing_ofQuotCoeffs hP hss (f := l) hl hfin g
theorem isBracketKernel_iff (hP : OneLoop.PauliMatrixRelations)
    (ha : 0 < meshAt L k j) (h : j ≤ k)
    (hqb : ∀ b : PeriodicOperators.PosEdge L k j,
      (projPositiveEdge L n k j b).1 = Tower.FullSpace.projEdge L n k j b.1)
    {V J : Tower.Edge L n k j → ComplexMatrix2} (hJ : J ∈ complexEdgeForms L n k j)
    (T : KernelMatrix (Idx L (CellClass.edgeClass k j h).colourPairs)
      (Idx L (CellClass.vertexClass k j h).colourPairs)) :
    IsBracketKernel L n k j h V J T ↔
      IsBilinearKernel L n (CellClass.vertexClass k j h).colourPairs
        (CellClass.edgeClass k j h).colourPairs (CellClass.edgeClass k j h).colourPairs
        (fullBracketMap h (liftGaugeField L n k j V))
        (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) J) T := by
  have key : ∀ (f : Idx L (CellClass.vertexClass k j h).colourPairs → ℂ)
      (f' : Idx L (CellClass.edgeClass k j h).colourPairs → ℂ),
      PeriodicOperators.HasFiniteSupport f' →
      Tower.FullSpace.finiteEdgePairing (liftGaugeField L n k j J)
        (Tower.FullSpace.levelBracketTerm (liftGaugeField L n k j V)
          (fullVertexField h f) (fullEdgeForm h f')) =
      weightedBracket L (CellClass.edgeClass k j h).colourPairs
        ((CellClass.edgeClass k j h).colourPairs.lift L n
          (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) J))
        (fullBracketMap h (liftGaugeField L n k j V) f f') := fun f f' hf' => by
    unfold Tower.FullSpace.finiteEdgePairing
    rw [restrictToPositiveEdges_full_levelBracketTerm]
    exact traceFinsumPairing_lift_right hP h hqb hJ _ (fun _ => bracketValue_mem _ _ _ _)
      (hasFiniteSupp_fullBracketTerm h _ f hf')
  constructor
  · intro hT f f' hf hf'
    have h₁ := hT _ (fullVertexField_mem h f) (hasFiniteSupp_ofCoeffs _ hf) _
      (fullEdgeForm_mem ha h f') (hasFiniteSupp_fullEdgeForm h hf')
    rw [coeffsOn_fullEdgeForm] at h₁
    have e := traceFinsumPairing_fullVertex hP h (l := fullVertexField h f)
      (fun x => ofPauliCoeffs_mem _ x) (hasFiniteSupp_ofCoeffs _ hf) (applyKernel T f')
    rw [coeffsOn_fullVertexField] at e
    exact e.symm.trans (h₁.trans (key f f' hf'))
  · intro hT l hl hlf B hB hBf
    have hf₁ := hasFiniteSupport_coeffs (CellClass.vertexClass k j h) hlf
    have hf₂ := hasFiniteSupport_coeffs (CellClass.edgeClass k j h) hBf
    have h₁ := hT (CellClass.coeffsOn L (CellClass.vertexClass k j h) l)
      (CellClass.coeffsOn L (CellClass.edgeClass k j h) B) hf₁ hf₂
    have h₂ := key (CellClass.coeffsOn L (CellClass.vertexClass k j h) l)
      (CellClass.coeffsOn L (CellClass.edgeClass k j h) B) hf₂
    rw [fullVertexField_coeffsOn h hl, fullEdgeForm_coeffsOn ha h hB] at h₂
    exact (traceFinsumPairing_fullVertex hP h (fun x => hl x (mem_univ _)) hlf _).trans
      (h₁.trans h₂.symm)
theorem isBracketMatrix_iff (hP : OneLoop.PauliMatrixRelations)
    (hx : ∀ b : Tower.Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (h : j ≤ k) (hss : ProjSurjective L n (CellClass.vertexClass k j h))
    (hs : ProjSurjective L n (CellClass.edgeClass k j h))
    (hfs : Finite (Tower.Vertex L n k j)) (hfb : Finite (Tower.PositiveEdge L n k j))
    {V J : Tower.Edge L n k j → ComplexMatrix2} (hJ : J ∈ complexEdgeForms L n k j)
    (M : KernelMatrix ((CellClass.edgeClass k j h).colourPairs.ImageCarrier L n)
      ((CellClass.vertexClass k j h).colourPairs.ImageCarrier L n)) :
    IsBracketMatrix L n k j h V J M ↔
      IsBilinearMatrix L n (CellClass.vertexClass k j h).colourPairs
        (CellClass.edgeClass k j h).colourPairs (CellClass.edgeClass k j h).colourPairs
        (quotBracketMap h hss hs V) (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) J) M := by
  have key : ∀ (f : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ)
      (f' : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ),
      edgeFormPairing J (levelBracketTerm V (quotVertexField h f) (quotEdgeForm h hs f')) =
      quotBracket L n (CellClass.edgeClass k j h).colourPairs
        (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) J)
        (quotBracketMap h hss hs V f f') := fun f f' => by
    unfold edgeFormPairing
    rw [restrictToPositiveEdges_quot_levelBracketTerm]
    exact traceFinsumPairing_quot_right hP h hs hfb hJ _ fun _ => bracketValue_mem _ _ _ _
  constructor
  · intro hM f f'
    have h₁ := hM _ (quotVertexField_mem h f) _ (quotEdgeForm_mem hx h hs f')
    have hfin : HasFiniteSupp (quotVertexField h f) := Set.toFinite _
    rw [quotCoeffsOn_quotEdgeForm] at h₁
    have e := traceFinsumPairing_quotVertex hP h hss (l := quotVertexField h f)
      (fun x => ofPauliCoeffs_mem _ x) hfin (applyKernel M f')
    rw [quotCoeffsOn_quotVertexField h hss] at e
    exact e.symm.trans (h₁.trans (key f f'))
  · intro hM l hl B hB
    have h₁ := hM (CellClass.quotCoeffsOn L n (CellClass.vertexClass k j h) l)
      (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) B)
    have h₂ := key (CellClass.quotCoeffsOn L n (CellClass.vertexClass k j h) l)
      (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) B)
    rw [quotVertexField_quotCoeffsOn h hss hl, quotEdgeForm_quotCoeffsOn hx h hs hB] at h₂
    have hfin : HasFiniteSupp l := Set.toFinite _
    exact (traceFinsumPairing_quotVertex hP h hss (fun x => hl x (mem_univ _)) hfin _).trans
      (h₁.trans h₂.symm)
theorem fullBracketTerm_lift (ha : 0 < meshAt L k j)
    (hx : ∀ b : Tower.Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (h : j ≤ k) (hss : ProjSurjective L n (CellClass.vertexClass k j h))
    (hs : ProjSurjective L n (CellClass.edgeClass k j h))
    (hB : ProjEdgesCompatible L n k j) (V : Tower.Edge L n k j → ComplexMatrix2)
    (f : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ)
    (f' : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ)
    (c : PeriodicOperators.PosEdge L k j) :
    fullBracketTerm h (liftGaugeField L n k j V)
        ((CellClass.vertexClass k j h).colourPairs.lift L n f)
        ((CellClass.edgeClass k j h).colourPairs.lift L n f') c =
      quotBracketTerm h hs V f f' (projPositiveEdge L n k j c) := by
  have hq := hB.2.1 c
  have t₁ : (projPositiveEdge L n k j c).1.source =
      Tower.FullSpace.projVertex L n k j c.1.initial := by
    rw [hq]
    exact (hB.1 c.1).1
  have t₂ : (projPositiveEdge L n k j c).1.target =
      Tower.FullSpace.projVertex L n k j c.1.terminal := by
    rw [hq]
    exact (hB.1 c.1).2
  have e₁ : fullVertexField h ((CellClass.vertexClass k j h).colourPairs.lift L n f) c.1.initial =
      quotVertexField h f (projPositiveEdge L n k j c).1.source := by
    rw [t₁]
    exact fullVertexField_lift h hss f _
  have e₂ : fullVertexField h ((CellClass.vertexClass k j h).colourPairs.lift L n f) c.1.terminal =
      quotVertexField h f (projPositiveEdge L n k j c).1.target := by
    rw [t₂]
    exact fullVertexField_lift h hss f _
  have e₃ : fullEdgeForm h ((CellClass.edgeClass k j h).colourPairs.lift L n f') c.1 =
      quotEdgeForm h hs f' (projPositiveEdge L n k j c).1 := by
    rw [fullEdgeForm_lift ha hx h hs hB f', hq]
    rfl
  have e₄ : liftGaugeField L n k j V c.1 = V (projPositiveEdge L n k j c).1 := by
    rw [hq]
    rfl
  unfold fullBracketTerm quotBracketTerm
  rw [e₁, e₂, e₃, e₄]
theorem full_levelBracketTerm_mem (ha : 0 < meshAt L k j)
    (W : Tower.FullSpace.Edge L k j → ComplexMatrix2)
    (l : Tower.FullSpace.Vertex L k j → ComplexMatrix2)
    (B : Tower.FullSpace.Edge L k j → ComplexMatrix2) :
    Tower.FullSpace.levelBracketTerm W l B ∈ Tower.FullSpace.complexEdgeForms (meshAt L k j) := by
  classical
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · show (if b.IsPositivelyOriented then _ else _) ∈ ComplexMatrix2.traceless
    rw [if_pos hb]
    exact bracketValue_mem _ _ _ _
  · show (if b.opposite.IsPositivelyOriented then _ else _) =
      -(if b.IsPositivelyOriented then _ else _)
    rcases link_xor_opposite ha b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [if_neg h₂, if_pos h₁, link_opposite_opposite]
    · rw [if_pos h₁, if_neg h₂, neg_neg]
end Sides
private theorem xor_opposite_of_level (hXor : PeriodicLattice.LevelBondOrientationDichotomy)
    {L n : ℕ} (k j : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (h : j ≤ k) :
    ∀ b : Tower.Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by
  have e : PeriodicLattice.levelDepth (k + 1) (j + 1) = PeriodicLattice.levelDepth k j := by
    simp [PeriodicLattice.levelDepth]
  have h₁ := hXor L n (k + 1) hL hn (Nat.succ_pos k) (j + 1) (Nat.succ_le_succ h)
  unfold Tower.Edge PeriodicLattice.BondAtLevel at *
  rw [e] at h₁
  exact h₁
abbrev _root_.YangMills.SharedProofs.p22685 := @xor_opposite_of_level
theorem descendsClaim (hBil : LocalBilinearKernels.Claim)
    (hCells : PeriodicLiftCells.CellsAndClassesHold)
    (hP : OneLoop.PauliMatrixRelations)
    (hXor : PeriodicLattice.LevelBondOrientationDichotomy) : DescendsClaim := by
  intro L hL k n hn j h V _ J hJ
  have hCl := hCells L hL k n hn
  have hc := hCl.1 j h
  have hss : ProjSurjective L n (CellClass.vertexClass k j h) := (hc.1 .vertex).1
  have hs : ProjSurjective L n (CellClass.edgeClass k j h) := (hc.1 .edge).1
  have hFs : Finite ((CellClass.vertexClass k j h).colourPairs.ImageCarrier L n) := (hCl.2 _).1
  have hFb : Finite ((CellClass.edgeClass k j h).colourPairs.ImageCarrier L n) := (hCl.2 _).1
  have hfs : Finite (Tower.Vertex L n k j) := by
    have : Finite (Fin 3 × Tower.Vertex L n k j) := Finite.of_equiv _ (quotIdxEquiv hss)
    exact Finite.of_injective (fun b => ((0 : Fin 3), b)) fun _ _ e => (Prod.ext_iff.1 e).2
  have hfb : Finite (Tower.PositiveEdge L n k j) := by
    have : Finite (Fin 3 × Tower.PositiveEdge L n k j) :=
      Finite.of_equiv _ (quotIdxEquiv hs)
    exact Finite.of_injective (fun b => ((0 : Fin 3), b)) fun _ _ e => (Prod.ext_iff.1 e).2
  have hx := xor_opposite_of_level hXor k j hL hn h
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  have ha₀ : 0 < meshAt L k j := zpow_pos (by linarith) _
  have ha₁ : meshAt L k j ≤ 1 :=
    zpow_le_one_of_nonpos₀ hL1 (by omega)
  have hloc := isLocalBilinear_fullBracketMap ha₁ ha₀ h (liftGaugeField L n k j V)
  have h4 : 4 * (1 : ℝ) < (periodSide L n : ℝ) := by
    have h₁ : L ≤ L ^ n := Nat.le_self_pow (Nat.pos_iff_ne_zero.1 hn) L
    have h₂ : 4 < periodSide L n := by
      have := hL.2
      unfold periodSide
      omega
    calc (4 : ℝ) * 1 = ((4 : ℕ) : ℝ) := by norm_num
      _ < _ := by exact_mod_cast h₂
  have hper : ∀ (f : (CellClass.vertexClass k j h).colourPairs.ImageCarrier L n → ℂ)
      (f' : (CellClass.edgeClass k j h).colourPairs.ImageCarrier L n → ℂ),
      fullBracketMap h (liftGaugeField L n k j V)
          ((CellClass.vertexClass k j h).colourPairs.lift L n f)
          ((CellClass.edgeClass k j h).colourPairs.lift L n f') =
        (CellClass.edgeClass k j h).colourPairs.lift L n (quotBracketMap h hss hs V f f') := by
    intro f f'
    funext ι
    rcases ι with ⟨⟨⟩, a, c⟩
    exact congrArg (pauliCoeff a) (fullBracketTerm_lift ha₀ hx h hss hs hc.2 V f f' c)
  obtain ⟨-, hTu, hMu, hall⟩ := hBil L hL k n hn (CellClass.vertexClass k j h).colourPairs
    (CellClass.edgeClass k j h).colourPairs (CellClass.edgeClass k j h).colourPairs 1
    (by norm_num) h4 _ (quotBracketMap h hss hs V)
    (CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h) J) hloc hper
  refine ⟨fun l _ _ B _ hBf => ⟨full_levelBracketTerm_mem ha₀ _ l B, ?_⟩, ?_, ?_,
    fun T M hT hM => ?_⟩
  · refine hBf.subset fun c hc' h0 => hc' ?_
    have h0' : B c.1 = 0 := h0
    have e : Tower.FullSpace.restrictToPositiveEdges (Tower.FullSpace.levelBracketTerm
        (liftGaugeField L n k j V) l B) c =
        bracketValue (liftGaugeField L n k j V c.1) (l c.1.initial) (l c.1.terminal) (B c.1) :=
      if_pos c.2
    rw [e, h0', bracketValue_zero]
  · exact (existsUnique_congr fun T => isBracketKernel_iff hP ha₀ h hc.2.2.1 hJ T).2 hTu
  · exact (existsUnique_congr fun M => isBracketMatrix_iff hP hx h hss hs hfs hfb hJ M).2 hMu
  · obtain ⟨h₁, h₂, h₃⟩ := hall T M ((isBracketKernel_iff hP ha₀ h hc.2.2.1 hJ T).1 hT)
      ((isBracketMatrix_iff hP hx h hss hs hfs hfb hJ M).1 hM)
    refine ⟨?_, h₂, h₃⟩
    have e : (2 : ℝ) * 1 = 2 := by norm_num
    rwa [e] at h₁
end YangMills.Construction.LocalKernels.BracketAtPeriodicLift
end
