import YangMills.Construction.Towers.RelationsOfTheIteratedAveragesOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.CommutatorTermAtAPeriodicExtensionDescendsProof
import YangMills.Construction.Towers.TheBracketOfTheMatricesOfTheBackgroundKernel
import YangMills.Construction.Towers.TheTorusMatricesOfTheMassiveOperatorFunctionsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower.SixMatrixBracket
open LocalKernels LocalKernels.Periodisation
open PeriodicOperators (BackgroundKernelFactors swapKernel applyKernel compKernel unitKernel)
open AsDifferentials (complexQuadraticTerm)
private theorem sum_smul_pauliFamily_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
private theorem pauliCoeff_add (a : Fin 3) {X Y : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (X + Y) = pauliCoeff a X + pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p106 <;> assumption
private theorem pauliCoeff_smul (a : Fin 3) (z : ℂ) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) : pauliCoeff a (z • X) = z * pauliCoeff a X := by apply _root_.YangMills.SharedProofs.p5172 <;> assumption
private theorem wPairing_toPauliCoeffs (hP : OneLoop.PauliMatrixRelations)
    {σ J : Type} (e : J ≃ Fin 3 × σ) (w : J → ℝ) (hw : ∀ i, w i = 1) (f g : σ → ComplexMatrix2)
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) (hg : ∀ x, g x ∈ ComplexMatrix2.traceless)
    (hfin : HasFiniteSupp f ∨ HasFiniteSupp g) :
    PeriodicOperators.wPairing w (fun i => toPauliCoeffs f (e i))
        (fun i => toPauliCoeffs g (e i)) = traceFinsumPairing f g := by apply _root_.YangMills.SharedProofs.p12066 <;> assumption
private theorem toPauliCoeffs_ofPauliCoeffs {σ : Type} (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
private theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
private theorem ofPauliCoeffs_toPauliCoeffs {σ : Type} {f : σ → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) : ofPauliCoeffs (toPauliCoeffs f) = f := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldMeans.ofPauliCoeffs_toPauliCoeffs <;> assumption
private theorem toPauliCoeffs_add {σ : Type} {X Y : σ → ComplexMatrix2}
    (hX : ∀ x, X x ∈ ComplexMatrix2.traceless) (hY : ∀ x, Y x ∈ ComplexMatrix2.traceless)
    (p : Fin 3 × σ) : toPauliCoeffs (X + Y) p = toPauliCoeffs X p + toPauliCoeffs Y p :=
  pauliCoeff_add p.1 (hX p.2) (hY p.2)
private theorem toPauliCoeffs_smul {σ : Type} (z : ℂ) {X : σ → ComplexMatrix2}
    (hX : ∀ x, X x ∈ ComplexMatrix2.traceless) (p : Fin 3 × σ) :
    toPauliCoeffs (z • X) p = z * toPauliCoeffs X p :=
  pauliCoeff_smul p.1 z (hX p.2)
def plainDot {N : Type} (f g : N → ℂ) : ℂ := ∑' i, f i * g i
section Matrices
variable {N N' N'' : Type}
theorem plainDot_eq_sum [Fintype N] (f g : N → ℂ) : plainDot f g = ∑ i, f i * g i := tsum_fintype _
theorem applyKernel_eq_sum [Fintype N] (T : N' → N → ℂ) (f : N → ℂ) (i : N') :
    applyKernel T f i = ∑ j, T i j * f j := tsum_fintype _
theorem plainDot_comm (f g : N → ℂ) : plainDot f g = plainDot g f := by
  simp only [plainDot, mul_comm]
theorem plainDot_add_right [Finite N] (f g h : N → ℂ) :
    plainDot f (g + h) = plainDot f g + plainDot f h := by
  have := Fintype.ofFinite N
  simp only [plainDot_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]
theorem plainDot_sub_right [Finite N] (f g h : N → ℂ) :
    plainDot f (g - h) = plainDot f g - plainDot f h := by
  have := Fintype.ofFinite N
  simp only [plainDot_eq_sum, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
theorem plainDot_smul_right [Finite N] (z : ℂ) (f g : N → ℂ) :
    plainDot f (z • g) = z * plainDot f g := by
  have := Fintype.ofFinite N
  simp only [plainDot_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
theorem plainDot_sub_left [Finite N] (f g h : N → ℂ) :
    plainDot (f - g) h = plainDot f h - plainDot g h := by
  rw [plainDot_comm, plainDot_sub_right, plainDot_comm h f, plainDot_comm h g]
theorem plainDot_smul_left [Finite N] (z : ℂ) (f g : N → ℂ) :
    plainDot (z • f) g = z * plainDot f g := by
  rw [plainDot_comm, plainDot_smul_right, plainDot_comm g f]
theorem applyKernel_comp [Finite N] [Finite N'] (S : N'' → N' → ℂ) (T : N' → N → ℂ)
    (f : N → ℂ) : applyKernel (compKernel S T) f = applyKernel S (applyKernel T f) := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices.applyKernel_compKernel <;> assumption
theorem applyKernel_add [Finite N] (S T : N' → N → ℂ) (f : N → ℂ) :
    applyKernel (S + T) f = applyKernel S f + applyKernel T f := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices.applyKernel_add <;> assumption
theorem applyKernel_sub [Finite N] (S T : N' → N → ℂ) (f : N → ℂ) :
    applyKernel (S - T) f = applyKernel S f - applyKernel T f := by apply _root_.YangMills.Construction.Tower.IterRelationsOnTorus.applyKernel_sub <;> assumption
theorem applyKernel_smul [Finite N] (z : ℂ) (T : N' → N → ℂ) (f : N → ℂ) :
    applyKernel (z • T) f = z • applyKernel T f := by
  have := Fintype.ofFinite N
  funext i
  simp only [applyKernel_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
theorem applyKernel_add_right [Finite N] (T : N' → N → ℂ) (f g : N → ℂ) :
    applyKernel T (f + g) = applyKernel T f + applyKernel T g := by
  have := Fintype.ofFinite N
  funext i
  simp only [applyKernel_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]
theorem applyKernel_smul_right [Finite N] (z : ℂ) (T : N' → N → ℂ) (f : N → ℂ) :
    applyKernel T (z • f) = z • applyKernel T f := by
  have := Fintype.ofFinite N
  funext i
  simp only [applyKernel_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring
theorem applyKernel_unit (f : N → ℂ) : applyKernel (unitKernel N) f = f := by apply _root_.YangMills.Construction.Tower.IterRelationsOnTorus.applyKernel_unit <;> assumption
theorem plainDot_applyKernel [Finite N] [Finite N'] (T : N' → N → ℂ) (x : N' → ℂ) (y : N → ℂ) :
    plainDot x (applyKernel T y) = plainDot (applyKernel (swapKernel T) x) y := by
  have := Fintype.ofFinite N
  have := Fintype.ofFinite N'
  simp only [plainDot_eq_sum, applyKernel_eq_sum, swapKernel, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
theorem plainDot_swapKernel [Finite N] [Finite N'] (T : N' → N → ℂ) (x : N → ℂ) (y : N' → ℂ) :
    plainDot x (applyKernel (swapKernel T) y) = plainDot (applyKernel T x) y :=
  plainDot_applyKernel (swapKernel T) x y
theorem plainDot_indicator [DecidableEq N] (f : N → ℂ) (i : N) :
    plainDot f (fun j => if j = i then 1 else 0) = f i := by
  unfold plainDot
  rw [tsum_eq_single i]
  · simp
  · intro b hb
    simp [hb]
end Matrices
section Factors
variable {S B S' : Type} [Finite S] [Finite B] [Finite S'] (F : BackgroundKernelFactors S B S')
omit [Finite S'] in
theorem applyKernel_tauKernel (x : B → ℂ) :
    applyKernel F.tauKernel x = x + applyKernel F.diff (applyKernel F.sigma x) := by
  unfold BackgroundKernelFactors.tauKernel
  rw [applyKernel_add, applyKernel_unit, applyKernel_comp]
omit [Finite B] in
theorem applyKernel_complementKernel (y : S → ℂ) :
    applyKernel F.complementKernel y =
      y - F.scale • applyKernel (swapKernel F.avg) (applyKernel F.avg y) := by
  unfold BackgroundKernelFactors.complementKernel
  rw [applyKernel_sub, applyKernel_unit, applyKernel_smul, applyKernel_comp]
omit [Finite B] in
theorem plainDot_complementKernel (x y : S → ℂ) :
    plainDot x (applyKernel F.complementKernel y) =
      plainDot (applyKernel F.complementKernel x) y := by
  rw [applyKernel_complementKernel, applyKernel_complementKernel, plainDot_sub_right,
    plainDot_sub_left, plainDot_smul_right, plainDot_smul_left, plainDot_swapKernel,
    plainDot_comm (applyKernel (swapKernel F.avg) _) y, plainDot_swapKernel,
    plainDot_comm (applyKernel F.avg y)]
theorem plainDot_assembled (b b' : B → ℂ) :
    plainDot b (applyKernel F.assembled b') =
      plainDot b (applyKernel F.hess b') +
        plainDot (applyKernel F.complementKernel (applyKernel (swapKernel F.diff) b))
          (applyKernel F.complementKernel (applyKernel (swapKernel F.diff) b')) +
        (2 * plainDot (applyKernel F.sigma b) (applyKernel F.brk b') +
          plainDot (applyKernel F.sigma b)
            (applyKernel F.brk (applyKernel F.diff (applyKernel F.sigma b'))) -
          plainDot (applyKernel F.tauKernel b)
            (applyKernel F.quad (applyKernel F.tauKernel b'))) := by
  have h₁ : plainDot b (applyKernel (compKernel (swapKernel F.sigma) F.brk) b') =
      plainDot (applyKernel F.sigma b) (applyKernel F.brk b') := by
    rw [applyKernel_comp, plainDot_swapKernel]
  have h₂ : plainDot b (applyKernel (compKernel (compKernel (swapKernel F.sigma) F.brk)
        (compKernel F.diff F.sigma)) b') =
      plainDot (applyKernel F.sigma b)
        (applyKernel F.brk (applyKernel F.diff (applyKernel F.sigma b'))) := by
    simp only [applyKernel_comp]
    rw [plainDot_swapKernel]
  have h₃ : plainDot b (applyKernel (compKernel (compKernel (swapKernel F.tauKernel) F.quad)
        F.tauKernel) b') =
      plainDot (applyKernel F.tauKernel b) (applyKernel F.quad (applyKernel F.tauKernel b')) := by
    simp only [applyKernel_comp]
    rw [plainDot_swapKernel]
  have h₄ : plainDot b (applyKernel (compKernel (compKernel F.diff F.complementKernel)
        (compKernel F.complementKernel (swapKernel F.diff))) b') =
      plainDot (applyKernel F.complementKernel (applyKernel (swapKernel F.diff) b))
        (applyKernel F.complementKernel (applyKernel (swapKernel F.diff) b')) := by
    simp only [applyKernel_comp]
    rw [plainDot_applyKernel, plainDot_complementKernel]
  unfold BackgroundKernelFactors.assembled
  rw [applyKernel_add, applyKernel_sub, applyKernel_add, applyKernel_add, applyKernel_smul,
    plainDot_add_right, plainDot_sub_right, plainDot_add_right, plainDot_add_right,
    plainDot_smul_right, h₁, h₂, h₃, h₄]
  ring
end Factors
structure CoeffExtraction (S : PairedFunctionSpace) (J : Type) where
  read : (S.index → ComplexMatrix2) → J → ℂ
  read_add : ∀ f ∈ S.complexSubmodule, ∀ g ∈ S.complexSubmodule, read (f + g) = read f + read g
  read_smul : ∀ (z : ℂ), ∀ f ∈ S.complexSubmodule, read (z • f) = z • read f
  pair_eq : ∀ f ∈ S.complexSubmodule, ∀ g ∈ S.complexSubmodule,
    S.pair f g = plainDot (read f) (read g)
structure CoeffExtraction.Inverse {S : PairedFunctionSpace} {J : Type} (R : CoeffExtraction S J) where
  lift : (J → ℂ) → S.index → ComplexMatrix2
  lift_mem : ∀ g, lift g ∈ S.complexSubmodule
  read_lift : ∀ g, R.read (lift g) = g
  lift_read : ∀ f ∈ S.complexSubmodule, lift (R.read f) = f
  finiteSupport : ∀ f, S.IsFinitelySupported f
section Transposes
variable {S S' : PairedFunctionSpace} {J J' : Type} [Finite J] [Finite J']
theorem read_transposeMap (R : CoeffExtraction S J) (I : R.Inverse) (R' : CoeffExtraction S' J')
    (T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule) (M : J' → J → ℂ)
    (hT : ∀ f : S.complexSubmodule, R'.read (T f) = applyKernel M (R.read f))
    (g : S'.complexSubmodule) :
    R.read (PairedFunctionSpace.transposeMap T g) = applyKernel (swapKernel M) (R'.read g) := by
  classical
  have lift_add : ∀ a b, I.lift (a + b) = I.lift a + I.lift b := by
    intro a b
    have h := I.lift_read _ (S.complexSubmodule.add_mem (I.lift_mem a) (I.lift_mem b))
    rwa [R.read_add _ (I.lift_mem a) _ (I.lift_mem b), I.read_lift, I.read_lift] at h
  have lift_smul : ∀ (z : ℂ) a, I.lift (z • a) = z • I.lift a := by
    intro z a
    have h := I.lift_read _ (S.complexSubmodule.smul_mem z (I.lift_mem a))
    rwa [R.read_smul _ _ (I.lift_mem a), I.read_lift] at h
  let T' : S'.complexSubmodule →ₗ[ℂ] S.complexSubmodule :=
    { toFun := fun g => ⟨I.lift (applyKernel (swapKernel M) (R'.read g)), I.lift_mem _⟩
      map_add' := fun a b => Subtype.ext (by
        show I.lift (applyKernel (swapKernel M) (R'.read (a.1 + b.1))) = _
        rw [R'.read_add _ a.2 _ b.2, applyKernel_add_right, lift_add]
        rfl)
      map_smul' := fun z a => Subtype.ext (by
        show I.lift (applyKernel (swapKernel M) (R'.read (z • a.1))) = _
        rw [R'.read_smul _ _ a.2, applyKernel_smul_right, lift_smul]
        rfl) }
  have hT' : PairedFunctionSpace.IsTransposeMap T T' := by
    intro g f _
    show S.pair (I.lift (applyKernel (swapKernel M) (R'.read g))) f = _
    rw [R.pair_eq _ (I.lift_mem _) _ f.2, R'.pair_eq _ g.2 _ (T f).2, I.read_lift, hT f,
      plainDot_applyKernel]
  have hspec : PairedFunctionSpace.IsTransposeMap T (PairedFunctionSpace.transposeMap T) :=
    Classical.epsilon_spec (p := PairedFunctionSpace.IsTransposeMap T) ⟨T', hT'⟩
  funext i
  have h₁ := hspec g ⟨I.lift fun j => if j = i then 1 else 0, I.lift_mem _⟩ (I.finiteSupport _)
  rw [R.pair_eq _ (PairedFunctionSpace.transposeMap T g).2 _ (I.lift_mem _),
    R'.pair_eq _ g.2 _ (T _).2, hT, I.read_lift, plainDot_indicator, plainDot_applyKernel,
    plainDot_indicator] at h₁
  exact h₁
theorem transposeOfValues_read (R : CoeffExtraction S J) (I : R.Inverse) (R' : CoeffExtraction S' J')
    (m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2)
    (hm : ∃ T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule,
      ∀ f : S.complexSubmodule, (T f : S'.index → ComplexMatrix2) = m f)
    (M : J' → J → ℂ) (hM : ∀ f ∈ S.complexSubmodule, R'.read (m f) = applyKernel M (R.read f))
    {g : S'.index → ComplexMatrix2} (hg : g ∈ S'.complexSubmodule) :
    PairedFunctionSpace.transposeOfValues S S' m g ∈ S.complexSubmodule ∧
      R.read (PairedFunctionSpace.transposeOfValues S S' m g) =
        applyKernel (swapKernel M) (R'.read g) := by
  have hv : ∀ f : S.complexSubmodule,
      (PairedFunctionSpace.linearOfValues S S' m f : S'.index → ComplexMatrix2) = m f :=
    Classical.epsilon_spec hm
  unfold PairedFunctionSpace.transposeOfValues
  rw [dif_pos hg]
  refine ⟨Subtype.property _, ?_⟩
  exact read_transposeMap R I R' _ M (fun f => by rw [hv f]; exact hM f f.2) ⟨g, hg⟩
end Transposes
section Cells
variable {L n k : ℕ}
abbrev ProjSurjective (L n : ℕ) (A : CellClass k) : Prop :=
  Function.Surjective
    (Cell.proj n : Cell L k A.level A.cellType → QuotientCell L n k A.level A.cellType)
theorem mem_colourImage {A : CellClass k} (hs : ProjSurjective L n A)
    (p : Fin 3 × QuotientCell L n k A.level A.cellType) : p ∈ A.colourComponent.image L n := by apply _root_.YangMills.Construction.LocalKernels.BracketAtPeriodicLift.mem_pairPart_image <;> assumption
def quotientPairEquiv {A : CellClass k} (hs : ProjSurjective L n A) :
    A.colourPairs.ImageCarrier L n ≃ Fin 3 × QuotientCell L n k A.level A.cellType where
  toFun κ := κ.2.1
  invFun p := ⟨(), ⟨p, mem_colourImage hs p⟩⟩
  left_inv κ := by rcases κ with ⟨⟨⟩, p, hp⟩; rfl
  right_inv _ := rfl
theorem toPauliCoeffs_ofQuotCoeffs {A : CellClass k} (hs : ProjSurjective L n A)
    (g : A.colourPairs.ImageCarrier L n → ℂ) (κ : A.colourPairs.ImageCarrier L n) :
    toPauliCoeffs (CellClass.ofQuotCoeffs L n A g) (quotientPairEquiv hs κ) = g κ := by
  rcases κ with ⟨⟨⟩, p, hp⟩
  refine (congrFun (toPauliCoeffs_ofPauliCoeffs _) p).trans ?_
  exact dif_pos hp
theorem ofQuotCoeffs_eq {A : CellClass k} (hs : ProjSurjective L n A)
    (g : A.colourPairs.ImageCarrier L n → ℂ) :
    CellClass.ofQuotCoeffs L n A g =
      ofPauliCoeffs fun p => g ((quotientPairEquiv hs).symm p) := by
  unfold CellClass.ofQuotCoeffs
  congr 1
  funext ι
  exact dif_pos (mem_colourImage hs ι)
theorem quotBracket_eq_plainDot (A : CellClass k) (f g : A.colourPairs.ImageCarrier L n → ℂ) :
    quotBracket L n A.colourPairs f g = plainDot f g := by
  unfold quotBracket PeriodicOperators.wPairing plainDot
  refine tsum_congr fun i => ?_
  have e : A.colourPairs.imageWeight L n i = 1 := rfl
  rw [e]
  simp
theorem traceFinsumPairing_ofQuotCoeffs (hP : OneLoop.PauliMatrixRelations)
    {A : CellClass k} (hs : ProjSurjective L n A)
    (hF : Finite (QuotientCell L n k A.level A.cellType))
    {f : QuotientCell L n k A.level A.cellType → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) (g : A.colourPairs.ImageCarrier L n → ℂ) :
    traceFinsumPairing f (CellClass.ofQuotCoeffs L n A g) =
      plainDot (fun κ => toPauliCoeffs f (quotientPairEquiv hs κ)) g := by
  have e := wPairing_toPauliCoeffs hP (quotientPairEquiv hs) (A.colourPairs.imageWeight L n)
    (fun _ => rfl) f (CellClass.ofQuotCoeffs L n A g) hf
    (fun _ => sum_smul_pauliFamily_mem_traceless _) (Or.inl (toFinite _))
  have e₁ : (fun i => toPauliCoeffs (CellClass.ofQuotCoeffs L n A g) (quotientPairEquiv hs i)) =
      g :=
    funext (toPauliCoeffs_ofQuotCoeffs hs g)
  rw [e₁] at e
  rw [← quotBracket_eq_plainDot]
  exact e.symm
end Cells
section BlockEvaluations
variable {L n k : ℕ}
theorem finite_quotientCell {A : CellClass k} (hs : ProjSurjective L n A)
    (hF : Finite (A.colourPairs.ImageCarrier L n)) :
    Finite (QuotientCell L n k A.level A.cellType) := by
  have : Finite (Fin 3 × QuotientCell L n k A.level A.cellType) :=
    Finite.of_equiv _ (quotientPairEquiv hs)
  exact Finite.of_injective (fun b => ((0 : Fin 3), b)) fun _ _ e => (Prod.ext_iff.1 e).2
def vertexCoeffCoordinate (hP : OneLoop.PauliMatrixRelations) {j : ℕ} (h : j ≤ k)
    (hs : ProjSurjective L n (CellClass.vertexClass k j h)) (hF : Finite (Vertex L n k j)) :
    CoeffExtraction (pairedFunctions (Vertex L n k j))
      ((CellClass.vertexClass k j h).colourPairs.ImageCarrier L n) where
  read := CellClass.quotCoeffsOn L n (CellClass.vertexClass k j h)
  read_add f hf g hg := funext fun κ => toPauliCoeffs_add (X := f) (Y := g)
    (fun x => hf x (mem_univ _)) (fun x => hg x (mem_univ _)) κ.2.1
  read_smul z f hf := funext fun κ => toPauliCoeffs_smul (X := f) z
    (fun x => hf x (mem_univ _)) κ.2.1
  pair_eq f hf g hg := by
    rw [← quotBracket_eq_plainDot]
    exact (wPairing_toPauliCoeffs hP (quotientPairEquiv hs) _ (fun _ => rfl) f g
      (fun x => hf x (mem_univ _)) (fun x => hg x (mem_univ _))
      (Or.inl (Set.toFinite (Function.support (show Vertex L n k j → ComplexMatrix2 from f))))).symm
def vertexCoeffInverse (hP : OneLoop.PauliMatrixRelations) {j : ℕ} (h : j ≤ k)
    (hs : ProjSurjective L n (CellClass.vertexClass k j h)) (hF : Finite (Vertex L n k j)) :
    (vertexCoeffCoordinate hP h hs hF).Inverse where
  lift := CellClass.ofQuotCoeffs L n (CellClass.vertexClass k j h)
  lift_mem g := fun x _ => ofPauliCoeffs_mem _ x
  read_lift g := funext (toPauliCoeffs_ofQuotCoeffs hs g)
  lift_read f hf := by
    rw [ofQuotCoeffs_eq hs]
    exact ofPauliCoeffs_toPauliCoeffs fun x => hf x (mem_univ _)
  finiteSupport f := Set.toFinite (Function.support (show Vertex L n k j → ComplexMatrix2 from f))
def edgeCoeffRepr (hP : OneLoop.PauliMatrixRelations) {j : ℕ} (h : j ≤ k)
    (hs : ProjSurjective L n (CellClass.edgeClass k j h))
    (hF : Finite (QuotientCell L n k (CellClass.edgeClass k j h).level
      (CellClass.edgeClass k j h).cellType)) :
    CoeffExtraction (edgePairedSpace L n k j)
      ((CellClass.edgeClass k j h).colourPairs.ImageCarrier L n) where
  read := CellClass.quotCoeffsOn L n (CellClass.edgeClass k j h)
  read_add f hf g hg := funext fun κ => toPauliCoeffs_add (X := restrictToPositiveEdges f)
    (Y := restrictToPositiveEdges g) (fun x => hf.1 x.1 x.2) (fun x => hg.1 x.1 x.2) κ.2.1
  read_smul z f hf := funext fun κ => toPauliCoeffs_smul (X := restrictToPositiveEdges f) z
    (fun x => hf.1 x.1 x.2) κ.2.1
  pair_eq f hf g hg := by
    rw [← quotBracket_eq_plainDot]
    exact (wPairing_toPauliCoeffs hP (quotientPairEquiv hs) _ (fun _ => rfl)
      (restrictToPositiveEdges f) (restrictToPositiveEdges g) (fun x => hf.1 x.1 x.2)
      (fun x => hg.1 x.1 x.2) (Or.inl (toFinite _))).symm
theorem linear_and_matrix_of_periodizes {A A' : CellClass k} {R : ℝ}
    {mW : ((CellClass.fullSpace L A).index → ComplexMatrix2) →
      (CellClass.fullSpace L A').index → ComplexMatrix2}
    {mT : ((CellClass.quotSpace L n A).index → ComplexMatrix2) →
      (CellClass.quotSpace L n A').index → ComplexMatrix2}
    (h : Periodizes L n A A' R mW mT) :
    (∃ T : (CellClass.quotSpace L n A).complexSubmodule →ₗ[ℂ]
        (CellClass.quotSpace L n A').complexSubmodule,
        ∀ f : (CellClass.quotSpace L n A).complexSubmodule,
          (T f : (CellClass.quotSpace L n A').index → ComplexMatrix2) = mT f) ∧
      ∀ f ∈ (CellClass.quotSpace L n A).complexSubmodule,
        CellClass.quotCoeffsOn L n A' (mT f) =
          applyKernel (pairMatrixOfMap L n A A' mT) (CellClass.quotCoeffsOn L n A f) := by
  obtain ⟨_, m, _, _, hval, ⟨M, hM, _⟩, _⟩ := h
  refine ⟨⟨m, hval⟩, fun f hf => ?_⟩
  have hex : ∃ M, ∀ f : (CellClass.quotSpace L n A).complexSubmodule,
      CellClass.quotCoeffsOn L n A' (mT f) = applyKernel M (CellClass.quotCoeffsOn L n A f) :=
    ⟨M, fun f => by rw [← hval f]; exact hM f⟩
  exact Classical.epsilon_spec hex ⟨f, hf⟩
end BlockEvaluations
section Gauge
variable {Ss Sb Sk : PairedFunctionSpace} {Js Jb Jk : Type} [Finite Js] [Finite Jb] [Finite Jk]
theorem mem_complexSubmodule_of_linear {S S' : PairedFunctionSpace}
    {m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2}
    (hm : ∃ T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule,
      ∀ f : S.complexSubmodule, (T f : S'.index → ComplexMatrix2) = m f)
    {f : S.index → ComplexMatrix2} (hf : f ∈ S.complexSubmodule) : m f ∈ S'.complexSubmodule := by
  obtain ⟨T, hT⟩ := hm
  have e := hT ⟨f, hf⟩
  exact e ▸ (T ⟨f, hf⟩).2
theorem complementTerm_read (Rs : CoeffExtraction Ss Js) (Is : Rs.Inverse) (Rb : CoeffExtraction Sb Jb)
    (Rk : CoeffExtraction Sk Jk) (F : BackgroundKernelFactors Js Jb Jk)
    (D : (Ss.index → ComplexMatrix2) → Sb.index → ComplexMatrix2)
    (a : (Ss.index → ComplexMatrix2) → Sk.index → ComplexMatrix2)
    (hD : ∃ T : Ss.complexSubmodule →ₗ[ℂ] Sb.complexSubmodule,
      ∀ f : Ss.complexSubmodule, (T f : Sb.index → ComplexMatrix2) = D f)
    (hDM : ∀ f ∈ Ss.complexSubmodule, Rb.read (D f) = applyKernel F.diff (Rs.read f))
    (ha : ∃ T : Ss.complexSubmodule →ₗ[ℂ] Sk.complexSubmodule,
      ∀ f : Ss.complexSubmodule, (T f : Sk.index → ComplexMatrix2) = a f)
    (haM : ∀ f ∈ Ss.complexSubmodule, Rk.read (a f) = applyKernel F.avg (Rs.read f))
    (r : ℝ) (hr : F.scale = (r : ℂ))
    (hsmul : ∀ (z : Ss.index → ComplexMatrix2), r • z = (r : ℂ) • z)
    {X : Sb.index → ComplexMatrix2} (hX : X ∈ Sb.complexSubmodule) :
    (PairedFunctionSpace.transposeOfValues Ss Sb D X -
        r • PairedFunctionSpace.transposeOfValues Ss Sk a
          (a (PairedFunctionSpace.transposeOfValues Ss Sb D X))) ∈ Ss.complexSubmodule ∧
      Rs.read (PairedFunctionSpace.transposeOfValues Ss Sb D X -
        r • PairedFunctionSpace.transposeOfValues Ss Sk a
          (a (PairedFunctionSpace.transposeOfValues Ss Sb D X))) =
        applyKernel F.complementKernel (applyKernel (swapKernel F.diff) (Rb.read X)) := by
  obtain ⟨hy, ry⟩ := transposeOfValues_read Rs Is Rb D hD F.diff hDM hX
  set y := PairedFunctionSpace.transposeOfValues Ss Sb D X with hyd
  have hw : a y ∈ Sk.complexSubmodule := mem_complexSubmodule_of_linear ha hy
  obtain ⟨hz, rz⟩ := transposeOfValues_read Rs Is Rk a ha F.avg haM hw
  set z := PairedFunctionSpace.transposeOfValues Ss Sk a (a y) with hzd
  have e : y - r • z = y + (-(r : ℂ)) • z := by
    rw [hsmul, neg_smul, sub_eq_add_neg]
  have hz' : (-(r : ℂ)) • z ∈ Ss.complexSubmodule := Ss.complexSubmodule.smul_mem _ hz
  rw [e]
  refine ⟨Ss.complexSubmodule.add_mem hy hz', ?_⟩
  rw [Rs.read_add _ hy _ hz', Rs.read_smul _ _ hz, rz, haM y hy, ry,
    applyKernel_complementKernel, hr, neg_smul, sub_eq_add_neg]
end Gauge
section Assembly
variable {L n k : ℕ}
abbrev evalEdgeForm (L n k : ℕ) :
    (Edge L n k 0 → ComplexMatrix2) → (edgesAtZero k).colourPairs.ImageCarrier L n → ℂ :=
  CellClass.quotCoeffsOn L n (edgesAtZero k)
abbrev readVertexFn (L n k : ℕ) :
    (Vertex L n k 0 → ComplexMatrix2) → (verticesAtZero k).colourPairs.ImageCarrier L n → ℂ :=
  CellClass.quotCoeffsOn L n (verticesAtZero k)
theorem plainDot_assembled_eq_backgroundBilinear
    [Finite ((verticesAtZero k).colourPairs.ImageCarrier L n)]
    [Finite ((edgesAtZero k).colourPairs.ImageCarrier L n)]
    [Finite ((CellClass.vertexClass k k le_rfl).colourPairs.ImageCarrier L n)]
    (U J : Edge L n k 0 → ComplexMatrix2) (μ : Edge L n k k → ComplexMatrix2)
    {B B' : Edge L n k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k 0) (hB' : B' ∈ complexEdgeForms L n k 0)
    (F : BackgroundKernelFactors ((verticesAtZero k).colourPairs.ImageCarrier L n)
      ((edgesAtZero k).colourPairs.ImageCarrier L n)
      ((CellClass.vertexClass k k le_rfl).colourPairs.ImageCarrier L n))
    (hA : plainDot (evalEdgeForm L n k B) (applyKernel F.hess (evalEdgeForm L n k B')) =
      complexActionHessian U B B')
    (hG : ∀ X ∈ complexEdgeForms L n k 0, readVertexFn L n k (gaugeFixingTerm L n k U X) =
      applyKernel F.complementKernel (applyKernel (swapKernel F.diff) (evalEdgeForm L n k X)))
    (hGp : traceFinsumPairing (gaugeFixingTerm L n k U B) (gaugeFixingTerm L n k U B') =
      plainDot (readVertexFn L n k (gaugeFixingTerm L n k U B))
        (readVertexFn L n k (gaugeFixingTerm L n k U B')))
    (hσ : ∀ X ∈ complexEdgeForms L n k 0, applyKernel F.sigma (evalEdgeForm L n k X) =
      readVertexFn L n k (backgroundGaugeParameter U X))
    (hσm : ∀ X ∈ complexEdgeForms L n k 0,
      backgroundGaugeParameter U X ∈ GroupLieProduct.tracelessFunctions (Vertex L n k 0))
    (hD : ∀ l ∈ GroupLieProduct.tracelessFunctions (Vertex L n k 0),
      applyKernel F.diff (readVertexFn L n k l) = evalEdgeForm L n k (covDiff U l))
    (hDm : ∀ l ∈ GroupLieProduct.tracelessFunctions (Vertex L n k 0),
      covDiff U l ∈ complexEdgeForms L n k 0)
    (hAdd : ∀ X ∈ complexEdgeForms L n k 0, ∀ Y ∈ complexEdgeForms L n k 0,
      evalEdgeForm L n k (X + Y) = evalEdgeForm L n k X + evalEdgeForm L n k Y)
    (hC : ∀ l ∈ GroupLieProduct.tracelessFunctions (Vertex L n k 0),
      ∀ X ∈ complexEdgeForms L n k 0,
      plainDot (readVertexFn L n k l) (applyKernel F.brk (evalEdgeForm L n k X)) =
        edgeFormPairing J (levelBracketTerm U l X))
    (hQ : ∀ X ∈ complexEdgeForms L n k 0, ∀ Y ∈ complexEdgeForms L n k 0,
      plainDot (evalEdgeForm L n k X) (applyKernel F.quad (evalEdgeForm L n k Y)) =
        traceFinsumPairing (restrictToPositiveEdges μ) (complexQuadraticTerm L n k U X Y)) :
    plainDot (evalEdgeForm L n k B) (applyKernel F.assembled (evalEdgeForm L n k B')) =
      backgroundBilinear U J μ B B' := by
  have hτ : ∀ X ∈ complexEdgeForms L n k 0,
      X + covDiff U (backgroundGaugeParameter U X) ∈ complexEdgeForms L n k 0 :=
    fun X hX => (complexEdgeForms L n k 0).add_mem hX (hDm _ (hσm X hX))
  have hs : ∀ X ∈ complexEdgeForms L n k 0, applyKernel F.tauKernel (evalEdgeForm L n k X) =
      evalEdgeForm L n k (X + covDiff U (backgroundGaugeParameter U X)) := by
    intro X hX
    rw [applyKernel_tauKernel, hσ X hX, hD _ (hσm X hX), hAdd X hX _ (hDm _ (hσm X hX))]
  rw [plainDot_assembled, hs B hB, hs B' hB', hσ B hB, hσ B' hB', hD _ (hσm B' hB'), hA,
    ← hG B hB, ← hG B' hB', ← hGp, hC _ (hσm B hB) B' hB',
    hC _ (hσm B hB) _ (hDm _ (hσm B' hB')), hQ _ (hτ B hB) _ (hτ B' hB')]
  rfl
end Assembly
theorem bracketIsBackgroundBilinear_holds (hY : Periodisation.PeriodisationHolds)
    (hP : OneLoop.PauliMatrixRelations)
    (hK : HessianKernel.KernelProperties) : BracketIsBackgroundBilinear := by
  intro L hL k hk n hn U hU J hJ μ hμ B hB B' hB'
  obtain ⟨hcells, hcls, -, -, -, -, -, hact, havg⟩ := hY L hL k n hn
  have hs0 : ProjSurjective L n (verticesAtZero k) := ((hcells 0 (Nat.zero_le k)).1 .vertex).1
  have hb0 : ProjSurjective L n (edgesAtZero k) := ((hcells 0 (Nat.zero_le k)).1 .edge).1
  have hsk : ProjSurjective L n (CellClass.vertexClass k k le_rfl) :=
    ((hcells k le_rfl).1 .vertex).1
  have i0 : Finite ((verticesAtZero k).colourPairs.ImageCarrier L n) := (hcls _).1
  have i1 : Finite ((edgesAtZero k).colourPairs.ImageCarrier L n) := (hcls _).1
  have i2 : Finite ((CellClass.vertexClass k k le_rfl).colourPairs.ImageCarrier L n) :=
    (hcls _).1
  have fs0 : Finite (Vertex L n k 0) := finite_quotientCell hs0 i0
  have fb0 := finite_quotientCell hb0 i1
  have fsk : Finite (Vertex L n k k) := finite_quotientCell hsk i2
  obtain ⟨-, hDp, hAp, hCp⟩ := hact 0 (Nat.zero_le k) U hU.1 J hJ
  obtain ⟨-, -, hIt, hEx, hSO⟩ := ((havg hk) U hU.1).2 hU μ hμ
  obtain ⟨-, -, hAvP, hDrP⟩ := hIt k le_rfl hk
  have pD := linear_and_matrix_of_periodizes hDp
  have pA := linear_and_matrix_of_periodizes hAp
  have pAv := linear_and_matrix_of_periodizes hAvP
  have pDr := linear_and_matrix_of_periodizes hDrP
  have pE := linear_and_matrix_of_periodizes hEx
  let Rs := vertexCoeffCoordinate hP (Nat.zero_le k) hs0 fs0
  let Is := vertexCoeffInverse hP (Nat.zero_le k) hs0 fs0
  let Rk := vertexCoeffCoordinate hP le_rfl hsk fsk
  let Rb := edgeCoeffRepr hP (Nat.zero_le k) hb0 fb0
  let F := quotFactors L n k U J μ
  have hCM : IsBracketMatrix L n k 0 (Nat.zero_le k) U J F.brk :=
    Classical.epsilon_spec hCp.2.1.exists
  have hQM : IsQuadraticMatrix L n k U μ F.quad :=
    Classical.epsilon_spec hSO.2.1.exists
  have hr : ∀ (z : Vertex L n k 0 → ComplexMatrix2),
      (((L : ℝ) ^ (4 * k)) : ℝ) • z = (((((L : ℝ) ^ (4 * k)) : ℝ)) : ℂ) • z := by
    intro z
    funext x
    ext i j
    simp
  have hgt := fun (X : Edge L n k 0 → ComplexMatrix2) (hX : X ∈ complexEdgeForms L n k 0) =>
    complementTerm_read Rs Is Rb Rk F (covDiff U) (iterAdjointCubeAverage L n k U k)
      pD.1 pD.2 pAv.1 pAv.2 (((L : ℝ) ^ (4 * k)) : ℝ) rfl hr (X := X) hX
  have hσm : ∀ X ∈ complexEdgeForms L n k 0,
      backgroundGaugeParameter U X ∈ GroupLieProduct.tracelessFunctions (Vertex L n k 0) :=
    fun X hX => mem_complexSubmodule_of_linear pE.1 (mem_complexSubmodule_of_linear pDr.1 hX)
  have key := plainDot_assembled_eq_backgroundBilinear (L := L) (n := n) (k := k) U J μ hB hB' F
    ?_ (fun X hX => (hgt X hX).2) ?_ ?_ hσm (fun l hl => (pD.2 l hl).symm)
    (fun l hl => mem_complexSubmodule_of_linear pD.1 hl)
    (fun X hX Y hY' => Rb.read_add X hX Y hY') ?_ ?_
  · rw [← quotBracket_eq_plainDot] at key
    exact key
  · have e := pA.2 B' hB'
    have hm : complexHessianOperator U B' ∈ complexEdgeForms L n k 0 :=
      mem_complexSubmodule_of_linear pA.1 hB'
    have e₂ := Rb.pair_eq B hB _ hm
    have e₃ := ((hK L hL k 0 (Nat.zero_le k)).1 n hn U hU.1).2.2.2.2.1 B hB B' hB'
    rw [← e₃]
    refine Eq.trans ?_ e₂.symm
    exact congrArg (plainDot _) e.symm
  · exact Rs.pair_eq _ (hgt B hB).1 _ (hgt B' hB').1
  · intro X hX
    have e₁ := pDr.2 X hX
    have e₂ := pE.2 _ (mem_complexSubmodule_of_linear pDr.1 hX)
    show applyKernel (compKernel _ _) _ = _
    rw [applyKernel_comp]
    exact (congrArg (applyKernel _) e₁.symm).trans e₂.symm
  · intro l hl X hX
    have e := hCM l hl X hX
    rw [← e]
    exact (traceFinsumPairing_ofQuotCoeffs hP hs0 (finite_quotientCell hs0 i0)
      (fun x => hl x (mem_univ _)) _).symm
  · intro X hX Y hY'
    have e := hQM X hX Y hY'
    rw [← e]
    exact (traceFinsumPairing_ofQuotCoeffs hP hb0 fb0 (fun x => hX.1 x.1 x.2) _).symm
end Tower.SixMatrixBracket
end YangMills.Construction
end
