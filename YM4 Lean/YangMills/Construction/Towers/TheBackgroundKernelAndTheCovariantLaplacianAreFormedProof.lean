import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.IteratedMapsReadTheBlocksProof
import YangMills.Construction.Towers.TheBackgroundKernelAndTheCovariantLaplacianAreFormed
import YangMills.Construction.Towers.TheBackgroundKernelAtZeroProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.HessianLaplacian
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.SymmetricKernels
open YangMills.Construction.Tower.FullSpace.ReadsCubes (LocalAt IsFinitelySupportedForm)
open YangMills.Construction.Tower.FullSpace.AsDifferentials (complexQuadraticTerm)
open YangMills.Construction.Tower.FullSpace.FieldValueFunctions (hessianBilinear rawHessianKernel)
open YangMills.Construction.Tower.AsDifferentials (boundedSubmodule quadraticTermAt)
section PauliCoefficients
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
end PauliCoefficients
structure IsFaithfulEvaluation (r : PauliComponentsOfSymmetricKernel) : Prop where
  mem : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule
  coeffs_ofCoeffs : ∀ c, r.coeffs (r.ofCoeffs c) = c
  ofCoeffs_coeffs : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f
  ofCoeffs_add : ∀ c c', r.ofCoeffs (c + c') = r.ofCoeffs c + r.ofCoeffs c'
  ofCoeffs_smul : ∀ (z : ℂ) c, r.ofCoeffs (z • c) = z • r.ofCoeffs c
  finite_iff : ∀ c, r.space.IsFinitelySupported (r.ofCoeffs c) ↔ (Function.support c).Finite
section Vertices
variable {σ : Type}
theorem ofPauliCoeffs_mem (c : Fin 3 × σ → ℂ) (i : σ) :
    ofPauliCoeffs c i ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem toPauliCoeffs_ofPauliCoeffs (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
theorem ofPauliCoeffs_add (c c' : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (c + c') = ofPauliCoeffs c + ofPauliCoeffs c' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_add <;> assumption
theorem ofPauliCoeffs_smul (z : ℂ) (c : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (z • c) = z • ofPauliCoeffs c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_smul <;> assumption
theorem hasFiniteSupp_ofPauliCoeffs_iff (c : Fin 3 × σ → ℂ) :
    HasFiniteSupp (ofPauliCoeffs c) ↔ (Function.support c).Finite := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.hasFiniteSupp_ofPauliCoeffs_iff <;> assumption
theorem vertexCoordinate_isFaithful (σ : Type) : IsFaithfulEvaluation (vertexCoordinate σ) where
  mem c := fun i _ => ofPauliCoeffs_mem c i
  coeffs_ofCoeffs c := toPauliCoeffs_ofPauliCoeffs c
  ofCoeffs_coeffs _ hf := funext fun i => sum_pauliCoeff_smul (hf i (mem_univ i))
  ofCoeffs_add c c' := ofPauliCoeffs_add c c'
  ofCoeffs_smul z c := ofPauliCoeffs_smul z c
  finite_iff c := hasFiniteSupp_ofPauliCoeffs_iff c
end Vertices
section Oriented
variable (S : PairedFunctionSpace) (pos : S.index → Prop) (rev : S.index → S.index)
def oddExtension (f : S.index → ComplexMatrix2) : S.index → ComplexMatrix2 :=
  open Classical in fun b => if pos b then f b else -f (rev b)
def positiveValues (c : Fin 3 × {b : S.index // pos b} → ℂ) : S.index → ComplexMatrix2 :=
  open Classical in fun b => if h : pos b then ofPauliCoeffs c ⟨b, h⟩ else 0
def formOfCoeffs (c : Fin 3 × {b : S.index // pos b} → ℂ) : S.index → ComplexMatrix2 :=
  oddExtension S pos rev (positiveValues S pos c)
def restrictPos (B : S.index → ComplexMatrix2) : {b : S.index // pos b} → ComplexMatrix2 :=
  fun b => B b.1
def orientedPauliBasis : PauliComponentsOfSymmetricKernel where
  space := S
  Place := {b : S.index // pos b}
  ofCoeffs := formOfCoeffs S pos rev
  coeffs := fun B => toPauliCoeffs (restrictPos S pos B)
structure IsOrientedSpace : Prop where
  xor_pos : ∀ b, Xor (pos b) (pos (rev b))
  rev_rev : ∀ b, rev (rev b) = b
  mem_iff : ∀ B, B ∈ S.complexSubmodule ↔
    (∀ b, pos b → B b ∈ ComplexMatrix2.traceless) ∧ ∀ b, B (rev b) = -B b
  finite_iff : ∀ B, S.IsFinitelySupported B ↔ HasFiniteSupp (restrictPos S pos B)
variable {S pos rev}
theorem oddExtension_of_pos {f : S.index → ComplexMatrix2} {b : S.index} (h : pos b) :
    oddExtension S pos rev f b = f b := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_pos <;> assumption
theorem oddExtension_of_not_pos {f : S.index → ComplexMatrix2} {b : S.index} (h : ¬ pos b) :
    oddExtension S pos rev f b = -f (rev b) := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_neg <;> assumption
theorem oddExtension_rev (hS : IsOrientedSpace S pos rev) (f : S.index → ComplexMatrix2)
    (b : S.index) : oddExtension S pos rev f (rev b) = -oddExtension S pos rev f b := by
  rcases hS.xor_pos b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [oddExtension_of_not_pos h₂, oddExtension_of_pos h₁, hS.rev_rev]
  · rw [oddExtension_of_pos h₁, oddExtension_of_not_pos h₂, neg_neg]
theorem oddExtension_add (f g : S.index → ComplexMatrix2) :
    oddExtension S pos rev (f + g) = oddExtension S pos rev f + oddExtension S pos rev g := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_add <;> assumption
theorem oddExtension_smul (z : ℂ) (f : S.index → ComplexMatrix2) :
    oddExtension S pos rev (z • f) = z • oddExtension S pos rev f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_smul <;> assumption
theorem formOfCoeffs_apply_pos (c : Fin 3 × {b : S.index // pos b} → ℂ) (b : S.index)
    (hb : pos b) : formOfCoeffs S pos rev c b = ofPauliCoeffs c ⟨b, hb⟩ := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_apply <;> assumption
theorem restrictPos_formOfCoeffs (c : Fin 3 × {b : S.index // pos b} → ℂ) :
    restrictPos S pos (formOfCoeffs S pos rev c) = ofPauliCoeffs c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.positivePart_formOfCoeffs <;> assumption
theorem formOfCoeffs_add (c c' : Fin 3 × {b : S.index // pos b} → ℂ) :
    formOfCoeffs S pos rev (c + c') = formOfCoeffs S pos rev c + formOfCoeffs S pos rev c' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_add <;> assumption
theorem formOfCoeffs_smul (z : ℂ) (c : Fin 3 × {b : S.index // pos b} → ℂ) :
    formOfCoeffs S pos rev (z • c) = z • formOfCoeffs S pos rev c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_smul <;> assumption
theorem formOfCoeffs_toPauliCoeffs (hS : IsOrientedSpace S pos rev)
    {f : S.index → ComplexMatrix2}
    (h₁ : ∀ b, pos b → f b ∈ ComplexMatrix2.traceless) (h₂ : ∀ b, f (rev b) = -f b) :
    formOfCoeffs S pos rev (toPauliCoeffs (restrictPos S pos f)) = f := by
  have hpos : ∀ b (hb : pos b),
      formOfCoeffs S pos rev (toPauliCoeffs (restrictPos S pos f)) b = f b := fun b hb =>
    (formOfCoeffs_apply_pos _ b hb).trans (sum_pauliCoeff_smul (h₁ b hb))
  funext b
  by_cases hb : pos b
  · exact hpos b hb
  · have hrb : pos (rev b) := by
      rcases hS.xor_pos b with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd h hb
      · exact h
    have e : formOfCoeffs S pos rev (toPauliCoeffs (restrictPos S pos f)) b =
        -positiveValues S pos (toPauliCoeffs (restrictPos S pos f)) (rev b) :=
      oddExtension_of_not_pos hb
    have e' : positiveValues S pos (toPauliCoeffs (restrictPos S pos f)) (rev b) = f (rev b) := by
      rw [← hpos _ hrb]
      exact (oddExtension_of_pos hrb).symm
    rw [e, e', h₂, neg_neg]
theorem orientedPauliBasis_isFaithful (hS : IsOrientedSpace S pos rev) :
    IsFaithfulEvaluation (orientedPauliBasis S pos rev) where
  mem c := (hS.mem_iff _).2 ⟨fun b hb => by
    have e : formOfCoeffs S pos rev c b ∈ ComplexMatrix2.traceless := by
      rw [formOfCoeffs_apply_pos c b hb]
      exact ofPauliCoeffs_mem c _
    exact e, fun b => oddExtension_rev hS _ b⟩
  coeffs_ofCoeffs c := (congrArg toPauliCoeffs (restrictPos_formOfCoeffs c)).trans
    (toPauliCoeffs_ofPauliCoeffs c)
  ofCoeffs_coeffs f hf :=
    formOfCoeffs_toPauliCoeffs hS ((hS.mem_iff f).1 hf).1 ((hS.mem_iff f).1 hf).2
  ofCoeffs_add c c' := formOfCoeffs_add c c'
  ofCoeffs_smul z c := formOfCoeffs_smul z c
  finite_iff c := by
    refine (hS.finite_iff _).trans ?_
    have e : restrictPos S pos ((orientedPauliBasis S pos rev).ofCoeffs c) = ofPauliCoeffs c :=
      restrictPos_formOfCoeffs c
    rw [e]
    exact hasFiniteSupp_ofPauliCoeffs_iff c
end Oriented
section FullLattice
variable {L : ℕ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem edgePairedSpace_isOriented {a : ℝ} (ha : 0 < a) :
    IsOrientedSpace (edgePairedSpace a) (fun b => b.IsPositivelyOriented)
      InfiniteLattice.Link.opposite where
  xor_pos b := by
    rcases InfiniteLattice.xor_mem_positiveLinks ha b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
    · exact Or.inr ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
  rev_rev _ := rfl
  mem_iff _ := Iff.rfl
  finite_iff _ := Iff.rfl
end FullLattice
section Basics
theorem finite_support_applyKernel_swap {N N' : Type} {K : KernelMatrix N N'} (hK : RowFinite K)
    {c : N' → ℂ} (hc : (Function.support c).Finite) :
    (Function.support (applyKernel (swapKernel K) c)).Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelAtZeroSources.finite_support_applyKernel_swap <;> assumption
variable {ι : Type}
theorem traceFinsumPairing_add_left (z : ℂ) (f g : ι → ComplexMatrix2) {h : ι → ComplexMatrix2}
    (hh : HasFiniteSupp h) :
    traceFinsumPairing (z • f + g) h =
      z * traceFinsumPairing f h + traceFinsumPairing g h := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelAtZeroSources.traceFinsumPairing_smul_add_left <;> assumption
theorem traceFinsumPairing_add_right (z : ℂ) (f g : ι → ComplexMatrix2)
    {h : ι → ComplexMatrix2} (hh : HasFiniteSupp h) :
    traceFinsumPairing h (z • f + g) =
      z * traceFinsumPairing h f + traceFinsumPairing h g := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelAtZeroSources.traceFinsumPairing_smul_add_right <;> assumption
theorem real_smul_eq_complex_smul (r : ℝ) (f : ι → ComplexMatrix2) : r • f = (r : ℂ) • f := by apply _root_.YangMills.SharedProofs.p7664 <;> assumption
theorem hasFiniteSupp_sub_smul (r : ℝ) {f g : ι → ComplexMatrix2} (hf : HasFiniteSupp f)
    (hg : HasFiniteSupp g) : HasFiniteSupp (f - r • g) := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelAtZeroSources.hasFiniteSupp_sub_smul <;> assumption
end Basics
section Transposes
variable {r r' : PauliComponentsOfSymmetricKernel}
theorem transposeOfValues_eq_transposeMap (S S' : PairedFunctionSpace)
    (m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2) (g : S'.complexSubmodule) :
    PairedFunctionSpace.transposeOfValues S S' m g.1 =
      (PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues S S' m) g).1 := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelAtZeroSources.transposeOfValues_val <;> assumption
theorem transposeOfValues_mem_complex (S S' : PairedFunctionSpace)
    (m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2)
    {g : S'.index → ComplexMatrix2} (hg : g ∈ S'.complexSubmodule) :
    PairedFunctionSpace.transposeOfValues S S' m g ∈ S.complexSubmodule := by apply _root_.YangMills.Construction.Tower.CovDiffTransposes.transposeOfValues_mem <;> assumption
theorem transposeOfValues_finitelySupported (hr : IsFaithfulEvaluation r)
    (hr' : IsFaithfulEvaluation r')
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (H : PauliComponentsOfSymmetricKernel.HasLocalKernel r r' m)
    {g : r'.space.index → ComplexMatrix2} (hg : g ∈ r'.space.complexSubmodule)
    (hfs : r'.space.IsFinitelySupported g) :
    r.space.IsFinitelySupported (PairedFunctionSpace.transposeOfValues r.space r'.space m g) := by
  have hc : (Function.support (r'.coeffs g)).Finite := by
    have e := (hr'.finite_iff (r'.coeffs g)).1
    rw [hr'.ofCoeffs_coeffs g hg] at e
    exact e hfs
  have hval : r.coeffs (PairedFunctionSpace.transposeOfValues r.space r'.space m g) =
      applyKernel (swapKernel (PauliComponentsOfSymmetricKernel.kernel r r' m)) (r'.coeffs g) := by
    have e := (H.swap_represents (r'.coeffs g)).2
    rw [e]
    show _ = r.coeffs (PairedFunctionSpace.transposeOfValues r.space r'.space m
      (r'.ofCoeffs (r'.coeffs g)))
    rw [hr'.ofCoeffs_coeffs g hg]
  have hs := finite_support_applyKernel_swap H.row_finite hc
  rw [← hval] at hs
  have e := (hr.finite_iff _).2 hs
  rwa [hr.ofCoeffs_coeffs _ (transposeOfValues_mem_complex r.space r'.space m hg)] at e
end Transposes
section GaugeFixing
variable {L k : ℕ}
def gaugeFixingLinearMap (L k : ℕ) (U : Edge L k 0 → ComplexMatrix2) :
    (edgePairedSpace (meshAt L k 0)).complexSubmodule →ₗ[ℂ]
      (pairedFunctions (Vertex L k 0)).complexSubmodule :=
  PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues
      (pairedFunctions (Vertex L k 0)) (edgePairedSpace (meshAt L k 0)) (covDiff U)) -
    ((((L : ℝ) ^ (4 * k) : ℝ)) : ℂ) •
      ((PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues
          (pairedFunctions (Vertex L k 0))
          (pairedFunctions (Vertex L k k)) (iterAdjointCubeAverage L k U k))).comp
        ((PairedFunctionSpace.linearOfValues (pairedFunctions (Vertex L k 0))
          (pairedFunctions (Vertex L k k)) (iterAdjointCubeAverage L k U k)).comp
          (PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues
            (pairedFunctions (Vertex L k 0))
            (edgePairedSpace (meshAt L k 0)) (covDiff U)))))
theorem gaugeFixingLinearMap_apply {U : Edge L k 0 → ComplexMatrix2}
    (hA : ∀ f : (pairedFunctions (Vertex L k 0)).complexSubmodule,
      (PairedFunctionSpace.linearOfValues (pairedFunctions (Vertex L k 0))
        (pairedFunctions (Vertex L k k)) (iterAdjointCubeAverage L k U k) f).1 =
          iterAdjointCubeAverage L k U k f.1)
    (B : (edgePairedSpace (meshAt L k 0)).complexSubmodule) :
    (gaugeFixingLinearMap L k U B).1 = gaugeFixingTerm L k U B.1 := by
  set D := PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues
    (pairedFunctions (Vertex L k 0)) (edgePairedSpace (meshAt L k 0)) (covDiff U))
    with hD
  set A := PairedFunctionSpace.linearOfValues (pairedFunctions (Vertex L k 0))
    (pairedFunctions (Vertex L k k)) (iterAdjointCubeAverage L k U k) with hAdef
  have e₁ : covDiffTranspose L k U B.1 = (D B).1 :=
    transposeOfValues_eq_transposeMap _ _ _ B
  have e₂ : iterAdjointCubeAverage L k U k (D B).1 = (A (D B)).1 := (hA _).symm
  have e₃ : iterAverageTranspose L k U (A (D B)).1 =
      (PairedFunctionSpace.transposeMap A (A (D B))).1 :=
    transposeOfValues_eq_transposeMap _ _ _ (A (D B))
  unfold gaugeFixingTerm
  rw [e₁, e₂, e₃]
  have e₄ := real_smul_eq_complex_smul ((L : ℝ) ^ (4 * k))
    ((PairedFunctionSpace.transposeMap A (A (D B))).1 : Vertex L k 0 → ComplexMatrix2)
  refine Eq.trans ?_ (congrArg (Sub.sub (α := Vertex L k 0 → ComplexMatrix2) (D B).1) e₄.symm)
  rfl
end GaugeFixing
section CoefficientForms
variable {L k : ℕ}
def formOfCoeffsLinear (hb : IsFaithfulEvaluation (edgePauliCoordinates L k 0)) :
    finsuppFunctions (Fin 3 × PositiveEdge (meshAt L k 0)) →ₗ[ℂ]
      Edge L k 0 → ComplexMatrix2 where
  toFun c := (edgePauliCoordinates L k 0).ofCoeffs c.1
  map_add' c c' := hb.ofCoeffs_add c.1 c'.1
  map_smul' z c := hb.ofCoeffs_smul z c.1
theorem ofCoeffs_basisFunction (p : Fin 3 × PositiveEdge (meshAt L k 0)) :
    (edgePauliCoordinates L k 0).ofCoeffs
        (PeriodicOperators.basisFunction p).1 = basisForm p.1 p.2 := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelAtZeroSources.ofCoeffs_basisFunction <;> assumption
theorem hasFiniteEdgeSupport_of_restrict {B : Edge L k 0 → ComplexMatrix2}
    (h : HasFiniteSupp (restrictToPositiveEdges B)) : HasFiniteEdgeSupport B :=
  (h.image Subtype.val).subset fun b hb => ⟨⟨b, hb.1⟩, hb.2, rfl⟩
theorem restrict_hasFiniteSupp {B : Edge L k 0 → ComplexMatrix2}
    (h : HasFiniteEdgeSupport B) : HasFiniteSupp (restrictToPositiveEdges B) :=
  (h.preimage Subtype.val_injective.injOn).subset fun b hb => ⟨b.2, hb⟩
end CoefficientForms
section Bilinear
variable {α ι : Type} {𝒮 : Set (α → ComplexMatrix2)}
theorem IsComplexBilinearOn.add {Q Q' : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ}
    (hQ : IsComplexBilinearOn 𝒮 Q) (hQ' : IsComplexBilinearOn 𝒮 Q') :
    IsComplexBilinearOn 𝒮 fun B B' => Q B B' + Q' B B' := by
  intro z E₁ h₁ E₂ h₂ E₃ h₃
  obtain ⟨a, b⟩ := hQ z E₁ h₁ E₂ h₂ E₃ h₃
  obtain ⟨a', b'⟩ := hQ' z E₁ h₁ E₂ h₂ E₃ h₃
  constructor
  · simp only [a, a']
    ring
  · simp only [b, b']
    ring
theorem IsComplexBilinearOn.sub {Q Q' : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ}
    (hQ : IsComplexBilinearOn 𝒮 Q) (hQ' : IsComplexBilinearOn 𝒮 Q') :
    IsComplexBilinearOn 𝒮 fun B B' => Q B B' - Q' B B' := by
  intro z E₁ h₁ E₂ h₂ E₃ h₃
  obtain ⟨a, b⟩ := hQ z E₁ h₁ E₂ h₂ E₃ h₃
  obtain ⟨a', b'⟩ := hQ' z E₁ h₁ E₂ h₂ E₃ h₃
  constructor
  · simp only [a, a']
    ring
  · simp only [b, b']
    ring
theorem IsComplexBilinearOn.const_mul {Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ}
    (c : ℂ) (hQ : IsComplexBilinearOn 𝒮 Q) : IsComplexBilinearOn 𝒮 fun B B' => c * Q B B' := by
  intro z E₁ h₁ E₂ h₂ E₃ h₃
  obtain ⟨a, b⟩ := hQ z E₁ h₁ E₂ h₂ E₃ h₃
  constructor
  · simp only [a]
    ring
  · simp only [b]
    ring
structure IsFinitelySupportedBilinearOn (𝒮 : Set (α → ComplexMatrix2))
    (R : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ι → ComplexMatrix2) : Prop where
  finite : ∀ E₁ ∈ 𝒮, ∀ E₂ ∈ 𝒮, HasFiniteSupp (R E₁ E₂)
  add_left : ∀ z : ℂ, ∀ E₁ ∈ 𝒮, ∀ E₂ ∈ 𝒮, ∀ E₃ ∈ 𝒮,
    R (z • E₁ + E₂) E₃ = z • R E₁ E₃ + R E₂ E₃
  add_right : ∀ z : ℂ, ∀ E₁ ∈ 𝒮, ∀ E₂ ∈ 𝒮, ∀ E₃ ∈ 𝒮,
    R E₃ (z • E₁ + E₂) = z • R E₃ E₁ + R E₃ E₂
theorem traceFinsumPairing_add_right_of_finite (h : ι → ComplexMatrix2) (z : ℂ)
    {f g : ι → ComplexMatrix2} (hf : HasFiniteSupp f) (hg : HasFiniteSupp g) :
    traceFinsumPairing h (z • f + g) =
      z * traceFinsumPairing h f + traceFinsumPairing h g := by
  classical
  have hf' : (Function.support f).Finite := hf
  have hg' : (Function.support g).Finite := hg
  set S : Finset ι := hf'.toFinset ∪ hg'.toFinset with hS
  have zf : ∀ i, i ∉ S → f i = 0 := fun i hi => by
    by_contra h0
    exact hi (Finset.mem_union_left _ (hf'.mem_toFinset.2 h0))
  have zg : ∀ i, i ∉ S → g i = 0 := fun i hi => by
    by_contra h0
    exact hi (Finset.mem_union_right _ (hg'.mem_toFinset.2 h0))
  have sub : ∀ u : ι → ComplexMatrix2, (∀ i, i ∉ S → u i = 0) →
      Function.support (fun i => ComplexMatrix2.halfTrace (h i * u i)) ⊆ ↑S := by
    intro u hu i hi
    rw [Finset.mem_coe]
    by_contra hn
    apply hi
    simp [hu i hn, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
  unfold traceFinsumPairing
  rw [finsum_eq_sum_of_support_subset _ (sub _ fun i hi => ?_),
    finsum_eq_sum_of_support_subset _ (sub _ zf), finsum_eq_sum_of_support_subset _ (sub _ zg),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have e : Matrix.trace (h i * (z • f i + g i)) =
        z * Matrix.trace (h i * f i) + Matrix.trace (h i * g i) := by
      rw [mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    show (1 / 2 : ℂ) * Matrix.trace (h i * (z • f i + g i)) =
      z * ((1 / 2 : ℂ) * Matrix.trace (h i * f i)) + (1 / 2 : ℂ) * Matrix.trace (h i * g i)
    rw [e]
    ring
  · simp [zf i hi, zg i hi]
theorem traceFinsumPairing_bilinear (h : ι → ComplexMatrix2)
    {R : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ι → ComplexMatrix2}
    (hR : IsFinitelySupportedBilinearOn 𝒮 R) :
    IsComplexBilinearOn 𝒮 fun B B' => traceFinsumPairing h (R B B') := by
  intro z E₁ h₁ E₂ h₂ E₃ h₃
  constructor
  · show traceFinsumPairing h (R (z • E₁ + E₂) E₃) = _
    rw [hR.add_left z E₁ h₁ E₂ h₂ E₃ h₃,
      traceFinsumPairing_add_right_of_finite h z (hR.finite _ h₁ _ h₃) (hR.finite _ h₂ _ h₃)]
  · show traceFinsumPairing h (R E₃ (z • E₁ + E₂)) = _
    rw [hR.add_right z E₁ h₁ E₂ h₂ E₃ h₃,
      traceFinsumPairing_add_right_of_finite h z (hR.finite _ h₃ _ h₁) (hR.finite _ h₃ _ h₂)]
variable {E : Type} [AddCommGroup E] [Module ℂ E]
theorem bilinear_zero_left {Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ}
    (hQ : IsComplexBilinearOn 𝒮 Q) (h0 : (0 : α → ComplexMatrix2) ∈ 𝒮)
    {x : α → ComplexMatrix2} (hx : x ∈ 𝒮) : Q 0 x = 0 := by
  have e := (hQ 1 0 h0 0 h0 x hx).1
  simp only [one_smul, add_zero, one_mul] at e
  have e' : Q 0 x + Q 0 x = Q 0 x := e.symm
  simpa using e'
theorem bilinear_zero_right {Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ}
    (hQ : IsComplexBilinearOn 𝒮 Q) (h0 : (0 : α → ComplexMatrix2) ∈ 𝒮)
    {x : α → ComplexMatrix2} (hx : x ∈ 𝒮) : Q x 0 = 0 := by
  have e := (hQ 1 0 h0 0 h0 x hx).2
  simp only [one_smul, add_zero, one_mul] at e
  have e' : Q x 0 + Q x 0 = Q x 0 := e.symm
  simpa using e'
def toBilinearMap (φ : E →ₗ[ℂ] α → ComplexMatrix2) (𝒮 : Set (α → ComplexMatrix2))
    (hφ : ∀ e, φ e ∈ 𝒮) (Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ)
    (hQ : IsComplexBilinearOn 𝒮 Q) : E →ₗ[ℂ] E →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun e e' => Q (φ e) (φ e'))
    (fun e₁ e₂ e₃ => by
      have h := (hQ 1 (φ e₁) (hφ e₁) (φ e₂) (hφ e₂) (φ e₃) (hφ e₃)).1
      simpa using h)
    (fun z e₁ e₃ => by
      have h0 : (0 : α → ComplexMatrix2) ∈ 𝒮 := by
        have := hφ 0
        rwa [map_zero] at this
      have h := (hQ z (φ e₁) (hφ e₁) 0 h0 (φ e₃) (hφ e₃)).1
      rw [bilinear_zero_left hQ h0 (hφ e₃), add_zero, add_zero] at h
      simpa using h)
    (fun e₁ e₂ e₃ => by
      have h := (hQ 1 (φ e₂) (hφ e₂) (φ e₃) (hφ e₃) (φ e₁) (hφ e₁)).2
      simpa using h)
    (fun z e₁ e₃ => by
      have h0 : (0 : α → ComplexMatrix2) ∈ 𝒮 := by
        have := hφ 0
        rwa [map_zero] at this
      have h := (hQ z (φ e₃) (hφ e₃) 0 h0 (φ e₁) (hφ e₁)).2
      rw [bilinear_zero_right hQ h0 (hφ e₁), add_zero, add_zero] at h
      simpa using h)
end Bilinear
section Shift
variable {L k : ℕ}
theorem zeroExtend_add_smul (z : ℂ) (g g' : Vertex L k k → ComplexMatrix2) :
    zeroExtend (z • g + g') = z • zeroExtend g + zeroExtend g' := by
  funext x
  by_cases h : ∃ y : Vertex L k k, y.1 = x.1
  · simp [zeroExtend, dif_pos h]
  · simp [zeroExtend, dif_neg h]
theorem zeroExtend_mem {g : Vertex L k k → ComplexMatrix2}
    (hg : ∀ y, g y ∈ ComplexMatrix2.traceless) (x : Vertex L k 0) :
    zeroExtend g x ∈ ComplexMatrix2.traceless := by
  by_cases h : ∃ y : Vertex L k k, y.1 = x.1
  · have e : zeroExtend g x = g h.choose := dif_pos h
    rw [e]
    exact hg _
  · have e : zeroExtend g x = 0 := dif_neg h
    rw [e]
    exact ComplexMatrix2.traceless.zero_mem
theorem zeroExtend_hasFiniteSupp {g : Vertex L k k → ComplexMatrix2} (hg : HasFiniteSupp g) :
    HasFiniteSupp (zeroExtend g) := by
  have hg' : (Function.support g).Finite := hg
  have hf : ((fun y : Vertex L k k => (y.1 : InfiniteLattice.AmbientSpace)) ''
      Function.support g).Finite := hg'.image _
  refine Set.Finite.of_finite_image (f := fun x : Vertex L k 0 =>
    (x.1 : InfiniteLattice.AmbientSpace)) (hf.subset ?_) Subtype.val_injective.injOn
  rintro _ ⟨x, hx, rfl⟩
  by_cases h : ∃ y : Vertex L k k, y.1 = x.1
  · refine ⟨h.choose, ?_, h.choose_spec⟩
    intro h0
    apply hx
    have e : zeroExtend g x = g h.choose := dif_pos h
    rw [e]
    exact h0
  · exact absurd (show zeroExtend g x = 0 from dif_neg h) hx
variable (hC : ComplexIterChain)
  (hN : CovariantStepComplexLinear)
  (hL : Conventions.IsAdmissibleBlockingFactor L) {U : Edge L k 0 → ComplexMatrix2}
  (hU : U ∈ smallIterateFields L k)
include hC hN hL hU
theorem complexIterDeriv_add_smul (z : ℂ) {B B' : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) (hB' : B' ∈ complexEdgeForms (meshAt L k 0))
    (j : ℕ) (hj : j ≤ k) :
    complexIterDeriv L k j U (z • B + B') =
      z • complexIterDeriv L k j U B + complexIterDeriv L k j U B' := by
  have hz : z • B + B' ∈ complexEdgeForms (meshAt L k 0) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hB) hB'
  induction j with
  | zero =>
    rw [(hC L hL k U hU _ hz).1, (hC L hL k U hU B hB).1, (hC L hL k U hU B' hB').1]
  | succ j ih =>
    have h : j < k := hj
    rw [(hC L hL k U hU _ hz).2.1 j h, ih h.le, (hC L hL k U hU B hB).2.1 j h,
      (hC L hL k U hU B' hB').2.1 j h]
    exact ((hN L hL k j h _ (hU.2 j h)).2.1 _ ((hC L hL k U hU B hB).2.2 j h.le) _
      ((hC L hL k U hU B' hB').2.2 j h.le) z).1
theorem iterContourLogDrift_mem {B : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) (j : ℕ) (hj : j ≤ k) :
    ∀ y, iterContourLogDrift L k U j B y ∈ ComplexMatrix2.traceless := by
  induction j with
  | zero => exact fun _ => ComplexMatrix2.traceless.zero_mem
  | succ j ih =>
    have h : j < k := hj
    have hn := hN L hL k j h _ (hU.2 j h)
    intro y
    exact ComplexMatrix2.traceless.add_mem ((hn.2.2.1 _ (ih h.le)).2 y)
      ((hn.1 _ ((hC L hL k U hU B hB).2.2 j h.le)).2 y)
theorem iterContourLogDrift_add_smul (z : ℂ) {B B' : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) (hB' : B' ∈ complexEdgeForms (meshAt L k 0))
    (j : ℕ) (hj : j ≤ k) :
    iterContourLogDrift L k U j (z • B + B') =
      z • iterContourLogDrift L k U j B + iterContourLogDrift L k U j B' := by
  induction j with
  | zero => simp [iterContourLogDrift]
  | succ j ih =>
    have h : j < k := hj
    have hn := hN L hL k j h _ (hU.2 j h)
    have hQ := (hC L hL k U hU B hB).2.2 j h.le
    have hQ' := (hC L hL k U hU B' hB').2.2 j h.le
    have hm := iterContourLogDrift_mem hC hN hL hU hB j h.le
    have hm' := iterContourLogDrift_mem hC hN hL hU hB' j h.le
    show adjointCubeAverage (complexIter L k j U)
        (iterContourLogDrift L k U j (z • B + B')) +
        contourLogDrift (complexIter L k j U) (complexIterDeriv L k j U (z • B + B')) =
      z • (adjointCubeAverage (complexIter L k j U) (iterContourLogDrift L k U j B) +
        contourLogDrift (complexIter L k j U) (complexIterDeriv L k j U B)) +
      (adjointCubeAverage (complexIter L k j U) (iterContourLogDrift L k U j B') +
        contourLogDrift (complexIter L k j U) (complexIterDeriv L k j U B'))
    rw [ih h.le, complexIterDeriv_add_smul hC hN hL hU z hB hB' j h.le,
      (hn.2.2.2 _ _ hm hm' z).2, (hn.2.1 _ hQ _ hQ' z).2, smul_add]
    abel
theorem gaugeParam_add_smul (z : ℂ) {B B' : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) (hB' : B' ∈ complexEdgeForms (meshAt L k 0)) :
    gaugeParam U (z • B + B') = z • gaugeParam U B + gaugeParam U B' := by
  unfold gaugeParam
  rw [iterContourLogDrift_add_smul hC hN hL hU z hB hB' k le_rfl, zeroExtend_add_smul]
theorem gaugeParam_mem {B : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) :
    ∀ x, gaugeParam U B x ∈ ComplexMatrix2.traceless :=
  zeroExtend_mem (iterContourLogDrift_mem hC hN hL hU hB k le_rfl)
omit hC hN hL hU in
theorem gaugeParam_hasFiniteSupp (hR : LocalAt U) {B : Edge L k 0 → ComplexMatrix2}
    (hB : IsFinitelySupportedForm B) : HasFiniteSupp (gaugeParam U B) :=
  zeroExtend_hasFiniteSupp (hR.contourDrift_finiteSupp B hB)
end Shift
section Bracket
variable {a : ℝ}
theorem restrict_levelBracketTerm_apply (U : InfiniteLattice.Link a → ComplexMatrix2)
    (l : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B : InfiniteLattice.Link a → ComplexMatrix2) (b : PositiveEdge a) :
    restrictToPositiveEdges (levelBracketTerm U l B) b =
      (Complex.I / 2) •
        ⁅l b.1.initial + ComplexMatrix2.conjugateBy (U b.1) (l b.1.terminal), B b.1⁆ := by
  simp [restrictToPositiveEdges, levelBracketTerm, extendOddly, b.2]
theorem levelBracketTerm_add_smul_left (U : InfiniteLattice.Link a → ComplexMatrix2) (z : ℂ)
    (l l' : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B : InfiniteLattice.Link a → ComplexMatrix2) :
    restrictToPositiveEdges (levelBracketTerm U (z • l + l') B) =
      z • restrictToPositiveEdges (levelBracketTerm U l B) +
        restrictToPositiveEdges (levelBracketTerm U l' B) := by
  funext b
  simp only [Pi.add_apply, Pi.smul_apply, restrict_levelBracketTerm_apply]
  simp only [ComplexMatrix2.conjugateBy, Ring.lie_def, mul_add, add_mul, sub_eq_add_neg, neg_add,
    smul_add, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
  rw [smul_comm z (Complex.I / 2)]
  simp only [smul_comm z (Complex.I / 2)]
  abel
theorem levelBracketTerm_add_smul_right (U : InfiniteLattice.Link a → ComplexMatrix2)
    (l : InfiniteLattice.LatticePoint a → ComplexMatrix2) (z : ℂ)
    (B B' : InfiniteLattice.Link a → ComplexMatrix2) :
    restrictToPositiveEdges (levelBracketTerm U l (z • B + B')) =
      z • restrictToPositiveEdges (levelBracketTerm U l B) +
        restrictToPositiveEdges (levelBracketTerm U l B') := by
  funext b
  simp only [Pi.add_apply, Pi.smul_apply, restrict_levelBracketTerm_apply]
  simp only [Ring.lie_def, mul_add, add_mul, sub_eq_add_neg, neg_add, smul_add,
    Matrix.mul_smul, Matrix.smul_mul, smul_neg]
  simp only [smul_comm z (Complex.I / 2)]
  abel
theorem levelBracketTerm_hasFiniteSupp (U : InfiniteLattice.Link a → ComplexMatrix2)
    (l : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    {B : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : HasFiniteSupp (restrictToPositiveEdges B)) :
    HasFiniteSupp (restrictToPositiveEdges (levelBracketTerm U l B)) := by
  have hB' : (Function.support (restrictToPositiveEdges B)).Finite := hB
  refine hB'.subset fun b hb h0 => hb ?_
  have h0' : B b.1 = 0 := h0
  rw [restrict_levelBracketTerm_apply, h0']
  simp [Ring.lie_def]
end Bracket
section QuadraticTerm
variable {L k : ℕ}
theorem mem_boundedSubmodule_of_finite {B : Edge L k 0 → ComplexMatrix2}
    (hB : IsFinitelySupportedForm B) :
    B ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)) := by apply _root_.YangMills.Construction.Tower.FullSpace.ReadsCubes.IsFinitelySupportedForm.mem_boundedSubmodule <;> assumption
theorem complexQuadraticTerm_add_smul_left (U : Edge L k 0 → ComplexMatrix2) (z : ℂ)
    {E₁ E₂ E₃ : Edge L k 0 → ComplexMatrix2}
    (h₁ : IsFinitelySupportedForm E₁) (h₂ : IsFinitelySupportedForm E₂)
    (h₃ : IsFinitelySupportedForm E₃) :
    complexQuadraticTerm L k U (z • E₁ + E₂) E₃ =
      z • complexQuadraticTerm L k U E₁ E₃ + complexQuadraticTerm L k U E₂ E₃ := by
  have b₁ := mem_boundedSubmodule_of_finite h₁
  have b₂ := mem_boundedSubmodule_of_finite h₂
  have b₃ := mem_boundedSubmodule_of_finite h₃
  have bz : z • E₁ + E₂ ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ b₁) b₂
  simp only [complexQuadraticTerm, quadraticTermAt, dif_pos (And.intro bz b₃),
    dif_pos (And.intro b₁ b₃), dif_pos (And.intro b₂ b₃)]
  have e : (⟨z • E₁ + E₂, bz⟩ : boundedSubmodule (complexEdgeForms (meshAt L k 0))) =
      z • ⟨E₁, b₁⟩ + ⟨E₂, b₂⟩ := rfl
  rw [e, map_add, map_smul]
  rfl
theorem complexQuadraticTerm_add_smul_right (U : Edge L k 0 → ComplexMatrix2) (z : ℂ)
    {E₁ E₂ E₃ : Edge L k 0 → ComplexMatrix2}
    (h₁ : IsFinitelySupportedForm E₁) (h₂ : IsFinitelySupportedForm E₂)
    (h₃ : IsFinitelySupportedForm E₃) :
    complexQuadraticTerm L k U E₃ (z • E₁ + E₂) =
      z • complexQuadraticTerm L k U E₃ E₁ + complexQuadraticTerm L k U E₃ E₂ := by
  have b₁ := mem_boundedSubmodule_of_finite h₁
  have b₂ := mem_boundedSubmodule_of_finite h₂
  have b₃ := mem_boundedSubmodule_of_finite h₃
  have bz : z • E₁ + E₂ ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ b₁) b₂
  simp only [complexQuadraticTerm, quadraticTermAt, dif_pos (And.intro b₃ bz),
    dif_pos (And.intro b₃ b₁), dif_pos (And.intro b₃ b₂)]
  have e : (⟨z • E₁ + E₂, bz⟩ : boundedSubmodule (complexEdgeForms (meshAt L k 0))) =
      z • ⟨E₁, b₁⟩ + ⟨E₂, b₂⟩ := rfl
  rw [e, map_add, map_smul]
end QuadraticTerm
section AtAField
open YangMills.Construction.Tower.HessianKernel
variable {L k : ℕ}
theorem hessianBilinear_isComplexBilinearOn (h₃ : ThreeMapKernels.Claim)
    (h₄ : CovariantStepComplexLinear)
    (h₆ : KernelProperties)
    (h₈ : ReadsCubes.Statement)
    (h₉ : ComplexIterChain)
    (h₀ : KernelAtZeroSources.ZeroSourceKernel)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) (J : Edge L k 0 → ComplexMatrix2)
    (μ : Edge L k k → ComplexMatrix2) :
    IsComplexBilinearOn (finiteSupportComplexForms L k 0) (hessianBilinear U J μ) := by
  classical
  have hs₀ : IsFaithfulEvaluation (vertexCoordinate (Vertex L k 0)) := vertexCoordinate_isFaithful _
  have hsk : IsFaithfulEvaluation (vertexCoordinate (Vertex L k k)) := vertexCoordinate_isFaithful _
  have hb : IsFaithfulEvaluation (edgePauliCoordinates L k 0) :=
    orientedPauliBasis_isFaithful (edgePairedSpace_isOriented (meshAt_pos hL k 0))
  have hKer := (h₃ L hL k hk).2
  have hUc : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup := hU.1
  have HD := hKer.2.1 U hUc
  have HA := (hKer.2.2.2 U hU).2
  have hUs : U ∈ smallComplexFields L k 0 := hU.2 0 (by omega)
  have hstep := h₄ L hL k 0 (by omega) U hUs
  obtain ⟨-, tA, -⟩ := h₀ L hL k hk U hU
  have hAmaps : ∀ f ∈ (vertexCoordinate (Vertex L k 0)).space.complexSubmodule,
      iterAdjointCubeAverage L k U k f ∈ (vertexCoordinate (Vertex L k k)).space.complexSubmodule := by
    intro f hf
    have e := tA.1 ⟨f, hf⟩
    have e' : iterAdjointCubeAverage L k U k f = _ := e.symm
    rw [e']
    exact Subtype.property _
  have hGval := gaugeFixingLinearMap_apply (L := L) (k := k) (U := U) tA.1
  have hGfin : ∀ B ∈ complexEdgeForms (meshAt L k 0),
      HasFiniteSupp (restrictToPositiveEdges B) → HasFiniteSupp (gaugeFixingTerm L k U B) := by
    intro B hB hf
    have a₁ := transposeOfValues_finitelySupported hs₀ hb HD hB hf
    have m₁ := transposeOfValues_mem_complex (vertexCoordinate (Vertex L k 0)).space
      (edgePauliCoordinates L k 0).space (covDiff U) hB
    have a₂ := HA.finitely_supported _ m₁ a₁
    have a₃ := transposeOfValues_finitelySupported hs₀ hsk HA (hAmaps _ m₁) a₂
    exact hasFiniteSupp_sub_smul _ a₁ a₃
  have hGlin : ∀ (z : ℂ), ∀ B ∈ complexEdgeForms (meshAt L k 0),
      ∀ B' ∈ complexEdgeForms (meshAt L k 0),
      gaugeFixingTerm L k U (z • B + B') =
        z • gaugeFixingTerm L k U B + gaugeFixingTerm L k U B' := by
    intro z B hB B' hB'
    let b₁ : (edgePairedSpace (meshAt L k 0)).complexSubmodule := ⟨B, hB⟩
    let b₂ : (edgePairedSpace (meshAt L k 0)).complexSubmodule := ⟨B', hB'⟩
    have e₁ := hGval (z • b₁ + b₂)
    have e₂ := hGval b₁
    have e₃ := hGval b₂
    rw [map_add, map_smul] at e₁
    have e₁' : gaugeFixingTerm L k U (z • B + B') = _ := e₁.symm
    have e₂' : gaugeFixingTerm L k U B = _ := e₂.symm
    have e₃' : gaugeFixingTerm L k U B' = _ := e₃.symm
    rw [e₁', e₂', e₃']
    rfl
  have hQ := (h₆ L hL k 0 (Nat.zero_le k)).2 U hUc |>.1
  have hA' : IsComplexBilinearOn (finiteSupportComplexForms L k 0)
      (complexActionHessian U) := fun z E₁ m₁ E₂ m₂ E₃ m₃ =>
    ⟨(hQ z E₁ m₁ E₂ m₂ E₃ m₃).1, (hQ z E₁ m₁ E₂ m₂ E₃ m₃).2.1⟩
  have hG : IsComplexBilinearOn (finiteSupportComplexForms L k 0)
      fun B B' => traceFinsumPairing (gaugeFixingTerm L k U B) (gaugeFixingTerm L k U B') := by
    rintro z E₁ ⟨m₁, f₁⟩ E₂ ⟨m₂, f₂⟩ E₃ ⟨m₃, f₃⟩
    have g₃ := hGfin E₃ m₃ (restrict_hasFiniteSupp f₃)
    refine ⟨?_, ?_⟩
    · show traceFinsumPairing (gaugeFixingTerm L k U (z • E₁ + E₂)) _ = _
      rw [hGlin z E₁ m₁ E₂ m₂, traceFinsumPairing_add_left z _ _ g₃]
    · show traceFinsumPairing _ (gaugeFixingTerm L k U (z • E₁ + E₂)) = _
      rw [hGlin z E₁ m₁ E₂ m₂, traceFinsumPairing_add_right z _ _ g₃]
  have hR : LocalAt U := (h₈ L hL k hk).1 U hU
  have hF : ∀ E ∈ finiteSupportComplexForms L k 0, IsFinitelySupportedForm E := fun E h =>
    ⟨h.1, restrict_hasFiniteSupp h.2⟩
  have hσm : ∀ E ∈ finiteSupportComplexForms L k 0,
      ∀ x, gaugeParam U E x ∈ ComplexMatrix2.traceless :=
    fun E h => gaugeParam_mem h₉ h₄ hL hU h.1
  have hσl : ∀ z : ℂ, ∀ E₁ ∈ finiteSupportComplexForms L k 0,
      ∀ E₂ ∈ finiteSupportComplexForms L k 0,
      gaugeParam U (z • E₁ + E₂) = z • gaugeParam U E₁ + gaugeParam U E₂ :=
    fun z E₁ m₁ E₂ m₂ => gaugeParam_add_smul h₉ h₄ hL hU z m₁.1 m₂.1
  have hDm : ∀ E ∈ finiteSupportComplexForms L k 0,
      covDiff U (gaugeParam U E) ∈ complexEdgeForms (meshAt L k 0) :=
    fun E h => (hstep.2.2.1 _ (hσm E h)).1
  have hDf : ∀ E ∈ finiteSupportComplexForms L k 0,
      HasFiniteSupp (restrictToPositiveEdges (covDiff U (gaugeParam U E))) :=
    fun E h => HD.finitely_supported _ (fun x _ => hσm E h x)
      (gaugeParam_hasFiniteSupp hR (hF E h))
  have hDl : ∀ z : ℂ, ∀ E₁ ∈ finiteSupportComplexForms L k 0,
      ∀ E₂ ∈ finiteSupportComplexForms L k 0,
      covDiff U (gaugeParam U (z • E₁ + E₂)) =
        z • covDiff U (gaugeParam U E₁) + covDiff U (gaugeParam U E₂) :=
    fun z E₁ m₁ E₂ m₂ => by
      rw [hσl z E₁ m₁ E₂ m₂]
      exact (hstep.2.2.2 _ _ (hσm E₁ m₁) (hσm E₂ m₂) z).1
  have hτl : ∀ z : ℂ, ∀ E₁ ∈ finiteSupportComplexForms L k 0,
      ∀ E₂ ∈ finiteSupportComplexForms L k 0,
      shiftedForm U (z • E₁ + E₂) = z • shiftedForm U E₁ + shiftedForm U E₂ :=
    fun z E₁ m₁ E₂ m₂ => by
      unfold shiftedForm
      rw [hDl z E₁ m₁ E₂ m₂, smul_add]
      abel
  have hτF : ∀ E ∈ finiteSupportComplexForms L k 0, IsFinitelySupportedForm (shiftedForm U E) :=
    fun E h => ⟨Submodule.add_mem _ h.1 (hDm E h),
      Set.Finite.subset (Set.Finite.union (hF E h).2 (hDf E h))
        (Function.support_add (restrictToPositiveEdges E)
          (restrictToPositiveEdges (covDiff U (gaugeParam U E))))⟩
  have R₃ : IsFinitelySupportedBilinearOn (finiteSupportComplexForms L k 0)
      fun B B' => restrictToPositiveEdges (levelBracketTerm U (gaugeParam U B) B') :=
    { finite := fun E₁ _ E₂ m₂ => levelBracketTerm_hasFiniteSupp U _ (hF E₂ m₂).2
      add_left := fun z E₁ m₁ E₂ m₂ E₃ _ => by
        show restrictToPositiveEdges (levelBracketTerm U (gaugeParam U (z • E₁ + E₂)) E₃) = _
        rw [hσl z E₁ m₁ E₂ m₂, levelBracketTerm_add_smul_left]
      add_right := fun z E₁ _ E₂ _ E₃ _ => levelBracketTerm_add_smul_right U _ z E₁ E₂ }
  have R₄ : IsFinitelySupportedBilinearOn (finiteSupportComplexForms L k 0)
      fun B B' => restrictToPositiveEdges (levelBracketTerm U (gaugeParam U B)
        (covDiff U (gaugeParam U B'))) :=
    { finite := fun E₁ _ E₂ m₂ => levelBracketTerm_hasFiniteSupp U _ (hDf E₂ m₂)
      add_left := fun z E₁ m₁ E₂ m₂ E₃ _ => by
        show restrictToPositiveEdges (levelBracketTerm U (gaugeParam U (z • E₁ + E₂)) _) = _
        rw [hσl z E₁ m₁ E₂ m₂, levelBracketTerm_add_smul_left]
      add_right := fun z E₁ m₁ E₂ m₂ E₃ _ => by
        show restrictToPositiveEdges (levelBracketTerm U _
          (covDiff U (gaugeParam U (z • E₁ + E₂)))) = _
        rw [hDl z E₁ m₁ E₂ m₂, levelBracketTerm_add_smul_right] }
  have R₅ : IsFinitelySupportedBilinearOn (finiteSupportComplexForms L k 0)
      fun B B' => complexQuadraticTerm L k U (shiftedForm U B) (shiftedForm U B') :=
    { finite := fun E₁ m₁ E₂ m₂ => hR.quadraticTerm_finiteSupp _ _ (hτF E₁ m₁) (hτF E₂ m₂)
      add_left := fun z E₁ m₁ E₂ m₂ E₃ m₃ => by
        show complexQuadraticTerm L k U (shiftedForm U (z • E₁ + E₂)) _ = _
        rw [hτl z E₁ m₁ E₂ m₂,
          complexQuadraticTerm_add_smul_left U z (hτF E₁ m₁) (hτF E₂ m₂) (hτF E₃ m₃)]
      add_right := fun z E₁ m₁ E₂ m₂ E₃ m₃ => by
        show complexQuadraticTerm L k U _ (shiftedForm U (z • E₁ + E₂)) = _
        rw [hτl z E₁ m₁ E₂ m₂,
          complexQuadraticTerm_add_smul_right U z (hτF E₁ m₁) (hτF E₂ m₂) (hτF E₃ m₃)] }
  exact (hA'.add hG).add ((((traceFinsumPairing_bilinear (restrictToPositiveEdges J) R₃).const_mul
    2).add (traceFinsumPairing_bilinear (restrictToPositiveEdges J) R₄)).sub
    (traceFinsumPairing_bilinear (restrictToPositiveEdges μ) R₅))
theorem hessianKernelWellDefined_of_bilinear (h₇ : SymmetricKernels.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (U J : Edge L k 0 → ComplexMatrix2)
    (μ : Edge L k k → ComplexMatrix2)
    (hβ : IsComplexBilinearOn (finiteSupportComplexForms L k 0) (hessianBilinear U J μ)) :
    HessianKernelWellDefined U J μ := by
  classical
  have hb : IsFaithfulEvaluation (edgePauliCoordinates L k 0) :=
    orientedPauliBasis_isFaithful (edgePairedSpace_isOriented (meshAt_pos hL k 0))
  have hφ : ∀ e, formOfCoeffsLinear hb e ∈ finiteSupportComplexForms L k 0 := by
    intro e
    refine ⟨hb.mem e.1, hasFiniteEdgeSupport_of_restrict ?_⟩
    exact (hb.finite_iff e.1).2 e.2
  set β := toBilinearMap (formOfCoeffsLinear hb) (finiteSupportComplexForms L k 0) hφ
    (hessianBilinear U J μ) hβ with hβdef
  have hβval : ∀ e e', β e e' = hessianBilinear U J μ (formOfCoeffsLinear hb e)
      (formOfCoeffsLinear hb e') := fun _ _ => rfl
  have hquad := (h₇.1 _ (fun _ => (1 : ℝ)) (fun _ => one_pos) β).2
  have hY : rawHessianKernel U J μ = bilinKernel (fun _ => (1 : ℝ)) β := by
    funext p p'
    show hessianBilinear U J μ _ _ = _
    unfold bilinKernel
    rw [hβval]
    simp only [inv_one, Complex.ofReal_one, one_mul]
    show _ = hessianBilinear U J μ ((edgePauliCoordinates L k 0).ofCoeffs _)
      ((edgePauliCoordinates L k 0).ofCoeffs _)
    rw [ofCoeffs_basisFunction, ofCoeffs_basisFunction]
  have hsym : symmHessianKernel U J μ =
      (1 / 2 : ℂ) • (bilinKernel (fun _ => (1 : ℝ)) β +
        wTranspose (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
          (bilinKernel (fun _ => (1 : ℝ)) β)) := by
    unfold symmHessianKernel
    rw [hY]
    congr 2
    funext p p'
    simp [wTranspose, swapKernel]
  have hbk : IsHessianKernel U J μ (symmHessianKernel U J μ) := by
    rw [hsym]
    refine ⟨hquad.2.1.1, fun B hB hf => ?_⟩
    have hc : (Function.support ((edgePauliCoordinates L k 0).coeffs B)).Finite := by
      have e := (hb.finite_iff ((edgePauliCoordinates L k 0).coeffs B)).1
      rw [hb.ofCoeffs_coeffs B hB] at e
      exact e hf
    refine (hquad.2.1.2 ⟨_, hc⟩).trans ?_
    rw [hβval]
    show hessianBilinear U J μ
      ((edgePauliCoordinates L k 0).ofCoeffs ((edgePauliCoordinates L k 0).coeffs B))
      ((edgePauliCoordinates L k 0).ofCoeffs ((edgePauliCoordinates L k 0).coeffs B)) = _
    rw [hb.ofCoeffs_coeffs B hB]
    rfl
  have huniq : ∀ X, IsHessianKernel U J μ X → X = symmHessianKernel U J μ := by
    intro X hX
    rw [hsym]
    refine hquad.1.unique ⟨hX.1, fun f => ?_⟩ hquad.2.1
    have hf : HasFiniteSupp (restrictToPositiveEdges ((edgePauliCoordinates L k 0).ofCoeffs f.1)) :=
      (hb.finite_iff f.1).2 f.2
    have e := hX.2 _ (hb.mem f.1) hf
    have e₀ : (edgePauliCoordinates L k 0).coeffs ((edgePauliCoordinates L k 0).ofCoeffs f.1) = f.1 :=
      hb.coeffs_ofCoeffs f.1
    rw [e₀] at e
    exact e
  exact ⟨hβ, fun _ _ => rfl, hbk, huniq,
    huniq _ (Classical.epsilon_spec (p := IsHessianKernel U J μ) ⟨_, hbk⟩)⟩
theorem covLaplacianWellDefined_of_kernels (h₁ : RowFiniteKernels.Claim)
    (h₃ : ThreeMapKernels.Claim)
    (h₄ : CovariantStepComplexLinear)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) : CovLaplacianWellDefined U := by
  have hs₀ : IsFaithfulEvaluation (vertexCoordinate (Vertex L k 0)) := vertexCoordinate_isFaithful _
  have hb : IsFaithfulEvaluation (edgePauliCoordinates L k 0) :=
    orientedPauliBasis_isFaithful (edgePairedSpace_isOriented (meshAt_pos hL k 0))
  have hUc : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup := hU.1
  have HD := (h₃ L hL k hk).2.2.1 U hUc
  have hUs : U ∈ smallComplexFields L k 0 := hU.2 0 (by omega)
  have hDmaps : ∀ f ∈ (vertexCoordinate (Vertex L k 0)).space.complexSubmodule,
      covDiff U f ∈ (edgePauliCoordinates L k 0).space.complexSubmodule := fun f hf =>
    ((h₄ L hL k 0 (by omega) U hUs).2.2.1 f fun x => hf x (mem_univ x)).1
  have hrows : RowFinite (covDiffKernel L k 0 U) := HD.row_finite
  have hrowsT : RowFinite (swapKernel (covDiffKernel L k 0 U)) := HD.column_finite
  obtain ⟨-, hTS⟩ := h₁.1 _ _ (covDiffKernel L k 0 U) hrows
  obtain ⟨hform, -, hact⟩ := hTS _ _ hrowsT
  refine ⟨fun p' p => hform p' p, fun f => ?_⟩
  obtain ⟨a₁, -, a₃⟩ := hact f
  refine ⟨a₁, ?_⟩
  have g : applyKernel (covDiffKernel L k 0 U) f = (edgePauliCoordinates L k 0).coeffs
      (covDiff U ((vertexCoordinate (Vertex L k 0)).ofCoeffs f)) := (HD.represents f).2
  rw [a₃, g]
  have m := hDmaps _ (hs₀.mem f)
  have e := (HD.swap_represents ((edgePauliCoordinates L k 0).coeffs
    (covDiff U ((vertexCoordinate (Vertex L k 0)).ofCoeffs f)))).2
  refine e.trans ?_
  show (vertexCoordinate (Vertex L k 0)).coeffs (PairedFunctionSpace.transposeOfValues _ _ _
    ((edgePauliCoordinates L k 0).ofCoeffs ((edgePauliCoordinates L k 0).coeffs
      (covDiff U ((vertexCoordinate (Vertex L k 0)).ofCoeffs f))))) = _
  rw [hb.ofCoeffs_coeffs _ m]
  rfl
end AtAField
theorem hessianKernelAndLaplacianExist_holds (h₁ : RowFiniteKernels.Claim)
    (h₃ : ThreeMapKernels.Claim)
    (h₄ : CovariantStepComplexLinear)
    (h₆ : HessianKernel.KernelProperties)
    (h₇ : SymmetricKernels.Claim)
    (h₈ : ReadsCubes.Statement)
    (h₉ : ComplexIterChain)
    (h₀ : KernelAtZeroSources.ZeroSourceKernel) : HessianKernelAndLaplacianExist :=
  fun _ hL _ hk U hU =>
    ⟨fun J _ μ _ => hessianKernelWellDefined_of_bilinear h₇ hL U J μ
      (hessianBilinear_isComplexBilinearOn h₃ h₄ h₆ h₈ h₉ h₀ hL hk hU J μ),
    covLaplacianWellDefined_of_kernels h₁ h₃ h₄ hL hk hU⟩
end YangMills.Construction.Tower.FullSpace.HessianLaplacian
end
