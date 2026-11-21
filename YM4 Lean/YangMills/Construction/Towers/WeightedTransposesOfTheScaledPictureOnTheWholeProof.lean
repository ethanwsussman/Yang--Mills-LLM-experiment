import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.WeightedTransposeOnFaithfulEvaluations
import YangMills.Construction.Towers.WeightedTransposesOfTheScaledPictureOnTheWhole
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Matrices
namespace Tower.WholeEvaluations
section PauliBasis
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
end PauliBasis
structure IsPauliBijection (r : PauliComponentsOfSymmetricKernel) : Prop where
  mem : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule
  left_inv : ∀ c, r.coeffs (r.ofCoeffs c) = c
  right_inv : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f
  map_add : ∀ c c', r.ofCoeffs (c + c') = r.ofCoeffs c + r.ofCoeffs c'
  map_smul : ∀ (z : ℂ) c, r.ofCoeffs (z • c) = z • r.ofCoeffs c
  finite_iff : ∀ c, r.space.IsFinitelySupported (r.ofCoeffs c) ↔ (Function.support c).Finite
  pair_eq : ∀ a b, (Function.support b).Finite →
    r.space.pair (r.ofCoeffs a) (r.ofCoeffs b) = ∑ᶠ ι, a ι * b ι
namespace IsPauliBijection
variable {r : PauliComponentsOfSymmetricKernel}
theorem coeffs_add (h : IsPauliBijection r) {f g : r.space.index → ComplexMatrix2}
    (hf : f ∈ r.space.complexSubmodule) (hg : g ∈ r.space.complexSubmodule) :
    r.coeffs (f + g) = r.coeffs f + r.coeffs g := by
  have hfg : f + g = r.ofCoeffs (r.coeffs f + r.coeffs g) := by
    rw [h.map_add, h.right_inv f hf, h.right_inv g hg]
  conv_lhs => rw [hfg, h.left_inv]
theorem coeffs_smul (h : IsPauliBijection r) (z : ℂ) {f : r.space.index → ComplexMatrix2}
    (hf : f ∈ r.space.complexSubmodule) : r.coeffs (z • f) = z • r.coeffs f := by
  have hzf : z • f = r.ofCoeffs (z • r.coeffs f) := by
    rw [h.map_smul, h.right_inv f hf]
  conv_lhs => rw [hzf, h.left_inv]
end IsPauliBijection
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
theorem traceFinsumPairing_ofPauliCoeffs (hP : OneLoop.PauliMatrixRelations)
    (a b : Fin 3 × σ → ℂ) (hb : (Function.support b).Finite) :
    traceFinsumPairing (ofPauliCoeffs a) (ofPauliCoeffs b) = ∑ᶠ ι, a ι * b ι := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.traceFinsumPairing_ofPauliCoeffs <;> assumption
theorem vertexCoordinates_isPauliBijection (hP : OneLoop.PauliMatrixRelations) (σ : Type) :
    IsPauliBijection (vertexCoordinate σ) where
  mem c := fun i _ => ofPauliCoeffs_mem c i
  left_inv c := toPauliCoeffs_ofPauliCoeffs c
  right_inv _ hf := funext fun i => sum_pauliCoeff_smul (hf i (mem_univ i))
  map_add c c' := ofPauliCoeffs_add c c'
  map_smul z c := ofPauliCoeffs_smul z c
  finite_iff c := hasFiniteSupp_ofPauliCoeffs_iff c
  pair_eq a b hb := traceFinsumPairing_ofPauliCoeffs hP a b hb
end Vertices
section OrientedFrames
variable (S : PairedFunctionSpace) (pos : S.index → Prop) (rev : S.index → S.index)
def antisymmExtend (f : S.index → ComplexMatrix2) : S.index → ComplexMatrix2 :=
  open Classical in fun b => if pos b then f b else -f (rev b)
def zeroExtendPositive (c : Fin 3 × {b : S.index // pos b} → ℂ) : S.index → ComplexMatrix2 :=
  open Classical in fun b => if h : pos b then ofPauliCoeffs c ⟨b, h⟩ else 0
def formOfCoeffs (c : Fin 3 × {b : S.index // pos b} → ℂ) : S.index → ComplexMatrix2 :=
  antisymmExtend S pos rev (zeroExtendPositive S pos c)
def restrictPositive (B : S.index → ComplexMatrix2) : {b : S.index // pos b} → ComplexMatrix2 :=
  fun b => B b.1
def orientedPauliBasis : PauliComponentsOfSymmetricKernel where
  space := S
  Place := {b : S.index // pos b}
  ofCoeffs := formOfCoeffs S pos rev
  coeffs := fun B => toPauliCoeffs (restrictPositive S pos B)
structure IsOrientedFrame : Prop where
  xor_pos : ∀ b, Xor (pos b) (pos (rev b))
  rev_rev : ∀ b, rev (rev b) = b
  mem_iff : ∀ B, B ∈ S.complexSubmodule ↔
    (∀ b, pos b → B b ∈ ComplexMatrix2.traceless) ∧ ∀ b, B (rev b) = -B b
  finitelySupported_iff : ∀ B, S.IsFinitelySupported B ↔ HasFiniteSupp (restrictPositive S pos B)
  pair_eq : ∀ B B', S.pair B B' =
    traceFinsumPairing (restrictPositive S pos B) (restrictPositive S pos B')
variable {S pos rev}
theorem antisymmExtend_of_pos {f : S.index → ComplexMatrix2} {b : S.index} (h : pos b) :
    antisymmExtend S pos rev f b = f b := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_pos <;> assumption
theorem antisymmExtend_of_not_pos {f : S.index → ComplexMatrix2} {b : S.index} (h : ¬ pos b) :
    antisymmExtend S pos rev f b = -f (rev b) := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_neg <;> assumption
theorem antisymmExtend_rev (hF : IsOrientedFrame S pos rev) (f : S.index → ComplexMatrix2)
    (b : S.index) : antisymmExtend S pos rev f (rev b) = -antisymmExtend S pos rev f b := by
  rcases hF.xor_pos b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [antisymmExtend_of_not_pos h₂, antisymmExtend_of_pos h₁, hF.rev_rev]
  · rw [antisymmExtend_of_pos h₁, antisymmExtend_of_not_pos h₂, neg_neg]
theorem antisymmExtend_add (f g : S.index → ComplexMatrix2) :
    antisymmExtend S pos rev (f + g) = antisymmExtend S pos rev f + antisymmExtend S pos rev g := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_add <;> assumption
theorem antisymmExtend_smul (z : ℂ) (f : S.index → ComplexMatrix2) :
    antisymmExtend S pos rev (z • f) = z • antisymmExtend S pos rev f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_smul <;> assumption
theorem formOfCoeffs_apply_of_pos (c : Fin 3 × {b : S.index // pos b} → ℂ) (b : S.index)
    (hb : pos b) : formOfCoeffs S pos rev c b = ofPauliCoeffs c ⟨b, hb⟩ := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_apply <;> assumption
theorem restrictPositive_formOfCoeffs (c : Fin 3 × {b : S.index // pos b} → ℂ) :
    restrictPositive S pos (formOfCoeffs S pos rev c) = ofPauliCoeffs c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.positivePart_formOfCoeffs <;> assumption
theorem formOfCoeffs_add (c c' : Fin 3 × {b : S.index // pos b} → ℂ) :
    formOfCoeffs S pos rev (c + c') = formOfCoeffs S pos rev c + formOfCoeffs S pos rev c' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_add <;> assumption
theorem formOfCoeffs_smul (z : ℂ) (c : Fin 3 × {b : S.index // pos b} → ℂ) :
    formOfCoeffs S pos rev (z • c) = z • formOfCoeffs S pos rev c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_smul <;> assumption
theorem formOfCoeffs_toPauliCoeffs (hF : IsOrientedFrame S pos rev) {f : S.index → ComplexMatrix2}
    (h₁ : ∀ b, pos b → f b ∈ ComplexMatrix2.traceless) (h₂ : ∀ b, f (rev b) = -f b) :
    formOfCoeffs S pos rev (toPauliCoeffs (restrictPositive S pos f)) = f := by
  have hpos : ∀ b (hb : pos b),
      formOfCoeffs S pos rev (toPauliCoeffs (restrictPositive S pos f)) b = f b := fun b hb =>
    (formOfCoeffs_apply_of_pos _ b hb).trans (sum_pauliCoeff_smul (h₁ b hb))
  funext b
  by_cases hb : pos b
  · exact hpos b hb
  · have hrb : pos (rev b) := by
      rcases hF.xor_pos b with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd h hb
      · exact h
    have hn : formOfCoeffs S pos rev (toPauliCoeffs (restrictPositive S pos f)) b =
        -zeroExtendPositive S pos (toPauliCoeffs (restrictPositive S pos f)) (rev b) :=
      antisymmExtend_of_not_pos hb
    have hv : zeroExtendPositive S pos (toPauliCoeffs (restrictPositive S pos f)) (rev b) =
        f (rev b) := by
      rw [← hpos _ hrb]
      exact (antisymmExtend_of_pos hrb).symm
    rw [hn, hv, h₂, neg_neg]
theorem orientedPauliBasis_isPauliBijection (hP : OneLoop.PauliMatrixRelations)
    (hF : IsOrientedFrame S pos rev) : IsPauliBijection (orientedPauliBasis S pos rev) where
  mem c := (hF.mem_iff _).2 ⟨fun b hb => by
    have hm : formOfCoeffs S pos rev c b ∈ ComplexMatrix2.traceless := by
      rw [formOfCoeffs_apply_of_pos c b hb]
      exact ofPauliCoeffs_mem c _
    exact hm, fun b => antisymmExtend_rev hF _ b⟩
  left_inv c := (congrArg toPauliCoeffs (restrictPositive_formOfCoeffs c)).trans
    (toPauliCoeffs_ofPauliCoeffs c)
  right_inv f hf :=
    formOfCoeffs_toPauliCoeffs hF ((hF.mem_iff f).1 hf).1 ((hF.mem_iff f).1 hf).2
  map_add c c' := formOfCoeffs_add c c'
  map_smul z c := formOfCoeffs_smul z c
  finite_iff c := by
    refine (hF.finitelySupported_iff _).trans ?_
    have hr : restrictPositive S pos ((orientedPauliBasis S pos rev).ofCoeffs c) = ofPauliCoeffs c :=
      restrictPositive_formOfCoeffs c
    rw [hr]
    exact hasFiniteSupp_ofPauliCoeffs_iff c
  pair_eq a b hb := by
    refine (hF.pair_eq _ _).trans ?_
    have ha' : restrictPositive S pos ((orientedPauliBasis S pos rev).ofCoeffs a) = ofPauliCoeffs a :=
      restrictPositive_formOfCoeffs a
    have hb' : restrictPositive S pos ((orientedPauliBasis S pos rev).ofCoeffs b) = ofPauliCoeffs b :=
      restrictPositive_formOfCoeffs b
    rw [ha', hb']
    exact traceFinsumPairing_ofPauliCoeffs hP a b hb
end OrientedFrames
section FullLattice
variable {L k : ℕ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem edgePairedSpace_isOrientedFrame {a : ℝ} (ha : 0 < a) :
    IsOrientedFrame (FullSpace.edgePairedSpace a) (fun b => b.IsPositivelyOriented)
      InfiniteLattice.Link.opposite where
  xor_pos b := by
    rcases InfiniteLattice.xor_mem_positiveLinks ha b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
    · exact Or.inr ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
  rev_rev _ := rfl
  mem_iff _ := Iff.rfl
  finitelySupported_iff _ := Iff.rfl
  pair_eq _ _ := rfl
theorem edgePauliCoordinates_isPauliBijection (hP : OneLoop.PauliMatrixRelations)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (j : ℕ) :
    IsPauliBijection (FullSpace.edgePauliCoordinates L k j) :=
  orientedPauliBasis_isPauliBijection hP (edgePairedSpace_isOrientedFrame (meshAt_pos hL k j))
end FullLattice
theorem IsPauliBijection.isFaithfulPauliCoordinates {r : PauliComponentsOfSymmetricKernel} (h : IsPauliBijection r) :
    FaithfulCoordinates.IsFaithfulEvaluation r where
  ofCoeffs_mem := h.mem
  coeffs_ofCoeffs := h.left_inv
  ofCoeffs_coeffs := h.right_inv
  coeffs_linear z f hf g hg := by
    rw [h.coeffs_add (r.space.complexSubmodule.smul_mem z hf) hg, h.coeffs_smul z hf]
  finitelySupported_iff f hf := by
    have hc := h.finite_iff (r.coeffs f)
    rwa [h.right_inv f hf] at hc
  pair_eq g hg f hf hfin := by
    have hs : (Function.support (r.coeffs f)).Finite := by
      have hc := h.finite_iff (r.coeffs f)
      rw [h.right_inv f hf] at hc
      exact hc.1 hfin
    have hp := h.pair_eq (r.coeffs g) (r.coeffs f) hs
    rwa [h.right_inv g hg, h.right_inv f hf] at hp
end Tower.WholeEvaluations
namespace Tower.FullSpace.MeshTransposes
open Tower.WholeEvaluations
theorem levelRestriction_isFaithful (hP : OneLoop.PauliMatrixRelations) {L : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) (i : Fin 3) :
    FaithfulCoordinates.IsFaithfulEvaluation (FullSpace.RescaledConditions.levelRestriction L k j i) :=
  match i with
  | 0 => (vertexCoordinates_isPauliBijection hP _).isFaithfulPauliCoordinates
  | 1 => (edgePauliCoordinates_isPauliBijection hP hL j).isFaithfulPauliCoordinates
  | 2 => (vertexCoordinates_isPauliBijection hP _).isFaithfulPauliCoordinates
theorem transposeScalingHolds_of (h₁ : FaithfulCoordinates.TransposeScales)
    (h₂ : OneLoop.PauliMatrixRelations) : TransposeScalingHolds := by
  intro L hL k _ i i' j j' _ _
  exact h₁ _ _ (levelRestriction_isFaithful h₂ hL k j i)
    (levelRestriction_isFaithful h₂ hL k j' i') _ _
end Tower.FullSpace.MeshTransposes
end YangMills.Construction
end
