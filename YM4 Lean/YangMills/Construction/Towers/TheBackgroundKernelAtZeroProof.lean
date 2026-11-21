import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.RunningCouplingSlope.NormsOfThePlainProductsProof
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinity
import YangMills.Construction.Towers.RelationsOfTheCovariantIteratesOfTheWholeLattice
import YangMills.Construction.Towers.TheBackgroundKernelAtZero
import YangMills.Construction.Towers.TransposesOfTheCovariantDifferenceAndOfTheDifferencesProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.KernelAtZeroSources
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.SymmetricKernels
section KernelActions
variable {N N' : Type}
theorem applyKernel_add {T : KernelMatrix N N'} (hT : RowFinite T) (f g : N → ℂ) :
    applyKernel T (f + g) = applyKernel T f + applyKernel T g := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applyKernel_add <;> assumption
theorem applyKernel_smul (T : KernelMatrix N N') (z : ℂ) (f : N → ℂ) :
    applyKernel T (z • f) = z • applyKernel T f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applyKernel_smul <;> assumption
end KernelActions
section PauliCoefficients
theorem pauliCombination_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
end PauliCoefficients
structure IsFaithfulEvaluation (r : PauliComponentsOfSymmetricKernel) : Prop where
  ofCoeffs_mem : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule
  coeffs_ofCoeffs : ∀ c, r.coeffs (r.ofCoeffs c) = c
  ofCoeffs_coeffs : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f
  ofCoeffs_add : ∀ c c', r.ofCoeffs (c + c') = r.ofCoeffs c + r.ofCoeffs c'
  ofCoeffs_smul : ∀ (z : ℂ) c, r.ofCoeffs (z • c) = z • r.ofCoeffs c
  finite_iff : ∀ c, r.space.IsFinitelySupported (r.ofCoeffs c) ↔ (Function.support c).Finite
  pair_eq : ∀ a b, (Function.support b).Finite →
    r.space.pair (r.ofCoeffs a) (r.ofCoeffs b) = ∑ᶠ i, a i * b i
namespace IsFaithfulEvaluation
variable {r : PauliComponentsOfSymmetricKernel}
theorem coeffs_add (h : IsFaithfulEvaluation r) {f g : r.space.index → ComplexMatrix2}
    (hf : f ∈ r.space.complexSubmodule) (hg : g ∈ r.space.complexSubmodule) :
    r.coeffs (f + g) = r.coeffs f + r.coeffs g := by
  have hsum : f + g = r.ofCoeffs (r.coeffs f + r.coeffs g) := by
    rw [h.ofCoeffs_add, h.ofCoeffs_coeffs f hf, h.ofCoeffs_coeffs g hg]
  conv_lhs => rw [hsum, h.coeffs_ofCoeffs]
theorem coeffs_smul (h : IsFaithfulEvaluation r) (z : ℂ) {f : r.space.index → ComplexMatrix2}
    (hf : f ∈ r.space.complexSubmodule) : r.coeffs (z • f) = z • r.coeffs f := by
  have hsmul : z • f = r.ofCoeffs (z • r.coeffs f) := by
    rw [h.ofCoeffs_smul, h.ofCoeffs_coeffs f hf]
  conv_lhs => rw [hsmul, h.coeffs_ofCoeffs]
end IsFaithfulEvaluation
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
    traceFinsumPairing (ofPauliCoeffs a) (ofPauliCoeffs b) = ∑ᶠ p, a p * b p := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.traceFinsumPairing_ofPauliCoeffs <;> assumption
theorem vertexCoordinate_faithful (hP : OneLoop.PauliMatrixRelations) (σ : Type) :
    IsFaithfulEvaluation (vertexCoordinate σ) where
  ofCoeffs_mem c := fun i _ => ofPauliCoeffs_mem c i
  coeffs_ofCoeffs c := toPauliCoeffs_ofPauliCoeffs c
  ofCoeffs_coeffs _ hf := funext fun i => pauliCombination_pauliCoeff (hf i (mem_univ i))
  ofCoeffs_add c c' := ofPauliCoeffs_add c c'
  ofCoeffs_smul z c := ofPauliCoeffs_smul z c
  finite_iff c := hasFiniteSupp_ofPauliCoeffs_iff c
  pair_eq a b hb := traceFinsumPairing_ofPauliCoeffs hP a b hb
end Vertices
section OrientedFrames
variable (S : PairedFunctionSpace) (pos : S.index → Prop) (flip : S.index → S.index)
def oddExtension (f : S.index → ComplexMatrix2) : S.index → ComplexMatrix2 :=
  open Classical in fun b => if pos b then f b else -f (flip b)
def zeroExtendCoeffs (c : Fin 3 × {b : S.index // pos b} → ℂ) : S.index → ComplexMatrix2 :=
  open Classical in fun b => if h : pos b then ofPauliCoeffs c ⟨b, h⟩ else 0
def coeffForm (c : Fin 3 × {b : S.index // pos b} → ℂ) : S.index → ComplexMatrix2 :=
  oddExtension S pos flip (zeroExtendCoeffs S pos c)
def positiveValues (B : S.index → ComplexMatrix2) : {b : S.index // pos b} → ComplexMatrix2 :=
  fun b => B b.1
def positiveRepresentation : PauliComponentsOfSymmetricKernel where
  space := S
  Place := {b : S.index // pos b}
  ofCoeffs := coeffForm S pos flip
  coeffs := fun B => toPauliCoeffs (positiveValues S pos B)
structure IsOrientedFrame : Prop where
  xor_pos : ∀ b, Xor (pos b) (pos (flip b))
  flip_flip : ∀ b, flip (flip b) = b
  mem_iff : ∀ B, B ∈ S.complexSubmodule ↔
    (∀ b, pos b → B b ∈ ComplexMatrix2.traceless) ∧ ∀ b, B (flip b) = -B b
  finite_iff : ∀ B, S.IsFinitelySupported B ↔ HasFiniteSupp (positiveValues S pos B)
  pair_eq : ∀ B B', S.pair B B' =
    traceFinsumPairing (positiveValues S pos B) (positiveValues S pos B')
variable {S pos flip}
theorem oddExtension_of_pos {f : S.index → ComplexMatrix2} {b : S.index} (h : pos b) :
    oddExtension S pos flip f b = f b := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_pos <;> assumption
theorem oddExtension_of_not_pos {f : S.index → ComplexMatrix2} {b : S.index} (h : ¬ pos b) :
    oddExtension S pos flip f b = -f (flip b) := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_neg <;> assumption
theorem oddExtension_flip (hF : IsOrientedFrame S pos flip) (f : S.index → ComplexMatrix2)
    (b : S.index) : oddExtension S pos flip f (flip b) = -oddExtension S pos flip f b := by
  rcases hF.xor_pos b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [oddExtension_of_not_pos h₂, oddExtension_of_pos h₁, hF.flip_flip]
  · rw [oddExtension_of_pos h₁, oddExtension_of_not_pos h₂, neg_neg]
theorem oddExtension_add (f g : S.index → ComplexMatrix2) :
    oddExtension S pos flip (f + g) = oddExtension S pos flip f + oddExtension S pos flip g := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_add <;> assumption
theorem oddExtension_smul (z : ℂ) (f : S.index → ComplexMatrix2) :
    oddExtension S pos flip (z • f) = z • oddExtension S pos flip f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_smul <;> assumption
theorem coeffForm_apply_of_pos (c : Fin 3 × {b : S.index // pos b} → ℂ) (b : S.index)
    (hb : pos b) : coeffForm S pos flip c b = ofPauliCoeffs c ⟨b, hb⟩ := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_apply <;> assumption
theorem positiveValues_coeffForm (c : Fin 3 × {b : S.index // pos b} → ℂ) :
    positiveValues S pos (coeffForm S pos flip c) = ofPauliCoeffs c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.positivePart_formOfCoeffs <;> assumption
theorem coeffForm_add (c c' : Fin 3 × {b : S.index // pos b} → ℂ) :
    coeffForm S pos flip (c + c') = coeffForm S pos flip c + coeffForm S pos flip c' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_add <;> assumption
theorem coeffForm_smul (z : ℂ) (c : Fin 3 × {b : S.index // pos b} → ℂ) :
    coeffForm S pos flip (z • c) = z • coeffForm S pos flip c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_smul <;> assumption
theorem coeffForm_toPauliCoeffs (hF : IsOrientedFrame S pos flip) {f : S.index → ComplexMatrix2}
    (h₁ : ∀ b, pos b → f b ∈ ComplexMatrix2.traceless) (h₂ : ∀ b, f (flip b) = -f b) :
    coeffForm S pos flip (toPauliCoeffs (positiveValues S pos f)) = f := by
  have hpos : ∀ b (hb : pos b),
      coeffForm S pos flip (toPauliCoeffs (positiveValues S pos f)) b = f b := fun b hb =>
    (coeffForm_apply_of_pos _ b hb).trans (pauliCombination_pauliCoeff (h₁ b hb))
  funext b
  by_cases hb : pos b
  · exact hpos b hb
  · have hfb : pos (flip b) := by
      rcases hF.xor_pos b with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd h hb
      · exact h
    have hneg : coeffForm S pos flip (toPauliCoeffs (positiveValues S pos f)) b =
        -zeroExtendCoeffs S pos (toPauliCoeffs (positiveValues S pos f)) (flip b) :=
      oddExtension_of_not_pos hb
    have hval : zeroExtendCoeffs S pos (toPauliCoeffs (positiveValues S pos f)) (flip b) =
        f (flip b) := by
      rw [← hpos _ hfb]
      exact (oddExtension_of_pos hfb).symm
    rw [hneg, hval, h₂, neg_neg]
theorem positiveRepresentation_faithful (hP : OneLoop.PauliMatrixRelations)
    (hF : IsOrientedFrame S pos flip) : IsFaithfulEvaluation (positiveRepresentation S pos flip) where
  ofCoeffs_mem c := (hF.mem_iff _).2 ⟨fun b hb => by
    have hmem : coeffForm S pos flip c b ∈ ComplexMatrix2.traceless := by
      rw [coeffForm_apply_of_pos c b hb]
      exact ofPauliCoeffs_mem c _
    exact hmem, fun b => oddExtension_flip hF _ b⟩
  coeffs_ofCoeffs c := (congrArg toPauliCoeffs (positiveValues_coeffForm c)).trans
    (toPauliCoeffs_ofPauliCoeffs c)
  ofCoeffs_coeffs f hf :=
    coeffForm_toPauliCoeffs hF ((hF.mem_iff f).1 hf).1 ((hF.mem_iff f).1 hf).2
  ofCoeffs_add c c' := coeffForm_add c c'
  ofCoeffs_smul z c := coeffForm_smul z c
  finite_iff c := by
    refine (hF.finite_iff _).trans ?_
    have hv : positiveValues S pos ((positiveRepresentation S pos flip).ofCoeffs c) = ofPauliCoeffs c :=
      positiveValues_coeffForm c
    rw [hv]
    exact hasFiniteSupp_ofPauliCoeffs_iff c
  pair_eq a b hb := by
    refine (hF.pair_eq _ _).trans ?_
    have ha' : positiveValues S pos ((positiveRepresentation S pos flip).ofCoeffs a) = ofPauliCoeffs a :=
      positiveValues_coeffForm a
    have hb' : positiveValues S pos ((positiveRepresentation S pos flip).ofCoeffs b) = ofPauliCoeffs b :=
      positiveValues_coeffForm b
    rw [ha', hb']
    exact traceFinsumPairing_ofPauliCoeffs hP a b hb
end OrientedFrames
section Lattice
variable {L : ℕ}
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem edgePairedSpace_isOrientedFrame {a : ℝ} (ha : 0 < a) :
    IsOrientedFrame (edgePairedSpace a) (fun b => b.IsPositivelyOriented)
      InfiniteLattice.Link.opposite where
  xor_pos b := by
    rcases InfiniteLattice.xor_mem_positiveLinks ha b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
    · exact Or.inr ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
  flip_flip _ := rfl
  mem_iff _ := Iff.rfl
  finite_iff _ := Iff.rfl
  pair_eq _ _ := rfl
end Lattice
section KernelsAndPairings
theorem finite_support_applyKernel_swap {N N' : Type} {K : KernelMatrix N N'} (hK : RowFinite K)
    {c : N' → ℂ} (hc : (Function.support c).Finite) :
    (Function.support (applyKernel (swapKernel K) c)).Finite := by
  refine (hc.biUnion fun j _ => hK j).subset fun i hi => ?_
  by_contra hn
  apply hi
  have hterm : ∀ j, swapKernel K i j * c j = 0 := by
    intro j
    by_cases hzero : c j = 0
    · rw [hzero, mul_zero]
    · have hK0 : K j i = 0 := by
        by_contra hK0
        exact hn (mem_biUnion (show j ∈ Function.support c from hzero) hK0)
      show K j i * c j = 0
      rw [hK0, zero_mul]
  simp only [applyKernel, hterm, tsum_zero]
variable {ι : Type}
theorem traceFinsumPairing_smul_add_left (z : ℂ) (f g : ι → ComplexMatrix2)
    {h : ι → ComplexMatrix2} (hh : HasFiniteSupp h) :
    traceFinsumPairing (z • f + g) h =
      z * traceFinsumPairing f h + traceFinsumPairing g h := by
  have hh' : (Function.support h).Finite := hh
  have hsub : ∀ u : ι → ComplexMatrix2,
      Function.support (fun i => ComplexMatrix2.halfTrace (u i * h i)) ⊆ ↑hh'.toFinset := by
    intro u i hi
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    intro hzero
    apply hi
    simp [hzero]
  unfold traceFinsumPairing
  rw [finsum_eq_sum_of_support_subset _ (hsub _), finsum_eq_sum_of_support_subset _ (hsub _),
    finsum_eq_sum_of_support_subset _ (hsub _), Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have htr : Matrix.trace ((z • f i + g i) * h i) =
      z * Matrix.trace (f i * h i) + Matrix.trace (g i * h i) := by
    rw [add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  show (1 / 2 : ℂ) * Matrix.trace ((z • f i + g i) * h i) =
    z * ((1 / 2 : ℂ) * Matrix.trace (f i * h i)) + (1 / 2 : ℂ) * Matrix.trace (g i * h i)
  rw [htr]
  ring
theorem traceFinsumPairing_comm (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f g = traceFinsumPairing g f := by
  unfold traceFinsumPairing
  refine finsum_congr fun i => ?_
  show (1 / 2 : ℂ) * Matrix.trace (f i * g i) = (1 / 2 : ℂ) * Matrix.trace (g i * f i)
  rw [Matrix.trace_mul_comm]
theorem traceFinsumPairing_smul_add_right (z : ℂ) (f g : ι → ComplexMatrix2)
    {h : ι → ComplexMatrix2} (hh : HasFiniteSupp h) :
    traceFinsumPairing h (z • f + g) =
      z * traceFinsumPairing h f + traceFinsumPairing h g := by
  rw [traceFinsumPairing_comm, traceFinsumPairing_smul_add_left z f g hh,
    traceFinsumPairing_comm f, traceFinsumPairing_comm g]
theorem real_smul_eq_ofReal_smul (r : ℝ) (f : ι → ComplexMatrix2) : r • f = (r : ℂ) • f := by apply _root_.YangMills.SharedProofs.p7664 <;> assumption
theorem hasFiniteSupp_sub_smul (r : ℝ) {f g : ι → ComplexMatrix2} (hf : HasFiniteSupp f)
    (hg : HasFiniteSupp g) : HasFiniteSupp (f - r • g) := by
  refine (hf.union hg).subset fun i hi => ?_
  by_contra hn
  have h₁ : f i = 0 := by
    by_contra h
    exact hn (Or.inl h)
  have h₂ : g i = 0 := by
    by_contra h
    exact hn (Or.inr h)
  apply hi
  simp [h₁, h₂]
end KernelsAndPairings
section Transposes
variable {r r' : PauliComponentsOfSymmetricKernel}
theorem transposeExists_of_localKernel (hT : RowFiniteKernels.TransposeDuality)
    (hr : IsFaithfulEvaluation r) (hr' : IsFaithfulEvaluation r')
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hmaps : ∀ f ∈ r.space.complexSubmodule, m f ∈ r'.space.complexSubmodule)
    (H : PauliComponentsOfSymmetricKernel.HasLocalKernel r r' m) :
    TransposeExists r.space r'.space m := by
  classical
  have hK := H.represents
  have hrows := H.row_finite
  have hcols := H.column_finite
  set K := PauliComponentsOfSymmetricKernel.kernel r r' m with hKdef
  have hrowsT : RowFinite (swapKernel K) := hcols
  have hM : ∀ f ∈ r.space.complexSubmodule, applyKernel K (r.coeffs f) = r'.coeffs (m f) := by
    intro f hf
    have hrep := (hK (r.coeffs f)).2
    rw [hrep]
    show r'.coeffs (m (r.ofCoeffs (r.coeffs f))) = _
    rw [hr.ofCoeffs_coeffs f hf]
  have hm_eq : ∀ f ∈ r.space.complexSubmodule, m f = r'.ofCoeffs (applyKernel K (r.coeffs f)) := by
    intro f hf
    rw [hM f hf, hr'.ofCoeffs_coeffs _ (hmaps f hf)]
  have hA₀ : ∃ A : r.space.complexSubmodule →ₗ[ℂ] r'.space.complexSubmodule,
      ∀ f : r.space.complexSubmodule, (A f : r'.space.index → ComplexMatrix2) = m f := by
    refine ⟨{
      toFun := fun f => ⟨m f, hmaps f f.2⟩
      map_add' := fun f g => ?_
      map_smul' := fun z f => ?_ }, fun f => rfl⟩
    · apply Subtype.ext
      show m (f.1 + g.1) = m f.1 + m g.1
      rw [hm_eq _ (r.space.complexSubmodule.add_mem f.2 g.2), hr.coeffs_add f.2 g.2,
        applyKernel_add hrows, hr'.ofCoeffs_add, ← hm_eq _ f.2, ← hm_eq _ g.2]
    · apply Subtype.ext
      show m (z • f.1) = z • m f.1
      rw [hm_eq _ (r.space.complexSubmodule.smul_mem z f.2), hr.coeffs_smul z f.2,
        applyKernel_smul, hr'.ofCoeffs_smul, ← hm_eq _ f.2]
  have hA : ∀ f : r.space.complexSubmodule,
      (PairedFunctionSpace.linearOfValues r.space r'.space m f :
        r'.space.index → ComplexMatrix2) = m f :=
    Classical.epsilon_spec
      (p := fun T : r.space.complexSubmodule →ₗ[ℂ] r'.space.complexSubmodule =>
        ∀ f : r.space.complexSubmodule, (T f : r'.space.index → ComplexMatrix2) = m f) hA₀
  set A := PairedFunctionSpace.linearOfValues r.space r'.space m with hAdef
  let A' : r'.space.complexSubmodule →ₗ[ℂ] r.space.complexSubmodule :=
    { toFun := fun g =>
        ⟨r.ofCoeffs (applyKernel (swapKernel K) (r'.coeffs g.1)), hr.ofCoeffs_mem _⟩
      map_add' := fun g g' => by
        apply Subtype.ext
        show r.ofCoeffs (applyKernel (swapKernel K) (r'.coeffs (g.1 + g'.1))) = _
        rw [hr'.coeffs_add g.2 g'.2, applyKernel_add hrowsT, hr.ofCoeffs_add]
        rfl
      map_smul' := fun z g => by
        apply Subtype.ext
        show r.ofCoeffs (applyKernel (swapKernel K) (r'.coeffs (z • g.1))) = _
        rw [hr'.coeffs_smul z g.2, applyKernel_smul, hr.ofCoeffs_smul]
        rfl }
  have hIT : PairedFunctionSpace.IsTransposeMap A A' := by
    intro g f hf
    have hcf : (Function.support (r.coeffs f.1)).Finite := by
      have hfin := (hr.finite_iff (r.coeffs f.1)).1
      rw [hr.ofCoeffs_coeffs f.1 f.2] at hfin
      exact hfin hf
    have hcm : (Function.support (applyKernel K (r.coeffs f.1))).Finite := by
      rw [hM f.1 f.2]
      have hfin := (hr'.finite_iff (r'.coeffs (m f.1))).1
      rw [hr'.ofCoeffs_coeffs _ (hmaps f.1 f.2)] at hfin
      exact hfin (H.finitely_supported f.1 f.2 hf)
    have hleft : r.space.pair (A' g) f =
        ∑ᶠ i, applyKernel (swapKernel K) (r'.coeffs g.1) i * r.coeffs f.1 i := by
      have hp := hr.pair_eq (applyKernel (swapKernel K) (r'.coeffs g.1)) (r.coeffs f.1) hcf
      rw [hr.ofCoeffs_coeffs f.1 f.2] at hp
      exact hp
    have hright : r'.space.pair g (A f) =
        ∑ᶠ j, r'.coeffs g.1 j * applyKernel K (r.coeffs f.1) j := by
      have hp := hr'.pair_eq (r'.coeffs g.1) (applyKernel K (r.coeffs f.1)) hcm
      rw [hr'.ofCoeffs_coeffs g.1 g.2, ← hm_eq f.1 f.2, ← hA f] at hp
      exact hp
    rw [hleft, hright]
    have key := (hT r.Index r'.Index (swapKernel K) (fun _ => 1) (fun _ => 1) hrowsT
      (fun _ => one_pos) (fun _ => one_pos) (r.coeffs f.1) hcf (r'.coeffs g.1)).2.2.2.2.2
    have hswap : wTranspose (fun _ : r'.Index => (1 : ℝ)) (fun _ : r.Index => (1 : ℝ))
        (swapKernel K) = K := by
      funext j i
      simp [wTranspose, swapKernel]
    rw [hswap] at key
    simp only [Complex.ofReal_one, one_mul] at key
    calc _ = ∑ᶠ i, r.coeffs f.1 i * applyKernel (swapKernel K) (r'.coeffs g.1) i :=
          finsum_congr fun i => mul_comm _ _
      _ = ∑ᶠ j, applyKernel K (r.coeffs f.1) j * r'.coeffs g.1 j := key.symm
      _ = _ := finsum_congr fun i => mul_comm _ _
  refine ⟨hA, ?_, Classical.epsilon_spec (p := PairedFunctionSpace.IsTransposeMap A) ⟨A', hIT⟩⟩
  intro f hf
  have hfin := H.finitely_supported f.1 f.2 hf
  rw [← hA f] at hfin
  exact hfin
theorem transposeOfValues_val (S S' : PairedFunctionSpace)
    (m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2) (g : S'.complexSubmodule) :
    PairedFunctionSpace.transposeOfValues S S' m g.1 =
      (PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues S S' m) g).1 := by
  unfold PairedFunctionSpace.transposeOfValues
  rw [dif_pos g.2]
theorem transposeOfValues_mem (S S' : PairedFunctionSpace)
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
    have hfin := (hr'.finite_iff (r'.coeffs g)).1
    rw [hr'.ofCoeffs_coeffs g hg] at hfin
    exact hfin hfs
  have hval : r.coeffs (PairedFunctionSpace.transposeOfValues r.space r'.space m g) =
      applyKernel (swapKernel (PauliComponentsOfSymmetricKernel.kernel r r' m)) (r'.coeffs g) := by
    have hrep := (H.swap_represents (r'.coeffs g)).2
    rw [hrep]
    show _ = r.coeffs (PairedFunctionSpace.transposeOfValues r.space r'.space m
      (r'.ofCoeffs (r'.coeffs g)))
    rw [hr'.ofCoeffs_coeffs g hg]
  have hs := finite_support_applyKernel_swap H.row_finite hc
  rw [← hval] at hs
  have hfin := (hr.finite_iff _).2 hs
  rwa [hr.ofCoeffs_coeffs _ (transposeOfValues_mem r.space r'.space m hg)] at hfin
end Transposes
section GaugeFixing
variable {L k : ℕ}
def gaugeFixingLinear (L k : ℕ) (U : Edge L k 0 → ComplexMatrix2) :
    (edgePairedSpace (meshAt L k 0)).complexSubmodule →ₗ[ℂ]
      (pairedFunctions (Vertex L k 0)).complexSubmodule :=
  PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues
      (pairedFunctions (Vertex L k 0)) (edgePairedSpace (meshAt L k 0)) (covDiff U)) -
    ((((L : ℝ) ^ (4 * k) : ℝ)) : ℂ) •
      ((PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues
          (pairedFunctions (Vertex L k 0)) (pairedFunctions (Vertex L k k))
          (iterAdjointCubeAverage L k U k))).comp
        ((PairedFunctionSpace.linearOfValues (pairedFunctions (Vertex L k 0))
          (pairedFunctions (Vertex L k k)) (iterAdjointCubeAverage L k U k)).comp
          (PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues
            (pairedFunctions (Vertex L k 0)) (edgePairedSpace (meshAt L k 0)) (covDiff U)))))
theorem gaugeFixingLinear_apply_val {U : Edge L k 0 → ComplexMatrix2}
    (hA : ∀ f : (pairedFunctions (Vertex L k 0)).complexSubmodule,
      (PairedFunctionSpace.linearOfValues (pairedFunctions (Vertex L k 0))
        (pairedFunctions (Vertex L k k)) (iterAdjointCubeAverage L k U k) f).1 =
          iterAdjointCubeAverage L k U k f.1)
    (B : (edgePairedSpace (meshAt L k 0)).complexSubmodule) :
    (gaugeFixingLinear L k U B).1 = gaugeFixingTerm L k U B.1 := by
  set D := PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues
    (pairedFunctions (Vertex L k 0)) (edgePairedSpace (meshAt L k 0)) (covDiff U)) with hD
  set A := PairedFunctionSpace.linearOfValues (pairedFunctions (Vertex L k 0))
    (pairedFunctions (Vertex L k k)) (iterAdjointCubeAverage L k U k) with hAdef
  have h₁ : covDiffTranspose L k U B.1 = (D B).1 :=
    transposeOfValues_val _ _ _ B
  have h₂ : iterAdjointCubeAverage L k U k (D B).1 = (A (D B)).1 := (hA _).symm
  have h₃ : iterAverageTranspose L k U (A (D B)).1 =
      (PairedFunctionSpace.transposeMap A (A (D B))).1 :=
    transposeOfValues_val _ _ _ (A (D B))
  unfold gaugeFixingTerm
  rw [h₁, h₂, h₃]
  have h₄ := real_smul_eq_ofReal_smul ((L : ℝ) ^ (4 * k))
    ((PairedFunctionSpace.transposeMap A (A (D B))).1 : Vertex L k 0 → ComplexMatrix2)
  refine Eq.trans ?_ (congrArg (Sub.sub (α := Vertex L k 0 → ComplexMatrix2) (D B).1) h₄.symm)
  rfl
end GaugeFixing
section PullbackBilinear
open YangMills.Construction.Tower.HessianKernel
variable {α E : Type} [AddCommGroup E] [Module ℂ E]
theorem symmBilinearOn_zero_left {𝒮 : Set (α → ComplexMatrix2)}
    {Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ}
    (hQ : IsSymmBilinearOn 𝒮 Q) (h0 : (0 : α → ComplexMatrix2) ∈ 𝒮)
    {x : α → ComplexMatrix2} (hx : x ∈ 𝒮) : Q 0 x = 0 := by
  have hlin := (hQ 1 0 h0 0 h0 x hx).1
  simp only [one_smul, add_zero, one_mul] at hlin
  have hdouble : Q 0 x + Q 0 x = Q 0 x := hlin.symm
  simpa using hdouble
def pullbackBilinear (φ : E →ₗ[ℂ] α → ComplexMatrix2) (𝒮 : Set (α → ComplexMatrix2))
    (hφ : ∀ e, φ e ∈ 𝒮) (Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ)
    (hQ : IsSymmBilinearOn 𝒮 Q) : E →ₗ[ℂ] E →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun e e' => Q (φ e) (φ e'))
    (fun e₁ e₂ e₃ => by
      have h := (hQ 1 (φ e₁) (hφ e₁) (φ e₂) (hφ e₂) (φ e₃) (hφ e₃)).1
      simpa using h)
    (fun z e₁ e₃ => by
      have h0 : (0 : α → ComplexMatrix2) ∈ 𝒮 := by
        have := hφ 0
        rwa [map_zero] at this
      have h := (hQ z (φ e₁) (hφ e₁) 0 h0 (φ e₃) (hφ e₃)).1
      rw [symmBilinearOn_zero_left hQ h0 (hφ e₃), add_zero, add_zero] at h
      simpa using h)
    (fun e₁ e₂ e₃ => by
      have h := (hQ 1 (φ e₂) (hφ e₂) (φ e₃) (hφ e₃) (φ e₁) (hφ e₁)).2.1
      simpa using h)
    (fun z e₁ e₃ => by
      have h0 : (0 : α → ComplexMatrix2) ∈ 𝒮 := by
        have := hφ 0
        rwa [map_zero] at this
      have h := (hQ z (φ e₃) (hφ e₃) 0 h0 (φ e₁) (hφ e₁)).2.1
      have hzero : Q (φ e₁) 0 = 0 := by
        rw [(hQ 0 0 h0 0 h0 (φ e₁) (hφ e₁)).2.2.symm]
        exact symmBilinearOn_zero_left hQ h0 (hφ e₁)
      rw [hzero, add_zero, add_zero] at h
      simpa using h)
end PullbackBilinear
section CoefficientForms
variable {L k : ℕ}
def coeffFormLinear (hb : IsFaithfulEvaluation (edgePauliCoordinates L k 0)) :
    finsuppFunctions (Fin 3 × PositiveEdge (meshAt L k 0)) →ₗ[ℂ]
      Edge L k 0 → ComplexMatrix2 where
  toFun c := (edgePauliCoordinates L k 0).ofCoeffs c.1
  map_add' c c' := hb.ofCoeffs_add c.1 c'.1
  map_smul' z c := hb.ofCoeffs_smul z c.1
theorem ofCoeffs_basisFunction (p : Fin 3 × PositiveEdge (meshAt L k 0)) :
    (edgePauliCoordinates L k 0).ofCoeffs (basisFunction p).1 = basisForm p.1 p.2 := by
  classical
  unfold basisForm edgePauliCoordinates
  dsimp only
  refine congrArg (@extendOddly (meshAt L k 0)) (funext fun b => ?_)
  by_cases hb : b.IsPositivelyOriented
  · rw [dif_pos hb]
    by_cases hbp : b = p.2.1
    · have hbp' : (⟨b, hb⟩ : PositiveEdge (meshAt L k 0)) = p.2 := Subtype.ext hbp
      rw [if_pos hbp, hbp']
      unfold ofPauliCoeffs
      rw [Finset.sum_eq_single p.1]
      · have : (basisFunction p).1 (p.1, p.2) = 1 := if_pos rfl
        rw [this, one_smul]
      · intro a _ ha
        have : (basisFunction p).1 (a, p.2) = 0 :=
          if_neg fun h => ha (Prod.ext_iff.1 h).1
        rw [this, zero_smul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [if_neg hbp]
      unfold ofPauliCoeffs
      refine Finset.sum_eq_zero fun a _ => ?_
      have : (basisFunction p).1 (a, ⟨b, hb⟩) = 0 :=
        if_neg fun h => hbp (congrArg Subtype.val (Prod.ext_iff.1 h).2)
      rw [this, zero_smul]
  · rw [dif_neg hb, if_neg]
    intro hbp
    exact hb (hbp ▸ p.2.2)
theorem sourceForm_zero (U B : Edge L k 0 → ComplexMatrix2) :
    sourceForm U 0 (0 : Edge L k k → ComplexMatrix2) B = 0 := by
  simp [sourceForm, finiteEdgePairing, traceFinsumPairing, restrictToPositiveEdges,
    ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
theorem hasFiniteEdgeSupport_of_restrict {B : Edge L k 0 → ComplexMatrix2}
    (h : HasFiniteSupp (restrictToPositiveEdges B)) : HasFiniteEdgeSupport B :=
  (h.image Subtype.val).subset fun b hb => ⟨⟨b, hb.1⟩, hb.2, rfl⟩
theorem restrict_hasFiniteSupp {B : Edge L k 0 → ComplexMatrix2}
    (h : HasFiniteEdgeSupport B) : HasFiniteSupp (restrictToPositiveEdges B) :=
  (h.preimage Subtype.val_injective.injOn).subset fun b hb => ⟨b.2, hb⟩
end CoefficientForms
open YangMills.Construction.Tower.HessianKernel in
theorem holdsAt_of {L k : ℕ} (h₁ : RowFiniteKernels.Claim)
    (h₂ : OneLoop.PauliMatrixRelations)
    (h₃ : ThreeMapKernels.Claim)
    (h₄ : CovariantStepComplexLinear)
    (h₅ : CovariantIterRelations)
    (h₆ : KernelProperties)
    (h₇ : SymmetricKernels.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) : HoldsAt L k U := by
  classical
  have hT := h₁.2.2.2
  have hv₀ : IsFaithfulEvaluation (vertexCoordinate (Vertex L k 0)) := vertexCoordinate_faithful h₂ _
  have hvk : IsFaithfulEvaluation (vertexCoordinate (Vertex L k k)) := vertexCoordinate_faithful h₂ _
  have hb : IsFaithfulEvaluation (edgePauliCoordinates L k 0) :=
    positiveRepresentation_faithful h₂ (edgePairedSpace_isOrientedFrame (meshAt_pos hL k 0))
  have hKer := (h₃ L hL k hk).2
  have hUc : U ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup := hU.1
  have HD := hKer.2.1 U hUc
  have HA := (hKer.2.2.2 U hU).2
  have hUs : U ∈ smallComplexFields L k 0 := hU.2 0 (by omega)
  have hDmaps : ∀ f ∈ (vertexCoordinate (Vertex L k 0)).space.complexSubmodule,
      covDiff U f ∈ (edgePauliCoordinates L k 0).space.complexSubmodule := fun f hf =>
    ((h₄ L hL k 0 (by omega) U hUs).2.2.1 f fun x => hf x (mem_univ x)).1
  obtain ⟨T, hTval, -, -⟩ := (h₅ L hL k k le_rfl U hU).2.2
  have hAmaps : ∀ f ∈ (vertexCoordinate (Vertex L k 0)).space.complexSubmodule,
      iterAdjointCubeAverage L k U k f ∈ (vertexCoordinate (Vertex L k k)).space.complexSubmodule := by
    intro f hf
    have hT₁ := hTval ⟨f, hf⟩
    have hT₂ : iterAdjointCubeAverage L k U k f = (T ⟨f, hf⟩).1 := hT₁.symm
    rw [hT₂]
    exact (T ⟨f, hf⟩).2
  have tD := transposeExists_of_localKernel hT hv₀ hb hDmaps HD
  have tA := transposeExists_of_localKernel hT hv₀ hvk hAmaps HA
  have hGval := gaugeFixingLinear_apply_val (L := L) (k := k) (U := U) tA.1
  have hGmem : ∀ B ∈ complexEdgeForms (meshAt L k 0),
      gaugeFixingTerm L k U B ∈ (pairedFunctions (Vertex L k 0)).complexSubmodule := by
    intro B hB
    have hg := hGval ⟨B, hB⟩
    have hg' : gaugeFixingTerm L k U B = (gaugeFixingLinear L k U ⟨B, hB⟩).1 := hg.symm
    rw [hg']
    exact (gaugeFixingLinear L k U ⟨B, hB⟩).2
  have hGfin : ∀ B ∈ complexEdgeForms (meshAt L k 0), HasFiniteSupp (restrictToPositiveEdges B) →
      HasFiniteSupp (gaugeFixingTerm L k U B) := by
    intro B hB hf
    have a₁ := transposeOfValues_finitelySupported hv₀ hb HD hB hf
    have m₁ := transposeOfValues_mem (vertexCoordinate (Vertex L k 0)).space
      (edgePauliCoordinates L k 0).space (covDiff U) hB
    have a₂ := HA.finitely_supported _ m₁ a₁
    have a₃ := transposeOfValues_finitelySupported hv₀ hvk HA (hAmaps _ m₁) a₂
    exact hasFiniteSupp_sub_smul _ a₁ a₃
  have hGlin : ∀ (z : ℂ), ∀ B ∈ complexEdgeForms (meshAt L k 0),
      ∀ B' ∈ complexEdgeForms (meshAt L k 0),
      gaugeFixingTerm L k U (z • B + B') =
        z • gaugeFixingTerm L k U B + gaugeFixingTerm L k U B' := by
    intro z B hB B' hB'
    let b₁ : (edgePairedSpace (meshAt L k 0)).complexSubmodule := ⟨B, hB⟩
    let b₂ : (edgePairedSpace (meshAt L k 0)).complexSubmodule := ⟨B', hB'⟩
    have g₁ := hGval (z • b₁ + b₂)
    have g₂ := hGval b₁
    have g₃ := hGval b₂
    rw [map_add, map_smul] at g₁
    have g₁' : gaugeFixingTerm L k U (z • B + B') = _ := g₁.symm
    have g₂' : gaugeFixingTerm L k U B = _ := g₂.symm
    have g₃' : gaugeFixingTerm L k U B' = _ := g₃.symm
    rw [g₁', g₂', g₃']
    rfl
  have hQ := (h₆ L hL k 0 (Nat.zero_le k)).2 U hUc |>.1
  have hP : IsSymmBilinearOn (finiteSupportComplexForms L k 0) (backgroundForm L k U) := by
    rintro z E₁ ⟨m₁, f₁⟩ E₂ ⟨m₂, f₂⟩ E₃ ⟨m₃, f₃⟩
    obtain ⟨a, b, c⟩ := hQ z E₁ ⟨m₁, f₁⟩ E₂ ⟨m₂, f₂⟩ E₃ ⟨m₃, f₃⟩
    have g₃ := hGfin E₃ m₃ (restrict_hasFiniteSupp f₃)
    refine ⟨?_, ?_, ?_⟩
    · unfold backgroundForm
      rw [a, hGlin z E₁ m₁ E₂ m₂, traceFinsumPairing_smul_add_left z _ _ g₃]
      ring
    · unfold backgroundForm
      rw [b, hGlin z E₁ m₁ E₂ m₂, traceFinsumPairing_smul_add_right z _ _ g₃]
      ring
    · unfold backgroundForm
      rw [c, traceFinsumPairing_comm]
  have hφ : ∀ e, coeffFormLinear hb e ∈ finiteSupportComplexForms L k 0 := by
    intro e
    refine ⟨hb.ofCoeffs_mem e.1, hasFiniteEdgeSupport_of_restrict ?_⟩
    exact (hb.finite_iff e.1).2 e.2
  set β := pullbackBilinear (coeffFormLinear hb) (finiteSupportComplexForms L k 0) hφ
    (backgroundForm L k U) hP with hβ
  have hβval : ∀ e e', β e e' = backgroundForm L k U (coeffFormLinear hb e)
      (coeffFormLinear hb e') := fun _ _ => rfl
  have hβsymm : ∀ e e', β e' e = β e e' := by
    intro e e'
    rw [hβval, hβval]
    have h0 : (0 : Edge L k 0 → ComplexMatrix2) ∈ finiteSupportComplexForms L k 0 := by
      have := hφ 0
      rwa [map_zero] at this
    exact (hP 0 _ (hφ e') 0 h0 _ (hφ e)).2.2
  have hker := (h₇.1 _ (fun _ => (1 : ℝ)) (fun _ => one_pos) β).1
  have hquad := (h₇.1 _ (fun _ => (1 : ℝ)) (fun _ => one_pos) β).2
  have hY : backgroundKernel L k U = bilinKernel (fun _ => (1 : ℝ)) β := by
    funext i i'
    show backgroundForm L k U _ _ = _
    unfold bilinKernel
    rw [hβval]
    simp only [inv_one, Complex.ofReal_one, one_mul]
    show _ = backgroundForm L k U ((edgePauliCoordinates L k 0).ofCoeffs _)
      ((edgePauliCoordinates L k 0).ofCoeffs _)
    rw [ofCoeffs_basisFunction, ofCoeffs_basisFunction]
  have hsymm : IsSymmKernel (fun _ => (1 : ℝ)) (backgroundKernel L k U) := by
    rw [hY]
    exact hker.2.2.2.2 hβsymm
  have hquadY : ∀ f : finsuppFunctions (Fin 3 × PositiveEdge (meshAt L k 0)),
      kernelPairing (fun _ => (1 : ℝ)) (backgroundKernel L k U) f f = β f f := by
    intro f
    rw [hY]
    exact hker.2.1 f f
  have hform : ∀ B ∈ complexEdgeForms (meshAt L k 0), hessianForm U 0 0 B =
      backgroundForm L k U B B := by
    intro B _
    unfold hessianForm
    rw [sourceForm_zero, add_zero]
  have hbk : IsHessianKernel U 0 0 (backgroundKernel L k U) := by
    refine ⟨hsymm, fun B hB hf => ?_⟩
    have hc : (Function.support ((edgePauliCoordinates L k 0).coeffs B)).Finite := by
      have hfin := (hb.finite_iff ((edgePauliCoordinates L k 0).coeffs B)).1
      rw [hb.ofCoeffs_coeffs B hB] at hfin
      exact hfin hf
    have hq := hquadY ⟨_, hc⟩
    rw [hform B hB]
    refine hq.trans ?_
    rw [hβval]
    show backgroundForm L k U ((edgePauliCoordinates L k 0).ofCoeffs ((edgePauliCoordinates L k 0).coeffs B))
      ((edgePauliCoordinates L k 0).ofCoeffs ((edgePauliCoordinates L k 0).coeffs B)) = _
    rw [hb.ofCoeffs_coeffs B hB]
  have huniq : ∀ X, IsHessianKernel U 0 0 X → X = backgroundKernel L k U := by
    intro X hX
    refine hquad.1.unique ⟨hX.1, fun f => ?_⟩ ⟨hsymm, hquadY⟩
    have hf : HasFiniteSupp (restrictToPositiveEdges ((edgePauliCoordinates L k 0).ofCoeffs f.1)) :=
      (hb.finite_iff f.1).2 f.2
    have hq := hX.2 _ (hb.ofCoeffs_mem f.1) hf
    have hc₀ : (edgePauliCoordinates L k 0).coeffs ((edgePauliCoordinates L k 0).ofCoeffs f.1) = f.1 :=
      hb.coeffs_ofCoeffs f.1
    rw [hc₀, hform _ (hb.ofCoeffs_mem f.1)] at hq
    exact hq
  refine ⟨tD, tA, hGmem, fun B hB B' hB' hf hf' => ?_, hsymm, hbk, huniq, fun ζ e₁ e₂ e₃ => ?_⟩
  · refine (hGfin B hB hf).subset fun i hi hzero => hi ?_
    have hzero' : gaugeFixingTerm L k U B i = 0 := hzero
    simp [hzero']
  · rw [e₃, e₁, e₂]
    exact huniq _ (Classical.epsilon_spec (p := IsHessianKernel U 0 0) ⟨_, hbk⟩)
open YangMills.Construction.Tower.HessianKernel in
theorem zeroSourceKernel_holds (h₁ : RowFiniteKernels.Claim)
    (h₂ : OneLoop.PauliMatrixRelations)
    (h₃ : ThreeMapKernels.Claim)
    (h₄ : CovariantStepComplexLinear)
    (h₅ : CovariantIterRelations)
    (h₆ : KernelProperties)
    (h₇ : SymmetricKernels.Claim) : ZeroSourceKernel := fun _ hL _ hk _ hU =>
  holdsAt_of h₁ h₂ h₃ h₄ h₅ h₆ h₇ hL hk hU
end YangMills.Construction.Tower.FullSpace.KernelAtZeroSources
end
