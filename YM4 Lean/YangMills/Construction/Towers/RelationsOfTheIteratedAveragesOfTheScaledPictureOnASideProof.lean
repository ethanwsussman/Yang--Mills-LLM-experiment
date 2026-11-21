import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.RunningCouplingSlope.NormsOfThePlainProductsProof
import YangMills.Construction.Towers.BackgroundFormOfTheFunctionalOnASideProof
import YangMills.Construction.Towers.IteratesOfSmallConfigurationsAreInTheComplexGroup
import YangMills.Construction.Towers.KernelAlgebraOfTheScaledPicture
import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnASide
import YangMills.Construction.Towers.RelationsOfTheIteratedAveragesOfTheScaledPictureOnASide
import YangMills.Construction.Towers.TransposesOfTheCovariantDifferenceAndOfTheDifferencesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.IterRelationsOnTorus
open Matrices
open PeriodicOperators
open RescaledConditions
open ScalarMultipleKernels (CoeffsRealHomogeneous)
section PauliCoordinates
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
end PauliCoordinates
structure IsExactEvaluation (r : PauliComponentsOfSymmetricKernel) : Prop where
  mem_space : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule
  coeffs_ofCoeffs : ∀ c, r.coeffs (r.ofCoeffs c) = c
  ofCoeffs_coeffs : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f
  map_add : ∀ c c', r.ofCoeffs (c + c') = r.ofCoeffs c + r.ofCoeffs c'
  map_smul : ∀ (z : ℂ) c, r.ofCoeffs (z • c) = z • r.ofCoeffs c
  pair_eq : ∀ a b, (Function.support b).Finite →
    r.space.pair (r.ofCoeffs a) (r.ofCoeffs b) = ∑ᶠ ι, a ι * b ι
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
theorem traceFinsumPairing_ofPauliCoeffs (hP : OneLoop.PauliMatrixRelations)
    (a b : Fin 3 × σ → ℂ) (hb : (Function.support b).Finite) :
    traceFinsumPairing (ofPauliCoeffs a) (ofPauliCoeffs b) = ∑ᶠ ι, a ι * b ι := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.traceFinsumPairing_ofPauliCoeffs <;> assumption
theorem vertexCoordinate_exact (hP : OneLoop.PauliMatrixRelations) (σ : Type) :
    IsExactEvaluation (vertexCoordinate σ) where
  mem_space c := fun i _ => ofPauliCoeffs_mem c i
  coeffs_ofCoeffs c := toPauliCoeffs_ofPauliCoeffs c
  ofCoeffs_coeffs f hf := funext fun i => sum_pauliCoeff_smul (hf i (mem_univ i))
  map_add c c' := ofPauliCoeffs_add c c'
  map_smul z c := ofPauliCoeffs_smul z c
  pair_eq a b hb := traceFinsumPairing_ofPauliCoeffs hP a b hb
end Vertices
section OrientedSpaces
variable (S : PairedFunctionSpace) (pos : S.index → Prop) (rev : S.index → S.index)
def oddExtension (f : S.index → ComplexMatrix2) : S.index → ComplexMatrix2 :=
  open Classical in fun b => if pos b then f b else -f (rev b)
def zeroExtension (c : Fin 3 × {b : S.index // pos b} → ℂ) : S.index → ComplexMatrix2 :=
  open Classical in fun b => if h : pos b then ofPauliCoeffs c ⟨b, h⟩ else 0
def formOfCoeffs (c : Fin 3 × {b : S.index // pos b} → ℂ) : S.index → ComplexMatrix2 :=
  oddExtension S pos rev (zeroExtension S pos c)
def restrictPositive (B : S.index → ComplexMatrix2) : {b : S.index // pos b} → ComplexMatrix2 :=
  fun b => B b.1
def positiveRepresentation : PauliComponentsOfSymmetricKernel where
  space := S
  Place := {b : S.index // pos b}
  ofCoeffs := formOfCoeffs S pos rev
  coeffs := fun B => toPauliCoeffs (restrictPositive S pos B)
structure IsOrientedSpace : Prop where
  xor_pos : ∀ b, Xor (pos b) (pos (rev b))
  rev_rev_eq : ∀ b, rev (rev b) = b
  mem_complex_iff : ∀ B, B ∈ S.complexSubmodule ↔
    (∀ b, pos b → B b ∈ ComplexMatrix2.traceless) ∧ ∀ b, B (rev b) = -B b
  pair_eq_restrict : ∀ B B', S.pair B B' =
    traceFinsumPairing (restrictPositive S pos B) (restrictPositive S pos B')
variable {S pos rev}
theorem oddExtension_of_pos {f : S.index → ComplexMatrix2} {b : S.index} (h : pos b) :
    oddExtension S pos rev f b = f b := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_pos <;> assumption
theorem oddExtension_of_not_pos {f : S.index → ComplexMatrix2} {b : S.index} (h : ¬ pos b) :
    oddExtension S pos rev f b = -f (rev b) := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_neg <;> assumption
theorem oddExtension_rev (hF : IsOrientedSpace S pos rev) (f : S.index → ComplexMatrix2)
    (b : S.index) : oddExtension S pos rev f (rev b) = -oddExtension S pos rev f b := by
  rcases hF.xor_pos b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [oddExtension_of_not_pos h₂, oddExtension_of_pos h₁, hF.rev_rev_eq]
  · rw [oddExtension_of_pos h₁, oddExtension_of_not_pos h₂, neg_neg]
theorem oddExtension_add (f g : S.index → ComplexMatrix2) :
    oddExtension S pos rev (f + g) = oddExtension S pos rev f + oddExtension S pos rev g := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_add <;> assumption
theorem oddExtension_smul (z : ℂ) (f : S.index → ComplexMatrix2) :
    oddExtension S pos rev (z • f) = z • oddExtension S pos rev f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_smul <;> assumption
theorem formOfCoeffs_apply (c : Fin 3 × {b : S.index // pos b} → ℂ) (b : S.index) (hb : pos b) :
    formOfCoeffs S pos rev c b = ofPauliCoeffs c ⟨b, hb⟩ := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_apply <;> assumption
theorem restrictPositive_formOfCoeffs (c : Fin 3 × {b : S.index // pos b} → ℂ) :
    restrictPositive S pos (formOfCoeffs S pos rev c) = ofPauliCoeffs c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.positivePart_formOfCoeffs <;> assumption
theorem zeroExtension_add (c c' : Fin 3 × {b : S.index // pos b} → ℂ) :
    zeroExtension S pos (c + c') = zeroExtension S pos c + zeroExtension S pos c' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.zeroExtension_add <;> assumption
theorem zeroExtension_smul (z : ℂ) (c : Fin 3 × {b : S.index // pos b} → ℂ) :
    zeroExtension S pos (z • c) = z • zeroExtension S pos c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.zeroExtension_smul <;> assumption
theorem formOfCoeffs_add (c c' : Fin 3 × {b : S.index // pos b} → ℂ) :
    formOfCoeffs S pos rev (c + c') = formOfCoeffs S pos rev c + formOfCoeffs S pos rev c' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_add <;> assumption
theorem formOfCoeffs_smul (z : ℂ) (c : Fin 3 × {b : S.index // pos b} → ℂ) :
    formOfCoeffs S pos rev (z • c) = z • formOfCoeffs S pos rev c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_smul <;> assumption
theorem formOfCoeffs_toPauliCoeffs (hF : IsOrientedSpace S pos rev) {f : S.index → ComplexMatrix2}
    (h₁ : ∀ b, pos b → f b ∈ ComplexMatrix2.traceless) (h₂ : ∀ b, f (rev b) = -f b) :
    formOfCoeffs S pos rev (toPauliCoeffs (restrictPositive S pos f)) = f := by
  have hpos : ∀ b (hb : pos b),
      formOfCoeffs S pos rev (toPauliCoeffs (restrictPositive S pos f)) b = f b := fun b hb =>
    (formOfCoeffs_apply _ b hb).trans (sum_pauliCoeff_smul (h₁ b hb))
  funext b
  by_cases hb : pos b
  · exact hpos b hb
  · have hrb : pos (rev b) := by
      rcases hF.xor_pos b with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd h hb
      · exact h
    have e : formOfCoeffs S pos rev (toPauliCoeffs (restrictPositive S pos f)) b =
        -zeroExtension S pos (toPauliCoeffs (restrictPositive S pos f)) (rev b) :=
      oddExtension_of_not_pos hb
    have e' : zeroExtension S pos (toPauliCoeffs (restrictPositive S pos f)) (rev b) =
        f (rev b) := by
      rw [← hpos _ hrb]
      exact (oddExtension_of_pos hrb).symm
    rw [e, e', h₂, neg_neg]
theorem positiveRepresentation_exact (hP : OneLoop.PauliMatrixRelations)
    (hF : IsOrientedSpace S pos rev) : IsExactEvaluation (positiveRepresentation S pos rev) where
  mem_space c := (hF.mem_complex_iff _).2 ⟨fun b hb => by
    have e : formOfCoeffs S pos rev c b ∈ ComplexMatrix2.traceless := by
      rw [formOfCoeffs_apply c b hb]
      exact ofPauliCoeffs_mem c _
    exact e, fun b => oddExtension_rev hF _ b⟩
  coeffs_ofCoeffs c := (congrArg toPauliCoeffs (restrictPositive_formOfCoeffs c)).trans
    (toPauliCoeffs_ofPauliCoeffs c)
  ofCoeffs_coeffs f hf := formOfCoeffs_toPauliCoeffs hF ((hF.mem_complex_iff f).1 hf).1
    ((hF.mem_complex_iff f).1 hf).2
  map_add c c' := formOfCoeffs_add c c'
  map_smul z c := formOfCoeffs_smul z c
  pair_eq a b hb := by
    refine (hF.pair_eq_restrict _ _).trans ?_
    have e₁ : restrictPositive S pos ((positiveRepresentation S pos rev).ofCoeffs a) = ofPauliCoeffs a :=
      restrictPositive_formOfCoeffs a
    have e₂ : restrictPositive S pos ((positiveRepresentation S pos rev).ofCoeffs b) = ofPauliCoeffs b :=
      restrictPositive_formOfCoeffs b
    rw [e₁, e₂]
    exact traceFinsumPairing_ofPauliCoeffs hP a b hb
end OrientedSpaces
section FiniteKernels
variable {N N' N'' : Type}
theorem rowFinite_of_finite [Finite N] (T : KernelMatrix N N') : RowFinite T :=
  fun _ => Set.toFinite _
theorem applyKernel_smul (T : KernelMatrix N N') (z : ℂ) (f : N → ℂ) :
    applyKernel T (z • f) = z • applyKernel T f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applyKernel_smul <;> assumption
theorem applyKernel_unit (f : N → ℂ) : applyKernel (unitKernel N) f = f := by
  classical
  funext ι'
  unfold applyKernel unitKernel
  rw [tsum_eq_single ι' fun ι h => by simp [Ne.symm h]]
  simp
theorem applyKernel_sub [Finite N] (T S : KernelMatrix N N') (f : N → ℂ) :
    applyKernel (T - S) f = applyKernel T f - applyKernel S f := by
  funext ι'
  show ∑' ι, (T ι' ι - S ι' ι) * f ι = ∑' ι, T ι' ι * f ι - ∑' ι, S ι' ι * f ι
  simp only [sub_mul]
  exact Summable.tsum_sub (f := fun ι => T ι' ι * f ι) (g := fun ι => S ι' ι * f ι)
    (summable_of_hasFiniteSupport (Set.toFinite _))
    (summable_of_hasFiniteSupport (Set.toFinite _))
theorem compKernel_represents (h : RowFiniteKernels.Claim) {T : KernelMatrix N' N''}
    {S : KernelMatrix N N'} (hT : RowFinite T) (hS : RowFinite S)
    {M : (N → ℂ) → N'' → ℂ} (hM : ∀ f, applyKernel T (applyKernel S f) = M f) :
    Represents (compKernel T S) M := fun f =>
  have e := (((h.1 _ _ S hS).2 _ T hT).2.2 f)
  ⟨e.1, e.2.2.trans (hM f)⟩
theorem compSummable_of_rowFinite (h : RowFiniteKernels.Claim) {T : KernelMatrix N' N''}
    {S : KernelMatrix N N'} (hT : RowFinite T) (hS : RowFinite S) :
    CompSummable T S :=
  ((h.1 _ _ S hS).2 _ T hT).1
theorem applyKernel_compKernel (h : RowFiniteKernels.Claim)
    {T : KernelMatrix N' N''} {S : KernelMatrix N N'} (hT : RowFinite T)
    (hS : RowFinite S) (f : N → ℂ) :
    applyKernel (compKernel T S) f = applyKernel T (applyKernel S f) :=
  (((h.1 _ _ S hS).2 _ T hT).2.2 f).2.2
theorem unitKernel_represents (h : RowFiniteKernels.Claim) :
    Represents (unitKernel N) (fun f => f) := fun f =>
  ⟨(h.1 _ _ _ (h.2.2.1 N).1).1 f, applyKernel_unit f⟩
theorem wPairing_meshWeight {σ : Type} [Finite (Fin 3 × σ)] (a : ℝ) (f f' : Fin 3 × σ → ℂ) :
    wPairing (meshWeight a) f f' = ((a : ℂ) ^ 4) * ∑ᶠ ι, f ι * f' ι := by
  have e : wPairing (meshWeight a) f f' = ∑' ι, ((a : ℂ) ^ 4) * (f ι * f' ι) := by
    unfold wPairing meshWeight
    exact tsum_congr fun ι => by push_cast; rfl
  rw [e, tsum_mul_left, tsum_eq_finsum (Set.toFinite _)]
end FiniteKernels
section TransposedValues
variable {S S' : PairedFunctionSpace} {m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2}
theorem transposeOfValues_mem (m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2)
    {g : S'.index → ComplexMatrix2} (hg : g ∈ S'.complexSubmodule) :
    PairedFunctionSpace.transposeOfValues S S' m g ∈ S.complexSubmodule := by apply _root_.YangMills.Construction.Tower.CovDiffTransposes.transposeOfValues_mem <;> assumption
theorem transposeOfValues_smul (m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2)
    (z : ℂ) {g : S'.index → ComplexMatrix2} (hg : g ∈ S'.complexSubmodule) :
    PairedFunctionSpace.transposeOfValues S S' m (z • g) =
      z • PairedFunctionSpace.transposeOfValues S S' m g := by
  have hz := S'.complexSubmodule.smul_mem z hg
  unfold PairedFunctionSpace.transposeOfValues
  rw [dif_pos hz, dif_pos hg]
  have e : (⟨z • g, hz⟩ : S'.complexSubmodule) = z • (⟨g, hg⟩ : S'.complexSubmodule) := rfl
  rw [e, map_smul]
  rfl
theorem linearOfValues_eq {T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule}
    (hT : ∀ l : S.complexSubmodule, (T l : S'.index → ComplexMatrix2) = m l) :
    PairedFunctionSpace.linearOfValues S S' m = T := by apply _root_.YangMills.Construction.Tower.RescaledBackgroundFormFiniteSide.linearOfValues_eq <;> assumption
end TransposedValues
theorem real_smul_fun_eq_ofReal_smul {ι : Type} (z : ℝ) (f : ι → ComplexMatrix2) :
    z • f = (z : ℂ) • f := by apply _root_.YangMills.SharedProofs.p7664 <;> assumption
section KernelRelations
variable {r₀ b₀ r b : PauliComponentsOfSymmetricKernel}
theorem kernel_real_smul_represents (hM : ScalarMultipleKernels.Statement)
    {r r' : PauliComponentsOfSymmetricKernel} {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (hc : CoeffsRealHomogeneous r') (hk : PauliComponentsOfSymmetricKernel.HasLocalKernel r r' m)
    (ho : KernelUnique r.Index r'.Index) (z : ℝ) :
    Represents (r.kernel r' fun f => z • m f) (r.mapOnCoeffs r' fun f => z • m f) := by
  rw [(hM r r' m hc hk ho z 1 1).1]
  have e : r.mapOnCoeffs r' (fun f => z • m f) = (z : ℂ) • r.mapOnCoeffs r' m :=
    funext fun f => hc z _
  rw [e]
  exact hk.smul_represents z
theorem comp_R_Rt_eq_unit (hP : RowFiniteKernels.Claim) (hr₀ : IsExactEvaluation r₀)
    (hr : IsExactEvaluation r) [Finite r₀.Index] [Finite r.Index] {R : KernelMatrix r₀.Index r.Index}
    {Rt : KernelMatrix r.Index r₀.Index}
    {Rm : (r₀.space.index → ComplexMatrix2) → r.space.index → ComplexMatrix2}
    {z c : ℂ} (hR : Represents R (r₀.mapOnCoeffs r Rm))
    (hRt : Represents Rt (z • r₀.transposeOnCoeffs r Rm))
    (hT : PairedFunctionSpace.HasTransposeProduct r₀.space r.space Rm c) (hzc : z * c = 1)
    (hone : KernelUnique r.Index r.Index) : compKernel R Rt = unitKernel r.Index := by
  refine hone (fun f => f) _ _ (compKernel_represents hP (rowFinite_of_finite _)
    (rowFinite_of_finite _) fun f => ?_) (unitKernel_represents hP)
  obtain ⟨T, hTv, -, hTT⟩ := hT
  have hcl := linearOfValues_eq hTv
  have hg := hr.mem_space f
  have ht : PairedFunctionSpace.transposeOfValues r₀.space r.space Rm (r.ofCoeffs f) =
      (PairedFunctionSpace.transposeMap T ⟨_, hg⟩ : r₀.space.complexSubmodule) := by
    unfold PairedFunctionSpace.transposeOfValues
    rw [dif_pos hg, hcl]
  have e₁ : applyKernel Rt f =
      z • r₀.coeffs (PairedFunctionSpace.transposeMap T ⟨_, hg⟩ : r₀.space.complexSubmodule) := by
    rw [(hRt f).2]
    show z • r₀.coeffs (PairedFunctionSpace.transposeOfValues r₀.space r.space Rm
      (r.ofCoeffs f)) = _
    rw [ht]
  rw [e₁, (hR _).2]
  show r.coeffs (Rm (r₀.ofCoeffs (z • r₀.coeffs _))) = f
  rw [hr₀.map_smul, hr₀.ofCoeffs_coeffs _ (Subtype.property _)]
  have e₂ : Rm (z • (PairedFunctionSpace.transposeMap T ⟨_, hg⟩ : r₀.space.complexSubmodule)) =
      (z * c) • r.ofCoeffs f := by
    have e₃ := hTv (z • PairedFunctionSpace.transposeMap T ⟨_, hg⟩)
    have e₄ : ((z • PairedFunctionSpace.transposeMap T ⟨_, hg⟩ : r₀.space.complexSubmodule) :
        r₀.space.index → ComplexMatrix2) =
        z • (PairedFunctionSpace.transposeMap T ⟨_, hg⟩ : r₀.space.complexSubmodule) := rfl
    rw [← e₄, ← e₃, map_smul]
    show z • (T (PairedFunctionSpace.transposeMap T ⟨_, hg⟩) : r.space.index → ComplexMatrix2) = _
    rw [hTT, smul_smul]
  rw [e₂, hzc, one_smul]
  exact hr.coeffs_ofCoeffs f
theorem comp_Q_D_eq (hP : RowFiniteKernels.Claim) (hr₀ : IsExactEvaluation r₀)
    (hb₀ : IsExactEvaluation b₀) (hr : IsExactEvaluation r) [Finite r₀.Index] [Finite b₀.Index]
    [Finite r.Index]
    {p : RescaledOperators r₀.Place b₀.Place r.Place b.Place}
    {Dm : (r₀.space.index → ComplexMatrix2) → b₀.space.index → ComplexMatrix2}
    {Qm : (b₀.space.index → ComplexMatrix2) → b.space.index → ComplexMatrix2}
    {Rm : (r₀.space.index → ComplexMatrix2) → r.space.index → ComplexMatrix2}
    {Wm : (r.space.index → ComplexMatrix2) → b.space.index → ComplexMatrix2}
    {DW : KernelMatrix (Fin 3 × r.Place) (Fin 3 × b.Place)} (hη : p.eta ≠ 0)
    (hcb₀ : CoeffsRealHomogeneous b₀) (hcb : CoeffsRealHomogeneous b)
    (hD : Represents p.D (r₀.mapOnCoeffs b₀ fun l => (p.eta)⁻¹ • Dm l))
    (hQ : Represents p.Q (b₀.mapOnCoeffs b fun B' => p.eta • Qm B'))
    (hR : Represents p.R (r₀.mapOnCoeffs r Rm)) (hW : Represents DW (r.mapOnCoeffs b Wm))
    (hDm : ∀ l ∈ r₀.space.complexSubmodule, Dm l ∈ b₀.space.complexSubmodule)
    (hRm : ∀ l ∈ r₀.space.complexSubmodule, Rm l ∈ r.space.complexSubmodule)
    (hrel : ∀ l ∈ r₀.space.complexSubmodule, Qm (Dm l) = Wm (Rm l))
    (hone : KernelUnique r₀.Index b.Index) : compKernel p.Q p.D = compKernel DW p.R := by
  refine hone (fun f => applyKernel DW (applyKernel p.R f)) _ _
    (compKernel_represents hP (rowFinite_of_finite _) (rowFinite_of_finite _) fun f => ?_)
    (compKernel_represents hP (rowFinite_of_finite _) (rowFinite_of_finite _) fun f => rfl)
  have hl := hr₀.mem_space f
  have e₁ : applyKernel p.D f = (((p.eta)⁻¹ : ℝ) : ℂ) • b₀.coeffs (Dm (r₀.ofCoeffs f)) :=
    (hD f).2.trans (hcb₀ _ _)
  have e₂ : applyKernel p.R f = r.coeffs (Rm (r₀.ofCoeffs f)) := (hR f).2
  rw [e₁, e₂, applyKernel_smul, (hQ _).2, (hW _).2]
  show _ • b.coeffs (p.eta • Qm (b₀.ofCoeffs (b₀.coeffs (Dm (r₀.ofCoeffs f))))) =
    b.coeffs (Wm (r.ofCoeffs (r.coeffs (Rm (r₀.ofCoeffs f)))))
  rw [hb₀.ofCoeffs_coeffs _ (hDm _ hl), hr.ofCoeffs_coeffs _ (hRm _ hl), hcb, hrel _ hl,
    smul_smul]
  have e₃ : (((p.eta)⁻¹ : ℝ) : ℂ) * (p.eta : ℂ) = 1 := by
    have : (p.eta : ℂ) ≠ 0 := by exact_mod_cast hη
    push_cast
    field_simp
  rw [e₃, one_smul]
theorem wPairing_H (hb₀ : IsExactEvaluation b₀) [Finite (Fin 3 × b₀.Place)]
    {p : RescaledOperators r₀.Place b₀.Place r.Place b.Place}
    {A : (b₀.space.index → ComplexMatrix2) → b₀.space.index → ComplexMatrix2}
    {B : b₀.space.index → ComplexMatrix2}
    (hB : B ∈ b₀.space.complexSubmodule) (hA : A B ∈ b₀.space.complexSubmodule)
    (hη : (p.eta : ℂ) ≠ 0)
    (hH : Represents p.H (((p.eta : ℂ) ^ 2)⁻¹ • b₀.mapOnCoeffs b₀ A)) :
    wPairing (meshWeight p.eta) (b₀.coeffs B) (applyKernel p.H (b₀.coeffs B)) =
      (p.eta : ℂ) ^ 2 * b₀.space.pair B (A B) := by
  have e₁ : applyKernel p.H (b₀.coeffs B) = ((p.eta : ℂ) ^ 2)⁻¹ • b₀.coeffs (A B) := by
    rw [(hH _).2]
    show ((p.eta : ℂ) ^ 2)⁻¹ • b₀.coeffs (A (b₀.ofCoeffs (b₀.coeffs B))) = _
    rw [hb₀.ofCoeffs_coeffs B hB]
  have e₂ : b₀.space.pair B (A B) = ∑ᶠ ι, b₀.coeffs B ι * b₀.coeffs (A B) ι := by
    have := hb₀.pair_eq (b₀.coeffs B) (b₀.coeffs (A B)) (Set.toFinite _)
    rwa [hb₀.ofCoeffs_coeffs B hB, hb₀.ofCoeffs_coeffs _ hA] at this
  rw [wPairing_meshWeight, e₁, e₂]
  have e₃ : ∀ ι, b₀.coeffs B ι * (((p.eta : ℂ) ^ 2)⁻¹ • b₀.coeffs (A B)) ι =
      ((p.eta : ℂ) ^ 2)⁻¹ * (b₀.coeffs B ι * b₀.coeffs (A B) ι) := fun ι => by
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp only [e₃]
  rw [← mul_finsum]
  field_simp
theorem gaugeTerm_eq (hP : RowFiniteKernels.Claim) (hr₀ : IsExactEvaluation r₀)
    (hb₀ : IsExactEvaluation b₀) (hr : IsExactEvaluation r) [Finite (Fin 3 × r₀.Place)]
    [Finite (Fin 3 × r.Place)]
    {p : RescaledOperators r₀.Place b₀.Place r.Place b.Place}
    {Dm : (r₀.space.index → ComplexMatrix2) → b₀.space.index → ComplexMatrix2}
    {Rm : (r₀.space.index → ComplexMatrix2) → r.space.index → ComplexMatrix2} {Lz : ℝ}
    {T : r₀.space.complexSubmodule →ₗ[ℂ] r.space.complexSubmodule}
    (hη : (p.eta : ℂ) ≠ 0)
    (hDt : Represents p.Dt ((p.eta : ℂ)⁻¹ • r₀.transposeOnCoeffs b₀ Dm))
    (hR : Represents p.R (r₀.mapOnCoeffs r Rm))
    (hRt : Represents p.Rt ((Lz : ℂ) • r₀.transposeOnCoeffs r Rm))
    (hT : ∀ l : r₀.space.complexSubmodule, (T l : r.space.index → ComplexMatrix2) = Rm l)
    {B : b₀.space.index → ComplexMatrix2} (hB : B ∈ b₀.space.complexSubmodule) :
    PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm (p.eta • B) -
        Lz • PairedFunctionSpace.transposeOfValues r₀.space r.space Rm
          (Rm (PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm (p.eta • B))) =
      r₀.ofCoeffs (((p.eta : ℂ) ^ 2) • applyKernel (complementProj p)
        (applyKernel p.Dt (b₀.coeffs B))) := by
  have hd := transposeOfValues_mem (S := r₀.space) Dm hB
  have hRm : ∀ l ∈ r₀.space.complexSubmodule, Rm l ∈ r.space.complexSubmodule := fun l hl => by
    rw [← hT ⟨l, hl⟩]
    exact Subtype.property _
  have hRs : ∀ (z : ℂ), ∀ l ∈ r₀.space.complexSubmodule, Rm (z • l) = z • Rm l :=
    fun z l hl => by
      have e₁ := hT (z • ⟨l, hl⟩)
      have e₂ := hT ⟨l, hl⟩
      rw [map_smul] at e₁
      have e₃ : ((z • (⟨l, hl⟩ : r₀.space.complexSubmodule) : r₀.space.complexSubmodule) :
          r₀.space.index → ComplexMatrix2) = z • l := rfl
      rw [e₃] at e₁
      rw [← e₁]
      show z • (T ⟨l, hl⟩ : r.space.index → ComplexMatrix2) = _
      rw [e₂]
  obtain ⟨g, hg⟩ : ∃ g, g = applyKernel p.Dt (b₀.coeffs B) := ⟨_, rfl⟩
  have hg₁ : g = (p.eta : ℂ)⁻¹ •
      r₀.coeffs (PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm B) := by
    rw [hg, (hDt _).2]
    show (p.eta : ℂ)⁻¹ • r₀.coeffs (PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm
      (b₀.ofCoeffs (b₀.coeffs B))) = _
    rw [hb₀.ofCoeffs_coeffs B hB]
  have hl : r₀.ofCoeffs g =
      (p.eta : ℂ)⁻¹ • PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm B := by
    rw [hg₁, hr₀.map_smul, hr₀.ofCoeffs_coeffs _ hd]
  have hlm := hr₀.mem_space g
  have hym := transposeOfValues_mem (S := r₀.space) Rm (hRm _ hlm)
  have hPg : applyKernel (compKernel p.Rt p.R) g = (Lz : ℂ) • r₀.coeffs
      (PairedFunctionSpace.transposeOfValues r₀.space r.space Rm (Rm (r₀.ofCoeffs g))) := by
    rw [applyKernel_compKernel hP (rowFinite_of_finite _) (rowFinite_of_finite _), (hR g).2,
      (hRt _).2]
    show (Lz : ℂ) • r₀.coeffs (PairedFunctionSpace.transposeOfValues r₀.space r.space Rm
      (r.ofCoeffs (r.coeffs (Rm (r₀.ofCoeffs g))))) = _
    rw [hr.ofCoeffs_coeffs _ (hRm _ hlm)]
  have hh : applyKernel (complementProj p) g = r₀.coeffs (r₀.ofCoeffs g) + (-(Lz : ℂ)) •
      r₀.coeffs (PairedFunctionSpace.transposeOfValues r₀.space r.space Rm
        (Rm (r₀.ofCoeffs g))) := by
    unfold complementProj
    rw [applyKernel_sub, applyKernel_unit, hPg, hr₀.coeffs_ofCoeffs, neg_smul, sub_eq_add_neg]
  have e₁ : PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm (p.eta • B) =
      ((p.eta : ℂ) ^ 2) • r₀.ofCoeffs g := by
    rw [real_smul_fun_eq_ofReal_smul, transposeOfValues_smul _ _ hB, hl, smul_smul]
    congr 1
    field_simp
  rw [← hg, hh, hr₀.map_smul, hr₀.map_add, hr₀.map_smul, hr₀.ofCoeffs_coeffs _ hlm,
    hr₀.ofCoeffs_coeffs _ hym, e₁, hRs _ _ hlm, transposeOfValues_smul _ _ (hRm _ hlm),
    real_smul_fun_eq_ofReal_smul]
  simp only [smul_add, smul_smul, neg_smul, smul_neg, sub_eq_add_neg]
  rw [mul_comm]
theorem pair_gaugeTerm (hr₀ : IsExactEvaluation r₀) [Finite (Fin 3 × r₀.Place)] (a : ℝ)
    (h : Fin 3 × r₀.Place → ℂ) :
    r₀.space.pair (r₀.ofCoeffs (((a : ℂ) ^ 2) • h)) (r₀.ofCoeffs (((a : ℂ) ^ 2) • h)) =
      wPairing (meshWeight a) h h := by
  rw [hr₀.pair_eq _ _ (Set.toFinite _), wPairing_meshWeight, mul_finsum]
  refine finsum_congr fun ι => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
theorem symmBilinear_smul_smul {α : Type} {𝒮 : Submodule ℂ (α → ComplexMatrix2)}
    {Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ}
    (hQ : HessianKernel.IsSymmBilinearOn (𝒮 : Set (α → ComplexMatrix2)) Q)
    (z : ℂ) {E : α → ComplexMatrix2} (hE : E ∈ 𝒮) : Q (z • E) (z • E) = z ^ 2 * Q E E := by
  have h0 := 𝒮.zero_mem
  have z₁ : ∀ F ∈ 𝒮, Q 0 F = 0 := fun F hF => by
    have := (hQ 1 0 h0 0 h0 F hF).1
    simpa using this
  have z₂ : ∀ F ∈ 𝒮, Q F 0 = 0 := fun F hF => by
    have := (hQ 1 0 h0 0 h0 F hF).2.1
    simpa using this
  have e₁ := (hQ z E hE 0 h0 (z • E) (𝒮.smul_mem z hE)).1
  have e₂ := (hQ z E hE 0 h0 E hE).2.1
  rw [add_zero] at e₁ e₂
  rw [e₁, e₂, z₁ _ (𝒮.smul_mem z hE), z₂ _ hE]
  ring
theorem coreRelations_of_maps (hP : RowFiniteKernels.Claim)
    (hAlg : RescaledKernelAlgebra.Claim) (hr₀ : IsExactEvaluation r₀)
    (hb₀ : IsExactEvaluation b₀) (hr : IsExactEvaluation r) [Finite (Fin 3 × r₀.Place)]
    [Finite (Fin 3 × b₀.Place)] [Finite (Fin 3 × r.Place)] [Finite (Fin 3 × b.Place)]
    {p : RescaledOperators r₀.Place b₀.Place r.Place b.Place}
    {Dm : (r₀.space.index → ComplexMatrix2) → b₀.space.index → ComplexMatrix2}
    {Qm : (b₀.space.index → ComplexMatrix2) → b.space.index → ComplexMatrix2}
    {Rm : (r₀.space.index → ComplexMatrix2) → r.space.index → ComplexMatrix2}
    {Wm : (r.space.index → ComplexMatrix2) → b.space.index → ComplexMatrix2}
    {DW : KernelMatrix (Fin 3 × r.Place) (Fin 3 × b.Place)}
    {background : (b₀.space.index → ComplexMatrix2) → (b₀.space.index → ComplexMatrix2) → ℂ}
    {A : (b₀.space.index → ComplexMatrix2) → b₀.space.index → ComplexMatrix2} {Lz : ℝ} {c : ℂ}
    (hη : 0 < p.eta) (hcoarse : 0 < p.coarse)
    (hcb₀ : CoeffsRealHomogeneous b₀) (hcb : CoeffsRealHomogeneous b)
    (hD : Represents p.D (r₀.mapOnCoeffs b₀ fun l => (p.eta)⁻¹ • Dm l))
    (hQ : Represents p.Q (b₀.mapOnCoeffs b fun B' => p.eta • Qm B'))
    (hR : Represents p.R (r₀.mapOnCoeffs r Rm)) (hW : Represents DW (r.mapOnCoeffs b Wm))
    (hDt : Represents p.Dt ((p.eta : ℂ)⁻¹ • r₀.transposeOnCoeffs b₀ Dm))
    (hH : Represents p.H (((p.eta : ℂ) ^ 2)⁻¹ • b₀.mapOnCoeffs b₀ A))
    (hRt : Represents p.Rt ((Lz : ℂ) • r₀.transposeOnCoeffs r Rm))
    (hTr : PairedFunctionSpace.HasTransposeProduct r₀.space r.space Rm c)
    (hzc : (Lz : ℂ) * c = 1)
    (hDm : ∀ l ∈ r₀.space.complexSubmodule, Dm l ∈ b₀.space.complexSubmodule)
    (hrel : ∀ l ∈ r₀.space.complexSubmodule, Qm (Dm l) = Wm (Rm l))
    (hA : ∀ B ∈ b₀.space.complexSubmodule, A B ∈ b₀.space.complexSubmodule)
    (hone₁ : KernelUnique r.Index r.Index) (hone₂ : KernelUnique r₀.Index b.Index)
    (hback : ∀ B ∈ b₀.space.complexSubmodule, background (p.eta • B) (p.eta • B) =
      (p.eta : ℂ) ^ 2 * b₀.space.pair B (A B) + r₀.space.pair
        (PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm (p.eta • B) -
          Lz • PairedFunctionSpace.transposeOfValues r₀.space r.space Rm
            (Rm (PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm (p.eta • B))))
        (PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm (p.eta • B) -
          Lz • PairedFunctionSpace.transposeOfValues r₀.space r.space Rm
            (Rm (PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm (p.eta • B))))) :
    CoreRelations r₀ b₀ r b p Dm Qm Rm Wm DW background := by
  have hηc : (p.eta : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have hRRt : compKernel p.R p.Rt = unitKernel (Fin 3 × r.Place) :=
    comp_R_Rt_eq_unit hP hr₀ hr hR hRt hTr hzc hone₁
  obtain ⟨T, hTv, -, -⟩ := id hTr
  have hRm : ∀ l ∈ r₀.space.complexSubmodule, Rm l ∈ r.space.complexSubmodule := fun l hl => by
    rw [← hTv ⟨l, hl⟩]
    exact Subtype.property _
  have hQD : compKernel p.Q p.D = compKernel DW p.R :=
    comp_Q_D_eq hP hr₀ hb₀ hr hη.ne' hcb₀ hcb hD hQ hR hW hDm hRm hrel hone₂
  have hcons := hAlg _ _ _ _ p hη hcoarse
    ⟨rowFinite_of_finite _, rowFinite_of_finite _, rowFinite_of_finite _,
      rowFinite_of_finite _, rowFinite_of_finite _⟩ hRRt
  refine ⟨hRRt, hQD, ?_, hR, hQ, hD, hW, ⟨rowFinite_of_finite _, rowFinite_of_finite _,
    rowFinite_of_finite _, rowFinite_of_finite _, rowFinite_of_finite _,
    rowFinite_of_finite _⟩, ⟨compSummable_of_rowFinite hP (rowFinite_of_finite _)
      (rowFinite_of_finite _), compSummable_of_rowFinite hP (rowFinite_of_finite _)
      (rowFinite_of_finite _), compSummable_of_rowFinite hP (rowFinite_of_finite _)
      (rowFinite_of_finite _), compSummable_of_rowFinite hP (rowFinite_of_finite _)
      (rowFinite_of_finite _)⟩, hcons.complementProj_row_finite, hcons.comp_assoc⟩
  intro B hB _
  rw [hcons.pairing_eq (b₀.coeffs B) (Set.toFinite _), wPairing_H hb₀ hB (hA B hB) hηc hH,
    ← pair_gaugeTerm hr₀ p.eta, ← gaugeTerm_eq hP hr₀ hb₀ hr hηc hDt hR hRt hTv hB]
  exact hback B hB
end KernelRelations
section TorusSide
variable {L n k : ℕ}
theorem edge_isOrientedSpace (hO : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ}
    (hj : j ≤ k) :
    IsOrientedSpace (edgePairedSpace L n k j) (fun b => b.IsPositivelyOriented)
      PeriodicLattice.Bond.opposite where
  xor_pos b := ((hO ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj).2.2.2 b).2.2.2.2.2
  rev_rev_eq _ := rfl
  mem_complex_iff _ := Iff.rfl
  pair_eq_restrict _ _ := rfl
theorem edgePauliCoordinates_exact (hP : OneLoop.PauliMatrixRelations)
    (hO : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ}
    (hj : j ≤ k) : IsExactEvaluation (edgePauliCoordinates L n k j) :=
  positiveRepresentation_exact hP (edge_isOrientedSpace hO hL hn hk hj)
theorem finite_edge (hF : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k) :
    Finite (Edge L n k j) :=
  Set.finite_univ_iff.1 ((hF L hL k j hj).1 n hn).2.1
theorem finite_vertex (hF : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k) :
    Finite (Vertex L n k j) :=
  have := finite_edge hF hL hn hj
  Finite.of_injective (fun x : Vertex L n k j => PeriodicLattice.Bond.forwardFrom x 0)
    fun _ _ h => congrArg PeriodicLattice.Bond.source h
theorem edgePauliCoordinates_homogeneous (j : ℕ) : CoeffsRealHomogeneous (edgePauliCoordinates L n k j) := by apply _root_.YangMills.Construction.Tower.IterTransposesOnTorus.edgePauliCoordinates_coeffsRealHomogeneous <;> assumption
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem covDiff_mem (hC : ComplexMatrix2.ConjugationPreservesTraceless)
    (hO : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    {W : Edge L n k 0 → ComplexMatrix2}
    (hW : W ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup)
    {l : Vertex L n k 0 → ComplexMatrix2}
    (hl : l ∈ (pairedFunctions (Vertex L n k 0)).complexSubmodule) :
    covDiff W l ∈ (edgePairedSpace L n k 0).complexSubmodule := by
  have hF := edge_isOrientedSpace hO hL hn hk (Nat.zero_le k)
  have hrev : ∀ (f : Edge L n k 0 → ComplexMatrix2) (b : Edge L n k 0),
      extendOddly f b.opposite = -extendOddly f b := fun f b => oddExtension_rev hF f b
  refine (hF.mem_complex_iff _).2 ⟨fun b hb => ?_, fun b => hrev _ b⟩
  have e : covDiff W l b = ComplexMatrix2.conjugateBy (W b) (l b.target) - l b.source := if_pos hb
  rw [e]
  have hV : W b ∈ ComplexMatrix2.unitDeterminant := hW.1 b (mem_univ b)
  exact ComplexMatrix2.traceless.sub_mem ((hC.2.2 _ (hC.1 _ hV)).2.2.2.1 (hl _ (mem_univ _)))
    (hl _ (mem_univ _))
theorem pow_mul_weight_pow (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    ((L : ℂ) ^ (4 * k)) * PeriodicLattice.inverseFourthPowerWeight L ^ k = 1 := by
  have h0 : (L : ℂ) ≠ 0 := by
    have := hL.2
    exact_mod_cast (by omega : L ≠ 0)
  unfold PeriodicLattice.inverseFourthPowerWeight
  push_cast
  rw [pow_mul, ← mul_pow]
  have : (L : ℂ) ^ 4 * (L : ℂ) ^ (-4 : ℤ) = 1 := by
    rw [zpow_neg]
    norm_cast
    field_simp
  rw [this, one_pow]
theorem ofReal_pow_cast (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    (((L : ℝ) ^ (4 * k) : ℝ) : ℂ) = (L : ℂ) ^ (4 * k) := by
  push_cast
  rfl
end TorusSide
theorem rescaledIterRelations_holds (hKernels : ThreeMapKernels.Claim)
    (hProducts : RowFiniteKernels.Claim)
    (hCovariant : CovariantSmoothingProperties.Statement)
    (hAlgebra : RescaledKernelAlgebra.Claim)
    (hMultiples : ScalarMultipleKernels.Statement)
    (hEvery : ComplexFieldRescaledRelations.Statement)
    (hAverages : IterTransposesOnTorus.Claim)
    (hSecond : HessianKernel.KernelProperties)
    (hPauli : OneLoop.PauliMatrixRelations)
    (hOrientation : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hFinite : BondSetFields.ProductStructureHolds)
    (hConjugation : ComplexMatrix2.ConjugationPreservesTraceless)
    (hIterates : LocalKernels.SmallIterates.SmallIteratesInComplexGaugeGroup) :
    RescaledIterRelations := by
  intro L hL k hk n hn U hU
  have hη : 0 < finestMesh L k := meshAt_pos hL k 0
  have hcoarse : 0 < meshAt L k k := meshAt_pos hL k k
  haveI := finite_vertex (k := k) hFinite hL hn (Nat.zero_le k)
  haveI := finite_vertex (k := k) hFinite hL hn (le_refl k)
  haveI := finite_edge (k := k) hFinite hL hn (Nat.zero_le k)
  haveI := finite_edge (k := k) hFinite hL hn (le_refl k)
  haveI : Finite (Fin 3 × (vertexCoordinate (Vertex L n k 0)).Place) :=
    inferInstanceAs (Finite (Fin 3 × Vertex L n k 0))
  haveI : Finite (Fin 3 × (vertexCoordinate (Vertex L n k k)).Place) :=
    inferInstanceAs (Finite (Fin 3 × Vertex L n k k))
  haveI : Finite (Fin 3 × (edgePauliCoordinates L n k 0).Place) :=
    inferInstanceAs (Finite (Fin 3 × PositiveEdge L n k 0))
  haveI : Finite (Fin 3 × (edgePauliCoordinates L n k k).Place) :=
    inferInstanceAs (Finite (Fin 3 × PositiveEdge L n k k))
  have hr₀ := vertexCoordinate_exact hPauli (Vertex L n k 0)
  have hr := vertexCoordinate_exact hPauli (Vertex L n k k)
  have hb₀ := edgePauliCoordinates_exact (k := k) (j := 0) hPauli hOrientation hL hn hk (Nat.zero_le k)
  have hcb₀ := edgePauliCoordinates_homogeneous (L := L) (n := n) (k := k) 0
  have hcb := edgePauliCoordinates_homogeneous (L := L) (n := n) (k := k) k
  obtain ⟨hone, hD0, hDk, hAv⟩ := (hKernels L hL k hk).1 n hn
  have hUc := hU.1
  have hWc := hIterates L hL k n hn hk U hU k le_rfl
  obtain ⟨hQk, hRk⟩ := hAv U hU
  have hDker := hD0 U hUc
  have hWker := hDk _ hWc
  have hev := hEvery L hL k hk n hn U hUc
  have hav := hAverages L hL k hk n hn U hU
  obtain ⟨-, hrel, hTr⟩ := (((hCovariant L hL).1 n k hn).2 k le_rfl).1 U hU
  have hD : Represents (rescaledOperators L n k U).D _ :=
    kernel_real_smul_represents hMultiples (edgePauliCoordinates_homogeneous 0) hDker
      (hone 0 0 (Nat.zero_le k) (Nat.zero_le k)).2.1 (finestMesh L k)⁻¹
  have hQ : Represents (rescaledOperators L n k U).Q _ :=
    kernel_real_smul_represents hMultiples (edgePauliCoordinates_homogeneous k) hQk
      (hone 0 k (Nat.zero_le k) le_rfl).2.2.2 (finestMesh L k)
  have hR := hRk.represents
  have hW := hWker.represents
  have hRt' : Represents (rescaledOperators L n k U).Rt
      ((((L : ℝ) ^ (4 * k) : ℝ) : ℂ) • (vertexCoordinate (Vertex L n k 0)).transposeOnCoeffs
        (vertexCoordinate (Vertex L n k k)) (iterAdjointCubeAverage L n k U k)) := by
    rw [ofReal_pow_cast hL k]
    exact hav.1
  have hzc : ((((L : ℝ) ^ (4 * k) : ℝ)) : ℂ) *
      PeriodicLattice.inverseFourthPowerWeight L ^ k = 1 := by
    rw [ofReal_pow_cast hL k]
    exact pow_mul_weight_pow hL k
  have hA₂ := (hSecond L hL k 0 (Nat.zero_le k)).1 n hn U hUc
  exact coreRelations_of_maps (r₀ := vertexCoordinate (Vertex L n k 0)) (b₀ := edgePauliCoordinates L n k 0)
    (r := vertexCoordinate (Vertex L n k k)) (b := edgePauliCoordinates L n k k)
    (p := rescaledOperators L n k U)
    (Dm := covDiff U) (Qm := iterCovariantDeriv L n k U k)
    (Rm := iterAdjointCubeAverage L n k U k)
    (Wm := covDiff (PeriodicLattice.complexBlockFieldAtLevel k U))
    (DW := covDiffKernel L n k k (PeriodicLattice.complexBlockFieldAtLevel k U))
    (background := backgroundForm L n k U) (A := complexHessianOperator U)
    hProducts hAlgebra hr₀ hb₀ hr hη hcoarse hcb₀ hcb hD hQ hR hW hev.1 hev.2.1 hRt' hTr hzc
    (fun l hl => covDiff_mem hConjugation hOrientation hL hn hk hUc hl)
    (fun l hl => (hrel l fun x => hl x (mem_univ x)).2)
    (fun _ _ => hb₀.mem_space _) (hone k k le_rfl le_rfl).1 (hone 0 k (Nat.zero_le k) le_rfl).2.1
    fun B hB => by
      have e₁ : complexActionHessian U (finestMesh L k • B) (finestMesh L k • B) =
          ((finestMesh L k : ℝ) : ℂ) ^ 2 * edgeFormPairing B (complexHessianOperator U B) := by
        have e₂ := symmBilinear_smul_smul (𝒮 := complexEdgeForms L n k 0)
          (Q := complexActionHessian U) hA₂.1 ((finestMesh L k : ℝ) : ℂ) hB
        rw [real_smul_fun_eq_ofReal_smul]
        exact e₂.trans (by rw [hA₂.2.2.2.2.1 B hB B hB])
      exact congrArg (· + _) e₁
end YangMills.Construction.Tower.IterRelationsOnTorus
end
