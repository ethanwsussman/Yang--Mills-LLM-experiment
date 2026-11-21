import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.KernelDeterminedByABilinearForm
import YangMills.Construction.Towers.LinearMapsBetweenTwoLevelsOfATower
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.RelationsOfTheIteratedAveragesOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import Mathlib
set_option autoImplicit false
open Set Filter
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.RescaledTrivialRelationsProof
open YangMills.Construction.Matrices
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.RescaledConditions (TrivialRelations complementProj)
open YangMills.Construction.Tower.FullSpace.RescaledConditions (TrivialStep)
section RowFiniteKernels
variable {N N' : Type}
theorem applySummable_of_rowFinite {T : KernelMatrix N N'} (hT : RowFinite T) (f : N → ℂ) :
    ApplySummable T f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applySummable_of_rowFinite <;> assumption
theorem applyKernel_smul (T : KernelMatrix N N') (z : ℂ) (f : N → ℂ) :
    applyKernel T (z • f) = z • applyKernel T f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applyKernel_smul <;> assumption
end RowFiniteKernels
section PauliCoefficients
theorem combination_pauliCoeff {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
end PauliCoefficients
structure IsFaithful (r : PauliComponentsOfSymmetricKernel) : Prop where
  mem : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule
  left : ∀ c, r.coeffs (r.ofCoeffs c) = c
  right : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f
  add : ∀ c c', r.ofCoeffs (c + c') = r.ofCoeffs c + r.ofCoeffs c'
  smul : ∀ (z : ℂ) c, r.ofCoeffs (z • c) = z • r.ofCoeffs c
  support : ∀ c, r.space.IsFinitelySupported (r.ofCoeffs c) ↔ (Function.support c).Finite
  pairing : ∀ a c, (Function.support c).Finite →
    r.space.pair (r.ofCoeffs a) (r.ofCoeffs c) = ∑ᶠ ι, a ι * c ι
namespace IsFaithful
variable {r : PauliComponentsOfSymmetricKernel}
theorem coeffs_smul (h : IsFaithful r) (z : ℂ) {f : r.space.index → ComplexMatrix2}
    (hf : f ∈ r.space.complexSubmodule) : r.coeffs (z • f) = z • r.coeffs f := by
  have e : z • f = r.ofCoeffs (z • r.coeffs f) := by
    rw [h.smul, h.right f hf]
  conv_lhs => rw [e, h.left]
end IsFaithful
section VertexFunctions
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
    (a c : Fin 3 × σ → ℂ) (hc : (Function.support c).Finite) :
    traceFinsumPairing (ofPauliCoeffs a) (ofPauliCoeffs c) = ∑ᶠ ι, a ι * c ι := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.traceFinsumPairing_ofPauliCoeffs <;> assumption
theorem vertexCoordinate_faithful (hP : OneLoop.PauliMatrixRelations) (σ : Type) :
    IsFaithful (vertexCoordinate σ) where
  mem c := fun i _ => ofPauliCoeffs_mem c i
  left c := toPauliCoeffs_ofPauliCoeffs c
  right f hf := funext fun i => combination_pauliCoeff (hf i (mem_univ i))
  add c c' := ofPauliCoeffs_add c c'
  smul z c := ofPauliCoeffs_smul z c
  support c := hasFiniteSupp_ofPauliCoeffs_iff c
  pairing a c hc := traceFinsumPairing_ofPauliCoeffs hP a c hc
end VertexFunctions
section OrientedFrames
variable (S : PairedFunctionSpace) (pos : S.index → Prop) (rev : S.index → S.index)
def oddExtension (f : S.index → ComplexMatrix2) : S.index → ComplexMatrix2 :=
  open Classical in fun e => if pos e then f e else -f (rev e)
def zeroExtension (c : Fin 3 × {e : S.index // pos e} → ℂ) : S.index → ComplexMatrix2 :=
  open Classical in fun e => if h : pos e then ofPauliCoeffs c ⟨e, h⟩ else 0
def orientedForm (c : Fin 3 × {e : S.index // pos e} → ℂ) : S.index → ComplexMatrix2 :=
  oddExtension S pos rev (zeroExtension S pos c)
def positiveValues (B : S.index → ComplexMatrix2) : {e : S.index // pos e} → ComplexMatrix2 :=
  fun e => B e.1
def orientedPauliBasis : PauliComponentsOfSymmetricKernel where
  space := S
  Place := {e : S.index // pos e}
  ofCoeffs := orientedForm S pos rev
  coeffs := fun B => toPauliCoeffs (positiveValues S pos B)
structure IsOrientedFrame : Prop where
  xor : ∀ e, Xor (pos e) (pos (rev e))
  rev_rev : ∀ e, rev (rev e) = e
  mem_iff : ∀ B, B ∈ S.complexSubmodule ↔
    (∀ e, pos e → B e ∈ ComplexMatrix2.traceless) ∧ ∀ e, B (rev e) = -B e
  fin_iff : ∀ B, S.IsFinitelySupported B ↔ HasFiniteSupp (positiveValues S pos B)
  pairing_eq : ∀ B B', S.pair B B' =
    traceFinsumPairing (positiveValues S pos B) (positiveValues S pos B')
variable {S pos rev}
theorem oddExtension_of_pos {f : S.index → ComplexMatrix2} {e : S.index} (h : pos e) :
    oddExtension S pos rev f e = f e := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_pos <;> assumption
theorem oddExtension_of_not_pos {f : S.index → ComplexMatrix2} {e : S.index} (h : ¬ pos e) :
    oddExtension S pos rev f e = -f (rev e) := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_neg <;> assumption
theorem oddExtension_rev (hF : IsOrientedFrame S pos rev) (f : S.index → ComplexMatrix2)
    (e : S.index) : oddExtension S pos rev f (rev e) = -oddExtension S pos rev f e := by
  rcases hF.xor e with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [oddExtension_of_not_pos h₂, oddExtension_of_pos h₁, hF.rev_rev]
  · rw [oddExtension_of_pos h₁, oddExtension_of_not_pos h₂, neg_neg]
theorem oddExtension_add (f g : S.index → ComplexMatrix2) :
    oddExtension S pos rev (f + g) = oddExtension S pos rev f + oddExtension S pos rev g := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_add <;> assumption
theorem oddExtension_smul (z : ℂ) (f : S.index → ComplexMatrix2) :
    oddExtension S pos rev (z • f) = z • oddExtension S pos rev f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.oddExtension_smul <;> assumption
theorem orientedForm_apply (c : Fin 3 × {e : S.index // pos e} → ℂ) (e : S.index)
    (he : pos e) : orientedForm S pos rev c e = ofPauliCoeffs c ⟨e, he⟩ := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_apply <;> assumption
theorem positiveValues_orientedForm (c : Fin 3 × {e : S.index // pos e} → ℂ) :
    positiveValues S pos (orientedForm S pos rev c) = ofPauliCoeffs c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.positivePart_formOfCoeffs <;> assumption
theorem zeroExtension_add (c c' : Fin 3 × {e : S.index // pos e} → ℂ) :
    zeroExtension S pos (c + c') = zeroExtension S pos c + zeroExtension S pos c' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.zeroExtension_add <;> assumption
theorem zeroExtension_smul (z : ℂ) (c : Fin 3 × {e : S.index // pos e} → ℂ) :
    zeroExtension S pos (z • c) = z • zeroExtension S pos c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.zeroExtension_smul <;> assumption
theorem orientedForm_add (c c' : Fin 3 × {e : S.index // pos e} → ℂ) :
    orientedForm S pos rev (c + c') = orientedForm S pos rev c + orientedForm S pos rev c' := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_add <;> assumption
theorem orientedForm_smul (z : ℂ) (c : Fin 3 × {e : S.index // pos e} → ℂ) :
    orientedForm S pos rev (z • c) = z • orientedForm S pos rev c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.formOfCoeffs_smul <;> assumption
theorem orientedForm_toPauliCoeffs (hF : IsOrientedFrame S pos rev) {f : S.index → ComplexMatrix2}
    (h₁ : ∀ e, pos e → f e ∈ ComplexMatrix2.traceless) (h₂ : ∀ e, f (rev e) = -f e) :
    orientedForm S pos rev (toPauliCoeffs (positiveValues S pos f)) = f := by
  have hpos : ∀ e (he : pos e),
      orientedForm S pos rev (toPauliCoeffs (positiveValues S pos f)) e = f e := fun e he =>
    (orientedForm_apply _ e he).trans (combination_pauliCoeff (h₁ e he))
  funext e
  by_cases he : pos e
  · exact hpos e he
  · have hre : pos (rev e) := by
      rcases hF.xor e with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd h he
      · exact h
    have x : orientedForm S pos rev (toPauliCoeffs (positiveValues S pos f)) e =
        -zeroExtension S pos (toPauliCoeffs (positiveValues S pos f)) (rev e) :=
      oddExtension_of_not_pos he
    have x' : zeroExtension S pos (toPauliCoeffs (positiveValues S pos f)) (rev e) =
        f (rev e) := by
      rw [← hpos _ hre]
      exact (oddExtension_of_pos hre).symm
    rw [x, x', h₂, neg_neg]
theorem orientedPauliBasis_faithful (hP : OneLoop.PauliMatrixRelations)
    (hF : IsOrientedFrame S pos rev) : IsFaithful (orientedPauliBasis S pos rev) where
  mem c := (hF.mem_iff _).2 ⟨fun e he => by
    have x : orientedForm S pos rev c e ∈ ComplexMatrix2.traceless := by
      rw [orientedForm_apply c e he]
      exact ofPauliCoeffs_mem c _
    exact x, fun e => oddExtension_rev hF _ e⟩
  left c := (congrArg toPauliCoeffs (positiveValues_orientedForm c)).trans
    (toPauliCoeffs_ofPauliCoeffs c)
  right f hf := orientedForm_toPauliCoeffs hF ((hF.mem_iff f).1 hf).1 ((hF.mem_iff f).1 hf).2
  add c c' := orientedForm_add c c'
  smul z c := orientedForm_smul z c
  support c := by
    refine (hF.fin_iff _).trans ?_
    have x : positiveValues S pos ((orientedPauliBasis S pos rev).ofCoeffs c) = ofPauliCoeffs c :=
      positiveValues_orientedForm c
    rw [x]
    exact hasFiniteSupp_ofPauliCoeffs_iff c
  pairing a c hc := by
    refine (hF.pairing_eq _ _).trans ?_
    have x₁ : positiveValues S pos ((orientedPauliBasis S pos rev).ofCoeffs a) = ofPauliCoeffs a :=
      positiveValues_orientedForm a
    have x₂ : positiveValues S pos ((orientedPauliBasis S pos rev).ofCoeffs c) = ofPauliCoeffs c :=
      positiveValues_orientedForm c
    rw [x₁, x₂]
    exact traceFinsumPairing_ofPauliCoeffs hP a c hc
end OrientedFrames
theorem edgePairedSpace_isOrientedFrame {a : ℝ} (ha : 0 < a) :
    IsOrientedFrame (edgePairedSpace a) (fun e => e.IsPositivelyOriented)
      InfiniteLattice.Link.opposite where
  xor e := by
    rcases InfiniteLattice.xor_mem_positiveLinks ha e with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
    · exact Or.inr ⟨InfiniteLattice.mem_positiveLinks_iff.1 h₁,
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)⟩
  rev_rev _ := rfl
  mem_iff _ := Iff.rfl
  fin_iff _ := Iff.rfl
  pairing_eq _ _ := rfl
section KernelMatrices
variable {N N' : Type}
theorem kernelMatrix_unique {T T' : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ}
    (h : Represents T M) (h' : Represents T' M) : T = T' := by
  classical
  funext ι' ι
  have key : ∀ S : KernelMatrix N N',
      applyKernel S (fun κ => if κ = ι then 1 else 0) ι' = S ι' ι := by
    intro S
    show ∑' κ, S ι' κ * (if κ = ι then 1 else 0) = _
    rw [tsum_eq_single ι]
    · simp
    · intro κ hκ
      simp [hκ]
  rw [← key T, ← key T', (h _).2, (h' _).2]
theorem kernelOfMap_eq {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ} (h : Represents T M) :
    kernelOfMap M = T :=
  kernelMatrix_unique (Classical.epsilon_spec (p := fun T => Represents T M) ⟨T, h⟩) h
theorem rowFinite_smul {T : KernelMatrix N N'} (hT : RowFinite T) (z : ℂ) :
    RowFinite (z • T) := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.rowFinite_smul <;> assumption
theorem columnFinite_smul {T : KernelMatrix N N'} (hT : ColumnFinite T) (z : ℂ) :
    ColumnFinite (z • T) := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.columnFinite_smul <;> assumption
theorem applyKernel_smul_kernel (T : KernelMatrix N N') (z : ℂ) (f : N → ℂ) :
    applyKernel (z • T) f = z • applyKernel T f := by apply _root_.YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations.applyKernel_smul_kernel <;> assumption
theorem represents_smul {T : KernelMatrix N N'} {M : (N → ℂ) → N' → ℂ} (hT : RowFinite T)
    (hM : Represents T M) (z : ℂ) : Represents (z • T) (z • M) := fun f =>
  ⟨applySummable_of_rowFinite (rowFinite_smul hT z) f, by
    rw [applyKernel_smul_kernel, (hM f).2]
    rfl⟩
theorem wTranspose_rowFinite {T : KernelMatrix N N'} (hT : ColumnFinite T) (w w' : ℝ) :
    RowFinite (wTranspose (fun _ : N => w) (fun _ : N' => w') T) :=
  fun ι => (hT ι).subset fun ι' hι h0 => hι (by
    have x : T ι' ι = 0 := h0
    simp [wTranspose, x])
theorem applyKernel_hasFiniteSupport {T : KernelMatrix N N'} (hT : ColumnFinite T)
    {f : N → ℂ} (hf : HasFiniteSupport f) : HasFiniteSupport (applyKernel T f) := by apply _root_.YangMills.Construction.Tower.FullSpace.IterRelations.applyKernel_hasFiniteSupport <;> assumption
theorem wPairing_transpose_comp (hK : RowFiniteKernels.Claim)
    {d : KernelMatrix N N'} (hr : RowFinite d) (hc : ColumnFinite d) {w : ℝ} (hw : 0 < w)
    {c : N → ℂ} (hf : HasFiniteSupport c) :
    wPairing (fun _ => w) c
        (applyKernel
          (compKernel (wTranspose (fun _ : N => w) (fun _ : N' => w) d) d) c) =
      (w : ℂ) * ∑ᶠ ι, applyKernel d c ι * applyKernel d c ι := by
  have hdt := wTranspose_rowFinite hc w w
  have hact := (((hK.1 _ _ d hr).2 _ _ hdt).2.2 c).2.2
  rw [hact]
  have hv := applyKernel_hasFiniteSupport hc hf
  obtain ⟨-, -, -, h₁, h₂, x⟩ := hK.2.2.2 N' N d (fun _ => w) (fun _ => w) hr (fun _ => hw)
    (fun _ => hw) _ hv c
  have hs : (Function.support fun i => (w : ℂ) * (c i * applyKernel
      (wTranspose (fun _ : N => w) (fun _ : N' => w) d)
      (applyKernel d c) i)).Finite := by
    refine h₁.subset fun i hi h0 => hi ?_
    have h0' : (w : ℂ) * (applyKernel
      (wTranspose (fun _ : N => w) (fun _ : N' => w) d)
      (applyKernel d c) i * c i) = 0 := h0
    simpa [mul_comm] using h0'
  show ∑' i, (w : ℂ) * (c i * _) = _
  rw [tsum_eq_finsum hs]
  have x₁ : (fun i => (w : ℂ) * (c i * applyKernel
      (wTranspose (fun _ : N => w) (fun _ : N' => w) d)
      (applyKernel d c) i)) = fun i => (w : ℂ) * (applyKernel
      (wTranspose (fun _ : N => w) (fun _ : N' => w) d)
      (applyKernel d c) i * c i) := funext fun i => by ring
  rw [x₁, x, mul_finsum]
end KernelMatrices
section Assembly
open YangMills.Construction.Tower.RescaledKernelAlgebra
theorem trivialRelations_of_kernels (hK : RowFiniteKernels.Claim)
    (hAlg : RescaledKernelAlgebra.Claim) {r₀ b₀ r b q₀ : PauliComponentsOfSymmetricKernel}
    {p : RescaledOperators r₀.Place b₀.Place r.Place b.Place}
    {site : (r₀.space.index → ComplexMatrix2) → b₀.space.index → ComplexMatrix2}
    {bond : (b₀.space.index → ComplexMatrix2) → q₀.space.index → ComplexMatrix2}
    {top : (r.space.index → ComplexMatrix2) → b.space.index → ComplexMatrix2}
    {Qm : (b₀.space.index → ComplexMatrix2) → b.space.index → ComplexMatrix2}
    {Rm : (r₀.space.index → ComplexMatrix2) → r.space.index → ComplexMatrix2}
    (hη : 0 < p.eta) (htop : 0 < p.coarse)
    (hsite : Represents (r₀.kernel b₀ site) (r₀.mapOnCoeffs b₀ site))
    (hbond : Represents (b₀.kernel q₀ bond) (b₀.mapOnCoeffs q₀ bond))
    (htopg : Represents (r.kernel b top) (r.mapOnCoeffs b top))
    (hD : p.D = r₀.kernel b₀ site)
    (hQ : Represents p.Q (b₀.mapOnCoeffs b fun B' => p.eta • Qm B'))
    (hR : Represents p.R (r₀.mapOnCoeffs r Rm))
    (hbr : RowFinite (b₀.kernel q₀ bond))
    (hbt : RowFinite (meshTranspose p.eta p.eta (b₀.kernel q₀ bond)))
    (htr : RowFinite (r.kernel b top)) (hQr : RowFinite p.Q) (hRr : RowFinite p.R)
    (hRt : RowFinite p.Rt) (hDr : RowFinite p.D) (hDt : RowFinite p.Dt)
    (hRRt : compKernel p.R p.Rt = unitKernel (Fin 3 × r.Place))
    (hQd : compKernel p.Q (r₀.kernel b₀ site) = compKernel (r.kernel b top) p.R)
    (hH : p.H = compKernel (meshTranspose p.eta p.eta (b₀.kernel q₀ bond))
      (b₀.kernel q₀ bond)) :
    TrivialRelations r₀ b₀ r b q₀ p site bond top Qm Rm := by
  have hAP := hK.1
  have hDt' : p.Dt = meshTranspose p.eta p.eta (r₀.kernel b₀ site) := by
    rw [← hD]
    rfl
  have hsr : RowFinite (r₀.kernel b₀ site) := hD ▸ hDr
  have hst : RowFinite (meshTranspose p.eta p.eta (r₀.kernel b₀ site)) := hDt' ▸ hDt
  have hHr : RowFinite p.H := by
    rw [hH]
    exact ((hAP _ _ _ hbr).2 _ _ hbt).2.1
  have cons := hAlg _ _ _ _ p hη htop ⟨hDr, hDt, hRr, hRt, hHr⟩ hRRt
  refine ⟨hsite, hbond, htopg, hD, hQ, hR, ⟨((hAP _ _ _ hsr).2 _ _ hQr).1,
    ((hAP _ _ _ hRr).2 _ _ htr).1, ((hAP _ _ _ hbr).2 _ _ hbt).1, ((hAP _ _ _ hst).2 _ _ hsr).1,
    ((hAP _ _ _ hsr).2 _ _ hst).1⟩, hQd, hH, ?_, ?_, ?_⟩
  · show p.H + compKernel p.D p.Dt = _
    rw [hDt', hD, hH]
  · show compKernel p.Dt p.D = _
    rw [hDt', hD]
  · rw [cons.X_eq]
    show p.H + compKernel (compKernel p.D (complementProj p)) p.Dt = _
    rw [hDt', hD, hH]
end Assembly
section FullTower
variable {L k : ℕ}
structure Inputs : Prop where
  relations : RescaledIterRelations
  steps : RescaledTrivialSteps
  algebra : RescaledKernelAlgebra.Claim
  polarisation : PolarisedKernel.ValueAtUnits
  transposes : CovDiffTransposes.Claim
  plaquette : FaceTermDerivatives.Statement
  second : HessianKernel.KernelProperties
  kernels : RowFiniteKernels.Claim
  pauli : OneLoop.PauliMatrixRelations
  linear : Tower.TwoLevelMaps.Statement
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem meshAt_self (hL : Conventions.IsAdmissibleBlockingFactor L) (k : ℕ) :
    meshAt L k k = 1 := by
  simp [meshAt]
theorem real_smul_eq_complex_smul {σ : Type} (a : ℝ) (f : σ → ComplexMatrix2) :
    a • f = (a : ℂ) • f := by apply _root_.YangMills.SharedProofs.p7664 <;> assumption
theorem complexIter_one (hs : ∀ i < k, TrivialStep L k i) :
    ∀ j, j ≤ k → complexIter L k j (fun _ => 1) = fun _ => 1
  | 0, _ => rfl
  | j + 1, h => by
    show smoothingMap L k j (complexIter L k j fun _ => 1) = _
    rw [complexIter_one hs j (by omega)]
    exact (hs j (by omega)).1
theorem crossingSmoothing_mem (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) {i : ℕ} (hi : i < k) {B : Edge L k i → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k i)) :
    crossingSmoothing (a := meshAt L k (i + 1)) L B ∈
      complexEdgeForms (meshAt L k (i + 1)) := by
  have h := (G.linear L hL k hk).2.2.1 1 (i + 1) (by omega) (by omega) (by omega)
  have h₂ := h.crossingSmoothing_mapsTo_surjOn.1 hB
  have x : TwoLevelMaps.crossingSmoothingBetween L k
      (Nat.sub_le (i + 1) 1) B = crossingSmoothing (a := meshAt L k (i + 1)) L B :=
    congrFun ((levelwiseComposition_succ (F := fun j => Edge L k j → ComplexMatrix2)
      (fun _ => crossingSmoothing L) (le_refl i) (Nat.le_succ i)).trans (by
        rw [levelwiseComposition_self]
        rfl)) B
  rw [← x]
  exact h₂
theorem vertexSmoothing_mem {i : ℕ} {l : Vertex L k i → ComplexMatrix2}
    (hl : l ∈ GroupLieProduct.tracelessFunctions (Vertex L k i)) :
    vertexSmoothing (a := meshAt L k (i + 1)) L l ∈
      GroupLieProduct.tracelessFunctions (Vertex L k (i + 1)) := by
  intro y _
  show PeriodicLattice.inverseFourthPowerWeight L •
    ∑ᶠ x ∈ cubeVertices L (meshAt L k i) y, l x ∈ ComplexMatrix2.traceless
  have h : ∑ᶠ x ∈ cubeVertices L (meshAt L k i) y, l x ∈ ComplexMatrix2.traceless :=
    finsum_mem_induction (p := fun X => X ∈ ComplexMatrix2.traceless)
      ComplexMatrix2.traceless.zero_mem
      (fun _ _ => ComplexMatrix2.traceless.add_mem) fun x _ => hl x (mem_univ x)
  exact ComplexMatrix2.traceless.smul_mem _ h
theorem iterCovariantDeriv_one (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) (hs : ∀ i < k, TrivialStep L k i) {B : Edge L k 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) :
    ∀ j, j ≤ k → iterCovariantDeriv L k (fun _ => 1) j B =
        crossingSmoothingIter L k j B ∧
      crossingSmoothingIter L k j B ∈ complexEdgeForms (meshAt L k j)
  | 0, _ => ⟨rfl, hB⟩
  | j + 1, h => by
    obtain ⟨x, hm⟩ := iterCovariantDeriv_one G hL hk hs hB j (by omega)
    refine ⟨?_, crossingSmoothing_mem G hL hk (by omega) hm⟩
    show covariantSmoothingDeriv (complexIter L k j fun _ => 1)
      (iterCovariantDeriv L k (fun _ => 1) j B) =
        crossingSmoothing (a := meshAt L k (j + 1)) L (crossingSmoothingIter L k j B)
    rw [x, complexIter_one hs j (by omega)]
    exact (((hs j (by omega)).2.2.1 _ hm).2.2)
theorem iterAdjointCubeAverage_one (hs : ∀ i < k, TrivialStep L k i)
    {l : Vertex L k 0 → ComplexMatrix2}
    (hl : l ∈ GroupLieProduct.tracelessFunctions (Vertex L k 0)) :
    ∀ j, j ≤ k → iterAdjointCubeAverage L k (fun _ => 1) j l = vertexSmoothingIter L k j l ∧
      vertexSmoothingIter L k j l ∈ GroupLieProduct.tracelessFunctions (Vertex L k j)
  | 0, _ => ⟨rfl, hl⟩
  | j + 1, h => by
    obtain ⟨x, hm⟩ := iterAdjointCubeAverage_one hs hl j (by omega)
    refine ⟨?_, vertexSmoothing_mem hm⟩
    show adjointCubeAverage (complexIter L k j fun _ => 1)
      (iterAdjointCubeAverage L k (fun _ => 1) j l) =
        vertexSmoothing (a := meshAt L k (j + 1)) L (vertexSmoothingIter L k j l)
    rw [x, complexIter_one hs j (by omega)]
    exact (hs j (by omega)).2.2.2 _ hm
theorem edgePauliCoordinates_faithful (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (k j : ℕ) : IsFaithful (edgePauliCoordinates L k j) :=
  orientedPauliBasis_faithful G.pauli (edgePairedSpace_isOrientedFrame (meshAt_pos hL k j))
theorem extendOddly_congr (hL : Conventions.IsAdmissibleBlockingFactor L) {j : ℕ}
    {f g : Edge L k j → ComplexMatrix2}
    (h : ∀ e : Edge L k j, e.IsPositivelyOriented → f e = g e) :
    extendOddly f = extendOddly g := by
  funext e
  by_cases he : e.IsPositivelyOriented
  · simp [extendOddly, he, h e he]
  · have hr : e.opposite.IsPositivelyOriented := by
      rcases (edgePairedSpace_isOrientedFrame (meshAt_pos hL k j)).xor e with ⟨h₁, _⟩ | ⟨h₁, _⟩
      · exact absurd h₁ he
      · exact h₁
    simp [extendOddly, he, h _ hr]
theorem ofCoeffs_unit_eq_basisForm (hL : Conventions.IsAdmissibleBlockingFactor L)
    (ι : Fin 3 × PositiveEdge (meshAt L k 0)) :
    (edgePauliCoordinates L k 0).ofCoeffs (fun κ => unitKernel _ κ ι) =
      basisForm (L := L) (k := k) (j := 0) ι.1 ι.2 := by
  classical
  have x₁ : (edgePauliCoordinates L k 0).ofCoeffs (fun κ => unitKernel _ κ ι) =
      extendOddly (a := meshAt L k 0) (fun e => if h : e.IsPositivelyOriented then
        ofPauliCoeffs (fun κ : Fin 3 × PositiveEdge (meshAt L k 0) => unitKernel _ κ ι)
          ⟨e, h⟩ else 0) := rfl
  have x₂ : basisForm (L := L) (k := k) (j := 0) ι.1 ι.2 =
      extendOddly (a := meshAt L k 0)
        (fun e' => if e' = ι.2.1 then ComplexMatrix2.pauliFamily ι.1 else 0) := rfl
  rw [x₁, x₂]
  refine extendOddly_congr (k := k) (j := 0) hL fun e he => ?_
  obtain ⟨a, ⟨e₀, h₀⟩⟩ := ι
  rw [dif_pos he]
  by_cases x : e = e₀
  · subst x
    simp [ofPauliCoeffs, unitKernel, Prod.ext_iff]
  · have x' : ∀ a', (((a', ⟨e, he⟩) : Fin 3 × PositiveEdge (meshAt L k 0)) = (a, ⟨e₀, h₀⟩)) ↔
        False := fun a' => by simp [Prod.ext_iff, x]
    simp [ofPauliCoeffs, unitKernel, x', x]
theorem ofCoeffs_mem_finiteSupportComplexForms (G : Inputs)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    {c : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ} (hc : HasFiniteSupport c) :
    (edgePauliCoordinates L k 0).ofCoeffs c ∈ HessianKernel.finiteSupportComplexForms L k 0 := by
  have hb := edgePauliCoordinates_faithful G hL k 0
  refine ⟨hb.mem c, ?_⟩
  have h : HasFiniteSupp (restrictToPositiveEdges ((edgePauliCoordinates L k 0).ofCoeffs c)) :=
    (hb.support c).2 hc
  refine (h.image Subtype.val).subset ?_
  rintro e ⟨hp, hne⟩
  exact ⟨⟨e, hp⟩, hne, rfl⟩
section MapsWithKernels
open YangMills.Construction.Tower.CovDiffTransposes (HasTransposeKernel matrixKernel)
theorem represents_matrixKernel {r r' : PauliComponentsOfSymmetricKernel} (hr : IsFaithful r)
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (h : HasTransposeKernel r r' m) :
    Represents (matrixKernel r r' m) (r.mapOnCoeffs r' m) := fun f =>
  ⟨applySummable_of_rowFinite h.row_finite f, by
    funext κ'
    have x := (h.represents _ (hr.mem f) κ').2
    rw [hr.left] at x
    exact x.symm⟩
theorem map_mem_complexSubmodule {r r' : PauliComponentsOfSymmetricKernel}
    {m : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2}
    (h : HasTransposeKernel r r' m) {f : r.space.index → ComplexMatrix2}
    (hf : f ∈ r.space.complexSubmodule) :
    m f ∈ r'.space.complexSubmodule := by
  have x := h.coe_linear ⟨f, hf⟩
  have x' : m f = _ := x.symm
  rw [x']
  exact Subtype.coe_prop _
theorem edgeCoboundary_hasTransposeKernel (G : Inputs)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hU : (fun _ => 1) ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup) :
    HasTransposeKernel (edgePauliCoordinates L k 0) (vertexCoordinate (Face L k 0)) edgeCoboundary :=
  ((G.transposes L hL k 0 (Nat.zero_le k)).2 _ hU).1.edgeCoboundary
theorem mapOnCoeffs_scaledEdgeCoboundary (G : Inputs)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hU : (fun _ => 1) ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup) :
    (edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (Face L k 0)) scaledEdgeCoboundary =
      ((((finestMesh L k)⁻¹ : ℝ)) : ℂ) •
        (edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (Face L k 0)) edgeCoboundary := by
  funext f
  have hq := vertexCoordinate_faithful G.pauli (Face L k 0)
  have hm := map_mem_complexSubmodule (edgeCoboundary_hasTransposeKernel G hL hU)
    ((edgePauliCoordinates_faithful G hL k 0).mem f)
  have x : scaledEdgeCoboundary ((edgePauliCoordinates L k 0).ofCoeffs f) =
      ((((finestMesh L k)⁻¹ : ℝ)) : ℂ) •
        edgeCoboundary ((edgePauliCoordinates L k 0).ofCoeffs f) :=
    real_smul_eq_complex_smul _ _
  exact (congrArg (vertexCoordinate (Face L k 0)).coeffs x).trans (hq.coeffs_smul _ hm)
theorem represents_scaledEdgeCoboundary (G : Inputs)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hU : (fun _ => 1) ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup) :
    Represents (((((finestMesh L k)⁻¹ : ℝ)) : ℂ) •
        matrixKernel (edgePauliCoordinates L k 0) (vertexCoordinate (Face L k 0)) edgeCoboundary)
      ((edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (Face L k 0)) scaledEdgeCoboundary) := by
  have mw := edgeCoboundary_hasTransposeKernel G hL hU
  rw [mapOnCoeffs_scaledEdgeCoboundary G hL hU]
  exact represents_smul mw.row_finite (represents_matrixKernel (edgePauliCoordinates_faithful G hL k 0) mw) _
theorem kernel_scaledEdgeCoboundary (G : Inputs)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hU : (fun _ => 1) ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup) :
    (edgePauliCoordinates L k 0).kernel (vertexCoordinate (Face L k 0)) scaledEdgeCoboundary =
      ((((finestMesh L k)⁻¹ : ℝ)) : ℂ) •
        matrixKernel (edgePauliCoordinates L k 0) (vertexCoordinate (Face L k 0)) edgeCoboundary :=
  kernelOfMap_eq (represents_scaledEdgeCoboundary G hL hU)
theorem H_one (G : Inputs) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hU : (fun _ => 1) ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup) :
    (rescaledOperators L k fun _ => 1).H =
      compKernel
        (meshTranspose (finestMesh L k) (finestMesh L k)
          ((edgePauliCoordinates L k 0).kernel (vertexCoordinate (Face L k 0)) scaledEdgeCoboundary))
        ((edgePauliCoordinates L k 0).kernel (vertexCoordinate (Face L k 0)) scaledEdgeCoboundary) := by
  classical
  have hd := kernel_scaledEdgeCoboundary G hL hU
  generalize (edgePauliCoordinates L k 0).kernel (vertexCoordinate (Face L k 0))
    scaledEdgeCoboundary = d at hd ⊢
  have mw := edgeCoboundary_hasTransposeKernel G hL hU
  have hb := edgePauliCoordinates_faithful G hL k 0
  have hq := vertexCoordinate_faithful G.pauli (Face L k 0)
  obtain ⟨η, hηdef⟩ : ∃ η, η = finestMesh L k := ⟨_, rfl⟩
  have hη : 0 < η := hηdef ▸ meshAt_pos hL k 0
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have hw : 0 < η ^ 4 := pow_pos hη 4
  rw [← hηdef] at hd
  have hdr : RowFinite d := hd ▸ rowFinite_smul mw.row_finite _
  have hdc : ColumnFinite d := hd ▸ columnFinite_smul mw.column_finite _
  have hdt := wTranspose_rowFinite hdc (η ^ 4) (η ^ 4)
  obtain ⟨T, hTdef⟩ : ∃ T, T = compKernel (wTranspose
    (fun _ : Fin 3 × PositiveEdge (meshAt L k 0) => η ^ 4)
    (fun _ : Fin 3 × Face L k 0 => η ^ 4) d) d := ⟨_, rfl⟩
  have hT : RowFinite T := hTdef ▸ ((G.kernels.1 _ _ d hdr).2 _ _ hdt).2.1
  have hsym : ∀ ι ι', T ι ι' = T ι' ι := fun ι ι' => by
    rw [hTdef]
    show ∑' κ, _ = ∑' κ, _
    exact tsum_congr fun κ => by
      simp only [wTranspose]
      ring
  let Gc : (Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) → Edge L k 0 → ComplexMatrix2 :=
    fun c => (edgePauliCoordinates L k 0).ofCoeffs ((η : ℂ) • c)
  let β : (Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) →
      (Fin 3 × PositiveEdge (meshAt L k 0) → ℂ) → ℂ :=
    fun c c' => complexActionHessian (fun _ => 1) (Gc c) (Gc c')
  have hmem : ∀ c, HasFiniteSupport c →
      Gc c ∈ HessianKernel.finiteSupportComplexForms L k 0 := fun c hc =>
    ofCoeffs_mem_finiteSupportComplexForms G hL (Set.Finite.subset hc fun ι h h0 => h (by
      have h0' : c ι = 0 := h0
      simp [h0']))
  have hA := ((G.second L hL k 0 (Nat.zero_le k)).2 _ hU).1
  have hG_add : ∀ (z : ℂ) f g, Gc (z • f + g) = z • Gc f + Gc g := fun z f g => by
    have x₁ : (η : ℂ) • (z • f + g) = z • ((η : ℂ) • f) + (η : ℂ) • g := by
      rw [smul_add, smul_comm]
    exact (congrArg (edgePauliCoordinates L k 0).ofCoeffs x₁).trans
      ((hb.add (z • ((η : ℂ) • f)) ((η : ℂ) • g)).trans
        (congrArg (fun X => X + (edgePauliCoordinates L k 0).ofCoeffs ((η : ℂ) • g))
          (hb.smul z ((η : ℂ) • f))))
  have hbil : PolarisedKernel.IsSymmBilinearOnFinite β :=
    ⟨fun z f g h hf hg hh => by
      show complexActionHessian _ (Gc (z • f + g)) (Gc h) = _
      rw [hG_add]
      exact (hA z _ (hmem f hf) _ (hmem g hg) _ (hmem h hh)).1,
    fun f g hf hg => (hA 0 _ (hmem f hf) _ (hmem f hf) _ (hmem g hg)).2.2⟩
  have hquad : ∀ c, HasFiniteSupport c →
      β c c = wPairing (fun _ => η ^ 4) c (applyKernel T c) := fun c hc => by
    have hBm := hmem c hc
    have hform := (((G.plaquette L hL k 0 (Nat.zero_le k)).2 (Gc c) hBm.1).2 hBm.2).2
    show complexActionHessian _ _ _ = _
    rw [hform, hTdef]
    refine Eq.trans ?_ (wPairing_transpose_comp G.kernels hdr hdc hw hc).symm
    have hv := applyKernel_hasFiniteSupport hdc hc
    have hsq : toPauliCoeffs (edgeCoboundary (Gc c)) =
        ((η : ℂ) ^ 2) • applyKernel d c := by
      have x₁ : toPauliCoeffs (edgeCoboundary (Gc c)) =
          applyKernel (matrixKernel (edgePauliCoordinates L k 0)
            (vertexCoordinate (Face L k 0)) edgeCoboundary) ((η : ℂ) • c) :=
        ((represents_matrixKernel hb mw _).2).symm
      obtain ⟨u, hu⟩ : ∃ u, u = applyKernel (matrixKernel (edgePauliCoordinates L k 0)
          (vertexCoordinate (Face L k 0)) edgeCoboundary) c := ⟨_, rfl⟩
      have x₂ : applyKernel (matrixKernel (edgePauliCoordinates L k 0)
          (vertexCoordinate (Face L k 0)) edgeCoboundary) ((η : ℂ) • c) =
          (η : ℂ) • u := hu ▸ applyKernel_smul _ _ _
      have x₃ : applyKernel d c = (((η⁻¹ : ℝ)) : ℂ) • u := by
        rw [hd, hu]
        exact applyKernel_smul_kernel _ _ _
      have x₄ : (η : ℂ) • u = ((η : ℂ) ^ 2) • ((((η⁻¹ : ℝ)) : ℂ) • u) := by
        rw [smul_smul]
        congr 1
        push_cast
        field_simp
      exact x₁.trans (x₂.trans (x₄.trans (by rw [x₃])))
    have hpB : edgeCoboundary (Gc c) = ofPauliCoeffs (((η : ℂ) ^ 2) • applyKernel d c) := by
      rw [← hsq]
      exact (hq.right _ (map_mem_complexSubmodule mw (hb.mem _))).symm
    have hv' : (Function.support (((η : ℂ) ^ 2) • applyKernel d c)).Finite :=
      Set.Finite.subset hv fun ι h h0 => h (by
        have h0' : applyKernel d c ι = 0 := h0
        simp [h0'])
    rw [hpB]
    refine (traceFinsumPairing_ofPauliCoeffs G.pauli
      (((η : ℂ) ^ 2) • applyKernel d c) _ hv').trans ?_
    refine Eq.trans ?_ (mul_finsum _ _).symm
    refine finsum_congr fun ι => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have x : ∀ ι : Fin 3 × PositiveEdge (meshAt L k 0),
      η • basisForm (L := L) (k := k) (j := 0) ι.1 ι.2 =
        Gc (fun κ => unitKernel _ κ ι) := fun ι => by
    exact ((real_smul_eq_complex_smul η _).trans (congrArg (fun X => (η : ℂ) • X)
      (ofCoeffs_unit_eq_basisForm hL ι).symm)).trans
        (hb.smul (η : ℂ) fun κ => unitKernel _ κ ι).symm
  funext ι ι'
  have h := G.polarisation _ T (η ^ 4) β hT hsym hbil hquad ι ι'
  have hg : compKernel (meshTranspose (finestMesh L k) (finestMesh L k) d) d ι ι' =
      T ι ι' := by
    rw [hTdef, ← hηdef]
    rfl
  rw [hg]
  show (((finestMesh L k ^ 4)⁻¹ : ℝ) : ℂ) * complexActionHessian (fun _ => 1)
    (finestMesh L k • basisForm ι.1 ι.2)
    (finestMesh L k • basisForm ι'.1 ι'.2) = _
  rw [← hηdef, x, x]
  show _ * β _ _ = _
  rw [h]
  push_cast
  field_simp
end MapsWithKernels
theorem covDiff_one_of_pos {j : ℕ} (l : Vertex L k j → ComplexMatrix2) (e : Edge L k j)
    (he : e.IsPositivelyOriented) : covDiff (fun _ => 1) l e = vertexCoboundary l e := by
  simp [covDiff, extendOddly, he, vertexCoboundary, ComplexMatrix2.conjugateBy]
end FullTower
theorem holds
    (h₁ : RescaledIterRelations)
    (h₂ : RescaledTrivialSteps)
    (h₃ : RescaledKernelAlgebra.Claim)
    (h₄ : PolarisedKernel.ValueAtUnits)
    (h₅ : CovDiffTransposes.Claim)
    (h₆ : FaceTermDerivatives.Statement)
    (h₇ : HessianKernel.KernelProperties)
    (h₈ : RowFiniteKernels.Claim)
    (h₉ : OneLoop.PauliMatrixRelations)
    (h₁₀ : Tower.TwoLevelMaps.Statement) : RescaledTrivialRelations := by
  have G : Inputs := ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩
  intro L hL k hk
  obtain ⟨hU, hs⟩ := G.steps L hL k hk
  have hU0 : (fun _ => 1) ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup := hU.1
  have hrel := G.relations L hL k hk _ hU
  have hblock := complexIter_one hs k le_rfl
  have hb := edgePauliCoordinates_faithful G hL k 0
  have hr := vertexCoordinate_faithful G.pauli (Vertex L k 0)
  have hSiteMap : (vertexCoordinate (Vertex L k 0)).mapOnCoeffs (edgePauliCoordinates L k 0)
        scaledVertexCoboundary =
      (vertexCoordinate (Vertex L k 0)).mapOnCoeffs (edgePauliCoordinates L k 0)
        fun l => (finestMesh L k)⁻¹ • covDiff (fun _ => 1) l := by
    funext f ι
    show pauliCoeff ι.1 (((meshAt L k 0)⁻¹ • vertexCoboundary _) ι.2.1) =
      pauliCoeff ι.1 (((finestMesh L k)⁻¹ • covDiff _ _) ι.2.1)
    rw [Pi.smul_apply, Pi.smul_apply]
    exact congrArg (fun X => pauliCoeff ι.1 ((finestMesh L k)⁻¹ • X))
      (covDiff_one_of_pos (L := L) (k := k) (j := 0) _ ι.2.1 ι.2.2).symm
  have hTopMap : (vertexCoordinate (Vertex L k k)).mapOnCoeffs (edgePauliCoordinates L k k)
        scaledVertexCoboundary =
      (vertexCoordinate (Vertex L k k)).mapOnCoeffs (edgePauliCoordinates L k k)
        (covDiff (complexIter L k k fun _ => 1)) := by
    rw [hblock]
    funext f ι
    show pauliCoeff ι.1 (((meshAt L k k)⁻¹ • vertexCoboundary _) ι.2.1) =
      pauliCoeff ι.1 (covDiff _ _ ι.2.1)
    have x₀ : ∀ X : ComplexMatrix2, (meshAt L k k)⁻¹ • X = X := fun X => by
      rw [meshAt_self hL, inv_one, one_smul]
    rw [Pi.smul_apply, x₀]
    exact congrArg _ (covDiff_one_of_pos (L := L) (k := k) (j := k) _ ι.2.1 ι.2.2).symm
  have hD : (rescaledOperators L k fun _ => 1).D =
      (vertexCoordinate (Vertex L k 0)).kernel (edgePauliCoordinates L k 0) scaledVertexCoboundary :=
    (congrArg kernelOfMap hSiteMap).symm
  have hTop : (vertexCoordinate (Vertex L k k)).kernel (edgePauliCoordinates L k k) scaledVertexCoboundary =
      covDiffKernel L k k (complexIter L k k fun _ => 1) :=
    congrArg kernelOfMap hTopMap
  have hQ : Represents (rescaledOperators L k fun _ => 1).Q
      ((edgePauliCoordinates L k 0).mapOnCoeffs (edgePauliCoordinates L k k) fun B' =>
        (rescaledOperators L k fun _ => 1).eta • crossingSmoothingIter L k k B') := by
    have x : ((edgePauliCoordinates L k 0).mapOnCoeffs (edgePauliCoordinates L k k) fun B' =>
          (rescaledOperators L k fun _ => 1).eta • crossingSmoothingIter L k k B') =
        (edgePauliCoordinates L k 0).mapOnCoeffs (edgePauliCoordinates L k k) fun B' =>
          (rescaledOperators L k fun _ => 1).eta •
            iterCovariantDeriv L k (fun _ => 1) k B' := by
      funext f
      show (edgePauliCoordinates L k k).coeffs (_ • crossingSmoothingIter L k k _) =
        (edgePauliCoordinates L k k).coeffs (_ • iterCovariantDeriv L k _ k _)
      rw [(iterCovariantDeriv_one G hL hk hs (hb.mem f) k le_rfl).1]
    rw [x]
    exact hrel.Q_represents
  have hR : Represents (rescaledOperators L k fun _ => 1).R
      ((vertexCoordinate (Vertex L k 0)).mapOnCoeffs (vertexCoordinate (Vertex L k k))
        (vertexSmoothingIter L k k)) := by
    have x : (vertexCoordinate (Vertex L k 0)).mapOnCoeffs (vertexCoordinate (Vertex L k k))
          (vertexSmoothingIter L k k) =
        (vertexCoordinate (Vertex L k 0)).mapOnCoeffs (vertexCoordinate (Vertex L k k))
          (iterAdjointCubeAverage L k (fun _ => 1) k) := by
      funext f
      show (vertexCoordinate (Vertex L k k)).coeffs (vertexSmoothingIter L k k _) =
        (vertexCoordinate (Vertex L k k)).coeffs (iterAdjointCubeAverage L k _ k _)
      rw [(iterAdjointCubeAverage_one hs (hr.mem f) k le_rfl).1]
    rw [x]
    exact hrel.R_represents
  obtain ⟨rR, rQ, rD, rDW, rRt, rDt⟩ := hrel.row_finite
  have mw := edgeCoboundary_hasTransposeKernel G hL hU0
  have hdk := kernel_scaledEdgeCoboundary G hL hU0
  have hdr : RowFinite ((edgePauliCoordinates L k 0).kernel (vertexCoordinate (Face L k 0))
      scaledEdgeCoboundary) := hdk ▸ rowFinite_smul mw.row_finite _
  have hdc : ColumnFinite ((edgePauliCoordinates L k 0).kernel (vertexCoordinate (Face L k 0))
      scaledEdgeCoboundary) := hdk ▸ columnFinite_smul mw.column_finite _
  refine trivialRelations_of_kernels G.kernels G.algebra (meshAt_pos hL k 0) (meshAt_pos hL k k)
    ?_ ?_ ?_ hD hQ hR hdr (wTranspose_rowFinite hdc _ _) (hTop ▸ rDW) rQ rR rRt rD rDt
    hrel.R_comp_Rt ?_ (H_one G hL hU0)
  · rw [← hD, hSiteMap]
    exact hrel.D_represents
  · rw [hdk]
    exact represents_scaledEdgeCoboundary G hL hU0
  · rw [hTop, hTopMap]
    exact hrel.DW_represents
  · rw [← hD, hTop]
    exact hrel.Q_comp_D
end YangMills.Construction.Tower.FullSpace.RescaledTrivialRelationsProof
end
