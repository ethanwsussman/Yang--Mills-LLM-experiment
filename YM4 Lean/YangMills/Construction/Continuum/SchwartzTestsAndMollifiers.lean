import YangMills.Construction.Continuum.ActionsOfMotionsAndTheSequencesOfTensorsOverTheUpperHalfSpace
import YangMills.Construction.Continuum.NormsBallsDistancesAndSupportsInFourSpace
import YangMills.Construction.Continuum.OpenHalvesAndFlatnessOutsideAnOpenSet
import YangMills.Construction.Continuum.SeparatedTuplesAsListsAndAsMaps
import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.WightmanReconstruction
open TestSpaces Motions
open TorusMetric (euclidNormVec)
theorem actOnFun_translateMotion {n : ℕ} {F : Type*} (v : Fin 4 → ℝ) (φ : PointTuple n → F)
    (x : PointTuple n) :
    actOnFun (UpperHalfTensors.translateMotion v) φ x = φ fun i => x i - v := by
  simp [actOnFun, RigidMotion.invFun, UpperHalfTensors.translateMotion]
section FunctionClasses
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (E F) in
def smoothMaps : Set (E → F) := {φ | ContDiff ℝ ∞ φ}
def lOneNorm [MeasureSpace E] (φ : E → F) : ℝ := ∫ x, ‖φ x‖
end FunctionClasses
def schwartzPlus (n : ℕ) : Set (PointTuple n → ℂ) :=
  {φ | φ ∈ schwartzSet n ∧ VanishesToInfiniteOrderOff φ (positiveTimeLocus n)}
def schwartzOfOrder : (n : ℕ) → Set (TensorVal ℂ n)
  | 0 => Set.univ
  | n + 1 => schwartzSet (n + 1)
def scalarOfOrderZero (c : TensorVal ℂ 0) : ℂ := c
def weightedSeminormOfOrder (k : ℕ) : {n : ℕ} → TensorVal ℂ n → ℝ≥0∞
  | 0, c => ENNReal.ofReal ‖scalarOfOrderZero c‖
  | _ + 1, φ => weightedSeminorm k φ
def actOfOrder (r : RigidMotion) : {n : ℕ} → TensorVal ℂ n → TensorVal ℂ n
  | 0, c => c
  | _ + 1, φ => actOnFun r φ
def smoothDisjointTuples (O : Set (Fin 4 → ℝ)) (n : ℕ) : Set (Fin n → (Fin 4 → ℝ) → ℝ) :=
  {f | f ∈ disjointSupportTuples O n ∧ HasSmoothComponents O f}
def smoothSupportedIn (O : Set (Fin 4 → ℝ)) : Set SeparatedTuples.SepTuple :=
  {X | X ∈ SeparatedTuples.supportedIn O ∧ ∀ f ∈ X.1, f ∈ smoothCompactSupp O}
def permuteComponents {n : ℕ} (X : SepTupleOfCard n) (ς : Equiv.Perm (Fin n)) : SepTupleOfCard n :=
  ⟨fun i => X.1 (ς i), fun i => X.2.1 (ς i), fun _ _ hij => X.2.2 (ς.injective.ne hij)⟩
def IsPermutationInvariant (σ : TestSpaces.SepTuple → ℝ) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (X : SepTupleOfCard n) (ς : Equiv.Perm (Fin n)),
    σ ⟨n, permuteComponents X ς⟩ = σ ⟨n, X⟩
def IsMotionInvariant (σ : TestSpaces.SepTuple → ℝ) (r : RigidMotion) : Prop :=
  ∀ X : TestSpaces.SepTuple, σ (UpperHalfTensors.actOnSTuple r X) = σ X
def linearExtension (σ : TestSpaces.SepTuple → ℝ) : SeparatedTuples.FormalSpan →ₗ[ℂ] ℂ :=
  SeparatedTuples.linearExtend fun X => ((σ (TupleLists.ofList X) : ℝ) : ℂ)
theorem isDisjointlySupported_of_mem_sepAll {X : EuclideanFunctionals.FnList}
    (hX : X ∈ EuclideanFunctionals.sepAll) : SeparatedTuples.IsDisjointlySupported X := by
  have hs := EuclideanFunctionals.isSeparatedList_of_mem_sepAll hX
  refine ⟨fun f hf => ?_, ?_⟩
  · have hc := hs.1 f hf
    rw [← FourSpace.C1c_eq_compactC1] at hc
    exact ⟨hc.1, hc.2⟩
  · refine hs.2.imp ?_
    intro f g hfg
    exact (congrArg₂ (Disjoint (α := Set (Fin 4 → ℝ)))
      (FourSpace.closedSupport_euclidean_eq_tsupport EuclideanFunctionals.defaultMirrorData f)
      (FourSpace.closedSupport_euclidean_eq_tsupport EuclideanFunctionals.defaultMirrorData g)).mp
      hfg
def toSepTuple (X : EuclideanFunctionals.sepAll) : SeparatedTuples.SepTuple :=
  ⟨X.1, isDisjointlySupported_of_mem_sepAll X.2⟩
def freeToFormalSpan : EuclideanFunctionals.FreeSep →ₗ[ℂ] SeparatedTuples.FormalSpan :=
  EuclideanFunctionals.liftLin fun X => SeparatedTuples.basisVec (toSepTuple X)
def complexTuple (h : (Fin 4 → ℝ) → ℂ) : SeparatedTuples.FormalSpan :=
  freeToFormalSpan (EuclideanFunctionals.complexList (n := 1) fun _ => h)
theorem complexTuple_ofReal (f : (Fin 4 → ℝ) → ℝ)
    (hf : [f] ∈ EuclideanFunctionals.sepAll) :
    complexTuple (fun x => (f x : ℂ)) =
      SeparatedTuples.basisVec (toSepTuple ⟨[f], hf⟩) := by
  have h := EuclideanFunctionals.complexList_ofReal (n := 1) fun _ => f
  have hl : List.ofFn (fun _ : Fin 1 => f) = [f] := rfl
  rw [hl] at h
  rw [complexTuple, h, freeToFormalSpan]
  exact EuclideanFunctionals.liftLin_toFree _ ⟨[f], hf⟩
theorem complexTuple_of_not_real (h : (Fin 4 → ℝ) → ℂ) (hn : ¬∀ x, (h x).im = 0)
    (hre : [fun x => (h x).re] ∈ EuclideanFunctionals.sepAll)
    (him : [fun x => (h x).im] ∈ EuclideanFunctionals.sepAll) :
    complexTuple h =
      SeparatedTuples.basisVec (toSepTuple ⟨_, hre⟩) +
        Complex.I • SeparatedTuples.basisVec (toSepTuple ⟨_, him⟩) := by
  have hI : EuclideanFunctionals.nonrealIdx (n := 1) (fun _ => h) = {0} := by
    ext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    simp [EuclideanFunctionals.nonrealIdx, hn]
  have hm : (0 : Fin 1) ∈ EuclideanFunctionals.nonrealIdx (n := 1) (fun _ => h) := by
    rw [hI]
    exact Finset.mem_singleton_self _
  let _ : Unique (EuclideanFunctionals.nonrealIdx (n := 1) (fun _ => h)) :=
    ⟨⟨⟨0, hm⟩⟩, fun k => Subtype.ext (Subsingleton.elim _ _)⟩
  have hsum : EuclideanFunctionals.complexList (n := 1) (fun _ => h) =
      EuclideanFunctionals.toFree [fun x => (h x).re] +
        Complex.I • EuclideanFunctionals.toFree [fun x => (h x).im] := by
    rw [EuclideanFunctionals.complexList,
      ← (Equiv.funUnique (EuclideanFunctionals.nonrealIdx (n := 1) (fun _ => h))
        (Fin 2)).symm.sum_comp, Fin.sum_univ_two]
    have hc : ∀ (e : Fin 2), EuclideanFunctionals.imagCount (n := 1) (fun _ => h)
        ((Equiv.funUnique _ (Fin 2)).symm e) = (e : ℕ) := fun e => by
      simp [EuclideanFunctionals.imagCount]
    have he : ∀ (e : Fin 2), List.ofFn (EuclideanFunctionals.realPartComponent (n := 1) (fun _ => h)
        ((Equiv.funUnique _ (Fin 2)).symm e)) =
          [if e = 0 then fun x => (h x).re else fun x => (h x).im] := fun e => by
      have hv : (Equiv.funUnique (EuclideanFunctionals.nonrealIdx (n := 1) (fun _ => h))
          (Fin 2)).symm e ⟨0, hm⟩ = e :=
        (Equiv.funUnique (EuclideanFunctionals.nonrealIdx (n := 1) (fun _ => h))
          (Fin 2)).apply_symm_apply e
      simp only [EuclideanFunctionals.realPartComponent, hm, List.ofFn_succ, List.ofFn_zero, dite_true,
        hv]
    rw [hc, hc, he, he]
    simp
  rw [complexTuple, hsum, map_add, map_smul, freeToFormalSpan]
  rw [show EuclideanFunctionals.liftLin
      (fun X => SeparatedTuples.basisVec (toSepTuple X))
      (EuclideanFunctionals.toFree [fun x => (h x).re]) = _ from
    EuclideanFunctionals.liftLin_toFree _ ⟨_, hre⟩]
  rw [show EuclideanFunctionals.liftLin
      (fun X => SeparatedTuples.basisVec (toSepTuple X))
      (EuclideanFunctionals.toFree [fun x => (h x).im]) = _ from
    EuclideanFunctionals.liftLin_toFree _ ⟨_, him⟩]
def IsCutSequence {n : ℕ} (X : Fin n → (Fin 4 → ℝ) → ℝ) (c : Fin (n + 1) → ℝ) : Prop :=
  StrictMono c ∧ ∀ i : Fin n, tsupport (X i) ⊆ {x | c i.castSucc < x 3 ∧ x 3 < c i.succ}
def IsTimeOrdered {n : ℕ} (X : Fin n → (Fin 4 → ℝ) → ℝ) : Prop :=
  X ∈ disjointSupportTuples (Set.univ : Set (Fin 4 → ℝ)) n ∧ ∃ c, IsCutSequence X c
def supC1Norm (f : (Fin 4 → ℝ) → ℂ) : ℝ :=
  TestFunctions.uniformNorm f + ⨆ x, Real.sqrt (∑ μ, ‖TestFunctions.partialDerivR4 μ f x‖ ^ 2)
def IsStandardMollifier (j : (Fin 4 → ℝ) → ℝ) : Prop :=
  j ∈ smoothCompactSupp (Set.univ : Set (Fin 4 → ℝ)) ∧ (∀ x, 0 ≤ j x) ∧ ∫ x, j x = 1 ∧
    (∀ x, 1 ≤ euclidNormVec x → j x = 0) ∧
    ∀ R ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∀ x, j (R.mulVec x) = j x
def stdMollifier : (Fin 4 → ℝ) → ℝ := Classical.epsilon IsStandardMollifier
theorem isStandardMollifier_stdMollifier (h : ∃ j, IsStandardMollifier j) :
    IsStandardMollifier stdMollifier :=
  Classical.epsilon_spec h
def scaledMollifier (ε : ℝ) (x : Fin 4 → ℝ) : ℝ := ε ^ (-4 : ℤ) * stdMollifier (ε⁻¹ • x)
def tensorMollifier (ε : ℝ) (n : ℕ) : PointTuple n → ℝ := tensorProd fun _ => scaledMollifier ε
end YangMills.Construction.WightmanReconstruction
