import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes.FourthPartProof
import YangMills.Construction.GrowingTori.TorusFunctionalsReadOnTuplesOfFourSpaceProof
import YangMills.Construction.GrowingTori.TransportThroughTheBallClassC1OnATorusAndInducedIsometries
import YangMills.Construction.Continuum.PictureOfAFunctionOnSymbolsAtAnotherMirror
import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes.FifthPartProof
import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes.SecondPartProof
import YangMills.Construction.GrowingTori.LimitsAlongGrowingVolumes.ThirdPartProof
import Mathlib
set_option autoImplicit false
open Set
open scoped NNReal ENNReal ComplexConjugate
namespace YangMills.Construction
section
open Set Filter Topology
open scoped NNReal ENNReal ComplexConjugate ContDiff
noncomputable section
namespace ToriLimits.GrowingVolumeLimits.ProofSteps.AtEveryMirror
open CentredTensorMoments (conjReflectTest tupleTensor realTupleTensor)
open PeriodicSpace TorusTransport.TestFunctionOrders
def reflOrder : ℕ → ℕ → ℕ
  | 0, 0 => 0
  | 0, q + 1 => q + 1
  | p + 1, 0 => p + 1
  | p + 1, q + 1 => p + 1 + (q + 1)
def reflProduct (μ : Fin 4) (c : ℝ) : {q q' : ℕ} → OrderedTestFun q →
    OrderedTestFun q' → OrderedTestFun (reflOrder q q')
  | 0, 0, A, B => conj (A : ℂ) * (B : ℂ)
  | 0, _ + 1, A, B => fun x => conj (A : ℂ) * B x
  | _ + 1, 0, A, B => fun x => (B : ℂ) * conjReflectTest μ c A x
  | p + 1, q + 1, A, B =>
      tensor (p := p + 1) (q := q + 1) (conjReflectTest μ c A) B
theorem reflectedTensor_eq (μ : Fin 4) (c : ℝ) (F F' : TestFamily) (q q' : ℕ) :
    reflectedTensor μ c F F' q q' = ⟨reflOrder q q', reflProduct μ c (F q) (F' q')⟩ := by
  cases q <;> cases q' <;> rfl
theorem reflProduct_add_smul_right (μ : Fin 4) (c : ℝ) {q q' : ℕ} (A : OrderedTestFun q)
    (B B' : OrderedTestFun q') (a b : ℂ) :
    reflProduct μ c A (a • B + b • B') =
      a • reflProduct μ c A B + b • reflProduct μ c A B' := by
  cases q <;> cases q'
  · show conj A * (a * B + b * B') = a * (conj A * B) + b * (conj A * B')
    ring
  · funext x
    show conj A * (a * B x + b * B' x) = a * (conj A * B x) + b * (conj A * B' x)
    ring
  · funext x
    show (a * B + b * B') * _ = a * (B * _) + b * (B' * _)
    ring
  · funext x
    show _ * (a * _ + b * _) = a * (_ * _) + b * (_ * _)
    ring
theorem conjReflectTest_add_smul (μ : Fin 4) (c : ℝ) {q : ℕ} (A A' : OrderedTestFun q)
    (a b : ℂ) : conjReflectTest μ c (a • A + b • A') =
      conj a • conjReflectTest μ c A + conj b • conjReflectTest μ c A' := by
  cases q with
  | zero =>
    show conj (a * A + b * A') = conj a * conj A + conj b * conj A'
    simp
  | succ q =>
    funext x
    show conj (a * _ + b * _) = conj a * conj _ + conj b * conj _
    simp
theorem reflProduct_add_smul_left (μ : Fin 4) (c : ℝ) {q q' : ℕ} (A A' : OrderedTestFun q)
    (B : OrderedTestFun q') (a b : ℂ) :
    reflProduct μ c (a • A + b • A') B =
      conj a • reflProduct μ c A B + conj b • reflProduct μ c A' B := by
  cases q <;> cases q'
  · show conj (a * A + b * A') * B = conj a * (conj A * B) + conj b * (conj A' * B)
    simp only [map_add, map_mul]
    ring
  · funext x
    show conj (a * A + b * A') * B x = conj a * (conj A * B x) + conj b * (conj A' * B x)
    simp only [map_add, map_mul]
    ring
  · funext x
    have h := congrFun (conjReflectTest_add_smul μ c A A' a b) x
    show B * conjReflectTest μ c (a • A + b • A') x =
      conj a * (B * conjReflectTest μ c A x) +
        conj b * (B * conjReflectTest μ c A' x)
    rw [h]
    show B * (conj a * _ + conj b * _) = _
    ring
  · rename_i p r
    funext x
    have h := congrFun (conjReflectTest_add_smul μ c A A' a b) (initPoints (p := p + 1) (q := r + 1) x)
    show conjReflectTest μ c (a • A + b • A') (initPoints (p := p + 1) (q := r + 1) x) *
        B (tailPoints (p := p + 1) (q := r + 1) x) =
      conj a * (conjReflectTest μ c A (initPoints (p := p + 1) (q := r + 1) x) *
          B (tailPoints (p := p + 1) (q := r + 1) x)) +
        conj b * (conjReflectTest μ c A' (initPoints (p := p + 1) (q := r + 1) x) *
          B (tailPoints (p := p + 1) (q := r + 1) x))
    rw [h]
    show (conj a * _ + conj b * _) * _ = _
    ring
end ToriLimits.GrowingVolumeLimits.ProofSteps.AtEveryMirror
end
end
section
open Set Filter Topology
open scoped NNReal ENNReal ComplexConjugate ContDiff
noncomputable section
namespace ToriLimits.GrowingVolumeLimits.ProofSteps.AtEveryMirror
open CentredTensorMoments (conjReflectTest tupleTensor realTupleTensor)
open PeriodicSpace TorusTransport.TestFunctionOrders
abbrev hyperplaneFlip (μ : Fin 4) (c : ℝ) : Equiv.Perm (Fin 4 → ℝ) :=
  (BallPeriodization.hyperplaneReflection μ c : Equiv.Perm (Fin 4 → ℝ))
theorem hyperplaneFlip_apply (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    hyperplaneFlip μ c x = x - (2 * (x μ - c)) • PeriodicLattice.coordVec μ := by apply _root_.YangMills.Construction.BallPeriodization.hyperplaneReflection_apply <;> assumption
theorem continuous_hyperplaneFlip (μ : Fin 4) (c : ℝ) : Continuous (hyperplaneFlip μ c) := by apply _root_.YangMills.Construction.CentredTensorMoments.TorusFunctionals.continuous_axisRefl <;> assumption
theorem hyperplaneFlip_hyperplaneFlip (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    hyperplaneFlip μ c (hyperplaneFlip μ c x) = x := by apply _root_.YangMills.Construction.CentredTensorMoments.TorusFunctionals.axisRefl_axisRefl <;> assumption
theorem hyperplaneFlip_apply_self (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    hyperplaneFlip μ c x μ = 2 * c - x μ := by apply _root_.YangMills.Construction.CentredTensorMoments.TorusFunctionals.axisRefl_apply_self <;> assumption
def hyperplaneFlipHomeomorph (μ : Fin 4) (c : ℝ) : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toFun := hyperplaneFlip μ c
  invFun := hyperplaneFlip μ c
  left_inv := hyperplaneFlip_hyperplaneFlip μ c
  right_inv := hyperplaneFlip_hyperplaneFlip μ c
  continuous_toFun := continuous_hyperplaneFlip μ c
  continuous_invFun := continuous_hyperplaneFlip μ c
theorem tsupport_comp_hyperplaneFlip (μ : Fin 4) (c : ℝ) (f : (Fin 4 → ℝ) → ℝ) :
    tsupport (f ∘ hyperplaneFlip μ c) = hyperplaneFlip μ c ⁻¹' tsupport f := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.SymbolPairing.tsupport_comp_axisReflect <;> assumption
theorem contDiff_hyperplaneFlip (μ : Fin 4) (c : ℝ) {m : WithTop ℕ∞} :
    ContDiff ℝ m (hyperplaneFlip μ c) := by
  have h : ⇑(hyperplaneFlip μ c) = fun x => x - (2 * (x μ - c)) • PeriodicLattice.coordVec μ :=
    funext (hyperplaneFlip_apply μ c)
  rw [h]
  have h₁ : ContDiff ℝ m fun x : Fin 4 → ℝ => x μ := contDiff_apply ℝ ℝ μ
  exact contDiff_id.sub (((contDiff_const.mul (h₁.sub contDiff_const))).smul contDiff_const)
structure IsSeparatedFamily (m : WithTop ℕ∞) (O : Set (Fin 4 → ℝ)) {n : ℕ}
    (X : Fin n → (Fin 4 → ℝ) → ℝ) : Prop where
  contDiff : ∀ l, ContDiff ℝ m (X l)
  isCompact : ∀ l, IsCompact (tsupport (X l))
  disj : ∀ l l', l ≠ l' → Disjoint (tsupport (X l)) (tsupport (X l'))
  subset_open : ∀ l, tsupport (X l) ⊆ O
def sepRealTensors (m : WithTop ℕ∞) (O : Set (Fin 4 → ℝ)) (q : ℕ) : Set (OrderedTestFun q) :=
  {F | ∃ X : Fin q → (Fin 4 → ℝ) → ℝ, IsSeparatedFamily m O X ∧ F = realTupleTensor X}
theorem isSeparatedFamily_of_fin_zero (m : WithTop ℕ∞) (O : Set (Fin 4 → ℝ))
    (X : Fin 0 → (Fin 4 → ℝ) → ℝ) : IsSeparatedFamily m O X :=
  ⟨fun l => l.elim0, fun l => l.elim0, fun l => l.elim0, fun l => l.elim0⟩
theorem top_eq_span_sepRealTensors (m : WithTop ℕ∞) (O : Set (Fin 4 → ℝ)) :
    (⊤ : Submodule ℂ (OrderedTestFun 0)) = Submodule.span ℂ (sepRealTensors m O 0) := by
  refine (eq_top_iff.2 fun z _ => ?_).symm
  have h1 : (1 : ℂ) ∈ sepRealTensors m O 0 := ⟨Fin.elim0, isSeparatedFamily_of_fin_zero m O _, rfl⟩
  have h : z = z • (1 : ℂ) := by simp
  rw [h]
  exact Submodule.smul_mem _ z (Submodule.subset_span h1)
theorem sepTensorSubmodule_eq_span (Y : PeriodicSpace.Params) (O : Set (Fin 4 → ℝ)) (q : ℕ) :
    sepTensorSubmodule Y O q = Submodule.span ℂ (sepRealTensors 1 O q) := by
  cases q with
  | zero => exact top_eq_span_sepRealTensors 1 O
  | succ q =>
    refine congrArg (Submodule.span ℂ) (Set.ext fun F => ?_)
    constructor
    · rintro ⟨f, ⟨hf, hO⟩, rfl⟩
      obtain ⟨h1, h2, h3⟩ := (BallTuples.mem_sepC1Tuples_euclidean_iff f).1 hf
      refine ⟨f, ⟨h1, h2, h3, fun l => ?_⟩, rfl⟩
      have e : Kind.supportQ Y Kind.euclidean (f l) = @tsupport (Fin 4 → ℝ) ℝ _ _ (f l) :=
        BallTuples.supportQ_euclidean (D := Y) (f l)
      exact e ▸ hO l
    · rintro ⟨f, ⟨h1, h2, h3, h4⟩, rfl⟩
      refine ⟨f, ⟨(BallTuples.mem_sepC1Tuples_euclidean_iff f).2 ⟨h1, h2, h3⟩, fun l => ?_⟩, rfl⟩
      have e : Kind.supportQ Y Kind.euclidean (f l) = @tsupport (Fin 4 → ℝ) ℝ _ _ (f l) :=
        BallTuples.supportQ_euclidean (D := Y) (f l)
      exact e ▸ h4 l
theorem smoothTensors_eq_span (Y : PeriodicSpace.Params) (O : Set (Fin 4 → ℝ)) (q : ℕ) :
    MirrorFamilies.smoothSepTensors Y O q = Submodule.span ℂ (sepRealTensors ∞ O q) := by
  cases q with
  | zero => exact top_eq_span_sepRealTensors ∞ O
  | succ q =>
    refine congrArg (Submodule.span ℂ) (Set.ext fun F => ?_)
    constructor
    · rintro ⟨f, hf, hs, hO, rfl⟩
      obtain ⟨h1, h2, h3⟩ := (BallTuples.mem_sepC1Tuples_euclidean_iff f).1 hf
      exact ⟨f, ⟨hs, h2, h3, fun l => (hO l).2⟩, rfl⟩
    · rintro ⟨f, ⟨h1, h2, h3, h4⟩, rfl⟩
      refine ⟨f, (BallTuples.mem_sepC1Tuples_euclidean_iff f).2
        ⟨fun l => (h1 l).of_le (by exact_mod_cast le_top), h2, h3⟩, h1, fun l => ⟨h2 l, h4 l⟩, rfl⟩
end ToriLimits.GrowingVolumeLimits.ProofSteps.AtEveryMirror
end
end
section
open Set Filter Topology
open scoped NNReal ENNReal ComplexConjugate ContDiff
noncomputable section
namespace ToriLimits.GrowingVolumeLimits.ProofSteps.AtEveryMirror
open CentredTensorMoments (conjReflectTest tupleTensor realTupleTensor)
open PeriodicSpace TorusTransport.TestFunctionOrders
def reflTuple (μ : Fin 4) (c : ℝ) : {q q' : ℕ} → (Fin q → (Fin 4 → ℝ) → ℝ) →
    (Fin q' → (Fin 4 → ℝ) → ℝ) → Fin (reflOrder q q') → (Fin 4 → ℝ) → ℝ
  | 0, 0, _, _ => Fin.elim0
  | 0, _ + 1, _, X' => X'
  | _ + 1, 0, X, _ => fun l => X l ∘ hyperplaneFlip μ c
  | _ + 1, _ + 1, X, X' => Fin.append (fun l => X l ∘ hyperplaneFlip μ c) X'
theorem conjReflectTest_realTupleTensor (μ : Fin 4) (c : ℝ) {q : ℕ}
    (X : Fin (q + 1) → (Fin 4 → ℝ) → ℝ) :
    conjReflectTest μ c (realTupleTensor X) =
      realTupleTensor fun l => X l ∘ hyperplaneFlip μ c := by
  funext x
  show conj (∏ i, ((X i (hyperplaneFlip μ c (x i)) : ℝ) : ℂ)) =
    ∏ i, ((X i (hyperplaneFlip μ c (x i)) : ℝ) : ℂ)
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => Complex.conj_ofReal _
theorem reflProduct_realTupleTensor (μ : Fin 4) (c : ℝ) {q q' : ℕ}
    (X : Fin q → (Fin 4 → ℝ) → ℝ) (X' : Fin q' → (Fin 4 → ℝ) → ℝ) :
    reflProduct μ c (realTupleTensor X) (realTupleTensor X') =
      realTupleTensor (reflTuple μ c X X') := by
  cases q <;> cases q'
  · show conj (1 : ℂ) * (1 : ℂ) = 1
    simp
  · funext x
    show conj (1 : ℂ) * realTupleTensor X' x = realTupleTensor X' x
    simp
  · funext x
    show (1 : ℂ) * conjReflectTest μ c (realTupleTensor X) x = _
    rw [one_mul, conjReflectTest_realTupleTensor]
    rfl
  · rename_i p r
    show tensor (p := p + 1) (q := r + 1)
      (conjReflectTest μ c (realTupleTensor X)) (realTupleTensor X') = _
    rw [conjReflectTest_realTupleTensor]
    have h : (fun l x => ((reflTuple μ c X X' l x : ℝ) : ℂ)) =
        Fin.append (fun l x => (((X l ∘ hyperplaneFlip μ c) x : ℝ) : ℂ))
          (fun l x => ((X' l x : ℝ) : ℂ)) := by
      funext l
      induction l using Fin.addCases with
      | left i =>
        simp [reflTuple]
      | right i =>
        simp [reflTuple]
    show tensor (prodTensor _) (prodTensor _) =
      prodTensor fun l x => ((reflTuple μ c X X' l x : ℝ) : ℂ)
    rw [h, tensor_prodTensor]
    rfl
theorem isSeparatedFamily_reflect {m : WithTop ℕ∞} {μ : Fin 4} {c : ℝ} {n : ℕ}
    {X : Fin n → (Fin 4 → ℝ) → ℝ}
    (hX : IsSeparatedFamily m (openHalfSpace μ c : Set (Fin 4 → ℝ)) X) :
    IsSeparatedFamily m univ (fun l => X l ∘ hyperplaneFlip μ c) ∧
      ∀ l, Disjoint (tsupport (X l ∘ hyperplaneFlip μ c)) (openHalfSpace μ c : Set (Fin 4 → ℝ)) := by
  refine ⟨⟨fun l => (hX.contDiff l).comp (contDiff_hyperplaneFlip μ c), fun l => ?_,
    fun l l' h => ?_, fun _ => subset_univ _⟩, fun l => ?_⟩
  · rw [tsupport_comp_hyperplaneFlip]
    exact (hyperplaneFlipHomeomorph μ c).isCompact_preimage.2 (hX.isCompact l)
  · rw [tsupport_comp_hyperplaneFlip, tsupport_comp_hyperplaneFlip]
    exact (hX.disj l l' h).preimage _
  · rw [tsupport_comp_hyperplaneFlip]
    refine Set.disjoint_left.2 fun x hx hO => ?_
    have h₁ : c < hyperplaneFlip μ c x μ := hX.subset_open l hx
    have h₂ : c < x μ := hO
    rw [hyperplaneFlip_apply_self] at h₁
    linarith
theorem isSeparatedFamily_reflTuple {m : WithTop ℕ∞} {μ : Fin 4} {c : ℝ} {q q' : ℕ}
    {X : Fin q → (Fin 4 → ℝ) → ℝ} {X' : Fin q' → (Fin 4 → ℝ) → ℝ}
    (hX : IsSeparatedFamily m (openHalfSpace μ c : Set (Fin 4 → ℝ)) X)
    (hX' : IsSeparatedFamily m (openHalfSpace μ c : Set (Fin 4 → ℝ)) X') :
    IsSeparatedFamily m univ (reflTuple μ c X X') := by
  obtain ⟨hr, hd⟩ := isSeparatedFamily_reflect hX
  cases q <;> cases q'
  · exact isSeparatedFamily_of_fin_zero m univ _
  · exact ⟨hX'.contDiff, hX'.isCompact, hX'.disj, fun _ => subset_univ _⟩
  · exact hr
  · rename_i p r
    refine ⟨fun l => ?_, fun l => ?_, fun l l' h => ?_, fun _ => subset_univ _⟩
    · induction l using Fin.addCases with
      | left i => simpa [reflTuple] using hr.contDiff i
      | right i => simpa [reflTuple] using hX'.contDiff i
    · induction l using Fin.addCases with
      | left i => simpa [reflTuple] using hr.isCompact i
      | right i => simpa [reflTuple] using hX'.isCompact i
    · induction l using Fin.addCases with
      | left i =>
        induction l' using Fin.addCases with
        | left k =>
          have hik : i ≠ k := fun e => h (by rw [e])
          simpa [reflTuple] using hr.disj i k hik
        | right k =>
          simpa [reflTuple] using (hd i).mono_right (hX'.subset_open k)
      | right i =>
        induction l' using Fin.addCases with
        | left k =>
          simpa [reflTuple] using ((hd k).mono_right (hX'.subset_open i)).symm
        | right k =>
          have hik : i ≠ k := fun e => h (by rw [e])
          simpa [reflTuple] using hX'.disj i k hik
theorem reflProduct_zero_right (μ : Fin 4) (c : ℝ) {q q' : ℕ} (A : OrderedTestFun q) :
    reflProduct μ c A (0 : OrderedTestFun q') = 0 := by
  have h := reflProduct_add_smul_right μ c A (0 : OrderedTestFun q') 0 0 0
  simpa using h
theorem reflProduct_zero_left (μ : Fin 4) (c : ℝ) {q q' : ℕ} (B : OrderedTestFun q') :
    reflProduct μ c (0 : OrderedTestFun q) B = 0 := by
  have h := reflProduct_add_smul_left μ c (0 : OrderedTestFun q) 0 B 0 0
  simpa using h
theorem reflProduct_mem_of_mem_span {μ : Fin 4} {c : ℝ} {q q' : ℕ}
    {G : Set (OrderedTestFun q)} {G' : Set (OrderedTestFun q')}
    (W : Submodule ℂ (OrderedTestFun (reflOrder q q')))
    (h : ∀ A ∈ G, ∀ B ∈ G', reflProduct μ c A B ∈ W) {A : OrderedTestFun q}
    {B : OrderedTestFun q'} (hA : A ∈ Submodule.span ℂ G) (hB : B ∈ Submodule.span ℂ G') :
    reflProduct μ c A B ∈ W := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    induction hB using Submodule.span_induction with
    | mem B hB => exact h A hA B hB
    | zero => rw [reflProduct_zero_right]; exact W.zero_mem
    | add B B' _ _ h₁ h₂ =>
      have e := reflProduct_add_smul_right μ c A B B' 1 1
      rw [one_smul, one_smul, one_smul, one_smul] at e
      rw [e]
      exact W.add_mem h₁ h₂
    | smul a B _ h₁ =>
      have e := reflProduct_add_smul_right μ c A B 0 a 0
      rw [zero_smul, add_zero, zero_smul, add_zero] at e
      rw [e]
      exact W.smul_mem a h₁
  | zero => rw [reflProduct_zero_left]; exact W.zero_mem
  | add A A' _ _ h₁ h₂ =>
    have e := reflProduct_add_smul_left μ c A A' B 1 1
    simp only [one_smul, map_one] at e
    rw [e]
    exact W.add_mem h₁ h₂
  | smul a A _ h₁ =>
    have e := reflProduct_add_smul_left μ c A 0 B a 0
    simp only [smul_zero, add_zero, map_zero, zero_smul] at e
    rw [e]
    exact W.smul_mem _ h₁
theorem reflectedTensorsSeparated_holds (Y : PeriodicSpace.Params) (μ : Fin 4) (c : ℝ) :
    ReflectedTensorsSeparated Y μ c := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.SymbolPairing.reflectedTensorsSeparated_holds <;> assumption
theorem reflectedTensor_mem_smoothTensors (Y : PeriodicSpace.Params) (μ : Fin 4) (c : ℝ)
    (F F' : TestFamily) (q q' : ℕ)
    (hF : F q ∈ MirrorFamilies.smoothSepTensors Y (openHalfSpace μ c : Set (Fin 4 → ℝ)) q)
    (hF' : F' q' ∈ MirrorFamilies.smoothSepTensors Y (openHalfSpace μ c : Set (Fin 4 → ℝ)) q') :
    (reflectedTensor μ c F F' q q').2 ∈
      MirrorFamilies.smoothSepTensors Y univ (reflectedTensor μ c F F' q q').1 := by
  rw [reflectedTensor_eq]
  rw [smoothTensors_eq_span] at hF hF' ⊢
  refine reflProduct_mem_of_mem_span _ ?_ hF hF'
  rintro _ ⟨X, hX, rfl⟩ _ ⟨X', hX', rfl⟩
  rw [reflProduct_realTupleTensor]
  exact Submodule.subset_span ⟨_, isSeparatedFamily_reflTuple hX hX', rfl⟩
theorem smoothTensors_le_sepTensorSubmodule (Y : PeriodicSpace.Params) (O : Set (Fin 4 → ℝ))
    (q : ℕ) : MirrorFamilies.smoothSepTensors Y O q ≤ sepTensorSubmodule Y O q := by
  rw [smoothTensors_eq_span, sepTensorSubmodule_eq_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨X, hX, rfl⟩
  exact ⟨X, ⟨fun l => (hX.contDiff l).of_le (by exact_mod_cast le_top), hX.isCompact, hX.disj,
    hX.subset_open⟩, rfl⟩
variable {Y : PeriodicSpace.Params}
theorem momentExtensionAt_zero (Ξ : EuclidHierarchy Y) (q : ℕ) :
    momentExtensionAt Ξ ⟨q, 0⟩ = 0 := by
  rw [momentExtensionAt, dif_pos (Submodule.zero_mem _)]
  exact map_zero _
theorem reflectionForm_eq_sum {Ξ : EuclidHierarchy Y} (μ : Fin 4) (c : ℝ) (F F' : TestFamily)
    (q₀ : ℕ) (hF : ∀ q, q₀ < q → F q = 0) (hF' : ∀ q, q₀ < q → F' q = 0) :
    reflectionForm Ξ μ c F F' = ∑ q ∈ Finset.range (q₀ + 1), ∑ q' ∈ Finset.range (q₀ + 1),
      momentExtensionAt Ξ (reflectedTensor μ c F F' q q') := by
  have hs : Function.support
      (fun p : ℕ × ℕ => momentExtensionAt Ξ (reflectedTensor μ c F F' p.1 p.2)) ⊆
      ↑(Finset.range (q₀ + 1) ×ˢ Finset.range (q₀ + 1)) := by
    intro p hp
    by_contra hn
    refine hp ?_
    have h' : q₀ < p.1 ∨ q₀ < p.2 := by
      by_contra h''
      simp only [not_or, not_lt] at h''
      exact hn (by simp; omega)
    show momentExtensionAt Ξ (reflectedTensor μ c F F' p.1 p.2) = 0
    rw [reflectedTensor_eq]
    rcases h' with h' | h'
    · rw [hF _ h', reflProduct_zero_left, momentExtensionAt_zero]
    · rw [hF' _ h', reflProduct_zero_right, momentExtensionAt_zero]
  rw [reflectionForm, finsum_eq_sum_of_support_subset _ hs, Finset.sum_product]
end ToriLimits.GrowingVolumeLimits.ProofSteps.AtEveryMirror
end
end
section
open Set Filter Topology
open scoped NNReal ENNReal ComplexConjugate ContDiff
noncomputable section
namespace ToriLimits.GrowingVolumeLimits.ProofSteps.AtEveryMirror
open TorusTransport (IsEuclideanMotion)
open CentredTensorMoments (conjReflectTest tupleTensor realTupleTensor)
open PeriodicSpace TorusTransport.TestFunctionOrders
open TorusTransport.TupleVectors
open TimeAxisSymbols
variable {D : Setup}
theorem isSeparatedFamily_of_sepTuple {O : Set (Fin 4 → ℝ)} (X : SepTuple (symbolSetup D) O) :
    IsSeparatedFamily 1 O X.1.2 := by
  obtain ⟨-, hk, hd, hc, ho⟩ :=
    (TorusTransport.TupleVectors.mem_sepTuples_iff (symbolSetup D) O X.1).1 X.2
  exact ⟨hc, hk, fun l l' h => hd h, ho⟩
theorem mem_sepTuples_of_isSeparatedFamily {O : Set (Fin 4 → ℝ)} {q : ℕ}
    {X : Fin q → (Fin 4 → ℝ) → ℝ} (hX : IsSeparatedFamily 1 O X) :
    (⟨q, X⟩ : FnTuple) ∈ TorusTransport.TupleVectors.sepTuples (symbolSetup D) O :=
  (TorusTransport.TupleVectors.mem_sepTuples_iff (symbolSetup D) O _).2
    ⟨fun l => lipschitzOn_of_isC1On (symbolSetup D) (hX.contDiff l) (hX.isCompact l), hX.isCompact,
      fun l l' h => hX.disj l l' h, hX.contDiff, hX.subset_open⟩
def tensorSeq (X : FnTuple) : TestFamily := Pi.single X.1 (realTupleTensor X.2)
theorem tensorSeq_mem (Y : PeriodicSpace.Params) {μ : Fin 4} {c : ℝ}
    (X : SepTuple (symbolSetup D) (openHalfSpace μ c : Set (Fin 4 → ℝ))) :
    tensorSeq X.1 ∈ finiteSeqsAbove Y μ c := by
  refine ⟨fun q => ?_, X.1.1 + 1, fun q hq => Pi.single_eq_of_ne (by omega) _⟩
  by_cases h : q = X.1.1
  · subst h
    rw [tensorSeq, Pi.single_eq_same, sepTensorSubmodule_eq_span]
    exact Submodule.subset_span ⟨X.1.2, isSeparatedFamily_of_sepTuple X, rfl⟩
  · rw [tensorSeq, Pi.single_eq_of_ne h]
    exact Submodule.zero_mem _
def spanToSeq (Y : PeriodicSpace.Params) (D : Setup) (μ : Fin 4) (c : ℝ) :
    SepSpan (symbolSetup D) (openHalfSpace μ c : Set (Fin 4 → ℝ)) →ₗ[ℂ] finiteSeqsAbove Y μ c :=
  linExtend fun X => ⟨tensorSeq X.1, tensorSeq_mem Y X⟩
theorem exists_spanToSeq_eq (Y : PeriodicSpace.Params) (D : Setup) {μ : Fin 4} {c : ℝ}
    (F : finiteSeqsAbove Y μ c) : ∃ v, spanToSeq Y D μ c v = F := by
  obtain ⟨F, hm, N, hN⟩ := F
  let R : Submodule ℂ TestFamily :=
    LinearMap.range ((finiteSeqsAbove Y μ c).subtype ∘ₗ spanToSeq Y D μ c)
  have hs : ∀ (q : ℕ) (A : OrderedTestFun q),
      A ∈ sepTensorSubmodule Y (openHalfSpace μ c : Set (Fin 4 → ℝ)) q →
      (Pi.single q A : TestFamily) ∈ R := by
    intro q A hA
    rw [sepTensorSubmodule_eq_span] at hA
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨X, hX, rfl⟩ := hA
      refine ⟨basisVec ⟨⟨q, X⟩, mem_sepTuples_of_isSeparatedFamily hX⟩, ?_⟩
      simp only [LinearMap.comp_apply, spanToSeq, linExtend_basisVec]
      rfl
    | zero =>
      rw [Pi.single_zero]
      exact R.zero_mem
    | add A B _ _ h₁ h₂ =>
      rw [Pi.single_add]
      exact R.add_mem h₁ h₂
    | smul a A _ h₁ =>
      rw [Pi.single_smul]
      exact R.smul_mem a h₁
  have hF : F = ∑ q ∈ Finset.range N, (Pi.single q (F q) : TestFamily) := by
    funext q
    rw [Finset.sum_apply, Finset.sum_pi_single]
    by_cases h : q ∈ Finset.range N
    · rw [if_pos h]
    · rw [if_neg h]
      exact hN q (by simpa using h)
  have hFR : F ∈ R := by
    rw [hF]
    exact R.sum_mem fun q _ => hs q _ (hm q)
  obtain ⟨v, hv⟩ := hFR
  exact ⟨v, Subtype.ext hv⟩
variable {Ξ : D.LimitHierarchy}
theorem reflectionForm_add_smul_right (hE : MomentLinearExtension Ξ) (μ : Fin 4) (c : ℝ)
    {F G H : TestFamily}
    (hF : F ∈ finiteSeqsAbove D.euclidParams μ c)
    (hG : G ∈ finiteSeqsAbove D.euclidParams μ c)
    (hH : H ∈ finiteSeqsAbove D.euclidParams μ c) (a b : ℂ) :
    reflectionForm Ξ μ c F (a • G + b • H) =
      a * reflectionForm Ξ μ c F G + b * reflectionForm Ξ μ c F H := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.SymbolPairing.reflectionForm_right_linear <;> assumption
theorem reflectionForm_add_smul_left (hE : MomentLinearExtension Ξ) (μ : Fin 4) (c : ℝ)
    {F G H : TestFamily}
    (hF : F ∈ finiteSeqsAbove D.euclidParams μ c)
    (hG : G ∈ finiteSeqsAbove D.euclidParams μ c)
    (hH : H ∈ finiteSeqsAbove D.euclidParams μ c) (a b : ℂ) :
    reflectionForm Ξ μ c (a • F + b • G) H =
      conj a * reflectionForm Ξ μ c F H + conj b * reflectionForm Ξ μ c G H := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.SymbolPairing.reflectionForm_left_antilinear <;> assumption
def reflectionSesqForm (hE : MomentLinearExtension Ξ) (μ : Fin 4) (c : ℝ) :
    finiteSeqsAbove D.euclidParams μ c →ₛₗ[starRingEnd ℂ]
      finiteSeqsAbove D.euclidParams μ c →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun F G => reflectionForm Ξ μ c F.1 G.1)
    (fun F G H => by
      have h := reflectionForm_add_smul_left hE μ c F.2 G.2 H.2 1 1
      simpa using h)
    (fun a F G => by
      have h := reflectionForm_add_smul_left hE μ c F.2 F.2 G.2 a 0
      simpa using h)
    (fun F G H => by
      have h := reflectionForm_add_smul_right hE μ c F.2 G.2 H.2 1 1
      simpa using h)
    (fun a F G => by
      have h := reflectionForm_add_smul_right hE μ c F.2 G.2 G.2 a 0
      simpa using h)
theorem reflectionSesqForm_apply (hE : MomentLinearExtension Ξ) (μ : Fin 4) (c : ℝ)
    (F G : finiteSeqsAbove D.euclidParams μ c) :
    reflectionSesqForm hE μ c F G = reflectionForm Ξ μ c F.1 G.1 :=
  rfl
theorem sesqForm_conj_symm_of_im_diag_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ) (h : ∀ F, (B F F).im = 0) (F G : V) :
    B G F = conj (B F G) := by
  have e₁ : B (F + G) (F + G) = B F F + B F G + B G F + B G G := by
    simp only [map_add, LinearMap.add_apply]
    ring
  have e₂ : B (F + Complex.I • G) (F + Complex.I • G) =
      B F F + Complex.I * B F G - Complex.I * B G F + B G G := by
    simp only [map_add, LinearMap.add_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, Complex.conj_I]
    linear_combination (-(B G G)) * Complex.I_mul_I
  have h₁ := h (F + G)
  have h₂ := h (F + Complex.I • G)
  rw [e₁] at h₁
  rw [e₂] at h₂
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, h F, h G,
    zero_mul, one_mul, add_zero, zero_add] at h₁ h₂
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith
end ToriLimits.GrowingVolumeLimits.ProofSteps.AtEveryMirror
end
end
section
open Set Filter Topology
open scoped NNReal ENNReal ComplexConjugate ContDiff
noncomputable section
namespace ToriLimits.GrowingVolumeLimits.ProofSteps.AtEveryMirror
open TorusTransport (IsEuclideanMotion)
open CentredTensorMoments (conjReflectTest tupleTensor realTupleTensor)
open PeriodicSpace TorusTransport.TestFunctionOrders
open TorusTransport.TupleVectors
open TimeAxisSymbols
variable {D : Setup} {Ξ : D.LimitHierarchy}
def auxMirrorData (D : Setup) : ReflectionPositivity.AxisMirror.MirrorData :=
  ⟨(symbolSetup D).toStandingParameters, 1, one_pos⟩
theorem conjugatesToTimeReflect_of_cited (D : Setup) (h : CitedFacts) (μ : Fin 4) (c : ℝ) :
    ConjugatesToTimeReflect μ c :=
  (h.translations (auxMirrorData D) ⟨1, Set.mem_Ici.2 le_rfl⟩).2.2.2.2 μ c
theorem isEuclideanMotion_of_mem (D : Setup) (h : CitedFacts) {s : Equiv.Perm (Fin 4 → ℝ)}
    (hs : s ∈ TorusPeriodization.euclideanMotions) : IsEuclideanMotion s :=
  (h.translations (auxMirrorData D) ⟨1, Set.mem_Ici.2 le_rfl⟩).2.1 s hs
theorem isEuclideanMotion_toTimeMirrorMotion (D : Setup) (h : CitedFacts) (μ : Fin 4) (c : ℝ) :
    IsEuclideanMotion (toTimeMirrorMotion μ c) :=
  isEuclideanMotion_of_mem D h (conjugatesToTimeReflect_of_cited D h μ c).2.1
theorem isEuclideanMotion_toTimeMirrorMotion_inv (D : Setup) (h : CitedFacts) (μ : Fin 4)
    (c : ℝ) : IsEuclideanMotion ((toTimeMirrorMotion μ c)⁻¹ : Equiv.Perm (Fin 4 → ℝ)) :=
  isEuclideanMotion_of_mem D h (inv_mem (conjugatesToTimeReflect_of_cited D h μ c).2.1)
theorem mapsTo_toTimeMirrorMotion (D : Setup) (h : CitedFacts) (μ : Fin 4) (c : ℝ) :
    Set.MapsTo (toTimeMirrorMotion μ c) (openHalfSpace μ c : Set (Fin 4 → ℝ)) posTimeHalf := by
  intro x hx
  have h₁ : toTimeMirrorMotion μ c x ∈ toTimeMirrorMotion μ c '' {x | c < x μ} :=
    ⟨x, hx, rfl⟩
  rw [(conjugatesToTimeReflect_of_cited D h μ c).2.2.1] at h₁
  exact h₁
def carriedSymbol (D : Setup) (h : CitedFacts) (μ : Fin 4) (c : ℝ)
    (X : SepTuple (symbolSetup D) (openHalfSpace μ c : Set (Fin 4 → ℝ))) :
    PosSymbol (symbolSetup D) :=
  MirrorPicture.motionOnSep (isEuclideanMotion_toTimeMirrorMotion D h μ c)
    (mapsTo_toTimeMirrorMotion D h μ c) X
def carriedSpan (D : Setup) (h : CitedFacts) (μ : Fin 4) (c : ℝ) :
    SepSpan (symbolSetup D) (openHalfSpace μ c : Set (Fin 4 → ℝ)) →ₗ[ℂ]
      PosSymbolSpan (symbolSetup D) :=
  MirrorPicture.motionOnSpan (isEuclideanMotion_toTimeMirrorMotion D h μ c)
    (mapsTo_toTimeMirrorMotion D h μ c)
theorem hyperplaneFlip_eq_hyperplaneReflect (μ : Fin 4) (c : ℝ) (x : Fin 4 → ℝ) :
    hyperplaneFlip μ c x = TorusTransport.hyperplaneReflect μ c x := by
  rw [hyperplaneFlip_apply, GrowingTori.hyperplaneReflect_eq_sub]
theorem hyperplaneFlip_eq_conj_timeReflect (D : Setup) (h : CitedFacts) (μ : Fin 4) (c : ℝ)
    (x : Fin 4 → ℝ) :
    hyperplaneFlip μ c x = (toTimeMirrorMotion μ c).symm
      (TorusTransport.timeReflect (toTimeMirrorMotion μ c x)) := by
  have h₁ := congrFun (conjugatesToTimeReflect_of_cited D h μ c).2.2.2.2
    (toTimeMirrorMotion μ c x)
  simp only [Function.comp_apply, Equiv.symm_apply_apply] at h₁
  rw [hyperplaneFlip_eq_hyperplaneReflect, h₁]
theorem reflectSymbol_carriedSymbol_fn (h : CitedFacts) (μ : Fin 4) (c : ℝ)
    (X : SepTuple (symbolSetup D) (openHalfSpace μ c : Set (Fin 4 → ℝ))) (l : Fin X.1.1)
    (y : Fin 4 → ℝ) :
    (reflectSymbol (posToSymbol (carriedSymbol D h μ c X))).1.2 l y =
      X.1.2 l ((isEuclideanMotion_toTimeMirrorMotion D h μ c).toPerm.symm
        (TorusTransport.timeReflect y)) :=
  congrFun (reflectSymbol_fn (posToSymbol (carriedSymbol D h μ c X)) l) y
theorem momentExtensionAt_realTupleTensor (hE : MomentLinearExtension Ξ) {n : ℕ}
    (Z : Fin n → (Fin 4 → ℝ) → ℝ) (hZ : IsSeparatedFamily 1 univ Z) :
    momentExtensionAt Ξ ⟨n, realTupleTensor Z⟩ =
      ((symbolMoments Ξ ⟨⟨n, Z⟩, mem_sepTuples_of_isSeparatedFamily hZ⟩ : ℝ) : ℂ) := by
  cases n with
  | zero =>
    rw [hE.at_zero]
    have h₁ := SymbolSequences.momentOnSymbol_unitSymbol (D := symbolSetup D) Ξ
    have h₂ : (⟨⟨0, Z⟩, mem_sepTuples_of_isSeparatedFamily hZ⟩ : SpaceTimeSymbol (symbolSetup D)) =
        unitSymbol (symbolSetup D) :=
      Subtype.ext ((fst_eq_zero_iff _).1 rfl)
    rw [h₂, symbolMoments, h₁]
    simp [realTupleTensor, tupleTensor]
  | succ q =>
    exact hE.at_tensor q ⟨Z, SymbolSequences.components_mem_sepC1Tuples _
      ⟨⟨q + 1, Z⟩, mem_sepTuples_of_isSeparatedFamily (D := D) hZ⟩⟩
theorem actAny_tupleAppend {s : (Fin 4 → ℝ) → Fin 4 → ℝ} (hs : IsEuclideanMotion s)
    (a b : FnTuple) :
    actAny hs (tupleAppend a b) = tupleAppend (actAny hs a) (actAny hs b) := by
  refine Sigma.ext rfl (heq_of_eq (funext fun i => ?_))
  induction i using Fin.addCases with
  | left i => simp [actAny, tupleAppend, TorusTransport.familyAct]
  | right i => simp [actAny, tupleAppend, TorusTransport.familyAct]
theorem reflTuple_eq_tupleAppend (μ : Fin 4) (c : ℝ) {q q' : ℕ}
    (X : Fin q → (Fin 4 → ℝ) → ℝ) (X' : Fin q' → (Fin 4 → ℝ) → ℝ) :
    (⟨reflOrder q q', reflTuple μ c X X'⟩ : FnTuple) =
      tupleAppend ⟨q, fun l => X l ∘ hyperplaneFlip μ c⟩ ⟨q', X'⟩ := by
  cases q <;> cases q'
  · exact Sigma.ext rfl (heq_of_eq (funext fun i => i.elim0))
  · have e : (⟨0, fun l => X l ∘ hyperplaneFlip μ c⟩ : FnTuple) = nilTuple _ :=
      (fst_eq_zero_iff _).1 rfl
    rw [e, nil_tupleAppend]
    rfl
  · have e : (⟨0, X'⟩ : FnTuple) = nilTuple _ := (fst_eq_zero_iff _).1 rfl
    rw [e, tupleAppend_nil]
    rfl
  · rfl
theorem reflectionForm_tensorSeq (h : CitedFacts) (hE : MomentLinearExtension Ξ)
    (hM3 : IsMotionInvariant (symbolMoments Ξ)) (μ : Fin 4) (c : ℝ)
    (X Y : SepTuple (symbolSetup D) (openHalfSpace μ c : Set (Fin 4 → ℝ))) :
    reflectionForm Ξ μ c (tensorSeq X.1) (tensorSeq Y.1) =
      ((symbolMoments Ξ (reflectAppend (carriedSymbol D h μ c X) (carriedSymbol D h μ c Y)) : ℝ) :
        ℂ) := by
  have hz : ∀ (Z : FnTuple) (q : ℕ), q ≠ Z.1 → tensorSeq Z q = 0 := fun Z q hq =>
    Pi.single_eq_of_ne hq _
  rw [reflectionForm_eq_sum μ c _ _ (X.1.1 + Y.1.1) (fun q hq => hz _ q (by omega))
    (fun q hq => hz _ q (by omega))]
  rw [Finset.sum_eq_single X.1.1, Finset.sum_eq_single Y.1.1]
  · rw [reflectedTensor_eq, tensorSeq, tensorSeq, Pi.single_eq_same, Pi.single_eq_same,
      reflProduct_realTupleTensor,
      momentExtensionAt_realTupleTensor hE _
        (isSeparatedFamily_reflTuple (m := 1) (isSeparatedFamily_of_sepTuple X)
          (isSeparatedFamily_of_sepTuple Y))]
    set W := reflectAppend (carriedSymbol D h μ c X) (carriedSymbol D h μ c Y) with hW
    have hinv := isEuclideanMotion_toTimeMirrorMotion_inv D h μ c
    have hmem : ⇑((toTimeMirrorMotion μ c)⁻¹ : Equiv.Perm (Fin 4 → ℝ)) ∈
        TorusTransport.affineHyperoctahedral :=
      (GrowingTori.mem_euclideanMotions_iff_mem_affineHyperoctahedral _).1
        (inv_mem (conjugatesToTimeReflect_of_cited D h μ c).2.1)
    have hsym : ∀ x, hinv.toPerm.symm x = toTimeMirrorMotion μ c x := fun x =>
      (Equiv.symm_apply_eq _).2 (by simp)
    have hsym' : ∀ x, (isEuclideanMotion_toTimeMirrorMotion D h μ c).toPerm.symm x =
        (toTimeMirrorMotion μ c).symm x := fun x =>
      (Equiv.symm_apply_eq _).2 (by simp)
    rw [← hM3 _ hinv hmem W]
    refine congrArg (fun t : ℝ => (t : ℂ)) (congrArg (symbolMoments Ξ) (Subtype.ext ?_))
    show (⟨_, reflTuple μ c X.1.2 Y.1.2⟩ : FnTuple) = actAny hinv (tupleAppend _ _)
    rw [reflTuple_eq_tupleAppend, actAny_tupleAppend]
    congr 1
    · refine Sigma.ext rfl (heq_of_eq (funext fun l => funext fun x => ?_))
      refine Eq.trans ?_ (reflectSymbol_carriedSymbol_fn h μ c X l (hinv.toPerm.symm x)).symm
      show X.1.2 l (hyperplaneFlip μ c x) = _
      rw [hsym, hsym', hyperplaneFlip_eq_conj_timeReflect D h]
    · refine Sigma.ext rfl (heq_of_eq (funext fun l => funext fun x => ?_))
      show Y.1.2 l x =
        Y.1.2 l ((isEuclideanMotion_toTimeMirrorMotion D h μ c).toPerm.symm (hinv.toPerm.symm x))
      rw [hsym, hsym', Equiv.symm_apply_apply]
  · intro q' _ hq'
    rw [reflectedTensor_eq, hz Y.1 q' hq', reflProduct_zero_right, momentExtensionAt_zero]
  · intro hn
    exact absurd (Finset.mem_range.2 (by omega)) hn
  · intro q _ hq
    refine Finset.sum_eq_zero fun q' _ => ?_
    rw [reflectedTensor_eq, hz X.1 q hq, reflProduct_zero_left, momentExtensionAt_zero]
  · intro hn
    exact absurd (Finset.mem_range.2 (by omega)) hn
theorem reflectionForm_spanToSeq (h : CitedFacts) (hE : MomentLinearExtension Ξ)
    (hM3 : IsMotionInvariant (symbolMoments Ξ)) (μ : Fin 4) (c : ℝ)
    (v w : SepSpan (symbolSetup D) (openHalfSpace μ c : Set (Fin 4 → ℝ))) :
    reflectionForm Ξ μ c (spanToSeq D.euclidParams D μ c v).1
        (spanToSeq D.euclidParams D μ c w).1 =
      osForm (symbolMoments Ξ) (carriedSpan D h μ c v) (carriedSpan D h μ c w) := by
  have hV : ∀ {ι : Type _} [Fintype ι] (a : ι → ℂ)
      (X : ι → SepTuple (symbolSetup D) (openHalfSpace μ c : Set (Fin 4 → ℝ))),
      spanToSeq D.euclidParams D μ c (linComb a X) =
        ∑ b, a b • (⟨tensorSeq (X b).1, tensorSeq_mem _ (X b)⟩ :
          finiteSeqsAbove D.euclidParams μ c) := by
    intro ι _ a X
    simp only [linComb, map_sum, map_smul, spanToSeq, linExtend_basisVec]
  have hA : ∀ {ι : Type _} [Fintype ι] (a : ι → ℂ)
      (X : ι → SepTuple (symbolSetup D) (openHalfSpace μ c : Set (Fin 4 → ℝ))),
      carriedSpan D h μ c (linComb a X) = linComb a fun b => carriedSymbol D h μ c (X b) := by
    intro ι _ a X
    simp only [linComb, map_sum, map_smul, carriedSpan, MirrorPicture.motionOnSpan,
      linExtend_basisVec, carriedSymbol]
  rw [← reflectionSesqForm_apply hE, eq_linComb_support v, eq_linComb_support w, hV, hV, hA, hA,
    SymbolSequences.osForm_linComb]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  have e := reflectionForm_tensorSeq h hE hM3 μ c b.1 b'.1
  rw [reflectionSesqForm_apply]
  show _ * (_ * reflectionForm Ξ μ c (tensorSeq b.1.1) (tensorSeq b'.1.1)) = _
  rw [e]
  ring
theorem reflectionFormPositive_holds (h : CitedFacts) (hE : MomentLinearExtension Ξ)
    (hM3 : IsMotionInvariant (symbolMoments Ξ)) (hF : SymbolPairingMatches Ξ)
    (hpos : ReflectionPositive Ξ) (μ : Fin 4) (c : ℝ) : ReflectionFormPositive Ξ μ c := by
  have hnn : ∀ F ∈ finiteSeqsAbove D.euclidParams μ c,
      IsNonnegComplex (reflectionForm Ξ μ c F F) := by
    intro F hF'
    obtain ⟨v, hv⟩ := exists_spanToSeq_eq D.euclidParams D ⟨F, hF'⟩
    have e : F = (spanToSeq D.euclidParams D μ c v).1 := congrArg Subtype.val hv.symm
    rw [e, reflectionForm_spanToSeq h hE hM3, ← hF.pairing_eq]
    exact hpos _
  refine ⟨fun F hF' G hG H hH a b => reflectionForm_add_smul_right hE μ c hF' hG hH a b,
    fun F hF' G hG H hH a b => reflectionForm_add_smul_left hE μ c hF' hG hH a b,
    fun F hF' G hG => ?_, hnn⟩
  refine sesqForm_conj_symm_of_im_diag_eq_zero (reflectionSesqForm hE μ c) (fun P => ?_)
    ⟨F, hF'⟩ ⟨G, hG⟩
  obtain ⟨x, -, hx⟩ := hnn P.1 P.2
  rw [reflectionSesqForm_apply, ← hx]
  exact Complex.ofReal_im x
end ToriLimits.GrowingVolumeLimits.ProofSteps.AtEveryMirror
end
end
section
open Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace ToriLimits.GrowingVolumeLimits.ProofSteps.AtEveryMirror
open PeriodicSpace TorusTransport.TestFunctionOrders
theorem isClosed_setOf_isNonnegComplex : IsClosed {ζ : ℂ | IsNonnegComplex ζ} :=
  Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _ isClosed_Ici
theorem reflectionPositiveAt_all (h : CitedFacts)
    (hD : PeriodicSpace.TupleMetric.QuotientDistanceAndLifts)
    (hDer : PeriodicSpace.TupleDerivatives.Statement)
    (hC : PeriodicSpace.ContPartialsIffContDiff)
    (hForms : Continuum.BlockProducts.AssembledFormsAreDistributions)
    {D : Setup} {Ξ : D.LimitHierarchy} (hMem : MembersAreDistribs Ξ)
    (hE : MomentLinearExtension Ξ)
    (hM3 : TimeAxisSymbols.IsMotionInvariant (symbolMoments Ξ)) (hF : SymbolPairingMatches Ξ)
    (hpos : ReflectionPositive Ξ) :
    ∀ u, IsMemberFamily Ξ u → ∀ (μ : Fin 4) (c : ℝ), ReflectionPositiveAt Ξ u μ c := by
  intro u hu μ c
  refine ⟨reflectedTensorsSeparated_holds _ μ c,
    reflectionFormPositive_holds h hE hM3 hF hpos μ c, ?_⟩
  intro q₀ F hFq
  have hex : ∀ q, ∃ Fs : ℕ+ → OrderedTestFun (q + 1), q + 1 ≤ q₀ →
      (∀ t, Fs t ∈ MirrorFamilies.smoothSepTensors D.euclidParams
        (openHalfSpace μ c : Set (Fin 4 → ℝ)) (q + 1)) ∧
      MirrorFamilies.TendstoInInjTestFns D.euclidParams (openHalfSpace μ c : Set (Fin 4 → ℝ))
        (n := q.succPNat) Fs
        (F (q + 1)) := by
    intro q
    by_cases hq : q + 1 ≤ q₀
    · obtain ⟨Fs, h₁, h₂⟩ :=
        MirrorStep.exists_smoothTensor_approximants h hD hC D.euclidParams μ c q (F (q + 1))
          (hFq q hq)
      exact ⟨Fs, fun _ => ⟨h₁, h₂⟩⟩
    · exact ⟨fun _ => 0, fun hq' => absurd hq' hq⟩
  choose Fs hFs using hex
  classical
  let Ft : ℕ+ → TestFamily := fun t q =>
    match q with
    | 0 => F 0
    | q + 1 => if q + 1 ≤ q₀ then Fs q t else 0
  have hm : ∀ t q, Ft t q ∈ MirrorFamilies.smoothSepTensors D.euclidParams
      (openHalfSpace μ c : Set (Fin 4 → ℝ)) q := by
    intro t q
    cases q with
    | zero => exact Submodule.mem_top
    | succ q =>
      by_cases hq : q + 1 ≤ q₀
      · have e : Ft t (q + 1) = Fs q t := if_pos hq
        rw [e]
        exact (hFs q hq).1 t
      · have e : Ft t (q + 1) = 0 := if_neg hq
        rw [e]
        exact Submodule.zero_mem _
  have hz : ∀ t q, q₀ < q → Ft t q = 0 := by
    intro t q hq
    cases q with
    | zero => omega
    | succ q => exact if_neg (by omega)
  have hconv : ∀ q, q + 1 ≤ q₀ → MirrorFamilies.TendstoInInjTestFns D.euclidParams
      (openHalfSpace μ c : Set (Fin 4 → ℝ)) (n := q.succPNat) (fun t => Ft t (q + 1))
        (F (q + 1)) := by
    intro q hq
    have e : (fun t => Ft t (q + 1)) = Fs q := funext fun t => if_pos hq
    rw [e]
    exact (hFs q hq).2
  obtain ⟨hT₁, hT₂⟩ :=
    MirrorStep.tendsto_assembledDistributionAt_reflectedTensor h hD hDer hC hForms
      D.euclidParams u μ c q₀ F Ft (fun _ => rfl) hconv
  refine ⟨hT₁, ?_⟩
  have hlim := tendsto_finsetSum (Finset.range (q₀ + 1)) fun q hq =>
    tendsto_finsetSum (Finset.range (q₀ + 1)) fun q' hq' =>
      hT₂ q q' (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq))
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq'))
  have hnon : ∀ t, IsNonnegComplex
      (∑ q ∈ Finset.range (q₀ + 1), ∑ q' ∈ Finset.range (q₀ + 1),
        assembledDistributionAt u (reflectedTensor μ c (Ft t) (Ft t) q q')) := by
    intro t
    have e : (∑ q ∈ Finset.range (q₀ + 1), ∑ q' ∈ Finset.range (q₀ + 1),
        assembledDistributionAt u (reflectedTensor μ c (Ft t) (Ft t) q q')) =
        reflectionForm Ξ μ c (Ft t) (Ft t) := by
      rw [reflectionForm_eq_sum μ c (Ft t) (Ft t) q₀ (hz t) (hz t)]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
      exact MirrorStep.assembledDistributionAt_eq_momentExtensionAt h hMem u hu hE _ _
        (reflectedTensor_mem_smoothTensors _ μ c _ _ q q' (hm t q) (hm t q'))
    rw [e]
    refine (reflectionFormPositive_holds h hE hM3 hF hpos μ c).2.2.2 (Ft t)
      ⟨fun q => ?_, q₀ + 1, ?_⟩
    · exact smoothTensors_le_sepTensorSubmodule _ _ q (hm t q)
    · exact fun q hq => hz t q (by omega)
  exact isClosed_setOf_isNonnegComplex.mem_of_tendsto hlim (Eventually.of_forall hnon)
end ToriLimits.GrowingVolumeLimits.ProofSteps.AtEveryMirror
end
end
section
open scoped NNReal ENNReal ComplexConjugate
noncomputable section
namespace ToriLimits.GrowingVolumeLimits
open PeriodicSpace
open ProofSteps
open ProofSteps.ExistencePart ProofSteps.LimitInvariance ProofSteps.SequenceForm
  ProofSteps.ReflectedLatticeFormula ProofSteps.MomentsAlongSeq ProofSteps.SymbolPairing
  ProofSteps.AtEveryMirror
theorem holds_of_cited (hCumulants : ToriLimits.MomentsAndConnected.Statement)
    (hTransport : ToriLimits.ExponentTorusPeriodization.Statement)
    (hMultilinear : ToriLimits.NonlinearDomain.Statement)
    (hCollars : ToriLimits.SubfamiliesAndGaps.Statement)
    (hExtension : ToriLimits.TensorExtension.Holds)
    (hPolynomials : ToriLimits.LatticePolynomialCalculus.Holds)
    (hNesting : GrowingTori.LatticeMotions.motions_lattices_mirrors)
    (hElementary : DistributionBasics.ElementaryFacts)
    (hProduct : Continuum.TensorProduct.TensorProductExistsUnique)
    (hFunctionals : CentredTensorMoments.TorusFunctionals.Statement)
    (hMoments : PeriodicSpace.Kind.CentredMoments.Statement)
    (hDensity : PeriodicSpace.DenseTensorSpan.DensityStatement)
    (hDistributions :
      PeriodicSpace.Kind.EuclideanLimitDistributions.LimitMembersAreDistributions)
    (hSymbols : TimeAxisSymbols.MomentFunctionals.Statement)
    (hReconstruction : PositiveFormReconstruction.ReconstructionStatement)
    (hCompactness : PeriodicSpace.EquicontinuityCompactness.Statement)
    (hTranslations : ToriLimits.EuclideanSymmetryFacts.Statement)
    (hCountable : PeriodicSpace.CountableChoiceFamilyFacts)
    (hFamilies : PeriodicSpace.DenseFamilies.Claim)
    (hCovers : PeriodicSpace.TorusBallCoversAndPartitionsOfUnity)
    (hPullback : CoordinateRepresentation.DistributionsReadInCoordinates)
    (hDistinct : PeriodicSpace.Kind.AdmissibleProductFacts)
    (hLifts : PeriodicSpace.TupleMetric.QuotientDistanceAndLifts)
    (hDerivatives : PeriodicSpace.TupleDerivatives.Statement)
    (hPartials : PeriodicSpace.ContPartialsIffContDiff)
    (hForms : Continuum.BlockProducts.AssembledFormsAreDistributions) : Holds := by
  have h : CitedFacts := ⟨hCumulants, hTransport, hMultilinear, hCollars, hExtension,
    hPolynomials, hNesting, hElementary, hProduct, hFunctionals, hMoments, hDensity,
    hDistributions, hSymbols, hReconstruction, hCompactness, hTranslations, hCountable⟩
  have hL : LimitCitedFacts := ⟨hFamilies, hCovers, hPullback, hDistinct⟩
  intro D S C hPB
  obtain ⟨Ψ, hΨ⟩ := exists_partialHierarchySeq S h C hPB
  refine ⟨eventuallyObeys_of_ballwise S h C hPB,
    fun B => exists_isConvergenceSetWith S h hL C hPB B, fun J Ξ hJ hΞ => ?_⟩
  have hA := existenceAndBounds_of_tendstoIn S h hL C hPB hJ hΞ
  have hDist := memberDistribsInvariant_of_tendstoIn S h C hPB hΞ
  have hB := symmetries_of_limit h S C hJ hΞ hDist
  have hM := centredMomentsConverge h S C hJ hΞ Ψ hΨ
  have hE := momentLinearExtension_holds h Ξ
  have hF := symbolPairingMatches_holds h Ξ
  have hM1 := symbolMoments_isNormedSymmMultilinear h Ξ
  have hM2 := symbolMoments_isScaleBounded h hA.mem_boundedEuclidHierarchies
  have hM3 := symbolMoments_isMotionInvariant h hB
  have hpos := reflectionPositive h S hM hE
  have hM4 := symbolMoments_isReflPositive h hpos
  exact ⟨hA, hB,
    ⟨tensorMoment_tendsTo h S hM hE, reflectionPairing_eq_limit h S hM hE,
      reflectionPositiveAt_all h hLifts hDerivatives hPartials hForms hA.membersAreDistribs hE
        hM3 hF hpos⟩,
    osReconstruction_of_symbolMoments h hM1 hM2 hM3 hM4 hF⟩
end ToriLimits.GrowingVolumeLimits
end
end
end YangMills.Construction
