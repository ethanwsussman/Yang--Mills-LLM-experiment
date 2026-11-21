import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.ReflectionPositivity.SixteenFamiliesOfMirrors
import Mathlib
set_option autoImplicit false
open Filter Function Topology
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.SeparatedTuples
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Mirrors (ReflectingHyperplane)
open YangMills.Construction.TorusMetric (euclidNormVec)
abbrev RealValued : Type := AmbientSpace → ℝ
def IsC1c (f : RealValued) : Prop :=
  TestFunctions.IsC1R4 f ∧ HasCompactSupport f
def IsDisjointlySupported (X : List RealValued) : Prop :=
  (∀ f ∈ X, IsC1c f) ∧ X.Pairwise fun f h => Disjoint (tsupport f) (tsupport h)
abbrev SepTuple : Type := {X : List RealValued // IsDisjointlySupported X}
namespace SepTuple
def size (X : SepTuple) : ℕ := X.1.length
def componentAt (X : SepTuple) (i : ℕ) : RealValued := X.1.getD i 0
def nil : SepTuple := ⟨[], by simp [IsDisjointlySupported]⟩
def Composable (X Y : SepTuple) : Prop :=
  ∀ f ∈ X.1, ∀ h ∈ Y.1, Disjoint (tsupport f) (tsupport h)
def glue (X Y : SepTuple) (hXY : Composable X Y) : SepTuple :=
  ⟨X.1 ++ Y.1, by
    refine ⟨fun f hf => ?_, List.pairwise_append.2 ⟨X.2.2, Y.2.2, hXY⟩⟩
    rcases List.mem_append.1 hf with hf | hf
    · exact X.2.1 f hf
    · exact Y.2.1 f hf⟩
open Classical in
def juxt (X Y : SepTuple) : SepTuple :=
  if h : Composable X Y then glue X Y h else nil
theorem juxt_val {X Y : SepTuple} (h : Composable X Y) : (juxt X Y).1 = X.1 ++ Y.1 := by
  simp [juxt, h, glue]
def sublistOn (X : List RealValued) (I : Finset ℕ) : List RealValued :=
  ((X.zipIdx 1).filter fun p => p.2 ∈ I).map Prod.fst
theorem sublistOn_sublist (X : List RealValued) (I : Finset ℕ) : (sublistOn X I).Sublist X := by
  have h := (List.filter_sublist (l := X.zipIdx 1) (p := fun p => decide (p.2 ∈ I))).map Prod.fst
  simpa [sublistOn, List.zipIdx_map_fst] using h
def subtuple (X : SepTuple) (I : Finset ℕ) : SepTuple :=
  ⟨sublistOn X.1 I, fun f hf => X.2.1 f ((sublistOn_sublist X.1 I).subset hf),
    X.2.2.sublist (sublistOn_sublist X.1 I)⟩
def reorder (X : SepTuple) (ς : Equiv.Perm (Fin X.1.length)) : SepTuple :=
  ⟨List.ofFn (X.1.get ∘ ς), by
    have hp : (List.ofFn (X.1.get ∘ ς)).Perm X.1 := by
      simpa using Equiv.Perm.ofFn_comp_perm ς X.1.get
    refine ⟨fun f hf => X.2.1 f (hp.mem_iff.1 hf), (hp.pairwise_iff ?_).2 X.2.2⟩
    exact fun h => h.symm⟩
end SepTuple
def supportedIn (O : Set AmbientSpace) : Set SepTuple := {X | ∀ f ∈ X.1, tsupport f ⊆ O}
theorem nil_mem_supportedIn (O : Set AmbientSpace) : SepTuple.nil ∈ supportedIn O := by
  intro f hf
  simp [SepTuple.nil] at hf
theorem composable_of_mem_supportedIn {O O' : Set AmbientSpace} (hO : Disjoint O O')
    {X Y : SepTuple} (hX : X ∈ supportedIn O) (hY : Y ∈ supportedIn O') :
    SepTuple.Composable X Y :=
  fun f hf h hh => hO.mono (hX f hf) (hY h hh)
abbrev FormalSpan : Type := SepTuple →₀ ℂ
def basisVec (X : SepTuple) : FormalSpan := Finsupp.single X 1
theorem linearIndependent_basisVec (O : Set AmbientSpace) :
    LinearIndependent ℂ fun X : supportedIn O => basisVec X.1 := by
  have h : LinearIndependent ℂ (Finsupp.basisSingleOne (R := ℂ) (ι := SepTuple)) :=
    Finsupp.basisSingleOne.linearIndependent
  have h' := h.comp (Subtype.val : supportedIn O → SepTuple) Subtype.val_injective
  convert h' using 1
  funext X
  simp [basisVec]
def spanIn (O : Set AmbientSpace) : Submodule ℂ FormalSpan :=
  Submodule.span ℂ (Set.range fun X : supportedIn O => basisVec X.1)
def spanBasisIn (O : Set AmbientSpace) : Module.Basis (supportedIn O) ℂ (spanIn O) :=
  Module.Basis.span (linearIndependent_basisVec O)
def conjugation : FormalSpan →ₛₗ[starRingEnd ℂ] FormalSpan where
  toFun F := F.mapRange (starRingEnd ℂ) (map_zero _)
  map_add' F G := by
    ext X
    simp
  map_smul' z F := by
    ext X
    simp
theorem conjugation_basisVec (X : SepTuple) : conjugation (basisVec X) = basisVec X := by
  ext Y
  by_cases h : X = Y <;> simp [conjugation, basisVec, h]
theorem conjugation_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (X : ι → SepTuple) :
    conjugation (∑ b ∈ s, c b • basisVec (X b)) = ∑ b ∈ s, conj (c b) • basisVec (X b) := by
  simp [map_sum, conjugation_basisVec]
section Extension
variable {V : Type*} [AddCommMonoid V] [Module ℂ V]
def linearExtend (φ : SepTuple → V) : FormalSpan →ₗ[ℂ] V := Finsupp.linearCombination ℂ φ
theorem linearExtend_basisVec (φ : SepTuple → V) (X : SepTuple) :
    linearExtend φ (basisVec X) = φ X := by
  simp [linearExtend, basisVec]
end Extension
def formalMul : FormalSpan →ₗ[ℂ] FormalSpan →ₗ[ℂ] FormalSpan :=
  linearExtend fun X => linearExtend fun Y => basisVec (SepTuple.juxt X Y)
theorem formalMul_basisVec (X Y : SepTuple) :
    formalMul (basisVec X) (basisVec Y) = basisVec (SepTuple.juxt X Y) := by
  simp [formalMul, linearExtend_basisVec]
theorem formalMul_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (c : ι → ℂ)
    (c' : κ → ℂ) (X : ι → SepTuple) (Y : κ → SepTuple) :
    formalMul (∑ b ∈ s, c b • basisVec (X b)) (∑ b' ∈ t, c' b' • basisVec (Y b')) =
      ∑ b ∈ s, ∑ b' ∈ t, (c b * c' b') • basisVec (SepTuple.juxt (X b) (Y b')) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    formalMul_basisVec, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [mul_comm]
def IsEuclidIsometry (r : AmbientSpace → AmbientSpace) : Prop :=
  ∀ x y, euclidNormVec (r x - r y) = euclidNormVec (x - y)
def invMap (r : AmbientSpace → AmbientSpace) : AmbientSpace → AmbientSpace := Function.invFun r
def pushList (r : AmbientSpace → AmbientSpace) (X : List RealValued) : List RealValued :=
  X.map fun f => f ∘ invMap r
open Classical in
def push (r : AmbientSpace → AmbientSpace) (X : SepTuple) : SepTuple :=
  if h : IsDisjointlySupported (pushList r X.1) then ⟨pushList r X.1, h⟩ else SepTuple.nil
theorem push_nil (r : AmbientSpace → AmbientSpace) : push r SepTuple.nil = SepTuple.nil := by
  have h : IsDisjointlySupported (pushList r SepTuple.nil.1) := by
    simp [pushList, SepTuple.nil, IsDisjointlySupported]
  unfold push
  rw [dif_pos h]
  exact Subtype.ext (by simp [pushList, SepTuple.nil])
def pushSpan (r : AmbientSpace → AmbientSpace) : FormalSpan →ₗ[ℂ] FormalSpan :=
  linearExtend fun X => basisVec (push r X)
def translate (v : AmbientSpace) : AmbientSpace → AmbientSpace := fun x => x + v
theorem isEuclidIsometry_translate (v : AmbientSpace) : IsEuclidIsometry (translate v) := by
  intro x y
  simp [translate]
theorem pushList_translate (v : AmbientSpace) (X : List RealValued) :
    pushList (translate v) X = X.map fun f x => f (x - v) := by
  have hinj : Function.Injective (translate v) := fun y z hyz => add_right_cancel hyz
  have hinv : ∀ x, invMap (translate v) x = x - v := fun x => by
    have hx : translate v (x - v) = x := by simp [translate]
    calc invMap (translate v) x = invMap (translate v) (translate v (x - v)) := by rw [hx]
      _ = x - v := Function.leftInverse_invFun hinj _
  refine List.map_congr_left fun f _ => ?_
  funext x
  simp [hinv]
def TendstoAdmissibly (r₀ : ℕ) (s : ℕ → SepTuple) (X : SepTuple) : Prop :=
  1 ≤ r₀ ∧ (∀ r, r₀ ≤ r → (s r).size = X.size) ∧
    ∃ A : Fin X.size → Set AmbientSpace, (∀ i, IsCompact (A i)) ∧ Pairwise (Disjoint on A) ∧
      (∀ r, r₀ ≤ r → ∀ i : Fin X.size,
        tsupport ((s r).componentAt i) ∪ tsupport (X.componentAt i) ⊆ A i) ∧
      ∀ i : Fin X.size,
        Tendsto (fun r => TestFunctions.c1NormR4 ((s r).componentAt i - X.componentAt i)) atTop (𝓝 0)
structure TupleFunctional where
  toFun : SepTuple → ℝ
  map_nil : toFun SepTuple.nil = 1
namespace TupleFunctional
variable (σ : TupleFunctional)
instance : CoeFun TupleFunctional fun _ => SepTuple → ℝ := ⟨TupleFunctional.toFun⟩
def spanExtension : FormalSpan →ₗ[ℂ] ℂ := linearExtend fun X => (σ X : ℂ)
def IsAdmissiblyContinuous : Prop :=
  ∀ (r₀ : ℕ) (s : ℕ → SepTuple) (X : SepTuple), TendstoAdmissibly r₀ s X →
    Tendsto (fun r => σ (s r)) atTop (𝓝 (σ X))
def IsPermInvariant : Prop :=
  ∀ (X : SepTuple) (ς : Equiv.Perm (Fin X.1.length)), σ (X.reorder ς) = σ X
def IsEntrywiseLinear : Prop :=
  ∀ (A B : List RealValued) (f f' : RealValued) (α α' : ℝ) (X X' Z : SepTuple),
    X.1 = A ++ f :: B → X'.1 = A ++ f' :: B → Z.1 = A ++ (α • f + α' • f') :: B →
      σ Z = α * σ X + α' * σ X'
def IsInvariant (r : AmbientSpace → AmbientSpace) : Prop := ∀ X : SepTuple, σ (push r X) = σ X
def IsTranslateInvariant : Prop := ∀ v : AmbientSpace, σ.IsInvariant (translate v)
def IsReflectionPositive (M : ReflectingHyperplane) : Prop :=
  ∀ J : ℕ, 1 ≤ J → ∀ X : Fin J → SepTuple, (∀ b, X b ∈ supportedIn M.positiveSide) →
    ∀ c : Fin J → ℂ,
    0 ≤ ∑ b, ∑ b', conj (c b) * c b' *
      (σ (SepTuple.juxt (push M.reflect (X b)) (X b')) : ℂ)
end TupleFunctional
end YangMills.Construction.SeparatedTuples
