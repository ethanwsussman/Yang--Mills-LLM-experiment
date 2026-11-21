import YangMills.Construction.Continuum.SchwingerFunctions
import Mathlib
set_option autoImplicit false
open Matrix Set
noncomputable section
namespace YangMills.Construction
namespace DisjointTuples
open SchwingerFunctions TorusMetric
abbrev RealFun : Type := (Fin 4 → ℝ) → ℝ
def IsDisjointTuple (L : List RealFun) : Prop :=
  (∀ f ∈ L, IsC1c f) ∧ L.Pairwise fun f g => Disjoint (tsupport f) (tsupport g)
abbrev DisjointTuple : Type := {L : List RealFun // IsDisjointTuple L}
namespace DisjointTuple
def nil : DisjointTuple := ⟨[], by simp [IsDisjointTuple]⟩
def Appendable (T U : DisjointTuple) : Prop :=
  ∀ f ∈ T.1, ∀ g ∈ U.1, Disjoint (tsupport f) (tsupport g)
def append (T U : DisjointTuple) (hTU : Appendable T U) : DisjointTuple :=
  ⟨T.1 ++ U.1, by
    refine ⟨fun f hf => ?_, List.pairwise_append.2 ⟨T.2.2, U.2.2, hTU⟩⟩
    rcases List.mem_append.1 hf with hf | hf
    · exact T.2.1 f hf
    · exact U.2.1 f hf⟩
end DisjointTuple
abbrev FreeTupleSpace : Type := DisjointTuple →₀ ℂ
def ofTuple (T : DisjointTuple) : FreeTupleSpace := Finsupp.single T 1
def liftFun (s : DisjointTuple → ℂ) : FreeTupleSpace →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ s
theorem liftFun_ofTuple (s : DisjointTuple → ℂ) (T : DisjointTuple) :
    liftFun s (ofTuple T) = s T := by
  simp [liftFun, ofTuple]
def liftMap (m : DisjointTuple → DisjointTuple) : FreeTupleSpace →ₗ[ℂ] FreeTupleSpace :=
  Finsupp.lmapDomain ℂ ℂ m
abbrev O4 := Matrix.orthogonalGroup (Fin 4) ℝ
def translate (v : Fin 4 → ℝ) : (Fin 4 → ℝ) → Fin 4 → ℝ := fun x => x + v
def affineEuclid (R : Matrix (Fin 4) (Fin 4) ℝ) (c : Fin 4 → ℝ) : (Fin 4 → ℝ) → Fin 4 → ℝ :=
  fun x => R *ᵥ x + c
def invMap (φ : (Fin 4 → ℝ) → Fin 4 → ℝ) : (Fin 4 → ℝ) → Fin 4 → ℝ := Function.invFun φ
theorem invMap_affineEuclid {R : Matrix (Fin 4) (Fin 4) ℝ} (hR : R ∈ O4)
    (c x : Fin 4 → ℝ) : invMap (affineEuclid R c) x = R⁻¹ *ᵥ (x - c) := by
  have h₁ : R * Rᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).1 hR
  have hinv : R⁻¹ = Rᵀ := Matrix.inv_eq_right_inv h₁
  have h₂ : Rᵀ * R = 1 := mul_eq_one_comm.1 h₁
  have hinj : Function.Injective (affineEuclid R c) := by
    intro y z hyz
    have hm : R *ᵥ y = R *ᵥ z := add_right_cancel hyz
    have := congrArg (fun u => Rᵀ *ᵥ u) hm
    simpa [Matrix.mulVec_mulVec, h₂] using this
  have hx : affineEuclid R c (R⁻¹ *ᵥ (x - c)) = x := by
    simp [affineEuclid, hinv, Matrix.mulVec_mulVec, h₁]
  calc invMap (affineEuclid R c) x
      = invMap (affineEuclid R c) (affineEuclid R c (R⁻¹ *ᵥ (x - c))) := by rw [hx]
    _ = R⁻¹ *ᵥ (x - c) := Function.leftInverse_invFun hinj _
def pushFun {E : Type*} (φ : (Fin 4 → ℝ) → Fin 4 → ℝ) (f : (Fin 4 → ℝ) → E) :
    (Fin 4 → ℝ) → E := f ∘ invMap φ
theorem pushFun_translate {E : Type*} (v : Fin 4 → ℝ) (f : (Fin 4 → ℝ) → E)
    (x : Fin 4 → ℝ) : pushFun (translate v) f x = f (x - v) := by
  have hinj : Function.Injective (translate v) := fun y z hyz => add_right_cancel hyz
  have hx : translate v (x - v) = x := by simp [translate]
  have : invMap (translate v) x = x - v := by
    calc invMap (translate v) x = invMap (translate v) (translate v (x - v)) := by rw [hx]
      _ = x - v := Function.leftInverse_invFun hinj _
  simp [pushFun, this]
def pushList (φ : (Fin 4 → ℝ) → Fin 4 → ℝ) (L : List RealFun) : List RealFun :=
  L.map (pushFun φ)
open Classical in
def pushTuple (φ : (Fin 4 → ℝ) → Fin 4 → ℝ) (T : DisjointTuple) : DisjointTuple :=
  if h : IsDisjointTuple (pushList φ T.1) then ⟨pushList φ T.1, h⟩ else DisjointTuple.nil
theorem pushTuple_val (φ : (Fin 4 → ℝ) → Fin 4 → ℝ) (T : DisjointTuple)
    (h : IsDisjointTuple (pushList φ T.1)) : (pushTuple φ T).1 = pushList φ T.1 := by
  simp [pushTuple, h]
end DisjointTuples
end YangMills.Construction
