import Reconstruction.MinkowskiSpace.LocalityOfTheTensorVectors
import Reconstruction.MinkowskiSpace.LocalityOfTheWightmanValues
import Reconstruction.MinkowskiSpace.ScalarProductsAndDensityOfTheTensorVectors
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.TensorLocality
open MinkowskiSpace FieldForms RealPointVectors WightmanTheory FieldFormHilbert ProjectionMeasures
  OneLoopNotation ComplexHilbert
abbrev appendPairThen {α : Type} {k m : ℕ} (G : Fin k → α) (p q : α) (u : Fin m → α) :
    Fin (k + (m + 2)) → α :=
  Fin.append (m := k) (n := m + 2) G (Fin.cons p (Fin.cons q u))
theorem appendPairThen_castSucc {α : Type} {k m : ℕ} (G : Fin k → α) (p q : α) (u : Fin m → α)
    (j : Fin (k + (m + 1))) (hj : j.1 = k) : appendPairThen G p q u j.castSucc = p := by
  have hc : (j.castSucc : Fin (k + (m + 2))) = Fin.natAdd k (0 : Fin (m + 2)) :=
    Fin.ext (by simp [hj])
  rw [hc]
  simp [appendPairThen, Fin.append_right]
theorem appendPairThen_succ {α : Type} {k m : ℕ} (G : Fin k → α) (p q : α) (u : Fin m → α)
    (j : Fin (k + (m + 1))) (hj : j.1 = k) : appendPairThen G p q u j.succ = q := by
  have hs : (j.succ : Fin (k + (m + 2))) = Fin.natAdd k (Fin.succ 0 : Fin (m + 2)) :=
    Fin.ext (by simp [hj])
  rw [hs]
  simp [appendPairThen, Fin.append_right]
theorem appendPairThen_swap {α : Type} {k m : ℕ} (G : Fin k → α) (p q : α) (u : Fin m → α)
    (j : Fin (k + (m + 1))) (hj : j.1 = k) (i : Fin (k + (m + 2))) :
    appendPairThen G q p u (Equiv.swap (j.castSucc : Fin (k + (m + 2))) j.succ i) =
      appendPairThen G p q u i := by
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · rw [Equiv.swap_apply_of_ne_of_ne]
    · simp only [appendPairThen, Fin.append_left]
    · intro h
      have := congrArg Fin.val h
      simp [hj] at this
      omega
    · intro h
      have := congrArg Fin.val h
      simp [hj] at this
      omega
  · have hc : (j.castSucc : Fin (k + (m + 2))) = Fin.natAdd k (0 : Fin (m + 2)) :=
      Fin.ext (by simp [hj])
    have hs : (j.succ : Fin (k + (m + 2))) = Fin.natAdd k (Fin.succ 0 : Fin (m + 2)) :=
      Fin.ext (by simp [hj])
    refine Fin.cases ?_ (fun l => ?_) l
    · rw [← hc, Equiv.swap_apply_left, appendPairThen_succ G q p u j hj,
        appendPairThen_castSucc G p q u j hj]
    · refine Fin.cases ?_ (fun l => ?_) l
      · rw [← hs, Equiv.swap_apply_right, appendPairThen_castSucc G q p u j hj,
          appendPairThen_succ G p q u j hj]
      · rw [Equiv.swap_apply_of_ne_of_ne]
        · simp [appendPairThen, Fin.append_right]
        · intro h
          have := congrArg Fin.val h
          simp [hj] at this
        · intro h
          have := congrArg Fin.val h
          simp [hj] at this
theorem spacelikeSwapInvariance_holds (hInner : TensorVecInner.Claim)
    (hLocal : WightmanLocality.WightmanLocalityStatement) : SpacelikeSwapInvariance := by
  intro K _ _ _ E Ω A ℘ C hform hE f h m u hsupp
  have H : TensorVecInner.Conclusions E Ω A := hInner E Ω A ℘ C hform
  have hmem : ∀ {r : ℕ} (a : Fin r → TestFn),
      tensorVec E Ω A a ∈ tensorDomainIn E Ω A := by
    intro r a
    rw [H.domain_eq_span]
    exact Submodule.subset_span ⟨⟨r, a⟩, rfl⟩
  refine sub_eq_zero.mp (H.eq_zero_of_inner_eq_zero _ (Submodule.sub_mem _ (hmem _) (hmem _)) ?_)
  intro k g
  rw [inner_sub_right, sub_eq_zero, Submodule.coe_inner, Submodule.coe_inner,
    H.inner_tensorVec, H.inner_tensorVec]
  let G : Fin k → TestFn := fun i => ⟨_, H.conj_mem_schwartz (g (Fin.rev i))⟩
  have hG : ∀ a : Fin (m + 2) → TestFn,
      Fin.append (fun i x => conj ((g (Fin.rev i)).1 x)) (fun i => (a i).1) =
        fun i => (Fin.append (m := k) (n := m + 2) G a i).1 := by
    intro a
    funext i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · simp only [Fin.append_left]
      rfl
    · simp only [Fin.append_right]
  rw [hG, hG]
  let j : Fin (k + (m + 1)) := ⟨k, by omega⟩
  have hj : j.1 = k := rfl
  have key := hLocal E Ω A ℘ C hform hE (k + (m + 1)) j (appendPairThen G h f u) (by
    intro x hx y hy
    rw [appendPairThen_castSucc G h f u j hj] at hx
    rw [appendPairThen_succ G h f u j hj] at hy
    exact hsupp y hy x hx)
  have hfun : (fun i => (appendPairThen G h f u (Equiv.swap j.castSucc j.succ i)).1) =
      fun i => (appendPairThen G f h u i).1 :=
    funext fun i => congrArg Subtype.val (appendPairThen_swap G f h u j hj i)
  rw [hfun] at key
  exact key
end YangMills.Construction.TensorLocality
end
