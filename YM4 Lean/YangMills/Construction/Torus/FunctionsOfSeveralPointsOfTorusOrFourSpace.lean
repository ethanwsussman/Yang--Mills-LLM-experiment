import YangMills.Construction.PowerSeries.MultiIndexNotation
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace AmbientPoints
section CoordinatePartials
variable {D : ℕ}
def partialDeriv (j : Fin D) (G : (Fin D → ℝ) → ℂ) : (Fin D → ℝ) → ℂ :=
  fun x => lineDeriv ℝ G x (Pi.single j 1)
def iteratedPartial (α : YangMills.Construction.PowerSeries.MultiIndex D) (G : (Fin D → ℝ) → ℂ) :
    (Fin D → ℝ) → ℂ :=
  (List.finRange D).foldr (fun j H => (partialDeriv j)^[α j] H) G
theorem iteratedPartial_zero (G : (Fin D → ℝ) → ℂ) :
    iteratedPartial (0 : YangMills.Construction.PowerSeries.MultiIndex D) G = G := by
  have key : ∀ l : List (Fin D),
      l.foldr (fun j H => (partialDeriv j)^[(0 : YangMills.Construction.PowerSeries.MultiIndex D) j] H)
        G = G := by
    intro l
    induction l with
    | nil => rfl
    | cons j l ih => simp
  exact key _
def ContinuousPartialsUpTo (U : Set (Fin D → ℝ)) : ℕ → ((Fin D → ℝ) → ℂ) → Prop
  | 0, G => ContinuousOn G U
  | n + 1, G =>
    ContinuousOn G U ∧ ∀ j : Fin D,
      (∀ x ∈ U, LineDifferentiableAt ℝ G x (Pi.single j 1)) ∧
        ContinuousPartialsUpTo U n (partialDeriv j G)
theorem ContinuousPartialsUpTo.continuousOn {U : Set (Fin D → ℝ)} {n : ℕ}
    {G : (Fin D → ℝ) → ℂ} (hG : ContinuousPartialsUpTo U n G) : ContinuousOn G U := by
  cases n with
  | zero => exact hG
  | succ n => exact hG.1
theorem ContinuousPartialsUpTo.of_succ {U : Set (Fin D → ℝ)} {n : ℕ} {G : (Fin D → ℝ) → ℂ}
    (hG : ContinuousPartialsUpTo U (n + 1) G) : ContinuousPartialsUpTo U n G := by
  induction n generalizing G with
  | zero => exact hG.1
  | succ n ih => exact ⟨hG.1, fun j => ⟨(hG.2 j).1, ih (hG.2 j).2⟩⟩
theorem ContinuousPartialsUpTo.mono {U : Set (Fin D → ℝ)} {n n' : ℕ} {G : (Fin D → ℝ) → ℂ}
    (hG : ContinuousPartialsUpTo U n G) (hn : n' ≤ n) : ContinuousPartialsUpTo U n' G := by
  induction hn with
  | refl => exact hG
  | step _ ih => exact (ih hG.of_succ)
def IsCnOn (U : Set (Fin D → ℝ)) (ν : ℕ∞) (G : (Fin D → ℝ) → ℂ) : Prop :=
  IsOpen U ∧ ∀ n : ℕ, (n : ℕ∞) ≤ ν → ContinuousPartialsUpTo U n G
theorem isCnOn_coe_iff (U : Set (Fin D → ℝ)) (n : ℕ) (G : (Fin D → ℝ) → ℂ) :
    IsCnOn U n G ↔ IsOpen U ∧ ContinuousPartialsUpTo U n G :=
  ⟨fun hG => ⟨hG.1, hG.2 n le_rfl⟩,
    fun hG => ⟨hG.1, fun _ hm => hG.2.mono (by exact_mod_cast hm)⟩⟩
theorem isCnOn_top_iff (U : Set (Fin D → ℝ)) (G : (Fin D → ℝ) → ℂ) :
    IsCnOn U ⊤ G ↔ ∀ n : ℕ, IsCnOn U n G :=
  ⟨fun hG _ => ⟨hG.1, fun m _ => hG.2 m le_top⟩,
    fun hG => ⟨(hG 0).1, fun n _ => (hG n).2 n le_rfl⟩⟩
end CoordinatePartials
variable (s : YangMills.Construction.Conventions.StandingParameters)
def tupleProj (E : Ambient) (p : ℕ) (x : Fin (4 * p) → ℝ) :
    YangMills.Construction.AmbientPoints.Tuple s E p :=
  fun i => YangMills.Construction.AmbientPoints.proj s E
    ((YangMills.Construction.AmbientPoints.flattenCoords p).symm x i)
theorem tupleProj_flattenCoords (E : Ambient) {p : ℕ} (u : Fin p → Fin 4 → ℝ) (i : Fin p) :
    tupleProj s E p (YangMills.Construction.AmbientPoints.flattenCoords p u) i =
      YangMills.Construction.AmbientPoints.proj s E (u i) := by
  simp [tupleProj]
theorem tupleProj_surjective (E : Ambient) (p : ℕ) :
    Function.Surjective (tupleProj s E p) := by
  have hone : Function.Surjective (YangMills.Construction.AmbientPoints.proj s E) := by
    cases E
    · intro y
      obtain ⟨b, hb, -⟩ :=
        YangMills.Construction.AmbientPoints.exists_torusProj_eq_euclidNormVec_eq
          (S := YangMills.Construction.PeriodicLattice.torusSide s.L s.m) y
      exact ⟨b, hb⟩
    · exact fun y => ⟨y, rfl⟩
  intro y
  choose b hb using fun i => hone (y i)
  exact ⟨YangMills.Construction.AmbientPoints.flattenCoords p b,
    funext fun i => by rw [tupleProj_flattenCoords, hb]⟩
def IsLiftOfTuple (E : Ambient) {p : ℕ} (y : YangMills.Construction.AmbientPoints.Tuple s E p)
    (x : Fin (4 * p) → ℝ) : Prop :=
  tupleProj s E p x = y
def IsTuplePeriod : Ambient → (p : ℕ) → (Fin (4 * p) → ℝ) → Prop
  | .torus, p, w => ∃ k : Fin (4 * p) → ℤ, ∀ j, w j = s.side * (k j : ℝ)
  | .euclidean, _, w => w = 0
variable {s} {E : Ambient} {p : ℕ}
def IsCn (ν : ℕ∞) (F : YangMills.Construction.AmbientPoints.Tuple s E p → ℂ) : Prop :=
  IsCnOn univ ν (F ∘ tupleProj s E p)
def IsSmoothFn (F : YangMills.Construction.AmbientPoints.Tuple s E p → ℂ) : Prop := IsCn ⊤ F
def multiDeriv (α : YangMills.Construction.PowerSeries.MultiIndex (4 * p))
    (F : YangMills.Construction.AmbientPoints.Tuple s E p → ℂ) :
    YangMills.Construction.AmbientPoints.Tuple s E p → ℂ :=
  Classical.epsilon fun H =>
    H ∘ tupleProj s E p = iteratedPartial α (F ∘ tupleProj s E p)
theorem multiDeriv_comp_tupleProj {α : YangMills.Construction.PowerSeries.MultiIndex (4 * p)}
    {F : YangMills.Construction.AmbientPoints.Tuple s E p → ℂ}
    (hex : ∃ H : YangMills.Construction.AmbientPoints.Tuple s E p → ℂ,
      H ∘ tupleProj s E p = iteratedPartial α (F ∘ tupleProj s E p)) :
    multiDeriv α F ∘ tupleProj s E p = iteratedPartial α (F ∘ tupleProj s E p) :=
  Classical.epsilon_spec hex
theorem multiDeriv_zero (F : YangMills.Construction.AmbientPoints.Tuple s E p → ℂ) :
    multiDeriv (0 : YangMills.Construction.PowerSeries.MultiIndex (4 * p)) F = F := by
  apply (tupleProj_surjective s E p).injective_comp_right
  change multiDeriv (0 : YangMills.Construction.PowerSeries.MultiIndex (4 * p)) F ∘ tupleProj s E p =
    F ∘ tupleProj s E p
  rw [multiDeriv_comp_tupleProj ⟨F, (iteratedPartial_zero _).symm⟩, iteratedPartial_zero]
def cnNorm (n : ℕ) (F : YangMills.Construction.AmbientPoints.Tuple s E p → ℂ) : ℝ≥0∞ :=
  ⨆ α : YangMills.Construction.PowerSeries.MultiIndex (4 * p), ⨆ _ : α.order ≤ n, ⨆ y,
    ENNReal.ofReal ‖multiDeriv α F y‖
def tupleSupNorm (F : YangMills.Construction.AmbientPoints.Tuple s E p → ℂ) : ℝ≥0∞ :=
  ⨆ y, ENNReal.ofReal ‖F y‖
theorem tupleSupNorm_eq_cnNorm_zero (F : YangMills.Construction.AmbientPoints.Tuple s E p → ℂ) :
    tupleSupNorm F = cnNorm 0 F := by
  apply le_antisymm
  · refine iSup_le fun y => ?_
    refine le_iSup_of_le (0 : YangMills.Construction.PowerSeries.MultiIndex (4 * p))
      (le_iSup_of_le (by simp [YangMills.Construction.PowerSeries.MultiIndex.order]) ?_)
    rw [multiDeriv_zero]
    exact le_iSup (fun y => ENNReal.ofReal ‖F y‖) y
  · refine iSup_le fun α => iSup_le fun hα => ?_
    have hzero : α = 0 := by
      funext j
      have hsum : ∑ i, α i = 0 := Nat.le_zero.mp hα
      exact (Finset.sum_eq_zero_iff.mp hsum) j (Finset.mem_univ j)
    rw [hzero, multiDeriv_zero]
    exact le_rfl
def closedSupport (F : YangMills.Construction.AmbientPoints.Tuple s E p → ℂ) :
    Set (YangMills.Construction.AmbientPoints.Tuple s E p) :=
  closure {y | F y ≠ 0}
def SupportedIn (F : YangMills.Construction.AmbientPoints.Tuple s E p → ℂ)
    (A : Set (YangMills.Construction.AmbientPoints.Tuple s E p)) : Prop :=
  closedSupport F ⊆ A
def tensorProd (φ : Fin p → YangMills.Construction.AmbientPoints.Pt s E → ℂ) :
    YangMills.Construction.AmbientPoints.Tuple s E p → ℂ :=
  fun x => ∏ i, φ i (x i)
def tensorPair {q : ℕ} (F : YangMills.Construction.AmbientPoints.Tuple s E p → ℂ)
    (H : YangMills.Construction.AmbientPoints.Tuple s E q → ℂ) :
    YangMills.Construction.AmbientPoints.Tuple s E (p + q) → ℂ :=
  fun z => F (fun i => z (Fin.castAdd q i)) * H (fun i => z (Fin.natAdd p i))
end AmbientPoints
end YangMills.Construction
