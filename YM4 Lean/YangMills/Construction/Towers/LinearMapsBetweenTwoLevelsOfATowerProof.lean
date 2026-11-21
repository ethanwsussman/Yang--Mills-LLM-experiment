import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOfTheLinearMapsProof
import YangMills.Construction.Lattice.CovarianceOfTheAveragingMapsProof
import YangMills.Construction.Towers.ComplexFormsUnderTheMapsOfOneStepOnASide
import YangMills.Construction.Towers.ComplexFormsUnderTheMapsOfOneStepOnTheWhole
import YangMills.Construction.Towers.LinearMapsBetweenTwoLevelsOfATower
import YangMills.Construction.Towers.ProductsOfTheAveragesAsMeansOnASide
import YangMills.Construction.Towers.ProductsOfTheAveragesAsMeansOnTheWhole
import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOnTheWholeLatticeProof
import YangMills.Construction.Towers.TransposeOfTheRestrictionOnASide
import YangMills.Construction.Towers.TransposeOfTheRestrictionOnTheWhole
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
namespace TwoLevelMaps
theorem norm_le_maxOperatorNorm {ι : Type*} (f : ι → Matrices.ComplexMatrix2) (i : ι) :
    ENNReal.ofReal ‖f i‖ ≤ maxOperatorNorm f := by apply _root_.YangMills.Construction.Tower.IterateBounds.ofReal_norm_le_maxOperatorNorm <;> assumption
theorem maxOperatorNorm_comp_le {ι κ : Type*} (f : ι → Matrices.ComplexMatrix2) (e : κ → ι) :
    maxOperatorNorm (f ∘ e) ≤ maxOperatorNorm f :=
  iSup_le fun x => norm_le_maxOperatorNorm f (e x)
theorem maxOperatorNorm_add_le {ι : Type*} (f g : ι → Matrices.ComplexMatrix2) :
    maxOperatorNorm (f + g) ≤ maxOperatorNorm f + maxOperatorNorm g := by
  refine iSup_le fun x => ?_
  change ENNReal.ofReal ‖f x + g x‖ ≤ _
  exact (ENNReal.ofReal_le_ofReal (norm_add_le _ _)).trans
    (ENNReal.ofReal_add_le.trans
      (add_le_add (norm_le_maxOperatorNorm f x) (norm_le_maxOperatorNorm g x)))
theorem maxOperatorNorm_sub_le {ι : Type*} (f g : ι → Matrices.ComplexMatrix2) :
    maxOperatorNorm (f - g) ≤ maxOperatorNorm f + maxOperatorNorm g := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.maxOperatorNorm_sub_le <;> assumption
theorem maxOperatorNorm_sum_le {ι κ : Type*} (s : Finset κ) (f : κ → ι → Matrices.ComplexMatrix2) :
    maxOperatorNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, maxOperatorNorm (f i) := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.maxOperatorNorm_finset_sum_le <;> assumption
theorem sum_range_sub_one_mul_pow_add_one (L : ℝ≥0∞) (hL : 1 ≤ L) (r : ℕ) :
    ∑ t ∈ Finset.range r, (L - 1) * L ^ t + 1 = L ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, add_right_comm, ih, pow_succ]
    calc L ^ r + (L - 1) * L ^ r = (1 + (L - 1)) * L ^ r := by ring
      _ = L * L ^ r := by rw [add_tsub_cancel_of_le hL]
      _ = L ^ r * L := mul_comm _ _
theorem le_induction_upTo {k i : ℕ} {p : ∀ l, i ≤ l → Prop} (h0 : i ≤ k → p i le_rfl)
    (hs : ∀ l (h : i ≤ l) (h' : i ≤ l + 1), l + 1 ≤ k → p l h → p (l + 1) h')
    (l : ℕ) (h : i ≤ l) (hl : l ≤ k) : p l h :=
  Nat.le_induction (m := i) (P := fun l h => l ≤ k → p l h) h0
    (fun n hn ih hk => hs n hn _ hk (ih (by omega))) l h hl
theorem levelwiseComposition_mapsTo {F : ℕ → Type*} (step : ∀ j, F j → F (j + 1))
    (S : ∀ j, Set (F j)) {k : ℕ} (hm : ∀ j, j + 1 ≤ k → MapsTo (step j) (S j) (S (j + 1)))
    {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) : MapsTo (levelwiseComposition step h) (S i) (S l) := by
  refine le_induction_upTo (p := fun l h => MapsTo (levelwiseComposition step h) (S i) (S l))
    ?_ ?_ l h hl
  · intro _
    rw [levelwiseComposition_self]
    exact mapsTo_id _
  · intro l h h' hk ih
    rw [levelwiseComposition_succ step h h']
    exact (hm l hk).comp ih
theorem levelwiseComposition_surjOn {F : ℕ → Type*} (step : ∀ j, F j → F (j + 1))
    (S : ∀ j, Set (F j)) {k : ℕ} (hm : ∀ j, j + 1 ≤ k → SurjOn (step j) (S j) (S (j + 1)))
    {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) : SurjOn (levelwiseComposition step h) (S i) (S l) := by
  refine le_induction_upTo (p := fun l h => SurjOn (levelwiseComposition step h) (S i) (S l))
    ?_ ?_ l h hl
  · intro _
    rw [levelwiseComposition_self]
    exact surjOn_id _
  · intro l h h' hk ih
    rw [levelwiseComposition_succ step h h']
    exact (hm l hk).comp ih
theorem levelwiseComposition_zero {F : ℕ → Type*} (step : ∀ j, F j → F (j + 1)) (n : ℕ) :
    levelwiseComposition step (Nat.zero_le n) = composeFromZero step n := by
  induction n with
  | zero =>
    funext B
    show levelwiseComposition step (le_refl 0) B = B
    rw [levelwiseComposition_self]
    rfl
  | succ n ih =>
    rw [levelwiseComposition_succ step (Nat.zero_le n) (Nat.zero_le (n + 1)), ih]
    rfl
structure LevelSystem where
  Links : ℕ → Type
  Points : ℕ → Type
  lin : ∀ j, (Links j → Matrices.ComplexMatrix2) → Links (j + 1) → Matrices.ComplexMatrix2
  cross : ∀ j, (Links j → Matrices.ComplexMatrix2) → Links (j + 1) → Matrices.ComplexMatrix2
  contour : ∀ j, (Links j → Matrices.ComplexMatrix2) → Points (j + 1) → Matrices.ComplexMatrix2
  avg : ∀ j, (Points j → Matrices.ComplexMatrix2) → Points (j + 1) → Matrices.ComplexMatrix2
  cobd : ∀ j, (Points j → Matrices.ComplexMatrix2) → Links j → Matrices.ComplexMatrix2
  embed : ∀ a b, Points b → Points a
  fwd : ∀ j, Points j → Fin 4 → Links j
  cplxForms : ∀ j, Submodule ℂ (Links j → Matrices.ComplexMatrix2)
  realForms : ∀ j, Submodule ℝ (Links j → Matrices.ComplexMatrix2)
  cplxFuns : ∀ j, Submodule ℂ (Points j → Matrices.ComplexMatrix2)
namespace LevelSystem
variable (T : LevelSystem)
def linComp {i l : ℕ} (h : i ≤ l) : (T.Links i → Matrices.ComplexMatrix2) → T.Links l → Matrices.ComplexMatrix2 :=
  levelwiseComposition (F := fun j => T.Links j → Matrices.ComplexMatrix2) T.lin h
def crossComp {i l : ℕ} (h : i ≤ l) : (T.Links i → Matrices.ComplexMatrix2) → T.Links l → Matrices.ComplexMatrix2 :=
  levelwiseComposition (F := fun j => T.Links j → Matrices.ComplexMatrix2) T.cross h
def avgComp {i l : ℕ} (h : i ≤ l) : (T.Points i → Matrices.ComplexMatrix2) → T.Points l → Matrices.ComplexMatrix2 :=
  levelwiseComposition (F := fun j => T.Points j → Matrices.ComplexMatrix2) T.avg h
def contourSum {i l : ℕ} (_h : i ≤ l) (B : T.Links i → Matrices.ComplexMatrix2) :
    T.Points l → Matrices.ComplexMatrix2 :=
  ∑ t ∈ Finset.range (l - i),
    T.contour (i + t) (T.crossComp (Nat.le_add_right i t) B) ∘ T.embed (i + t + 1) l
theorem linComp_self {i : ℕ} (h : i ≤ i) (B : T.Links i → Matrices.ComplexMatrix2) : T.linComp h B = B :=
  congrFun (levelwiseComposition_self (F := fun j => T.Links j → Matrices.ComplexMatrix2) T.lin i) B
theorem crossComp_self {i : ℕ} (h : i ≤ i) (B : T.Links i → Matrices.ComplexMatrix2) : T.crossComp h B = B :=
  congrFun (levelwiseComposition_self (F := fun j => T.Links j → Matrices.ComplexMatrix2) T.cross i) B
theorem avgComp_self {i : ℕ} (h : i ≤ i) (f : T.Points i → Matrices.ComplexMatrix2) : T.avgComp h f = f :=
  congrFun (levelwiseComposition_self (F := fun j => T.Points j → Matrices.ComplexMatrix2) T.avg i) f
theorem linComp_succ {i l : ℕ} (h : i ≤ l) (h' : i ≤ l + 1) (B : T.Links i → Matrices.ComplexMatrix2) :
    T.linComp h' B = T.lin l (T.linComp h B) :=
  congrFun (levelwiseComposition_succ (F := fun j => T.Links j → Matrices.ComplexMatrix2) T.lin h h') B
theorem crossComp_succ {i l : ℕ} (h : i ≤ l) (h' : i ≤ l + 1) (B : T.Links i → Matrices.ComplexMatrix2) :
    T.crossComp h' B = T.cross l (T.crossComp h B) :=
  congrFun (levelwiseComposition_succ (F := fun j => T.Links j → Matrices.ComplexMatrix2) T.cross h h') B
theorem avgComp_succ {i l : ℕ} (h : i ≤ l) (h' : i ≤ l + 1) (f : T.Points i → Matrices.ComplexMatrix2) :
    T.avgComp h' f = T.avg l (T.avgComp h f) :=
  congrFun (levelwiseComposition_succ (F := fun j => T.Points j → Matrices.ComplexMatrix2) T.avg h h') f
structure Satisfies (L k : ℕ) : Prop where
  one_le : 1 ≤ L
  embed_self : ∀ a, a ≤ k → ∀ y, T.embed a a y = y
  embed_embed : ∀ a b c, a ≤ b → b ≤ c → c ≤ k → ∀ y, T.embed a b (T.embed b c y) = T.embed a c y
  cplxFuns_embed : ∀ a b, ∀ f ∈ T.cplxFuns a, f ∘ T.embed a b ∈ T.cplxFuns b
  cobd_mem : ∀ j, ∀ f ∈ T.cplxFuns j, T.cobd j f ∈ T.cplxForms j
  cobd_zero : ∀ j, T.cobd j 0 = 0
  cobd_add : ∀ j f g, T.cobd j (f + g) = T.cobd j f + T.cobd j g
  cobd_norm : ∀ j f, maxOperatorNorm (T.cobd j f) ≤ 2 * maxOperatorNorm f
  lin_sub : ∀ j, j + 1 ≤ k → ∀ B ∈ T.cplxForms j, ∀ B' ∈ T.cplxForms j,
    T.lin j (B - B') = T.lin j B - T.lin j B'
  lin_mem : ∀ j, j + 1 ≤ k → MapsTo (T.lin j) (T.cplxForms j) (T.cplxForms (j + 1))
  cross_mem : ∀ j, j + 1 ≤ k → MapsTo (T.cross j) (T.cplxForms j) (T.cplxForms (j + 1))
  lin_mem_real : ∀ j, j + 1 ≤ k → MapsTo (T.lin j) (T.realForms j) (T.realForms (j + 1))
  cross_mem_real : ∀ j, j + 1 ≤ k → MapsTo (T.cross j) (T.realForms j) (T.realForms (j + 1))
  contour_mem : ∀ j, j + 1 ≤ k → ∀ B ∈ T.cplxForms j, T.contour j B ∈ T.cplxFuns (j + 1)
  avg_mem : ∀ j, j + 1 ≤ k → MapsTo (T.avg j) (T.cplxFuns j) (T.cplxFuns (j + 1))
  lin_eq : ∀ j, j + 1 ≤ k → ∀ B ∈ T.cplxForms j,
    T.lin j B = T.cross j B - T.cobd (j + 1) (T.contour j B)
  lin_cobd : ∀ j, j + 1 ≤ k → ∀ f ∈ T.cplxFuns j,
    T.lin j (T.cobd j f) = T.cobd (j + 1) (f ∘ T.embed j (j + 1))
  cross_cobd : ∀ j, j + 1 ≤ k → ∀ f ∈ T.cplxFuns j, T.cross j (T.cobd j f) = T.cobd (j + 1) (T.avg j f)
  const : ∀ j, j + 1 ≤ k → ∀ B ∈ T.cplxForms j, ∀ a : Fin 4 → Matrices.ComplexMatrix2,
    (∀ x μ, B (T.fwd j x μ) = a μ) →
      T.lin j B = T.cross j B ∧ ∀ x μ, T.cross j B (T.fwd (j + 1) x μ) = (L : ℂ) • a μ
  lin_surj : ∀ j, j + 1 ≤ k → SurjOn (T.lin j) (T.cplxForms j) (T.cplxForms (j + 1))
  cross_surj : ∀ j, j + 1 ≤ k → SurjOn (T.cross j) (T.cplxForms j) (T.cplxForms (j + 1))
  lin_surj_real : ∀ j, j + 1 ≤ k → SurjOn (T.lin j) (T.realForms j) (T.realForms (j + 1))
  cross_surj_real : ∀ j, j + 1 ≤ k → SurjOn (T.cross j) (T.realForms j) (T.realForms (j + 1))
  contour_norm : ∀ j, j + 1 ≤ k → ∀ B ∈ T.cplxForms j,
    maxOperatorNorm (T.contour j B) ≤ 2 * ((L : ℝ≥0∞) - 1) * maxOperatorNorm B
  crossComp_norm : ∀ i l (h : i ≤ l), l ≤ k → ∀ B,
    maxOperatorNorm (T.crossComp h B) ≤ (L : ℝ≥0∞) ^ (l - i) * maxOperatorNorm B
namespace Satisfies
variable {T} {L k : ℕ} (hT : T.Satisfies L k)
include hT
theorem linComp_maps {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) :
    MapsTo (T.linComp h) (T.cplxForms i) (T.cplxForms l) :=
  levelwiseComposition_mapsTo (F := fun j => T.Links j → Matrices.ComplexMatrix2) T.lin
    (fun j => (T.cplxForms j : Set (T.Links j → Matrices.ComplexMatrix2))) hT.lin_mem h hl
theorem crossComp_maps {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) :
    MapsTo (T.crossComp h) (T.cplxForms i) (T.cplxForms l) :=
  levelwiseComposition_mapsTo (F := fun j => T.Links j → Matrices.ComplexMatrix2) T.cross
    (fun j => (T.cplxForms j : Set (T.Links j → Matrices.ComplexMatrix2))) hT.cross_mem h hl
theorem linComp_maps_real {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) :
    MapsTo (T.linComp h) (T.realForms i) (T.realForms l) :=
  levelwiseComposition_mapsTo (F := fun j => T.Links j → Matrices.ComplexMatrix2) T.lin
    (fun j => (T.realForms j : Set (T.Links j → Matrices.ComplexMatrix2))) hT.lin_mem_real h hl
theorem crossComp_maps_real {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) :
    MapsTo (T.crossComp h) (T.realForms i) (T.realForms l) :=
  levelwiseComposition_mapsTo (F := fun j => T.Links j → Matrices.ComplexMatrix2) T.cross
    (fun j => (T.realForms j : Set (T.Links j → Matrices.ComplexMatrix2))) hT.cross_mem_real h hl
theorem avgComp_maps {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) :
    MapsTo (T.avgComp h) (T.cplxFuns i) (T.cplxFuns l) :=
  levelwiseComposition_mapsTo (F := fun j => T.Points j → Matrices.ComplexMatrix2) T.avg
    (fun j => (T.cplxFuns j : Set (T.Points j → Matrices.ComplexMatrix2))) hT.avg_mem h hl
theorem linComp_surj {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) :
    SurjOn (T.linComp h) (T.cplxForms i) (T.cplxForms l) :=
  levelwiseComposition_surjOn (F := fun j => T.Links j → Matrices.ComplexMatrix2) T.lin
    (fun j => (T.cplxForms j : Set (T.Links j → Matrices.ComplexMatrix2))) hT.lin_surj h hl
theorem crossComp_surj {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) :
    SurjOn (T.crossComp h) (T.cplxForms i) (T.cplxForms l) :=
  levelwiseComposition_surjOn (F := fun j => T.Links j → Matrices.ComplexMatrix2) T.cross
    (fun j => (T.cplxForms j : Set (T.Links j → Matrices.ComplexMatrix2))) hT.cross_surj h hl
theorem linComp_surj_real {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) :
    SurjOn (T.linComp h) (T.realForms i) (T.realForms l) :=
  levelwiseComposition_surjOn (F := fun j => T.Links j → Matrices.ComplexMatrix2) T.lin
    (fun j => (T.realForms j : Set (T.Links j → Matrices.ComplexMatrix2))) hT.lin_surj_real h hl
theorem crossComp_surj_real {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) :
    SurjOn (T.crossComp h) (T.realForms i) (T.realForms l) :=
  levelwiseComposition_surjOn (F := fun j => T.Links j → Matrices.ComplexMatrix2) T.cross
    (fun j => (T.realForms j : Set (T.Links j → Matrices.ComplexMatrix2))) hT.cross_surj_real h hl
theorem contourSum_succ {i l : ℕ} (h : i ≤ l) (h' : i ≤ l + 1) (hk : l + 1 ≤ k)
    (B : T.Links i → Matrices.ComplexMatrix2) :
    T.contourSum h' B = T.contour l (T.crossComp h B) + T.contourSum h B ∘ T.embed l (l + 1) := by
  funext y
  have e : l + 1 - i = (l - i) + 1 := by omega
  simp only [contourSum, e, Finset.sum_range_succ]
  simp only [Pi.add_apply, Finset.sum_apply, Function.comp_apply]
  rw [add_comm]
  congr 1
  · have key : ∀ s (hs : i ≤ s), s = l →
        T.contour s (T.crossComp hs B) (T.embed (s + 1) (l + 1) y) = T.contour l (T.crossComp h B) y := by
      rintro s hs rfl
      rw [hT.embed_self _ hk]
    exact key _ _ (by omega)
  · refine Finset.sum_congr rfl fun t ht => ?_
    have := Finset.mem_range.1 ht
    rw [hT.embed_embed (i + t + 1) l (l + 1) (by omega) (by omega) hk]
theorem linComp_eq {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) : ∀ B ∈ T.cplxForms i,
    T.linComp h B = T.crossComp h B - T.cobd l (T.contourSum h B) ∧ T.contourSum h B ∈ T.cplxFuns l := by
  refine le_induction_upTo (p := fun l h => ∀ B ∈ T.cplxForms i,
    T.linComp h B = T.crossComp h B - T.cobd l (T.contourSum h B) ∧ T.contourSum h B ∈ T.cplxFuns l)
    ?_ ?_ l h hl
  · intro _ B _
    have e : T.contourSum (le_refl i) B = 0 := by simp [contourSum]
    rw [e, T.linComp_self, T.crossComp_self, hT.cobd_zero, sub_zero]
    exact ⟨rfl, zero_mem _⟩
  · intro l h h' hk ih B hB
    obtain ⟨e, hm⟩ := ih B hB
    have hC : T.crossComp h B ∈ T.cplxForms l := hT.crossComp_maps h (by omega) hB
    have hd : T.cobd l (T.contourSum h B) ∈ T.cplxForms l := hT.cobd_mem l _ hm
    constructor
    · rw [T.linComp_succ h h', T.crossComp_succ h h', hT.contourSum_succ h h' hk, e,
        hT.lin_sub l hk _ hC _ hd, hT.lin_eq l hk _ hC, hT.lin_cobd l hk _ hm, hT.cobd_add, sub_sub]
    · rw [hT.contourSum_succ h h' hk]
      exact add_mem (hT.contour_mem l hk _ hC) (hT.cplxFuns_embed _ _ _ hm)
theorem linComp_cobd {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) : ∀ f ∈ T.cplxFuns i,
    T.linComp h (T.cobd i f) = T.cobd l (f ∘ T.embed i l) := by
  refine le_induction_upTo (p := fun l h => ∀ f ∈ T.cplxFuns i,
    T.linComp h (T.cobd i f) = T.cobd l (f ∘ T.embed i l)) ?_ ?_ l h hl
  · intro hik f _
    have e : f ∘ T.embed i i = f := by
      funext y
      simp [hT.embed_self i hik]
    rw [e, T.linComp_self]
  · intro l h h' hk ih f hf
    have e : (f ∘ T.embed i l) ∘ T.embed l (l + 1) = f ∘ T.embed i (l + 1) := by
      funext y
      simp [hT.embed_embed i l (l + 1) h (by omega) hk]
    rw [T.linComp_succ h h', ih f hf, hT.lin_cobd l hk _ (hT.cplxFuns_embed _ _ _ hf), e]
theorem crossComp_cobd {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) : ∀ f ∈ T.cplxFuns i,
    T.crossComp h (T.cobd i f) = T.cobd l (T.avgComp h f) := by
  refine le_induction_upTo (p := fun l h => ∀ f ∈ T.cplxFuns i,
    T.crossComp h (T.cobd i f) = T.cobd l (T.avgComp h f)) ?_ ?_ l h hl
  · intro _ f _
    rw [T.crossComp_self, T.avgComp_self]
  · intro l h h' hk ih f hf
    rw [T.crossComp_succ h h', ih f hf, hT.cross_cobd l hk _ (hT.avgComp_maps h (by omega) hf),
      T.avgComp_succ h h']
theorem contourSum_norm {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) (B : T.Links i → Matrices.ComplexMatrix2)
    (hB : B ∈ T.cplxForms i) :
    maxOperatorNorm (T.contourSum h B) ≤ 2 * (L : ℝ≥0∞) ^ (l - i) * maxOperatorNorm B := by
  have hL : (1 : ℝ≥0∞) ≤ L := by exact_mod_cast hT.one_le
  have geo := sum_range_sub_one_mul_pow_add_one (L : ℝ≥0∞) hL (l - i)
  unfold contourSum
  calc maxOperatorNorm (∑ t ∈ Finset.range (l - i),
        T.contour (i + t) (T.crossComp (Nat.le_add_right i t) B) ∘ T.embed (i + t + 1) l)
      ≤ ∑ t ∈ Finset.range (l - i), maxOperatorNorm
        (T.contour (i + t) (T.crossComp (Nat.le_add_right i t) B) ∘ T.embed (i + t + 1) l) :=
        maxOperatorNorm_sum_le _ _
    _ ≤ ∑ t ∈ Finset.range (l - i),
        2 * ((L : ℝ≥0∞) - 1) * ((L : ℝ≥0∞) ^ t * maxOperatorNorm B) := by
        refine Finset.sum_le_sum fun t ht => ?_
        have ht' := Finset.mem_range.1 ht
        have hs : i + t + 1 ≤ k := by omega
        have hm := hT.crossComp_maps (Nat.le_add_right i t) (by omega) hB
        refine (maxOperatorNorm_comp_le _ _).trans ((hT.contour_norm (i + t) hs _ hm).trans ?_)
        have hb := hT.crossComp_norm i (i + t) (Nat.le_add_right i t) (by omega) B
        rw [Nat.add_sub_cancel_left] at hb
        gcongr
    _ = 2 * (∑ t ∈ Finset.range (l - i), ((L : ℝ≥0∞) - 1) * (L : ℝ≥0∞) ^ t) * maxOperatorNorm B := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun t _ => by ring
    _ ≤ 2 * (L : ℝ≥0∞) ^ (l - i) * maxOperatorNorm B := by
        gcongr
        rw [← geo]
        exact le_self_add
theorem linComp_norm {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) (B : T.Links i → Matrices.ComplexMatrix2)
    (hB : B ∈ T.cplxForms i) :
    maxOperatorNorm (T.linComp h B) ≤ 5 * (L : ℝ≥0∞) ^ (l - i) * maxOperatorNorm B := by
  rw [(hT.linComp_eq h hl B hB).1]
  calc maxOperatorNorm (T.crossComp h B - T.cobd l (T.contourSum h B))
      ≤ maxOperatorNorm (T.crossComp h B) + maxOperatorNorm (T.cobd l (T.contourSum h B)) :=
        maxOperatorNorm_sub_le _ _
    _ ≤ (L : ℝ≥0∞) ^ (l - i) * maxOperatorNorm B +
          2 * (2 * (L : ℝ≥0∞) ^ (l - i) * maxOperatorNorm B) :=
        add_le_add (hT.crossComp_norm i l h hl B)
          ((hT.cobd_norm l _).trans (by gcongr; exact hT.contourSum_norm h hl B hB))
    _ = 5 * (L : ℝ≥0∞) ^ (l - i) * maxOperatorNorm B := by ring
theorem comp_const {i l : ℕ} (h : i ≤ l) (hl : l ≤ k) : ∀ B ∈ T.cplxForms i,
    ∀ a : Fin 4 → Matrices.ComplexMatrix2,
    (∀ x μ, B (T.fwd i x μ) = a μ) →
      T.linComp h B = T.crossComp h B ∧
        ∀ x μ, T.crossComp h B (T.fwd l x μ) = (L : ℂ) ^ (l - i) • a μ := by
  refine le_induction_upTo (p := fun l h => ∀ B ∈ T.cplxForms i,
    ∀ a : Fin 4 → Matrices.ComplexMatrix2,
    (∀ x μ, B (T.fwd i x μ) = a μ) →
      T.linComp h B = T.crossComp h B ∧
        ∀ x μ, T.crossComp h B (T.fwd l x μ) = (L : ℂ) ^ (l - i) • a μ) ?_ ?_ l h hl
  · intro _ B _ a ha
    rw [T.linComp_self, T.crossComp_self]
    refine ⟨rfl, fun x μ => ?_⟩
    simp [ha]
  · intro l h h' hk ih B hB a ha
    obtain ⟨e, c⟩ := ih B hB a ha
    obtain ⟨e', c'⟩ := hT.const l hk _ (hT.crossComp_maps h (by omega) hB)
      (fun μ => (L : ℂ) ^ (l - i) • a μ) c
    refine ⟨by rw [T.linComp_succ h h', T.crossComp_succ h h', e, e'], fun x μ => ?_⟩
    rw [T.crossComp_succ h h', c', smul_smul, show l + 1 - i = (l - i) + 1 by omega, pow_succ']
end Satisfies
end LevelSystem
abbrev periodicSystem (L m k : ℕ) : LevelSystem where
  Links := Edge L m k
  Points := Vertex L m k
  lin := linearSmoothing L m k
  cross := crossingSmoothing L m k
  contour := cubeContourAverage L m k
  avg := vertexSmoothing L m k
  cobd := fun _ => vertexCoboundary
  embed := fun a _ y => PeriodicLattice.Site.toSublattice y (PeriodicLattice.levelDepth k a)
  fwd := fun _ x μ => PeriodicLattice.Bond.forwardFrom x μ
  cplxForms := complexEdgeForms L m k
  realForms := edgeFormSpace L m k
  cplxFuns := fun j => Matrices.GroupLieProduct.tracelessFunctions (Vertex L m k j)
section PeriodicCase
open PeriodicLattice (FourTorus refinedBlock crossingPath sitesIn)
variable {L m k : ℕ}
theorem coe_toSublattice (hL : 0 < L) {i i' : ℤ} (hi : i ≤ i') (y : PeriodicLattice.Site L m i) :
    ((PeriodicLattice.Site.toSublattice y i' : PeriodicLattice.Site L m i') : FourTorus L m) = y := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
theorem toSublattice_self (hL : 0 < L) {i : ℤ} (y : PeriodicLattice.Site L m i) :
    PeriodicLattice.Site.toSublattice y i = y :=
  Subtype.ext (coe_toSublattice hL le_rfl y)
theorem toSublattice_toSublattice (hL : 0 < L) {i i' : ℤ} (hi : i ≤ i') (i'' : ℤ)
    (y : PeriodicLattice.Site L m i) :
    PeriodicLattice.Site.toSublattice (PeriodicLattice.Site.toSublattice y i') i'' =
      PeriodicLattice.Site.toSublattice y i'' := by apply _root_.YangMills.Construction.Tower.IterateBounds.toSublattice_toSublattice <;> assumption
theorem levelDepth_anti {a b : ℕ} (h : a ≤ b) :
    PeriodicLattice.levelDepth k b ≤ PeriodicLattice.levelDepth k a := by apply _root_.YangMills.Construction.PeriodicLattice.EquivarianceProof.levelDepth_anti <;> assumption
theorem vertexCoboundary_mem {j : ℕ} {f : Vertex L m k j → Matrices.ComplexMatrix2}
    (hf : f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L m k j)) :
    vertexCoboundary f ∈ complexEdgeForms L m k j := by
  refine (⟨fun b _ => Submodule.sub_mem Matrices.ComplexMatrix2.traceless
      (hf _ (mem_univ _)) (hf _ (mem_univ _)), fun b => ?_⟩ :
    PeriodicLattice.IsBondForm PeriodicLattice.complexLieAlgebra (vertexCoboundary f))
  show f b.source - f b.target = -(f b.target - f b.source)
  rw [neg_sub]
theorem maxOperatorNorm_vertexCoboundary_le {j : ℕ} (f : Vertex L m k j → Matrices.ComplexMatrix2) :
    maxOperatorNorm (vertexCoboundary f) ≤ 2 * maxOperatorNorm f := by
  refine iSup_le fun b => ?_
  change ENNReal.ofReal ‖f b.target - f b.source‖ ≤ _
  rw [two_mul]
  exact (ENNReal.ofReal_le_ofReal (norm_sub_le _ _)).trans
    (ENNReal.ofReal_add_le.trans
      (add_le_add (norm_le_maxOperatorNorm f _) (norm_le_maxOperatorNorm f _)))
theorem crossingSmoothingBetween_norm_le (hLs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hk : 1 ≤ k) (h₃ : IteratedSmoothingMeans.IteratedMeansStatement) (i l : ℕ) (h : i ≤ l)
    (hl : l ≤ k) (B : Edge L m k i → Matrices.ComplexMatrix2) :
    maxOperatorNorm (crossingSmoothingBetween L m k h B) ≤ (L : ℝ≥0∞) ^ (l - i) * maxOperatorNorm B := by
  obtain ⟨n, hn, rfl⟩ : ∃ n, n ≤ l ∧ i = l - n := ⟨l - i, by omega, by omega⟩
  rw [show l - (l - n) = n by omega]
  exact (h₃ L hLs m k n l hm hk hn hl).maxOperatorNorm_iterate_le
    (fun l' h' => crossingSmoothingBetween L m k h') (fun _ => levelwiseComposition_self _ _)
    (fun _ h' h'' => levelwiseComposition_succ _ h' h'') B
theorem periodicSystem_satisfies (hLs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hk : 1 ≤ k) (h₁ : PeriodicCoarseningStep.Holds)
    (h₃ : IteratedSmoothingMeans.IteratedMeansStatement) : (periodicSystem L m k).Satisfies L k := by
  have hL : 0 < L := by have := hLs.2; omega
  have hS := fun j (hj : j + 1 ≤ k) => h₁ L hLs m k j hm hj
  exact
    { one_le := hL
      embed_self := fun a _ y => toSublattice_self hL y
      embed_embed := fun a b c _ hbc _ y => toSublattice_toSublattice hL (levelDepth_anti hbc) _ y
      cplxFuns_embed := fun a b f hf x _ => hf _ (mem_univ _)
      cobd_mem := fun j f hf => vertexCoboundary_mem hf
      cobd_zero := fun j => by
        funext b
        show (0 : Matrices.ComplexMatrix2) - 0 = 0
        simp
      cobd_add := fun j f g => by
        funext b
        show f b.target + g b.target - (f b.source + g b.source) =
          (f b.target - f b.source) + (g b.target - g b.source)
        abel
      cobd_norm := fun j f => maxOperatorNorm_vertexCoboundary_le f
      lin_sub := fun j hj => (hS j hj).linearSmoothing_sub
      lin_mem := fun j hj => (hS j hj).linearSmoothing_mapsTo
      cross_mem := fun j hj => (hS j hj).crossingSmoothing_mapsTo
      lin_mem_real := fun j hj => (hS j hj).linearSmoothing_mapsTo_real
      cross_mem_real := fun j hj => (hS j hj).crossingSmoothing_mapsTo_real
      contour_mem := fun j hj B hB => (hS j hj).cubeContourAverage_mapsTo hB
      avg_mem := fun j hj => (hS j hj).vertexSmoothing_mapsTo
      lin_eq := fun j hj => (hS j hj).linearSmoothing_eq
      lin_cobd := fun j hj => (hS j hj).linearSmoothing_vertexCoboundary
      cross_cobd := fun j hj => (hS j hj).crossingSmoothing_vertexCoboundary
      const := fun j hj B hB a ha => ((hS j hj).of_constant B hB a ha).2
      lin_surj := fun j hj => (hS j hj).linearSmoothing_surjOn
      cross_surj := fun j hj => (hS j hj).crossingSmoothing_surjOn
      lin_surj_real := fun j hj => (hS j hj).linearSmoothing_surjOn_real
      cross_surj_real := fun j hj => (hS j hj).crossingSmoothing_surjOn_real
      contour_norm := fun j hj => (hS j hj).maxOperatorNorm_cubeContourAverage_le
      crossComp_norm := fun i l h hl B => crossingSmoothingBetween_norm_le hLs hm hk h₃ i l h hl B }
theorem oneStepRelations (hLs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℕ}
    (hi : i + 1 ≤ k) (h₁ : PeriodicCoarseningStep.Holds) :
    OneStepRelations L m k i :=
  have h := h₁ L hLs m k i hm hi
  ⟨h.linearSmoothing_eq, h.linearSmoothing_vertexCoboundary, h.crossingSmoothing_vertexCoboundary,
    h.cubeContourAverage_vertexCoboundary, fun B hB a ha => (h.of_constant B hB a ha).1⟩
theorem compositeRelations (hLs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hk : 1 ≤ k)
    (h₁ : PeriodicCoarseningStep.Holds)
    (h₃ : IteratedSmoothingMeans.IteratedMeansStatement)
    (h₅ : RestrictionTranspose.Statement) {n j : ℕ} (hn : n ≤ j) (hj : j ≤ k) :
    CompositeRelations L m k n j := by
  have hT := periodicSystem_satisfies hLs hm hk h₁ h₃
  have hM := h₃ L hLs m k n j hm hk hn hj
  have hle := Nat.sub_le j n
  have hr : j - (j - n) = n := by omega
  have hR := h₅ L hLs m k (j - n) j hm hle hj (complexRestriction L m k (j - n) j)
    (fun _ => rfl)
  exact
    { linearSmoothing_eq := fun B hB => (hT.linComp_eq hle hj B hB).1
      linearSmoothing_coboundary := fun f hf => hT.linComp_cobd hle hj f hf
      crossingSmoothing_coboundary := fun f hf => hT.crossComp_cobd hle hj f hf
      vertexSmoothing_eq := fun f _ y => hM.vertexSmoothing_iterate_eq
        (fun l h' => vertexSmoothingBetween L m k h') (fun _ => levelwiseComposition_self _ _)
        (fun _ h' h'' => levelwiseComposition_succ _ h' h'') f y
      crossingSmoothing_eq := fun B _ c => hM.crossingSmoothing_iterate_eq
        (fun l h' => crossingSmoothingBetween L m k h') (fun _ => levelwiseComposition_self _ _)
        (fun _ h' h'' => levelwiseComposition_succ _ h' h'') B c
      crossingPath_length := hM.crossingPath_length
      crossingSmoothing_norm_le := fun B _ => hM.maxOperatorNorm_iterate_le
        (fun l h' => crossingSmoothingBetween L m k h') (fun _ => levelwiseComposition_self _ _)
        (fun _ h' h'' => levelwiseComposition_succ _ h' h'') B
      cubeContourAverage_norm_le := fun B hB => by
        have h := hT.contourSum_norm hle hj B hB
        rw [hr] at h
        exact h
      linearSmoothing_norm_le := fun B hB => by
        have h := hT.linComp_norm hle hj B hB
        rw [hr] at h
        exact h
      of_constant := fun B hB a ha => by
        obtain ⟨e, c⟩ := hT.comp_const hle hj B hB a ha
        rw [hr] at c
        exact ⟨e, hT.crossComp_maps hle hj hB, c⟩
      linearSmoothing_mapsTo_surjOn := ⟨hT.linComp_maps hle hj, hT.linComp_surj hle hj⟩
      crossingSmoothing_mapsTo_surjOn := ⟨hT.crossComp_maps hle hj, hT.crossComp_surj hle hj⟩
      linearSmoothing_mapsTo_surjOn_real :=
        ⟨hT.linComp_maps_real hle hj, hT.linComp_surj_real hle hj⟩
      crossingSmoothing_mapsTo_surjOn_real :=
        ⟨hT.crossComp_maps_real hle hj, hT.crossComp_surj_real hle hj⟩
      restriction_preservesFiniteSupport := hR.preservesFiniteSupport
      restriction_isTransposeMap := hR.isTranspose
      transposeMap_eq := fun g => by
        classical
        funext x
        unfold extendByZero
        split_ifs with hx
        · exact hR.transpose_apply_of_coarse g x _ hx.choose_spec
        · exact hR.transpose_apply_of_not_coarse g x hx
      restrict_transposeMap := hR.restrict_transpose }
theorem iterateFromBare_eq (f : ∀ j, (Edge L m k j → Matrices.ComplexMatrix2) → Edge L m k (j + 1) →
    Matrices.ComplexMatrix2) (n : ℕ) :
    PeriodicLattice.iterateFromBare f n =
      composeFromZero (F := fun j => Edge L m k j → Matrices.ComplexMatrix2) f n := by
  induction n with
  | zero =>
    funext B
    rfl
  | succ n ih =>
    funext B
    show f n (PeriodicLattice.iterateFromBare f n B) =
      f n (composeFromZero (F := fun j => Edge L m k j → Matrices.ComplexMatrix2) f n B)
    rw [ih]
theorem crossingSmoothingBetween_zero (n : ℕ) (B : Edge L m k 0 → Matrices.ComplexMatrix2) :
    crossingSmoothingBetween L m k (Nat.zero_le n) B = crossingSmoothingIter L m k n B :=
  congrFun ((levelwiseComposition_zero (F := fun j => Edge L m k j → Matrices.ComplexMatrix2)
    (crossingSmoothing L m k) n).trans (iterateFromBare_eq _ n).symm) B
theorem compositesFromBase (L m k n : ℕ) : CompositesFromBase L m k n where
  linearSmoothing_eq := fun B _ => congrFun
    ((levelwiseComposition_zero (F := fun j => Edge L m k j → Matrices.ComplexMatrix2)
      (linearSmoothing L m k) n).trans (iterateFromBare_eq _ n).symm) B
  crossingSmoothing_eq := fun B _ => crossingSmoothingBetween_zero n B
  vertexSmoothing_eq := fun f _ => congrFun
    (levelwiseComposition_zero (F := fun j => Vertex L m k j → Matrices.ComplexMatrix2)
      (vertexSmoothing L m k) n) f
  cubeContourAverage_eq := fun B _ => by
    show ∑ t ∈ Finset.range (n - 0), restrictVertexFunction n (cubeContourAverage L m k (0 + t)
        (crossingSmoothingBetween L m k (Nat.le_add_right 0 t) B)) =
      ∑ i ∈ Finset.range n,
        restrictVertexFunction n (cubeContourAverage L m k i (crossingSmoothingIter L m k i B))
    refine Finset.sum_congr (by simp) fun t _ => ?_
    have key : ∀ s (hs : 0 ≤ s), s = t →
        restrictVertexFunction n (cubeContourAverage L m k s (crossingSmoothingBetween L m k hs B)) =
          restrictVertexFunction n (cubeContourAverage L m k t (crossingSmoothingIter L m k t B)) := by
      rintro s hs rfl
      rw [crossingSmoothingBetween_zero]
    exact key _ _ (by omega)
end PeriodicCase
end TwoLevelMaps
namespace FullSpace.TwoLevelMaps
open YangMills.Construction.Tower.TwoLevelMaps
  (LevelSystem norm_le_maxOperatorNorm levelwiseComposition_zero)
open InfiniteLattice (AmbientSpace)
abbrev fullSpaceSystem (L k : ℕ) : LevelSystem where
  Links := Edge L k
  Points := Vertex L k
  lin := fun j => linearSmoothing (a := meshAt L k (j + 1)) (a' := meshAt L k j) L
  cross := fun j => crossingSmoothing (a := meshAt L k (j + 1)) (a' := meshAt L k j) L
  contour := fun j => cubeContourAverage (a := meshAt L k (j + 1)) (a' := meshAt L k j) L
  avg := fun j => vertexSmoothing (a := meshAt L k (j + 1)) (a' := meshAt L k j) L
  cobd := fun _ => vertexCoboundary
  embed := fun a _ y => toFiner (meshAt L k a) y
  fwd := fun _ x μ => InfiniteLattice.Link.forwardFrom x μ
  cplxForms := fun j => complexEdgeForms (meshAt L k j)
  realForms := fun j => edgeFormSpace (meshAt L k j)
  cplxFuns := fun j => Matrices.GroupLieProduct.tracelessFunctions (Vertex L k j)
variable {L k : ℕ}
theorem latticeSubgroup_subset_of_le (L k i j : ℕ) (hL : L ≠ 0) (hij : i ≤ j) :
    (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) ⊆
      InfiniteLattice.latticeSubgroup (meshAt L k i) := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.latticeSubgroup_meshAt_subset_of_le <;> assumption
theorem coe_toFiner {a : ℝ} (a' : ℝ) (y : InfiniteLattice.LatticePoint a)
    (h : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a') :
    ((toFiner a' y : InfiniteLattice.LatticePoint a') : AmbientSpace) = y := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.coe_toFiner <;> assumption
theorem toFiner_toFiner {a a' : ℝ} (a'' : ℝ) (y : InfiniteLattice.LatticePoint a)
    (h : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a') :
    toFiner a'' (toFiner a' y) = toFiner a'' y := by
  have e := coe_toFiner a' y h
  unfold toFiner at e ⊢
  rw [e]
theorem vertexCoboundary_mem {j : ℕ} {f : Vertex L k j → Matrices.ComplexMatrix2}
    (hf : f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L k j)) :
    vertexCoboundary f ∈ complexEdgeForms (meshAt L k j) := by
  refine (⟨fun b _ => Submodule.sub_mem Matrices.ComplexMatrix2.traceless
      (hf _ (mem_univ _)) (hf _ (mem_univ _)), fun b => ?_⟩ :
    (∀ b : InfiniteLattice.Link (meshAt L k j), b.IsPositivelyOriented →
      vertexCoboundary f b ∈ PeriodicLattice.complexLieAlgebra) ∧
      ∀ b : InfiniteLattice.Link (meshAt L k j),
        vertexCoboundary f b.opposite = -vertexCoboundary f b)
  show f b.initial - f b.terminal = -(f b.terminal - f b.initial)
  rw [neg_sub]
theorem maxOperatorNorm_vertexCoboundary_le {a : ℝ} (f : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) :
    maxOperatorNorm (vertexCoboundary f) ≤ 2 * maxOperatorNorm f := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.maxOperatorNorm_vertexCoboundary_le <;> assumption
theorem crossingSmoothingBetween_norm_le (hLs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (h₄ : IteratedSmoothing.IteratedSmoothingAsMeans) (i l : ℕ) (h : i ≤ l) (hl : l ≤ k)
    (B : Edge L k i → Matrices.ComplexMatrix2) :
    maxOperatorNorm (crossingSmoothingBetween L k h B) ≤ (L : ℝ≥0∞) ^ (l - i) * maxOperatorNorm B := by
  obtain ⟨n, hn, rfl⟩ : ∃ n, n ≤ l ∧ i = l - n := ⟨l - i, by omega, by omega⟩
  rw [show l - (l - n) = n by omega]
  exact (h₄ L hLs k n l hk hn hl).maxOperatorNorm_crossingSmoothing_iterate_le
    (fun l' h' => crossingSmoothingBetween L k h') (fun _ => levelwiseComposition_self _ _)
    (fun _ h' h'' => levelwiseComposition_succ _ h' h'') B
theorem fullSpaceSystem_satisfies (hLs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (h₂ : OneStepComplexForms.OneStepClaim)
    (h₄ : IteratedSmoothing.IteratedSmoothingAsMeans) : (fullSpaceSystem L k).Satisfies L k := by
  have hL : 0 < L := by have := hLs.2; omega
  have hS := fun j (hj : j + 1 ≤ k) => h₂ L hLs k j hj
  exact
    { one_le := hL
      embed_self := fun a _ y => Subtype.ext (coe_toFiner _ y y.2)
      embed_embed := fun a b c _ hbc _ y =>
        toFiner_toFiner _ y (latticeSubgroup_subset_of_le L k b c hL.ne' hbc y.2)
      cplxFuns_embed := fun a b f hf x _ => hf _ (mem_univ _)
      cobd_mem := fun j f hf => vertexCoboundary_mem hf
      cobd_zero := fun j => by
        funext b
        show (0 : Matrices.ComplexMatrix2) - 0 = 0
        simp
      cobd_add := fun j f g => by
        funext b
        show f b.terminal + g b.terminal - (f b.initial + g b.initial) =
          (f b.terminal - f b.initial) + (g b.terminal - g b.initial)
        abel
      cobd_norm := fun j f => maxOperatorNorm_vertexCoboundary_le f
      lin_sub := fun j hj => (hS j hj).linearSmoothing_sub
      lin_mem := fun j hj => (hS j hj).linearSmoothing_mapsTo
      cross_mem := fun j hj => (hS j hj).crossingSmoothing_mapsTo
      lin_mem_real := fun j hj => (hS j hj).linearSmoothing_mapsTo_real
      cross_mem_real := fun j hj => (hS j hj).crossingSmoothing_mapsTo_real
      contour_mem := fun j hj B hB => (hS j hj).cubeContourAverage_mapsTo hB
      avg_mem := fun j hj => (hS j hj).vertexSmoothing_mapsTo
      lin_eq := fun j hj => (hS j hj).linearSmoothing_eq
      lin_cobd := fun j hj => (hS j hj).linearSmoothing_coboundary
      cross_cobd := fun j hj => (hS j hj).crossingSmoothing_coboundary
      const := fun j hj B hB a ha => ((hS j hj).of_constant B hB a ha).2
      lin_surj := fun j hj => (hS j hj).linearSmoothing_surjOn
      cross_surj := fun j hj => (hS j hj).crossingSmoothing_surjOn
      lin_surj_real := fun j hj => (hS j hj).linearSmoothing_surjOn_real
      cross_surj_real := fun j hj => (hS j hj).crossingSmoothing_surjOn_real
      contour_norm := fun j hj => (hS j hj).maxOperatorNorm_cubeContourAverage_le
      crossComp_norm := fun i l h hl B => crossingSmoothingBetween_norm_le hLs hk h₄ i l h hl B }
theorem oneStepRelations (hLs : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ} (hi : i + 1 ≤ k)
    (h₂ : OneStepComplexForms.OneStepClaim) :
    OneStepRelations L k i :=
  have h := h₂ L hLs k i hi
  ⟨h.linearSmoothing_eq, h.linearSmoothing_coboundary, h.crossingSmoothing_coboundary,
    h.cubeContourAverage_coboundary, fun B hB a ha => (h.of_constant B hB a ha).1⟩
theorem compositeRelations (hLs : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (h₂ : OneStepComplexForms.OneStepClaim)
    (h₄ : IteratedSmoothing.IteratedSmoothingAsMeans)
    (h₆ : RestrictionTranspose.MainStatement) {n j : ℕ} (hn : n ≤ j) (hj : j ≤ k) :
    CompositeRelations L k n j := by
  have hT := fullSpaceSystem_satisfies hLs hk h₂ h₄
  have hM := h₄ L hLs k n j hk hn hj
  have hle := Nat.sub_le j n
  have hr : j - (j - n) = n := by omega
  have hR := h₆ L hLs k (j - n) j hle hj (complexRestriction L k (j - n) j)
    (fun _ => rfl)
  exact
    { linearSmoothing_eq := fun B hB => (hT.linComp_eq hle hj B hB).1
      linearSmoothing_coboundary := fun f hf => hT.linComp_cobd hle hj f hf
      crossingSmoothing_coboundary := fun f hf => hT.crossComp_cobd hle hj f hf
      vertexSmoothing_eq := fun f _ y => hM.vertexSmoothing_iterate_eq
        (fun l h' => vertexSmoothingBetween L k h') (fun _ => levelwiseComposition_self _ _)
        (fun _ h' h'' => levelwiseComposition_succ _ h' h'') f y
      crossingSmoothing_eq := fun B _ c => hM.crossingSmoothing_iterate_eq
        (fun l h' => crossingSmoothingBetween L k h') (fun _ => levelwiseComposition_self _ _)
        (fun _ h' h'' => levelwiseComposition_succ _ h' h'') B c
      crossingPath_length := hM.crossingPath_length
      crossingSmoothing_norm_le := fun B _ => hM.maxOperatorNorm_crossingSmoothing_iterate_le
        (fun l h' => crossingSmoothingBetween L k h') (fun _ => levelwiseComposition_self _ _)
        (fun _ h' h'' => levelwiseComposition_succ _ h' h'') B
      cubeContourAverage_norm_le := fun B hB => by
        have h := hT.contourSum_norm hle hj B hB
        rw [hr] at h
        exact h
      linearSmoothing_norm_le := fun B hB => by
        have h := hT.linComp_norm hle hj B hB
        rw [hr] at h
        exact h
      of_constant := fun B hB a ha => by
        obtain ⟨e, c⟩ := hT.comp_const hle hj B hB a ha
        rw [hr] at c
        exact ⟨e, hT.crossComp_maps hle hj hB, c⟩
      linearSmoothing_mapsTo_surjOn := ⟨hT.linComp_maps hle hj, hT.linComp_surj hle hj⟩
      crossingSmoothing_mapsTo_surjOn := ⟨hT.crossComp_maps hle hj, hT.crossComp_surj hle hj⟩
      linearSmoothing_mapsTo_surjOn_real :=
        ⟨hT.linComp_maps_real hle hj, hT.linComp_surj_real hle hj⟩
      crossingSmoothing_mapsTo_surjOn_real :=
        ⟨hT.crossComp_maps_real hle hj, hT.crossComp_surj_real hle hj⟩
      restriction_preservesFiniteSupport := hR.preservesFiniteSupport
      restriction_isTransposeMap := hR.isTransposeMap
      transposeMap_eq := fun g => by
        classical
        funext x
        unfold extendByZero
        split_ifs with hx
        · exact hR.apply_of_coe_eq g x _ hx.choose_spec
        · exact hR.apply_of_not_mem g x hx
      restrict_transposeMap := hR.restrict_transposeMap }
theorem crossingSmoothingBetween_zero (n : ℕ) (B : Edge L k 0 → Matrices.ComplexMatrix2) :
    crossingSmoothingBetween L k (Nat.zero_le n) B = crossingSmoothingIter L k n B :=
  congrFun (levelwiseComposition_zero (F := fun j => Edge L k j → Matrices.ComplexMatrix2)
    (fun _ => crossingSmoothing L) n) B
theorem compositesFromBase (L k n : ℕ) : CompositesFromBase L k n where
  linearSmoothing_eq := fun B _ => congrFun
    (levelwiseComposition_zero (F := fun j => Edge L k j → Matrices.ComplexMatrix2)
      (fun _ => linearSmoothing L) n) B
  crossingSmoothing_eq := fun B _ => crossingSmoothingBetween_zero n B
  vertexSmoothing_eq := fun f _ => congrFun
    (levelwiseComposition_zero (F := fun j => Vertex L k j → Matrices.ComplexMatrix2)
      (fun _ => vertexSmoothing L) n) f
  cubeContourAverage_eq := fun B _ => by
    show ∑ t ∈ Finset.range (n - 0), restrictVertexFunction (meshAt L k n)
        (cubeContourAverage (a := meshAt L k (0 + t + 1)) L
          (crossingSmoothingBetween L k (Nat.le_add_right 0 t) B)) =
      ∑ i ∈ Finset.range n, restrictVertexFunction (meshAt L k n)
        (cubeContourAverage (a := meshAt L k (i + 1)) L (crossingSmoothingIter L k i B))
    refine Finset.sum_congr (by simp) fun t _ => ?_
    have key : ∀ s (hs : 0 ≤ s), s = t →
        restrictVertexFunction (meshAt L k n) (cubeContourAverage (a := meshAt L k (s + 1)) L
          (crossingSmoothingBetween L k hs B)) =
        restrictVertexFunction (meshAt L k n) (cubeContourAverage (a := meshAt L k (t + 1)) L
          (crossingSmoothingIter L k t B)) := by
      rintro s hs rfl
      rw [crossingSmoothingBetween_zero]
    exact key _ _ (by omega)
end FullSpace.TwoLevelMaps
namespace TwoLevelMaps
theorem statement_of_parts (h₁ : PeriodicCoarseningStep.Holds)
    (h₂ : FullSpace.OneStepComplexForms.OneStepClaim)
    (h₃ : IteratedSmoothingMeans.IteratedMeansStatement)
    (h₄ : FullSpace.IteratedSmoothing.IteratedSmoothingAsMeans)
    (h₅ : RestrictionTranspose.Statement)
    (h₆ : FullSpace.RestrictionTranspose.MainStatement) : Statement := by
  intro L hLs k hk
  exact ⟨fun m hm => ⟨fun _ hi => oneStepRelations hLs hm hi h₁,
      fun _ _ _ hn hj => compositeRelations hLs hm hk h₁ h₃ h₅ hn hj,
      fun n _ => compositesFromBase L m k n⟩,
    fun _ hi => FullSpace.TwoLevelMaps.oneStepRelations hLs hi h₂,
    fun _ _ _ hn hj =>
      FullSpace.TwoLevelMaps.compositeRelations hLs hk h₂ h₄ h₆ hn hj,
    fun n _ => FullSpace.TwoLevelMaps.compositesFromBase L k n⟩
end TwoLevelMaps
end YangMills.Construction.Tower
end
