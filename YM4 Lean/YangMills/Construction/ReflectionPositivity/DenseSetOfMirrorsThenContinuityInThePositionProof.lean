import YangMills.Construction.LinearAlgebra.BoundedMultilinearForms
import YangMills.Construction.PassageToTheLimit.MovingAMirrorIsTranslatingTheImage
import YangMills.Construction.PassageToTheLimit.NestedPositions
import YangMills.Construction.PassageToTheLimit.SpacesOfTestFunctionsProductsAndSeparatedTuples
import YangMills.Construction.ReflectionPositivity.DenseSetOfMirrorsThenContinuityInThePosition
import YangMills.Construction.ReflectionPositivity.InequalityPassesToTheLimitAtFixedTuples
import YangMills.Construction.ReflectionPositivity.MirrorsAndSides
import Mathlib
set_option autoImplicit false
open Filter
open scoped ENNReal Topology ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.DenseMirrors
section Forms
variable {Pt : Type} {n : ℕ}
def IsMultilinearOnSubmodules (W : Fin n → Submodule ℝ (Pt → ℝ)) (Φ : (Fin n → Pt → ℝ) → ℝ) : Prop :=
  ∀ (i : Fin n) (a b : ℝ) (x y z : Fin n → Pt → ℝ), (∀ j, x j ∈ W j) → (∀ j, y j ∈ W j) →
    (∀ j, z j ∈ W j) → (∀ j, j ≠ i → y j = x j) → (∀ j, j ≠ i → z j = x j) →
    z i = a • x i + b • y i → Φ z = a * Φ x + b * Φ y
def seminormOfSubmodule (W : Submodule ℝ (Pt → ℝ)) (N : (Pt → ℝ) → ℝ)
    (hs : ∀ (a : ℝ), ∀ f ∈ W, N (a • f) = |a| * N f)
    (ha : ∀ f ∈ W, ∀ g ∈ W, N (f + g) ≤ N f + N g) : Seminorm ℝ W where
  toFun f := N f.1
  map_zero' := by simpa using hs 0 0 W.zero_mem
  add_le' f g := ha _ f.2 _ g.2
  neg' f := by
    have h := hs (-1) f.1 f.2
    simpa using h
  smul' a f := by simpa using hs a f.1 f.2
def multilinearOfSubmodules (W : Fin n → Submodule ℝ (Pt → ℝ)) (Φ : (Fin n → Pt → ℝ) → ℝ)
    (hl : IsMultilinearOnSubmodules W Φ) : MultilinearMap ℝ (fun j => W j) ℝ where
  toFun x := Φ fun j => (x j).1
  map_update_add' := by
    intro _ m i u v
    refine hl i 1 1 _ _ _ (fun j => (Function.update m i u j).2)
      (fun j => (Function.update m i v j).2) (fun j => (Function.update m i (u + v) j).2)
      (fun j hj => ?_) (fun j hj => ?_) ?_ |>.trans (by simp)
    · simp [Function.update_of_ne hj]
    · simp [Function.update_of_ne hj]
    · simp
  map_update_smul' := by
    intro _ m i a u
    refine hl i a 0 _ _ _ (fun j => (Function.update m i u j).2)
      (fun j => (Function.update m i u j).2) (fun j => (Function.update m i (a • u) j).2)
      (fun _ _ => rfl) (fun j hj => ?_) ?_ |>.trans (by simp)
    · simp [Function.update_of_ne hj]
    · simp
theorem tendsto_of_multilinear_bound (hF : Multilinear.BoundedMultilinearEstimates)
    (hn : 1 ≤ n) (W : Fin n → Submodule ℝ (Pt → ℝ)) (N : (Pt → ℝ) → ℝ)
    (h0 : ∀ j, ∀ f ∈ W j, 0 ≤ N f)
    (hs : ∀ j, ∀ (a : ℝ), ∀ f ∈ W j, N (a • f) = |a| * N f)
    (ha : ∀ j, ∀ f ∈ W j, ∀ g ∈ W j, N (f + g) ≤ N f + N g)
    (Φ : (Fin n → Pt → ℝ) → ℝ) (hl : IsMultilinearOnSubmodules W Φ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x : Fin n → Pt → ℝ, (∀ j, x j ∈ W j) → |Φ x| ≤ C * ∏ j, N (x j))
    {α : Type*} {F : Filter α} (e : α → Fin n → Pt → ℝ) (g : Fin n → Pt → ℝ)
    (hg : ∀ j, g j ∈ W j) (he : ∀ᶠ a in F, ∀ j, e a j ∈ W j)
    (ht : ∀ j, Tendsto (fun a => ENNReal.ofReal (N (e a j - g j))) F (𝓝 0)) :
    Tendsto (fun a => Φ (e a)) F (𝓝 (Φ g)) := by
  have ht' : ∀ j, Tendsto (fun a => N (e a j - g j)) F (𝓝 0) := fun j => by
    have h₁ := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (ht j)
    simp only [ENNReal.toReal_zero] at h₁
    refine h₁.congr' ?_
    filter_upwards [he] with a hae
    simp only [Function.comp_apply]
    exact ENNReal.toReal_ofReal (h0 j _ ((W j).sub_mem (hae j) (hg j)))
  have hN : ∀ j, Tendsto (fun a => N (e a j)) F (𝓝 (N (g j))) := fun j => by
    refine tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' ?_ (ht' j))
    filter_upwards [he] with a hae
    have hd := (W j).sub_mem (hae j) (hg j)
    have h₁ := ha j _ hd _ (hg j)
    have h₂ := ha j _ ((W j).smul_mem (-1) hd) _ (hae j)
    rw [hs j (-1) _ hd] at h₂
    have e₁ : e a j - g j + g j = e a j := by abel
    have e₂ : (-1 : ℝ) • (e a j - g j) + e a j = g j := by
      rw [neg_one_smul]
      abel
    rw [e₁] at h₁
    rw [e₂] at h₂
    simp only [abs_neg, abs_one, one_mul] at h₂
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have key := (hF n hn (fun j => W j)
    (fun j => seminormOfSubmodule (W j) N (hs j) (ha j))).1 (multilinearOfSubmodules W Φ hl) C hC
    (fun h => hb _ fun j => (h j).2)
  have hu : Tendsto (fun a => C * ∑ l, N (e a l - g l) *
      ∏ l' ∈ Finset.univ.erase l, (N (e a l') + N (g l'))) F (𝓝 0) := by
    have h₁ : Tendsto (fun a => C * ∑ l, N (e a l - g l) *
        ∏ l' ∈ Finset.univ.erase l, (N (e a l') + N (g l'))) F
        (𝓝 (C * ∑ l : Fin n, 0 * ∏ l' ∈ Finset.univ.erase l, (N (g l') + N (g l')))) :=
      Tendsto.const_mul _ (tendsto_finsetSum _ fun l _ => (ht' l).mul
        (tendsto_finsetProd _ fun l' _ => (hN l').add tendsto_const_nhds))
    simpa using h₁
  refine tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' ?_ hu)
  filter_upwards [he] with a hae
  have h₁ := key (fun j => ⟨e a j, hae j⟩) (fun j => ⟨g j, hg j⟩)
  exact h₁.1.trans h₁.2
end Forms
section OnTheSpaces
open Ambient
variable (D : MirrorData)
theorem exists_submodule_compactC1SuppIn
    (hP : LimitSpaces.Ambient.testSpacesAndSepTuples) (E : Ambient)
    (A : Set (E.Point D)) :
    ∃ W : Submodule ℝ (E.Point D → ℝ), ∀ f, f ∈ W ↔ f ∈ compactC1SuppIn D E A := by
  cases E with
  | torus =>
    obtain ⟨W, hW⟩ := (hP D.toStandingParameters .periodic ⟨1, Set.mem_Ici.2 le_rfl⟩ A A 1 le_rfl).1.2.2.1
    refine ⟨W, fun f => ?_⟩
    have h : f ∈ W ↔ f ∈ LimitSpaces.Ambient.periodic.c1Within D.toStandingParameters A := by
      rw [← hW]
      rfl
    exact h.trans ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1.2, h.2⟩⟩
  | euclidean =>
    obtain ⟨W, hW⟩ := (hP D.toStandingParameters .euclidean ⟨1, Set.mem_Ici.2 le_rfl⟩ A A 1 le_rfl).1.2.2.1
    refine ⟨W, fun f => ?_⟩
    have h : f ∈ W ↔ f ∈ LimitSpaces.Ambient.euclidean.c1Within D.toStandingParameters A := by
      rw [← hW]
      rfl
    exact h.trans ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1.2, h.2⟩⟩
theorem normSharp_seminorm_props_limit
    (hP : LimitSpaces.Ambient.testSpacesAndSepTuples)
    (P : LimitSpaces.Ambient) (M : ScaleParam) (A : Set (P.Carrier D.toStandingParameters)) :
    (∀ f ∈ P.c1Within D.toStandingParameters A, 0 ≤ P.normSharp D.toStandingParameters M f) ∧
    (∀ (a : ℝ), ∀ f ∈ P.c1Within D.toStandingParameters A,
      P.normSharp D.toStandingParameters M (a • f) = |a| * P.normSharp D.toStandingParameters M f) ∧
    ∀ f ∈ P.c1Within D.toStandingParameters A, ∀ g ∈ P.c1Within D.toStandingParameters A,
      P.normSharp D.toStandingParameters M (f + g) ≤
        P.normSharp D.toStandingParameters M f + P.normSharp D.toStandingParameters M g := by
  obtain ⟨-, -, -, hsub, ⟨h₁, -, h₂, h₃⟩, -⟩ := (hP D.toStandingParameters P M A A 1 le_rfl).1
  exact ⟨fun f hf => h₁ f (hsub hf), fun a f hf => h₂ a f (hsub hf),
    fun f hf g hg => h₃ f (hsub hf) g (hsub hg)⟩
theorem normSharp_seminorm_props
    (hP : LimitSpaces.Ambient.testSpacesAndSepTuples) (M : ScaleParam)
    (E : Ambient) (A : Set (E.Point D)) :
    (∀ f ∈ compactC1SuppIn D E A, 0 ≤ normSharp D M E f) ∧
    (∀ (a : ℝ), ∀ f ∈ compactC1SuppIn D E A, normSharp D M E (a • f) = |a| * normSharp D M E f) ∧
    ∀ f ∈ compactC1SuppIn D E A, ∀ g ∈ compactC1SuppIn D E A,
      normSharp D M E (f + g) ≤ normSharp D M E f + normSharp D M E g := by
  cases E with
  | torus =>
    obtain ⟨h₁, h₂, h₃⟩ := normSharp_seminorm_props_limit D hP .periodic M A
    exact ⟨fun f hf => h₁ f ⟨hf.1, hf.1.2, hf.2⟩, fun a f hf => h₂ a f ⟨hf.1, hf.1.2, hf.2⟩,
      fun f hf g hg => h₃ f ⟨hf.1, hf.1.2, hf.2⟩ g ⟨hg.1, hg.1.2, hg.2⟩⟩
  | euclidean =>
    obtain ⟨h₁, h₂, h₃⟩ := normSharp_seminorm_props_limit D hP .euclidean M A
    exact ⟨fun f hf => h₁ f ⟨hf.1, hf.1.2, hf.2⟩, fun a f hf => h₂ a f ⟨hf.1, hf.1.2, hf.2⟩,
      fun f hf g hg => h₃ f ⟨hf.1, hf.1.2, hf.2⟩ g ⟨hg.1, hg.1.2, hg.2⟩⟩
theorem normSharp_zero
    (hP : LimitSpaces.Ambient.testSpacesAndSepTuples) (M : ScaleParam)
    (E : Ambient) : normSharp D M E (0 : E.Point D → ℝ) = 0 := by
  obtain ⟨W, hW⟩ := exists_submodule_compactC1SuppIn D hP E (Set.univ : Set (E.Point D))
  have h := (normSharp_seminorm_props D hP M E Set.univ).2.1 0 0 ((hW 0).1 W.zero_mem)
  simpa using h
theorem isMultilinearOnSubmodules_limit
    (hP : LimitSpaces.Ambient.testSpacesAndSepTuples)
    (P : LimitSpaces.Ambient) {n : ℕ} (hn : 1 ≤ n)
    (Ψ : P.SepTupleUniv D.toStandingParameters .cOne n → ℝ)
    (hΨ : P.IsMultilinearOn D.toStandingParameters Ψ)
    (A : Fin n → Set (P.Carrier D.toStandingParameters))
    (hA : Pairwise fun i j => P.PositivelySeparated D.toStandingParameters (A i) (A j))
    (Φ : (Fin n → P.Carrier D.toStandingParameters → ℝ) → ℝ)
    (hΦ : ∀ w (hw : P.IsSepTuple D.toStandingParameters .cOne Set.univ w), Φ w = Ψ ⟨w, hw⟩)
    (W : Fin n → Submodule ℝ (P.Carrier D.toStandingParameters → ℝ))
    (hW : ∀ j, ∀ f ∈ W j, f ∈ P.c1Within D.toStandingParameters (A j)) :
    IsMultilinearOnSubmodules W Φ := by
  intro i a b x y z hx hy hz hyx hzx hzi
  have hsep : ∀ w : Fin n → P.Carrier D.toStandingParameters → ℝ, (∀ j, w j ∈ W j) →
      P.IsSepTuple D.toStandingParameters .cOne Set.univ w := fun w hw =>
    ((hP D.toStandingParameters P ⟨1, Set.mem_Ici.2 le_rfl⟩ Set.univ Set.univ n hn).2.1.1 A
      (fun _ => Set.subset_univ _) hA).2 w fun j => hW j _ (hw j)
  rw [hΦ z (hsep z hz), hΦ x (hsep x hx), hΦ y (hsep y hy)]
  exact hΨ A (fun _ => Set.subset_univ _) hA i a b ⟨x, hsep x hx⟩ ⟨y, hsep y hy⟩ ⟨z, hsep z hz⟩
    (fun j => hW j _ (hx j)) (fun j => hW j _ (hy j)) (fun j => hW j _ (hz j)) hyx hzx hzi
theorem evalOrZero_of_mem {E : Ambient} {B : Set (FnList D E)} (φ : B → ℝ) {X : FnList D E}
    (h : X ∈ B) : evalOrZero φ X = φ ⟨X, h⟩ :=
  dif_pos h
theorem isMultilinearOnSubmodules
    (hP : LimitSpaces.Ambient.testSpacesAndSepTuples) (E : Ambient)
    {n : ℕ} (hn : 1 ≤ n) (φ : separatedN D E n → ℝ)
    (hφ : (toLimitAmbient E).IsMultilinearOn D.toStandingParameters (restrictToSepTuples D E φ))
    (A : Fin n → Set (E.Point D))
    (hA : Pairwise fun i j => 0 < setDist D E (A i) (A j))
    (W : Fin n → Submodule ℝ (E.Point D → ℝ))
    (hW : ∀ j f, f ∈ W j ↔ f ∈ compactC1SuppIn D E (A j)) :
    IsMultilinearOnSubmodules W fun x => evalOrZero φ (List.ofFn x) := by
  cases E with
  | torus =>
    exact isMultilinearOnSubmodules_limit D hP .periodic hn _ hφ A hA _
      (fun w hw => evalOrZero_of_mem D φ (listOfSepTuple_mem_separatedN D torus ⟨w, hw⟩)) W
      (fun j f hf => by
        have h := (hW j f).1 hf
        exact ⟨h.1, h.1.2, h.2⟩)
  | euclidean =>
    exact isMultilinearOnSubmodules_limit D hP .euclidean hn _ hφ A hA _
      (fun w hw => evalOrZero_of_mem D φ (listOfSepTuple_mem_separatedN D euclidean ⟨w, hw⟩)) W
      (fun j f hf => by
        have h := (hW j f).1 hf
        exact ⟨h.1, h.1.2, h.2⟩)
theorem eq_zero_of_closedSupport_subset_empty (hS : Sides.HyperplaneSidesClaim) (E : Ambient)
    {f : E.Point D → ℝ} (h : closedSupport D E f ⊆ ∅) : f = 0 := by
  funext x
  by_contra hx
  cases E with
  | torus =>
    have hd := ((hS D 0 0).1 .periodic).1.1
    exact h (show x ∈ closedSupport D torus f from fun r hr =>
      ⟨x, hx, by
        exact lt_of_eq_of_lt ((hd.eq_zero_iff x x).2 rfl) hr⟩)
  | euclidean =>
    have hd := ((hS D 0 0).1 .euclidean).1.1
    exact h (show x ∈ closedSupport D euclidean f from fun r hr =>
      ⟨x, hx, lt_of_eq_of_lt ((hd.eq_zero_iff x x).2 rfl) hr⟩)
theorem mem_compactC1SuppIn_iff (E : Ambient) {A : Set (E.Point D)} {f : E.Point D → ℝ}
    (hf : f ∈ compactC1 D ℝ E) :
    f ∈ compactC1SuppIn D E A ↔ MovingMirrorSets.SupportedOn D E A f := by
  cases E with
  | torus => exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨hf, h.2⟩⟩
  | euclidean => exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨hf, h.2⟩⟩
theorem tendsto_reflectFun_limit
    (hM : LimitSpaces.MirrorTranslation.Claim)
    (P : LimitSpaces.Ambient) (M : ScaleParam) (μ : Fin 4) (c : ℝ)
    {f : P.Carrier D.toStandingParameters → ℝ} (hf : f ∈ P.c1Compact D.toStandingParameters) :
    Tendsto (fun c' => ENNReal.ofReal (P.normSharp D.toStandingParameters M
      (P.reflectFun D.toStandingParameters μ c' f - P.reflectFun D.toStandingParameters μ c f)))
      (𝓝 c) (𝓝 0) := by
  obtain ⟨-, -, -, -, -, hclose, hmod⟩ := hM D.toStandingParameters M P μ
  have ht : Tendsto (fun c' : ℝ => (2 * |c' - c|).toNNReal) (𝓝 c) (𝓝 0) := by
    have hc : Continuous fun c' : ℝ => (2 * |c' - c|).toNNReal :=
      continuous_real_toNNReal.comp (continuous_const.mul (continuous_id.sub continuous_const).abs)
    simpa using hc.tendsto c
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ((hmod ⟨f, hf⟩).2.comp ht) (fun _ => zero_le) (fun c' => hclose ⟨f, hf⟩ c c')
theorem tendsto_pullback
    (hM : LimitSpaces.MirrorTranslation.Claim) (M : ScaleParam)
    (E : Ambient) (μ : Fin 4) (c : ℝ) {f : E.Point D → ℝ} (hf : f ∈ compactC1 D ℝ E) :
    Tendsto (fun c' => ENNReal.ofReal (normSharp D M E
      ((CoordMirror.mk μ c').pullback D E f - (CoordMirror.mk μ c).pullback D E f)))
      (𝓝 c) (𝓝 0) := by
  cases E with
  | torus =>
    have e : ∀ c', (CoordMirror.mk μ c').pullback D torus f =
        LimitSpaces.Ambient.periodic.reflectFun D.toStandingParameters μ c' f := fun c' => by
      show f ∘ CoordMirror.reflect D ⟨μ, c'⟩ .torus = _
      rw [Sides.reflect_torus]
      rfl
    simp only [e]
    exact tendsto_reflectFun_limit D hM .periodic M μ c hf
  | euclidean =>
    have e : ∀ c', (CoordMirror.mk μ c').pullback D euclidean f =
        LimitSpaces.Ambient.euclidean.reflectFun D.toStandingParameters μ c' f := fun c' => by
      show f ∘ CoordMirror.reflect D ⟨μ, c'⟩ .euclidean = _
      rw [Sides.reflect_euclidean]
      rfl
    simp only [e]
    exact tendsto_reflectFun_limit D hM .euclidean M μ c hf
end OnTheSpaces
section Blocks
open Ambient
variable {D : MirrorData} {E : Ambient}
theorem tendsto_eval_block (hF : Multilinear.BoundedMultilinearEstimates)
    (hP : LimitSpaces.Ambient.testSpacesAndSepTuples)
    (hS : Sides.HyperplaneSidesClaim) (M : ScaleParam) (T : FunctionalFamily D E)
    (hT : FunctionalFamily.MultilinearSymmetric T)
    (hD : SeparatedCompactBound M T) {q : ℕ} (A : Fin q → Set (E.Point D))
    (hc : ∀ l, MetricNotions.IsCompactWrt (metric D E) (A l))
    (hA : ∀ l l', l ≠ l' → 0 < setDist D E (A l) (A l'))
    (J : Finset (Fin q)) (hJ : 2 ≤ J.card) {α : Type*} {F : Filter α}
    (e : α → Fin q → E.Point D → ℝ) (g : Fin q → E.Point D → ℝ)
    (hg : ∀ l, g l ∈ compactC1SuppIn D E (A l))
    (he : ∀ᶠ a in F, ∀ l, e a l ∈ compactC1SuppIn D E (A l))
    (ht : ∀ l, Tendsto (fun a => ENNReal.ofReal (normSharp D M E (e a l - g l))) F (𝓝 0)) :
    Tendsto (fun a => FunctionalFamily.eval T J.card
        (List.ofFn fun k : Fin J.card => e a (J.orderEmbOfFin rfl k))) F
      (𝓝 (FunctionalFamily.eval T J.card
        (List.ofFn fun k : Fin J.card => g (J.orderEmbOfFin rfl k)))) := by
  have hJq : J.card ≤ q := by simpa using J.card_le_univ
  obtain ⟨C, hC0, hC⟩ := hD q (hJ.trans hJq) A hc hA
  have hAι : Pairwise fun i j : Fin J.card => 0 < setDist D E
      (A (J.orderEmbOfFin rfl i)) (A (J.orderEmbOfFin rfl j)) := fun i j hij =>
    hA _ _ ((J.orderEmbOfFin rfl).injective.ne hij)
  choose W hW using fun k : Fin J.card =>
    exists_submodule_compactC1SuppIn D hP E (A (J.orderEmbOfFin rfl k))
  have hread : ∀ x : Fin J.card → E.Point D → ℝ, FunctionalFamily.eval T J.card (List.ofFn x) =
      evalOrZero (T J.card hJ) (List.ofFn x) := fun x => dif_pos hJ
  have hl : IsMultilinearOnSubmodules W
      fun x => FunctionalFamily.eval T J.card (List.ofFn x) := by
    have h := isMultilinearOnSubmodules D hP E (by omega) (T J.card hJ) (hT J.card hJ).1 _ hAι W hW
    simpa only [hread] using h
  refine tendsto_of_multilinear_bound hF (by omega) W (normSharp D M E)
    (fun j f hf => (normSharp_seminorm_props D hP M E _).1 f ((hW j f).1 hf))
    (fun j a f hf => (normSharp_seminorm_props D hP M E _).2.1 a f ((hW j f).1 hf))
    (fun j f hf g hg => (normSharp_seminorm_props D hP M E _).2.2 f ((hW j f).1 hf) g ((hW j g).1 hg))
    (fun x => FunctionalFamily.eval T J.card (List.ofFn x)) hl (C J.card)
    (hC0 _ hJ hJq) ?_ (fun a k => e a (J.orderEmbOfFin rfl k))
    (fun k => g (J.orderEmbOfFin rfl k)) (fun k => (hW k _).2 (hg _)) ?_ (fun k => ht _)
  · intro x hx
    have hnn : 0 ≤ C J.card * ∏ j, normSharp D M E (x j) :=
      mul_nonneg (hC0 _ hJ hJq) (Finset.prod_nonneg fun j _ =>
        (normSharp_seminorm_props D hP M E _).1 _ ((hW j _).1 (hx j)))
    by_cases hinj : Function.Injective (A ∘ J.orderEmbOfFin rfl)
    · have hmem : List.ofFn x ∈ separatedN D E J.card :=
        ofFn_mem_separatedN D E hAι fun i => (hW i _).1 (hx i)
      have hlen : (List.ofFn x).length = J.card := List.length_ofFn
      have hb := hC J.card hJ hJq ⟨List.ofFn x, hmem⟩
        ⟨J.orderEmbOfFin rfl ∘ Fin.cast hlen, ?_, ?_⟩
      · rw [FunctionalFamily.eval_of_mem T hJ hmem]
        simpa [List.map_ofFn, List.prod_ofFn] using hb
      · exact fun i j hij => Fin.cast_injective hlen (hinj hij)
      · intro i
        have hm := (hW (Fin.cast hlen i) _).1 (hx (Fin.cast hlen i))
        have e₁ : (List.ofFn x).get i = x (Fin.cast hlen i) := by
          simp
          rfl
        show MovingMirrorSets.SupportedOn D E _ ((List.ofFn x).get i)
        rw [e₁]
        exact (mem_compactC1SuppIn_iff D E hm.1).1 hm
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, (A ∘ J.orderEmbOfFin rfl) i = (A ∘ J.orderEmbOfFin rfl) j ∧
          i ≠ j := by
        simpa [Function.Injective] using hinj
      have hdis := disjoint_of_setDist_pos D E (hAι hne)
      have hi : A (J.orderEmbOfFin rfl i) = ∅ := by
        have e₁ : A (J.orderEmbOfFin rfl j) = A (J.orderEmbOfFin rfl i) := hij.symm
        rw [e₁] at hdis
        exact disjoint_self.1 hdis
      have hzero : x i = 0 := by
        have hm := (hW i _).1 (hx i)
        exact eq_zero_of_closedSupport_subset_empty D hS E (hi ▸ hm.2)
      have hv := hl i 0 0 x x x hx hx hx (fun _ _ => rfl) (fun _ _ => rfl) (by simp [hzero])
      have hv' : FunctionalFamily.eval T J.card (List.ofFn x) = 0 := by simpa using hv
      rw [hv', abs_zero]
      exact hnn
  · filter_upwards [he] with a h k
    exact (hW k _).2 (h _)
theorem evalOrZero_centeredFunctional (T : FunctionalFamily D E) {L : FnList D E}
    (hL : L ∈ separatedAll D E) {q : ℕ} (hq : L.length = q) :
    evalOrZero (FunctionalFamily.centeredFunctional T) L =
      ∑ π ∈ SetPartition.nonSingletonPartitions q, ∏ J ∈ π.parts,
        FunctionalFamily.eval T J.card (List.ofFn fun k : Fin J.card =>
          L.getD (J.orderEmbOfFin rfl k) 0) := by
  subst hq
  rw [evalOrZero_of_mem D _ hL]
  refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ => ?_
  congr 1
  unfold subList
  congr 1
  funext k
  simp
theorem forall₂_getD_of_lt {β γ : Type*} {R : β → γ → Prop} {a : List β} {b : List γ}
    (h : List.Forall₂ R a b) (da : β) (db : γ) :
    ∀ l, l < a.length → R (a.getD l da) (b.getD l db) := by
  induction h with
  | nil => intro l hl; simp at hl
  | @cons x y u v hxy _ ih =>
    intro l hl
    cases l with
    | zero => simpa using hxy
    | succ l => simpa using ih l (by simpa using hl)
theorem getD_reflectAppend_cases (μ : Fin 4) (X Y : FnList D E) (l : ℕ) :
    (∃ f ∈ X, ∀ c' : ℝ, ((CoordMirror.mk μ c').reflectAppend D E X Y).getD l 0 =
      (CoordMirror.mk μ c').pullback D E f) ∨
    ∃ h : E.Point D → ℝ, ∀ c' : ℝ,
      ((CoordMirror.mk μ c').reflectAppend D E X Y).getD l 0 = h := by
  by_cases hl : l < X.length
  · refine Or.inl ⟨X[l], List.getElem_mem hl, fun c' => ?_⟩
    simp [CoordMirror.reflectAppend, CoordMirror.reflectList, append,
      List.getD_eq_getElem?_getD, List.getElem?_append_left, hl]
  · refine Or.inr ⟨Y.getD (l - X.length) 0, fun c' => ?_⟩
    have hl' : (X.map ((CoordMirror.mk μ c').pullback D E)).length ≤ l := by simpa using hl
    simp [CoordMirror.reflectAppend, CoordMirror.reflectList, append,
      List.getD_eq_getElem?_getD, List.getElem?_append_right hl']
end Blocks
section Requirements
open Ambient
variable {D : MirrorData} {E : Ambient}
theorem isCompactSubset_iUnion_closedSupport
    (hP : LimitSpaces.Ambient.testSpacesAndSepTuples)
    (P : LimitSpaces.Ambient)
    (hlip : ∀ f ∈ P.c1Compact D.toStandingParameters, P.IsLip D.toStandingParameters f)
    {r : ℕ} (X : Fin r → List (P.Carrier D.toStandingParameters → ℝ))
    (hc : ∀ p, ∀ f ∈ X p, f ∈ P.c1Compact D.toStandingParameters)
    (hd : ∀ p, (X p).Pairwise fun f g =>
      Disjoint (P.closedSupport D.toStandingParameters f) (P.closedSupport D.toStandingParameters g)) :
    P.IsCompactSubset D.toStandingParameters
      (⋃ p, ⋃ f ∈ X p, P.closedSupport D.toStandingParameters f) := by
  have h := (hP D.toStandingParameters P ⟨1, Set.mem_Ici.2 le_rfl⟩ Set.univ Set.univ 1 le_rfl).2.2.1.2.2.2
    r (fun p => (X p).length) (fun p => (X p).get) (fun p =>
      ⟨fun i => ⟨hlip _ (hc p _ (List.get_mem _ _)), (hc p _ (List.get_mem _ _)).2,
        Set.subset_univ _⟩, fun i j hij => by
          rcases lt_or_gt_of_ne hij with hlt | hlt
          · exact List.pairwise_iff_get.1 (hd p) i j hlt
          · exact (List.pairwise_iff_get.1 (hd p) j i hlt).symm⟩)
  have e : (⋃ p, ⋃ f ∈ X p, P.closedSupport D.toStandingParameters f) =
      ⋃ p, ⋃ i, P.closedSupport D.toStandingParameters ((X p).get i) := by
    refine Set.iUnion_congr fun p => ?_
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨f, hf, hx⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hf
      exact ⟨i, hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨_, List.get_mem _ _, hx⟩
  rw [e]
  exact h
theorem suppUnion_upper (hS : Sides.HyperplaneSidesClaim)
    (hP : LimitSpaces.Ambient.testSpacesAndSepTuples)
    {μ : Fin 4} {c : ℝ} (I : (CoordMirror.mk μ c).PositivityInstance D E) :
    0 < I.distToMirror ∧
      (∀ c' : ℝ, ENNReal.ofReal |c' - c| < I.distToMirror →
        I.suppUnion ⊆ (CoordMirror.mk μ c').upperSide D E) ∧
      (E = euclidean → ∀ c' : ℝ, c' ≤ c →
        I.suppUnion ⊆ (CoordMirror.mk μ c').upperSide D E) := by
  have hsep : ∀ i, IsSeparatedList D E (I.tuples i).1 := fun i =>
    isSeparatedList_of_mem_separatedAll (I.tuples i).2.1
  have hsub : I.suppUnion ⊆ (CoordMirror.mk μ c).upperSide D E := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 hi
    exact (I.tuples i).2.2 f hf hxf
  cases E with
  | torus =>
    have hd := (hS D μ c).1 .periodic
    have hK := isCompactSubset_iUnion_closedSupport (D := D) hP .periodic
      (fun f hf => (hd.1.2.2.2.2.2.2.2 f hf).2.2)
      (fun i => (I.tuples i).1) (fun p f hf => (hsep p).1 f hf) (fun p => (hsep p).2)
    have h := hd.2.2.2.1 I.suppUnion hK hsub
    exact ⟨h.1, h.2, fun hE => by cases hE⟩
  | euclidean =>
    have hd := (hS D μ c).1 .euclidean
    have hK := isCompactSubset_iUnion_closedSupport (D := D) hP .euclidean
      (fun f hf => (hd.1.2.2.2.2.2.2.2 f hf).2.2)
      (fun i => (I.tuples i).1) (fun p f hf => (hsep p).1 f hf) (fun p => (hsep p).2)
    have h := hd.2.2.2.1 I.suppUnion hK hsub
    exact ⟨h.1, h.2, fun _ c' hc' => (hS D μ c).2.2.2.1 I.suppUnion hK hsub c' hc'⟩
theorem tuples_mem_separatedWithin {μ : Fin 4} {c : ℝ}
    (I : (CoordMirror.mk μ c).PositivityInstance D E)
    {O : Set (E.Point D)} (h : I.suppUnion ⊆ O) (i : Fin I.size) :
    (I.tuples i).1 ∈ separatedWithin D E O :=
  ⟨(I.tuples i).2.1, fun _ hf _ hx => h (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion₂.2 ⟨_, hf, hx⟩⟩)⟩
theorem instancesStayUpper (hS : Sides.HyperplaneSidesClaim)
    (hP : LimitSpaces.Ambient.testSpacesAndSepTuples)
    (μ : Fin 4) (c : ℝ) : InstancesStayUpper D E μ c := by
  intro I
  obtain ⟨-, h₁, h₂⟩ := suppUnion_upper hS hP I
  exact ⟨fun c' hc' => ⟨h₁ c' hc', tuples_mem_separatedWithin I (h₁ c' hc')⟩,
    fun hE c' hc' => ⟨h₂ hE c' hc', tuples_mem_separatedWithin I (h₂ hE c' hc')⟩⟩
theorem centeredContinuousInHeight (hF : Multilinear.BoundedMultilinearEstimates)
    (hP : LimitSpaces.Ambient.testSpacesAndSepTuples)
    (hS : Sides.HyperplaneSidesClaim) (hC : MovingMirrorSets.SharedSetsProperties)
    (hM : LimitSpaces.MirrorTranslation.Claim) (M : ScaleParam)
    (T : FunctionalFamily D E)
    (hT : FunctionalFamily.MultilinearSymmetric T)
    (hD : SeparatedCompactBound M T) (μ : Fin 4) (c : ℝ) :
    CenteredContinuousInHeight T μ c := by
  intro X Y
  obtain ⟨⟨hη, -, hcomp, hmin, hapart⟩, hmove, -⟩ := hC D E μ c X.1 Y.1 X.2 Y.2
  refine ⟨fun c' h => separatedN_subset_separatedAll D E _ (hmove c' h).2, ?_⟩
  set η := MovingMirrorSets.margin D E μ c X.1 Y.1 with hηdef
  set S := MovingMirrorSets.sharedSets D E μ c X.1 Y.1 with hSdef
  have hlenS : S.length = X.1.length + Y.1.length := by
    simp [hSdef, MovingMirrorSets.sharedSets]
  have hlenZ : ∀ c' : ℝ, ((CoordMirror.mk μ c').reflectAppend D E X.1 Y.1).length =
      X.1.length + Y.1.length := fun c' => by
    simp [CoordMirror.reflectAppend, CoordMirror.reflectList, append]
  have hnear : ∀ᶠ c' in 𝓝 c, 2 * |c' - c| ≤ η := by
    have hcont : Continuous fun c' : ℝ => 2 * |c' - c| :=
      continuous_const.mul (continuous_id.sub continuous_const).abs
    have h₁ := hcont.tendsto c
    simp only [sub_self, abs_zero, mul_zero] at h₁
    exact (h₁.eventually_lt_const hη).mono fun _ h => h.le
  have hcc : 2 * |c - c| ≤ η := by simpa using hη.le
  let A : Fin (X.1.length + Y.1.length) → Set (E.Point D) := fun l => S.getD l ∅
  let e : ℝ → Fin (X.1.length + Y.1.length) → E.Point D → ℝ := fun c' l =>
    ((CoordMirror.mk μ c').reflectAppend D E X.1 Y.1).getD l 0
  have hAget : ∀ l, A l = S.get (Fin.cast hlenS.symm l) := fun l => by
    simp [A, List.getD_eq_getElem?_getD, hlenS]
  have hAc : ∀ l, MetricNotions.IsCompactWrt (metric D E) (A l) := fun l => by
    rw [hAget]
    exact hcomp _ (List.get_mem _ _)
  have hAd : ∀ l l', l ≠ l' → 0 < setDist D E (A l) (A l') := fun l l' hne => by
    rw [hAget, hAget]
    exact hmin.trans_le (hapart _ _ fun h => hne (Fin.cast_injective _ h))
  have hsupp : ∀ c' : ℝ, 2 * |c' - c| ≤ η → ∀ l, e c' l ∈ compactC1SuppIn D E (A l) :=
      fun c' h l => by
    have hlt : (l : ℕ) < ((CoordMirror.mk μ c').reflectAppend D E X.1 Y.1).length := by
      rw [hlenZ]
      exact l.2
    have h₁ := forall₂_getD_of_lt (hmove c' h).1 0 ∅ l hlt
    have h₂ : e c' l ∈ compactC1 D ℝ E := by
      refine (hmove c' h).2.2.1 _ ?_
      simp only [e]
      rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem hlt
    exact (mem_compactC1SuppIn_iff D E h₂).2 h₁
  have hvalue : ∀ c' : ℝ, 2 * |c' - c| ≤ η →
      evalOrZero (FunctionalFamily.centeredFunctional T)
          ((CoordMirror.mk μ c').reflectAppend D E X.1 Y.1) =
        ∑ π ∈ SetPartition.nonSingletonPartitions (X.1.length + Y.1.length), ∏ J ∈ π.parts,
          FunctionalFamily.eval T J.card (List.ofFn fun k : Fin J.card =>
            e c' (J.orderEmbOfFin rfl k)) := fun c' h =>
    evalOrZero_centeredFunctional T (separatedN_subset_separatedAll D E _ (hmove c' h).2) (hlenZ c')
  have ht : ∀ l, Tendsto (fun c' => ENNReal.ofReal (normSharp D M E (e c' l - e c l)))
      (𝓝 c) (𝓝 0) := fun l => by
    rcases getD_reflectAppend_cases μ X.1 Y.1 (l : ℕ) with ⟨f, hf, he⟩ | ⟨h, he⟩
    · simp only [e, he]
      exact tendsto_pullback D hM M E μ c
        ((isSeparatedList_of_mem_separatedAll X.2.1).1 f hf)
    · simp only [e, he, sub_self, normSharp_zero D hP M E, ENNReal.ofReal_zero]
      exact tendsto_const_nhds
  rw [hvalue c hcc]
  refine Tendsto.congr' (hnear.mono fun c' h => (hvalue c' h).symm) ?_
  refine tendsto_finsetSum _ fun π hπ => tendsto_finsetProd _ fun J hJ => ?_
  exact tendsto_eval_block hF hP hS M T hT hD A hAc hAd J
    (LimitSpaces.Ambient.two_le_card_of_mem_nonSingleton ⟨π, hπ⟩ ⟨J, hJ⟩) e (e c) (hsupp c hcc)
    (hnear.mono fun c' h => hsupp c' h) ht
theorem holdsReal_of_dense (hS : Sides.HyperplaneSidesClaim)
    (hP : LimitSpaces.Ambient.testSpacesAndSepTuples)
    (T : FunctionalFamily D E) (μ : Fin 4) (c : ℝ)
    (hii : CenteredContinuousInHeight T μ c)
    (hL : Dense (LimitSpaces.edgeMidCoordsAll D.toStandingParameters))
    (hfix : ∀ c' ∈ LimitSpaces.edgeMidCoordsAll D.toStandingParameters,
      ∀ I : (CoordMirror.mk μ c').PositivityInstance D E,
        I.HoldsReal (FunctionalFamily.centeredFunctional T))
    (I : (CoordMirror.mk μ c).PositivityInstance D E) :
    I.HoldsReal (FunctionalFamily.centeredFunctional T) := by
  obtain ⟨hδ, hstay, -⟩ := suppUnion_upper hS hP I
  let σ : separatedAll D E → ℂ := fun X => (FunctionalFamily.centeredFunctional T X : ℂ)
  let G : ℝ → ℂ := fun c' =>
    (CoordMirror.mk μ c').positivitySum D E σ (fun i => (I.tuples i : FnList D E)) I.coeffs
  have hG : Tendsto G (𝓝 c) (𝓝 (G c)) := by
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun k _ => Tendsto.const_mul _ ?_
    simp only [σ, evalOrZeroC_ofReal]
    exact (Complex.continuous_ofReal.tendsto _).comp (hii (I.tuples i) (I.tuples k)).2
  have hnear : ∀ᶠ c' in 𝓝 c, ENNReal.ofReal |c' - c| < I.distToMirror := by
    have hcont : Continuous fun c' : ℝ => ENNReal.ofReal |c' - c| :=
      ENNReal.continuous_ofReal.comp (continuous_id.sub continuous_const).abs
    have h₁ := hcont.tendsto c
    simp only [sub_self, abs_zero, ENNReal.ofReal_zero] at h₁
    exact h₁.eventually_lt_const hδ
  have hsat : ∀ c' ∈ LimitSpaces.edgeMidCoordsAll D.toStandingParameters,
      ENNReal.ofReal |c' - c| < I.distToMirror → (G c').im = 0 ∧ 0 ≤ (G c').re :=
    fun c' hc' h => hfix c' hc'
      { size := I.size
        one_le_size := I.one_le_size
        tuples := fun i => ⟨(I.tuples i).1, tuples_mem_separatedWithin I (hstay c' h) i⟩
        coeffs := I.coeffs }
  have : (𝓝[LimitSpaces.edgeMidCoordsAll D.toStandingParameters] c).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (hL c)
  have hG' := hG.mono_left
    (nhdsWithin_le_nhds (s := LimitSpaces.edgeMidCoordsAll D.toStandingParameters))
  have hev : ∀ᶠ c' in 𝓝[LimitSpaces.edgeMidCoordsAll D.toStandingParameters] c,
      (G c').im = 0 ∧ 0 ≤ (G c').re := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hnear] with c' h₁ h₂
    exact hsat c' h₁ h₂
  have him := (Complex.continuous_im.tendsto _).comp hG'
  have hre := (Complex.continuous_re.tendsto _).comp hG'
  refine ⟨?_, ?_⟩
  · exact tendsto_nhds_unique him
      (tendsto_const_nhds.congr' (hev.mono fun _ h => h.1.symm))
  · exact ge_of_tendsto hre (hev.mono fun _ h => h.2)
end Requirements
theorem continuityInHeight (hS : Sides.HyperplaneSidesClaim)
    (hC : MovingMirrorSets.SharedSetsProperties)
    (hM : LimitSpaces.MirrorTranslation.Claim)
    (hF : Multilinear.BoundedMultilinearEstimates)
    (hP : LimitSpaces.Ambient.testSpacesAndSepTuples)
    (hN : LimitSpaces.RefinedCutoffs.Claim)
    (hσ : Ambient.LatticeDataSeq.CenteredFunctionalsConverge)
    (hX : Ambient.LatticeDataSeq.PositivityPassesToLimit) :
    ContinuityInHeight := by
  intro D E S T hconv M hD μ c
  have hT := (hσ.1 D E S T hconv).2
  have hii := centeredContinuousInHeight hF hP hS hC hM M T hT hD μ c
  have hL : Dense (LimitSpaces.edgeMidCoordsAll D.toStandingParameters) :=
    (hN D.toStandingParameters D.toStandingParameters.K le_rfl).2.2.2.2.2.2.2.2.2
  exact ⟨instancesStayUpper hS hP μ c, hii, holdsReal_of_dense hS hP T μ c hii hL
    fun c' hc' I => hX.1 D E S T hconv μ c' hc' I⟩
end YangMills.Construction.ReflectionPositivity.AxisMirror.DenseMirrors
end
