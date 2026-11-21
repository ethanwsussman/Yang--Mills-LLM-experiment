import YangMills.Construction.TorusOrFourSpace.IteratedPartialsOfProductsOverTheFactors
import YangMills.Construction.TorusOrFourSpace.RulesForTensors
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.TensorRules
open Euclid
open Coords (partialAlong iterPartial ContPartialsUpTo)
variable {n n' : ℕ+}
def embedLeft (j : Fin (4 * (n : ℕ))) : Fin (4 * ((n + n' : ℕ+) : ℕ)) :=
  ⟨j, by have := j.2; rw [PNat.add_coe]; omega⟩
def embedRight (j : Fin (4 * (n' : ℕ))) : Fin (4 * ((n + n' : ℕ+) : ℕ)) :=
  ⟨4 * (n : ℕ) + j, by have := j.2; rw [PNat.add_coe]; omega⟩
theorem embedLeft_inj {i j : Fin (4 * (n : ℕ))} :
    (embedLeft (n' := n') i = embedLeft j) ↔ i = j := by
  constructor
  · intro e
    have e' := congrArg Fin.val e
    exact Fin.ext e'
  · rintro rfl
    rfl
theorem embedRight_inj {i j : Fin (4 * (n' : ℕ))} :
    (embedRight (n := n) i = embedRight j) ↔ i = j := by
  constructor
  · intro e
    have e' := congrArg Fin.val e
    simp only [embedRight] at e'
    exact Fin.ext (by omega)
  · rintro rfl
    rfl
theorem embedLeft_ne_embedRight (i : Fin (4 * (n : ℕ))) (j : Fin (4 * (n' : ℕ))) :
    embedLeft (n' := n') i ≠ embedRight j := by
  intro e
  have e' := congrArg Fin.val e
  simp only [embedLeft, embedRight] at e'
  have := i.2
  omega
def restrictLeft (x : Coords (n + n')) : Coords n := fun j => x (embedLeft j)
def restrictRight (x : Coords (n + n')) : Coords n' := fun j => x (embedRight j)
def blockMul (G : Coords n → ℂ) (K : Coords n' → ℂ) : Coords (n + n') → ℂ :=
  fun x => G (restrictLeft x) * K (restrictRight x)
theorem restrictLeft_add_left (x : Coords (n + n')) (t : ℝ) (j : Fin (4 * (n : ℕ))) :
    restrictLeft (x + t • (Pi.single (embedLeft j) 1 : Coords (n + n'))) =
      restrictLeft x + t • (Pi.single j 1 : Coords n) := by
  funext i
  show x (embedLeft i) + t * (Pi.single (embedLeft j) (1 : ℝ) : Fin _ → ℝ) (embedLeft i) =
    x (embedLeft i) + t * (Pi.single j (1 : ℝ) : Fin _ → ℝ) i
  simp only [Pi.single_apply, embedLeft_inj]
theorem restrictRight_add_left (x : Coords (n + n')) (t : ℝ) (j : Fin (4 * (n : ℕ))) :
    restrictRight (x + t • (Pi.single (embedLeft j) 1 : Coords (n + n'))) = restrictRight x := by
  funext i
  have h : embedRight (n := n) i ≠ embedLeft j := (embedLeft_ne_embedRight j i).symm
  show x (embedRight i) + t * (Pi.single (embedLeft j) (1 : ℝ) : Fin _ → ℝ) (embedRight i) =
    x (embedRight i)
  rw [Pi.single_apply, if_neg h, mul_zero, add_zero]
theorem restrictRight_add_right (x : Coords (n + n')) (t : ℝ) (j : Fin (4 * (n' : ℕ))) :
    restrictRight (x + t • (Pi.single (embedRight j) 1 : Coords (n + n'))) =
      restrictRight x + t • (Pi.single j 1 : Coords n') := by
  funext i
  show x (embedRight i) + t * (Pi.single (embedRight j) (1 : ℝ) : Fin _ → ℝ) (embedRight i) =
    x (embedRight i) + t * (Pi.single j (1 : ℝ) : Fin _ → ℝ) i
  simp only [Pi.single_apply, embedRight_inj]
theorem restrictLeft_add_right (x : Coords (n + n')) (t : ℝ) (j : Fin (4 * (n' : ℕ))) :
    restrictLeft (x + t • (Pi.single (embedRight j) 1 : Coords (n + n'))) = restrictLeft x := by
  funext i
  have h : embedLeft (n' := n') i ≠ embedRight j := embedLeft_ne_embedRight i j
  show x (embedLeft i) + t * (Pi.single (embedRight j) (1 : ℝ) : Fin _ → ℝ) (embedLeft i) =
    x (embedLeft i)
  rw [Pi.single_apply, if_neg h, mul_zero, add_zero]
theorem partialAlong_blockMul_left (j : Fin (4 * (n : ℕ))) (G : Coords n → ℂ)
    (K : Coords n' → ℂ) :
    partialAlong (embedLeft j) (blockMul G K) =
      blockMul (partialAlong j G) K := by
  funext x
  have hline : (fun t : ℝ =>
      blockMul G K (x + t • (Pi.single (embedLeft j) 1 : Coords (n + n')))) =
      fun t : ℝ => G (restrictLeft x + t • (Pi.single j 1 : Coords n)) * K (restrictRight x) := by
    funext t
    simp only [blockMul, restrictLeft_add_left, restrictRight_add_left]
  simp only [partialAlong, lineDeriv, blockMul] at hline ⊢
  rw [hline, deriv_mul_const_field]
theorem partialAlong_blockMul_right (j : Fin (4 * (n' : ℕ))) (G : Coords n → ℂ)
    (K : Coords n' → ℂ) :
    partialAlong (embedRight j) (blockMul G K) =
      blockMul G (partialAlong j K) := by
  funext x
  have hline : (fun t : ℝ =>
      blockMul G K (x + t • (Pi.single (embedRight j) 1 : Coords (n + n')))) =
      fun t : ℝ => G (restrictLeft x) * K (restrictRight x + t • (Pi.single j 1 : Coords n')) := by
    funext t
    simp only [blockMul, restrictLeft_add_right, restrictRight_add_right]
  simp only [partialAlong, lineDeriv, blockMul] at hline ⊢
  rw [hline, deriv_const_mul_field]
theorem iterate_partialAlong_left (j : Fin (4 * (n : ℕ))) (k : ℕ) (G : Coords n → ℂ)
    (K : Coords n' → ℂ) :
    (partialAlong (embedLeft j))^[k] (blockMul G K) =
      blockMul ((partialAlong j)^[k] G) K := by
  induction k generalizing G with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp]
    rw [partialAlong_blockMul_left, ih]
theorem iterate_partialAlong_right (j : Fin (4 * (n' : ℕ))) (k : ℕ) (G : Coords n → ℂ)
    (K : Coords n' → ℂ) :
    (partialAlong (embedRight j))^[k] (blockMul G K) =
      blockMul G ((partialAlong j)^[k] K) := by
  induction k generalizing K with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp]
    rw [partialAlong_blockMul_right, ih]
theorem foldr_partials_left (γ : CoordIndex (n + n')) (l : List (Fin (4 * (n : ℕ))))
    (G : Coords n → ℂ) (K : Coords n' → ℂ) :
    (l.map embedLeft).foldr (fun j A => (partialAlong j)^[γ j] A) (blockMul G K) =
      blockMul (l.foldr (fun j A => (partialAlong j)^[γ (embedLeft j)] A) G) K := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [ih, iterate_partialAlong_left]
theorem foldr_partials_right (γ : CoordIndex (n + n')) (l : List (Fin (4 * (n' : ℕ))))
    (G : Coords n → ℂ) (K : Coords n' → ℂ) :
    (l.map embedRight).foldr (fun j A => (partialAlong j)^[γ j] A) (blockMul G K) =
      blockMul G (l.foldr (fun j A => (partialAlong j)^[γ (embedRight j)] A) K) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [ih, iterate_partialAlong_right]
theorem finRange_eq_append_embed :
    List.finRange (4 * ((n + n' : ℕ+) : ℕ)) =
      (List.finRange (4 * (n : ℕ))).map embedLeft ++
        (List.finRange (4 * (n' : ℕ))).map embedRight := by
  apply List.ext_getElem
  · rw [List.length_append, List.length_map, List.length_map, List.length_finRange,
      List.length_finRange, List.length_finRange, PNat.add_coe]
    ring
  · intro i h₁ h₂
    rw [List.getElem_finRange, List.getElem_append]
    split_ifs with h
    · rw [List.getElem_map, List.getElem_finRange]
      rfl
    · rw [List.getElem_map, List.getElem_finRange]
      rw [List.length_map, List.length_finRange] at h
      apply Fin.ext
      simp only [embedRight, Fin.val_cast, List.length_map, List.length_finRange]
      omega
theorem appendIdx_embedLeft (α : CoordIndex n) (α' : CoordIndex n')
    (j : Fin (4 * (n : ℕ))) : appendIdx α α' (embedLeft j) = α j := by
  have h : ((embedLeft (n' := n') j : Fin _) : ℕ) < 4 * (n : ℕ) := j.2
  simp only [appendIdx, dif_pos h]
  rfl
theorem appendIdx_embedRight (α : CoordIndex n) (α' : CoordIndex n')
    (j : Fin (4 * (n' : ℕ))) : appendIdx α α' (embedRight j) = α' j := by
  have h : ¬ ((embedRight (n := n) j : Fin _) : ℕ) < 4 * (n : ℕ) := by
    simp only [embedRight]
    omega
  simp only [appendIdx, dif_neg h]
  congr 1
  apply Fin.ext
  simp [embedRight]
theorem iterPartial_blockMul (α : CoordIndex n) (α' : CoordIndex n')
    (G : Coords n → ℂ) (K : Coords n' → ℂ) :
    iterPartial (appendIdx α α') (blockMul G K) =
      blockMul (iterPartial α G) (iterPartial α' K) := by
  simp only [iterPartial]
  rw [finRange_eq_append_embed, List.foldr_append, foldr_partials_right, foldr_partials_left]
  simp only [appendIdx_embedLeft, appendIdx_embedRight]
theorem contPartialsUpTo_of_succ {p : ℕ+} (ν : ℕ) (G : Coords p → ℂ)
    (h : ContPartialsUpTo (ν + 1) G) : ContPartialsUpTo ν G := by
  induction ν generalizing G with
  | zero => exact h.1
  | succ ν ih => exact ⟨h.1, fun j => ⟨(h.2 j).1, ih _ (h.2 j).2⟩⟩
theorem continuous_restrictLeft : Continuous (restrictLeft (n := n) (n' := n')) :=
  continuous_pi fun _ => continuous_apply _
theorem continuous_restrictRight : Continuous (restrictRight (n := n) (n' := n')) :=
  continuous_pi fun _ => continuous_apply _
theorem continuous_blockMul {G : Coords n → ℂ} {K : Coords n' → ℂ}
    (hG : Continuous G) (hK : Continuous K) : Continuous (blockMul G K) :=
  (hG.comp continuous_restrictLeft).mul (hK.comp continuous_restrictRight)
theorem lineDifferentiableAt_blockMul_left (j : Fin (4 * (n : ℕ))) {G : Coords n → ℂ}
    (K : Coords n' → ℂ) (hG : ∀ x, LineDifferentiableAt ℝ G x (Pi.single j 1))
    (x : Coords (n + n')) :
    LineDifferentiableAt ℝ (blockMul G K) x (Pi.single (embedLeft j) 1) := by
  have hline : (fun t : ℝ =>
      blockMul G K (x + t • (Pi.single (embedLeft j) 1 : Coords (n + n')))) =
      fun t : ℝ => G (restrictLeft x + t • (Pi.single j 1 : Coords n)) * K (restrictRight x) := by
    funext t
    simp only [blockMul, restrictLeft_add_left, restrictRight_add_left]
  unfold LineDifferentiableAt
  rw [hline]
  exact DifferentiableAt.mul_const (hG (restrictLeft x)) _
theorem lineDifferentiableAt_blockMul_right (j : Fin (4 * (n' : ℕ))) (G : Coords n → ℂ)
    {K : Coords n' → ℂ} (hK : ∀ x, LineDifferentiableAt ℝ K x (Pi.single j 1))
    (x : Coords (n + n')) :
    LineDifferentiableAt ℝ (blockMul G K) x (Pi.single (embedRight j) 1) := by
  have hline : (fun t : ℝ =>
      blockMul G K (x + t • (Pi.single (embedRight j) 1 : Coords (n + n')))) =
      fun t : ℝ => G (restrictLeft x) * K (restrictRight x + t • (Pi.single j 1 : Coords n')) := by
    funext t
    simp only [blockMul, restrictLeft_add_right, restrictRight_add_right]
  unfold LineDifferentiableAt
  rw [hline]
  exact DifferentiableAt.const_mul (hK (restrictRight x)) _
theorem index_embed_cases (j : Fin (4 * ((n + n' : ℕ+) : ℕ))) :
    (∃ i, j = embedLeft i) ∨ ∃ i, j = embedRight i := by
  have hj : (j : ℕ) < 4 * ((n : ℕ) + (n' : ℕ)) := j.2
  by_cases h : (j : ℕ) < 4 * (n : ℕ)
  · exact Or.inl ⟨⟨j, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨(j : ℕ) - 4 * (n : ℕ), by omega⟩, Fin.ext ?_⟩
    simp only [embedRight]
    omega
theorem contPartialsUpTo_blockMul (ν : ℕ) (G : Coords n → ℂ)
    (K : Coords n' → ℂ) (hG : ContPartialsUpTo ν G)
    (hK : ContPartialsUpTo ν K) :
    ContPartialsUpTo ν (blockMul G K) := by
  induction ν generalizing G K with
  | zero => exact continuous_blockMul hG hK
  | succ ν ih =>
    refine ⟨continuous_blockMul hG.1 hK.1, fun j => ?_⟩
    rcases index_embed_cases j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · refine ⟨lineDifferentiableAt_blockMul_left i K (hG.2 i).1, ?_⟩
      rw [partialAlong_blockMul_left]
      exact ih _ _ (hG.2 i).2 (contPartialsUpTo_of_succ ν K hK)
    · refine ⟨lineDifferentiableAt_blockMul_right i G (hK.2 i).1, ?_⟩
      rw [partialAlong_blockMul_right]
      exact ih _ _ (contPartialsUpTo_of_succ ν G hG) (hK.2 i).2
section Flat
variable (D : Params)
theorem proj_flatCoords {p : ℕ+} (y : Kind.euclidean.Tuple D p) :
    Kind.Tuple.proj D .euclidean (flatCoords y) = y := by
  funext i
  exact block_flatCoords y i
theorem flatCoords_proj {p : ℕ+} (x : Coords p) :
    flatCoords (Kind.Tuple.proj D .euclidean x) = x := by
  funext j
  show x ⟨4 * ((j : ℕ) / 4) + (j : ℕ) % 4, _⟩ = x j
  congr 1
  apply Fin.ext
  simp only
  omega
theorem eq_of_comp_proj {p : ℕ+} {A B : Kind.euclidean.Tuple D p → ℂ}
    (h : A ∘ Kind.Tuple.proj D .euclidean =
      B ∘ Kind.Tuple.proj D .euclidean) : A = B := by
  funext y
  have := congrFun h (flatCoords y)
  simpa only [Function.comp, proj_flatCoords] using this
theorem partialDeriv_comp_proj {p : ℕ+} (α : CoordIndex p)
    (F : Kind.euclidean.Tuple D p → ℂ) :
    Kind.Tuple.partialDeriv D .euclidean α F ∘
        Kind.Tuple.proj D .euclidean =
      iterPartial α (F ∘ Kind.Tuple.proj D .euclidean) := by
  refine Classical.epsilon_spec
    (p := fun A : Kind.euclidean.Tuple D p → ℂ =>
      A ∘ Kind.Tuple.proj D .euclidean =
        iterPartial α (F ∘ Kind.Tuple.proj D .euclidean))
    ⟨fun y => iterPartial α (F ∘ Kind.Tuple.proj D .euclidean)
      (flatCoords y), ?_⟩
  funext x
  simp only [Function.comp, flatCoords_proj]
def initPts (y : Kind.euclidean.Tuple D (n + n')) : Kind.euclidean.Tuple D n :=
  fun i => y (Fin.castAdd (n' : ℕ) i)
def tailPts (y : Kind.euclidean.Tuple D (n + n')) : Kind.euclidean.Tuple D n' :=
  fun i => y (Fin.natAdd (n : ℕ) i)
theorem tensorMul_apply (F : Kind.euclidean.Tuple D n → ℂ)
    (H : Kind.euclidean.Tuple D n' → ℂ) (y : Kind.euclidean.Tuple D (n + n')) :
    tensorMul D F H y = F (initPts D y) * H (tailPts D y) :=
  rfl
theorem initPts_appendPts (a : Kind.euclidean.Tuple D n)
    (b : Kind.euclidean.Tuple D n') : initPts D (appendPts D a b) = a :=
  funext fun i => Fin.append_left a b i
theorem tailPts_appendPts (a : Kind.euclidean.Tuple D n)
    (b : Kind.euclidean.Tuple D n') : tailPts D (appendPts D a b) = b :=
  funext fun i => Fin.append_right a b i
theorem appendPts_initPts_tailPts (y : Kind.euclidean.Tuple D (n + n')) :
    appendPts D (initPts D y) (tailPts D y) = y :=
  Fin.append_castAdd_natAdd (f := y)
theorem initPts_proj (x : Coords (n + n')) :
    initPts D (Kind.Tuple.proj D .euclidean x) =
      Kind.Tuple.proj D .euclidean (restrictLeft x) :=
  rfl
theorem tailPts_proj (x : Coords (n + n')) :
    tailPts D (Kind.Tuple.proj D .euclidean x) =
      Kind.Tuple.proj D .euclidean (restrictRight x) := by
  funext i μ
  show x ⟨4 * ((n : ℕ) + (i : ℕ)) + (μ : ℕ), _⟩ = x ⟨4 * (n : ℕ) + (4 * (i : ℕ) + (μ : ℕ)), _⟩
  congr 1
  apply Fin.ext
  simp only
  omega
theorem tensorMul_comp_proj (F : Kind.euclidean.Tuple D n → ℂ)
    (H : Kind.euclidean.Tuple D n' → ℂ) :
    tensorMul D F H ∘ Kind.Tuple.proj D .euclidean =
      blockMul (F ∘ Kind.Tuple.proj D .euclidean)
        (H ∘ Kind.Tuple.proj D .euclidean) := by
  funext x
  simp only [Function.comp, tensorMul_apply, initPts_proj, tailPts_proj, blockMul]
theorem partialDeriv_tensorMul (α : CoordIndex n) (α' : CoordIndex n')
    (F : Kind.euclidean.Tuple D n → ℂ) (H : Kind.euclidean.Tuple D n' → ℂ) :
    Kind.Tuple.partialDeriv D .euclidean (appendIdx α α') (tensorMul D F H) =
      tensorMul D (Kind.Tuple.partialDeriv D .euclidean α F)
        (Kind.Tuple.partialDeriv D .euclidean α' H) := by
  apply eq_of_comp_proj
  rw [partialDeriv_comp_proj, tensorMul_comp_proj, tensorMul_comp_proj, iterPartial_blockMul,
    partialDeriv_comp_proj, partialDeriv_comp_proj]
def idxLeft (γ : CoordIndex (n + n')) : CoordIndex n :=
  fun j => γ (embedLeft j)
def idxRight (γ : CoordIndex (n + n')) : CoordIndex n' :=
  fun j => γ (embedRight j)
theorem appendIdx_idxLeft_idxRight (γ : CoordIndex (n + n')) :
    appendIdx (idxLeft γ) (idxRight γ) = γ := by
  funext j
  rcases index_embed_cases j with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [appendIdx_embedLeft]
    rfl
  · rw [appendIdx_embedRight]
    rfl
theorem degree_idxLeft_le (γ : CoordIndex (n + n')) :
    (idxLeft γ).degree ≤ γ.degree := by
  have hinj : Function.Injective (embedLeft (n := n) (n' := n')) := fun _ _ e => embedLeft_inj.1 e
  have h := Finset.sum_image (s := Finset.univ) (g := embedLeft (n := n) (n' := n')) (f := γ)
    (fun _ _ _ _ e => hinj e)
  simp only [CoordIndex.degree, idxLeft]
  rw [← h]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
theorem degree_idxRight_le (γ : CoordIndex (n + n')) :
    (idxRight γ).degree ≤ γ.degree := by
  have hinj : Function.Injective (embedRight (n := n) (n' := n')) :=
    fun _ _ e => embedRight_inj.1 e
  have h := Finset.sum_image (s := Finset.univ) (g := embedRight (n := n) (n' := n')) (f := γ)
    (fun _ _ _ _ e => hinj e)
  simp only [CoordIndex.degree, idxRight]
  rw [← h]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
theorem quotDist_nonneg (y y' : Kind.euclidean.Pt D) : 0 ≤ Kind.quotDist D .euclidean y y' := by
  apply Real.sInf_nonneg
  rintro r ⟨x, x', _, _, k, _, rfl⟩
  exact Real.sqrt_nonneg _
theorem mem_supportT_iff {p : ℕ+} (F : Kind.euclidean.Tuple D p → ℂ)
    (y : Kind.euclidean.Tuple D p) :
    y ∈ Kind.Tuple.supportT D .euclidean F ↔
      ∀ r : ℝ, 0 < r → ∃ z, F z ≠ 0 ∧ Kind.Tuple.tupleDist D .euclidean y z < r :=
  Iff.rfl
theorem mem_supportQ_iff (f : Kind.euclidean.Pt D → ℂ) (y : Kind.euclidean.Pt D) :
    y ∈ Kind.supportQ D .euclidean f ↔
      ∀ r : ℝ, 0 < r → ∃ z, f z ≠ 0 ∧ Kind.quotDist D .euclidean y z < r :=
  Iff.rfl
theorem sum_sq_quotDist_appendPts (a u : Kind.euclidean.Tuple D n)
    (b v : Kind.euclidean.Tuple D n') :
    ∑ i, Kind.quotDist D .euclidean (appendPts D a b i) (appendPts D u v i) ^ 2 =
      (∑ i, Kind.quotDist D .euclidean (a i) (u i) ^ 2) +
        ∑ i, Kind.quotDist D .euclidean (b i) (v i) ^ 2 := by
  show ∑ i : Fin ((n : ℕ) + (n' : ℕ)),
    Kind.quotDist D .euclidean (Fin.append a b i) (Fin.append u v i) ^ 2 = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
theorem sum_sq_quotDist_nonneg {p : ℕ+} (a u : Kind.euclidean.Tuple D p) :
    0 ≤ ∑ i, Kind.quotDist D .euclidean (a i) (u i) ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
theorem tupleDist_init_le (a u : Kind.euclidean.Tuple D n)
    (b v : Kind.euclidean.Tuple D n') :
    Kind.Tuple.tupleDist D .euclidean a u ≤
      Kind.Tuple.tupleDist D .euclidean (appendPts D a b) (appendPts D u v) := by
  simp only [Kind.Tuple.tupleDist]
  rw [sum_sq_quotDist_appendPts]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sum_sq_quotDist_nonneg D b v))
theorem tupleDist_tail_le (a u : Kind.euclidean.Tuple D n)
    (b v : Kind.euclidean.Tuple D n') :
    Kind.Tuple.tupleDist D .euclidean b v ≤
      Kind.Tuple.tupleDist D .euclidean (appendPts D a b) (appendPts D u v) := by
  simp only [Kind.Tuple.tupleDist]
  rw [sum_sq_quotDist_appendPts]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (sum_sq_quotDist_nonneg D a u))
theorem tupleDist_appendPts_lt {r : ℝ} (hr : 0 < r) (a u : Kind.euclidean.Tuple D n)
    (b v : Kind.euclidean.Tuple D n')
    (h₁ : Kind.Tuple.tupleDist D .euclidean a u < r / 2)
    (h₂ : Kind.Tuple.tupleDist D .euclidean b v < r / 2) :
    Kind.Tuple.tupleDist D .euclidean (appendPts D a b) (appendPts D u v) < r := by
  simp only [Kind.Tuple.tupleDist] at h₁ h₂ ⊢
  rw [sum_sq_quotDist_appendPts, Real.sqrt_lt' hr]
  rw [Real.sqrt_lt' (by positivity)] at h₁ h₂
  nlinarith
theorem supportT_tensorMul (F : Kind.euclidean.Tuple D n → ℂ)
    (H : Kind.euclidean.Tuple D n' → ℂ) :
    Kind.Tuple.supportT D .euclidean (tensorMul D F H) =
      Set.image2 (appendPts D) (Kind.Tuple.supportT D .euclidean F)
        (Kind.Tuple.supportT D .euclidean H) := by
  ext y
  constructor
  · intro hy
    rw [mem_supportT_iff] at hy
    refine ⟨initPts D y, ?_, tailPts D y, ?_, appendPts_initPts_tailPts D y⟩
    · rw [mem_supportT_iff]
      intro r hr
      obtain ⟨z, hz, hd⟩ := hy r hr
      rw [tensorMul_apply] at hz
      refine ⟨initPts D z, left_ne_zero_of_mul hz, lt_of_le_of_lt ?_ hd⟩
      have := tupleDist_init_le D (initPts D y) (initPts D z) (tailPts D y) (tailPts D z)
      rwa [appendPts_initPts_tailPts, appendPts_initPts_tailPts] at this
    · rw [mem_supportT_iff]
      intro r hr
      obtain ⟨z, hz, hd⟩ := hy r hr
      rw [tensorMul_apply] at hz
      refine ⟨tailPts D z, right_ne_zero_of_mul hz, lt_of_le_of_lt ?_ hd⟩
      have := tupleDist_tail_le D (initPts D y) (initPts D z) (tailPts D y) (tailPts D z)
      rwa [appendPts_initPts_tailPts, appendPts_initPts_tailPts] at this
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [mem_supportT_iff] at ha hb ⊢
    intro r hr
    obtain ⟨u, hu, hdu⟩ := ha (r / 2) (by positivity)
    obtain ⟨v, hv, hdv⟩ := hb (r / 2) (by positivity)
    refine ⟨appendPts D u v, ?_, tupleDist_appendPts_lt D hr a u b v hdu hdv⟩
    rw [tensorMul_apply, initPts_appendPts, tailPts_appendPts]
    exact mul_ne_zero hu hv
theorem supportT_tensorFn (f : Fin (n : ℕ) → Kind.euclidean.Pt D → ℂ) :
    Kind.Tuple.supportT (p := n) D .euclidean (Kind.tensorFn D .euclidean f) =
      Set.univ.pi fun i => Kind.supportQ D .euclidean (f i) := by
  ext y
  rw [Set.mem_univ_pi]
  constructor
  · intro hy i
    rw [mem_supportT_iff] at hy
    rw [mem_supportQ_iff]
    intro r hr
    obtain ⟨z, hz, hd⟩ := hy r hr
    refine ⟨z i, (Finset.prod_ne_zero_iff.1 hz) i (Finset.mem_univ i), lt_of_le_of_lt ?_ hd⟩
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    exact Finset.single_le_sum (f := fun k => Kind.quotDist D .euclidean (y k) (z k) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  · intro hy
    rw [mem_supportT_iff]
    intro r hr
    obtain ⟨δ, hδ, hrδ⟩ : ∃ δ : ℝ, 0 < δ ∧ r = (((n : ℕ) : ℝ) + 1) * δ :=
      ⟨r / (((n : ℕ) : ℝ) + 1), by positivity, by field_simp⟩
    have hz := fun i => (mem_supportQ_iff D (f i) (y i)).1 (hy i) δ hδ
    choose z hz hd using hz
    refine ⟨z, Finset.prod_ne_zero_iff.2 fun i _ => hz i, ?_⟩
    simp only [Kind.Tuple.tupleDist]
    rw [Real.sqrt_lt' hr]
    have hsum : ∑ i, Kind.quotDist D .euclidean (y i) (z i) ^ 2 ≤ ((n : ℕ) : ℝ) * δ ^ 2 := by
      have hle : ∀ i ∈ (Finset.univ : Finset (Fin (n : ℕ))),
          Kind.quotDist D .euclidean (y i) (z i) ^ 2 ≤ δ ^ 2 := fun i _ =>
        pow_le_pow_left₀ (quotDist_nonneg D _ _) (hd i).le 2
      have := Finset.sum_le_card_nsmul _ _ _ hle
      simpa using this
    have hpos : 0 < (((n : ℕ) : ℝ) ^ 2 + ((n : ℕ) : ℝ) + 1) * δ ^ 2 := by positivity
    rw [hrδ]
    nlinarith
theorem tensorFn_update (f : Fin (n : ℕ) → Kind.euclidean.Pt D → ℂ) (i : Fin (n : ℕ))
    (u : Kind.euclidean.Pt D → ℂ) (y : Fin (n : ℕ) → Kind.euclidean.Pt D) :
    Kind.tensorFn D .euclidean (Function.update f i u) y =
      u (y i) * ∏ k ∈ Finset.univ.erase i, f k (y k) := by
  show ∏ k, Function.update f i u k (y k) = _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
theorem tensorFnOfOne_holds : TensorFnOfOne D := by
  intro f
  funext y
  show ∏ i : Fin 1, f i (y i) = f 0 (y ⟨0, (1 : ℕ+).pos⟩)
  rw [Fin.prod_univ_one]
  rfl
theorem tensorMulOfTensorFns_holds : TensorMulOfTensorFns D n n' := by
  intro f g
  funext y
  rw [tensorMul_apply]
  show (∏ i, f i (initPts D y i)) * ∏ i, g i (tailPts D y i) =
    ∏ k : Fin ((n : ℕ) + (n' : ℕ)), Fin.append f g k (y k)
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rfl
theorem tensorMulLinear_holds : TensorMulLinear D n n' := by
  refine ⟨fun H => ⟨fun A B => ?_, fun c A => ?_⟩, fun F => ⟨fun A B => ?_, fun c A => ?_⟩⟩
  · funext y
    simp only [tensorMul_apply, Pi.add_apply, add_mul]
  · funext y
    simp only [tensorMul_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  · funext y
    simp only [tensorMul_apply, Pi.add_apply, mul_add]
  · funext y
    simp only [tensorMul_apply, Pi.smul_apply, smul_eq_mul]
    ring
theorem tensorFnLinearInFactor_holds : TensorFnLinearInEntry D n := by
  intro f i
  refine ⟨fun u v => ?_, fun c u => ?_⟩
  · funext y
    simp only [Pi.add_apply, tensorFn_update, add_mul]
  · funext y
    simp only [Pi.smul_apply, tensorFn_update, smul_eq_mul, mul_assoc]
theorem tensorFnMul_holds : TensorFnMul D n := by
  intro f h
  funext y
  show (∏ i, f i (y i)) * ∏ i, h i (y i) = ∏ i, (f i * h i) (y i)
  rw [← Finset.prod_mul_distrib]
  rfl
theorem derivTensorMul_holds : DerivTensorMul D n n' := by
  intro F H hF hH
  refine ⟨fun ν => ?_, fun α α' => partialDeriv_tensorMul D α α' F H⟩
  show ContPartialsUpTo ν
    (tensorMul D F H ∘ Kind.Tuple.proj D .euclidean)
  rw [tensorMul_comp_proj]
  exact contPartialsUpTo_blockMul ν _ _ (hF ν) (hH ν)
theorem tensorFnSmooth_holds (hI : PartialDerivatives.IteratedPartialsOfBlockProduct) :
    TensorFnSmooth D n := by
  intro f hf ν
  have h := (hI n ν (fun i => Kind.Tuple.ofSingle D .euclidean (f i) ∘
    Kind.Tuple.proj D .euclidean) fun i => hf i ν).1
  have e : (fun x : Coords n => ∏ i, (Kind.Tuple.ofSingle D .euclidean (f i) ∘
      Kind.Tuple.proj D .euclidean) (x.block i)) =
      Kind.tensorFn D .euclidean f ∘ Kind.Tuple.proj D .euclidean := by
    funext x
    refine Finset.prod_congr rfl fun i _ => ?_
    show f i _ = f i _
    congr 1
    funext μ
    show (x.block i) ⟨4 * 0 + (μ : ℕ), _⟩ = x.block i μ
    congr 1
    apply Fin.ext
    simp
  rw [e] at h
  exact h
theorem normTensorMulLE_holds : NormTensorMulLE D n n' := by
  intro F H ν _ _ _ _
  refine iSup_le fun γ => iSup_le fun hγ => iSup_le fun y => ?_
  have hF : ENNReal.ofReal ‖Kind.Tuple.partialDeriv D .euclidean (idxLeft γ) F
      (initPts D y)‖ ≤ Kind.Tuple.cNorm D .euclidean ν F :=
    le_iSup_of_le (idxLeft γ) (le_iSup_of_le ((degree_idxLeft_le γ).trans hγ)
      (le_iSup_of_le (initPts D y) le_rfl))
  have hH : ENNReal.ofReal ‖Kind.Tuple.partialDeriv D .euclidean (idxRight γ) H
      (tailPts D y)‖ ≤ Kind.Tuple.cNorm D .euclidean ν H :=
    le_iSup_of_le (idxRight γ) (le_iSup_of_le ((degree_idxRight_le γ).trans hγ)
      (le_iSup_of_le (tailPts D y) le_rfl))
  have hd := congrFun (partialDeriv_tensorMul D (idxLeft γ) (idxRight γ) F H) y
  rw [appendIdx_idxLeft_idxRight, tensorMul_apply] at hd
  rw [hd, norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
  exact mul_le_mul' hF hH
end Flat
theorem allRules_holds (hI : PartialDerivatives.IteratedPartialsOfBlockProduct) : AllRules :=
  fun D _ _ =>
    ⟨tensorFnOfOne_holds D, tensorMulOfTensorFns_holds D, tensorMulLinear_holds D,
      tensorFnLinearInFactor_holds D, tensorFnMul_holds D, supportT_tensorMul D,
      supportT_tensorFn D, derivTensorMul_holds D, tensorFnSmooth_holds D hI,
      normTensorMulLE_holds D⟩
end YangMills.Construction.PeriodicSpace.TensorRules
end
