import YangMills.Construction.Continuum.FirstFactsOnTheTestSpaces
import YangMills.Construction.Continuum.OperationsOnTestFunctions
import YangMills.Construction.Continuum.PassageFromTuplesToSchwartzFunctions
import YangMills.Construction.Continuum.TensorBoundsIntegrationBoundsAndDensity
import YangMills.Construction.Continuum.TransferPrinciple
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ENNReal ContDiff
noncomputable section
namespace YangMills.Construction.TestSpaces.SchwartzPassage
open TestFunctionOps TestSpaceFacts Motions
theorem multiDeriv_of_fin_zero (α : MultiIdx4 0) (g : PointTuple 0 → ℂ) :
    multiDeriv α g = g := by
  simp [multiDeriv]
theorem weightedSeminorm_of_fin_zero (K : ℕ) (g : PointTuple 0 → ℂ) (e : PointTuple 0) :
    weightedSeminorm K g = ENNReal.ofReal ‖g e‖ := by
  unfold weightedSeminorm
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun α => iSup_le fun _ => ?_
    rw [multiDeriv_of_fin_zero, tupleNorm_of_fin_zero, Subsingleton.elim x e]
    simp
  · refine le_iSup_of_le e (le_iSup_of_le (fun i => i.elim0) (le_iSup_of_le (by simp [idxOrder]) ?_))
    rw [multiDeriv_of_fin_zero, tupleNorm_of_fin_zero]
    simp
theorem mem_flatSchwartzSet_of_fin_zero (g : PointTuple 0 → ℂ) : g ∈ flatSchwartzSet 0 := by
  have hs : ContDiff ℝ ∞ g := by
    have h : g = fun _ => g 0 := funext fun x => congrArg g (Subsingleton.elim _ _)
    rw [h]
    exact contDiff_const
  refine ⟨⟨hs, fun k _ => ?_⟩, fun α x hx => ?_⟩
  · rw [weightedSeminorm_of_fin_zero k g 0]
    exact ENNReal.ofReal_lt_top
  · obtain ⟨i, _⟩ := (mem_diagonalLocus_iff x).1 hx
    exact i.elim0
theorem exists_submodule_flatSchwartzSet (hF : Elementary.BasicProperties) (n : ℕ) :
    ∃ W : Submodule ℂ (PointTuple n → ℂ), ∀ g, g ∈ W ↔ g ∈ flatSchwartzSet n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨⊤, fun g => by simpa using mem_flatSchwartzSet_of_fin_zero g⟩
  · obtain ⟨hOps, hOpen, -, -, -⟩ := hF n hn
    obtain ⟨oD, -, -, -, -, -, hflat, -⟩ := hOpen
    obtain ⟨W, hW⟩ := hOps.2 _ oD
    refine ⟨W, fun g => ?_⟩
    rw [hflat, ← hW]
    rfl
def IsPositiveTimeTest (q : ℕ) (a : PointTuple q → ℂ) : Prop :=
  0 < q → a ∈ schwartzSet q ∧ VanishesToInfiniteOrderOff a (positiveTimeLocus q)
theorem exists_submodule_positiveTimeTest (hF : Elementary.BasicProperties) (q : ℕ) :
    ∃ W : Submodule ℂ (PointTuple q → ℂ), ∀ a, a ∈ W ↔ IsPositiveTimeTest q a := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact ⟨⊤, fun a => by simp [IsPositiveTimeTest]⟩
  · obtain ⟨hOps, hOpen, -, -, -⟩ := hF q hq
    obtain ⟨-, oP, -, -, -, -, -, -⟩ := hOpen
    obtain ⟨W, hW⟩ := hOps.2 _ oP
    refine ⟨W, fun a => ?_⟩
    have h : a ∈ W ↔ a ∈ (W : Set (PointTuple q → ℂ)) := Iff.rfl
    rw [h, hW]
    exact ⟨fun h _ => h, fun h => h hq⟩
theorem IsPositiveTimeTest.mem_flatSchwartzSet (hF : Elementary.BasicProperties) {q : ℕ}
    {a : PointTuple q → ℂ} (ha : IsPositiveTimeTest q a) : a ∈ flatSchwartzSet q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact mem_flatSchwartzSet_of_fin_zero a
  · obtain ⟨has, haf⟩ := ha hq
    obtain ⟨-, -, -, -, -, -, -, hsub⟩ := (hF q hq).2.1
    exact hsub a has (Or.inl haf)
theorem tensorFun_of_left_fin_zero {q' : ℕ} {P : ∀ m, (PointTuple m → ℂ) → Prop}
    (a : PointTuple 0 → ℂ) (b : PointTuple q' → ℂ) (h : P q' (scalarTensorLeft (a 0) b)) :
    P (0 + q') (tensorFun a b) := by
  have key : ∀ (m : ℕ) (hm : m = q') (g : PointTuple m → ℂ),
      (∀ y : PointTuple q', g (fun i => y (Fin.cast hm i)) = a 0 * b y) → P m g := by
    intro m hm g hg
    subst hm
    have e : g = scalarTensorLeft (a 0) b := funext fun y => hg y
    exact e ▸ h
  refine key _ (Nat.zero_add q') _ fun y => ?_
  show a _ * b _ = _
  rw [Subsingleton.elim (leftPart (q := 0) (q' := q') _) 0]
  congr 2
  funext j
  simp only [rightPart]
  congr 1
  ext
  simp
theorem scalarTensorLeft_mem_and_seminorm (hF : Elementary.BasicProperties)
    (hD : TestSpaceFacts.Statement) {p : ℕ} (c : ℂ)
    {g : PointTuple p → ℂ} (hg : g ∈ flatSchwartzSet p) :
    scalarTensorLeft c g ∈ flatSchwartzSet p ∧
      ∀ K : ℕ, 0 < K →
        weightedSeminorm K (scalarTensorLeft c g) = ENNReal.ofReal ‖c‖ * weightedSeminorm K g := by
  obtain ⟨W, hW⟩ := exists_submodule_flatSchwartzSet hF p
  have hmem : scalarTensorLeft c g ∈ W := W.smul_mem c ((hW g).2 hg)
  refine ⟨(hW _).1 hmem, fun K hK => ?_⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [weightedSeminorm_of_fin_zero K _ 0, weightedSeminorm_of_fin_zero K _ 0,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    simp [scalarTensorLeft]
  · exact hD.2.1 p K hp hK c g hg.1
theorem reflectConj_tensorFun_mem_and_le (hF : Elementary.BasicProperties)
    (hO : OperationsStatement) (hD : TestSpaceFacts.Statement) {q q' : ℕ}
    {a : PointTuple q → ℂ} {b : PointTuple q' → ℂ} (ha : IsPositiveTimeTest q a)
    (hb : IsPositiveTimeTest q' b) :
    tensorFun (reflectConj a) b ∈ flatSchwartzSet (q + q') ∧
      ∀ K : ℕ, 0 < K → weightedSeminorm K (tensorFun (reflectConj a) b) ≤
        weightedSeminorm K a * weightedSeminorm K b := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hθ : ‖reflectConj a 0‖ = ‖a 0‖ := by
      show ‖conj (a (timeReflectTuple 0))‖ = _
      rw [Subsingleton.elim (timeReflectTuple (0 : PointTuple 0)) 0]
      simp
    refine tensorFun_of_left_fin_zero (P := fun m g => g ∈ flatSchwartzSet m ∧
      ∀ K : ℕ, 0 < K → weightedSeminorm K g ≤ weightedSeminorm K a * weightedSeminorm K b)
      (reflectConj a) b ?_
    obtain ⟨h₁, h₂⟩ := scalarTensorLeft_mem_and_seminorm hF hD (reflectConj a 0) (hb.mem_flatSchwartzSet hF)
    refine ⟨h₁, fun K hK => ?_⟩
    rw [h₂ K hK, weightedSeminorm_of_fin_zero K a 0, hθ]
  · obtain ⟨has, haf⟩ := ha hq
    have hkeep := (hO.1 q 1 hq one_pos 1 RigidMotion.timeReflection).2.1 a has
    have hθs : reflectConj a ∈ schwartzSet q := hkeep.1.2.2.1
    have hθf : VanishesToInfiniteOrderOff (reflectConj a) (negativeTimeLocus q) := hkeep.2.2.1 haf
    have hθn : ∀ K : ℕ, 0 < K → weightedSeminorm K (reflectConj a) = weightedSeminorm K a :=
      fun K hK => ((hO.1 q K hq hK 1 RigidMotion.timeReflection).2.1 a has).2.1.2.1
    rcases Nat.eq_zero_or_pos q' with rfl | hq'
    · obtain ⟨-, -, -, -, -, -, -, hsub⟩ := (hF q hq).2.1
      have hθm : reflectConj a ∈ flatSchwartzSet q := hsub _ hθs (Or.inr hθf)
      have e : tensorFun (reflectConj a) b = scalarTensorLeft (b 0) (reflectConj a) := by
        funext x
        show reflectConj a (leftPart x) * b (rightPart x) = b 0 * reflectConj a x
        rw [Subsingleton.elim (rightPart x) 0, mul_comm]
        rfl
      obtain ⟨h₁, h₂⟩ := scalarTensorLeft_mem_and_seminorm hF hD (b 0) hθm
      refine ⟨by rw [e]; exact h₁, fun K hK => ?_⟩
      rw [e, h₂ K hK, hθn K hK, weightedSeminorm_of_fin_zero K b 0, mul_comm]
    · obtain ⟨hbs, hbf⟩ := hb hq'
      refine ⟨(hD.1 q q' 1 hq hq' one_pos _ hθs _ hbs).2.2 hθf hbf, fun K hK => ?_⟩
      rw [← hθn K hK]
      exact (hD.1 q q' K hq hq' hK _ hθs _ hbs).2.1
theorem tensorFun_reflectConj_tensorProdComplex {q q' : ℕ} (f : Fin q → (Fin 4 → ℝ) → ℝ)
    (g : Fin q' → (Fin 4 → ℝ) → ℝ) :
    tensorFun (reflectConj (tensorProdComplex f)) (tensorProdComplex g) =
      tensorProdComplex (concatTuple (reflectTuple f) g) := by
  funext z
  simp only [tensorFun, reflectConj, tensorProdComplex, Complex.conj_ofReal, tensorProd]
  rw [Fin.prod_univ_add]
  simp only [concatTuple_castAdd, concatTuple_natAdd, reflectTuple, reflectFun_eq,
    Function.comp, timeReflectTuple, leftPart, rightPart]
  push_cast
  rfl
theorem tensorCombination_eq_sum {n m : ℕ} (c : Fin m → ℂ) (f : Fin m → Fin n → (Fin 4 → ℝ) → ℝ) :
    tensorCombination c f = ∑ ι, c ι • tensorProdComplex (f ι) := by
  funext x
  simp [tensorCombination, tensorProdComplex, Finset.sum_apply]
theorem tensorFun_reflectConj_tensorCombination {q q' m m' : ℕ} (c : Fin m → ℂ)
    (f : Fin m → Fin q → (Fin 4 → ℝ) → ℝ) (c' : Fin m' → ℂ)
    (f' : Fin m' → Fin q' → (Fin 4 → ℝ) → ℝ) :
    tensorFun (reflectConj (tensorCombination c f)) (tensorCombination c' f') =
      ∑ p : Fin m × Fin m', (conj (c p.1) * c' p.2) •
        tensorProdComplex (concatTuple (reflectTuple (f p.1)) (f' p.2)) := by
  funext z
  simp only [← tensorFun_reflectConj_tensorProdComplex, tensorCombination_eq_sum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, tensorFun, reflectConj, map_sum, map_mul, Finset.sum_mul_sum,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
theorem tensorProdComplex_eq_tensorProd {n : ℕ} (f : Fin n → (Fin 4 → ℝ) → ℝ) :
    tensorProdComplex f = tensorProd (complexify f) :=
  funext fun x => (tensorProd_complexify f x).symm
theorem isOpen_upperHalfSpace : IsOpen upperHalfSpace :=
  isOpen_lt continuous_const (continuous_apply 3)
theorem tensorProdComplex_mem_flatSchwartzSet (hF : Elementary.BasicProperties) {n : ℕ}
    {f : Fin n → (Fin 4 → ℝ) → ℝ} (hf : f ∈ disjointSupportTuples Set.univ n)
    (hs : HasSmoothComponents Set.univ f) : tensorProdComplex f ∈ flatSchwartzSet n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact mem_flatSchwartzSet_of_fin_zero _
  · exact (((hF n hn).2.2.2.1 Set.univ isOpen_univ f hf).2 hs).2.1
theorem tensorProdComplex_positiveTimeTest (hF : Elementary.BasicProperties) {q : ℕ}
    {f : Fin q → (Fin 4 → ℝ) → ℝ} (hf : f ∈ disjointSupportTuples upperHalfSpace q)
    (hs : HasSmoothComponents upperHalfSpace f) : IsPositiveTimeTest q (tensorProdComplex f) :=
  fun hq =>
    have h := ((hF q hq).2.2.2.1 upperHalfSpace isOpen_upperHalfSpace f hf).2 hs
    ⟨h.2.1.1, h.2.2 rfl⟩
theorem weightedSeminorm_add_le (hF : Elementary.BasicProperties) {p : ℕ} (hp : 0 < p)
    {D₁ D₂ : PointTuple p → ℂ} (h₁ : D₁ ∈ schwartzSet p) (h₂ : D₂ ∈ schwartzSet p)
    {K : ℕ} (hK : 0 < K) :
    weightedSeminorm K (D₁ + D₂) ≤ weightedSeminorm K D₁ + weightedSeminorm K D₂ := by
  have h := (((hF p hp).1.1 D₁ h₁ D₂ h₂ 1 1).2.1 K K hK le_rfl).2.1
  have e : Elementary.linComb 1 D₁ 1 D₂ = D₁ + D₂ := by
    funext x
    simp [Elementary.linComb]
  rw [e] at h
  simpa using h
theorem IsPositiveTimeTest.weightedSeminorm_ne_top {q : ℕ} {a : PointTuple q → ℂ}
    (ha : IsPositiveTimeTest q a) {K : ℕ} (hK : 0 < K) : weightedSeminorm K a ≠ ⊤ := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [weightedSeminorm_of_fin_zero K a 0]
    exact ENNReal.ofReal_ne_top
  · exact ((ha hq).1.2 K hK).ne
theorem weightedSeminorm_le_add_one_of_close (hF : Elementary.BasicProperties) {q : ℕ}
    {a a' : PointTuple q → ℂ} (ha : IsPositiveTimeTest q a) (ha' : IsPositiveTimeTest q a')
    {K : ℕ} (hK : 0 < K) {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (h₁ : weightedSeminorm K a ≤ ENNReal.ofReal A)
    (h₂ : weightedSeminorm K (a - a') ≤ ENNReal.ofReal ε) :
    weightedSeminorm K a' ≤ ENNReal.ofReal (A + 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [weightedSeminorm_of_fin_zero K _ 0] at h₁ h₂ ⊢
    have i₁ := (ENNReal.ofReal_le_ofReal_iff hA).1 h₁
    have i₂ := (ENNReal.ofReal_le_ofReal_iff hε).1 h₂
    refine ENNReal.ofReal_le_ofReal ?_
    have h : ‖a' 0‖ ≤ ‖a 0‖ + ‖(a - a') 0‖ := by
      have e : a' 0 = a 0 - (a - a') 0 := by simp
      rw [e]
      exact norm_sub_le _ _
    linarith
  · obtain ⟨W, hW⟩ := exists_submodule_positiveTimeTest hF q
    have hds : a - a' ∈ schwartzSet q :=
      ((hW _).1 (W.sub_mem ((hW _).2 ha) ((hW _).2 ha')) hq).1
    have h := (((hF q hq).1.1 a (ha hq).1 (a - a') hds 1 (-1)).2.1 K K hK le_rfl).2.1
    have e : Elementary.linComb 1 a (-1) (a - a') = a' := by
      funext x
      simp [Elementary.linComb]
    rw [e] at h
    simp only [norm_one, norm_neg, ENNReal.ofReal_one, one_mul] at h
    calc weightedSeminorm K a' ≤ ENNReal.ofReal A + ENNReal.ofReal ε := h.trans (add_le_add h₁ h₂)
      _ = ENNReal.ofReal (A + ε) := (ENNReal.ofReal_add hA hε).symm
      _ ≤ ENNReal.ofReal (A + 1) := ENNReal.ofReal_le_ofReal (by linarith)
theorem nonpos_of_le_const_mul_forall {C x : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → x ≤ C * ε) : x ≤ 0 := by
  by_contra hx
  rw [not_le] at hx
  have hpos : 0 < min 1 (x / (2 * (C + 1))) := lt_min one_pos (by positivity)
  have h₁ := h _ hpos (min_le_left _ _)
  have h₂ : min 1 (x / (2 * (C + 1))) ≤ x / (2 * (C + 1)) := min_le_right _ _
  have h₃ : min 1 (x / (2 * (C + 1))) * (2 * (C + 1)) ≤ x := by
    rwa [le_div_iff₀ (by positivity)] at h₂
  nlinarith [mul_nonneg hC hpos.le]
open Classical in
def extendByZero (T : (n : ℕ) → flatSchwartzSet n → ℂ) (n : ℕ) (g : PointTuple n → ℂ) : ℂ :=
  if h : g ∈ flatSchwartzSet n then T n ⟨g, h⟩ else 0
section Functionals
variable {σ : SepTuple → ℝ} {T : (n : ℕ) → flatSchwartzSet n → ℂ} {k : ℕ → ℕ}
  {c : ℕ → ℝ}
theorem extendByZero_of_mem {n : ℕ} {g : PointTuple n → ℂ} (h : g ∈ flatSchwartzSet n) :
    _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n g = T n ⟨g, h⟩ :=
  dif_pos h
theorem extendByZero_linear (hT : IsBoundedExtensionFamily σ T k c) {n : ℕ}
    {g h : PointTuple n → ℂ} (hg : g ∈ flatSchwartzSet n) (hh : h ∈ flatSchwartzSet n)
    (a b : ℂ) (hm : a • g + b • h ∈ flatSchwartzSet n) :
    _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n (a • g + b • h) = a * _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n g + b * _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n h := by
  rw [extendByZero_of_mem hm, extendByZero_of_mem hg, extendByZero_of_mem hh]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [hT.1, hT.1, hT.1]
    simp
  · exact (hT.2 n hn).1 a b ⟨g, hg⟩ ⟨h, hh⟩ ⟨_, hm⟩ rfl
theorem extendByZero_sum (hF : Elementary.BasicProperties) (hT : IsBoundedExtensionFamily σ T k c)
    {n : ℕ} {ι : Type*} (s : Finset ι) (a : ι → ℂ) (g : ι → PointTuple n → ℂ)
    (hg : ∀ i ∈ s, g i ∈ flatSchwartzSet n) :
    _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n (∑ i ∈ s, a i • g i) = ∑ i ∈ s, a i * _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n (g i) := by
  classical
  obtain ⟨W, hW⟩ := exists_submodule_flatSchwartzSet hF n
  have hz : _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n (0 : PointTuple n → ℂ) = 0 := by
    have h0 : (0 : PointTuple n → ℂ) ∈ flatSchwartzSet n := (hW 0).1 W.zero_mem
    have h := extendByZero_linear hT h0 h0 0 0 (by simpa using h0)
    simpa using h
  induction s using Finset.induction_on with
  | empty => simpa using hz
  | insert i s hi ih =>
    have hgi := hg i (Finset.mem_insert_self i s)
    have hgs : ∀ j ∈ s, g j ∈ flatSchwartzSet n :=
      fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have hS : (∑ j ∈ s, a j • g j) ∈ flatSchwartzSet n :=
      (hW _).1 (W.sum_mem fun j hj => W.smul_mem _ ((hW _).2 (hgs j hj)))
    have hlin := extendByZero_linear hT hgi hS (a i) 1
      ((hW _).1 (W.add_mem (W.smul_mem _ ((hW _).2 hgi)) (W.smul_mem _ ((hW _).2 hS))))
    rw [one_smul, one_mul] at hlin
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hlin, ih hgs]
theorem extendByZero_sub (hF : Elementary.BasicProperties) (hT : IsBoundedExtensionFamily σ T k c)
    {n : ℕ} {g h : PointTuple n → ℂ} (hg : g ∈ flatSchwartzSet n)
    (hh : h ∈ flatSchwartzSet n) :
    _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n (g - h) = _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n g - _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n h := by
  obtain ⟨W, hW⟩ := exists_submodule_flatSchwartzSet hF n
  have e : g - h = (1 : ℂ) • g + (-1 : ℂ) • h := by simp [sub_eq_add_neg]
  rw [e, extendByZero_linear hT hg hh 1 (-1)
    (by rw [← e]; exact (hW _).1 (W.sub_mem ((hW _).2 hg) ((hW _).2 hh)))]
  ring
theorem extendByZero_tensorProdComplex (hF : Elementary.BasicProperties)
    (hσ : IsSepFunctional σ) (hT : IsBoundedExtensionFamily σ T k c) {n : ℕ}
    (X : SepTupleOfCard n) (hs : HasSmoothComponents Set.univ X.1) :
    _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n (tensorProdComplex X.1) = σ ⟨n, X⟩ := by
  have hm := tensorProdComplex_mem_flatSchwartzSet hF X.2 hs
  rw [extendByZero_of_mem hm]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have e : (⟨0, X⟩ : SepTuple) = sepTupleNil :=
      sepTuple_ext X sepTupleNil.2 rfl fun i => i.elim0
    rw [hT.1, e, hσ.1]
    simp [tensorProdComplex, tensorProd]
  · exact (hT.2 n hn).2.2.2.2 X hs hm
theorem norm_extendByZero_le (hT : IsBoundedExtensionFamily σ T k c) {n : ℕ} (hn : 0 < n)
    {g : PointTuple n → ℂ} (hg : g ∈ flatSchwartzSet n) {B : ℝ} (hB : 0 ≤ B)
    (h : weightedSeminorm (k n) g ≤ ENNReal.ofReal B) : ‖_root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n g‖ ≤ c n * B := by
  obtain ⟨-, -, hc, hb, -⟩ := hT.2 n hn
  rw [extendByZero_of_mem hg]
  have h₁ : ENNReal.ofReal ‖T n ⟨g, hg⟩‖ ≤ ENNReal.ofReal (c n * B) := by
    rw [ENNReal.ofReal_mul hc]
    exact (hb ⟨g, hg⟩).trans (by gcongr)
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc hB)).1 h₁
theorem eq_comp_of_preserves_tensors (hTr : DensityTransfer.Statement)
    (hT : IsBoundedExtensionFamily σ T k c) {n : ℕ} (hn : 0 < n)
    (A : (PointTuple n → ℂ) → PointTuple n → ℂ)
    (hkeep : ∀ ψ ∈ flatSchwartzSet n, A ψ ∈ flatSchwartzSet n)
    (hlin : ∀ ψ₁ ∈ flatSchwartzSet n, ∀ ψ₂ ∈ flatSchwartzSet n, ∀ a b : ℂ,
      A (a • ψ₁ + b • ψ₂) = a • A ψ₁ + b • A ψ₂)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ ψ ∈ flatSchwartzSet n,
      weightedSeminorm (k n) (A ψ) ≤ ENNReal.ofReal C * weightedSeminorm (k n) ψ)
    (hagree : ∀ X : SepTupleOfCard n, HasSmoothComponents Set.univ X.1 →
      ∃ Y : SepTupleOfCard n, HasSmoothComponents Set.univ Y.1 ∧
        A (tensorProdComplex X.1) = tensorProdComplex Y.1 ∧ σ ⟨n, Y⟩ = σ ⟨n, X⟩)
    (φ : flatSchwartzSet n) :
    ∃ h : A φ.1 ∈ flatSchwartzSet n, T n ⟨_, h⟩ = T n φ := by
  obtain ⟨hlinT, hk, hc, hb, htens⟩ := hT.2 n hn
  let T₂ : flatSchwartzSet n → ℂ := fun ψ => T n ⟨A ψ.1, hkeep _ ψ.2⟩
  have hlin₂ : IsCLinearOnFlat T₂ := by
    intro a b ψ₁ ψ₂ χ hχ
    refine hlinT a b ⟨_, hkeep _ ψ₁.2⟩ ⟨_, hkeep _ ψ₂.2⟩ ⟨_, hkeep _ χ.2⟩ ?_
    show A χ.1 = _
    rw [hχ]
    exact hlin _ ψ₁.2 _ ψ₂.2 a b
  have hb₂ : IsBoundedByWeighted (c n * C) (k n) T₂ := by
    intro ψ
    refine (hb ⟨_, hkeep _ ψ.2⟩).trans ?_
    rw [ENNReal.ofReal_mul hc, mul_assoc]
    have h := hbound _ ψ.2
    gcongr
  have hag : EqOnSmoothTensors (T n) T₂ := by
    intro X hs h
    obtain ⟨Y, hY, e, hσY⟩ := hagree X hs
    have hYm : tensorProdComplex Y.1 ∈ flatSchwartzSet n := e ▸ hkeep _ h
    have e₂ : T₂ ⟨_, h⟩ = T n ⟨_, hYm⟩ := congrArg (T n) (Subtype.ext e)
    rw [e₂, htens X hs h, htens Y hY hYm, hσY]
  have h := hTr.1 n (k n) hn hk (T n) T₂ hlinT hlin₂
    ⟨c n, c n * C, hc, mul_nonneg hc hC, hb, hb₂⟩ hag
  exact ⟨hkeep _ φ.2, (congrFun h φ).symm⟩
theorem motion_invariance (hTr : DensityTransfer.Statement) (hO : OperationsStatement)
    (hT : IsBoundedExtensionFamily σ T k c) {n : ℕ} (hn : 0 < n) (r : RigidMotion)
    (hr : SepTupleInvariant σ n r) (φ : flatSchwartzSet n) :
    ∃ h : actOnFun r φ.1 ∈ flatSchwartzSet n, T n ⟨_, h⟩ = T n φ := by
  obtain ⟨hlin, hcl, -, hact⟩ := hO.1 n (k n) hn (hT.2 n hn).2.1 1 r
  refine eq_comp_of_preserves_tensors hTr hT hn (actOnFun r)
    (fun ψ hψ => ((hcl ψ hψ.1).1.2.2.2.1 hψ).2.1)
    (fun ψ₁ h₁ ψ₂ h₂ a b => (hlin ψ₁ h₁.1 ψ₂ h₂.1 a b).2.1) (motionBound r n (k n)) ?_
    (fun ψ hψ => (hcl ψ hψ.1).2.1.2.2) (fun X hs => ?_) φ
  · unfold motionBound
    positivity
  · obtain ⟨e₁, -, -, hm, hsm, -, -, -, -⟩ := hact X.1 X.2 hs
    refine ⟨⟨_, hm⟩, hsm, ?_, hr X ⟨_, hm⟩ hs rfl⟩
    rw [tensorProdComplex_eq_tensorProd, tensorProdComplex_eq_tensorProd]
    exact e₁
theorem permutation_invariance (hTr : DensityTransfer.Statement) (hO : OperationsStatement)
    (hT : IsBoundedExtensionFamily σ T k c) {n : ℕ} (hn : 0 < n)
    (hsym : SepTupleSymmetric σ n) (ς : Equiv.Perm (Fin n)) (φ : flatSchwartzSet n) :
    ∃ h : permuteArgs ς φ.1 ∈ flatSchwartzSet n, T n ⟨_, h⟩ = T n φ := by
  obtain ⟨hlin, hcl, -, hact⟩ := hO.1 n (k n) hn (hT.2 n hn).2.1 ς RigidMotion.timeReflection
  refine eq_comp_of_preserves_tensors hTr hT hn (permuteArgs ς)
    (fun ψ hψ => ((hcl ψ hψ.1).1.2.2.2.1 hψ).1)
    (fun ψ₁ h₁ ψ₂ h₂ a b => (hlin ψ₁ h₁.1 ψ₂ h₂.1 a b).1) 1 zero_le_one
    (fun ψ hψ => ?_) (fun X hs => ?_) φ
  · rw [(hcl ψ hψ.1).2.1.1]
    simp
  · obtain ⟨-, e₂, -, -, -, hm, hsm, -, -⟩ := hact X.1 X.2 hs
    refine ⟨⟨_, hm⟩, hsm, ?_, hsym ς.symm X ⟨_, hm⟩ hs rfl⟩
    rw [tensorProdComplex_eq_tensorProd, tensorProdComplex_eq_tensorProd]
    exact e₂
theorem im_extendByZero_eq_zero_of_real (hF : Elementary.BasicProperties)
    (hD : TestSpaceFacts.Statement)
    (hσ : IsSepFunctional σ) (hT : IsBoundedExtensionFamily σ T k c) {n : ℕ}
    (hn : 0 < n) {φ : PointTuple n → ℂ} (hφ : φ ∈ flatSchwartzSet n)
    (hre : ∀ x, (φ x).im = 0) : (_root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n φ).im = 0 := by
  obtain ⟨-, hk, hc, -, -⟩ := hT.2 n hn
  obtain ⟨W, hW⟩ := exists_submodule_flatSchwartzSet hF n
  obtain ⟨-, -, -, -, -, -, hflat, -⟩ := (hF n hn).2.1
  have hφ' : φ ∈ {φ | φ ∈ schwartzSet n ∧ VanishesToInfiniteOrderOff φ (distinctLocus n)} :=
    hflat ▸ hφ
  have hle : |(_root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n φ).im| ≤ 0 := by
    refine nonpos_of_le_const_mul_forall hc fun ε hε _ => ?_
    obtain ⟨m, a, f, -, hf, hclose⟩ :=
      ((hD.2.2.2 n (k n) hn hk).1 φ hφ'.1 hφ'.2 ε hε).2 hre
    have hg : ∀ ι ∈ (Finset.univ : Finset (Fin m)), tensorProdComplex (f ι) ∈
        flatSchwartzSet n :=
      fun ι _ => tensorProdComplex_mem_flatSchwartzSet hF (hf ι).1 (hf ι).2
    have hFm : tensorCombination (fun ι => (a ι : ℂ)) f ∈ flatSchwartzSet n := by
      rw [tensorCombination_eq_sum]
      exact (hW _).1 (W.sum_mem fun ι hι => W.smul_mem _ ((hW _).2 (hg ι hι)))
    have hval : (_root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n (tensorCombination (fun ι => (a ι : ℂ)) f)).im = 0 := by
      rw [tensorCombination_eq_sum, extendByZero_sum hF hT _ _ _ hg, Complex.im_sum]
      refine Finset.sum_eq_zero fun ι _ => ?_
      have h := extendByZero_tensorProdComplex hF hσ hT ⟨f ι, (hf ι).1⟩ (hf ι).2
      rw [show _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n (tensorProdComplex (f ι)) = _ from h]
      simp
    have hb := norm_extendByZero_le hT hn
      ((hW _).1 (W.sub_mem ((hW _).2 hφ) ((hW _).2 hFm))) hε.le hclose
    rw [extendByZero_sub hF hT hφ hFm] at hb
    calc |(_root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n φ).im|
        = |(_root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n φ -
            _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n (tensorCombination (fun ι => (a ι : ℂ)) f)).im| := by
          rw [Complex.sub_im, hval, sub_zero]
      _ ≤ ‖_root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n φ - _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n (tensorCombination (fun ι => (a ι : ℂ)) f)‖ :=
          Complex.abs_im_le_norm _
      _ ≤ c n * ε := hb
  exact abs_nonpos_iff.1 hle
theorem conj_apply_eq (hF : Elementary.BasicProperties)
    (hD : TestSpaceFacts.Statement)
    (hσ : IsSepFunctional σ) (hT : IsBoundedExtensionFamily σ T k c) {n : ℕ}
    (hn : 0 < n) (φ : flatSchwartzSet n) :
    ∃ h : (fun x => conj (φ.1 x)) ∈ flatSchwartzSet n, T n ⟨_, h⟩ = conj (T n φ) := by
  obtain ⟨hOps, hOpen, -, -, -⟩ := hF n hn
  obtain ⟨oD, -, -, -, -, -, hflat, -⟩ := hOpen
  have hφ' : φ.1 ∈ {φ | φ ∈ schwartzSet n ∧ VanishesToInfiniteOrderOff φ (distinctLocus n)} :=
    hflat ▸ φ.2
  have hcl := hOps.1 φ.1 hφ'.1 φ.1 hφ'.1 1 1
  have hfl := hcl.2.2 _ oD hφ'.2 hφ'.2
  have mem : ∀ g, g ∈ schwartzSet n → VanishesToInfiniteOrderOff g (distinctLocus n) →
      g ∈ flatSchwartzSet n := fun g h₁ h₂ => by
    rw [hflat]
    exact ⟨h₁, h₂⟩
  have hc : Elementary.conjPointwise φ.1 ∈ flatSchwartzSet n := mem _ hcl.1.2.1 hfl.2.1
  have hr : Elementary.rePart φ.1 ∈ flatSchwartzSet n := mem _ hcl.1.2.2.1 hfl.2.2.1
  have hi : Elementary.imPart φ.1 ∈ flatSchwartzSet n := mem _ hcl.1.2.2.2 hfl.2.2.2
  have e₁ : φ.1 = (1 : ℂ) • Elementary.rePart φ.1 +
      Complex.I • Elementary.imPart φ.1 := by
    funext x
    apply Complex.ext <;> simp [Elementary.rePart, Elementary.imPart]
  have e₂ : Elementary.conjPointwise φ.1 = (1 : ℂ) • Elementary.rePart φ.1 +
      (-Complex.I) • Elementary.imPart φ.1 := by
    funext x
    apply Complex.ext <;>
      simp [Elementary.conjPointwise, Elementary.rePart, Elementary.imPart]
  have v₁ := extendByZero_linear hT hr hi 1 Complex.I (by rw [← e₁]; exact φ.2)
  have v₂ := extendByZero_linear hT hr hi 1 (-Complex.I) (by rw [← e₂]; exact hc)
  rw [← e₁] at v₁
  rw [← e₂] at v₂
  have hRi := im_extendByZero_eq_zero_of_real hF hD hσ hT hn hr fun x => by
    simp [Elementary.rePart]
  have hJi := im_extendByZero_eq_zero_of_real hF hD hσ hT hn hi fun x => by
    simp [Elementary.imPart]
  refine ⟨hc, ?_⟩
  have a₁ : T n ⟨_, hc⟩ = _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n (Elementary.conjPointwise φ.1) :=
    (extendByZero_of_mem hc).symm
  have a₂ : T n φ = _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n φ.1 := (extendByZero_of_mem φ.2).symm
  show T n ⟨Elementary.conjPointwise φ.1, hc⟩ = _
  rw [a₁, v₂, a₂, v₁]
  apply Complex.ext <;> simp [hRi, hJi]
theorem reflectConj_apply_eq (hF : Elementary.BasicProperties) (hTr : DensityTransfer.Statement)
    (hD : TestSpaceFacts.Statement)
    (hO : OperationsStatement) (hσ : IsSepFunctional σ)
    (hT : IsBoundedExtensionFamily σ T k c) {n : ℕ} (hn : 0 < n)
    (φ : flatSchwartzSet n) (hinv : SepTupleInvariant σ n RigidMotion.timeReflection) :
    ∃ h : reflectConj φ.1 ∈ flatSchwartzSet n, T n ⟨_, h⟩ = conj (T n φ) := by
  obtain ⟨hc, hcv⟩ := conj_apply_eq hF hD hσ hT hn φ
  obtain ⟨h₁, h₂⟩ := motion_invariance hTr hO hT hn RigidMotion.timeReflection hinv ⟨_, hc⟩
  have e : reflectConj φ.1 = actOnFun RigidMotion.timeReflection fun x => conj (φ.1 x) :=
    ((hO.1 n (k n) hn (hT.2 n hn).2.1 1 RigidMotion.timeReflection).2.1 φ.1 φ.2.1).1.2.2.2.2
  refine ⟨e ▸ h₁, ?_⟩
  rw [← hcv, ← h₂]
  exact congrArg (T n) (Subtype.ext e)
theorem exists_tensorCombination_close (hD : TestSpaceFacts.Statement)
    {q : ℕ} {a : PointTuple q → ℂ} (ha : IsPositiveTimeTest q a) {K : ℕ} (hK : 0 < K) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (m : ℕ) (b : Fin m → ℂ) (f : Fin m → Fin q → (Fin 4 → ℝ) → ℝ),
      (∀ ι, f ι ∈ disjointSupportTuples upperHalfSpace q ∧
        HasSmoothComponents upperHalfSpace (f ι)) ∧
      weightedSeminorm K (a - tensorCombination b f) ≤ ENNReal.ofReal ε ∧
      (q = 0 → tensorCombination b f = a) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have e : tensorCombination (fun _ : Fin 1 => a 0) (fun _ i => i.elim0) = a := by
      funext x
      have h : a x = a 0 := congrArg a (Subsingleton.elim _ _)
      rw [h]
      simp [tensorCombination, tensorProd]
    refine ⟨1, fun _ => a 0, fun _ i => i.elim0,
      fun _ => ⟨⟨fun i => i.elim0, fun i => i.elim0⟩, hasSmoothComponents_of_fin_zero _ _⟩, ?_,
      fun _ => e⟩
    rw [e, sub_self, weightedSeminorm_of_fin_zero K _ 0]
    simp
  · obtain ⟨m, b, f, -, hf, hw⟩ := ((hD.2.2.2 q K hq hK).2 a (ha hq).1 (ha hq).2 ε hε).1
    exact ⟨m, b, f, hf, hw, fun h => absurd h hq.ne'⟩
theorem norm_sub_pairing_le (hF : Elementary.BasicProperties) (hO : OperationsStatement)
    (hD : TestSpaceFacts.Statement)
    (hT : IsBoundedExtensionFamily σ T k c) {q q' : ℕ} (hp : 0 < q + q')
    {a a' : PointTuple q → ℂ} {b b' : PointTuple q' → ℂ} (ha : IsPositiveTimeTest q a)
    (ha' : IsPositiveTimeTest q a') (hb : IsPositiveTimeTest q' b)
    (hb' : IsPositiveTimeTest q' b') {K : ℕ}
    (hK : 0 < K) (hkK : k (q + q') ≤ K) {cS : ℝ} (hcS : c (q + q') ≤ cS) {ε A : ℝ}
    (hε : 0 ≤ ε) (hA : 0 ≤ A) (h₁ : weightedSeminorm K (a - a') ≤ ENNReal.ofReal ε)
    (h₂ : weightedSeminorm K (b - b') ≤ ENNReal.ofReal ε)
    (h₃ : weightedSeminorm K b ≤ ENNReal.ofReal A)
    (h₄ : weightedSeminorm K a' ≤ ENNReal.ofReal (A + 1)) :
    ‖_root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T (q + q') (tensorFun (reflectConj a) b) -
        _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T (q + q') (tensorFun (reflectConj a') b')‖ ≤ cS * ((2 * A + 1) * ε) := by
  obtain ⟨Wq, hWq⟩ := exists_submodule_positiveTimeTest hF q
  obtain ⟨Wq', hWq'⟩ := exists_submodule_positiveTimeTest hF q'
  obtain ⟨W, hW⟩ := exists_submodule_flatSchwartzSet hF (q + q')
  have had : IsPositiveTimeTest q (a - a') :=
    (hWq _).1 (Wq.sub_mem ((hWq _).2 ha) ((hWq _).2 ha'))
  have hbd : IsPositiveTimeTest q' (b - b') :=
    (hWq' _).1 (Wq'.sub_mem ((hWq' _).2 hb) ((hWq' _).2 hb'))
  obtain ⟨m₁, n₁⟩ := reflectConj_tensorFun_mem_and_le hF hO hD had hb
  obtain ⟨m₂, n₂⟩ := reflectConj_tensorFun_mem_and_le hF hO hD ha' hbd
  have mA := (reflectConj_tensorFun_mem_and_le hF hO hD ha hb).1
  have mB := (reflectConj_tensorFun_mem_and_le hF hO hD ha' hb').1
  have e : tensorFun (reflectConj a) b - tensorFun (reflectConj a') b' =
      tensorFun (reflectConj (a - a')) b + tensorFun (reflectConj a') (b - b') := by
    funext z
    simp only [Pi.sub_apply, Pi.add_apply, tensorFun, reflectConj, map_sub]
    ring
  obtain ⟨-, hk, -, -, -⟩ := hT.2 _ hp
  have hDm : tensorFun (reflectConj (a - a')) b + tensorFun (reflectConj a') (b - b') ∈
      flatSchwartzSet (q + q') := (hW _).1 (W.add_mem ((hW _).2 m₁) ((hW _).2 m₂))
  have hbound : weightedSeminorm (k (q + q'))
      (tensorFun (reflectConj (a - a')) b + tensorFun (reflectConj a') (b - b')) ≤
        ENNReal.ofReal ((2 * A + 1) * ε) := by
    calc _ ≤ weightedSeminorm K
          (tensorFun (reflectConj (a - a')) b + tensorFun (reflectConj a') (b - b')) :=
          (((hF _ hp).1.1 _ hDm.1 _ hDm.1 1 1).2.1 (k (q + q')) K hk hkK).1
      _ ≤ weightedSeminorm K (tensorFun (reflectConj (a - a')) b) +
          weightedSeminorm K (tensorFun (reflectConj a') (b - b')) :=
          weightedSeminorm_add_le hF hp m₁.1 m₂.1 hK
      _ ≤ ENNReal.ofReal ε * ENNReal.ofReal A + ENNReal.ofReal (A + 1) * ENNReal.ofReal ε :=
          add_le_add ((n₁ K hK).trans (mul_le_mul' h₁ h₃)) ((n₂ K hK).trans (mul_le_mul' h₄ h₂))
      _ = ENNReal.ofReal ((2 * A + 1) * ε) := by
          rw [← ENNReal.ofReal_mul hε, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  have hfin := norm_extendByZero_le hT hp hDm (by positivity) hbound
  rw [← e, extendByZero_sub hF hT mA mB] at hfin
  exact hfin.trans (mul_le_mul_of_nonneg_right hcS (by positivity))
theorem pairing_sum_of_tensorCombinations (hF : Elementary.BasicProperties)
    (hO : OperationsStatement)
    (hσ : IsSepFunctional σ) (hT : IsBoundedExtensionFamily σ T k c)
    (hpos : SepTupleReflectionPositive σ) (q₀ : ℕ) (m : Fin (q₀ + 1) → ℕ)
    (b : ∀ q, Fin (m q) → ℂ)
    (f : ∀ q : Fin (q₀ + 1), Fin (m q) → Fin (q : ℕ) → (Fin 4 → ℝ) → ℝ)
    (hf : ∀ (q : Fin (q₀ + 1)) (ι : Fin (m q)), f q ι ∈ disjointSupportTuples upperHalfSpace q ∧
      HasSmoothComponents upperHalfSpace (f q ι)) :
    (∑ q : Fin (q₀ + 1), ∑ q' : Fin (q₀ + 1), _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T ((q : ℕ) + q')
        (tensorFun (reflectConj (tensorCombination (b q) (f q)))
          (tensorCombination (b q') (f q')))).im = 0 ∧
      0 ≤ (∑ q : Fin (q₀ + 1), ∑ q' : Fin (q₀ + 1), _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T ((q : ℕ) + q')
        (tensorFun (reflectConj (tensorCombination (b q) (f q)))
          (tensorCombination (b q') (f q')))).re := by
  have hconc : ∀ (q q' : Fin (q₀ + 1)) (ι : Fin (m q)) (ι' : Fin (m q')),
      concatTuple (reflectTuple (f q ι)) (f q' ι') ∈
          disjointSupportTuples Set.univ ((q : ℕ) + q') ∧
        HasSmoothComponents Set.univ (concatTuple (reflectTuple (f q ι)) (f q' ι')) :=
    fun q q' ι ι' =>
      have h := hO.2 q q' (f q ι) (f q' ι') (hf q ι).1 (hf q ι).2 (hf q' ι').1 (hf q' ι').2
      ⟨h.1, h.2.1⟩
  have hI := hpos (Σ q, Fin (m q)) (fun i => b i.1 i.2)
    (fun i => ⟨i.1, f i.1 i.2, (hf _ _).1⟩)
    (fun i i' => ⟨_, (hconc i.1 i'.1 i.2 i'.2).1⟩) (fun i => (hf _ _).2) (fun _ _ => rfl)
  have hterm : ∀ q q' : Fin (q₀ + 1), _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T ((q : ℕ) + q')
      (tensorFun (reflectConj (tensorCombination (b q) (f q)))
        (tensorCombination (b q') (f q'))) =
      ∑ ι, ∑ ι', conj (b q ι) * b q' ι' *
        (σ ⟨(q : ℕ) + q', ⟨_, (hconc q q' ι ι').1⟩⟩ : ℂ) := by
    intro q q'
    rw [tensorFun_reflectConj_tensorCombination,
      extendByZero_sum hF hT (Finset.univ : Finset (Fin (m q) × Fin (m q')))
        (fun p => conj (b q p.1) * b q' p.2)
        (fun p => tensorProdComplex (concatTuple (reflectTuple (f q p.1)) (f q' p.2)))
        (fun p _ => tensorProdComplex_mem_flatSchwartzSet hF (hconc q q' p.1 p.2).1
          (hconc q q' p.1 p.2).2),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ι _ => Finset.sum_congr rfl fun ι' _ => ?_
    exact congrArg _
      (extendByZero_tensorProdComplex hF hσ hT ⟨_, (hconc q q' ι ι').1⟩ (hconc q q' ι ι').2)
  have hz : (∑ q : Fin (q₀ + 1), ∑ q' : Fin (q₀ + 1), _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T ((q : ℕ) + q')
      (tensorFun (reflectConj (tensorCombination (b q) (f q)))
        (tensorCombination (b q') (f q')))) =
      ∑ i : (Σ q, Fin (m q)), ∑ i' : (Σ q, Fin (m q)), conj (b i.1 i.2) * b i'.1 i'.2 *
        (σ ⟨(i.1 : ℕ) + i'.1, ⟨_, (hconc i.1 i'.1 i.2 i'.2).1⟩⟩ : ℂ) := by
    simp only [Fintype.sum_sigma, hterm]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_comm
  rw [hz]
  exact hI
theorem reflection_positive (hF : Elementary.BasicProperties)
    (hO : OperationsStatement)
    (hD : TestSpaceFacts.Statement)
    (hσ : IsSepFunctional σ) (hT : IsBoundedExtensionFamily σ T k c)
    (hpos : SepTupleReflectionPositive σ) (q₀ : ℕ) (hq₀ : 1 ≤ q₀)
    (φ : (q : ℕ) → PointTuple q → ℂ) (hφ : IsPositiveTimeFlatFamily q₀ φ) :
    ∃ h : ∀ q q' : Fin (q₀ + 1), tensorFun (reflectConj (φ q)) (φ q') ∈
        flatSchwartzSet ((q : ℕ) + q'),
      (∑ q : Fin (q₀ + 1), ∑ q' : Fin (q₀ + 1), T ((q : ℕ) + q') ⟨_, h q q'⟩).im = 0 ∧
        0 ≤ (∑ q : Fin (q₀ + 1), ∑ q' : Fin (q₀ + 1), T ((q : ℕ) + q') ⟨_, h q q'⟩).re := by
  have hadm : ∀ q : Fin (q₀ + 1), IsPositiveTimeTest q (φ q) :=
    fun q hq => hφ (q : ℕ) hq (Nat.lt_succ_iff.1 q.2)
  have hmem := fun q q' : Fin (q₀ + 1) =>
    (reflectConj_tensorFun_mem_and_le hF hO hD (hadm q) (hadm q')).1
  refine ⟨hmem, ?_⟩
  have hsum : (∑ q : Fin (q₀ + 1), ∑ q' : Fin (q₀ + 1), T ((q : ℕ) + q') ⟨_, hmem q q'⟩) =
      ∑ q : Fin (q₀ + 1), ∑ q' : Fin (q₀ + 1), _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T ((q : ℕ) + q')
        (tensorFun (reflectConj (φ q)) (φ q')) :=
    Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ =>
      (extendByZero_of_mem (hmem q q')).symm
  rw [hsum]
  obtain ⟨K, hK, hkK⟩ : ∃ K : ℕ, 0 < K ∧ ∀ p, 1 ≤ p → p ≤ 2 * q₀ → k p ≤ K := by
    have hle : ∀ p, 1 ≤ p → p ≤ 2 * q₀ → k p ≤ ∑ p ∈ Finset.Icc 1 (2 * q₀), k p :=
      fun p h₁ h₂ => Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _)
        (Finset.mem_Icc.2 ⟨h₁, h₂⟩)
    exact ⟨_, lt_of_lt_of_le (hT.2 1 le_rfl).2.1 (hle 1 le_rfl (by omega)), hle⟩
  obtain ⟨cS, hcS₀, hcS⟩ : ∃ cS : ℝ, 0 ≤ cS ∧ ∀ p, 1 ≤ p → p ≤ 2 * q₀ → c p ≤ cS := by
    have hnn : ∀ i ∈ Finset.Icc 1 (2 * q₀), 0 ≤ c i :=
      fun i hi => (hT.2 i (Finset.mem_Icc.1 hi).1).2.2.1
    exact ⟨_, Finset.sum_nonneg hnn, fun p h₁ h₂ =>
      Finset.single_le_sum (f := c) hnn (Finset.mem_Icc.2 ⟨h₁, h₂⟩)⟩
  obtain ⟨A, hA₀, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧
      ∀ q : Fin (q₀ + 1), weightedSeminorm K (φ q) ≤ ENNReal.ofReal A := by
    refine ⟨∑ q : Fin (q₀ + 1), (weightedSeminorm K (φ q)).toReal,
      Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg, fun q => ?_⟩
    calc weightedSeminorm K (φ q) = ENNReal.ofReal (weightedSeminorm K (φ q)).toReal :=
          (ENNReal.ofReal_toReal ((hadm q).weightedSeminorm_ne_top hK)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (Finset.single_le_sum
          (f := fun q : Fin (q₀ + 1) => (weightedSeminorm K (φ q)).toReal)
          (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ q))
  obtain ⟨S, hS⟩ : ∃ S : ℂ, S = ∑ q : Fin (q₀ + 1), ∑ q' : Fin (q₀ + 1),
      _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T ((q : ℕ) + q') (tensorFun (reflectConj (φ q)) (φ q')) := ⟨_, rfl⟩
  rw [← hS]
  have hC : 0 ≤ ((q₀ : ℝ) + 1) ^ 2 * (cS * (2 * A + 1)) := by positivity
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ z : ℂ, z.im = 0 ∧ 0 ≤ z.re ∧
      ‖S - z‖ ≤ ((q₀ : ℝ) + 1) ^ 2 * (cS * (2 * A + 1)) * ε := by
    intro ε hε hε₁
    choose m b f hf hclose hzero using fun q : Fin (q₀ + 1) =>
      exists_tensorCombination_close hD (hadm q) hK hε
    obtain ⟨hzi, hzr⟩ := pairing_sum_of_tensorCombinations hF hO hσ hT hpos q₀ m b f hf
    obtain ⟨G, hG⟩ : ∃ G : ∀ q : Fin (q₀ + 1), PointTuple q → ℂ,
        ∀ q, G q = tensorCombination (b q) (f q) := ⟨_, fun _ => rfl⟩
    simp only [← hG] at hzi hzr hclose hzero
    have hGadm : ∀ q : Fin (q₀ + 1), IsPositiveTimeTest q (G q) := by
      intro q
      obtain ⟨W, hW⟩ := exists_submodule_positiveTimeTest hF q
      rw [hG, tensorCombination_eq_sum]
      exact (hW _).1 (W.sum_mem fun ι _ => W.smul_mem _
        ((hW _).2 (tensorProdComplex_positiveTimeTest hF (hf q ι).1 (hf q ι).2)))
    have hGn : ∀ q : Fin (q₀ + 1), weightedSeminorm K (G q) ≤ ENNReal.ofReal (A + 1) :=
      fun q => weightedSeminorm_le_add_one_of_close hF (hadm q) (hGadm q) hK hA₀ hε.le hε₁
        (hA q) (hclose q)
    have hterm : ∀ q q' : Fin (q₀ + 1),
        ‖_root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T ((q : ℕ) + q') (tensorFun (reflectConj (φ q)) (φ q')) -
          _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T ((q : ℕ) + q') (tensorFun (reflectConj (G q)) (G q'))‖ ≤
        cS * ((2 * A + 1) * ε) := by
      intro q q'
      rcases Nat.eq_zero_or_pos ((q : ℕ) + q') with h0 | hp
      · rw [hzero q (by omega), hzero q' (by omega), sub_self, norm_zero]
        positivity
      · have hle : (q : ℕ) + q' ≤ 2 * q₀ := by
          have := q.2
          have := q'.2
          omega
        exact norm_sub_pairing_le hF hO hD hT hp (hadm q) (hGadm q) (hadm q') (hGadm q') hK
          (hkK _ hp hle) (hcS _ hp hle) hε.le hA₀ (hclose q) (hclose q') (hA q') (hGn q)
    refine ⟨_, hzi, hzr, ?_⟩
    rw [hS, ← Finset.sum_sub_distrib]
    simp only [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ q : Fin (q₀ + 1), ‖∑ q' : Fin (q₀ + 1),
            (_root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T ((q : ℕ) + q') (tensorFun (reflectConj (φ q)) (φ q')) -
              _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T ((q : ℕ) + q') (tensorFun (reflectConj (G q)) (G q')))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _q : Fin (q₀ + 1), ∑ _q' : Fin (q₀ + 1), cS * ((2 * A + 1) * ε) :=
          Finset.sum_le_sum fun q _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun q' _ => hterm q q')
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hle₁ : |S.im| ≤ 0 := nonpos_of_le_const_mul_forall hC fun ε hε h₁ => by
    obtain ⟨z, hzi, -, hz⟩ := key ε hε h₁
    calc |S.im| = |(S - z).im| := by rw [Complex.sub_im, hzi, sub_zero]
      _ ≤ ‖S - z‖ := Complex.abs_im_le_norm _
      _ ≤ _ := hz
  have hle₂ : -S.re ≤ 0 := nonpos_of_le_const_mul_forall hC fun ε hε h₁ => by
    obtain ⟨z, -, hzr, hz⟩ := key ε hε h₁
    have h := (abs_le.1 (Complex.abs_re_le_norm (S - z))).1
    rw [Complex.sub_re] at h
    linarith
  exact ⟨abs_nonpos_iff.1 hle₁, by linarith⟩
end Functionals
theorem schwingerPropertiesTransfer_holds (hF : Elementary.BasicProperties)
    (hTr : DensityTransfer.Statement)
    (hD : TestSpaceFacts.Statement)
    (hO : OperationsStatement) :
    SchwingerPropertiesTransfer := by
  intro σ T k c hσ hT
  refine ⟨⟨fun n hn => ?_, hT.1⟩, fun n hn φ => ⟨fun r hr => motion_invariance hTr hO hT hn r hr φ,
    fun hs ς => permutation_invariance hTr hO hT hn hs ς φ, fun hre => ?_,
    conj_apply_eq hF hD hσ hT hn φ, reflectConj_apply_eq hF hTr hD hO hσ hT hn φ⟩,
    fun hpos q₀ φ hq₀ hφ => reflection_positive hF hO hD hσ hT hpos q₀ hq₀ φ hφ⟩
  · obtain ⟨hl, hk, hc, hb, ht⟩ := hT.2 n hn
    exact ⟨hl, ⟨k n, c n, hk, hc, hb⟩, ht⟩
  · have e : _root_.YangMills.Construction.TestSpaces.SchwartzPassage.extendByZero T n φ.1 = T n φ := extendByZero_of_mem φ.2
    rw [← e]
    exact im_extendByZero_eq_zero_of_real hF hD hσ hT hn φ.2 hre
end YangMills.Construction.TestSpaces.SchwartzPassage
