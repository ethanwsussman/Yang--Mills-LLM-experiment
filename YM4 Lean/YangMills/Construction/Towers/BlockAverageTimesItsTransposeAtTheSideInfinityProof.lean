import YangMills.Construction.Towers.AveragingPolydiscRadiusExists
import YangMills.Construction.Towers.BlockAverageTimesItsTransposeAtTheSideInfinity
import YangMills.Construction.Towers.LinearMapsOnTheRealSpacesProof
import YangMills.Construction.Towers.RelationsOfTheCovariantIteratesOnTheSidesProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.CubeAverageMulTranspose
open YangMills.Construction.Matrices
section Blocks
variable {X Y : Type} (B : Y → Set X) (W : Y → X → ComplexMatrix2) (w : ℂ)
theorem mem_complexSubmodule_iff {Z : Type} {f : Z → ComplexMatrix2} :
    f ∈ (pairedFunctions Z).complexSubmodule ↔ ∀ z, f z ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.IterRelationsProof.mem_complexSubmodule_iff <;> assumption
def valFn {Z : Type} (f : (pairedFunctions Z).complexSubmodule) : Z → ComplexMatrix2 := f.val
def ofFn {Z : Type} (f : Z → ComplexMatrix2) (h : ∀ z, f z ∈ ComplexMatrix2.traceless) :
    (pairedFunctions Z).complexSubmodule :=
  ⟨f, mem_complexSubmodule_iff.2 h⟩
theorem valFn_mem_traceless {Z : Type} (f : (pairedFunctions Z).complexSubmodule) (z : Z) :
    valFn f z ∈ ComplexMatrix2.traceless :=
  mem_complexSubmodule_iff.1 f.property z
theorem ext_valFn {Z : Type} {f f' : (pairedFunctions Z).complexSubmodule}
    (h : ∀ z, valFn f z = valFn f' z) : f = f' :=
  Subtype.ext (funext h)
def weightedConjSum (l : X → ComplexMatrix2) : Y → ComplexMatrix2 :=
  fun y => w • ∑ᶠ x ∈ B y, ComplexMatrix2.conjugateBy (W y x) (l x)
variable {B}
theorem weightedConjSum_eq_finsetSum (hfin : ∀ y, (B y).Finite) (l : X → ComplexMatrix2) (y : Y) :
    weightedConjSum B W w l y =
      w • ∑ x ∈ (hfin y).toFinset, ComplexMatrix2.conjugateBy (W y x) (l x) := by
  unfold weightedConjSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
def weightedConjSumLinear (hfin : ∀ y, (B y).Finite) :
    (pairedFunctions X).complexSubmodule →ₗ[ℂ] (pairedFunctions Y).complexSubmodule where
  toFun l := ofFn (weightedConjSum B W w (valFn l)) fun y => by
    rw [weightedConjSum_eq_finsetSum W w hfin]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun x _ => ?_)
    exact ComplexMatrix2.conjugateByLinear_mem_traceless _ _ (valFn_mem_traceless l x)
  map_add' l l' := by
    refine ext_valFn fun y => ?_
    change weightedConjSum B W w (valFn l + valFn l') y =
      weightedConjSum B W w (valFn l) y + weightedConjSum B W w (valFn l') y
    simp only [weightedConjSum_eq_finsetSum W w hfin, ← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    exact map_add (ComplexMatrix2.conjugateByLinear (W y x)) (valFn l x) (valFn l' x)
  map_smul' c l := by
    refine ext_valFn fun y => ?_
    change weightedConjSum B W w (c • valFn l) y = c • weightedConjSum B W w (valFn l) y
    simp only [weightedConjSum_eq_finsetSum W w hfin]
    rw [smul_comm c w]
    refine congrArg (fun M : ComplexMatrix2 => w • M) ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact (ComplexMatrix2.conjugateByLinear (W y x)).map_smul c (valFn l x)
variable {Yof : X → Y}
theorem weightedConjSum_eq_sum_filter (hfin : ∀ y, (B y).Finite)
    (hY : ∀ y x, x ∈ B y ↔ Yof x = y)
    [DecidableEq Y] {f : X → ComplexMatrix2} {s : Finset X} (hs : ∀ x, x ∉ s → f x = 0) (y : Y) :
    weightedConjSum B W w f y =
      w • ∑ x ∈ s with Yof x = y, ComplexMatrix2.conjugateBy (W y x) (f x) := by
  rw [weightedConjSum_eq_finsetSum W w hfin]
  congr 1
  symm
  refine Finset.sum_subset (fun x hx => ?_) fun x hx hx' => ?_
  · exact (hfin y).mem_toFinset.2 ((hY y x).2 (Finset.mem_filter.1 hx).2)
  · have hxs : x ∉ s := fun h => hx' (Finset.mem_filter.2
      ⟨h, (hY y x).1 ((hfin y).mem_toFinset.1 hx)⟩)
    rw [hs x hxs]
    exact map_zero (ComplexMatrix2.conjugateByLinear (W y x))
def inverseConj (Yof : X → Y) (g : Y → ComplexMatrix2) : X → ComplexMatrix2 :=
  fun x => w • ((W (Yof x) x)⁻¹ * g (Yof x) * W (Yof x) x)
def inverseConjLinear (Yof : X → Y) (hunit : ∀ x, IsUnit (W (Yof x) x).det) :
    (pairedFunctions Y).complexSubmodule →ₗ[ℂ] (pairedFunctions X).complexSubmodule where
  toFun g := ofFn (inverseConj W w Yof (valFn g)) fun x => by
    refine Submodule.smul_mem _ _ ?_
    change Matrix.trace _ = 0
    have hg : Matrix.trace (valFn g (Yof x)) = 0 := valFn_mem_traceless g (Yof x)
    rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.mul_nonsing_inv _ (hunit x), one_mul, hg]
  map_add' g g' := by
    refine ext_valFn fun x => ?_
    change w • ((W (Yof x) x)⁻¹ * (valFn g (Yof x) + valFn g' (Yof x)) * W (Yof x) x) =
      inverseConj W w Yof (valFn g) x + inverseConj W w Yof (valFn g') x
    simp only [inverseConj, mul_add, add_mul, smul_add]
  map_smul' c g := by
    refine ext_valFn fun x => ?_
    change w • ((W (Yof x) x)⁻¹ * (c • valFn g (Yof x)) * W (Yof x) x) =
      c • inverseConj W w Yof (valFn g) x
    simp only [inverseConj, mul_smul_comm, smul_mul_assoc]
    rw [smul_comm]
theorem pair_inverseConj (hfin : ∀ y, (B y).Finite) (hY : ∀ y x, x ∈ B y ↔ Yof x = y)
    (g : Y → ComplexMatrix2) {f : X → ComplexMatrix2} (hf : HasFiniteSupp f) :
    traceFinsumPairing (inverseConj W w Yof g) f = traceFinsumPairing g (weightedConjSum B W w f) := by
  classical
  set s : Finset X := Set.Finite.toFinset hf with hsdef
  have hs : ∀ x, x ∉ s → f x = 0 := fun x hx => by
    by_contra h
    exact hx (hf.mem_toFinset.2 h)
  have hval := fun y => weightedConjSum_eq_sum_filter W w hfin hY hs y
  have h1 : traceFinsumPairing (inverseConj W w Yof g) f =
      ∑ x ∈ s, ComplexMatrix2.halfTrace (inverseConj W w Yof g x * f x) := by
    refine finsum_eq_sum_of_support_subset _ fun x hx => ?_
    by_contra h
    apply hx
    change ComplexMatrix2.halfTrace (inverseConj W w Yof g x * f x) = 0
    rw [hs x h]
    simp
  have h2 : traceFinsumPairing g (weightedConjSum B W w f) =
      ∑ y ∈ s.image Yof, ComplexMatrix2.halfTrace (g y * weightedConjSum B W w f y) := by
    refine finsum_eq_sum_of_support_subset _ fun y hy => ?_
    by_contra h
    apply hy
    change ComplexMatrix2.halfTrace (g y * weightedConjSum B W w f y) = 0
    have hem : (s.filter fun x => Yof x = y) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun x hx hxy => h ?_
      exact Finset.coe_image (f := Yof) ▸ ⟨x, hx, hxy⟩
    rw [hval y, hem]
    simp
  rw [h1, h2, ← Finset.sum_fiberwise_of_maps_to (t := s.image Yof)
    (fun x hx => Finset.mem_image_of_mem Yof hx)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hval y, mul_smul_comm, Finset.mul_sum]
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_smul,
    Matrix.trace_sum, smul_eq_mul, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxy : Yof x = y := (Finset.mem_filter.1 hx).2
  subst hxy
  simp only [inverseConj, ComplexMatrix2.conjugateBy, smul_mul_assoc, Matrix.trace_smul,
    smul_eq_mul]
  have : Matrix.trace ((W (Yof x) x)⁻¹ * g (Yof x) * W (Yof x) x * f x) =
      Matrix.trace (g (Yof x) * (W (Yof x) x * f x * (W (Yof x) x)⁻¹)) := by
    rw [mul_assoc, mul_assoc, Matrix.trace_mul_comm]
    simp only [mul_assoc]
  rw [this]
def singleSite [DecidableEq X] (x₀ : X) (A : ComplexMatrix2) (hA : A ∈ ComplexMatrix2.traceless) :
    (pairedFunctions X).complexSubmodule :=
  ofFn (Pi.single x₀ A) fun x => by
    by_cases h : x = x₀
    · subst h
      simpa using hA
    · simp [Pi.single_eq_of_ne h]
theorem pair_single [DecidableEq X] (h : X → ComplexMatrix2) (x₀ : X) (A : ComplexMatrix2) :
    traceFinsumPairing h (Pi.single x₀ A : X → ComplexMatrix2) =
      ComplexMatrix2.halfTrace (h x₀ * A) := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.traceFinsumPairing_single <;> assumption
theorem eq_of_pair_eq {f f' : (pairedFunctions X).complexSubmodule}
    (h : ∀ e : (pairedFunctions X).complexSubmodule, HasFiniteSupp (valFn e) →
      traceFinsumPairing (valFn f) (valFn e) = traceFinsumPairing (valFn f') (valFn e)) :
    f = f' := by
  classical
  refine ext_valFn fun x₀ => ?_
  have hD : valFn f x₀ - valFn f' x₀ ∈ ComplexMatrix2.traceless :=
    Submodule.sub_mem _ (valFn_mem_traceless f x₀) (valFn_mem_traceless f' x₀)
  set D : ComplexMatrix2 := valFn f x₀ - valFn f' x₀ with hDdef
  have hA : D.conjTranspose ∈ ComplexMatrix2.traceless := by
    change Matrix.trace _ = 0
    have hD' : Matrix.trace D = 0 := hD
    rw [Matrix.trace_conjTranspose, hD', star_zero]
  have hfs : HasFiniteSupp (valFn (singleSite x₀ D.conjTranspose hA)) := by
    change (Function.support (Pi.single x₀ D.conjTranspose : X → ComplexMatrix2)).Finite
    exact (finite_singleton x₀).subset Pi.support_single_subset
  have he := h _ hfs
  change traceFinsumPairing (valFn f) (Pi.single x₀ D.conjTranspose) =
    traceFinsumPairing (valFn f') (Pi.single x₀ D.conjTranspose) at he
  rw [pair_single, pair_single] at he
  have htr : Matrix.trace (D * D.conjTranspose) = 0 := by
    have h2 : Matrix.trace (valFn f x₀ * D.conjTranspose) =
        Matrix.trace (valFn f' x₀ * D.conjTranspose) := by
      simpa [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace] using he
    rw [hDdef, sub_mul, Matrix.trace_sub, ← hDdef, h2, sub_self]
  have hz : D = 0 := Matrix.trace_mul_conjTranspose_self_eq_zero_iff.1 htr
  exact sub_eq_zero.1 hz
theorem exists_weightedConjSum_linear (hfin : ∀ y, (B y).Finite) (hsort : ∀ x, ∃! y, x ∈ B y)
    {N : ℕ} (hcard : ∀ y, (B y).ncard = N) (hw : w * N = 1)
    (hunit : ∀ y, ∀ x ∈ B y, IsUnit (W y x).det) :
    ∃ T : (pairedFunctions X).complexSubmodule →ₗ[ℂ] (pairedFunctions Y).complexSubmodule,
      (∀ l : (pairedFunctions X).complexSubmodule, valFn (T l) = weightedConjSum B W w (valFn l)) ∧
      PairedFunctionSpace.PreservesFiniteSupport T ∧
      ∀ g : (pairedFunctions Y).complexSubmodule,
        valFn (T (PairedFunctionSpace.transposeMap T g)) = w • valFn g := by
  classical
  choose Yof hYof hYuniq using hsort
  have hY : ∀ y x, x ∈ B y ↔ Yof x = y :=
    fun y x => ⟨fun h => (hYuniq x y h).symm, fun h => h ▸ hYof x⟩
  have hunit' : ∀ x, IsUnit (W (Yof x) x).det := fun x => hunit _ x (hYof x)
  set T := weightedConjSumLinear W w hfin with hT
  set T' := inverseConjLinear W w Yof hunit' with hT'
  have hIs : PairedFunctionSpace.IsTransposeMap T T' := fun g f hf =>
    pair_inverseConj W w hfin hY (valFn g) hf
  have hspec : PairedFunctionSpace.IsTransposeMap T (PairedFunctionSpace.transposeMap T) :=
    Classical.epsilon_spec (p := PairedFunctionSpace.IsTransposeMap T) ⟨T', hIs⟩
  have htr : ∀ g, PairedFunctionSpace.transposeMap T g = T' g := fun g =>
    eq_of_pair_eq fun e he => (hspec g e he).trans (hIs g e he).symm
  refine ⟨T, fun _ => rfl, fun f hf => ?_, fun g => ?_⟩
  · have hf' : (Function.support (valFn f)).Finite := hf
    change (Function.support (valFn (T f))).Finite
    refine (hf'.image Yof).subset fun y hy => ?_
    by_contra h
    apply hy
    have hs : ∀ x, x ∉ hf'.toFinset → valFn f x = 0 := fun x hx => by
      by_contra h'
      exact hx (hf'.mem_toFinset.2 h')
    change weightedConjSum B W w (valFn f) y = 0
    rw [weightedConjSum_eq_sum_filter W w hfin hY hs y]
    have hem : (hf'.toFinset.filter fun x => Yof x = y) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun x hx hxy => h ⟨x, hf'.mem_toFinset.1 hx, hxy⟩
    rw [hem]
    simp
  · rw [htr g]
    refine funext fun y : Y => ?_
    change weightedConjSum B W w (inverseConj W w Yof (valFn g)) y = w • valFn g y
    rw [weightedConjSum_eq_finsetSum W w hfin]
    have hterm : ∀ x ∈ (hfin y).toFinset,
        ComplexMatrix2.conjugateBy (W y x) (inverseConj W w Yof (valFn g) x) = w • valFn g y :=
      fun x hx => by
      have hx' : x ∈ B y := (hfin y).mem_toFinset.1 hx
      have hxy : Yof x = y := (hY y x).1 hx'
      have hu : IsUnit (W y x).det := hunit y x hx'
      simp only [inverseConj, ComplexMatrix2.conjugateBy, hxy]
      rw [mul_smul_comm, smul_mul_assoc]
      congr 1
      calc W y x * ((W y x)⁻¹ * valFn g y * W y x) * (W y x)⁻¹
          = (W y x * (W y x)⁻¹) * valFn g y * (W y x * (W y x)⁻¹) := by
            simp only [mul_assoc]
        _ = valFn g y := by
            rw [Matrix.mul_nonsing_inv _ hu, one_mul, mul_one]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, ← Set.ncard_eq_toFinset_card _ (hfin y),
      hcard y, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    rw [hw, one_mul]
end Blocks
theorem isUnit_det_of_operatorNorm_sub_one_lt {A : ComplexMatrix2}
    (h : ComplexMatrix2.operatorNorm (A - 1) < 1) : IsUnit A.det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  have h' : ‖(1 : ComplexMatrix2) - A‖ < 1 := by rwa [norm_sub_rev]
  simpa using (Units.oneSub ((1 : ComplexMatrix2) - A) h').isUnit
end YangMills.Construction.Tower.FullSpace.CubeAverageMulTranspose
namespace YangMills.Construction.Tower.FullSpace
open CubeAverageMulTranspose in
theorem CubeAverageMulTranspose.holds (hZ : BlockStructure)
    (hρ : AdmissiblePolydiscRadiusExists) : CubeAverageMulTranspose.Statement := by
  intro L hL k j hj V hV
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hrad : IsAdmissiblePolydiscRadius L (polydiscRadius L) :=
    Classical.epsilon_spec (hρ L hL)
  have hblocks := hZ L k (j + 1) hL (by omega) (by omega) hj
  have hdisp : ∀ y : Vertex L k (j + 1), BlockEqOffsetImage L k (j + 1) y := hblocks.2.1
  have hsortB : ∀ x : Vertex L k j, ∃! y : Vertex L k (j + 1),
      (x : InfiniteLattice.AmbientSpace) ∈ cube L (meshAt L k j) y := hblocks.2.2.1.2.1
  have hcardB : ∀ y : Vertex L k (j + 1),
      (cube L (meshAt L k j) y).ncard = L ^ 4 := fun y => (hdisp y).2.2.1
  have hsubB : ∀ y : Vertex L k (j + 1), cube L (meshAt L k j) y ⊆
      (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set InfiniteLattice.AmbientSpace) :=
    fun y => (hdisp y).2.2.2
  have himage : ∀ y : Vertex L k (j + 1),
      Subtype.val '' (cubeVertices L (meshAt L k j) y) =
        cube L (meshAt L k j) y := fun y => by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      exact ⟨⟨p, hsubB y hp⟩, hp, rfl⟩
  have hcard : ∀ y : Vertex L k (j + 1),
      (cubeVertices L (meshAt L k j) y).ncard = L ^ 4 := fun y => by
    rw [← hcardB y, ← himage y, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hfin : ∀ y : Vertex L k (j + 1), (cubeVertices L (meshAt L k j) y).Finite := by
    intro y
    have hpos : 0 < (cubeVertices L (meshAt L k j) y).ncard := by
      rw [hcard y]
      positivity
    exact Set.finite_of_ncard_pos hpos
  have hunit : ∀ y : Vertex L k (j + 1), ∀ x ∈ cubeVertices L (meshAt L k j) y,
      IsUnit (complexContourMean L V y x).det := by
    intro y x hx
    let c : Edge L k (j + 1) := InfiniteLattice.Link.forwardFrom y 0
    have hc : c.IsPositivelyOriented := ⟨0, by simp [c, InfiniteLattice.Link.forwardFrom]⟩
    have hP : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c :=
      ⟨⟨fun b _ => hV.1.1 b, fun b _ => hV.1.2 b⟩, fun b _ => hV.2 b⟩
    have hs := (hrad.fullSpace k j hj c hc).contourMean_near_one V hP y (Or.inl rfl) x hx
    exact isUnit_det_of_operatorNorm_sub_one_lt (hs.trans (by norm_num))
  have hw : PeriodicLattice.inverseFourthPowerWeight L * ((L ^ 4 : ℕ) : ℂ) = 1 := by
    have hne : (L : ℝ) ≠ 0 := by exact_mod_cast hL0.ne'
    have hr : (L : ℝ) ^ (-4 : ℤ) * (L : ℝ) ^ 4 = 1 := by
      rw [zpow_neg]
      field_simp
    unfold PeriodicLattice.inverseFourthPowerWeight
    have := congrArg (fun r : ℝ => (r : ℂ)) hr
    simpa using this
  exact exists_weightedConjSum_linear (B := cubeVertices L (meshAt L k j))
    (complexContourMean L V) (PeriodicLattice.inverseFourthPowerWeight L) hfin hsortB hcard hw hunit
end YangMills.Construction.Tower.FullSpace
end
