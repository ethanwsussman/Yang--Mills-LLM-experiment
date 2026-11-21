import YangMills.Construction.ClusterExpansion.PolymerSystemOfARegion
import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.Towers.BlocksOfATower
import YangMills.Construction.Towers.ComplexAverageLiesInTheComplexGroup
import YangMills.Construction.Towers.ProductOfTheBlockAverageWithItsTransposeOnTheSides
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices
namespace CubeAverageTranspose
theorem eq_of_halfTrace_mul_eq {A A' : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.traceless)
    (hA' : A' ∈ ComplexMatrix2.traceless)
    (h : ∀ C ∈ ComplexMatrix2.traceless,
      ComplexMatrix2.halfTrace (A * C) = ComplexMatrix2.halfTrace (A' * C)) :
    A = A' := by
  have t : A 0 0 + A 1 1 = 0 := by
    have : ComplexMatrix2.fullTrace A = 0 := hA
    simpa [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] using this
  have t' : A' 0 0 + A' 1 1 = 0 := by
    have : ComplexMatrix2.fullTrace A' = 0 := hA'
    simpa [ComplexMatrix2.fullTrace, Matrix.trace_fin_two] using this
  have e₁ := h !![0, 1; 0, 0]
    (by simp [ComplexMatrix2.traceless, ComplexMatrix2.fullTrace, Matrix.trace_fin_two])
  have e₂ := h !![0, 0; 1, 0]
    (by simp [ComplexMatrix2.traceless, ComplexMatrix2.fullTrace, Matrix.trace_fin_two])
  have e₃ := h !![1, 0; 0, -1]
    (by simp [ComplexMatrix2.traceless, ComplexMatrix2.fullTrace, Matrix.trace_fin_two])
  simp [ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    at e₁ e₂ e₃
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination e₃ / 2 + (t - t') / 2
  · exact e₂
  · exact e₁
  · linear_combination (t - t') / 2 - e₃ / 2
theorem fullTrace_conjugateBy {U : ComplexMatrix2} (hU : U.det ≠ 0) (A : ComplexMatrix2) :
    ComplexMatrix2.fullTrace (ComplexMatrix2.conjugateBy U A) = ComplexMatrix2.fullTrace A := by
  have hu : IsUnit U.det := isUnit_iff_ne_zero.mpr hU
  simp only [ComplexMatrix2.fullTrace, ComplexMatrix2.conjugateBy]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
theorem fullTrace_inv_mul_mul {U : ComplexMatrix2} (hU : U.det ≠ 0) (A : ComplexMatrix2) :
    ComplexMatrix2.fullTrace (U⁻¹ * A * U) = ComplexMatrix2.fullTrace A := by
  have hu : IsUnit U.det := isUnit_iff_ne_zero.mpr hU
  simp only [ComplexMatrix2.fullTrace]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
theorem conjugateBy_inv_mul_mul {U : ComplexMatrix2} (hU : U.det ≠ 0) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy U (U⁻¹ * A * U) = A := by
  have hu : IsUnit U.det := isUnit_iff_ne_zero.mpr hU
  simp only [ComplexMatrix2.conjugateBy]
  calc U * (U⁻¹ * A * U) * U⁻¹ = (U * U⁻¹) * A * (U * U⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = A := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]
theorem fullTrace_inv_mul_mul_mul (U A C : ComplexMatrix2) :
    ComplexMatrix2.fullTrace ((U⁻¹ * A * U) * C) =
      ComplexMatrix2.fullTrace (A * ComplexMatrix2.conjugateBy U C) := by
  simp only [ComplexMatrix2.fullTrace, ComplexMatrix2.conjugateBy]
  calc Matrix.trace (U⁻¹ * A * U * C) = Matrix.trace (U⁻¹ * (A * (U * C))) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (A * (U * C) * U⁻¹) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (A * (U * C * U⁻¹)) := by simp only [Matrix.mul_assoc]
theorem conjugateBy_add (U A C : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy U (A + C) =
      ComplexMatrix2.conjugateBy U A + ComplexMatrix2.conjugateBy U C := by
  simp only [ComplexMatrix2.conjugateBy, Matrix.mul_add, Matrix.add_mul]
theorem conjugateBy_smul (U : ComplexMatrix2) (c : ℂ) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy U (c • A) = c • ComplexMatrix2.conjugateBy U A := by apply _root_.YangMills.Construction.LieInnerProductProof.conjugateBy_smul <;> assumption
section Finite
variable {X Y : Type} [Finite X] [Finite Y]
abbrev tracelessOn (Z : Type) : Submodule ℂ (Z → ComplexMatrix2) :=
  GroupLieProduct.tracelessFunctions Z
theorem mem_tracelessOn {Z : Type} {f : Z → ComplexMatrix2} :
    f ∈ tracelessOn Z ↔ ∀ z, f z ∈ ComplexMatrix2.traceless := by
  simp [GroupLieProduct.tracelessFunctions, Submodule.mem_pi]
theorem eq_of_traceFinsumPairing_eq {R R' : X → ComplexMatrix2} (hR : R ∈ tracelessOn X)
    (hR' : R' ∈ tracelessOn X)
    (h : ∀ f ∈ tracelessOn X, traceFinsumPairing R f = traceFinsumPairing R' f) : R = R' := by
  classical
  cases nonempty_fintype X
  funext x
  refine eq_of_halfTrace_mul_eq (mem_tracelessOn.mp hR x) (mem_tracelessOn.mp hR' x)
    fun C hC => ?_
  have hf : (Pi.single x C : X → ComplexMatrix2) ∈ tracelessOn X := by
    refine mem_tracelessOn.mpr fun z => ?_
    by_cases hz : z = x
    · subst hz; simpa using hC
    · simp [Pi.single_eq_of_ne hz]
  have hsingle : ∀ u : X → ComplexMatrix2,
      traceFinsumPairing u (Pi.single x C : X → ComplexMatrix2) =
        ComplexMatrix2.halfTrace (u x * C) := by
    intro u
    simp only [traceFinsumPairing, finsum_eq_sum_of_fintype]
    rw [Finset.sum_eq_single x]
    · simp
    · intro z _ hz
      simp [Pi.single_eq_of_ne hz, ComplexMatrix2.fullTrace]
    · simp
  have e := h _ hf
  rwa [hsingle, hsingle] at e
def weightedConjugateMean (B : Y → Set X) (w : ℂ) (U : Y → X → ComplexMatrix2)
    (l : X → ComplexMatrix2) : Y → ComplexMatrix2 :=
  fun y => w • ∑ᶠ x ∈ B y, ComplexMatrix2.conjugateBy (U y x) (l x)
theorem exists_linear_weightedConjugateMean_and_transpose (B : Y → Set X) (w : ℂ)
    (U : Y → X → ComplexMatrix2)
    (hB : ∀ x, ∃! y, x ∈ B y) (hN : ∀ y, ((B y).ncard : ℂ) * w = 1)
    (hU : ∀ y, ∀ x ∈ B y, (U y x).det ≠ 0) :
    ∃ (T : tracelessOn X →ₗ[ℂ] tracelessOn Y) (T' : tracelessOn Y →ₗ[ℂ] tracelessOn X),
      (∀ l, (T l).1 = weightedConjugateMean B w U l.1) ∧
      (∀ g f, traceFinsumPairing (T' g).1 f.1 = traceFinsumPairing g.1 (T f).1) ∧
      ∀ g, (T (T' g)).1 = w • g.1 := by
  classical
  cases nonempty_fintype X
  cases nonempty_fintype Y
  let p : X → Y := fun x => (hB x).exists.choose
  have hp : ∀ x, x ∈ B (p x) := fun x => (hB x).exists.choose_spec
  have hmem : ∀ x y, x ∈ B y ↔ p x = y :=
    fun x y => ⟨fun h => (hB x).unique (hp x) h, fun h => h ▸ hp x⟩
  have hU' : ∀ x, (U (p x) x).det ≠ 0 := fun x => hU _ x (hp x)
  have hsum : ∀ (l : X → ComplexMatrix2) (y : Y), weightedConjugateMean B w U l y =
      w • ∑ x, if p x = y then ComplexMatrix2.conjugateBy (U y x) (l x) else 0 := by
    intro l y
    simp only [weightedConjugateMean, hmem]
    rw [finsum_eq_sum_of_fintype]
    simp only [finsum_eq_if]
  have hadd : ∀ l l' : X → ComplexMatrix2, weightedConjugateMean B w U (l + l') =
      weightedConjugateMean B w U l + weightedConjugateMean B w U l' := by
    intro l l'
    funext y
    simp only [Pi.add_apply, hsum, ← smul_add, ← Finset.sum_add_distrib]
    refine congrArg (fun S : ComplexMatrix2 => w • S) (Finset.sum_congr rfl fun x _ => ?_)
    split_ifs
    · exact conjugateBy_add _ _ _
    · simp
  have hsmul : ∀ (c : ℂ) (l : X → ComplexMatrix2),
      weightedConjugateMean B w U (c • l) = c • weightedConjugateMean B w U l := by
    intro c l
    funext y
    simp only [Pi.smul_apply, hsum]
    rw [smul_comm c w]
    refine congrArg (fun S : ComplexMatrix2 => w • S) ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs
    · exact conjugateBy_smul _ _ _
    · simp
  have hin : ∀ l : tracelessOn X, weightedConjugateMean B w U l.1 ∈ tracelessOn Y := by
    intro l
    refine mem_tracelessOn.mpr fun y => ?_
    rw [hsum]
    refine ComplexMatrix2.traceless.smul_mem _ (Submodule.sum_mem _ fun x _ => ?_)
    split_ifs with h
    · subst h
      show ComplexMatrix2.fullTrace _ = 0
      rw [fullTrace_conjugateBy (hU' x)]
      exact mem_tracelessOn.mp l.2 x
    · exact ComplexMatrix2.traceless.zero_mem
  let T : tracelessOn X →ₗ[ℂ] tracelessOn Y :=
    { toFun := fun l => ⟨weightedConjugateMean B w U l.1, hin l⟩
      map_add' := fun l l' => Subtype.ext (hadd _ _)
      map_smul' := fun c l => Subtype.ext (hsmul c _) }
  let back : (Y → ComplexMatrix2) → X → ComplexMatrix2 :=
    fun g x => w • ((U (p x) x)⁻¹ * g (p x) * U (p x) x)
  have hbackin : ∀ g : tracelessOn Y, back g.1 ∈ tracelessOn X := by
    intro g
    refine mem_tracelessOn.mpr fun x => ComplexMatrix2.traceless.smul_mem _ ?_
    show ComplexMatrix2.fullTrace _ = 0
    rw [fullTrace_inv_mul_mul (hU' x)]
    exact mem_tracelessOn.mp g.2 (p x)
  have hbackadd : ∀ g g' : Y → ComplexMatrix2, back (g + g') = back g + back g' := by
    intro g g'
    funext x
    simp only [back, Pi.add_apply, Matrix.mul_add, Matrix.add_mul, smul_add]
  have hbacksmul : ∀ (c : ℂ) (g : Y → ComplexMatrix2), back (c • g) = c • back g := by
    intro c g
    funext x
    simp only [back, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
    rw [smul_comm]
  let T' : tracelessOn Y →ₗ[ℂ] tracelessOn X :=
    { toFun := fun g => ⟨back g.1, hbackin g⟩
      map_add' := fun g g' => Subtype.ext (hbackadd _ _)
      map_smul' := fun c g => Subtype.ext (hbacksmul c _) }
  have hpair : ∀ (g : Y → ComplexMatrix2) (f : X → ComplexMatrix2),
      traceFinsumPairing (back g) f = traceFinsumPairing g (weightedConjugateMean B w U f) := by
    intro g f
    simp only [traceFinsumPairing, finsum_eq_sum_of_fintype]
    have hy : ∀ y, ComplexMatrix2.halfTrace (g y * weightedConjugateMean B w U f y) =
        ∑ x, if p x = y then ComplexMatrix2.halfTrace (back g x * f x) else 0 := by
      intro y
      rw [hsum, Matrix.mul_smul, Matrix.mul_sum]
      simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_smul,
        Matrix.trace_sum, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs with h
      · subst h
        have := fullTrace_inv_mul_mul_mul (U (p x) x) (g (p x)) (f x)
        simp only [ComplexMatrix2.fullTrace] at this
        simp only [back, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, this]
      · simp
    simp only [hy]
    rw [Finset.sum_comm]
    simp
  refine ⟨T, T', fun l => rfl, fun g f => hpair g.1 f.1, fun g => ?_⟩
  funext y
  show weightedConjugateMean B w U (back g.1) y = w • g.1 y
  rw [hsum]
  have hterm : ∀ x, (if p x = y then ComplexMatrix2.conjugateBy (U y x) (back g.1 x) else 0) =
      if p x = y then w • g.1 y else 0 := by
    intro x
    split_ifs with h
    · subst h
      show ComplexMatrix2.conjugateBy _ (w • _) = _
      rw [conjugateBy_smul, conjugateBy_inv_mul_mul (hU' x)]
    · rfl
  simp only [hterm]
  have hcount : B y = ↑(Finset.univ.filter fun x => p x = y) := by
    ext x
    simp [hmem]
  have hc : ∑ x, (if p x = y then w • g.1 y else 0) =
      ((B y).ncard : ℂ) • (w • g.1 y) := by
    rw [← Finset.sum_filter, Finset.sum_const, hcount, Set.ncard_coe_finset,
      Nat.cast_smul_eq_nsmul]
  rw [hc, smul_smul ((B y).ncard : ℂ) w, hN, one_smul]
theorem exists_weightedConjugateMean_pairedMap (B : Y → Set X) (w : ℂ)
    (U : Y → X → ComplexMatrix2)
    (hB : ∀ x, ∃! y, x ∈ B y) (hN : ∀ y, ((B y).ncard : ℂ) * w = 1)
    (hU : ∀ y, ∀ x ∈ B y, (U y x).det ≠ 0) :
    ∃ T : (pairedFunctions X).complexSubmodule →ₗ[ℂ] (pairedFunctions Y).complexSubmodule,
      (∀ l : (pairedFunctions X).complexSubmodule,
        (T l : (pairedFunctions Y).index → ComplexMatrix2) =
          weightedConjugateMean B w U (l : (pairedFunctions X).index → ComplexMatrix2)) ∧
      PairedFunctionSpace.PreservesFiniteSupport T ∧
      ∀ g : (pairedFunctions Y).complexSubmodule,
        (T (PairedFunctionSpace.transposeMap T g) :
            (pairedFunctions Y).index → ComplexMatrix2) =
          w • (g : (pairedFunctions Y).index → ComplexMatrix2) := by
  obtain ⟨T₀, T₀', h₁, h₂, h₃⟩ :=
    exists_linear_weightedConjugateMean_and_transpose B w U hB hN hU
  have hfinX : ∀ f : X → ComplexMatrix2, (pairedFunctions X).IsFinitelySupported f :=
    fun f => Set.toFinite (Function.support f)
  have hfinY : ∀ f : Y → ComplexMatrix2, (pairedFunctions Y).IsFinitelySupported f :=
    fun f => Set.toFinite (Function.support f)
  let T : (pairedFunctions X).complexSubmodule →ₗ[ℂ] (pairedFunctions Y).complexSubmodule := T₀
  let T' : (pairedFunctions Y).complexSubmodule →ₗ[ℂ] (pairedFunctions X).complexSubmodule :=
    T₀'
  have hT' : PairedFunctionSpace.IsTransposeMap T T' := fun g f _ => h₂ g f
  have hspec : PairedFunctionSpace.IsTransposeMap T (PairedFunctionSpace.transposeMap T) :=
    Classical.epsilon_spec ⟨T', hT'⟩
  have huniq : ∀ g, PairedFunctionSpace.transposeMap T g = T' g := by
    intro g
    refine Subtype.ext (eq_of_traceFinsumPairing_eq (X := X)
      (PairedFunctionSpace.transposeMap T g).2 (T' g).2 fun f hf => ?_)
    exact (hspec g ⟨f, hf⟩ (hfinX f)).trans (hT' g ⟨f, hf⟩ (hfinX f)).symm
  refine ⟨T, h₁, fun f _ => hfinY _, fun g => ?_⟩
  rw [huniq]
  exact h₃ g
end Finite
end CubeAverageTranspose
open CubeAverageTranspose in
theorem adjointCubeAverageMulTranspose_proof
    (hBlocks : BlockStructure)
    (hComplex : ComplexMeanLiesInComplexGaugeGroup)
    (hSmooth : SmoothingNearIdentity) :
    AdjointCubeAverageMulTranspose := by
  intro L hL n k j hn hj V hV
  have hLpos : 0 < L := by have := hL.2; omega
  have : Finite (Vertex L n k j) :=
    (ClusterExpansion.RegionPolymers.sublattice_finite hLpos n _).to_subtype
  have : Finite (Vertex L n k (j + 1)) :=
    (ClusterExpansion.RegionPolymers.sublattice_finite hLpos n _).to_subtype
  have hcubes := (hBlocks L k (j + 1) hL (by omega) (by omega) (by omega)).1 n hn
  have hρ := (hSmooth.1 L hL).2.2
  have hsort : ∀ x : Vertex L n k j,
      ∃! y : Vertex L n k (j + 1),
        x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :=
    hcubes.2.1.2.1
  have hcard : ∀ y : Vertex L n k (j + 1),
      (((PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).ncard : ℕ) : ℂ) *
        PeriodicLattice.inverseFourthPowerWeight L = 1 := by
    intro y
    obtain ⟨-, -, hn₄, hsub⟩ := hcubes.1 y
    have himg : Subtype.val '' PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y =
        PeriodicLattice.unitBlock y := by
      ext x
      constructor
      · rintro ⟨x', hx', rfl⟩
        exact hx'
      · intro hx
        exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
    have hnc : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).ncard = L ^ 4 := by
      rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg]
      exact hn₄
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hLpos.ne'
    rw [hnc, PeriodicLattice.inverseFourthPowerWeight]
    have : ((L ^ 4 : ℕ) : ℝ) * (L : ℝ) ^ (-4 : ℤ) = 1 := by
      push_cast
      rw [zpow_neg, mul_inv_eq_one₀ (zpow_ne_zero _ hL0)]
      norm_cast
    exact_mod_cast this
  have hdet : ∀ y : Vertex L n k (j + 1),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        (PeriodicLattice.complexMeanContourHolonomy V y x).det ≠ 0 := by
    intro y x hx
    let c : Edge L n k (j + 1) := PeriodicLattice.Bond.forwardFrom y 0
    have hc : c.IsPositivelyOriented := ⟨0, by simp [c, PeriodicLattice.Bond.forwardFrom]⟩
    have hdom : V ∈ (PeriodicLattice.complexAveragingDomainNearOne c :
        Set (Edge L n k j → ComplexMatrix2)) :=
      (hρ.periodic n k j hn hj c hc).subset_complexDomain
        ⟨⟨fun b _ => hV.1.1 b (mem_univ b), fun b _ => hV.1.2 b (mem_univ b)⟩,
          fun b _ => hV.2 b⟩
    have hG := ((hComplex.2 L k (j + 1) hL (by omega) (by omega)).1 n hn c V hc hdom).1 y
      (Or.inl rfl) x hx
    have h1 : (PeriodicLattice.complexMeanContourHolonomy V y x).det = 1 := hG
    rw [h1]
    exact one_ne_zero
  exact exists_weightedConjugateMean_pairedMap
    (fun y => PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    (PeriodicLattice.inverseFourthPowerWeight L)
    (fun y x => PeriodicLattice.complexMeanContourHolonomy V y x)
    hsort hcard hdet
end YangMills.Construction.Tower
end
