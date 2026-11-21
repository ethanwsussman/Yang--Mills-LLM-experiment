import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.BlocksOfTheTwoOperatorFunctionsDescend
import YangMills.Construction.Towers.CellsAndClassesOfThePeriodicExtension
import YangMills.Construction.Towers.DeterminantsOfTheTwoOperatorFunctionsOnTheTorus
import YangMills.Construction.Towers.FirstDifferentialInTheExponentialChartVanishesProof
import YangMills.Construction.Towers.SumsProductsAndTransposesOfDescendingKernels
import YangMills.Construction.Towers.TheTorusMatricesOfTheMassiveOperatorFunctionsProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
open Matrices
namespace Tower
namespace PeriodicDeterminants
open PeriodicOperators
open LocalKernels
open LocalKernels.Periodisation
open OperatorBlocksDescend
theorem abs_det_eq_norm_det_of_coords {V : Type*} {J : Type} [AddCommGroup V] [Module ℝ V] [Fintype J]
    [DecidableEq J] (Φ : V ≃ₗ[ℝ] (J → ℝ)) (m : V →ₗ[ℝ] V) (M : J → J → ℂ)
    (h : ∀ x, (fun j => ((Φ (m x) j : ℝ) : ℂ)) = applyKernel M (fun j => ((Φ x j : ℝ) : ℂ))) :
    |LinearMap.det m| = ‖(Matrix.of M).det‖ := by
  have hdet : LinearMap.det (Φ.conj m) = LinearMap.det m := LinearMap.det_conj m Φ
  have hentry : ∀ i j, M i j = ((LinearMap.toMatrix' (Φ.conj m) i j : ℝ) : ℂ) := by
    intro i j
    have h1 := congrFun (h (Φ.symm (Pi.single j 1))) i
    simp only [LinearEquiv.apply_symm_apply] at h1
    have h2 : applyKernel M (fun l => (((Pi.single j (1 : ℝ) : J → ℝ) l : ℝ) : ℂ)) i = M i j := by
      unfold applyKernel
      rw [tsum_eq_single j]
      · simp
      · intro l hl
        simp [Pi.single_eq_of_ne hl]
    rw [h2] at h1
    rw [← h1, LinearMap.toMatrix'_apply]
    simp [LinearEquiv.conj_apply]
  have hM : Matrix.of M = (LinearMap.toMatrix' (Φ.conj m)).map Complex.ofRealHom := by
    ext i j
    simp [hentry]
  have h4 : (Matrix.of M).det = ((LinearMap.det m : ℝ) : ℂ) := by
    rw [hM, ← hdet, ← LinearMap.det_toMatrix' (Φ.conj m)]
    exact (RingHom.map_det Complex.ofRealHom _).symm
  rw [h4, Complex.norm_real, Real.norm_eq_abs]
theorem det_linearMapOfEntries {C : Type} [Fintype C] [DecidableEq C] (K : C → C → ℂ) :
    LinearMap.det (linearMapOfEntries K) = (Matrix.of K).det := by
  have hex : ∃ M : (C → ℂ) →ₗ[ℂ] (C → ℂ), linearMapEntry M = K := by
    refine ⟨Matrix.toLin' (Matrix.of K), ?_⟩
    funext c' c
    simp only [linearMapEntry]
    rw [Matrix.toLin'_apply]
    have h := congrFun (Matrix.mulVec_single_one (Matrix.of K) c) c'
    calc _ = (Matrix.of K).mulVec (Pi.single c 1) c' := by congr!
      _ = K c' c := h
  have hs : linearMapEntry (linearMapOfEntries K) = K := Classical.epsilon_spec hex
  rw [← LinearMap.det_toMatrix' (linearMapOfEntries K)]
  congr 1
  ext c' c
  rw [LinearMap.toMatrix'_apply]
  have := congrFun (congrFun hs c') c
  simp only [linearMapEntry] at this
  simp only [Matrix.of_apply]
  rw [← this]
  congr!
def quotEquivOfTranslate {I I' : PeriodicData} (β : I.Carrier ≃ I'.Carrier)
    (hβ : ∀ m ι, β (I.translate m ι) = I'.translate m (β ι)) (s : ℕ) :
    I.QuotMod s ≃ I'.QuotMod s where
  toFun := Quot.map β (by
    rintro a b ⟨n, rfl⟩
    exact ⟨n, hβ _ _⟩)
  invFun := Quot.map β.symm (by
    rintro a b ⟨n, rfl⟩
    refine ⟨n, β.injective ?_⟩
    simp [hβ])
  left_inv := by
    rintro ⟨a⟩
    exact congrArg (Quot.mk _) (β.symm_apply_apply a)
  right_inv := by
    rintro ⟨a⟩
    exact congrArg (Quot.mk _) (β.apply_symm_apply a)
theorem det_descendMatrix_periodization {k : ℕ} (L n : ℕ) (I : PeriodicData) (P : WeightedIndexSet k)
    (β : Idx L P ≃ I.Carrier)
    (hβ : ∀ m ι, β ((P.toPeriodicData L).translate m ι) = I.translate m (β ι))
    (hcl : QuotientClassesPeriodic L n P)
    (T : I.Carrier → I.Carrier → ℂ) (M : KernelMatrix (P.ImageCarrier L n) (P.ImageCarrier L n))
    (hsum : ∀ ι' ι, M (P.proj L n ι') (P.proj L n ι) =
      periodization (P.toPeriodicData L) (P.toPeriodicData L) (fun a b => T (β a) (β b))
        (periodSide L n) ι' ι)
    [Fintype (P.ImageCarrier L n)] [DecidableEq (P.ImageCarrier L n)] :
    LinearMap.det (linearMapOfEntries (descendMatrix I I (periodSide L n)
      (periodization I I T (periodSide L n)))) = (Matrix.of M).det := by
  classical
  obtain ⟨-, ⟨φ, hφ, hφq⟩, -⟩ := hcl
  let e : I.QuotMod (periodSide L n) ≃ P.ImageCarrier L n :=
    (quotEquivOfTranslate β hβ (periodSide L n)).symm.trans (Equiv.ofBijective φ hφ)
  have he : ∀ i, e (I.mkQuot (periodSide L n) i) = P.proj L n (β.symm i) := by
    intro i
    exact hφq (β.symm i)
  have hkey : ∀ i' i, periodization I I T (periodSide L n) i' i =
      M (e (I.mkQuot (periodSide L n) i')) (e (I.mkQuot (periodSide L n) i)) := by
    intro i' i
    rw [he, he, hsum]
    simp only [periodization, Equiv.apply_symm_apply, hβ]
  have hmat : descendMatrix I I (periodSide L n) (periodization I I T (periodSide L n)) =
      fun c' c => M (e c') (e c) := by
    funext c' c
    have hex : ∃ z, ∀ ι' ι, I.mkQuot (periodSide L n) ι' = c' →
        I.mkQuot (periodSide L n) ι = c → periodization I I T (periodSide L n) ι' ι = z :=
      ⟨M (e c') (e c), fun ι' ι h' h => by rw [hkey, h', h]⟩
    have hs := Classical.epsilon_spec hex
    obtain ⟨a', ha'⟩ := Quot.exists_rep c'
    obtain ⟨a, ha⟩ := Quot.exists_rep c
    have h1 := hs a' a ha' ha
    simp only [descendMatrix]
    rw [← h1, hkey]
    exact congrArg₂ (fun x y => M (e x) (e y)) ha' ha
  let _ : Fintype (I.QuotMod (periodSide L n)) := Fintype.ofEquiv _ e.symm
  rw [hmat, det_linearMapOfEntries]
  exact Matrix.det_submatrix_equiv_self e (Matrix.of M)
theorem pauliCoeff_sum_smul (c : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ v, c v • ComplexMatrix2.pauliFamily v) = c a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem mem_traceless_of_mem_hermitianTraceless {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) : X ∈ ComplexMatrix2.traceless := hX.2
theorem pauliCoeff_im_eq_zero {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    (a : Fin 3) : (pauliCoeff a X).im = 0 := by apply _root_.YangMills.SharedProofs.p23717 <;> assumption
theorem real_sum_smul_mem_hermitianTraceless (c : Fin 3 → ℝ) :
    (∑ v, ((c v : ℝ) : ℂ) • ComplexMatrix2.pauliFamily v) ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.PeriodicMatrices.real_pauli_sum_mem_hermitianTraceless <;> assumption
section Charts
variable {L n k j : ℕ}
def edgeFormOfCoeffs (c : Fin 3 × PositiveEdge L n k j → ℂ) : Edge L n k j → ComplexMatrix2 :=
  extendOddly fun v => open Classical in
    if h : v.IsPositivelyOriented then ofPauliCoeffs c ⟨v, h⟩ else 0
theorem edgeFormOfCoeffs_positive (c : Fin 3 × PositiveEdge L n k j → ℂ) (v : PositiveEdge L n k j) :
    edgeFormOfCoeffs c v.1 = ofPauliCoeffs c v := by apply _root_.YangMills.Construction.Tower.TrivialFieldRescaledRelations.edgeFormOfCoeffs_of_pos <;> assumption
theorem edgeFormOfCoeffs_opposite
    (hX : ∀ v : Edge L n k j, Xor v.IsPositivelyOriented v.opposite.IsPositivelyOriented)
    (c : Fin 3 × PositiveEdge L n k j → ℂ) (v : Edge L n k j) :
    edgeFormOfCoeffs c v.opposite = -edgeFormOfCoeffs c v := by
  simp only [edgeFormOfCoeffs, extendOddly]
  rcases hX v with ⟨hp, hn⟩ | ⟨hp, hn⟩
  · rw [if_neg hn, if_pos hp, show v.opposite.opposite = v from rfl]
  · rw [if_pos hp, if_neg hn, neg_neg]
theorem oddForm_ext
    (hX : ∀ v : Edge L n k j, Xor v.IsPositivelyOriented v.opposite.IsPositivelyOriented)
    {B B' : Edge L n k j → ComplexMatrix2} (hB : ∀ v, B v.opposite = -B v)
    (hB' : ∀ v, B' v.opposite = -B' v)
    (h : ∀ v : PositiveEdge L n k j, B v.1 = B' v.1) : B = B' := by
  funext v
  rcases hX v with ⟨hp, -⟩ | ⟨hp, -⟩
  · exact h ⟨v, hp⟩
  · have h1 : B v.opposite = B' v.opposite := h ⟨_, hp⟩
    rw [hB, hB'] at h1
    exact neg_injective h1
def edgeChart
    (hX : ∀ v : Edge L n k j, Xor v.IsPositivelyOriented v.opposite.IsPositivelyOriented) :
    (Fin 3 × PositiveEdge L n k j → ℝ) →ₗ[ℝ] edgeFormSpace L n k j where
  toFun c := ⟨edgeFormOfCoeffs fun ι => ((c ι : ℝ) : ℂ),
    show _ ∈ edgeFormSpace L n k j from ⟨fun v hv => by
      have h1 := edgeFormOfCoeffs_positive (fun ι => ((c ι : ℝ) : ℂ)) ⟨v, hv⟩
      change edgeFormOfCoeffs _ v = _ at h1
      rw [h1]
      exact real_sum_smul_mem_hermitianTraceless _, edgeFormOfCoeffs_opposite hX _⟩⟩
  map_add' c c' := by
    apply Subtype.ext
    refine oddForm_ext hX (edgeFormOfCoeffs_opposite hX _) (fun v => ?_) fun v => ?_
    · change edgeFormOfCoeffs _ v.opposite + edgeFormOfCoeffs _ v.opposite =
        -(edgeFormOfCoeffs _ v + edgeFormOfCoeffs _ v)
      rw [edgeFormOfCoeffs_opposite hX, edgeFormOfCoeffs_opposite hX]
      abel
    · change edgeFormOfCoeffs _ v.1 = edgeFormOfCoeffs _ v.1 + edgeFormOfCoeffs _ v.1
      simp only [edgeFormOfCoeffs_positive, ofPauliCoeffs, Pi.add_apply, Complex.ofReal_add, add_smul,
        Finset.sum_add_distrib]
  map_smul' r c := by
    apply Subtype.ext
    refine oddForm_ext hX (edgeFormOfCoeffs_opposite hX _) (fun v => ?_) fun v => ?_
    · change r • edgeFormOfCoeffs _ v.opposite = -(r • edgeFormOfCoeffs _ v)
      rw [edgeFormOfCoeffs_opposite hX, smul_neg]
    · change edgeFormOfCoeffs _ v.1 = r • edgeFormOfCoeffs _ v.1
      simp only [edgeFormOfCoeffs_positive, ofPauliCoeffs, Pi.smul_apply, smul_eq_mul,
        Complex.ofReal_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_smul]
      rfl
theorem toPauliCoeffs_edgeChart
    (hX : ∀ v : Edge L n k j, Xor v.IsPositivelyOriented v.opposite.IsPositivelyOriented)
    (c : Fin 3 × PositiveEdge L n k j → ℝ) (ι : Fin 3 × PositiveEdge L n k j) :
    toPauliCoeffs (restrictToPositiveEdges (edgeChart hX c : Edge L n k j → ComplexMatrix2)) ι =
      ((c ι : ℝ) : ℂ) := by
  change pauliCoeff ι.1 (edgeFormOfCoeffs _ ι.2.1) = _
  rw [edgeFormOfCoeffs_positive]
  exact pauliCoeff_sum_smul (fun a => ((c (a, ι.2) : ℝ) : ℂ)) ι.1
theorem edgeChart_re
    (hX : ∀ v : Edge L n k j, Xor v.IsPositivelyOriented v.opposite.IsPositivelyOriented)
    (f : edgeFormSpace L n k j) :
    edgeChart hX (fun ι =>
      (toPauliCoeffs (restrictToPositiveEdges (f : Edge L n k j → ComplexMatrix2)) ι).re) = f := by
  apply Subtype.ext
  refine oddForm_ext hX (edgeFormOfCoeffs_opposite hX _) f.2.2 fun v => ?_
  have hm : (f : Edge L n k j → ComplexMatrix2) v.1 ∈ ComplexMatrix2.hermitianTraceless := f.2.1 v.1 v.2
  change edgeFormOfCoeffs _ v.1 = _
  rw [edgeFormOfCoeffs_positive]
  conv_rhs => rw [← sum_pauliCoeff_smul (mem_traceless_of_mem_hermitianTraceless hm)]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  apply Complex.ext
  · rfl
  · simpa using (pauliCoeff_im_eq_zero hm a).symm
def vertexChart : (Fin 3 × Vertex L n k j → ℝ) →ₗ[ℝ] vertexFunctionSpace L n k j where
  toFun c := ⟨ofPauliCoeffs fun ι => ((c ι : ℝ) : ℂ), fun x _ => real_sum_smul_mem_hermitianTraceless _⟩
  map_add' c c' := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_add, Pi.add_apply, ofPauliCoeffs, Complex.ofReal_add, add_smul,
      Finset.sum_add_distrib]
  map_smul' r c := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, ofPauliCoeffs,
      Finset.smul_sum, smul_eq_mul, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_smul]
    rfl
theorem toPauliCoeffs_vertexChart (c : Fin 3 × Vertex L n k j → ℝ) (ι : Fin 3 × Vertex L n k j) :
    toPauliCoeffs (vertexChart c : Vertex L n k j → ComplexMatrix2) ι = ((c ι : ℝ) : ℂ) :=
  pauliCoeff_sum_smul (fun a => ((c (a, ι.2) : ℝ) : ℂ)) ι.1
theorem vertexChart_re (f : vertexFunctionSpace L n k j) :
    vertexChart (fun ι => (toPauliCoeffs (f : Vertex L n k j → ComplexMatrix2) ι).re) = f := by
  apply Subtype.ext
  funext x
  have hm : (f : Vertex L n k j → ComplexMatrix2) x ∈ ComplexMatrix2.hermitianTraceless :=
    f.2 x (mem_univ x)
  change ofPauliCoeffs
    (fun ι => (((toPauliCoeffs (f : Vertex L n k j → ComplexMatrix2) ι).re : ℝ) : ℂ)) x = _
  simp only [ofPauliCoeffs]
  conv_rhs => rw [← sum_pauliCoeff_smul (mem_traceless_of_mem_hermitianTraceless hm)]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  apply Complex.ext
  · rfl
  · simpa using (pauliCoeff_im_eq_zero hm a).symm
theorem exists_realCoords {X σ : Type} (p : Submodule ℝ (X → ComplexMatrix2))
    (read : (X → ComplexMatrix2) → Fin 3 × σ → ℂ) (G : (Fin 3 × σ → ℝ) →ₗ[ℝ] p)
    (h1 : ∀ c ι, read (G c) ι = ((c ι : ℝ) : ℂ))
    (h2 : ∀ f : p, G (fun ι => (read f ι).re) = f) :
    ∃ Ψ : p ≃ₗ[ℝ] (Fin 3 × σ → ℝ), ∀ (f : p) ι, read f ι = ((Ψ f ι : ℝ) : ℂ) := by
  have hinj : Function.Injective G := by
    intro c c' h
    funext ι
    have h3 := h1 c ι
    rw [h, h1] at h3
    exact_mod_cast h3.symm
  let E := LinearEquiv.ofBijective G ⟨hinj, fun f => ⟨_, h2 f⟩⟩
  refine ⟨E.symm, fun f ι => ?_⟩
  have h4 : f = G (E.symm f) := (E.apply_symm_apply f).symm
  conv_lhs => rw [h4]
  exact h1 _ ι
end Charts
def HasRealCoords {k : ℕ} (L n : ℕ) (A : CellClass k)
    (p : Submodule ℝ ((CellClass.quotSpace L n A).index → ComplexMatrix2)) : Prop :=
  ∃ Ψ : p ≃ₗ[ℝ] (A.colourPairs.ImageCarrier L n → ℝ), ∀ (f : p) κ,
    CellClass.quotCoeffsOn L n A (f : (CellClass.quotSpace L n A).index → ComplexMatrix2) κ =
      ((Ψ f κ : ℝ) : ℂ)
def imageCarrierEquiv {k : ℕ} (L n : ℕ) (A : CellClass k)
    (hs : Function.Surjective
      (Cell.proj n : Cell L k A.level A.cellType → QuotientCell L n k A.level A.cellType)) :
    A.colourPairs.ImageCarrier L n ≃ Fin 3 × QuotientCell L n k A.level A.cellType where
  toFun κ := κ.2.1
  invFun x := ⟨(), ⟨x, by
    obtain ⟨c, hc⟩ := hs x.2
    refine ⟨(x.1, c), ?_⟩
    change (x.1, Cell.proj n c) = x
    rw [hc]⟩⟩
  left_inv := by
    rintro ⟨⟨⟩, ⟨x, hx⟩⟩
    rfl
  right_inv := fun x => rfl
theorem hasRealCoords_of_chart {k : ℕ} (L n : ℕ) (A : CellClass k)
    (hs : Function.Surjective
      (Cell.proj n : Cell L k A.level A.cellType → QuotientCell L n k A.level A.cellType))
    (p : Submodule ℝ ((CellClass.quotSpace L n A).index → ComplexMatrix2))
    (h : ∃ Ψ : p ≃ₗ[ℝ] (Fin 3 × QuotientCell L n k A.level A.cellType → ℝ), ∀ (f : p) ι,
      toPauliCoeffs (CellClass.quotCellFn L n A f) ι = ((Ψ f ι : ℝ) : ℂ)) :
    HasRealCoords L n A p := by
  obtain ⟨Ψ, hΨ⟩ := h
  refine ⟨Ψ.trans (LinearEquiv.funCongrLeft ℝ ℝ (imageCarrierEquiv L n A hs)), fun f κ => ?_⟩
  exact hΨ f κ.2.1
theorem hasRealCoords_edges {k j : ℕ} (L n : ℕ) (hj : j ≤ k)
    (hX : ∀ v : Edge L n k j, Xor v.IsPositivelyOriented v.opposite.IsPositivelyOriented)
    (hs : Function.Surjective
      (Cell.proj n : Cell L k j CellType.edge → QuotientCell L n k j CellType.edge)) :
    HasRealCoords L n (CellClass.edgeClass k j hj) (edgeFormSpace L n k j) :=
  hasRealCoords_of_chart L n _ hs _
    (exists_realCoords (edgeFormSpace L n k j) (fun f => toPauliCoeffs (restrictToPositiveEdges f))
      (edgeChart hX) (toPauliCoeffs_edgeChart hX) (edgeChart_re hX))
theorem hasRealCoords_vertices {k j : ℕ} (L n : ℕ) (hj : j ≤ k)
    (hs : Function.Surjective
      (Cell.proj n : Cell L k j CellType.vertex → QuotientCell L n k j CellType.vertex)) :
    HasRealCoords L n (CellClass.vertexClass k j hj) (vertexFunctionSpace L n k j) :=
  hasRealCoords_of_chart L n _ hs _
    (exists_realCoords (vertexFunctionSpace L n k j) (fun f => toPauliCoeffs f)
      vertexChart toPauliCoeffs_vertexChart vertexChart_re)
section Two
variable {k : ℕ} (L n : ℕ)
def imageCarrierPairedEquiv (A A' : CellClass k) :
    (pairedSum A A').ImageCarrier L n ≃
      A.colourPairs.ImageCarrier L n ⊕ A'.colourPairs.ImageCarrier L n where
  toFun
    | ⟨.inl u, c⟩ => .inl ⟨u, c⟩
    | ⟨.inr u, c⟩ => .inr ⟨u, c⟩
  invFun
    | .inl ⟨u, c⟩ => ⟨.inl u, c⟩
    | .inr ⟨u, c⟩ => ⟨.inr u, c⟩
  left_inv := by
    rintro ⟨_ | _, c⟩ <;> rfl
  right_inv := by
    rintro (⟨_, c⟩ | ⟨_, c⟩) <;> rfl
theorem abs_det_pair (A A' : CellClass k)
    {p : Submodule ℝ ((CellClass.quotSpace L n A).index → ComplexMatrix2)}
    {p' : Submodule ℝ ((CellClass.quotSpace L n A').index → ComplexMatrix2)}
    (hp : HasRealCoords L n A p) (hp' : HasRealCoords L n A' p')
    (m : (p × p') →ₗ[ℝ] p × p')
    (M : KernelMatrix ((pairedSum A A').ImageCarrier L n) ((pairedSum A A').ImageCarrier L n))
    (hM : IsPauliMatrixOfPair L n A A' m M)
    [Fintype ((pairedSum A A').ImageCarrier L n)] [DecidableEq ((pairedSum A A').ImageCarrier L n)] :
    |LinearMap.det m| = ‖(Matrix.of M).det‖ := by
  obtain ⟨Ψ, hΨ⟩ := hp
  obtain ⟨Ψ', hΨ'⟩ := hp'
  let Φ : (p × p') ≃ₗ[ℝ] ((pairedSum A A').ImageCarrier L n → ℝ) :=
    (Ψ.prodCongr Ψ').trans ((LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).symm.trans
      (LinearEquiv.funCongrLeft ℝ ℝ (imageCarrierPairedEquiv L n A A')))
  have hread : ∀ x : p × p', quotCoeffsOnPair L n A A' (x.1 : _ → ComplexMatrix2)
      (x.2 : _ → ComplexMatrix2) = fun κ => ((Φ x κ : ℝ) : ℂ) := by
    intro x
    funext κ
    obtain ⟨_ | _, c⟩ := κ
    · exact hΨ x.1 ⟨(), c⟩
    · exact hΨ' x.2 ⟨(), c⟩
  refine abs_det_eq_norm_det_of_coords Φ m M fun x => ?_
  rw [← hread, ← hread]
  exact hM x
def toSumEquiv (A A' : CellClass k) :
    Idx L (pairedSum A A') ≃ ColourCell L A ⊕ ColourCell L A' where
  toFun := toSum L A A'
  invFun
    | .inl ι => ⟨.inl (), ι⟩
    | .inr ι => ⟨.inr (), ι⟩
  left_inv := by
    rintro ⟨_ | _, ι⟩ <;> rfl
  right_inv := by
    rintro (ι | ι) <;> rfl
end Two
section Exponential
theorem continuous_matExp : Continuous (fun X : ComplexMatrix2 => ComplexMatrix2.matExp X) := by apply _root_.YangMills.Construction.Tower.FirstDerivVanishing.continuous_matExp <;> assumption
theorem inv_matExp_neg (X : ComplexMatrix2) :
    (ComplexMatrix2.matExp (-X))⁻¹ = ComplexMatrix2.matExp X := by
  rw [ComplexMatrix2.matExp, Matrix.exp_neg, Matrix.nonsing_inv_nonsing_inv]
  exact (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp X)
theorem matExp_I_smul_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • X) ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.matExp_mem_compactGaugeGroup <;> assumption
variable {L n k j : ℕ}
theorem expTwist_one {Y : Edge L n k j → ComplexMatrix2} (hY : ∀ v, Y v.opposite = -Y v)
    (v : Edge L n k j) :
    PeriodicLattice.expTwist Y 1 v = ComplexMatrix2.matExp (Complex.I • Y v) := by
  classical
  simp only [PeriodicLattice.expTwist, Pi.one_apply, mul_one]
  split_ifs
  · rfl
  · rw [hY, smul_neg, inv_matExp_neg]
theorem fullExpTwist_one {a : ℝ} {Y : InfiniteLattice.Link a → ComplexMatrix2}
    (hY : ∀ v, Y v.opposite = -Y v) (v : InfiniteLattice.Link a) :
    FullSpace.expTwist Y 1 v = ComplexMatrix2.matExp (Complex.I • Y v) := by
  classical
  simp only [FullSpace.expTwist, Pi.one_apply, mul_one]
  split_ifs
  · rfl
  · rw [hY, smul_neg, inv_matExp_neg]
end Exponential
section Fields
variable {L n k : ℕ}
theorem opposite_positive_of_not_positive {a : ℝ} {v : InfiniteLattice.Link a}
    (h : ¬v.IsPositivelyOriented) : v.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
def fullEdgeForm {j : ℕ} (c : Fin 3 × PeriodicOperators.PosEdge L k j → ℂ) :
    FullSpace.Edge L k j → ComplexMatrix2 :=
  FullSpace.extendOddly fun v => open Classical in
    if h : v.IsPositivelyOriented then ofPauliCoeffs c ⟨v, h⟩ else 0
theorem fullEdgeForm_eq_lift {j : ℕ}
    (hq : ∀ v : FullSpace.Edge L k j,
      (FullSpace.projEdge L n k j v).opposite = FullSpace.projEdge L n k j v.opposite)
    (hp : ∀ v : PeriodicOperators.PosEdge L k j,
      (projPositiveEdge L n k j v).1 = FullSpace.projEdge L n k j v.1)
    {B : Edge L n k j → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k j) :
    fullEdgeForm (fun ι => toPauliCoeffs (restrictToPositiveEdges B)
        (ι.1, projPositiveEdge L n k j ι.2)) =
      liftGaugeField L n k j B := by
  have hpos : ∀ v : PeriodicOperators.PosEdge L k j,
      ofPauliCoeffs (fun ι : Fin 3 × PeriodicOperators.PosEdge L k j =>
        toPauliCoeffs (restrictToPositiveEdges B) (ι.1, projPositiveEdge L n k j ι.2)) v =
        B (FullSpace.projEdge L n k j v.1) := by
    intro v
    have hm : B (projPositiveEdge L n k j v).1 ∈ ComplexMatrix2.traceless :=
      hB.1 _ (projPositiveEdge L n k j v).2
    rw [← hp]
    exact sum_pauliCoeff_smul hm
  funext v
  simp only [fullEdgeForm, FullSpace.extendOddly]
  by_cases h : v.IsPositivelyOriented
  · rw [if_pos h, dif_pos h]
    exact hpos ⟨v, h⟩
  · have h' := opposite_positive_of_not_positive h
    rw [if_neg h, dif_pos h', hpos ⟨v.opposite, h'⟩]
    change -B (FullSpace.projEdge L n k j v.opposite) = B (FullSpace.projEdge L n k j v)
    rw [← hq, hB.2, neg_neg]
theorem expForm_lift
    (hq : ∀ v : FullSpace.Edge L k 0,
      (FullSpace.projEdge L n k 0 v).opposite = FullSpace.projEdge L n k 0 v.opposite)
    {Y : Edge L n k 0 → ComplexMatrix2} (hY : ∀ v, Y v.opposite = -Y v) :
    FullSpace.expForm (liftGaugeField L n k 0 Y) =
      liftGaugeField L n k 0 (IdentityExpChart.expForm Y) := by
  funext v
  have hodd : ∀ v : FullSpace.Edge L k 0, liftGaugeField L n k 0 Y v.opposite =
      -liftGaugeField L n k 0 Y v := by
    intro v
    change Y (FullSpace.projEdge L n k 0 v.opposite) = -Y (FullSpace.projEdge L n k 0 v)
    rw [← hq, hY]
  exact (fullExpTwist_one hodd v).trans (expTwist_one hY _).symm
theorem coeffForms_eq_lift (hL : 0 < L)
    (hq0 : ∀ v : FullSpace.Edge L k 0,
      (FullSpace.projEdge L n k 0 v).opposite = FullSpace.projEdge L n k 0 v.opposite)
    (hp0 : ∀ v : PeriodicOperators.PosEdge L k 0,
      (projPositiveEdge L n k 0 v).1 = FullSpace.projEdge L n k 0 v.1)
    (hqk : ∀ v : FullSpace.Edge L k k,
      (FullSpace.projEdge L n k k v).opposite = FullSpace.projEdge L n k k v.opposite)
    (hpk : ∀ v : PeriodicOperators.PosEdge L k k,
      (projPositiveEdge L n k k v).1 = FullSpace.projEdge L n k k v.1)
    (ζ : PeriodicField L n k) :
    FullSpace.backgroundOfCoeffs hL (ζ.pauliCoeffs hL) =
        liftGaugeField L n k 0 (ζ.1 : Edge L n k 0 → ComplexMatrix2) ∧
      FullSpace.sourceOfCoeffs hL (ζ.pauliCoeffs hL) =
        liftGaugeField L n k 0 (ζ.2.1 : Edge L n k 0 → ComplexMatrix2) ∧
      FullSpace.coarseOfCoeffs hL (ζ.pauliCoeffs hL) =
        liftGaugeField L n k k (ζ.2.2 : Edge L n k k → ComplexMatrix2) :=
  ⟨fullEdgeForm_eq_lift hq0 hp0 ζ.1.2, fullEdgeForm_eq_lift hq0 hp0 ζ.2.1.2,
    fullEdgeForm_eq_lift hqk hpk ζ.2.2.2⟩
def pauliCoeffsOnImage (hL : 0 < L) (ζ : PeriodicField L n k) :
    (fieldIndices L k hL).ImageCarrier L n → ℂ
  | ⟨.background, c⟩ => (edgePauliCoordinates L n k 0).coeffs ζ.1.1 c.1
  | ⟨.source, c⟩ => (edgePauliCoordinates L n k 0).coeffs ζ.2.1.1 c.1
  | ⟨.coarse, c⟩ => (edgePauliCoordinates L n k k).coeffs ζ.2.2.1 c.1
theorem pauliCoeffsOnImage_proj (hL : 0 < L) (ζ : PeriodicField L n k)
    (κ : LocalKernels.FieldIdx L k hL) :
    pauliCoeffsOnImage hL ζ ((fieldIndices L k hL).proj L n κ) = ζ.pauliCoeffs hL κ := by
  obtain ⟨_ | _ | _, ι⟩ := κ <;> rfl
theorem liftQuotField_onQuotient (hL : 0 < L)
    (hcl : QuotientClassesPeriodic L n (fieldIndices L k hL)) (ζ : PeriodicField L n k) :
    liftQuotField (FullSpace.fieldPeriodicData L k hL) (2 * L ^ n) (ζ.onQuotient hL) =
      ζ.pauliCoeffs hL := by
  obtain ⟨-, ⟨φ, -, hφ⟩, -⟩ := hcl
  have hex : ∃ f : ((fieldIndices L k hL).toPeriodicData L).QuotMod (2 * L ^ n) → ℂ,
      ∀ κ : LocalKernels.FieldIdx L k hL,
        f (((fieldIndices L k hL).toPeriodicData L).mkQuot (2 * L ^ n) κ) = ζ.pauliCoeffs hL κ :=
    ⟨fun c => pauliCoeffsOnImage hL ζ (φ c), fun κ => by
      have h1 := hφ κ
      change pauliCoeffsOnImage hL ζ
        (φ (((fieldIndices L k hL).toPeriodicData L).mkQuot (periodSide L n) κ)) = _
      rw [h1, pauliCoeffsOnImage_proj]⟩
  funext κ
  exact Classical.epsilon_spec hex κ
end Fields
section Near
variable {L n k : ℕ}
theorem exists_coord_radius [Fintype (PositiveEdge L n k 0)] [Fintype (PositiveEdge L n k k)]
    (hX0 : ∀ v : Edge L n k 0, Xor v.IsPositivelyOriented v.opposite.IsPositivelyOriented)
    (hXk : ∀ v : Edge L n k k, Xor v.IsPositivelyOriented v.opposite.IsPositivelyOriented)
    (O : Set (FieldTriple L n k)) (hO : O ∈ 𝓝 (0 : FieldTriple L n k)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : FieldTriple L n k, (∀ i, |fieldTripleCoords x i| < ε) → x ∈ O := by
  let C : (FieldTripleIndex L n k → ℝ) → FieldTriple L n k := fun y =>
    (edgeChart hX0 (fun ι => y (Sum.inl ι)), edgeChart hX0 (fun ι => y (Sum.inr (Sum.inl ι))),
      edgeChart hXk (fun ι => y (Sum.inr (Sum.inr ι))))
  have hc : Continuous C := by
    have c0 : Continuous (edgeChart hX0) := LinearMap.continuous_of_finiteDimensional _
    have ck : Continuous (edgeChart hXk) := LinearMap.continuous_of_finiteDimensional _
    exact (c0.comp (by fun_prop)).prodMk ((c0.comp (by fun_prop)).prodMk (ck.comp (by fun_prop)))
  have hC0 : C 0 = 0 := by
    refine Prod.ext (map_zero (edgeChart hX0)) (Prod.ext (map_zero (edgeChart hX0))
      (map_zero (edgeChart hXk)))
  have hCx : ∀ x, C (fieldTripleCoords x) = x := fun x =>
    Prod.ext (edgeChart_re hX0 x.1) (Prod.ext (edgeChart_re hX0 x.2.1) (edgeChart_re hXk x.2.2))
  have hmem : C ⁻¹' O ∈ 𝓝 (0 : FieldTripleIndex L n k → ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by rwa [hC0])
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨ε, hε, fun x hx => ?_⟩
  rw [← hCx x]
  apply hb
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro i
  simpa [Real.dist_eq] using hx i
theorem continuous_expGaugeField :
    Continuous fun x : FieldTriple L n k =>
      PeriodicLattice.expGaugeField (x.1 : Edge L n k 0 → ComplexMatrix2) := by
  refine continuous_pi fun v => continuous_matExp.comp ?_
  have h1 : Continuous fun x : FieldTriple L n k => (x.1 : Edge L n k 0 → ComplexMatrix2) v :=
    (continuous_apply v).comp (continuous_subtype_val.comp continuous_fst)
  exact h1.const_smul Complex.I
theorem expGaugeField_mem
    (hX : ∀ v : Edge L n k 0, Xor v.IsPositivelyOriented v.opposite.IsPositivelyOriented)
    (B : edgeFormSpace L n k 0) :
    PeriodicLattice.expGaugeField (B : Edge L n k 0 → ComplexMatrix2) ∈ fieldSpace L n k 0 := by
  have hsu : ∀ v : Edge L n k 0,
      (B : Edge L n k 0 → ComplexMatrix2) v ∈ ComplexMatrix2.hermitianTraceless := by
    intro v
    rcases hX v with ⟨hp, -⟩ | ⟨hp, -⟩
    · exact B.2.1 v hp
    · have h1 : (B : Edge L n k 0 → ComplexMatrix2) v.opposite ∈ ComplexMatrix2.hermitianTraceless :=
        B.2.1 _ hp
      rw [B.2.2 v] at h1
      simpa using ComplexMatrix2.hermitianTraceless.neg_mem h1
  refine ⟨fun v _ => matExp_I_smul_mem (hsu v), fun v _ => ?_⟩
  change ComplexMatrix2.matExp (Complex.I • (B : Edge L n k 0 → ComplexMatrix2) v.opposite) =
    (ComplexMatrix2.matExp (Complex.I • (B : Edge L n k 0 → ComplexMatrix2) v))⁻¹
  rw [B.2.2 v, smul_neg, ComplexMatrix2.matExp, ComplexMatrix2.matExp, Matrix.exp_neg]
theorem abs_fieldTripleCoords_le (hL : 0 < L)
    (hs0 : Function.Surjective
      (Cell.proj n : Cell L k 0 CellType.edge → QuotientCell L n k 0 CellType.edge))
    (hsk : Function.Surjective
      (Cell.proj n : Cell L k k CellType.edge → QuotientCell L n k k CellType.edge))
    (ζ : PeriodicField L n k) (r : RealPeriodicField L n k) (hr : ζ.RealizedBy r) (t : ℝ)
    (ht : ∀ κ, ‖ζ.pauliCoeffs hL κ‖ ≤ t) (i : FieldTripleIndex L n k) :
    |fieldTripleCoords r i| ≤ t := by
  obtain ⟨h1, h2, h3⟩ := hr
  rcases i with ⟨a, c⟩ | ⟨a, c⟩ | ⟨a, c⟩
  · obtain ⟨c', rfl⟩ := hs0 c
    have h := ht ⟨.background, (a, c')⟩
    change ‖toPauliCoeffs (restrictToPositiveEdges (ζ.1 : Edge L n k 0 → ComplexMatrix2)) _‖ ≤ t at h
    rw [h1] at h
    exact (Complex.abs_re_le_norm _).trans h
  · obtain ⟨c', rfl⟩ := hs0 c
    have h := ht ⟨.source, (a, c')⟩
    change ‖toPauliCoeffs (restrictToPositiveEdges (ζ.2.1 : Edge L n k 0 → ComplexMatrix2)) _‖ ≤ t at h
    rw [h2] at h
    exact (Complex.abs_re_le_norm _).trans h
  · obtain ⟨c', rfl⟩ := hsk c
    have h := ht ⟨.coarse, (a, c')⟩
    change ‖toPauliCoeffs (restrictToPositiveEdges (ζ.2.2 : Edge L n k k → ComplexMatrix2)) _‖ ≤ t at h
    rw [h3] at h
    exact (Complex.abs_re_le_norm _).trans h
end Near
theorem abs_det_eq_periodization {k : ℕ} (L n : ℕ) (A A' : CellClass k)
    {p : Submodule ℝ ((CellClass.quotSpace L n A).index → ComplexMatrix2)}
    {p' : Submodule ℝ ((CellClass.quotSpace L n A').index → ComplexMatrix2)}
    (hp : HasRealCoords L n A p) (hp' : HasRealCoords L n A' p')
    (m : (p × p') →ₗ[ℝ] p × p')
    (M : KernelMatrix ((pairedSum A A').ImageCarrier L n) ((pairedSum A A').ImageCarrier L n))
    (hM : IsPauliMatrixOfPair L n A A' m M)
    (I : PeriodicData) (β : Idx L (pairedSum A A') ≃ I.Carrier)
    (hβ : ∀ m ι, β (((pairedSum A A').toPeriodicData L).translate m ι) = I.translate m (β ι))
    (T : I.Carrier → I.Carrier → ℂ)
    (hD : KernelDescends L n (pairedSum A A') (pairedSum A A')
      (fun a b => T (β a) (β b)) M)
    (hcl : QuotientClassesPeriodic L n (pairedSum A A'))
    (hS : DescendsAlgebra (k := k) L n) :
    |LinearMap.det m| = ‖LinearMap.det (linearMapOfEntries (descendMatrix I I (periodSide L n)
      (periodization I I T (periodSide L n))))‖ := by
  classical
  have := hcl.1
  let _ : Fintype ((pairedSum A A').ImageCarrier L n) := Fintype.ofFinite _
  obtain ⟨⟨R, hR, hloc⟩, -⟩ := id hD
  have hsum := (hS _ _ _ R hR _ _ _ _ _ _ hloc hloc hloc hD hD hD).1.1
  rw [abs_det_pair L n A A' hp hp' m M hM,
    det_descendMatrix_periodization L n I _ β hβ hcl T M hsum]
theorem saddleDetOnEdgeForms_eq {L n k : ℕ}
    (X : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0)
    (M : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k) (h : saddleDetOnEdgeForms X M ≠ 0) :
    saddleDetOnEdgeForms X M = LinearMap.det (saddleOnEdgeForms X M) := by
  classical
  by_cases hE : EdgeFormsEuclidean L n k 0 ∧ EdgeFormsEuclidean L n k k
  · simp only [saddleDetOnEdgeForms, saddleOnEdgeForms, dif_pos hE]
    rfl
  · simp only [saddleDetOnEdgeForms, dif_neg hE, ne_eq, not_true_eq_false] at h
theorem saddleDetOnVertexFunctions_eq {L n k : ℕ}
    (X : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0)
    (M : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k)
    (h : saddleDetOnVertexFunctions X M ≠ 0) :
    saddleDetOnVertexFunctions X M = LinearMap.det (saddleOnVertexFunctions X M) := by
  classical
  by_cases hE : VertexFunctionsEuclidean L n k 0 ∧ VertexFunctionsEuclidean L n k k
  · simp only [saddleDetOnVertexFunctions, saddleOnVertexFunctions, dif_pos hE]
    rfl
  · simp only [saddleDetOnVertexFunctions, dif_neg hE, ne_eq, not_true_eq_false] at h
end PeriodicDeterminants
namespace FullSpace.TorusDeterminants
open PeriodicOperators
open PeriodicOperators.LogDetSecondDerivs (quotOperator)
open LocalKernels
open LocalKernels.Periodisation
open Tower.OperatorBlocksDescend
open Tower.PeriodicDeterminants
theorem claim_holds (h₁ : Tower.OperatorBlocksDescend.BlocksDescend)
    (h₂ : Tower.ExpChartFunctionalClaim)
    (h₃ : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (h₄ : LocalKernels.DescendingKernelAlgebra)
    (h₅ : Tower.EdgeProjectionProperties) : Claim := by
  intro L hL hS k hk R _ _ n hn _
  obtain ⟨hcells, hclasses⟩ := h₃ L hS k n hn
  have hXj : ∀ j, j ≤ k → ∀ v : Tower.Edge L n k j,
      Xor v.IsPositivelyOriented v.opposite.IsPositivelyOriented := by
    intro j hj v
    have hL2 : 2 ≤ L := by
      have := hS.2
      omega
    exact PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite hL2
      (by simp only [PeriodicLattice.levelDepth]; omega) v
  have hsj : ∀ j, j ≤ k → ∀ c, Function.Surjective
      (Cell.proj n : Cell L k j c → QuotientCell L n k j c) :=
    fun j hj c => ((hcells j hj).1 c).1
  have hq : ∀ j, j ≤ k → ∀ v : Edge L k j,
      (projEdge L n k j v).opposite = projEdge L n k j v.opposite :=
    fun j hj v => ((h₅ L n k j hS hn hj).1 v).2.2.2
  have hpj : ∀ j, j ≤ k → ∀ v : PeriodicOperators.PosEdge L k j,
      (projPositiveEdge L n k j v).1 = projEdge L n k j v.1 :=
    fun j hj => (hcells j hj).2.2.1
  have h0 : 0 ≤ k := Nat.zero_le k
  have hp0 := hasRealCoords_edges L n h0 (hXj 0 h0) (hsj 0 h0 .edge)
  have hpk := hasRealCoords_edges L n (le_refl k) (hXj k le_rfl) (hsj k le_rfl .edge)
  have hg0 := hasRealCoords_vertices L n h0 (hsj 0 h0 .vertex)
  have hgk := hasRealCoords_vertices L n (le_refl k) (hsj k le_rfl .vertex)
  have hfin : ∀ j, j ≤ k → Finite (Tower.PositiveEdge L n k j) := by
    intro j hj
    have h1 := (hclasses (CellClass.edgeClass k j hj).colourPairs).1
    have h2 : Finite (Fin 3 × QuotientCell L n k j .edge) :=
      Finite.of_equiv _ (imageCarrierEquiv L n (CellClass.edgeClass k j hj) (hsj j hj .edge))
    exact Finite.of_surjective (Prod.snd : Fin 3 × QuotientCell L n k j .edge → _)
      Prod.snd_surjective
  have := hfin 0 h0
  have := hfin k le_rfl
  let _ : Fintype (Tower.PositiveEdge L n k 0) := Fintype.ofFinite _
  let _ : Fintype (Tower.PositiveEdge L n k k) := Fintype.ofFinite _
  obtain ⟨𝒲, hW, h0W, hform, -⟩ := (h₂ L n k hS hn hk).2.exists_nhd
  have hB := eventually_nhdsWithin_iff.1 (h₁ L hS k hk n hn)
  have hφ0 : PeriodicLattice.expGaugeField
      (((0 : FieldTriple L n k).1 : Tower.Edge L n k 0 → ComplexMatrix2)) =
        fun _ => (1 : ComplexMatrix2) := by
    funext v
    simp [PeriodicLattice.expGaugeField]
  have hB' := (continuous_expGaugeField (L := L) (n := n) (k := k)).tendsto 0
  rw [hφ0] at hB'
  have hO := Filter.inter_mem (hW.mem_nhds h0W) (hB'.eventually hB)
  obtain ⟨ε, hε, hr0⟩ := exists_coord_radius (hXj 0 h0) (hXj k le_rfl) _ hO
  refine ⟨ε, hε, fun ζ r hr hb => ?_⟩
  obtain ⟨t, ht, hle⟩ := hb
  obtain ⟨hrW, hrP⟩ := hr0 r fun i => lt_of_le_of_lt
    (abs_fieldTripleCoords_le (L := L) hL (hsj 0 h0 .edge) (hsj k le_rfl .edge) ζ r hr t hle i) ht
  have hE : IdentityExpChart.expForm (r.1 : Tower.Edge L n k 0 → ComplexMatrix2) =
      PeriodicLattice.expGaugeField (r.1 : Tower.Edge L n k 0 → ComplexMatrix2) :=
    funext (expTwist_one r.1.2.2)
  have hformed : BackgroundFunctionalWellDefined
      (IdentityExpChart.expForm (r.1 : Tower.Edge L n k 0 → ComplexMatrix2))
      r.2.1 r.2.2 := by
    rw [hE]
    exact hform r hrW
  have hH := (hrP (expGaugeField_mem (hXj 0 h0) r.1)).2 r.2.1 r.2.2
  rw [← hE] at hH
  have hfc := liftQuotField_onQuotient hL (hclasses (LocalKernels.fieldIndices L k hL)) ζ
  obtain ⟨e1, e2, e3⟩ := coeffForms_eq_lift hL (hq 0 h0) (hpj 0 h0) (hq k le_rfl) (hpj k le_rfl) ζ
  have ex := expForm_lift (hq 0 h0) (Y := (r.1 : Tower.Edge L n k 0 → ComplexMatrix2)) r.1.2.2
  refine ⟨hformed, ?_, ?_⟩
  · obtain ⟨M, hM, hD⟩ := hH.edgeBlock_descends
    have hT : vectorOpFn L k hL (ζ.pauliCoeffs hL) =
        hessianSaddle (liftAtBase
            (IdentityExpChart.expForm (r.1 : Tower.Edge L n k 0 → ComplexMatrix2)))
          (liftAtBase (r.2.1 : Tower.Edge L n k 0 → ComplexMatrix2))
          (liftAtTop (r.2.2 : Tower.Edge L n k k → ComplexMatrix2)) := by
      change hessianSaddle (FullSpace.expForm (backgroundOfCoeffs hL _))
        (sourceOfCoeffs hL _) (coarseOfCoeffs hL _) = _
      rw [e1, e2, e3, hr.1, hr.2.1, hr.2.2, ex]
    have key := abs_det_eq_periodization L n (edgesAtZero k) (edgesAtTop k) hp0 hpk _ M hM
      (vectorIndices L k) (toSumEquiv L _ _) (by rintro m ⟨_ | _, ι⟩ <;> rfl)
      (vectorOpFn L k hL (ζ.pauliCoeffs hL)) (by rw [hT]; exact hD) (hclasses _)
      (h₄ L hS k n hn)
    rw [hessianSaddleDet, saddleDetOnEdgeForms_eq _ _ hformed.1]
    refine Eq.trans key ?_
    change _ = ‖LinearMap.det (linearMapOfEntries (descendMatrix _ _ _ (periodization _ _
      (vectorOpFn L k hL (liftQuotField _ _ (ζ.onQuotient hL))) _)))‖
    rw [hfc]
    rfl
  · obtain ⟨M, hM, hD⟩ := hH.vertexBlock_descends
    have hT : ghostOpFn L k hL (ζ.pauliCoeffs hL) =
        laplacianSaddle L k (liftAtBase
            (IdentityExpChart.expForm (r.1 : Tower.Edge L n k 0 → ComplexMatrix2))) := by
      change laplacianSaddle L k (FullSpace.expForm (backgroundOfCoeffs hL _)) = _
      rw [e1, hr.1, ex]
    have key := abs_det_eq_periodization L n (verticesAtZero k) (verticesAtTop k) hg0 hgk _ M hM
      (ghostIndices L k) (toSumEquiv L _ _) (by rintro m ⟨_ | _, ι⟩ <;> rfl)
      (ghostOpFn L k hL (ζ.pauliCoeffs hL)) (by rw [hT]; exact hD) (hclasses _)
      (h₄ L hS k n hn)
    rw [ghostSaddleDet, saddleDetOnVertexFunctions_eq _ _ hformed.2]
    refine Eq.trans key ?_
    change _ = ‖LinearMap.det (linearMapOfEntries (descendMatrix _ _ _ (periodization _ _
      (ghostOpFn L k hL (liftQuotField _ _ (ζ.onQuotient hL))) _)))‖
    rw [hfc]
    rfl
end FullSpace.TorusDeterminants
end Tower
end YangMills.Construction
end
