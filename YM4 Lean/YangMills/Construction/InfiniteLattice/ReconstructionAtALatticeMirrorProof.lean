import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservables
import YangMills.Construction.InfiniteLattice.ReconstructionAtALatticeMirror
import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslation
import YangMills.Construction.InfiniteLattice.ReflectionsAndLatticeMirrors
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace ComplexOrder
noncomputable section
namespace YangMills.Construction
open OneLoopNotation ComplexHilbert ContractionUnitary
open FormCompletion
namespace LatticeConventions
namespace MirrorReconstructionProof
section Iteration
variable {𝒜 : Type} (q : 𝒜 → 𝒜 → ℂ) (T : 𝒜 → 𝒜)
theorem form_iterate_comm (hsym : ∀ F F', q F (T F') = q (T F) F') (n : ℕ) (G G' : 𝒜) :
    q (T^[n] G) G' = q G (T^[n] G') := by
  induction n generalizing G G' with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← hsym, ih, Function.iterate_succ_apply]
theorem re_form_apply_le_of_symm (hsym : ∀ F F', q F (T F') = q (T F) F')
    (cs : ∀ F F', ‖q F F'‖ ^ 2 ≤ (q F F).re * (q F' F').re) (nn : ∀ F, 0 ≤ (q F F).re)
    (F : 𝒜) (M : ℝ) (hM : ∀ n : ℕ, (q (T^[n] F) (T^[n] F)).re ≤ M) :
    (q (T F) (T F)).re ≤ (q F F).re := by
  set b : ℕ → ℝ := fun n => (q (T^[n] F) (T^[n] F)).re with hb
  have hb0 : b 0 = (q F F).re := rfl
  have hb1 : b 1 = (q (T F) (T F)).re := rfl
  have hbn : ∀ n, 0 ≤ b n := fun n => nn _
  have hstep : ∀ n, b n ^ 2 ≤ b 0 * b (2 * n) := by
    intro n
    have h₁ : q (T^[n] F) (T^[n] F) = q F (T^[2 * n] F) := by
      rw [form_iterate_comm q T hsym, two_mul, Function.iterate_add_apply]
    have h₂ : b n ^ 2 ≤ ‖q F (T^[2 * n] F)‖ ^ 2 := by
      have h₃ : |b n| ≤ ‖q F (T^[2 * n] F)‖ := by
        rw [← h₁]
        exact Complex.abs_re_le_norm _
      rw [← sq_abs (b n)]
      exact pow_le_pow_left₀ (abs_nonneg _) h₃ 2
    exact h₂.trans (cs _ _)
  rw [← hb0, ← hb1]
  by_contra hlt
  rw [not_le] at hlt
  rcases (hbn 0).eq_or_lt with h0 | hpos
  · have h₁ := hstep 1
    rw [← h0, zero_mul] at h₁
    have h₂ : b 1 = 0 := by
      have := hbn 1
      nlinarith
    rw [← h0, h₂] at hlt
    exact lt_irrefl _ hlt
  · set r : ℝ := b 1 / b 0 with hr
    have hr1 : 1 < r := (one_lt_div hpos).2 hlt
    have hiter : ∀ p : ℕ, r ^ (2 ^ p) ≤ b (2 ^ p) / b 0 := by
      intro p
      induction p with
      | zero => simp [hr]
      | succ p ih =>
        have hr0 : 0 ≤ r := by linarith
        have h₁ : r ^ (2 ^ (p + 1)) = (r ^ (2 ^ p)) ^ 2 := by
          rw [← pow_mul, pow_succ]
        have h₂ : (r ^ (2 ^ p)) ^ 2 ≤ (b (2 ^ p) / b 0) ^ 2 :=
          pow_le_pow_left₀ (pow_nonneg hr0 _) ih 2
        have h₃ : (b (2 ^ p) / b 0) ^ 2 ≤ b (2 ^ (p + 1)) / b 0 := by
          rw [div_pow, div_le_div_iff₀ (by positivity) hpos]
          have h₄ := hstep (2 ^ p)
          have h₅ : 2 * 2 ^ p = 2 ^ (p + 1) := by rw [pow_succ]; ring
          rw [h₅] at h₄
          nlinarith
        rw [h₁]
        exact h₂.trans h₃
    obtain ⟨p, hp⟩ := pow_unbounded_of_one_lt (M / b 0) hr1
    have h₁ : r ^ p ≤ r ^ (2 ^ p) :=
      pow_le_pow_right₀ hr1.le Nat.lt_two_pow_self.le
    have h₂ : b (2 ^ p) / b 0 ≤ M / b 0 := div_le_div_of_nonneg_right (hM _) hpos.le
    linarith [hiter p]
end Iteration
section Completion
variable {𝒜 : Type} [AddCommGroup 𝒜] [Module ℂ 𝒜] {q : 𝒜 → 𝒜 → ℂ}
def classVecLinear (hA : DualSpaceComplete q) (hB : FormCompletionHilbert q) :
    𝒜 →ₗ[ℂ] FormHilbertSpace q where
  toFun := classVec q
  map_add' F F' := by
    obtain ⟨-, -, -, -, hadd, -⟩ := hA
    obtain ⟨-, -, -, -, -, hmap, -⟩ := hB
    apply asMap_injective
    rw [asMap_add, hmap, hmap, hmap, hadd]
  map_smul' z F := by
    obtain ⟨-, -, -, -, -, hsmul, -⟩ := hA
    obtain ⟨-, -, -, -, -, hmap, -⟩ := hB
    apply asMap_injective
    rw [RingHom.id_apply, asMap_smul, hmap, hmap, hsmul]
theorem norm_classVec (hA : DualSpaceComplete q) (hB : FormCompletionHilbert q) (F : 𝒜) :
    ‖classVec q F‖ = seminormOfForm q F := by
  obtain ⟨-, -, -, -, -, -, hsharp, -⟩ := hA
  obtain ⟨-, -, -, -, hnorm, hmap, -⟩ := hB
  rw [hnorm, hmap, hsharp]
theorem denseRange_classVec (hB : FormCompletionHilbert q) :
    DenseRange (classVec q) := hB.2.2.2.2.2.2.2.2
theorem exists_bddOp_of_seminorm_le (hA : DualSpaceComplete q) (hB : FormCompletionHilbert q)
    (hC : InducedOperators q) (T : 𝒜 →ₗ[ℂ] 𝒜)
    (hT : ∀ F, seminormOfForm q (T F) ≤ seminormOfForm q F) :
    ∃ B : BddOp (FormHilbertSpace q),
      (∀ F, B (classVec q F) = classVec q (T F)) ∧ ‖B‖ ≤ 1 := by
  obtain ⟨⟨B, hB₁, -⟩, hB₂⟩ := hC (FormHilbertSpace q) 1 (classVecLinear hA hB ∘ₗ T) zero_le_one
    (fun F => by
      change ‖classVec q (T F)‖ ≤ _
      rw [norm_classVec hA hB, one_mul]
      exact hT F)
  exact ⟨B, hB₁, (hB₂ B hB₁).1⟩
theorem exists_unitary_of_seminorm_eq (hA : DualSpaceComplete q) (hB : FormCompletionHilbert q)
    (hC : InducedOperators q) (T S : 𝒜 →ₗ[ℂ] 𝒜)
    (hT : ∀ F, seminormOfForm q (T F) = seminormOfForm q F) (hS : ∀ F, T (S F) = F) :
    ∃ B : BddOp (FormHilbertSpace q),
      (∀ F, B (classVec q F) = classVec q (T F)) ∧
        IsUnitaryMap (B : FormHilbertSpace q →ₗ[ℂ] FormHilbertSpace q) := by
  have hR : ∀ F, ‖(classVecLinear hA hB ∘ₗ T) F‖ = seminormOfForm q F := fun F => by
    change ‖classVec q (T F)‖ = _
    rw [norm_classVec hA hB, hT]
  obtain ⟨⟨B, hB₁, -⟩, hB₂⟩ := hC (FormHilbertSpace q) 1 (classVecLinear hA hB ∘ₗ T) zero_le_one
    (fun F => by rw [hR, one_mul])
  obtain ⟨hiso, hrange⟩ := (hB₂ B hB₁).2 hR
  refine ⟨B, hB₁, hiso, ?_⟩
  have hsame : Set.range (classVecLinear hA hB ∘ₗ T) = Set.range (classVec q) := by
    ext φ
    constructor
    · rintro ⟨F, rfl⟩
      exact ⟨T F, rfl⟩
    · rintro ⟨F, rfl⟩
      refine ⟨S F, ?_⟩
      change classVec q (T (S F)) = _
      rw [hS]
  have huniv : Set.range B = Set.univ := by
    rw [hrange, hsame]
    exact (denseRange_classVec hB).closure_range
  intro φ
  have hφ : φ ∈ Set.range B := by
    rw [huniv]
    exact Set.mem_univ φ
  obtain ⟨ψ, rfl⟩ := hφ
  exact ⟨ψ, rfl⟩
end Completion
section Dense
variable {H 𝒜 : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem symm_nonneg_le_one_of_denseRange {e : 𝒜 → H} (he : DenseRange e) (B : BddOp H)
    (hnorm : ‖B‖ ≤ 1) (hsym : ∀ F F', ⟪e F, B (e F')⟫_ℂ = ⟪B (e F), e F'⟫_ℂ)
    (hpos : ∀ F, 0 ≤ (⟪e F, B (e F)⟫_ℂ).re) :
    IsSymmetricOp B ∧ OpGE B 0 ∧ OpLE B (idOp H) := by
  have hsa : IsSymmetricOp B := by
    intro φ ψ
    refine he.induction_on₂ (p := fun φ ψ => ⟪φ, B ψ⟫_ℂ = ⟪B φ, ψ⟫_ℂ) ?_ hsym φ ψ
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hre : ∀ ψ, 0 ≤ (⟪ψ, B ψ⟫_ℂ).re := by
    intro ψ
    refine he.induction_on (p := fun ψ => 0 ≤ (⟪ψ, B ψ⟫_ℂ).re) ψ ?_ hpos
    exact isClosed_le continuous_const (by fun_prop)
  have hid : IsSymmetricOp (idOp H) := fun φ ψ => rfl
  have hzero : IsSymmetricOp (0 : BddOp H) := fun φ ψ => by simp
  refine ⟨hsa, ⟨hzero, hsa, fun ψ => ?_⟩, ⟨hsa, hid, fun ψ => ?_⟩⟩
  · rw [Complex.le_def]
    refine ⟨by simpa using hre ψ, by simpa using (hsa.inner_self_apply_im_eq_zero ψ).symm⟩
  · rw [Complex.le_def]
    have him : (⟪ψ, ψ⟫_ℂ).im = 0 := hid.inner_self_apply_im_eq_zero ψ
    refine ⟨?_, (hsa.inner_self_apply_im_eq_zero ψ).trans him.symm⟩
    have h₁ : (⟪ψ, B ψ⟫_ℂ).re ≤ ‖ψ‖ * ‖B ψ‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm ψ (B ψ))
    have h₂ : ‖B ψ‖ ≤ ‖ψ‖ := by
      have := B.le_of_opNorm_le hnorm ψ
      rwa [one_mul] at this
    have h₃ : (⟪ψ, (idOp H) ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by
      change (⟪ψ, ψ⟫_ℂ).re = _
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [h₃, sq]
    exact h₁.trans (mul_le_mul_of_nonneg_left h₂ (norm_nonneg _))
end Dense
section Lattice
open InfiniteLattice (Link GaugeField IsSymmetricUnder IsBoundedObservable LatticeSymmetry
  LatticePoint localRegionObservables observableSupNorm shift)
variable {a : ℝ}
theorem latticeSymmetry_eq_of_toFun {r r' : LatticeSymmetry a} (h : r.toFun = r'.toFun) :
    r = r' := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem actOn_comp (r r' : LatticeSymmetry a) (F : GaugeField a → ℂ) :
    (r.comp r').actOn F = r.actOn (r'.actOn F) := rfl
theorem shift_comp_shift (v v' : LatticePoint a) :
    (shift v).comp (shift v') = shift (v + v') := by
  apply latticeSymmetry_eq_of_toFun
  funext x
  change x + (v' : InfiniteLattice.AmbientSpace) + (v : InfiniteLattice.AmbientSpace) =
    x + ((v : InfiniteLattice.AmbientSpace) + (v' : InfiniteLattice.AmbientSpace))
  abel
theorem actOn_shift_add (v v' : LatticePoint a) (F : GaugeField a → ℂ) :
    (shift (v + v')).actOn F = (shift v).actOn ((shift v').actOn F) := by
  rw [← shift_comp_shift, actOn_comp]
theorem actOn_shift_zero (F : GaugeField a → ℂ) :
    (shift (0 : LatticePoint a)).actOn F = F := by
  funext U
  change F ((shift (0 : LatticePoint a)).pullbackField U) = F U
  congr 1
  apply Subtype.ext
  funext b
  change U ((shift (0 : LatticePoint a)).linkMap b) = U b
  have hb : (shift (0 : LatticePoint a)).linkMap b = b := by
    apply Link.ext
    · apply Subtype.ext
      change (b.initial : InfiniteLattice.AmbientSpace) +
        ((0 : LatticePoint a) : InfiniteLattice.AmbientSpace) = b.initial
      simp
    · apply Subtype.ext
      change (b.terminal : InfiniteLattice.AmbientSpace) +
        ((0 : LatticePoint a) : InfiniteLattice.AmbientSpace) = b.terminal
      simp
  rw [hb]
theorem isBoundedObservable_of_mem_local {S : Set InfiniteLattice.AmbientSpace}
    {F : GaugeField a → ℂ} (hF : F ∈ localRegionObservables a S) : IsBoundedObservable F := by
  obtain ⟨Q, -, oF, -⟩ := Set.mem_iUnion₂.1 hF
  exact oF
theorem isBoundedObservable_mul {F F' : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hF' : IsBoundedObservable F') : IsBoundedObservable (F * F') := by
  obtain ⟨mF, C, hC⟩ := hF
  obtain ⟨mF', C', hC'⟩ := hF'
  refine ⟨mF.mul mF', |C| * |C'|, fun U => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul ((hC U).trans (le_abs_self C)) ((hC' U).trans (le_abs_self C'))
    (norm_nonneg _) (abs_nonneg _)
theorem isBoundedObservable_conjFun {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable (conjFun F) := by
  obtain ⟨mF, C, hC⟩ := hF
  refine ⟨Complex.continuous_conj.measurable.comp mF, C, fun U => ?_⟩
  change ‖(starRingEnd ℂ) (F U)‖ ≤ C
  rw [Complex.norm_conj]
  exact hC U
theorem integral_conj_mul_actOn {ν : Measure (GaugeField a)} {r s θ : LatticeSymmetry a}
    (hobs : ∀ (r : LatticeSymmetry a) (F : GaugeField a → ℂ), IsBoundedObservable F →
      IsBoundedObservable (r.actOn F))
    (hinv : IsSymmetricUnder ν r) (hc : r.comp θ = θ.comp s)
    {F F' : GaugeField a → ℂ} (hF : IsBoundedObservable F) (hF' : IsBoundedObservable F') :
    ∫ U, conjFun (θ.actOn (s.actOn F)) U * r.actOn F' U ∂ν =
      ∫ U, conjFun (θ.actOn F) U * F' U ∂ν := by
  have h₁ := hinv (conjFun (θ.actOn F) * F')
    (isBoundedObservable_mul (isBoundedObservable_conjFun (hobs _ _ hF)) hF')
  have h₂ : r.actOn (θ.actOn F) = θ.actOn (s.actOn F) := by
    rw [← actOn_comp, hc, actOn_comp]
  have h₃ : r.actOn (conjFun (θ.actOn F) * F') =
      conjFun (θ.actOn (s.actOn F)) * r.actOn F' := by
    rw [← h₂]
    rfl
  rw [h₃] at h₁
  exact h₁
end Lattice
section Geometry
theorem euclidDot_add (n x y : Point) : euclidDot n (x + y) = euclidDot n x + euclidDot n y := by
  simp [euclidDot, mul_add, Finset.sum_add_distrib]
theorem reflect_midPlane_add (Q : NormalHyperplane) (h x : Point)
    (hh : h = ((euclidNorm Q.normal ^ 2)⁻¹ * euclidDot Q.normal h) • Q.normal) :
    (Q.midPlane h).reflect (x + h) = Q.reflect x := by
  have hn : (Q.midPlane h).normal = Q.normal := rfl
  have hp : (Q.midPlane h).level = Q.level + 1 / 2 * euclidDot Q.normal h := rfl
  simp only [NormalHyperplane.reflect, hn, hp, euclidDot_add]
  funext μ
  have hμ : h μ = ((euclidNorm Q.normal ^ 2)⁻¹ * euclidDot Q.normal h) * Q.normal μ :=
    congrFun hh μ
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hμ]
  ring
end Geometry
section Carrying
open InfiniteLattice (GaugeField IsSymmetricUnder IsBoundedObservable LatticeSymmetry LatticePoint
  localRegionObservables observableSupNorm shift)
open NormalHyperplane
variable {a : ℝ} {Q : NormalHyperplane} {hQ : Q.IsLatticeMirror a}
  {ν : Measure (GaugeField a)} [IsProbabilityMeasure ν]
theorem transports_one : TransportsClassesBy hQ ν 0 1 :=
  fun F => ⟨F, (actOn_shift_zero F.1).symm, rfl⟩
theorem transports_mul {v v' : LatticePoint a} {B B' : BddOp (MirrorHilbertSpace hQ ν)}
    (h : TransportsClassesBy hQ ν v B) (h' : TransportsClassesBy hQ ν v' B') :
    TransportsClassesBy hQ ν (v + v') (B * B') := by
  intro F
  obtain ⟨F₁, e₁, b₁⟩ := h' F
  obtain ⟨F₂, e₂, b₂⟩ := h F₁
  refine ⟨F₂, ?_, ?_⟩
  · rw [e₂, e₁, actOn_shift_add]
  · change B (B' _) = _
    rw [b₁, b₂]
theorem transports_pow {v : LatticePoint a} {B : BddOp (MirrorHilbertSpace hQ ν)}
    (h : TransportsClassesBy hQ ν v B) (n : ℕ) : TransportsClassesBy hQ ν (n • v) (B ^ n) := by
  induction n with
  | zero =>
    rw [zero_nsmul, pow_zero]
    exact transports_one
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact transports_mul ih h
theorem transports_zpowOp {v : LatticePoint a} {V : BddOp (MirrorHilbertSpace hQ ν)}
    (h : TransportsClassesBy hQ ν v V) (h' : TransportsClassesBy hQ ν (-v) (opInv V))
    (y : ℤ) : TransportsClassesBy hQ ν (y • v) (zpowOp V y) := by
  by_cases hy : 0 ≤ y
  · have h₁ : y • v = y.toNat • v := by
      rw [← natCast_zsmul, Int.toNat_of_nonneg hy]
    rw [zpowOp, if_pos hy, h₁]
    exact transports_pow h _
  · have h₁ : y • v = (-y).toNat • (-v) := by
      rw [← natCast_zsmul, Int.toNat_of_nonneg (by omega), smul_neg, neg_smul, neg_neg]
    rw [zpowOp, if_neg hy, h₁]
    exact transports_pow h' _
theorem transports_prod_ofFn {k : ℕ} (B : Fin k → BddOp (MirrorHilbertSpace hQ ν))
    (v : Fin k → LatticePoint a) (h : ∀ i, TransportsClassesBy hQ ν (v i) (B i)) :
    TransportsClassesBy hQ ν (∑ i, v i) (List.ofFn B).prod := by
  induction k with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact transports_one
  | succ k ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact transports_mul (h 0) (ih _ _ fun i => h i.succ)
theorem eq_of_transports (hd : DenseRange (mirrorClass hQ ν)) {v : LatticePoint a}
    {B B' : BddOp (MirrorHilbertSpace hQ ν)}
    (h : TransportsClassesBy hQ ν v B) (h' : TransportsClassesBy hQ ν v B') : B = B' := by
  apply DFunLike.coe_injective
  refine hd.equalizer B.continuous B'.continuous (funext fun F => ?_)
  obtain ⟨F₁, e₁, b₁⟩ := h F
  obtain ⟨F₂, e₂, b₂⟩ := h' F
  have h₁ : F₁ = F₂ := Subtype.ext (e₁.trans e₂.symm)
  change B _ = B' _
  rw [b₁, b₂, h₁]
def shiftLinear (Q : NormalHyperplane) (v : LatticePoint a)
    (hv : ∀ F ∈ localRegionObservables a Q.upperHalfSpace,
      (shift v).actOn F ∈ localRegionObservables a Q.upperHalfSpace) :
    upperObservables a Q →ₗ[ℂ] upperObservables a Q where
  toFun F := ⟨(shift v).actOn F.1, hv _ F.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end Carrying
open InfiniteLattice (GaugeField IsSymmetricUnder IsBoundedObservable LatticeSymmetry LatticePoint
  localRegionObservables observableSupNorm shift)
open NormalHyperplane
theorem mirrorReconstruction_proof (hAct : InfiniteLattice.SymmetryActionOnObservables)
    (hComp : FormCompletion.FormCompletionIsHilbertSpace)
    (hMir : MirrorReflections.MirrorReflectionsStatement)
    (hRP : ReflectionPositivityWithTranslation) :
    MirrorReconstruction := by
  intro a S S' hS hS' h k w ν _ hcond hinvh hinvw hrp hrp'
  obtain ⟨-, -, hkeep, -, -, hlin, hgrow, -, hloc, -, hmult⟩ := hAct a
  have hobs : ∀ (r : LatticeSymmetry (a : ℝ)) (F : GaugeField (a : ℝ) → ℂ),
      IsBoundedObservable F → IsBoundedObservable (r.actOn F) :=
    fun r F hF => ((hkeep r).1 F F hF hF).1
  obtain ⟨hm₁, -, -, -, hm₂, -⟩ := hMir a
  have hdotw := hcond.euclidDot_step
  have hhalf := hcond.isMidPlane
  obtain ⟨-, ⟨-, hlinh, hposh⟩, rfl⟩ := hhalf
  have hrefl : ∀ x v : Point, S.reflect (x + v) = S.reflect x + S.reflectionLinear v :=
    (hm₂ S).1.2.2.1
  have hfix : ∀ v : Point, euclidDot S.normal v = 0 → S.reflectionLinear v = v := (hm₁ S).2.1.2
  have hh : (h : Point) =
      ((euclidNorm S.normal ^ 2)⁻¹ * euclidDot S.normal (h : Point)) • S.normal :=
    (((hm₂ S).2 (h : Point)).1).1 hlinh
  have hne : h ≠ 0 := by
    rintro rfl
    have h₀ : euclidDot S.normal ((0 : LatticePoint (a : ℝ)) : Point) = 0 := by
      simp [euclidDot]
    rw [h₀] at hposh
    exact lt_irrefl _ hposh
  obtain ⟨hform, hrest⟩ := hRP a S hS ν hrp
  obtain ⟨hinvθ, -, -⟩ := hrest h hne hlinh hinvh
  obtain ⟨hA, hB, hC⟩ := hComp _ (upperReflectionForm hS ν) hform.1
  have hd : DenseRange (mirrorClass hS ν) := denseRange_classVec hB
  have hinner : ∀ F F', ⟪mirrorClass hS ν F, mirrorClass hS ν F'⟫_ℂ =
      upperReflectionForm hS ν F F' := hB.2.2.2.2.2.2.1
  have hmove : ∀ (v : LatticePoint (a : ℝ)) (A A' : Set InfiniteLattice.AmbientSpace),
      translateSet A (v : Point) ⊆ A' → ∀ F ∈ localRegionObservables (a : ℝ) A,
        (shift v).actOn F ∈ localRegionObservables (a : ℝ) A' := by
    intro v A A' hsub F hF
    refine (hgrow.2.1 _ _ hsub).2 ?_
    rw [← hloc.2 v A]
    exact ⟨F, hF, rfl⟩
  have hmaph' : ∀ F ∈ localRegionObservables (a : ℝ) S.upperHalfSpace,
      (shift h).actOn F ∈
        localRegionObservables (a : ℝ) (S.midPlane (h : Point)).upperHalfSpace := by
    refine hmove h _ _ ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : S.level ≤ euclidDot S.normal x := hx
    change S.level + 1 / 2 * euclidDot S.normal (h : Point) ≤ euclidDot S.normal (x + (h : Point))
    rw [euclidDot_add]
    linarith
  have hmaph : ∀ F ∈ localRegionObservables (a : ℝ) S.upperHalfSpace,
      (shift h).actOn F ∈ localRegionObservables (a : ℝ) S.upperHalfSpace := by
    intro F hF
    refine (hgrow.2.1 _ _ ?_).2 (hmaph' F hF)
    intro x hx
    have hx' : S.level + 1 / 2 * euclidDot S.normal (h : Point) ≤ euclidDot S.normal x := hx
    change S.level ≤ euclidDot S.normal x
    linarith
  have hmapw : ∀ v : LatticePoint (a : ℝ), euclidDot S.normal (v : Point) = 0 →
      ∀ F ∈ localRegionObservables (a : ℝ) S.upperHalfSpace,
        (shift v).actOn F ∈ localRegionObservables (a : ℝ) S.upperHalfSpace := by
    intro v hv
    refine hmove v _ _ ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : S.level ≤ euclidDot S.normal x := hx
    change S.level ≤ euclidDot S.normal (x + (v : Point))
    rw [euclidDot_add, hv, add_zero]
    exact hx'
  have hinvneg : IsSymmetricUnder ν (shift (-h)) := by
    have h₁ := (hmult ν inferInstance).2 h hinvh (-1)
    rwa [neg_one_zsmul] at h₁
  have hcommh : (shift (-h)).comp (reflectSymmetry hS) =
      (reflectSymmetry hS).comp (shift h) := by
    apply latticeSymmetry_eq_of_toFun
    funext x
    change S.reflect x + ((-h : LatticePoint (a : ℝ)) : Point) = S.reflect (x + (h : Point))
    rw [hrefl, hlinh]
    rfl
  set T := shiftLinear S h hmaph with hTdef
  have hsym : ∀ F F', upperReflectionForm hS ν F (T F') = upperReflectionForm hS ν (T F) F' := by
    intro F F'
    have h₁ := integral_conj_mul_actOn hobs hinvneg hcommh (isBoundedObservable_of_mem_local F.2)
      (hobs (shift h) _ (isBoundedObservable_of_mem_local F'.2))
    rw [← actOn_shift_add, neg_add_cancel, actOn_shift_zero] at h₁
    exact h₁.symm
  have hθ : reflectSymmetry hS = (reflectSymmetry hS').comp (shift h) := by
    apply latticeSymmetry_eq_of_toFun
    funext x
    exact (reflect_midPlane_add S (h : Point) x hh).symm
  have hpos : ∀ F, 0 ≤ (upperReflectionForm hS ν F (T F)).re := by
    intro F
    have h₁ := (hrp' ⟨(shift h).actOn F.1, hmaph' F.1 F.2⟩).2
    have h₂ : upperReflectionForm hS ν F (T F) =
        reflectionForm hS' ν ⟨(shift h).actOn F.1, hmaph' F.1 F.2⟩
          ⟨(shift h).actOn F.1, hmaph' F.1 F.2⟩ := by
      change ∫ U, conjFun ((reflectSymmetry hS).actOn F.1) U *
          (shift h).actOn F.1 U ∂ν =
        ∫ U, conjFun ((reflectSymmetry hS').actOn
          ((shift h).actOn F.1)) U * (shift h).actOn F.1 U ∂ν
      rw [hθ, actOn_comp]
    rw [h₂]
    exact h₁
  have hnormiter : ∀ (F : upperObservables (a : ℝ) S) (n : ℕ),
      observableSupNorm (T^[n] F).1 = observableSupNorm F.1 := by
    intro F n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      change observableSupNorm ((shift h).actOn (T^[n] F).1) = _
      rw [((hlin (shift h)).2 _ (isBoundedObservable_of_mem_local (T^[n] F).2)).2.2.2, ih]
  have hcontr : ∀ F, seminormOfForm (upperReflectionForm hS ν) (T F) ≤
      seminormOfForm (upperReflectionForm hS ν) F := by
    intro F
    refine Real.sqrt_le_sqrt ?_
    refine re_form_apply_le_of_symm (upperReflectionForm hS ν) T hsym
      (fun F F' => (hform.2 F F').1) hform.1.nonneg F (observableSupNorm F.1 ^ 2) fun n => ?_
    have h₁ := (hform.2 (T^[n] F) (T^[n] F)).2.2.2
    rwa [hnormiter] at h₁
  obtain ⟨B, hBc, hBn⟩ := exists_bddOp_of_seminorm_le hA hB hC T hcontr
  have hcarB : TransportsClassesBy hS ν h B := fun F => ⟨T F, rfl, hBc F⟩
  have hspecT : TransportsClassesBy hS ν h (stepOperator hS ν h) :=
    Classical.epsilon_spec ⟨B, hcarB⟩
  have hTB : stepOperator hS ν h = B := eq_of_transports hd hspecT hcarB
  obtain ⟨hsa, h0, h1⟩ := symm_nonneg_le_one_of_denseRange hd B hBn
    (fun F F' => by
      change ⟪mirrorClass hS ν F, B (mirrorClass hS ν F')⟫_ℂ =
        ⟪B (mirrorClass hS ν F), mirrorClass hS ν F'⟫_ℂ
      have e₁ : B (mirrorClass hS ν F') = mirrorClass hS ν (T F') := hBc F'
      have e₂ : B (mirrorClass hS ν F) = mirrorClass hS ν (T F) := hBc F
      rw [e₁, e₂, hinner, hinner, hsym])
    (fun F => by
      have e₁ : B (mirrorClass hS ν F) = mirrorClass hS ν (T F) := hBc F
      rw [e₁, hinner]
      exact hpos F)
  have hunit : ∀ v : LatticePoint (a : ℝ), euclidDot S.normal (v : Point) = 0 →
      IsSymmetricUnder ν (shift v) →
      VectorIsUnitary hS ν v ∧
        TransportsClassesBy hS ν (-v) (opInv (vectorUnitary hS ν v)) := by
    intro v hv hinvv
    have hv' : euclidDot S.normal ((-v : LatticePoint (a : ℝ)) : Point) = 0 := by
      have h₁ : euclidDot S.normal ((-v : LatticePoint (a : ℝ)) : Point) =
          -euclidDot S.normal (v : Point) := by
        change euclidDot S.normal (-(v : Point)) = _
        simp [euclidDot]
      rw [h₁, hv, neg_zero]
    set W := shiftLinear S v (hmapw v hv) with hWdef
    set W' := shiftLinear S (-v) (hmapw (-v) hv') with hW'def
    have hcommv : (shift v).comp (reflectSymmetry hS) =
        (reflectSymmetry hS).comp (shift v) := by
      apply latticeSymmetry_eq_of_toFun
      funext x
      change S.reflect x + (v : Point) = S.reflect (x + (v : Point))
      rw [hrefl, hfix _ hv]
    have hkeepform : ∀ F, upperReflectionForm hS ν (W F) (W F) = upperReflectionForm hS ν F F :=
      fun F => integral_conj_mul_actOn hobs hinvv hcommv (isBoundedObservable_of_mem_local F.2)
        (isBoundedObservable_of_mem_local F.2)
    have hiso : ∀ F, seminormOfForm (upperReflectionForm hS ν) (W F) =
        seminormOfForm (upperReflectionForm hS ν) F := fun F => by
      rw [seminormOfForm, seminormOfForm, hkeepform]
    have hright : ∀ F, W (W' F) = F := by
      intro F
      apply Subtype.ext
      change (shift v).actOn ((shift (-v)).actOn F.1) = F.1
      rw [← actOn_shift_add, add_neg_cancel, actOn_shift_zero]
    obtain ⟨V, hVc, hVu⟩ := exists_unitary_of_seminorm_eq hA hB hC W W' hiso hright
    have hcarV : TransportsClassesBy hS ν v V := fun F => ⟨W F, rfl, hVc F⟩
    have hspec : TransportsClassesBy hS ν v (vectorUnitary hS ν v) ∧
        IsUnitaryMap (vectorUnitary hS ν v :
          MirrorHilbertSpace hS ν →ₗ[ℂ] MirrorHilbertSpace hS ν) :=
      Classical.epsilon_spec (p := fun V : BddOp (MirrorHilbertSpace hS ν) =>
        TransportsClassesBy hS ν v V ∧
          IsUnitaryMap (V : MirrorHilbertSpace hS ν →ₗ[ℂ] MirrorHilbertSpace hS ν))
        ⟨V, hcarV, hVu⟩
    refine ⟨⟨hspec.1, hspec.2, fun V' hV' _ => eq_of_transports hd hV' hspec.1⟩, fun F => ?_⟩
    refine ⟨W' F, rfl, ?_⟩
    obtain ⟨F₂, e₂, b₂⟩ := hspec.1 (W' F)
    have h₁ : F₂ = F := Subtype.ext (e₂.trans (congrArg Subtype.val (hright F)))
    have h₂ : mirrorClass hS ν F =
        vectorUnitary hS ν v (mirrorClass hS ν (W' F)) := by
      rw [b₂, h₁]
    rw [h₂]
    exact DFunLike.congr_fun (isTwoSidedInverse_opInv hspec.2).2 _
  have hcarV : ∀ i, TransportsClassesBy hS ν (w i) (vectorUnitary hS ν (w i)) :=
    fun i => (hunit (w i) (hdotw i) (hinvw i)).1.1
  refine ⟨⟨hinvθ, fun F => ?_⟩, ?_, fun i => (hunit (w i) (hdotw i) (hinvw i)).1, ?_, ?_, ?_⟩
  · change ‖classVec (upperReflectionForm hS ν) F‖ ≤ _
    rw [norm_classVec hA hB]
    have hN : 0 ≤ observableSupNorm F.1 := Real.iSup_nonneg fun _ => norm_nonneg _
    exact Real.sqrt_le_iff.2 ⟨hN, (hform.2 F F).2.2.2⟩
  · refine ⟨hspecT, fun B' hB' => eq_of_transports hd hB' hspecT, ?_, ?_, ?_⟩
    · rw [hTB]
      exact hsa
    · rw [hTB]
      exact h0
    · rw [hTB]
      exact h1
  · intro i
    refine eq_of_transports hd (transports_mul hspecT (hcarV i)) ?_
    rw [add_comm]
    exact transports_mul (hcarV i) hspecT
  · intro i j
    refine eq_of_transports hd (transports_mul (hcarV i) (hcarV j)) ?_
    rw [add_comm]
    exact transports_mul (hcarV j) (hcarV i)
  · intro F F' n y
    obtain ⟨F'', e, b⟩ := transports_mul (transports_pow hspecT n)
      (transports_prod_ofFn (fun i => zpowOp (vectorUnitary hS ν (w i)) (y i))
        (fun i => y i • w i)
        (fun i => transports_zpowOp (hcarV i) (hunit (w i) (hdotw i) (hinvw i)).2 (y i))) F'
    rw [b, hinner]
    change ∫ U, conjFun ((reflectSymmetry hS).actOn F.1) U * F''.1 U ∂ν = _
    rw [e]
end MirrorReconstructionProof
end LatticeConventions
end YangMills.Construction
end
