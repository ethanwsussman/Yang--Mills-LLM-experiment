import YangMills.Construction.Lattice.WilsonActionAsAPlaquetteSumAndSymmetriesOfProductHaarProof
import YangMills.Construction.ReflectionPositivity.ActionInTheDoubledVariablesOfALinkMirror
import YangMills.Construction.ReflectionPositivity.BondsAndPlaquettesAreNotDegenerate
import YangMills.Construction.ReflectionPositivity.DoublingOfTheCrossingVariables
import YangMills.Construction.ReflectionPositivity.PlaquetteActionReadsOneSideOfALinkMirror
import YangMills.Construction.ReflectionPositivity.ReflectionInALinkMirror
import YangMills.Construction.ReflectionPositivity.SpaceOfConfigurationsAndPlaquetteEnergiesAtOneCutoff
import Mathlib
set_option autoImplicit false
open Set Filter
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.DoubledAction
open YangMills.Construction.Matrices
variable {D : MirrorData}
open HalfSpaces
theorem coe_inv_specialUnitary (g : ComplexMatrix2.specialUnitary) :
    (g : ComplexMatrix2)⁻¹ = ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.WilsonPlaquetteSum.coe_inv_specialUnitary <;> assumption
theorem fullTrace_cyclic_rearrange (A B A' B' X Y : ComplexMatrix2.specialUnitary) :
    ComplexMatrix2.fullTrace (((A'⁻¹ * A : ComplexMatrix2.specialUnitary) : ComplexMatrix2) *
        (X : ComplexMatrix2) * ((B'⁻¹ * B : ComplexMatrix2.specialUnitary) : ComplexMatrix2)⁻¹ *
        (Y : ComplexMatrix2)⁻¹) =
      ComplexMatrix2.fullTrace (((A * X * B⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) *
        ((A' * Y * B'⁻¹)⁻¹ : ComplexMatrix2.specialUnitary)) := by
  rw [coe_inv_specialUnitary, coe_inv_specialUnitary]
  have e₁ : ((A'⁻¹ * A : ComplexMatrix2.specialUnitary) : ComplexMatrix2) * (X : ComplexMatrix2) *
      (((B'⁻¹ * B)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) *
      ((Y⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      ((A'⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) *
        ((A * X * B⁻¹ * B' * Y⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := by
    simp only [← Submonoid.coe_mul]
    congr 1
    group
  have e₂ : ((A * X * B⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) *
      (((A' * Y * B'⁻¹)⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
      ((A * X * B⁻¹ * B' * Y⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) *
        ((A'⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := by
    simp only [← Submonoid.coe_mul]
    congr 1
    group
  rw [e₁, e₂, ComplexMatrix2.fullTrace, Matrix.trace_mul_comm]
theorem fullTrace_mul_inv_eq_sum (X : ComplexMatrix2) (Y : ComplexMatrix2.specialUnitary) :
    ComplexMatrix2.fullTrace (X * ((Y⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)) =
      ∑ i : Fin 2, ∑ k : Fin 2, X i k * starRingEnd ℂ ((Y : ComplexMatrix2) i k) := by
  have h : ((Y⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) = star (Y : ComplexMatrix2) := rfl
  rw [h]
  simp only [ComplexMatrix2.fullTrace, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  rfl
theorem norm_entry_le_one (g : ComplexMatrix2.specialUnitary) (i k : Fin 2) :
    ‖(g : ComplexMatrix2) i k‖ ≤ 1 :=
  entry_norm_bound_of_unitary (Matrix.mem_specialUnitaryGroup_iff.1 g.2).1 i k
theorem finsum_mem_eq_fintype_sum {α M : Type*} [AddCommMonoid M] (S : Set α) [Fintype S]
    (f : α → M) : ∑ᶠ p ∈ S, f p = ∑ p : S, f p := by
  rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
theorem symmetry_ext {s s' : D.Symmetry} (h : s.toFun = s'.toFun) : s = s' := by
  obtain ⟨f, h₁, h₂⟩ := s
  obtain ⟨f', h₁', h₂'⟩ := s'
  simp only at h
  subst h
  rfl
theorem hasCoords_fieldOfCoords (C : LinkLevel D) (h : IsHomeomorph C.splitCoords)
    (uPos : C.halfEdges .pos → ComplexMatrix2.specialUnitary)
    (uNeg : C.halfEdges .neg → ComplexMatrix2.specialUnitary)
    (v : C.transversalEdges → ComplexMatrix2.specialUnitary) :
    C.HasCoords (C.fieldOfCoords uPos uNeg v) uPos uNeg v := by
  obtain ⟨U, hU⟩ := h.bijective.2 (uPos, uNeg, v)
  have hex : ∃ U, C.HasCoords U uPos uNeg v :=
    ⟨U, congrArg Prod.fst hU, congrArg (fun x => x.2.1) hU, congrArg (fun x => x.2.2) hU⟩
  exact Classical.epsilon_spec hex
theorem exists_continuous_section (C : LinkLevel D) (h : IsHomeomorph C.splitCoords) :
    ∃ σ : (C.halfEdges .pos → ComplexMatrix2.specialUnitary) → D.FieldSpace, Continuous σ ∧
      ∀ u, C.halfCoords .pos (σ u) = u := by
  let e := h.homeomorph
  refine ⟨fun u => e.symm (u, 1, 1), ?_, ?_⟩
  · exact e.symm.continuous.comp (by fun_prop)
  · intro u
    have h₁ : C.splitCoords (e.symm (u, 1, 1)) = (u, 1, 1) := e.apply_symm_apply _
    exact congrArg Prod.fst h₁
theorem centeredRep_shift_ne (C : LinkLevel D) (hN : PlaquetteNondegeneracy.NondegeneracyStatement)
    (hStep : HeightStep C) (y : D.Vertex) :
    C.centeredRep (shiftBy y D.dir : D.Torus) ≠ C.centeredRep (y : D.Torus) := by
  obtain ⟨-, -, -, hq, h4, -⟩ := (hN D).1
  intro he
  have ha : D.spacing ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hq
    linarith
  by_cases hy : C.centeredRep (y : D.Torus) = C.pos + D.side / 2 - D.spacing / 2
  · have h₁ := hStep.2.2 y hy
    have hs : D.side = D.spacing := by linarith
    rw [hs, div_self ha] at hq
    linarith
  · have h₁ := hStep.2.1 y hy
    exact ha (by linarith)
theorem cornerEdge_not_parallel (C : LinkLevel D)
    (hN : PlaquetteNondegeneracy.NondegeneracyStatement) (hStep : HeightStep C)
    {p : D.Face} (hdir : C.ContainsMirrorAxis p)
    (hsec : C.upperCorner .pos p = shiftBy (C.lowerCorner .pos p) (C.complementaryAxis p))
    (hcb : (C.cornerEdge .pos p).source = C.lowerCorner .pos p ∧
      (C.cornerEdge .pos p).target = C.upperCorner .pos p) :
    ¬(C.cornerEdge .pos p).IsParallelToAxis D.dir := by
  have hne : p.firstAxis ≠ p.secondAxis := ne_of_lt p.firstAxis_lt_secondAxis
  have hν : C.complementaryAxis p ≠ D.dir := by
    unfold LinkLevel.complementaryAxis
    split_ifs with h
    · rw [← h]
      exact hne.symm
    · rcases hdir with h' | h'
      · exact absurd h'.symm h
      · rw [h']
        exact hne
  have hflat := hStep.1 (C.lowerCorner .pos p) (C.complementaryAxis p) hν
  rw [← hsec] at hflat
  rintro (h | h)
  · rw [hcb.1, hcb.2, hsec] at h
    have e : shiftBy (C.lowerCorner .pos p) D.dir = C.upperCorner .pos p := by
      rw [hsec]
      simp only [shiftBy]
      rw [← h]
      abel
    apply centeredRep_shift_ne C hN hStep (C.lowerCorner .pos p)
    rw [e]
    exact hflat
  · rw [hcb.1, hcb.2, hsec] at h
    have e : shiftBy (C.upperCorner .pos p) D.dir = C.lowerCorner .pos p := by
      rw [hsec]
      simp only [shiftBy]
      have h' : PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) D.dir = -(C.lowerCorner .pos p +
          PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) (C.complementaryAxis p) -
            C.lowerCorner .pos p) := by
        rw [h, neg_neg]
      rw [h']
      abel
    apply centeredRep_shift_ne C hN hStep (C.upperCorner .pos p)
    rw [e]
    exact hflat.symm
theorem halfActionFacts (C : LinkLevel D) (hfin : Finite D.Face)
    (hI : HalfFaceEnergy.FaceEnergyEqHalf C)
    (hSum : HalfFaceEnergy.HalfActionEqSum C)
    (hCo : IsHomeomorph C.splitCoords)
    (hRel : ∀ U : D.FieldSpace, C.halfCoords .pos (C.reflectField U) =
      C.transfer (C.halfCoords .neg U))
    (hTop : D.productTopology = (inferInstance : TopologicalSpace D.FieldSpace))
    (hE : ∀ p : D.Face,
      D.ContinuousForProduct
          (fun U : D.FieldSpace => PeriodicLattice.plaquetteCost U.1 p) ∧
        ∀ U : D.FieldSpace, PeriodicLattice.plaquetteCost U.1 p ∈ Icc (0 : ℝ) 2)
    (s₀ : D.Symmetry) (hs₀ : s₀.toFun = C.refl)
    (hImg : MirrorData.Symmetry.faceImage s₀ '' C.halfFaces .pos = C.halfFaces .neg)
    (hInv : Function.Involutive (MirrorData.Symmetry.faceImage s₀))
    (hPull : ∀ U ∈ LinkReflection.gaugeFieldSpace D, ∀ p : D.Face,
      PeriodicLattice.plaquetteCost (MirrorData.Symmetry.pullback s₀ U) p =
        PeriodicLattice.plaquetteCost U (MirrorData.Symmetry.faceImage s₀ p)) :
    HalfActionFacts C := by
  obtain ⟨σ, hσc, hσ⟩ := exists_continuous_section C hCo
  have hval : ∀ p ∈ C.halfFaces .pos, ∀ u,
      C.faceEnergyOfHalf p u = PeriodicLattice.plaquetteCost (σ u).1 p := by
    intro p hp u
    rw [hI p hp (σ u), hσ]
  have hcont : ∀ p ∈ C.halfFaces .pos, Continuous (C.faceEnergyOfHalf p) := by
    intro p hp
    have h₁ : Continuous fun U : D.FieldSpace => PeriodicLattice.plaquetteCost U.1 p := by
      have h := (hE p).1
      unfold MirrorData.ContinuousForProduct at h
      rw [hTop] at h
      exact h
    have e : C.faceEnergyOfHalf p = fun u => PeriodicLattice.plaquetteCost (σ u).1 p :=
      funext (hval p hp)
    rw [e]
    exact h₁.comp hσc
  have hS : (C.halfFaces .pos).Finite := Set.toFinite _
  have hAct : C.halfAction = fun u => ∑ p ∈ hS.toFinset, C.faceEnergyOfHalf p u :=
    funext fun u => finsum_mem_eq_finite_toFinset_sum _ hS
  refine ⟨fun p hp => ⟨hcont p hp, hI p hp⟩, ?_, ?_, ?_⟩
  · rw [hAct]
    exact continuous_finsetSum _ fun p hp => hcont p (hS.mem_toFinset.1 hp)
  · intro u
    rw [hAct]
    refine Finset.sum_nonneg fun p hp => ?_
    rw [hval p (hS.mem_toFinset.1 hp)]
    exact ((hE p).2 (σ u)).1
  · intro s hs U
    obtain rfl : s = s₀ := symmetry_ext (hs.trans hs₀.symm)
    refine ⟨?_, ?_, ?_⟩
    · rw [← hImg, finsum_mem_image hInv.injective.injOn]
    · refine finsum_mem_congr rfl fun p _ => ?_
      rw [C.reflectField_val s hs U]
      exact (hPull U.1 U.2 p).symm
    · rw [← hRel U, hSum]
theorem transversalTrace (C : LinkLevel D) (hN : PlaquetteNondegeneracy.NondegeneracyStatement)
    (hStep : HeightStep C) (hCP : TransversalFaceProperties C) (hCo : IsHomeomorph C.splitCoords) :
    TransversalTrace C := by
  intro p hp uPos uNeg vPos vNeg
  obtain ⟨hdir, hb₁, hb₂, -, -, hsec, hcb, hcP, hcM, hmir, -⟩ := hCP p hp
  have hnp := cornerEdge_not_parallel C hN hStep hdir (hsec .pos) (hcb .pos)
  have hmat : LinkLevel.extendByOne (C.transfer uNeg) (C.cornerEdge .pos p) =
      LinkLevel.extendByOne uNeg (C.cornerEdge .neg p) := by
    unfold LinkLevel.extendByOne
    rw [dif_pos hcP, dif_pos hcM]
    simp only [LinkLevel.transfer]
    rw [if_neg hnp, hmir, LinkLevel.extendByOne, dif_pos hcM]
  have hneg : C.kernelMat p (C.negPoint uNeg vNeg) =
      LinkLevel.extendByOne vNeg (C.lowerEdge p) *
        LinkLevel.extendByOne uNeg (C.cornerEdge .neg p) *
          (LinkLevel.extendByOne vNeg (C.upperEdge p))⁻¹ := by
    change LinkLevel.extendByOne vNeg (C.lowerEdge p) *
      LinkLevel.extendByOne (C.transfer uNeg) (C.cornerEdge .pos p) *
        (LinkLevel.extendByOne vNeg (C.upperEdge p))⁻¹ = _
    rw [hmat]
  have hpos : C.kernelMat p (C.posPoint uPos vPos) =
      LinkLevel.extendByOne vPos (C.lowerEdge p) *
        LinkLevel.extendByOne uPos (C.cornerEdge .pos p) *
          (LinkLevel.extendByOne vPos (C.upperEdge p))⁻¹ := rfl
  refine ⟨hpos, hneg, ?_, ?_⟩
  · obtain ⟨hcP', hcM', hcV⟩ :=
      hasCoords_fieldOfCoords C hCo uPos uNeg (C.transversalQuot vPos vNeg)
    have eP : (C.doubledField uPos uNeg vPos vNeg).1 (C.cornerEdge .pos p) =
        (LinkLevel.extendByOne uPos (C.cornerEdge .pos p) : ComplexMatrix2) := by
      have h := congrArg Subtype.val (congrFun hcP' ⟨_, hcP⟩)
      rw [LinkLevel.extendByOne, dif_pos hcP]
      exact h
    have eM : (C.doubledField uPos uNeg vPos vNeg).1 (C.cornerEdge .neg p) =
        (LinkLevel.extendByOne uNeg (C.cornerEdge .neg p) : ComplexMatrix2) := by
      have h := congrArg Subtype.val (congrFun hcM' ⟨_, hcM⟩)
      rw [LinkLevel.extendByOne, dif_pos hcM]
      exact h
    have eV : ∀ (b : D.Edge) (hb : b ∈ C.transversalEdges),
        C.transversalVariable b (C.doubledField uPos uNeg vPos vNeg) =
          (((LinkLevel.extendByOne vNeg b)⁻¹ * LinkLevel.extendByOne vPos b :
            ComplexMatrix2.specialUnitary) : ComplexMatrix2) := by
      intro b hb
      have h := congrArg Subtype.val (congrFun hcV ⟨b, hb⟩)
      rw [LinkLevel.extendByOne, LinkLevel.extendByOne, dif_pos hb, dif_pos hb]
      exact h
    rw [hpos, hneg]
    unfold LinkLevel.transversalHolonomy
    rw [eP, eM, eV _ hb₁, eV _ hb₂]
    exact fullTrace_cyclic_rearrange _ _ _ _ _ _
  · exact fullTrace_mul_inv_eq_sum _ _
theorem continuous_extendByOne {E : Set D.Edge} (b : D.Edge) :
    Continuous fun g : E → ComplexMatrix2.specialUnitary => LinkLevel.extendByOne g b := by
  by_cases h : b ∈ E
  · have e : (fun g : E → ComplexMatrix2.specialUnitary => LinkLevel.extendByOne g b) =
        fun g => g ⟨b, h⟩ :=
      funext fun g => dif_pos h
    rw [e]
    exact continuous_apply _
  · have e : (fun g : E → ComplexMatrix2.specialUnitary => LinkLevel.extendByOne g b) =
        fun _ => 1 :=
      funext fun g => dif_neg h
    rw [e]
    exact continuous_const
theorem continuous_kernelMat (C : LinkLevel D) (p : D.Face) :
    Continuous (C.kernelMat p) := by
  unfold LinkLevel.kernelMat
  exact (((continuous_extendByOne _).comp continuous_snd).mul
    ((continuous_extendByOne _).comp continuous_fst)).mul
    (((continuous_extendByOne _).comp continuous_snd).inv)
theorem continuous_kernelMat_entry (C : LinkLevel D) (p : D.Face) (i k : Fin 2) :
    Continuous fun ω => (C.kernelMat p ω : ComplexMatrix2) i k :=
  (continuous_subtype_val.comp (continuous_kernelMat C p)).matrix_elem i k
theorem continuous_kernelFn (C : LinkLevel D) (γ : C.KernelLabel) :
    Continuous (C.kernelFn γ) := by
  by_cases h : γ.2.2 = 0
  · have e : C.kernelFn γ = fun ω => (C.kernelMat γ.1.1 ω : ComplexMatrix2) γ.2.1.1 γ.2.1.2 :=
      funext fun ω => if_pos h
    rw [e]
    exact continuous_kernelMat_entry C _ _ _
  · have e : C.kernelFn γ =
        fun ω => starRingEnd ℂ ((C.kernelMat γ.1.1 ω : ComplexMatrix2) γ.2.1.1 γ.2.1.2) :=
      funext fun ω => if_neg h
    rw [e]
    exact Complex.continuous_conj.comp (continuous_kernelMat_entry C _ _ _)
theorem norm_kernelFn_le_one (C : LinkLevel D) (γ : C.KernelLabel) (ω : C.DoubleSpace) :
    ‖C.kernelFn γ ω‖ ≤ 1 := by
  unfold LinkLevel.kernelFn
  split_ifs
  · exact norm_entry_le_one _ _ _
  · rw [RCLike.norm_conj]
    exact norm_entry_le_one _ _ _
theorem transversalFace_term (C : LinkLevel D) (hT : TransversalTrace C)
    (hRe : ∀ p ∈ C.transversalFaces, ∀ U : D.FieldSpace,
      (1 / 2 : ℝ) * (ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy U.1 p)).re =
        (1 / 2 : ℝ) * (ComplexMatrix2.fullTrace (C.transversalHolonomy p U)).re)
    (uPos : C.halfEdges .pos → ComplexMatrix2.specialUnitary)
    (uNeg : C.halfEdges .neg → ComplexMatrix2.specialUnitary)
    (vPos vNeg : C.transversalEdges → ComplexMatrix2.specialUnitary) (p : C.transversalFaces) :
    (((1 / 2 : ℝ) * (ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy
        (C.doubledField uPos uNeg vPos vNeg).1 p.1)).re : ℝ) : ℂ) =
      (1 / 4 : ℂ) * ∑ i : Fin 2, ∑ k : Fin 2, ∑ ε : Fin 2,
        C.kernelFn (p, (i, k), ε) (C.posPoint uPos vPos) *
          starRingEnd ℂ (C.kernelFn (p, (i, k), ε) (C.negPoint uNeg vNeg)) := by
  obtain ⟨-, -, h₃, h₄⟩ := hT p.1 p.2 uPos uNeg vPos vNeg
  rw [hRe p.1 p.2, h₃, h₄]
  set X : ComplexMatrix2 := (C.kernelMat p.1 (C.posPoint uPos vPos) : ComplexMatrix2) with hX
  set Y : ComplexMatrix2 := (C.kernelMat p.1 (C.negPoint uNeg vNeg) : ComplexMatrix2) with hY
  set z : ℂ := ∑ i : Fin 2, ∑ k : Fin 2, X i k * starRingEnd ℂ (Y i k) with hz
  have hzc : ((1 / 2 : ℝ) * z.re : ℝ) = (1 / 2 : ℝ) * z.re := rfl
  have e₁ : (((1 / 2 : ℝ) * z.re : ℝ) : ℂ) = (1 / 4 : ℂ) * (z + starRingEnd ℂ z) := by
    rw [Complex.add_conj]
    push_cast
    ring
  rw [e₁]
  congr 1
  have e₂ : ∀ i k : Fin 2, ∑ ε : Fin 2,
      C.kernelFn (p, (i, k), ε) (C.posPoint uPos vPos) *
        starRingEnd ℂ (C.kernelFn (p, (i, k), ε) (C.negPoint uNeg vNeg)) =
      X i k * starRingEnd ℂ (Y i k) + starRingEnd ℂ (X i k * starRingEnd ℂ (Y i k)) := by
    intro i k
    rw [Fin.sum_univ_two]
    simp [LinkLevel.kernelFn, hX, hY]
  simp only [e₂, Finset.sum_add_distrib, hz, map_sum]
theorem kernelSumIdentity (C : LinkLevel D) (hfin : Finite D.Face) (hT : TransversalTrace C)
    (hRe : ∀ p ∈ C.transversalFaces, ∀ U : D.FieldSpace,
      (1 / 2 : ℝ) * (ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy U.1 p)).re =
        (1 / 2 : ℝ) * (ComplexMatrix2.fullTrace (C.transversalHolonomy p U)).re) :
    KernelSumIdentity C := by
  refine ⟨fun γ => ⟨continuous_kernelFn C γ, norm_kernelFn_le_one C γ⟩, ?_⟩
  intro uPos uNeg vPos vNeg
  classical
  let _ : Fintype C.transversalFaces := Fintype.ofFinite _
  rw [finsum_mem_eq_fintype_sum, finsum_eq_sum_of_fintype, Complex.ofReal_sum]
  simp only [transversalFace_term C hT hRe uPos uNeg vPos vNeg, Fintype.sum_prod_type,
    Finset.mul_sum]
def kernelPairing (C : LinkLevel D) (ω ω' : C.DoubleSpace) : ℂ :=
  ∑ᶠ γ : C.KernelLabel, C.kernelFn γ ω * starRingEnd ℂ (C.kernelFn γ ω')
theorem seriesTerm_eq (C : LinkLevel D) [Fintype C.transversalFaces] (n : ℕ)
    (ω ω' : C.DoubleSpace) :
    C.seriesTerm n ω ω' = ((D.coupling : ℂ) / 4 * kernelPairing C ω ω') ^ n / (n.factorial : ℂ) := by
  classical
  have hprod : ∀ γ : Fin n → C.KernelLabel,
      C.kernelProd γ ω * starRingEnd ℂ (C.kernelProd γ ω') =
        ∏ j, (C.kernelFn (γ j) ω * starRingEnd ℂ (C.kernelFn (γ j) ω')) := by
    intro γ
    simp only [LinkLevel.kernelProd, map_prod, Finset.prod_mul_distrib]
  unfold LinkLevel.seriesTerm LinkLevel.seriesCoeff kernelPairing
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, mul_pow, Fintype.sum_pow]
  simp only [hprod]
  push_cast
  ring
theorem tsum_seriesTerm (C : LinkLevel D) [Fintype C.transversalFaces]
    (ω ω' : C.DoubleSpace) :
    ∑' n : ℕ, C.seriesTerm n ω ω' = Complex.exp ((D.coupling : ℂ) / 4 * kernelPairing C ω ω') := by
  simp only [seriesTerm_eq]
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
theorem norm_kernelPairing_le (C : LinkLevel D) [Fintype C.transversalFaces]
    (ω ω' : C.DoubleSpace) : ‖kernelPairing C ω ω'‖ ≤ (Nat.card C.KernelLabel : ℝ) := by
  classical
  unfold kernelPairing
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ γ ∈ (Finset.univ : Finset C.KernelLabel),
      ‖C.kernelFn γ ω * starRingEnd ℂ (C.kernelFn γ ω')‖ ≤ 1 := by
    intro γ _
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_one₀ (norm_kernelFn_le_one C γ ω) (norm_nonneg _)
      (norm_kernelFn_le_one C γ ω')
  refine (Finset.sum_le_card_nsmul _ _ 1 h).trans ?_
  simp
theorem norm_seriesTerm_le (C : LinkLevel D) [Fintype C.transversalFaces] (n : ℕ)
    (ω ω' : C.DoubleSpace) :
    ‖C.seriesTerm n ω ω'‖ ≤
      (D.coupling * (Nat.card C.KernelLabel : ℝ) / 4) ^ n / (n.factorial : ℝ) := by
  have hβ := D.coupling_pos
  rw [seriesTerm_eq, norm_div, norm_pow, norm_mul, norm_div, Complex.norm_real,
    Real.norm_of_nonneg hβ.le, Complex.norm_natCast]
  have h₁ : ‖(4 : ℂ)‖ = 4 := by simp
  rw [h₁]
  have h₂ : D.coupling / 4 * ‖kernelPairing C ω ω'‖ ≤
      D.coupling * (Nat.card C.KernelLabel : ℝ) / 4 := by
    have h₃ := norm_kernelPairing_le C ω ω'
    have h₄ : D.coupling / 4 * ‖kernelPairing C ω ω'‖ ≤
        D.coupling / 4 * (Nat.card C.KernelLabel : ℝ) :=
      mul_le_mul_of_nonneg_left h₃ (by positivity)
    calc _ ≤ _ := h₄
      _ = _ := by ring
  gcongr
theorem expSeries (C : LinkLevel D) (hfin : Finite D.Face) (hK : KernelSumIdentity C) :
    ExpSeries C := by
  classical
  let _ : Fintype C.transversalFaces := Fintype.ofFinite _
  have hb : ∀ (n : ℕ) (x : C.DoubledCoords),
      ‖C.seriesTerm n (C.posPoint x.1 x.2.2.1) (C.negPoint x.2.1 x.2.2.2)‖ ≤
        (D.coupling * (Nat.card C.KernelLabel : ℝ) / 4) ^ n / (n.factorial : ℝ) :=
    fun n x => norm_seriesTerm_le C n _ _
  refine ⟨?_, tendstoUniformly_tsum_nat (Real.summable_pow_div_factorial _) hb, hb, ?_⟩
  · intro uPos uNeg vPos vNeg
    have hk := hK.2 uPos uNeg vPos vNeg
    rw [tsum_seriesTerm]
    set U := C.doubledField uPos uNeg vPos vNeg with hU
    set K : ℝ := ∑ᶠ p ∈ C.transversalFaces, (1 / 2 : ℝ) *
      (ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy U.1 p)).re with hKdef
    have hS : ∑ᶠ p ∈ C.transversalFaces, PeriodicLattice.plaquetteCost U.1 p =
        (C.transversalFaces.ncard : ℝ) - K := by
      rw [hKdef, finsum_mem_eq_fintype_sum, finsum_mem_eq_fintype_sum, ← Nat.card_coe_set_eq,
        Nat.card_eq_fintype_card]
      simp only [PeriodicLattice.plaquetteCost, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, mul_one]
    have e : -D.coupling * ((C.transversalFaces.ncard : ℝ) - K) =
        -D.coupling * (C.transversalFaces.ncard : ℝ) + D.coupling * K := by ring
    rw [hS, e, Real.exp_add, Complex.ofReal_mul]
    congr 1
    rw [Complex.ofReal_exp, Complex.ofReal_mul, hk]
    have e' : (D.coupling : ℂ) * ((1 / 4 : ℂ) * ∑ᶠ γ : C.KernelLabel,
        C.kernelFn γ (C.posPoint uPos vPos) *
          starRingEnd ℂ (C.kernelFn γ (C.negPoint uNeg vNeg))) =
        (D.coupling : ℂ) / 4 * kernelPairing C (C.posPoint uPos vPos) (C.negPoint uNeg vNeg) := by
      unfold kernelPairing
      ring
    rw [e']
  · intro n
    have hβ := D.coupling_pos
    unfold LinkLevel.seriesCoeff
    positivity
theorem doubledActionProperties_holds (hPlaquette : HalfFaceEnergy.HalfFaceEnergyFacts)
    (hDoubling : DoubledTransversal.DoublingProperties)
    (hGeometry : HalfSpaces.HalfSpaceStructure)
    (hReflection : LinkReflection.LinkReflectionProperties)
    (hSpace : FieldSpaceAndFaceEnergies.Statement)
    (hNondegenerate : PlaquetteNondegeneracy.NondegeneracyStatement) :
    DoubledActionProperties := by
  intro D C
  obtain ⟨-, hI, hSum⟩ := hPlaquette D C
  obtain ⟨-, hCo, -, hRel, -, -, -⟩ := hDoubling D C
  obtain ⟨-, hStep, -, -, -, hCP, -, s₀, hs₀, -, hImg⟩ := hGeometry D C
  obtain ⟨-, s₁, hs₁, -, -, hOnP, -⟩ := hReflection D C
  obtain ⟨hF, -, hE⟩ := hSpace D
  obtain rfl : s₁ = s₀ := symmetry_ext (hs₁.trans hs₀.symm)
  have hfin : Finite D.Face := hF.2.2.1
  have hT : TransversalTrace C := transversalTrace C hNondegenerate hStep hCP hCo.1
  have hRe : ∀ p ∈ C.transversalFaces, ∀ U : D.FieldSpace,
      (1 / 2 : ℝ) * (ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy U.1 p)).re =
        (1 / 2 : ℝ) * (ComplexMatrix2.fullTrace (C.transversalHolonomy p U)).re := by
    intro p hp U
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ := hCP p hp
    exact h U
  have hK : KernelSumIdentity C := kernelSumIdentity C hfin hT hRe
  exact ⟨halfActionFacts C hfin hI hSum hCo.1 hRel.2.2.1 hF.2.2.2.2.2.2.1 hE.1 s₁ hs₁ hImg hOnP.2.1
      hOnP.2.2.2.1, hT, hK, expSeries C hfin hK⟩
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.DoubledAction
end
