import YangMills.Construction.ChessboardTori.BoxAgainstTheTorusProof
import YangMills.Construction.ChessboardTori.TorusAgainstTheFreeBoxProof
import YangMills.Construction.ChessboardTori.BoxAgainstTheTorus
import YangMills.Construction.ChessboardTori.GibbsStateAgainstTheTorusOnABox
import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorus
import YangMills.Construction.InfiniteLattice.ContinuousObservablesAndTheWilsonKernelOfACutoff
import YangMills.Construction.MirrorGridsOfEverySide.BoxAgainstTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set InfiniteLattice
open scoped ComplexOrder
namespace MirrorGridsAllSides.CubeVersusTorus
theorem exists_torusSide_eq_int_mul_mesh (D : GridSetup) :
    ∃ N : ℤ, 2 ≤ N ∧ PeriodicLattice.torusSide D.L D.m = (N : ℝ) * D.mesh := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGrid.exists_torusSide_eq_int_mul_mesh <;> assumption
theorem torusSide_pos (D : GridSetup) : 0 < PeriodicLattice.torusSide D.L D.m := by
  obtain ⟨N, hN2, hN⟩ := exists_torusSide_eq_int_mul_mesh D
  rw [hN]
  have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  exact mul_pos (by linarith) D.mesh_pos
variable {D : GridSetup} {c : AmbientSpace}
theorem mem_cornerCube_iff {x : AmbientSpace} :
    x ∈ D.cornerCube c ↔ ∀ μ, x μ - c μ ∈ Icc 0 (PeriodicLattice.torusSide D.L D.m) := by
  refine forall_congr' fun μ => ?_
  have e : D.side = PeriodicLattice.torusSide D.L D.m := rfl
  rw [e, mem_Icc]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, by linarith⟩
theorem point_sub_corner_ne_int_mul (hc : D.IsDualLatticePoint c) (x : LatticePoint D.mesh) (μ : Fin 4)
    (N : ℤ) : (x : AmbientSpace) μ - c μ ≠ (N : ℝ) * D.mesh := by
  intro h
  obtain ⟨n, hn⟩ := x.2
  obtain ⟨i, hi⟩ := hc μ
  rw [hn μ, hi] at h
  have ha : D.mesh ≠ 0 := D.mesh_pos.ne'
  have h1 : (n μ : ℝ) - ((i : ℝ) + 1 / 2) = (N : ℝ) := by
    apply mul_right_cancel₀ ha
    linarith
  have h2 : ((2 * (n μ - i - N) : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by
    push_cast
    linarith
  have h3 : 2 * (n μ - i - N) = 1 := by exact_mod_cast h2
  omega
theorem point_sub_corner_mem_Ioo (hc : D.IsDualLatticePoint c) {x : LatticePoint D.mesh}
    (h : (x : AmbientSpace) ∈ D.cornerCube c) (μ : Fin 4) :
    (x : AmbientSpace) μ - c μ ∈ Ioo 0 (PeriodicLattice.torusSide D.L D.m) := by
  obtain ⟨h0, h1⟩ := mem_cornerCube_iff.1 h μ
  obtain ⟨N, -, hN⟩ := exists_torusSide_eq_int_mul_mesh D
  refine ⟨lt_of_le_of_ne h0 ?_, lt_of_le_of_ne h1 ?_⟩
  · intro e
    exact point_sub_corner_ne_int_mul hc x μ 0 (by simpa using e.symm)
  · intro e
    exact point_sub_corner_ne_int_mul hc x μ N (by rw [e, hN])
theorem point_mem_interior_cornerCube (hc : D.IsDualLatticePoint c) {x : LatticePoint D.mesh}
    (h : (x : AmbientSpace) ∈ D.cornerCube c) : (x : AmbientSpace) ∈ interior (D.cornerCube c) := by
  have hopen : IsOpen {y : AmbientSpace | ∀ μ, y μ - c μ ∈ Ioo 0 (PeriodicLattice.torusSide D.L D.m)} := by
    have e : {y : AmbientSpace | ∀ μ, y μ - c μ ∈ Ioo 0 (PeriodicLattice.torusSide D.L D.m)} =
        ⋂ μ, (fun y : AmbientSpace => y μ - c μ) ⁻¹' Ioo 0 (PeriodicLattice.torusSide D.L D.m) := by
      ext y
      simp
    rw [e]
    exact isOpen_iInter_of_finite fun μ =>
      isOpen_Ioo.preimage (by fun_prop : Continuous fun y : AmbientSpace => y μ - c μ)
  refine interior_maximal (fun y hy => ?_) hopen (point_sub_corner_mem_Ioo hc h)
  exact mem_cornerCube_iff.2 fun μ => Ioo_subset_Icc_self (hy μ)
theorem isClosed_cornerCube : IsClosed (D.cornerCube c) := by
  have e : D.cornerCube c =
      ⋂ μ, (fun y : AmbientSpace => y μ - c μ) ⁻¹' Icc 0 (PeriodicLattice.torusSide D.L D.m) := by
    ext y
    simp only [mem_iInter, mem_preimage]
    exact mem_cornerCube_iff
  rw [e]
  exact isClosed_iInter fun μ =>
    isClosed_Icc.preimage (by fun_prop : Continuous fun y : AmbientSpace => y μ - c μ)
theorem not_mem_frontier_cornerCube (hc : D.IsDualLatticePoint c) {x : AmbientSpace}
    (hx : x ∈ D.gridPoints) : x ∉ frontier (D.cornerCube c) := by
  intro hf
  have hb : x ∈ D.cornerCube c := isClosed_cornerCube.frontier_subset hf
  exact hf.2 (point_mem_interior_cornerCube (x := ⟨x, hx⟩) hc hb)
theorem eq_of_proj_eq {x y : AmbientSpace}
    (hx : ∀ μ, x μ - c μ ∈ Ioo 0 (PeriodicLattice.torusSide D.L D.m))
    (hy : ∀ μ, y μ - c μ ∈ Ioo 0 (PeriodicLattice.torusSide D.L D.m))
    (h : D.proj x = D.proj y) : x = y := by
  have : Fact (0 < PeriodicLattice.torusSide D.L D.m) := ⟨torusSide_pos D⟩
  funext μ
  have hμ : ((x μ : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) =
      ((y μ : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) := congrFun h μ
  have hx' := hx μ
  have hy' := hy μ
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := c μ)
    ⟨by linarith [hx'.1], by linarith [hx'.2]⟩ ⟨by linarith [hy'.1], by linarith [hy'.2]⟩).mp hμ
theorem point_eq_of_projectPoint_eq (hc : D.IsDualLatticePoint c) {x y : LatticePoint D.mesh}
    (hx : (x : AmbientSpace) ∈ D.cornerCube c) (hy : (y : AmbientSpace) ∈ D.cornerCube c)
    (h : projectPoint D.L D.m ((D.K : ℕ) : ℤ) x = projectPoint D.L D.m ((D.K : ℕ) : ℤ) y) : x = y :=
  Subtype.ext (eq_of_proj_eq (point_sub_corner_mem_Ioo hc hx) (point_sub_corner_mem_Ioo hc hy)
    (congrArg Subtype.val h))
theorem exists_lift_mem_cornerCube {y : D.Torus}
    (hy : y ∈ PeriodicLattice.sublattice D.L D.m ((D.K : ℕ) : ℤ)) :
    ∃ x ∈ (D.gridPoints : Set AmbientSpace) ∩ D.cornerCube c, D.proj x = y := by
  obtain ⟨n, hn⟩ := hy
  obtain ⟨N, -, hN⟩ := exists_torusSide_eq_int_mul_mesh D
  have hpos := torusSide_pos D
  have : Fact (0 < PeriodicLattice.torusSide D.L D.m) := ⟨hpos⟩
  let k : Fin 4 → ℤ := fun μ => ⌈(c μ - (n μ : ℝ) * D.mesh) / PeriodicLattice.torusSide D.L D.m⌉
  refine ⟨fun μ => ((n μ + N * k μ : ℤ) : ℝ) * D.mesh, ⟨⟨fun μ => n μ + N * k μ, fun _ => rfl⟩, ?_⟩, ?_⟩
  · refine mem_cornerCube_iff.2 fun μ => ?_
    have e : ((n μ + N * k μ : ℤ) : ℝ) * D.mesh =
        (n μ : ℝ) * D.mesh + (k μ : ℝ) * PeriodicLattice.torusSide D.L D.m := by
      rw [hN]
      push_cast
      ring
    have h₁ : (c μ - (n μ : ℝ) * D.mesh) / PeriodicLattice.torusSide D.L D.m ≤ (k μ : ℝ) :=
      Int.le_ceil _
    have h₂ : (k μ : ℝ) < (c μ - (n μ : ℝ) * D.mesh) / PeriodicLattice.torusSide D.L D.m + 1 :=
      Int.ceil_lt_add_one _
    rw [div_le_iff₀ hpos] at h₁
    have h₃ : (k μ : ℝ) * PeriodicLattice.torusSide D.L D.m <
        ((c μ - (n μ : ℝ) * D.mesh) / PeriodicLattice.torusSide D.L D.m + 1) *
          PeriodicLattice.torusSide D.L D.m := mul_lt_mul_of_pos_right h₂ hpos
    rw [add_mul, div_mul_cancel₀ _ hpos.ne', one_mul] at h₃
    simp only [mem_Icc]
    rw [e]
    constructor <;> linarith
  · funext μ
    have e : ((n μ + N * k μ : ℤ) : ℝ) * D.mesh =
        (n μ : ℝ) * D.mesh + k μ • PeriodicLattice.torusSide D.L D.m := by
      rw [hN, zsmul_eq_mul]
      push_cast
      ring
    have h0 : (((k μ • PeriodicLattice.torusSide D.L D.m : ℝ)) :
        AddCircle (PeriodicLattice.torusSide D.L D.m)) = 0 :=
      (AddCircle.coe_eq_zero_iff _).mpr ⟨k μ, rfl⟩
    show (((((n μ + N * k μ : ℤ) : ℝ) * D.mesh : ℝ)) : AddCircle (PeriodicLattice.torusSide D.L D.m)) = y μ
    rw [e, AddCircle.coe_add, h0, add_zero, hn μ]
    rfl
theorem bijOn_proj (hc : D.IsDualLatticePoint c) :
    BijOn D.proj ((D.gridPoints : Set AmbientSpace) ∩ D.cornerCube c)
      (PeriodicLattice.sublattice D.L D.m ((D.K : ℕ) : ℤ) : Set D.Torus) := by
  refine ⟨fun x hx => (projectPoint D.L D.m ((D.K : ℕ) : ℤ) ⟨x, hx.1⟩).2, ?_, ?_⟩
  · intro x hx y hy h
    exact eq_of_proj_eq (point_sub_corner_mem_Ioo (x := ⟨x, hx.1⟩) hc hx.2)
      (point_sub_corner_mem_Ioo (x := ⟨y, hy.1⟩) hc hy.2) h
  · intro y hy
    exact exists_lift_mem_cornerCube hy
theorem mem_positiveLinksWithin_of_mem_boxLinks {B : Set AmbientSpace} {b : D.Link}
    (h : b ∈ D.boxLinks B) : b ∈ positiveLinksWithin D.mesh B := by apply _root_.YangMills.Construction.ChessboardTori.TorusVersusFreeBox.mem_positiveLinksWithin_of_mem_boxLinks <;> assumption
theorem injOn_projLink (hc : D.IsDualLatticePoint c) :
    InjOn D.projLink (D.cornerCubeLinks c : Set D.Link) := by
  intro b hb b' hb' h
  have h₁ := mem_positiveLinksWithin_of_mem_boxLinks (Finset.mem_coe.1 hb)
  have h₂ := mem_positiveLinksWithin_of_mem_boxLinks (Finset.mem_coe.1 hb')
  exact Link.ext (point_eq_of_projectPoint_eq hc h₁.2.1 h₂.2.1 (congrArg PeriodicLattice.Bond.source h))
    (point_eq_of_projectPoint_eq hc h₁.2.2 h₂.2.2 (congrArg PeriodicLattice.Bond.target h))
def cornerGrid (D : GridSetup) {c : AmbientSpace} (hc : D.IsDualLatticePoint c) :
    ChessboardTori.ReflectionGrid D :=
  ⟨0, by have : 0 < (D.K : ℕ) := D.K.pos
         omega, c, hc⟩
theorem cornerGrid_isCoarse (hc : D.IsDualLatticePoint c) : (cornerGrid D hc).IsCoarse :=
  le_refl (0 : ℤ)
theorem two_mul_cellSide_cornerGrid_le (hc : D.IsDualLatticePoint c) :
    2 * (cornerGrid D hc).cellSide ≤ PeriodicLattice.torusSide D.L D.m := by
  have hL : (1 : ℝ) ≤ D.L := D.one_lt_factor.le
  have e : (cornerGrid D hc).cellSide = 1 := by
    simp [ChessboardTori.ReflectionGrid.cellSide, cornerGrid]
  rw [e, PeriodicLattice.torusSide]
  have : (1 : ℝ) ≤ (D.L : ℝ) ^ (D.m : ℕ) := one_le_pow₀ hL
  linarith
theorem fundamentalBlock_cornerGrid (hc : D.IsDualLatticePoint c) :
    (cornerGrid D hc).fundamentalBlock = D.cornerCube c := by
  rw [ChessboardTori.ReflectionGrid.fundamentalBlock_eq]
  ext x
  exact mem_cornerCube_iff.symm
theorem positiveLinksWithin_interior (hc : D.IsDualLatticePoint c) :
    positiveLinksWithin D.mesh (cornerGrid D hc).fundamentalBlockInterior =
      positiveLinksWithin D.mesh (D.cornerCube c) := by
  have e : (cornerGrid D hc).fundamentalBlockInterior = interior (D.cornerCube c) := by
    rw [ChessboardTori.ReflectionGrid.fundamentalBlockInterior, fundamentalBlock_cornerGrid]
  rw [e]
  ext b
  constructor
  · rintro ⟨hb, h₁, h₂⟩
    exact ⟨hb, interior_subset h₁, interior_subset h₂⟩
  · rintro ⟨hb, h₁, h₂⟩
    exact ⟨hb, point_mem_interior_cornerCube hc h₁, point_mem_interior_cornerCube hc h₂⟩
theorem interiorLinks_cornerGrid (hc : D.IsDualLatticePoint c) :
    (cornerGrid D hc).openBlockLinks = D.cornerCubeLinks c := by
  have h := positiveLinksWithin_interior hc
  show D.boxLinks _ = D.boxLinks _
  by_cases hf : (positiveLinksWithin D.mesh (D.cornerCube c)).Finite
  · apply Finset.coe_injective
    rw [D.coe_boxLinks (h ▸ hf), D.coe_boxLinks hf, h]
  · have hf' : ¬ (positiveLinksWithin D.mesh (cornerGrid D hc).fundamentalBlockInterior).Finite :=
      h ▸ hf
    simp [ChessboardTori.ChessboardSetup.boxLinks, hf, hf']
theorem isRegionMeasurable_interior
    (hObs : ChessboardTori.MeasurableObservablesAndLifts.Statement)
    (hc : D.IsDualLatticePoint c) {F : D.GaugeField → ℂ}
    (hF : D.IsBoundedMeasurableInLinks (D.cornerCubeLinks c) F) :
    IsRegionMeasurable (cornerGrid D hc).fundamentalBlockInterior F := by
  have hobs := hF.isBoundedObservable
  obtain ⟨Φ, ⟨hΦ, C, hC⟩, rfl⟩ := hF
  have hsub : ∀ b : ((D.cornerCubeLinks c : Finset D.Link) : Set D.Link),
      (b : D.Link) ∈ D.positiveLinksOn (cornerGrid D hc).fundamentalBlockInterior := fun b => by
    have := mem_positiveLinksWithin_of_mem_boxLinks (Finset.mem_coe.1 b.2)
    rw [← positiveLinksWithin_interior hc] at this
    exact this
  refine ((hObs D).2.1 _ _ hobs).2
    ⟨fun V => Φ fun b => V ⟨b, hsub b⟩, ?_, ⟨C, fun V => hC _⟩, fun U => rfl⟩
  have hcont : Continuous fun V : LinkVariables
      (D.positiveLinksOn (cornerGrid D hc).fundamentalBlockInterior) =>
      (fun b => V ⟨b, hsub b⟩ :
        LinkVariables ((D.cornerCubeLinks c : Finset D.Link) : Set D.Link)) :=
    continuous_pi fun b => continuous_apply _
  let m₁ : MeasurableSpace (LinkVariables
    (D.positiveLinksOn (cornerGrid D hc).fundamentalBlockInterior)) := borel _
  have : BorelSpace (LinkVariables
    (D.positiveLinksOn (cornerGrid D hc).fundamentalBlockInterior)) := ⟨rfl⟩
  let m₂ : MeasurableSpace (LinkVariables
    ((D.cornerCubeLinks c : Finset D.Link) : Set D.Link)) := borel _
  have : BorelSpace (LinkVariables
    ((D.cornerCubeLinks c : Finset D.Link) : Set D.Link)) := ⟨rfl⟩
  exact hΦ.comp hcont.measurable
theorem kernelIntegral_eq_wilsonKernelAt (D : GridSetup) {E : Finset D.Link}
    (hE : (E : Set D.Link) ⊆ positiveLinkSet D.mesh) (A : D.GaugeField → ℂ)
    (ξ : D.GaugeField) :
    D.kernelIntegral hE A ξ = ChessboardTori.ChessboardSetup.wilsonKernelAt D E hE A ξ := by
  have hs : ∀ V : E → Matrices.ComplexMatrix2.specialUnitary,
      GibbsEquivalences.glueOnLinks D.mesh_pos E hE ξ V = D.splice hE V ξ := by
    intro V
    refine WilsonOperator.eq_splice D.mesh_pos hE V ξ _ (fun b => ?_) (fun b hb => ?_)
    · exact CutoffStates.glueOnLinks_apply_of_mem D.mesh_pos hE ξ V b
    · exact CutoffStates.glueOnLinks_apply_of_not_mem D.mesh_pos hE ξ V
        (fun h => hb.2 (Finset.mem_coe.2 h))
        (fun hr => opposite_notMem_positiveLinks D.mesh_pos hb.1 (hE (Finset.mem_coe.2 hr)))
  have h := CutoffStates.specKernel_eq_integral_wilsonSpecification D.mesh_pos D.β hE A ξ
  simp only [hs] at h
  exact h.symm
theorem integral_nonneg_of_complex_nonneg {X : Type*} [MeasurableSpace X] (P : Measure X)
    {f : X → ℂ} (h : ∀ x, 0 ≤ f x) : 0 ≤ ∫ x, f x ∂P := by
  have e : ∀ x, f x = (((f x).re : ℝ) : ℂ) := fun x =>
    Complex.ext rfl (by simpa using ((Complex.le_def.1 (h x)).2).symm)
  have hi : ∫ x, f x ∂P = ((∫ x, (f x).re ∂P : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (ae_of_all _ e)
  rw [hi]
  exact Complex.zero_le_real.2 (integral_nonneg fun x => by
    simpa using (Complex.le_def.1 (h x)).1)
theorem surfaceExponent_le (D : GridSetup) :
    2 * D.β * ((Constants.SurfaceTerms.plaquetteCount : ℝ) *
        (PeriodicLattice.torusSide D.L D.m / D.mesh) ^ 3) ≤
      cubeComparisonConstant * D.β * (D.side / D.mesh) ^ 3 := by
  have e : D.side = PeriodicLattice.torusSide D.L D.m := rfl
  have hq : 0 ≤ (PeriodicLattice.torusSide D.L D.m / D.mesh) ^ 3 :=
    pow_nonneg (div_nonneg (torusSide_pos D).le D.mesh_pos.le) 3
  have hβ := D.beta_pos
  have hprod := mul_nonneg hβ.le hq
  rw [e]
  simp only [cubeComparisonConstant, Constants.SurfaceTerms.plaquetteCount]
  push_cast
  nlinarith
theorem statement_holds (hBox : ChessboardTori.BoxTorusComparison.Statement)
    (hState : ChessboardTori.GibbsBoundByTorusOnBlock.Statement)
    (hObs : ChessboardTori.MeasurableObservablesAndLifts.Statement) :
    Statement := by
  intro D c hc
  have hg := cornerGrid_isCoarse hc
  have hside := two_mul_cellSide_cornerGrid_le hc
  refine ⟨⟨fun x hx => not_mem_frontier_cornerCube hc hx, bijOn_proj hc, ?_, injOn_projLink hc⟩,
    ?_, ?_⟩
  · intro b hb
    exact D.projLink_isPositivelyOriented
      (mem_positiveLinks_iff.1 (D.cornerCubeLinks_subset_positiveLinks c hb))
  · intro P hP hP0 ξ
    have hobs := hP.isBoundedObservable
    obtain ⟨hcount, hcmp⟩ := hBox D (cornerGrid D hc) hg hside
    have h := hcmp P hobs (isRegionMeasurable_interior hObs hc hP) hP0 ξ
    have hlinks : ∀ (E E' : Finset D.Link) (e : E = E')
        (h₁ : (E : Set D.Link) ⊆ positiveLinkSet D.mesh)
        (h₂ : (E' : Set D.Link) ⊆ positiveLinkSet D.mesh),
        ChessboardTori.ChessboardSetup.wilsonKernelAt D E h₁ P ξ =
          ChessboardTori.ChessboardSetup.wilsonKernelAt D E' h₂ P ξ := by
      rintro E _ rfl _ _
      rfl
    rw [kernelIntegral_eq_wilsonKernelAt, ← hlinks _ _ (interiorLinks_cornerGrid hc)
      (D.coe_boxLinks_subset_positive _)]
    refine h.trans ?_
    have hE : 0 ≤ D.expect (D.liftedObservable P) :=
      integral_nonneg_of_complex_nonneg _ fun U => hP0 _
    refine mul_le_mul_of_nonneg_right ?_ hE
    refine Complex.real_le_real.2 (Real.exp_le_exp.2 ?_)
    exact (mul_le_mul_of_nonneg_left hcount (by linarith [D.beta_pos])).trans (surfaceExponent_le D)
  · intro ν hν H hH
    have hobs := hH.isBoundedObservable
    have h := hState D (cornerGrid D hc) hg hside ν hν (fun U => (H U : ℂ)) hobs
      (fun U => Complex.ofReal_im _) (isRegionMeasurable_interior hObs hc hH)
    have hl : (∫ U, (H U : ℂ) ∂ν).re = ∫ U, H U ∂ν := by
      rw [integral_complex_ofReal, Complex.ofReal_re]
    have hr : (D.periodicExpectation (D.liftedObservable fun U => Complex.exp (H U : ℂ))).re =
        D.expect ((fun U => Real.exp (H U)) ∘ D.liftField) := by
      have e : D.periodicExpectation (D.liftedObservable fun U => Complex.exp (H U : ℂ)) =
          ((D.expect ((fun U => Real.exp (H U)) ∘ D.liftField) : ℝ) : ℂ) := by
        simp only [ChessboardTori.ChessboardSetup.periodicExpectation, GridSetup.expect,
          PeriodicLattice.gibbsExpectation, ChessboardTori.ChessboardSetup.liftedObservable,
          Function.comp_apply]
        rw [← integral_complex_ofReal]
        simp only [Complex.ofReal_exp]
      rw [e, Complex.ofReal_re]
    rw [hl, hr] at h
    have hc2 : (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
        (PeriodicLattice.torusSide D.L D.m / D.mesh) ^ 3 ≤
        cubeComparisonConstant * D.β * (D.side / D.mesh) ^ 3 := by
      have := surfaceExponent_le D
      have hs : (Constants.SurfaceTerms.surfaceFactor : ℝ) =
          2 * (Constants.SurfaceTerms.plaquetteCount : ℝ) := by
        simp [Constants.SurfaceTerms.surfaceFactor]
      rw [hs]
      linarith
    linarith
end MirrorGridsAllSides.CubeVersusTorus
end YangMills.Construction
end
