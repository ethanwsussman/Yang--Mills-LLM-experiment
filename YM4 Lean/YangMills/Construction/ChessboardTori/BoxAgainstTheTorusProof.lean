import YangMills.Construction.ChessboardTori.BoxAgainstTheTorus
import YangMills.Construction.ChessboardTori.BoxAgainstTheTorusThroughFreeBoundaryConditions
import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorus
import YangMills.Construction.InfiniteLattice.SitesLinksAndPlaquettesOfTheLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice Set
open scoped ComplexOrder
namespace ChessboardTori
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
theorem exists_torusSide_eq_int_mul_mesh :
    ∃ N : ℤ, 2 ≤ N ∧ PeriodicLattice.torusSide D.L D.m = (N : ℝ) * D.mesh := by
  have hL1 : 1 ≤ D.L := by
    have := D.one_lt_factor
    have h : (0 : ℝ) < D.L := by linarith
    exact_mod_cast h
  refine ⟨2 * (D.L : ℤ) ^ ((D.m : ℕ) + (D.K : ℕ)), ?_, ?_⟩
  · have : (1 : ℤ) ≤ (D.L : ℤ) ^ ((D.m : ℕ) + (D.K : ℕ)) :=
      one_le_pow₀ (by exact_mod_cast hL1)
    linarith
  · simp only [PeriodicLattice.torusSide, ChessboardSetup.mesh, PeriodicLattice.meshSize]
    push_cast
    rw [zpow_neg, pow_add, zpow_natCast]
    field_simp
theorem coord_sub_origin_ne_int_mul (x : LatticePoint D.mesh) (μ : Fin 4) (N : ℤ) :
    (x : AmbientSpace) μ - g.origin μ ≠ (N : ℝ) * D.mesh := by
  intro h
  obtain ⟨n, hn⟩ := x.2
  obtain ⟨i, hi⟩ := g.origin_mem μ
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
theorem coord_sub_origin_mem_Ioo {x : LatticePoint D.mesh}
    (h : (x : AmbientSpace) ∈ g.fundamentalBlock) (μ : Fin 4) :
    (x : AmbientSpace) μ - g.origin μ ∈ Ioo 0 (PeriodicLattice.torusSide D.L D.m) := by
  rw [g.fundamentalBlock_eq] at h
  obtain ⟨h0, h1⟩ := h μ
  obtain ⟨N, -, hN⟩ := exists_torusSide_eq_int_mul_mesh (D := D)
  refine ⟨lt_of_le_of_ne h0 ?_, lt_of_le_of_ne h1 ?_⟩
  · intro e
    exact g.coord_sub_origin_ne_int_mul x μ 0 (by simpa using e.symm)
  · intro e
    exact g.coord_sub_origin_ne_int_mul x μ N (by rw [e, hN])
theorem mem_interior_of_mem_fundamentalBlock {x : LatticePoint D.mesh}
    (h : (x : AmbientSpace) ∈ g.fundamentalBlock) :
    (x : AmbientSpace) ∈ g.fundamentalBlockInterior := by
  have hopen : IsOpen {y : AmbientSpace |
      ∀ μ, y μ - g.origin μ ∈ Ioo 0 (PeriodicLattice.torusSide D.L D.m)} := by
    have e : {y : AmbientSpace |
        ∀ μ, y μ - g.origin μ ∈ Ioo 0 (PeriodicLattice.torusSide D.L D.m)} =
        ⋂ μ, (fun y : AmbientSpace => y μ - g.origin μ) ⁻¹'
          Ioo 0 (PeriodicLattice.torusSide D.L D.m) := by
      ext y
      simp
    rw [e]
    exact isOpen_iInter_of_finite fun μ =>
      isOpen_Ioo.preimage (by fun_prop : Continuous fun y : AmbientSpace => y μ - g.origin μ)
  refine interior_maximal (fun y hy => ?_) hopen (g.coord_sub_origin_mem_Ioo h)
  rw [g.fundamentalBlock_eq]
  exact fun μ => Ioo_subset_Icc_self (hy μ)
theorem positiveLinksWithin_interior :
    positiveLinksWithin D.mesh g.fundamentalBlockInterior =
      positiveLinksWithin D.mesh g.fundamentalBlock := by
  ext b
  constructor
  · rintro ⟨hb, h₁, h₂⟩
    exact ⟨hb, interior_subset h₁, interior_subset h₂⟩
  · rintro ⟨hb, h₁, h₂⟩
    exact ⟨hb, g.mem_interior_of_mem_fundamentalBlock h₁,
      g.mem_interior_of_mem_fundamentalBlock h₂⟩
theorem interiorLinks_eq_boxLinks : g.openBlockLinks = D.boxLinks g.fundamentalBlock := by
  have h := g.positiveLinksWithin_interior
  by_cases hf : (positiveLinksWithin D.mesh g.fundamentalBlock).Finite
  · apply Finset.coe_injective
    rw [openBlockLinks, D.coe_boxLinks (h ▸ hf), D.coe_boxLinks hf, h]
  · have hf' : ¬ (positiveLinksWithin D.mesh g.fundamentalBlockInterior).Finite := h ▸ hf
    simp [openBlockLinks, ChessboardSetup.boxLinks, hf, hf']
theorem mem_boxLinks_iff (hfin : (positiveLinksWithin D.mesh g.fundamentalBlock).Finite)
    {b : D.Link} : b ∈ D.boxLinks g.fundamentalBlock ↔
      b ∈ positiveLinksWithin D.mesh g.fundamentalBlock := by
  rw [← Finset.mem_coe, D.coe_boxLinks hfin]
theorem facesLeavingInterior_eq
    (hfin : (positiveLinksWithin D.mesh g.fundamentalBlock).Finite)
    (hends : ∀ p : D.Plaquette, ∀ b ∈ p.edges, b.initial ∈ p.cornerSet ∧ b.terminal ∈ p.cornerSet) :
    g.facesLeavingInterior =
      {p : D.Plaquette | (∃ b ∈ p.edges, b ∈ D.boxLinks g.fundamentalBlock) ∧
        ∃ b ∈ p.edges, b ∉ D.boxLinks g.fundamentalBlock} := by
  ext p
  simp only [facesLeavingInterior, mem_ofPred_eq, g.interiorLinks_eq_boxLinks]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨c, hc, hcO⟩
    by_contra hall
    push Not at hall
    have hin : ∀ b ∈ p.edges, ((b.initial : LatticePoint D.mesh) : AmbientSpace) ∈ g.fundamentalBlock ∧
        ((b.terminal : LatticePoint D.mesh) : AmbientSpace) ∈ g.fundamentalBlock := fun b hb =>
      ((g.mem_boxLinks_iff hfin).mp (hall b hb)).2
    apply hcO
    simp only [ElementaryPlaquette.cornerSet, mem_insert_iff, mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact g.mem_interior_of_mem_fundamentalBlock
        (hin (Link.forwardFrom p.corner p.lowAxis) (by simp [ElementaryPlaquette.edges])).1
    · exact g.mem_interior_of_mem_fundamentalBlock
        (hin (Link.forwardFrom p.corner p.lowAxis) (by simp [ElementaryPlaquette.edges])).2
    · exact g.mem_interior_of_mem_fundamentalBlock
        (hin (Link.forwardFrom (p.corner + axisStep D.mesh p.lowAxis) p.highAxis)
          (by simp [ElementaryPlaquette.edges])).2
    · exact g.mem_interior_of_mem_fundamentalBlock
        (hin (Link.forwardFrom p.corner p.highAxis) (by simp [ElementaryPlaquette.edges])).2
  · rintro ⟨b, hb, hbn⟩
    by_contra hall
    push Not at hall
    apply hbn
    rw [g.mem_boxLinks_iff hfin]
    exact ⟨WilsonOperator.mem_positiveLinks_of_mem_edgeList p hb,
      interior_subset (hall _ (hends p b hb).1), interior_subset (hall _ (hends p b hb).2)⟩
theorem projectPoint_add (x y : LatticePoint D.mesh) :
    projectPoint D.L D.m ((D.K : ℕ) : ℤ) (x + y) =
      projectPoint D.L D.m ((D.K : ℕ) : ℤ) x + projectPoint D.L D.m ((D.K : ℕ) : ℤ) y :=
  Subtype.ext (funext fun μ => by simp [projectPoint, TorusMetric.torusProj])
theorem projLink_forwardFrom (x : LatticePoint D.mesh) (μ : Fin 4) :
    D.projLink (Link.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom (projectPoint D.L D.m ((D.K : ℕ) : ℤ) x) μ :=
  PeriodicLattice.Bond.ext rfl (by
    change projectPoint D.L D.m ((D.K : ℕ) : ℤ) (x + axisStep D.mesh μ) = _ + _
    rw [projectPoint_add]
    exact congrArg _ (projectPoint_axisStep D.L D.m ((D.K : ℕ) : ℤ) μ))
theorem projectPoint_injOn {x y : LatticePoint D.mesh} (hx : (x : AmbientSpace) ∈ g.fundamentalBlock)
    (hy : (y : AmbientSpace) ∈ g.fundamentalBlock)
    (h : projectPoint D.L D.m ((D.K : ℕ) : ℤ) x = projectPoint D.L D.m ((D.K : ℕ) : ℤ) y) :
    x = y := by
  obtain ⟨N, hN2, hN⟩ := exists_torusSide_eq_int_mul_mesh (D := D)
  have hpos : 0 < PeriodicLattice.torusSide D.L D.m := by
    rw [hN]
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    exact mul_pos (by linarith) D.mesh_pos
  have : Fact (0 < PeriodicLattice.torusSide D.L D.m) := ⟨hpos⟩
  refine Subtype.ext (funext fun μ => ?_)
  have hμ : (((x : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) =
      (((y : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) :=
    congrFun (congrArg Subtype.val h) μ
  have hx' := g.coord_sub_origin_mem_Ioo hx μ
  have hy' := g.coord_sub_origin_mem_Ioo hy μ
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := g.origin μ)
    ⟨by linarith [hx'.1], by linarith [hx'.2]⟩ ⟨by linarith [hy'.1], by linarith [hy'.2]⟩).mp hμ
theorem unitStep_injective {μ ν : Fin 4}
    (h : PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) μ =
      PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) ν) : μ = ν := by
  by_contra hne
  obtain ⟨N, hN2, hN⟩ := exists_torusSide_eq_int_mul_mesh (D := D)
  have ha := D.mesh_pos
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hpos : 0 < PeriodicLattice.torusSide D.L D.m := by
    rw [hN]
    exact mul_pos (by linarith) ha
  have : Fact (0 < PeriodicLattice.torusSide D.L D.m) := ⟨hpos⟩
  have h1 : ((D.mesh : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) = 0 := by
    have := congrFun (congrArg Subtype.val h) μ
    simpa [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hne,
      ChessboardSetup.mesh] using this
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).mp h1
  rw [zsmul_eq_mul, hN] at hk
  have hk' : (k : ℝ) * (N : ℝ) = 1 := by
    apply mul_right_cancel₀ ha.ne'
    linarith
  have hk'' : k * N = 1 := by exact_mod_cast hk'
  have : N ∣ 1 := ⟨k, by rw [mul_comm]; exact hk''.symm⟩
  have := Int.le_of_dvd one_pos this
  omega
theorem exists_forwardFrom_of_projLink_eq
    (hfin : (positiveLinksWithin D.mesh g.fundamentalBlock).Finite) {b : D.Link}
    (hb : b ∈ D.boxLinks g.fundamentalBlock)
    {y : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ)} {μ : Fin 4}
    (h : D.projLink b = PeriodicLattice.Bond.forwardFrom y μ) :
    ∃ x : LatticePoint D.mesh, b = Link.forwardFrom x μ ∧
      projectPoint D.L D.m ((D.K : ℕ) : ℤ) x = y ∧
      (x : AmbientSpace) ∈ g.fundamentalBlock ∧
      ((x + axisStep D.mesh μ : LatticePoint D.mesh) : AmbientSpace) ∈ g.fundamentalBlock := by
  obtain ⟨⟨x, κ, rfl⟩, h₁, h₂⟩ := (g.mem_boxLinks_iff hfin).mp hb
  rw [projLink_forwardFrom] at h
  have ht : projectPoint D.L D.m ((D.K : ℕ) : ℤ) x = y := congrArg PeriodicLattice.Bond.source h
  subst ht
  have hh := congrArg PeriodicLattice.Bond.target h
  have hs : PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) κ =
      PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) μ := add_left_cancel hh
  obtain rfl := unitStep_injective (D := D) hs
  exact ⟨x, rfl, rfl, h₁, h₂⟩
theorem facesCrossingBoundary_eq
    (hfin : (positiveLinksWithin D.mesh g.fundamentalBlock).Finite) :
    g.facesCrossingBoundary =
      {q : PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ) |
        ¬ ∃ p ∈ D.interiorPlaquettes g.fundamentalBlock,
          CutoffLattice.projectFace D.L D.m D.K p = q} := by
  ext q
  simp only [facesCrossingBoundary, mem_ofPred_eq, g.interiorLinks_eq_boxLinks]
  constructor
  · rintro ⟨b, hb, hnot⟩ ⟨p, hp, rfl⟩
    have hex : ∃ b₀ ∈ p.edges, D.projLink b₀ = b := by
      simp only [WilsonOperator.periodicEdgeList, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact ⟨Link.forwardFrom p.corner p.lowAxis, by simp [ElementaryPlaquette.edges],
          projLink_forwardFrom _ _⟩
      · refine ⟨Link.forwardFrom (p.corner + axisStep D.mesh p.lowAxis) p.highAxis,
          by simp [ElementaryPlaquette.edges], ?_⟩
        rw [projLink_forwardFrom, projectPoint_add]
        exact congrArg (fun z => PeriodicLattice.Bond.forwardFrom (_ + z) _)
          (projectPoint_axisStep D.L D.m ((D.K : ℕ) : ℤ) p.lowAxis)
      · refine ⟨Link.forwardFrom (p.corner + axisStep D.mesh p.highAxis) p.lowAxis,
          by simp [ElementaryPlaquette.edges], ?_⟩
        rw [projLink_forwardFrom, projectPoint_add]
        exact congrArg (fun z => PeriodicLattice.Bond.forwardFrom (_ + z) _)
          (projectPoint_axisStep D.L D.m ((D.K : ℕ) : ℤ) p.highAxis)
      · exact ⟨Link.forwardFrom p.corner p.highAxis, by simp [ElementaryPlaquette.edges],
          projLink_forwardFrom _ _⟩
    obtain ⟨b₀, hb₀, rfl⟩ := hex
    exact hnot b₀ (hp b₀ hb₀) rfl
  · intro hno
    by_contra hcross
    push Not at hcross
    apply hno
    have hc := fun b hb => hcross b hb
    simp only [WilsonOperator.periodicEdgeList, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hc
    obtain ⟨⟨b₁, m₁, e₁⟩, ⟨b₂, m₂, e₂⟩, ⟨b₃, m₃, e₃⟩, ⟨b₄, m₄, e₄⟩⟩ := hc
    obtain ⟨x, rfl, hx, hxB, hxμ⟩ := g.exists_forwardFrom_of_projLink_eq hfin m₁ e₁
    obtain ⟨x₄, rfl, hx₄, hx₄B, hx₄s⟩ := g.exists_forwardFrom_of_projLink_eq hfin m₄ e₄
    obtain rfl : x₄ = x := g.projectPoint_injOn hx₄B hxB (hx₄.trans hx.symm)
    obtain ⟨x₂, rfl, hx₂, hx₂B, -⟩ := g.exists_forwardFrom_of_projLink_eq hfin m₂ e₂
    obtain ⟨x₃, rfl, hx₃, hx₃B, -⟩ := g.exists_forwardFrom_of_projLink_eq hfin m₃ e₃
    have hcov : ∀ κ, projectPoint D.L D.m ((D.K : ℕ) : ℤ) (x₄ + axisStep D.mesh κ) =
        q.origin + PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) κ := fun κ => by
      rw [projectPoint_add, hx]
      exact congrArg _ (projectPoint_axisStep D.L D.m ((D.K : ℕ) : ℤ) κ)
    obtain rfl : x₂ = x₄ + axisStep D.mesh q.firstAxis :=
      g.projectPoint_injOn hx₂B hxμ (hx₂.trans (hcov _).symm)
    obtain rfl : x₃ = x₄ + axisStep D.mesh q.secondAxis :=
      g.projectPoint_injOn hx₃B hx₄s (hx₃.trans (hcov _).symm)
    refine ⟨⟨x₄, q.firstAxis, q.secondAxis, q.firstAxis_lt_secondAxis⟩, ?_, ?_⟩
    · intro b hb
      simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> assumption
    · exact PeriodicLattice.Plaquette.ext hx rfl rfl
theorem boundaryFaceCount_eq (hfin : (positiveLinksWithin D.mesh g.fundamentalBlock).Finite)
    (hends : ∀ p : D.Plaquette, ∀ b ∈ p.edges, b.initial ∈ p.cornerSet ∧ b.terminal ∈ p.cornerSet) :
    g.boundaryFaceCount =
      D.boundaryPlaquetteCount g.fundamentalBlock +
        D.torusBoundaryPlaquetteCount g.fundamentalBlock := by
  unfold boundaryFaceCount ChessboardSetup.boundaryPlaquetteCount
    ChessboardSetup.torusBoundaryPlaquetteCount
  rw [g.facesLeavingInterior_eq hfin hends, g.facesCrossingBoundary_eq hfin, add_comm]
end ReflectionGrid
theorem BoxTorusComparison.statement_holds
    (hObservables : MeasurableObservablesAndLifts.Statement)
    (hFree : BoxVersusTorusViaFreeBoundary.Statement)
    (hGeometry : LatticeGeometry.LatticeGeometryStatement) :
    BoxTorusComparison.Statement := by
  intro D g hg hside
  have hB : g.fundamentalBlock ∈ g.blocks := g.fundamentalBlock_mem_blocks
  have hgeo := hGeometry D.mesh D.mesh_pos
  have hfin : (positiveLinksWithin D.mesh g.fundamentalBlock).Finite :=
    (hgeo.2.1.1 _ (g.isBounded_block 0)).2
  have hends : ∀ p : D.Plaquette, ∀ b ∈ p.edges,
      b.initial ∈ p.cornerSet ∧ b.terminal ∈ p.cornerSet :=
    hgeo.2.2.1.2.2.2.2.1
  have hcount := g.boundaryFaceCount_eq hfin hends
  refine ⟨?_, fun A hA hAm hA0 ξ => ?_⟩
  · have hone : D.IsBoxLocalObservable g.fundamentalBlock fun _ => (1 : ℂ) :=
      ⟨⟨measurable_const, 1, fun _ => by simp⟩, fun _ _ _ => rfl⟩
    have h := hFree D g hg hside _ hB _ hone (fun _ => zero_le_one) (trivialField D.mesh)
    rw [hcount]
    exact h.2.2.2.2.1
  · have hobs := hObservables D
    have hloc : D.IsBoxLocalObservable g.fundamentalBlock A := by
      refine ⟨hA, fun U U' hU => hobs.1 _ A hA hAm U U' fun b hb => ?_⟩
      have hb' : b ∈ D.boxLinks g.fundamentalBlock := (g.mem_boxLinks_iff hfin).mpr
        ⟨hb.1, interior_subset hb.2.1, interior_subset hb.2.2⟩
      exact congrFun hU ⟨b, Finset.mem_coe.mpr hb'⟩
    have h := (hFree D g hg hside _ hB A hloc hA0 ξ).2.2.2.2.2.1
    have hlift : PeriodicLattice.gibbsExpectation D.L D.m D.K D.β (D.liftedObservable A) =
        D.liftedExpectation A := (hobs.2.2.2.2 A A hA hA).2.1
    have hlinks : ∀ (S S' : Finset D.Link) (e : S = S')
        (h₁ : (S : Set D.Link) ⊆ positiveLinkSet D.mesh)
        (h₂ : (S' : Set D.Link) ⊆ positiveLinkSet D.mesh),
        D.wilsonKernelAt S h₁ A ξ = D.wilsonKernelAt S' h₂ A ξ := by
      rintro S _ rfl _ _
      rfl
    rw [hlift, hcount]
    exact (hlinks _ _ g.interiorLinks_eq_boxLinks _ (D.coe_boxLinks_subset_positive _)).trans_le h
end ChessboardTori
end YangMills.Construction
end
