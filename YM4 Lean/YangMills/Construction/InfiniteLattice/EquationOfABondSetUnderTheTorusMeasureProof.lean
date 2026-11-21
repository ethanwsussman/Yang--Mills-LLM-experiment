import YangMills.Construction.InfiniteLattice.FormsOfTheWilsonSpecificationOfAWindowProof
import YangMills.Construction.InfiniteLattice.CoveringOnBondsAndPlaquettesProof
import YangMills.Construction.InfiniteLattice.EquationOfABondSetUnderTheTorusMeasure
import YangMills.Construction.InfiniteLattice.FactsOfOneLatticeAtOneSpacing
import YangMills.Construction.InfiniteLattice.SpecificationDensityReadsTheBoundary
import YangMills.Construction.InfiniteLattice.TorusMeasureSatisfiesThePerturbedEquationOfAWindowProof
import YangMills.Construction.Lattice.LatticesOfATorusAndTheProductTopologyOfConfigurations
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open MeasureTheory Set InfiniteLattice InfiniteLattice.PeriodicExtensions GibbsAtFixedSpacing Matrices
noncomputable section
namespace FixedSpacing.KernelPreservesTorusExpectation
section Resampling
variable {S P : Type} [Finite S] [Finite P]
theorem secondCountableTopology_specialUnitary :
    SecondCountableTopology ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
theorem integral_extend_resample (hprod : ComplexMatrix2.FiniteProductGroupStatement)
    {ι : S → P} (hι : Function.Injective ι) {h : (P → ComplexMatrix2.specialUnitary) → ℂ}
    (hm : Measurable h) {C : ℝ} (hb : ∀ v, ‖h v‖ ≤ C) :
    ∫ v, (∫ V, h (Function.extend ι V v) ∂ComplexMatrix2.haarPi S) ∂ComplexMatrix2.haarPi P =
      ∫ v, h v ∂ComplexMatrix2.haarPi P := by apply _root_.YangMills.Construction.InfiniteLattice.TiltedTorusMeasureWindowEquation.integral_extend_haarPi <;> assumption
end Resampling
section Edges
variable {a : ℝ}
theorem eq_forwardFrom_of_isPositivelyOriented {b : Link a} (h : b.IsPositivelyOriented) :
    ∃ μ, b = Link.forwardFrom b.initial μ := by apply _root_.YangMills.Construction.InfiniteLattice.Covering.exists_eq_forwardFrom_of_isPositivelyOriented <;> assumption
theorem isPositivelyOriented_of_mem_edges {p : ElementaryPlaquette a} {b : Link a}
    (hb : b ∈ p.edges) : b.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.WindowSpecificationForms.isPositivelyOriented_of_mem_edgeList <;> assumption
theorem initial_coord_bounds (ha : 0 < a) (p : ElementaryPlaquette a) {b : Link a}
    (hb : b ∈ p.edges) (μ : Fin 4) :
    (p.corner : AmbientSpace) μ ≤ (b.initial : AmbientSpace) μ ∧
      (b.initial : AmbientSpace) μ ≤ (p.corner : AmbientSpace) μ + a := by
  have hstep : ∀ κ, 0 ≤ ((axisStep a κ : LatticePoint a) : AmbientSpace) μ ∧
      ((axisStep a κ : LatticePoint a) : AmbientSpace) μ ≤ a := by
    intro κ
    by_cases h : μ = κ
    · subst h
      simp [axisStep, ha.le]
    · simp [axisStep, h, ha.le]
  simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨le_rfl, by
      have : ((Link.forwardFrom p.corner p.lowAxis).initial : AmbientSpace) μ =
        (p.corner : AmbientSpace) μ := rfl
      linarith⟩
  · have e : ((Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis).initial :
        AmbientSpace) μ =
        (p.corner : AmbientSpace) μ + ((axisStep a p.lowAxis : LatticePoint a) : AmbientSpace) μ :=
      rfl
    rw [e]
    constructor <;> linarith [(hstep p.lowAxis).1, (hstep p.lowAxis).2]
  · have e : ((Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis).initial :
        AmbientSpace) μ =
        (p.corner : AmbientSpace) μ + ((axisStep a p.highAxis : LatticePoint a) : AmbientSpace) μ :=
      rfl
    rw [e]
    constructor <;> linarith [(hstep p.highAxis).1, (hstep p.highAxis).2]
  · exact ⟨le_rfl, by
      have : ((Link.forwardFrom p.corner p.highAxis).initial : AmbientSpace) μ =
        (p.corner : AmbientSpace) μ := rfl
      linarith⟩
theorem abs_apply_le_linfNorm (x : AmbientSpace) (μ : Fin 4) : |x μ| ≤ linfNorm x :=
  Finset.le_sup' (fun μ => |x μ|) (Finset.mem_univ μ)
theorem translateLink_mem_edges {p : ElementaryPlaquette a} {t : Link a} (ht : t ∈ p.edges)
    (v : LatticePoint a) :
    CutoffLattice.translateLink t v ∈ (CutoffLattice.translateFace p v).edges := by
  simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at ht ⊢
  have e : ∀ (x : LatticePoint a) (κ : Fin 4), CutoffLattice.translateLink (Link.forwardFrom x κ) v =
      Link.forwardFrom (x + v) κ := fun x κ =>
    Link.ext rfl (add_right_comm x (axisStep a κ) v)
  rcases ht with rfl | rfl | rfl | rfl
  · exact Or.inl (e _ _)
  · exact Or.inr (Or.inl ((e _ _).trans (by
      show Link.forwardFrom _ _ = Link.forwardFrom (p.corner + v + axisStep a p.lowAxis) p.highAxis
      rw [add_right_comm])))
  · exact Or.inr (Or.inr (Or.inl ((e _ _).trans (by
      show Link.forwardFrom _ _ = Link.forwardFrom (p.corner + v + axisStep a p.highAxis) p.lowAxis
      rw [add_right_comm]))))
  · exact Or.inr (Or.inr (Or.inr (e _ _)))
end Edges
theorem plaquetteEnergy_congr {L m : ℕ} {j : ℤ} (U U' : PeriodicLattice.CompactGaugeField L m j)
    (P : PeriodicLattice.Plaquette L m j)
    (h₁ : U.linkValue (torusFirstEdge P) = U'.linkValue (torusFirstEdge P))
    (h₂ : U.linkValue (torusSecondEdge P) = U'.linkValue (torusSecondEdge P))
    (h₃ : U.linkValue (torusThirdEdge P) = U'.linkValue (torusThirdEdge P))
    (h₄ : U.linkValue (torusFourthEdge P) = U'.linkValue (torusFourthEdge P)) :
    PeriodicLattice.plaquetteCost U.1 P = PeriodicLattice.plaquetteCost U'.1 P := by
  have e : ∀ b, U.linkValue b = U'.linkValue b → U.1 b = U'.1 b := fun b h =>
    congrArg Subtype.val h
  have er : ∀ b, U.linkValue b = U'.linkValue b → U.1 b.opposite = U'.1 b.opposite := fun b h =>
    congrArg Subtype.val (show U.linkValue b.opposite = U'.linkValue b.opposite by
      rw [U.linkValue_opposite, U'.linkValue_opposite, h])
  simp only [torusFirstEdge, torusSecondEdge, torusThirdEdge, torusFourthEdge] at h₁ h₂ h₃ h₄
  simp only [PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteHolonomy,
    PeriodicLattice.pathHolonomy, PeriodicLattice.Plaquette.boundaryBonds, List.map_cons,
    List.map_nil]
  rw [e _ h₁, e _ h₂, er _ h₃, er _ h₄]
section Measure
variable (D : Setup)
abbrev PosLink : Type := PeriodicLattice.PositivelyOrientedBond D.L D.m (D.level : ℤ)
theorem continuous_wilsonEnergy (hP : GaugeFieldProduct.Statement) : Continuous D.wilsonEnergy := by
  obtain ⟨-, ⟨-, -, hfin⟩, -, hact⟩ :=
    hP.1 D.L D.m (D.level : ℤ) D.admissible D.m.pos (Int.natCast_nonneg _)
  have := hfin.1
  have := Fintype.ofFinite (PeriodicLattice.Plaquette D.L D.m (D.level : ℤ))
  have e : D.wilsonEnergy = fun U => ∑ p : PeriodicLattice.Plaquette D.L D.m (D.level : ℤ),
      (PeriodicLattice.plaquetteEnergy U.1 p).re := by
    funext U
    change ∑ᶠ p, PeriodicLattice.plaquetteCost U.1 p = _
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [PeriodicLattice.complexPlaquetteEnergy_eq, Complex.ofReal_re]
  rw [e]
  exact continuous_finsetSum _ fun p _ => Complex.continuous_re.comp (hact p).1
theorem complexExpectation_liftedGibbs_eq (hP : GaugeFieldProduct.Statement)
    (hext : Continuous (liftCompactField : D.TorusFields → D.Fields))
    (e : D.TorusFields ≃ₜ (PosLink D → ComplexMatrix2.specialUnitary))
    (he : ⇑e = PeriodicLattice.restrictToPositiveBonds)
    (hhaar : PeriodicLattice.IsProductHaarImage D.L D.m (D.level : ℤ) D.haarMeasure)
    {G : D.Fields → ℂ} (hG : Measurable G) :
    Probability.complexExpectation D.liftedGibbs G =
      (ENNReal.ofReal D.partitionFunction)⁻¹.toReal •
        ∫ v : PosLink D → ComplexMatrix2.specialUnitary,
          ((Real.exp (-D.β * D.wilsonEnergy (e.symm v)) : ℝ) : ℂ) * G (D.lift (e.symm v))
          ∂ComplexMatrix2.haarPi (PosLink D) := by
  have := secondCountableTopology_specialUnitary
  obtain ⟨-, ⟨-, ⟨hBf, -⟩, -⟩, -, -⟩ :=
    hP.1 D.L D.m (D.level : ℤ) D.admissible D.m.pos (Int.natCast_nonneg _)
  have := hBf
  have hper : Measurable D.lift := hext.measurable
  have hρ : Measurable fun U : D.TorusFields =>
      ENNReal.ofReal (Real.exp (-D.β * D.wilsonEnergy U)) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_wilsonEnergy D hP))).measurable.ennreal_ofReal
  have e₁ : Probability.complexExpectation D.liftedGibbs G =
      ∫ U, G (D.lift U) ∂D.gibbs :=
    integral_map hper.aemeasurable hG.aestronglyMeasurable
  rw [e₁, Setup.gibbs, integral_smul_measure]
  congr 1
  rw [integral_withDensity_eq_integral_toReal_smul hρ (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hmap : D.haarMeasure.map e = ComplexMatrix2.haarPi (PosLink D) := by
    rw [he]
    exact hhaar
  rw [← hmap, e.measurableEmbedding.integral_map]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  simp only [Homeomorph.symm_apply_apply]
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul]
end Measure
section Covering
variable (D : Setup)
theorem projLink_edges (hcov : InfiniteLattice.TorusCovering.Statement)
    (p : ElementaryPlaquette D.mesh) :
    D.projLink (firstEdge p) = torusFirstEdge (D.projFace p) ∧
      D.projLink (secondEdge p) = torusSecondEdge (D.projFace p) ∧
      D.projLink (thirdEdge p) = torusThirdEdge (D.projFace p) ∧
      D.projLink (fourthEdge p) = torusFourthEdge (D.projFace p) := by
  obtain ⟨-, -, ⟨-, -, h⟩, -⟩ := hcov D
  have l := (h p).2.1
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at l
  exact ⟨l.1.symm, l.2.1.symm, l.2.2.1.symm, l.2.2.2.symm⟩
theorem projFace_mem_image_faces (hcov : InfiniteLattice.TorusCovering.Statement)
    {𝓛 : LinkWindow D.mesh} {b : Link D.mesh} (hb : b ∈ 𝓛.links) {p₀ : ElementaryPlaquette D.mesh}
    {t : Link D.mesh} (ht : t ∈ p₀.edges) (h : D.projLink t = D.projLink b) :
    D.projFace p₀ ∈ D.projFace '' 𝓛.faces := by
  obtain ⟨-, ⟨-, -, hper⟩, ⟨-, hpp, -⟩, -⟩ := hcov D
  obtain ⟨κ, hκ⟩ := eq_forwardFrom_of_isPositivelyOriented (isPositivelyOriented_of_mem_edges ht)
  obtain ⟨κ', hκ'⟩ := eq_forwardFrom_of_isPositivelyOriented (𝓛.isPositive b hb)
  rw [hκ, hκ'] at h
  obtain ⟨v, hv, hbv⟩ := (hper _ _ _ _).2.1 h
  have hb' : b = CutoffLattice.translateLink t v := by
    rw [hκ', hbv, ← hκ]
  refine ⟨CutoffLattice.translateFace p₀ v, ⟨b, ?_, hb⟩, ?_⟩
  · rw [hb']
    exact translateLink_mem_edges ht v
  · exact ((hpp p₀ _).1.2 ⟨v, hv, rfl⟩).symm
theorem projLink_injOn (hcov : InfiniteLattice.TorusCovering.Statement)
    {S : Set (Link D.mesh)} (hpos : ∀ b ∈ S, b.IsPositivelyOriented) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ b ∈ S, ∀ μ, |(b.initial : AmbientSpace) μ| ≤ R) (hside : 2 * R < D.side) :
    InjOn D.projLink S := by
  obtain ⟨-, ⟨-, -, hper⟩, -, -⟩ := hcov D
  intro b hb b' hb' h
  obtain ⟨κ, hκ⟩ := eq_forwardFrom_of_isPositivelyOriented (hpos b hb)
  obtain ⟨κ', hκ'⟩ := eq_forwardFrom_of_isPositivelyOriented (hpos b' hb')
  rw [hκ, hκ'] at h
  obtain ⟨hκκ, k, hk⟩ := (hper _ _ _ _).1.1 h
  have hspos : 0 < D.side := by linarith
  have hinit : b.initial = b'.initial := by
    refine Subtype.ext (funext fun μ => ?_)
    have h1 := hR b hb μ
    have h2 := hR b' hb' μ
    have h3 : (b'.initial : AmbientSpace) μ - (b.initial : AmbientSpace) μ =
        (k μ : ℝ) * D.side := hk μ
    have hk0 : k μ = 0 := by
      by_contra hne
      have h4 : (1 : ℝ) ≤ |(k μ : ℝ)| := by
        exact_mod_cast Int.one_le_abs hne
      have h5 : |(k μ : ℝ)| * D.side =
          |(b'.initial : AmbientSpace) μ - (b.initial : AmbientSpace) μ| := by
        rw [h3, abs_mul, abs_of_pos hspos]
      have h6 := abs_sub ((b'.initial : AmbientSpace) μ) ((b.initial : AmbientSpace) μ)
      nlinarith
    rw [hk0] at h3
    simp only [Int.cast_zero, zero_mul] at h3
    linarith
  calc b = Link.forwardFrom b.initial κ := hκ
    _ = Link.forwardFrom b'.initial κ' := by rw [hinit, hκκ]
    _ = b' := hκ'.symm
theorem projFace_injOn (hcov : InfiniteLattice.TorusCovering.Statement)
    {𝓛 : LinkWindow D.mesh} {S : Set (Link D.mesh)} (hsub : ∀ p ∈ 𝓛.faces, ∀ b ∈ p.edges, b ∈ S)
    (hinj : InjOn D.projLink S) : InjOn D.projFace 𝓛.faces := by
  intro p hp p' hp' h
  have hf : p.lowAxis = p'.lowAxis := congrArg PeriodicLattice.Plaquette.firstAxis h
  have hs : p.highAxis = p'.highAxis := congrArg PeriodicLattice.Plaquette.secondAxis h
  have e1 : D.projLink (firstEdge p) = D.projLink (firstEdge p') := by
    rw [(projLink_edges D hcov p).1, (projLink_edges D hcov p').1, h]
  have hb : firstEdge p ∈ p.edges := by simp [firstEdge, ElementaryPlaquette.edges]
  have hb' : firstEdge p' ∈ p'.edges := by simp [firstEdge, ElementaryPlaquette.edges]
  have e2 := hinj (hsub p hp _ hb) (hsub p' hp' _ hb') e1
  have hcorner : p.corner = p'.corner := congrArg Link.initial e2
  exact ElementaryPlaquette.ext hcorner hf hs
end Covering
set_option maxHeartbeats 1000000 in
theorem kernelPreservesTorusExpectation (hprod : ComplexMatrix2.FiniteProductGroupStatement)
    (hP : GaugeFieldProduct.Statement)
    (hcov : InfiniteLattice.TorusCovering.Statement)
    (hF : BasicFacts)
    (hD : ConditionalDensityDependsOnRim.Statement) :
    Statement := by
  classical
  intro D 𝓛 𝓕 F hread r hr hend hside
  have ha := D.mesh_pos
  obtain ⟨-, ⟨-, ⟨hBf, -⟩, ⟨hPf, -⟩⟩, ⟨-, ⟨e, he⟩, -, -, -, hhaar, -⟩, hactB⟩ :=
    hP.1 D.L D.m (D.level : ℤ) D.admissible D.m.pos (Int.natCast_nonneg _)
  have := hBf
  have := hPf
  obtain ⟨-, hlinks, hfaces, hcfg⟩ := hcov D
  have hext := hcfg.2.2.2
  obtain ⟨-, ⟨hcpt, -⟩, ⟨hsub, -⟩, -⟩ := hF D
  have := hcpt
  have pos : ∀ b : Link D.mesh, b.IsPositivelyOriented → (D.projLink b).IsPositivelyOriented :=
    fun b hb => (hlinks.1 b).2.2.1 (mem_positiveLinks_iff.2 hb)
  set S : Set (Link D.mesh) := (𝓛.links : Set (Link D.mesh)) ∪ 𝓛.rim ∪ 𝓕 with hSdef
  have hSpos : ∀ b ∈ S, b.IsPositivelyOriented := by
    rintro b ((h | ⟨⟨p, -, h⟩, -⟩) | h)
    · exact 𝓛.isPositive b h
    · exact isPositivelyOriented_of_mem_edges h
    · exact mem_positiveLinks_iff.1 (hread.2.1 h)
  have hSR : ∀ b ∈ S, ∀ μ, |(b.initial : AmbientSpace) μ| ≤ r + D.mesh := by
    rintro b ((h | ⟨⟨p, hp, hb⟩, -⟩) | h) μ
    · have h0 : linfNorm (b.initial : AmbientSpace) ≤ r := (hend b (Or.inl h)).1
      linarith [abs_apply_le_linfNorm (b.initial : AmbientSpace) μ]
    · obtain ⟨b₀, hb₀, hW⟩ := hp
      have h0 : linfNorm (b₀.initial : AmbientSpace) ≤ r := (hend b₀ (Or.inl hW)).1
      have h1 := (abs_apply_le_linfNorm (b₀.initial : AmbientSpace) μ).trans h0
      have t1 := initial_coord_bounds ha p hb μ
      have t2 := initial_coord_bounds ha p hb₀ μ
      rw [abs_le] at h1 ⊢
      constructor <;> linarith [t1.1, t1.2, t2.1, t2.2, h1.1, h1.2]
    · have h0 : linfNorm (b.initial : AmbientSpace) ≤ r := (hend b (Or.inr h)).1
      linarith [abs_apply_le_linfNorm (b.initial : AmbientSpace) μ]
  have hinj : InjOn D.projLink S :=
    projLink_injOn D hcov hSpos (add_nonneg hr ha.le) hSR (by linarith)
  have hPbd : ∀ p ∈ 𝓛.faces, ∀ b ∈ p.edges, b ∈ S := by
    intro p hp b hb
    by_cases h : b ∈ 𝓛.links
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨⟨p, hp, hb⟩, h⟩)
  have hPinj := projFace_injOn D hcov hPbd hinj
  let ι : 𝓛.links → PosLink D := fun b => ⟨D.projLink b, pos b (𝓛.isPositive b b.2)⟩
  have hι : Function.Injective ι := fun b b' h => Subtype.ext
    (hinj (Or.inl (Or.inl b.2)) (Or.inl (Or.inl b'.2)) (congrArg Subtype.val h))
  have hvalue : ∀ (v : PosLink D → ComplexMatrix2.specialUnitary) (c : D.TorusLink)
      (hc : c.IsPositivelyOriented), (e.symm v).linkValue c = v ⟨c, hc⟩ := by
    intro v c hc
    have h := e.apply_symm_apply v
    rw [he] at h
    exact congrFun h ⟨c, hc⟩
  let T : (PosLink D → ComplexMatrix2.specialUnitary) → D.Fields := fun v => D.lift (e.symm v)
  have hTv : ∀ v (b : Link D.mesh) (hb : b.IsPositivelyOriented),
      T v b = v ⟨D.projLink b, pos b hb⟩ :=
    fun v b hb => (D.lift_apply _ b).trans (hvalue v _ _)
  have hout : ∀ b (hb : b ∈ S), b ∉ 𝓛.links → ∀ hp, ¬ ∃ s, ι s = ⟨D.projLink b, hp⟩ := by
    rintro b hb hbW hp ⟨s, hs⟩
    have e' : (s : Link D.mesh) = b :=
      hinj (Or.inl (Or.inl s.2)) hb (congrArg Subtype.val hs)
    exact hbW (e' ▸ s.2)
  have hkeep : ∀ (V : 𝓛.Assignments) v, ∀ b ∈ S, b ∉ 𝓛.links →
      T (Function.extend ι V v) b = T v b := by
    intro V v b hb hbW
    rw [hTv _ b (hSpos b hb), hTv v b (hSpos b hb)]
    exact Function.extend_apply' _ _ _ (hout b hb hbW _)
  have hagree : ∀ (V : 𝓛.Assignments) v, ∀ b ∈ S,
      T (Function.extend ι V v) b = 𝓛.glue ha V (T v) b := by
    intro V v b hb
    by_cases hbW : b ∈ 𝓛.links
    · rw [hTv _ b (hSpos b hb)]
      have e' : (⟨D.projLink b, pos b (hSpos b hb)⟩ : PosLink D) = ι ⟨b, hbW⟩ := rfl
      rw [e', hι.extend_apply]
      simp [LinkWindow.glue, hbW]
    · have hrev : b.opposite ∉ 𝓛.links := fun h' =>
        Link.opposite_not_isPositivelyOriented ha (hSpos b hb) (𝓛.isPositive _ h')
      rw [hkeep V v b hb hbW]
      simp [LinkWindow.glue, hbW, hrev]
  obtain ⟨φ, -, hφ⟩ := hread.2.2
  have hFT : ∀ (V : 𝓛.Assignments) v, F (T (Function.extend ι V v)) = F (𝓛.glue ha V (T v)) := by
    intro V v
    rw [hφ, hφ]
    congr 1
    funext b
    exact hagree V v b (Or.inr b.2)
  have hKread := (hD D 𝓛).2.2.2 𝓕 F hread
  obtain ⟨ψ, -, hψ⟩ := hKread.2.2
  have hKT : ∀ (V : 𝓛.Assignments) v,
      D.conditionalKernel 𝓛 F (T (Function.extend ι V v)) = D.conditionalKernel 𝓛 F (T v) := by
    intro V v
    rw [hψ, hψ]
    congr 1
    funext b
    have hb : (b : Link D.mesh) ∈ S ∧ (b : Link D.mesh) ∉ 𝓛.links := by
      rcases b.2 with h | h
      · exact ⟨Or.inl (Or.inr h), h.2⟩
      · exact ⟨Or.inr h.1, fun h' => h.2 (Finset.mem_coe.2 h')⟩
    exact hkeep V v b hb.1 hb.2
  set Q : Set D.TorusFace := D.projFace '' 𝓛.faces with hQdef
  let A₂ : (PosLink D → ComplexMatrix2.specialUnitary) → ℝ :=
    fun v => ∑ᶠ P ∈ (univ \ Q), D.faceEnergy P (e.symm v)
  let A₁ : (PosLink D → ComplexMatrix2.specialUnitary) → ℝ :=
    fun v => ∑ᶠ p ∈ 𝓛.faces, faceEnergy (T v) p
  have hsplit : ∀ v, D.wilsonEnergy (e.symm v) = A₁ v + A₂ v := by
    intro v
    have e₀ := finsum_mem_add_sdiff (subset_univ Q) finite_univ
      (f := fun P => D.faceEnergy P (e.symm v))
    rw [finsum_mem_univ] at e₀
    have h₂ : ∑ᶠ P ∈ Q, D.faceEnergy P (e.symm v) = A₁ v := by
      rw [hQdef, finsum_mem_image hPinj]
      exact finsum_mem_congr rfl fun p _ => (hcfg.2.2.1 (e.symm v) p).symm
    change ∑ᶠ P, D.faceEnergy P (e.symm v) = _
    rw [← e₀, h₂]
  have hA₂ : ∀ (V : 𝓛.Assignments) v, A₂ (Function.extend ι V v) = A₂ v := by
    intro V v
    refine finsum_mem_congr rfl fun P hP' => ?_
    obtain ⟨p₀, rfl⟩ := hfaces.1 P
    have hnot : ∀ t ∈ p₀.edges,
        (e.symm (Function.extend ι V v)).linkValue (D.projLink t) =
          (e.symm v).linkValue (D.projLink t) := by
      intro t ht
      have htp := isPositivelyOriented_of_mem_edges ht
      rw [hvalue _ _ (pos t htp), hvalue _ _ (pos t htp)]
      refine Function.extend_apply' _ _ _ ?_
      rintro ⟨s, hs⟩
      have hc : D.projLink t = D.projLink s := (congrArg Subtype.val hs).symm
      exact hP'.2 (projFace_mem_image_faces D hcov s.2 ht hc)
    obtain ⟨c₁, c₂, c₃, c₄⟩ := projLink_edges D hcov p₀
    refine plaquetteEnergy_congr _ _ _ ?_ ?_ ?_ ?_
    · rw [← c₁]
      exact hnot _ (by simp [firstEdge, ElementaryPlaquette.edges])
    · rw [← c₂]
      exact hnot _ (by simp [secondEdge, ElementaryPlaquette.edges])
    · rw [← c₃]
      exact hnot _ (by simp [thirdEdge, ElementaryPlaquette.edges])
    · rw [← c₄]
      exact hnot _ (by simp [fourthEdge, ElementaryPlaquette.edges])
  have hact : ∀ (V : 𝓛.Assignments) v, D.wilsonEnergy (e.symm (Function.extend ι V v)) =
      (∑ᶠ p ∈ 𝓛.faces, faceEnergy (𝓛.glue ha V (T v)) p) + A₂ v := by
    intro V v
    have hA₁ : A₁ (Function.extend ι V v) =
        ∑ᶠ p ∈ 𝓛.faces, faceEnergy (𝓛.glue ha V (T v)) p := by
      refine finsum_mem_congr rfl fun p hp => ?_
      have key : ∀ b ∈ p.edges, T (Function.extend ι V v) b = 𝓛.glue ha V (T v) b :=
        fun b hb => hagree V v b (hPbd p hp b hb)
      simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at key
      obtain ⟨h1, h2, h3, h4⟩ := key
      simp only [faceEnergy, faceHolonomy, h1, h2, h3, h4]
    rw [hsplit, hA₂, hA₁]
  let ρ : (PosLink D → ComplexMatrix2.specialUnitary) → ℝ :=
    fun v => Real.exp (-D.β * D.wilsonEnergy (e.symm v))
  have hρle : ∀ v, ‖((ρ v : ℝ) : ℂ)‖ ≤ 1 := by
    intro v
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have h0 : 0 ≤ D.wilsonEnergy (e.symm v) := by
      refine finsum_nonneg fun P => ?_
      obtain ⟨t, ⟨ht, -⟩, hE⟩ := (hactB P).2 (e.symm v)
      rw [PeriodicLattice.complexPlaquetteEnergy_eq] at hE
      rw [← Complex.ofReal_injective hE]
      exact ht
    nlinarith [D.β_pos]
  have := secondCountableTopology_specialUnitary
  have hρm : Measurable fun v => ((ρ v : ℝ) : ℂ) := by
    have hc : Continuous ρ :=
      Real.continuous_exp.comp (continuous_const.mul
        ((continuous_wilsonEnergy D hP).comp e.symm.continuous))
    exact Complex.measurable_ofReal.comp hc.measurable
  have hTm : Measurable T := (hext.comp e.symm.continuous).measurable
  have hFc : Continuous F := hsub ⟨𝓕, hread⟩
  have hKc : Continuous (D.conditionalKernel 𝓛 F) := hsub ⟨_, hKread⟩
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hFc.continuousOn
  obtain ⟨Cγ, hCγ⟩ := isCompact_univ.exists_bound_of_continuousOn hKc.continuousOn
  have hbound : ∀ {B : ℝ} {G : D.Fields → ℂ}, (∀ U ∈ univ, ‖G U‖ ≤ B) →
      ∀ v, ‖((ρ v : ℝ) : ℂ) * G (T v)‖ ≤ B := by
    intro B G hG v
    rw [norm_mul]
    calc _ ≤ 1 * B := mul_le_mul (hρle v) (hG _ (mem_univ _)) (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  have hhaar' : PeriodicLattice.IsProductHaarImage D.L D.m (D.level : ℤ) D.haarMeasure := hhaar
  rw [complexExpectation_liftedGibbs_eq D hP hext e he hhaar' hKc.measurable,
    complexExpectation_liftedGibbs_eq D hP hext e he hhaar' hFc.measurable]
  congr 1
  have r₁ := integral_extend_resample hprod hι
    (h := fun v => ((ρ v : ℝ) : ℂ) * D.conditionalKernel 𝓛 F (T v))
    (hρm.mul (hKc.measurable.comp hTm)) (hbound hCγ)
  have r₂ := integral_extend_resample hprod hι
    (h := fun v => ((ρ v : ℝ) : ℂ) * F (T v)) (hρm.mul (hFc.measurable.comp hTm)) (hbound hC)
  refine r₁.symm.trans (Eq.trans ?_ r₂)
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  let w : 𝓛.Assignments → ℝ := fun V => Real.exp (D.localAction 𝓛 (𝓛.glue ha V (T v)))
  let c : ℂ := ((Real.exp (-D.β * A₂ v) : ℝ) : ℂ)
  have hρV : ∀ V : 𝓛.Assignments, ((ρ (Function.extend ι V v) : ℝ) : ℂ) = (w V : ℂ) * c := by
    intro V
    rw [← Complex.ofReal_mul]
    congr 1
    simp only [ρ, w]
    rw [hact, ← Real.exp_add]
    congr 1
    simp only [Setup.localAction]
    ring
  have e₁ : ∀ V : 𝓛.Assignments, ((ρ (Function.extend ι V v) : ℝ) : ℂ) *
      D.conditionalKernel 𝓛 F (T (Function.extend ι V v)) =
        (w V : ℂ) * (c * D.conditionalKernel 𝓛 F (T v)) := by
    intro V
    rw [hρV, hKT]
    ring
  have e₂ : ∀ V : 𝓛.Assignments,
      ((ρ (Function.extend ι V v) : ℝ) : ℂ) * F (T (Function.extend ι V v)) =
        (F (𝓛.glue ha V (T v)) * (w V : ℂ)) * c := by
    intro V
    rw [hρV, hFT]
    ring
  simp only [e₁, e₂]
  rw [integral_mul_const, integral_mul_const]
  have hZc : ∫ V, (w V : ℂ) ∂ComplexMatrix2.haarPi 𝓛.links =
      ((D.localPartition 𝓛 (T v) : ℝ) : ℂ) :=
    integral_ofReal
  have hZ : D.localPartition 𝓛 (T v) ≠ 0 := by
    intro h0
    have h1 := (hD D 𝓛).1.2.2.2.2 (T v)
    simp only [Setup.conditionalDensity, h0, div_zero, integral_zero] at h1
    exact zero_ne_one h1
  have hZ' : ((D.localPartition 𝓛 (T v) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hZ
  have hKv : D.conditionalKernel 𝓛 F (T v) =
      (∫ V, F (𝓛.glue ha V (T v)) * (w V : ℂ) ∂ComplexMatrix2.haarPi 𝓛.links) /
        ((D.localPartition 𝓛 (T v) : ℝ) : ℂ) := by
    have e' : D.conditionalKernel 𝓛 F (T v) =
        ∫ V, (F (𝓛.glue ha V (T v)) * (w V : ℂ)) / ((D.localPartition 𝓛 (T v) : ℝ) : ℂ)
          ∂ComplexMatrix2.haarPi 𝓛.links := by
      refine integral_congr_ae (ae_of_all _ fun V => ?_)
      simp only [Setup.conditionalDensity, Complex.ofReal_div, mul_div_assoc, w]
    rw [e', integral_div]
  rw [hZc, hKv]
  field_simp
end FixedSpacing.KernelPreservesTorusExpectation
end
end YangMills.Construction
