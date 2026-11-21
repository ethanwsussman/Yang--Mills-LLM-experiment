import YangMills.Construction.ChessboardTori.OuterConfigurationAgainstTheFreeBoxProof
import YangMills.Construction.ChessboardTori.TorusAgainstTheFreeBox
import YangMills.Construction.InfiniteLattice.ConfigurationsOfTheTorusLatticeAtPositiveLinks
import YangMills.Construction.InfiniteLattice.CoveringOnAWindow
import YangMills.Construction.LawInAState.GridDataAtEveryExponentProofForm
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction
open InfiniteLattice GibbsAtFixedSpacing Matrices
namespace ChessboardTori
namespace TorusVersusFreeBox
theorem map_comp_haarPi {S P : Type} [Countable S] [Countable P] {ι : S → P}
    (hι : Function.Injective ι) :
    (ComplexMatrix2.haarPi P).map (fun v : P → ComplexMatrix2.specialUnitary => v ∘ ι) =
      ComplexMatrix2.haarPi S := by
  classical
  have hm : Measurable (fun v : P → ComplexMatrix2.specialUnitary => v ∘ ι) :=
    measurable_pi_iff.2 fun s => measurable_pi_apply (ι s)
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  set t' : P → Set ComplexMatrix2.specialUnitary := Function.extend ι t fun _ => univ with ht'
  have e : (fun v : P → ComplexMatrix2.specialUnitary => v ∘ ι) ⁻¹' Set.pi (s : Set S) t =
      Set.pi ((s.image ι : Finset P) : Set P) t' := by
    ext v
    simp [Set.mem_pi, ht', hι.extend_apply]
  have hmt : ∀ p ∈ s.image ι, MeasurableSet (t' p) := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    rw [ht', hι.extend_apply]
    exact ht i
  rw [e, ComplexMatrix2.haarPi, Measure.infinitePi_pi _ hmt, Finset.prod_image hι.injOn]
  simp [ht', hι.extend_apply]
theorem coord_ne_blockFace {D : ChessboardSetup} (g : ReflectionGrid D) (k : Fin 4 → ℤ)
    (x : LatticePoint D.mesh) (μ : Fin 4) :
    (x : AmbientSpace) μ ≠ g.origin μ + g.cellSide * k μ := by
  intro h
  obtain ⟨z, hz⟩ := x.2
  obtain ⟨i, hi⟩ := g.origin_mem μ
  have ha : D.mesh ≠ 0 := D.mesh_pos.ne'
  rw [hz μ, hi, g.cellSide_eq] at h
  have h2 : (z μ : ℝ) = i + 1 / 2 + g.cellRatio * k μ := by
    apply mul_right_cancel₀ ha
    linear_combination h
  have h3 : ((2 * z μ : ℤ) : ℝ) = ((2 * i + 1 + 2 * (g.cellRatio * k μ) : ℤ) : ℝ) := by
    push_cast
    linarith
  have h4 : 2 * z μ = 2 * i + 1 + 2 * (g.cellRatio * k μ) := by exact_mod_cast h3
  generalize g.cellRatio * k μ = w at h4
  omega
theorem eq_of_sub_mem_latticeSubgroup {D : ChessboardSetup} (g : ReflectionGrid D)
    {k : Fin 4 → ℤ} {x x' : LatticePoint D.mesh}
    (hx : (x : AmbientSpace) ∈ g.block k) (hx' : (x' : AmbientSpace) ∈ g.block k)
    (h : (x : AmbientSpace) - x' ∈ latticeSubgroup (PeriodicLattice.torusSide D.L D.m)) :
    x = x' := by
  obtain ⟨z, hz⟩ := h
  have hℓ : 0 < PeriodicLattice.torusSide D.L D.m := by
    have hL : (0 : ℝ) < D.L := by linarith [D.one_lt_factor]
    unfold PeriodicLattice.torusSide
    positivity
  refine Subtype.ext (funext fun μ => ?_)
  obtain ⟨h₁, h₂⟩ := hx μ
  obtain ⟨h₁', h₂'⟩ := hx' μ
  have hc := coord_ne_blockFace g k x μ
  have hc' := coord_ne_blockFace g k x' μ
  have hzμ : (x : AmbientSpace) μ - (x' : AmbientSpace) μ =
      (z μ : ℝ) * PeriodicLattice.torusSide D.L D.m := hz μ
  rcases lt_trichotomy (z μ) 0 with hneg | h0 | hpos
  · have h₃ : (z μ : ℝ) ≤ -1 := by exact_mod_cast (by omega : z μ ≤ -1)
    have h₄ : (z μ : ℝ) * PeriodicLattice.torusSide D.L D.m ≤
        -PeriodicLattice.torusSide D.L D.m := by nlinarith
    exact absurd (by linarith) hc
  · rw [h0] at hzμ
    simp only [Int.cast_zero, zero_mul] at hzμ
    linarith
  · have h₃ : (1 : ℝ) ≤ z μ := by exact_mod_cast (by omega : 1 ≤ z μ)
    have h₄ : PeriodicLattice.torusSide D.L D.m ≤
        (z μ : ℝ) * PeriodicLattice.torusSide D.L D.m := by nlinarith
    exact absurd (by linarith) hc'
variable (D : ChessboardSetup)
abbrev toCutoffData : CutoffLinks.CutoffData := ⟨D.toStandingParameters, D.β, D.beta_pos⟩
abbrev TorusForwardLink : Type :=
  PeriodicLattice.PositivelyOrientedBond D.L D.m ((D.K : ℕ) : ℤ)
variable {D}
theorem mem_positiveLinksWithin_of_mem_boxLinks {B : Set AmbientSpace} {b : D.Link}
    (hb : b ∈ D.boxLinks B) : b ∈ positiveLinksWithin D.mesh B := by
  by_cases h : (positiveLinksWithin D.mesh B).Finite
  · have hb' : b ∈ (D.boxLinks B : Set D.Link) := hb
    rwa [D.coe_boxLinks h] at hb'
  · simp [ChessboardSetup.boxLinks, h] at hb
theorem isPositivelyOriented_projectLink {b : D.Link} (hb : b ∈ positiveLinkSet D.mesh) :
    (projectLink D.L D.m ((D.K : ℕ) : ℤ) b).IsPositivelyOriented := by
  obtain ⟨x, κ, rfl⟩ := hb
  exact PeriodicLattice.mem_positiveBonds_iff.1
    ⟨_, κ, (toCutoffData D).projLink_forwardFrom x κ⟩
variable (D) in
def projBoxLink (B : Set AmbientSpace) (b : (D.boxLinks B : Set D.Link)) : TorusForwardLink D :=
  ⟨projectLink D.L D.m ((D.K : ℕ) : ℤ) b.1,
    isPositivelyOriented_projectLink (D.coe_boxLinks_subset_positive B b.2)⟩
theorem projBoxLink_injective (hcov : CutoffLinks.WindowProjectionProperties)
    (g : ReflectionGrid D) (k : Fin 4 → ℤ) : Function.Injective (projBoxLink D (g.block k)) := by
  rintro ⟨b, hb⟩ ⟨b', hb'⟩ h
  obtain ⟨⟨x, μ, rfl⟩, hx, -⟩ := mem_positiveLinksWithin_of_mem_boxLinks hb
  obtain ⟨⟨x', μ', rfl⟩, hx', -⟩ := mem_positiveLinksWithin_of_mem_boxLinks hb'
  obtain ⟨-, -, -, -, -, hiff, -⟩ := (hcov (toCutoffData D)).1
  obtain ⟨rfl, hs⟩ := (hiff x x' μ μ').1 (congrArg Subtype.val h)
  have e : x = x' := eq_of_sub_mem_latticeSubgroup g hx hx' hs
  subst e
  rfl
theorem injOn_projectFace (hcov : CutoffLinks.WindowProjectionProperties)
    (g : ReflectionGrid D) (k : Fin 4 → ℤ) :
    InjOn (CutoffLattice.projectFace D.L D.m D.K) (D.interiorPlaquettes (g.block k)) := by
  intro p hp p' hp' h
  obtain ⟨-, -, -, -, -, hiff, -⟩ := (hcov (toCutoffData D)).1
  have hbase : ∀ q ∈ D.interiorPlaquettes (g.block k), (q.corner : AmbientSpace) ∈ g.block k :=
    fun q hq => (mem_positiveLinksWithin_of_mem_boxLinks
      (hq (Link.forwardFrom q.corner q.lowAxis) (by simp [ElementaryPlaquette.edges]))).2.1
  have h₁ : projectPoint D.L D.m ((D.K : ℕ) : ℤ) p.corner =
      projectPoint D.L D.m ((D.K : ℕ) : ℤ) p'.corner :=
    congrArg PeriodicLattice.Plaquette.origin h
  have h₂ : p.lowAxis = p'.lowAxis := congrArg PeriodicLattice.Plaquette.firstAxis h
  have h₃ : p.highAxis = p'.highAxis := congrArg PeriodicLattice.Plaquette.secondAxis h
  have hb : (toCutoffData D).projLink (Link.forwardFrom p.corner p.lowAxis) =
      (toCutoffData D).projLink (Link.forwardFrom p'.corner p.lowAxis) := by
    rw [(toCutoffData D).projLink_forwardFrom, (toCutoffData D).projLink_forwardFrom]
    exact congrArg (fun y => (toCutoffData D).positiveLinkAt y p.lowAxis) h₁
  have e : p.corner = p'.corner :=
    eq_of_sub_mem_latticeSubgroup g (hbase p hp) (hbase p' hp') ((hiff _ _ _ _).1 hb).2
  exact ElementaryPlaquette.ext e h₂ h₃
theorem measurable_gaugeFieldOfPositive {L m : ℕ} {j : ℤ} :
    Measurable (PeriodicLattice.gaugeFieldOfPositive :
      (PeriodicLattice.PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary) →
        PeriodicLattice.Bond L m j → ComplexMatrix2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.measurable_gaugeFieldOfPositive <;> assumption
theorem measurable_boltzmannWeight {L m : ℕ} {j : ℤ} [Finite (PeriodicLattice.Plaquette L m j)]
    (β : ℝ) :
    Measurable (PeriodicLattice.boltzmannWeight β :
      (PeriodicLattice.Bond L m j → ComplexMatrix2) → ℝ) := by apply _root_.YangMills.Construction.EqualSideGridsAtEveryExponent.boltzmannWeight_measurable <;> assumption
theorem exists_periodicField
    (hlinks : CutoffLinks.PeriodicFieldsAtPositiveLinks)
    (v : TorusForwardLink D → ComplexMatrix2.specialUnitary) :
    ∃ U : (toCutoffData D).PeriodicFields, (∀ l : TorusForwardLink D, U.linkValue l.1 = v l) ∧
      U.1 = PeriodicLattice.gaugeFieldOfPositive v := by
  classical
  obtain ⟨⟨-, -, -, hxor, hbij⟩, -⟩ := hlinks (toCutoffData D)
  obtain ⟨U, hU⟩ := hbij.2 fun l =>
    v ⟨l.1, PeriodicLattice.mem_positiveBonds_iff.1 l.2⟩
  have hval : ∀ l : TorusForwardLink D, U.linkValue l.1 = v l := fun l =>
    congrFun hU ⟨l.1, PeriodicLattice.mem_positiveBonds_iff.2 l.2⟩
  refine ⟨U, hval, ?_⟩
  funext b
  unfold PeriodicLattice.gaugeFieldOfPositive
  by_cases h : b.IsPositivelyOriented
  · rw [dif_pos h]
    exact congrArg Subtype.val (hval ⟨b, h⟩)
  · have h' : b.opposite.IsPositivelyOriented := by
      rcases hxor b with h₁ | h₁
      · exact absurd (PeriodicLattice.mem_positiveBonds_iff.1 h₁.1) h
      · obtain ⟨l', hl', rfl⟩ := h₁.1
        exact PeriodicLattice.mem_positiveBonds_iff.1 hl'
    rw [dif_neg h, dif_pos h']
    have e := U.2.2 b.opposite (mem_univ _)
    have hr : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
    rw [hr] at e
    have e₂ : U.1 b.opposite = ((v ⟨b.opposite, h'⟩ : ComplexMatrix2.specialUnitary) :
        ComplexMatrix2) :=
      congrArg Subtype.val (hval ⟨b.opposite, h'⟩)
    rw [e, e₂]
variable (D) in
def interiorEnergy (B : Set AmbientSpace) (V : D.BoxLinkVariables B) : ℝ :=
  ∑ᶠ p ∈ D.interiorPlaquettes B,
    D.evalOnBox B (fun U : D.GaugeField => faceEnergy U p) V
theorem restrictField_liftField
    (hlinks : CutoffLinks.PeriodicFieldsAtPositiveLinks)
    (hcov : CutoffLinks.WindowProjectionProperties) (B : Set AmbientSpace)
    (v : TorusForwardLink D → ComplexMatrix2.specialUnitary) :
    restrictField (D.liftField (PeriodicLattice.gaugeFieldOfPositive v))
        (D.boxLinks B : Set D.Link) = v ∘ projBoxLink D B := by
  obtain ⟨U, hval, hU⟩ := exists_periodicField hlinks v
  obtain ⟨-, -, -, -, -, -, hpv, -, -⟩ := (hcov (toCutoffData D)).1
  have e : D.liftField (PeriodicLattice.gaugeFieldOfPositive v) =
      (toCutoffData D).liftField U := by
    rw [← hU]
    rfl
  rw [e]
  funext b
  have h₁ := hpv U b.1 (D.coe_boxLinks_subset_positive B b.2)
  exact h₁.trans (hval (projBoxLink D B b))
theorem exists_wilsonAction_eq_interiorEnergy_add
    (hlinks : CutoffLinks.PeriodicFieldsAtPositiveLinks)
    (hcov : CutoffLinks.WindowProjectionProperties) (g : ReflectionGrid D) (k : Fin 4 → ℤ)
    (v : TorusForwardLink D → ComplexMatrix2.specialUnitary) :
    ∃ R : ℝ, 0 ≤ R ∧ R ≤ 2 * (D.torusBoundaryPlaquetteCount (g.block k) : ℝ) ∧
      0 ≤ interiorEnergy D (g.block k) (v ∘ projBoxLink D (g.block k)) ∧
      PeriodicLattice.wilsonAction (PeriodicLattice.gaugeFieldOfPositive v) =
        interiorEnergy D (g.block k) (v ∘ projBoxLink D (g.block k)) + R := by
  classical
  obtain ⟨U, hval, hU⟩ := exists_periodicField hlinks v
  obtain ⟨⟨-, -, hPf, -, -⟩, hact, -, -⟩ := hlinks (toCutoffData D)
  obtain ⟨-, -, -, -, -, -, -, hpp, -⟩ := (hcov (toCutoffData D)).1
  have := hPf
  set B := g.block k with hB
  set Q : Set (toCutoffData D).PeriodicPlaquette :=
    CutoffLattice.projectFace D.L D.m D.K '' D.interiorPlaquettes B with hQ
  have hres := restrictField_liftField hlinks hcov B v
  have e₀ : D.liftField (PeriodicLattice.gaugeFieldOfPositive v) =
      (toCutoffData D).liftField U := by
    rw [← hU]
    rfl
  have hpoint : ∀ p ∈ D.interiorPlaquettes B,
      D.evalOnBox B (fun U : D.GaugeField => faceEnergy U p) (v ∘ projBoxLink D B) =
        (toCutoffData D).faceAction (CutoffLattice.projectFace D.L D.m D.K p) U := by
    intro p hp
    rw [ChessboardSetup.evalOnBox_eq (ChessboardSetup.dependsOnlyOnLinks_faceEnergy hp) hres, e₀]
    exact congrArg (fun M : ComplexMatrix2 => 1 - (1 / 2 : ℝ) * (ComplexMatrix2.fullTrace M).re)
      (hpp U p)
  have hin : interiorEnergy D B (v ∘ projBoxLink D B) =
      ∑ᶠ P ∈ Q, (toCutoffData D).faceAction P U := by
    rw [hQ, finsum_mem_image (injOn_projectFace hcov g k)]
    exact finsum_mem_congr rfl hpoint
  have hsplit : PeriodicLattice.wilsonAction (PeriodicLattice.gaugeFieldOfPositive v) =
      (∑ᶠ P ∈ Q, (toCutoffData D).faceAction P U) +
        ∑ᶠ P ∈ (univ \ Q), (toCutoffData D).faceAction P U := by
    rw [← hU]
    have e := finsum_mem_add_sdiff (subset_univ Q) finite_univ
      (f := fun P => (toCutoffData D).faceAction P U)
    rw [finsum_mem_univ] at e
    exact e.symm
  have hnn : ∀ P, 0 ≤ (toCutoffData D).faceAction P U := fun P => ((hact P).2.1 U).1
  have hcomp : (univ \ Q : Set (toCutoffData D).PeriodicPlaquette) =
      {p' | ¬ ∃ p ∈ D.interiorPlaquettes B, CutoffLattice.projectFace D.L D.m D.K p = p'} := by
    ext P
    exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
  refine ⟨∑ᶠ P ∈ (univ \ Q), (toCutoffData D).faceAction P U,
    finsum_nonneg fun P => finsum_nonneg fun _ => hnn P, ?_, ?_, ?_⟩
  · have hfin : (univ \ Q : Set (toCutoffData D).PeriodicPlaquette).Finite := toFinite _
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hcard : (D.torusBoundaryPlaquetteCount B : ℝ) = (hfin.toFinset.card : ℝ) := by
      rw [ChessboardSetup.torusBoundaryPlaquetteCount, ← hcomp, Set.ncard_eq_toFinset_card _ hfin]
    rw [hcard]
    have h₁ := Finset.sum_le_card_nsmul hfin.toFinset
      (fun P => (toCutoffData D).faceAction P U) 2 fun P _ => ((hact P).2.1 U).2
    simpa [mul_comm] using h₁
  · rw [hin]
    exact finsum_nonneg fun P => finsum_nonneg fun _ => hnn P
  · rw [hin]
    exact hsplit
theorem secondCountable_specialUnitary : SecondCountableTopology ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.InfiniteLattice.WilsonOperator.secondCountable_specialUnitary <;> assumption
theorem continuous_faceEnergy (p : D.Plaquette) :
    Continuous fun U : D.GaugeField => faceEnergy U p := by
  have hb : ∀ b : D.Link, Continuous fun U : D.GaugeField => U b := fun b =>
    (continuous_apply b).comp
      (continuous_subtype_val
        (p := fun U : D.Link → ComplexMatrix2.specialUnitary => ∀ b, U b.opposite = (U b)⁻¹))
  have hv : Continuous fun U : D.GaugeField => faceHolonomy U p := by
    unfold faceHolonomy
    exact (((hb _).mul (hb _)).mul (hb _).inv).mul (hb _).inv
  unfold faceEnergy
  have ht : Continuous fun U : D.GaugeField =>
      ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2) :=
    (continuous_subtype_val.comp hv).matrix_trace
  exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp ht))
theorem continuous_overwriteBox (B : Set AmbientSpace) (ξ : D.GaugeField) :
    Continuous fun V : D.BoxLinkVariables B => D.overwriteBox B V ξ := by apply _root_.YangMills.Construction.ChessboardTori.FreeBoxComparison.continuous_overwriteBox <;> assumption
theorem measurable_overwriteBox (B : Set AmbientSpace) (ξ : D.GaugeField) :
    Measurable fun V : D.BoxLinkVariables B => D.overwriteBox B V ξ := by
  have := secondCountable_specialUnitary
  exact (continuous_overwriteBox B ξ).measurable
theorem measurable_interiorEnergy {B : Set AmbientSpace} (hfin : (D.interiorPlaquettes B).Finite) :
    Measurable (interiorEnergy D B) := by
  have e : interiorEnergy D B = fun V => ∑ p ∈ hfin.toFinset,
      D.evalOnBox B (fun U : D.GaugeField => faceEnergy U p) V := by
    funext V
    exact finsum_mem_eq_finite_toFinset_sum _ hfin
  rw [e]
  refine Finset.measurable_sum _ fun p _ => ?_
  exact (continuous_faceEnergy p).measurable.comp
    (measurable_overwriteBox B (trivialField D.mesh))
end TorusVersusFreeBox
open TorusVersusFreeBox in
theorem TorusVersusFreeBox.holds
    (hlinks : CutoffLinks.PeriodicFieldsAtPositiveLinks)
    (hcov : CutoffLinks.WindowProjectionProperties) : TorusVersusFreeBox.Statement := by
  classical
  intro D g _ _ B hB Ψ hΨ hnn
  obtain ⟨k, rfl⟩ := hB
  obtain ⟨⟨-, -, hPf, -, -⟩, -, -, -⟩ := hlinks (toCutoffData D)
  have hPf' : Finite (PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ)) := hPf
  set B := g.block k with hBdef
  set c : ℝ := Real.exp (-2 * D.β * (D.torusBoundaryPlaquetteCount B : ℝ)) with hc
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  have hinj := projBoxLink_injective hcov g k
  have hfin : (D.interiorPlaquettes B).Finite :=
    Set.Finite.of_finite_image (toFinite _) (injOn_projectFace hcov g k)
  have hΨre : ∀ U, Ψ U = ((Ψ U).re : ℂ) := fun U =>
    Complex.ext (by simp) (by simpa using ((Complex.le_def.mp (hnn U)).2).symm)
  have hΨ0 : ∀ U, 0 ≤ (Ψ U).re := fun U => by simpa using (Complex.le_def.mp (hnn U)).1
  obtain ⟨hΨm, C, hC⟩ := hΨ.1
  let f : D.BoxLinkVariables B → ℝ := fun V =>
    (D.evalOnBox B Ψ V).re * Real.exp (-D.β * interiorEnergy D B V)
  let t : (TorusForwardLink D → ComplexMatrix2.specialUnitary) → ℝ := fun v =>
    (Ψ (D.liftField (PeriodicLattice.gaugeFieldOfPositive v))).re *
      PeriodicLattice.boltzmannWeight D.β (PeriodicLattice.gaugeFieldOfPositive v)
  have hcfg := measurable_gaugeFieldOfPositive (L := D.L) (m := D.m) (j := ((D.K : ℕ) : ℤ))
  have hper : Measurable D.liftField :=
    measurable_liftField D.L D.m ((D.K : ℕ) : ℤ)
  have hden := measurable_boltzmannWeight (L := D.L) (m := D.m) (j := ((D.K : ℕ) : ℤ)) D.β
  have hfm : Measurable f :=
    (Complex.measurable_re.comp (hΨm.comp (measurable_overwriteBox B _))).mul
      (Real.measurable_exp.comp (measurable_const.mul (measurable_interiorEnergy hfin)))
  have htm : Measurable t :=
    (Complex.measurable_re.comp (hΨm.comp (hper.comp hcfg))).mul (hden.comp hcfg)
  have hrm : Measurable fun v : TorusForwardLink D → ComplexMatrix2.specialUnitary =>
      v ∘ projBoxLink D B :=
    measurable_pi_iff.2 fun s => measurable_pi_apply _
  have hpt : ∀ v, c * f (v ∘ projBoxLink D B) ≤ t v ∧ t v ≤ f (v ∘ projBoxLink D B) ∧
      0 ≤ f (v ∘ projBoxLink D B) ∧ f (v ∘ projBoxLink D B) ≤ |C| := by
    intro v
    obtain ⟨R, hR0, hR2, hin0, hW⟩ := exists_wilsonAction_eq_interiorEnergy_add hlinks hcov g k v
    have hval : D.evalOnBox B Ψ (v ∘ projBoxLink D B) =
        Ψ (D.liftField (PeriodicLattice.gaugeFieldOfPositive v)) :=
      ChessboardSetup.evalOnBox_eq hΨ.2 (restrictField_liftField hlinks hcov B v)
    have hβ := D.beta_pos
    set y := (Ψ (D.liftField (PeriodicLattice.gaugeFieldOfPositive v))).re with hy
    have hy0 : 0 ≤ y := hΨ0 _
    have hyC : y ≤ |C| := by
      have h₁ := hC (D.liftField (PeriodicLattice.gaugeFieldOfPositive v))
      have h₂ := Complex.re_le_norm (Ψ (D.liftField (PeriodicLattice.gaugeFieldOfPositive v)))
      exact (h₂.trans h₁).trans (le_abs_self C)
    set E := Real.exp (-D.β * interiorEnergy D B (v ∘ projBoxLink D B)) with hE
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hfv : f (v ∘ projBoxLink D B) = y * E := by
      simp only [f]
      rw [hval]
    have htv : t v = y * E * Real.exp (-D.β * R) := by
      have hW' : PeriodicLattice.wilsonAction (PeriodicLattice.gaugeFieldOfPositive v) =
          interiorEnergy D B (v ∘ projBoxLink D B) + R := hW
      have hexp : Real.exp (-D.β * PeriodicLattice.wilsonAction
          (PeriodicLattice.gaugeFieldOfPositive v)) = E * Real.exp (-D.β * R) := by
        rw [hW', mul_add, Real.exp_add, hE]
      show y * Real.exp (-D.β * PeriodicLattice.wilsonAction _) = _
      rw [hexp]
      ring
    have hR1 : Real.exp (-D.β * R) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hRc : c ≤ Real.exp (-D.β * R) := by
      apply Real.exp_le_exp.2
      nlinarith
    have hyE : 0 ≤ y * E := mul_nonneg hy0 hE0
    rw [hfv, htv]
    refine ⟨?_, ?_, hyE, ?_⟩
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hRc hyE
    · exact mul_le_of_le_one_right hyE hR1
    · calc y * E ≤ y * 1 := mul_le_mul_of_nonneg_left hE1 hy0
        _ = y := mul_one y
        _ ≤ |C| := hyC
  have hprob : IsProbabilityMeasure (ComplexMatrix2.haarPi (TorusForwardLink D)) := by
    unfold ComplexMatrix2.haarPi
    infer_instance
  have hfi : Integrable (fun v : TorusForwardLink D → ComplexMatrix2.specialUnitary =>
      f (v ∘ projBoxLink D B)) (ComplexMatrix2.haarPi (TorusForwardLink D)) := by
    refine Integrable.of_bound (hfm.comp hrm).aestronglyMeasurable |C| (ae_of_all _ fun v => ?_)
    obtain ⟨-, -, h₀, h₁⟩ := hpt v
    rwa [Real.norm_eq_abs, abs_of_nonneg h₀]
  have hti : Integrable t (ComplexMatrix2.haarPi (TorusForwardLink D)) := by
    refine hfi.mono' htm.aestronglyMeasurable (ae_of_all _ fun v => ?_)
    obtain ⟨h₁, h₂, h₀, -⟩ := hpt v
    rw [Real.norm_eq_abs, abs_of_nonneg ((mul_nonneg hc0 h₀).trans h₁)]
    exact h₂
  have hZf : D.freeBoxPartition B Ψ =
      ((∫ v, f (v ∘ projBoxLink D B) ∂ComplexMatrix2.haarPi (TorusForwardLink D) : ℝ) : ℂ) := by
    have e₁ : ∫ v, f (v ∘ projBoxLink D B) ∂ComplexMatrix2.haarPi (TorusForwardLink D) =
        ∫ V, f V ∂D.boxHaar B := by
      have hmap := map_comp_haarPi (P := TorusForwardLink D) hinj
      have e := integral_map (μ := ComplexMatrix2.haarPi (TorusForwardLink D)) hrm.aemeasurable
        (f := f) hfm.aestronglyMeasurable
      rw [hmap] at e
      exact e.symm
    rw [e₁, ← integral_complex_ofReal, ChessboardSetup.freeBoxPartition]
    refine integral_congr_ae (ae_of_all _ fun V => ?_)
    have hv : D.evalOnBox B Ψ V = ((D.evalOnBox B Ψ V).re : ℂ) := hΨre _
    simp only [f, Complex.ofReal_mul]
    rw [← hv]
    rfl
  have hZt : D.torusPartition Ψ =
      ((∫ v, t v ∂ComplexMatrix2.haarPi (TorusForwardLink D) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ChessboardSetup.torusPartition,
      PeriodicLattice.productHaarMeasure, PeriodicLattice.gaugeFieldHaar]
    have hF : Measurable fun U : PeriodicLattice.Bond D.L D.m ((D.K : ℕ) : ℤ) → ComplexMatrix2 =>
        Ψ (D.liftField U) * (PeriodicLattice.boltzmannWeight D.β U : ℂ) :=
      (hΨm.comp hper).mul (Complex.measurable_ofReal.comp hden)
    rw [integral_map hcfg.aemeasurable hF.aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [t, Complex.ofReal_mul]
    rw [← hΨre]
  rw [hZf, hZt, ← Complex.ofReal_mul, Complex.real_le_real, Complex.real_le_real]
  constructor
  · rw [← integral_const_mul]
    exact integral_mono (hfi.const_mul c) hti fun v => (hpt v).1
  · exact integral_mono hti hfi fun v => (hpt v).2.1
end ChessboardTori
end YangMills.Construction
end
