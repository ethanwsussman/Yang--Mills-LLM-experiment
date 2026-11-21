import YangMills.Construction.InfiniteLattice.TorusOfAPeriodLatticeIsFaithfulProof
import YangMills.Construction.LawInAState.TheLeastTorusLawUnderLatticeIsometriesProof
import YangMills.Construction.InfiniteLattice.PeriodicExtensionAndPlaquetteActionsOfAPeriodLatticeProof
import YangMills.Construction.InfiniteLattice.SitesLinksAndPlaquettesOfTheLattice
import YangMills.Construction.InfiniteLattice.TorusOfAPeriodLatticeIsFinite
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
variable {a : ℝ}
namespace PeriodQuotient
def intCoordsHom (a : ℝ) : (Fin 4 → ℤ) →+ LatticePoint a where
  toFun n := ⟨fun μ => (n μ : ℝ) * a, n, fun _ => rfl⟩
  map_zero' := by
    ext μ
    simp
  map_add' n n' := by
    ext μ
    simp [add_mul]
theorem finite_quotient (Γ : PeriodSublattice a) : Finite (LatticePoint a ⧸ Γ.periods) := by apply _root_.YangMills.Construction.InfiniteLattice.QuotientTorusFaithful.finite_quotientTorus <;> assumption
theorem linkOrbit_translate (Γ : PeriodSublattice a) (b : PositiveLink a) {γ : LatticePoint a}
    (hγ : γ ∈ Γ.periods) : Γ.linkOrbit (PositiveLink.translate b γ) = Γ.linkOrbit b := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicLift.linkOrbit_translate <;> assumption
theorem finite_quotientLink (Γ : PeriodSublattice a) : Finite Γ.QuotientLink := by
  have := finite_quotient Γ
  let f : (LatticePoint a ⧸ Γ.periods) × Fin 4 → Set (PositiveLink a) := fun c =>
    Γ.linkOrbit ⟨Link.forwardFrom (Quotient.out c.1) c.2, c.2, add_sub_cancel_left _ _⟩
  refine ((Set.finite_range f).subset ?_).to_subtype
  rintro _ ⟨b, rfl⟩
  obtain ⟨μ, hμ⟩ := b.2
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add Γ.periods b.1.initial
  refine ⟨((b.1.initial : LatticePoint a ⧸ Γ.periods), μ), ?_⟩
  have hb : (⟨Link.forwardFrom (Quotient.out (b.1.initial : LatticePoint a ⧸ Γ.periods)) μ, μ,
      add_sub_cancel_left _ _⟩ : PositiveLink a) = PositiveLink.translate b h := by
    refine Subtype.ext (Link.ext hh ?_)
    change Quotient.out (b.1.initial : LatticePoint a ⧸ Γ.periods) + axisStep a μ = b.1.terminal + h
    rw [hh, ← hμ]
    abel
  change Γ.linkOrbit _ = Γ.linkOrbit b
  rw [hb]
  exact linkOrbit_translate Γ b h.2
def translateCorner (p : ElementaryPlaquette a) (γ : LatticePoint a) : ElementaryPlaquette a :=
  ⟨p.corner + γ, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
theorem translateCorner_translateCorner (p : ElementaryPlaquette a) (γ γ' : LatticePoint a) :
    translateCorner (translateCorner p γ) γ' = translateCorner p (γ + γ') := by apply _root_.YangMills.DeltaSharedProofs.p502013 <;> assumption
theorem cornerSet_translateCorner (p : ElementaryPlaquette a) (γ : LatticePoint a) :
    (translateCorner p γ).cornerSet = (shift γ).pointMap '' p.cornerSet := by apply _root_.YangMills.DeltaSharedProofs.p501596 <;> assumption
theorem plaquetteMap_shift
    (h : ∀ p q : ElementaryPlaquette a, p.cornerSet = q.cornerSet → p = q)
    (p : ElementaryPlaquette a) (γ : LatticePoint a) :
    (shift γ).plaquetteMap p = translateCorner p γ := by
  have hex : ∃ p' : ElementaryPlaquette a, p'.cornerSet = (shift γ).pointMap '' p.cornerSet :=
    ⟨translateCorner p γ, cornerSet_translateCorner p γ⟩
  unfold LatticeSymmetry.plaquetteMap
  rw [dif_pos hex]
  exact h _ _ (hex.choose_spec.trans (cornerSet_translateCorner p γ).symm)
theorem plaquetteOrbit_translateCorner (Γ : PeriodSublattice a)
    (h : ∀ p q : ElementaryPlaquette a, p.cornerSet = q.cornerSet → p = q)
    (p : ElementaryPlaquette a) {γ : LatticePoint a}
    (hγ : γ ∈ Γ.periods) : Γ.plaquetteOrbit (translateCorner p γ) = Γ.plaquetteOrbit p := by
  ext q
  constructor
  · rintro ⟨γ', h', rfl⟩
    refine ⟨γ + γ', add_mem hγ h', ?_⟩
    rw [plaquetteMap_shift h, plaquetteMap_shift h, translateCorner_translateCorner]
  · rintro ⟨γ', h', rfl⟩
    refine ⟨γ' - γ, sub_mem h' hγ, ?_⟩
    rw [plaquetteMap_shift h, plaquetteMap_shift h, translateCorner_translateCorner,
      add_sub_cancel]
theorem finite_quotientPlaquette (Γ : PeriodSublattice a)
    (h : ∀ p q : ElementaryPlaquette a, p.cornerSet = q.cornerSet → p = q) :
    Finite Γ.QuotientPlaquette := by
  have := finite_quotient Γ
  let f : (LatticePoint a ⧸ Γ.periods) × {m : Fin 4 × Fin 4 // m.1 < m.2} →
      Set (ElementaryPlaquette a) := fun c =>
    Γ.plaquetteOrbit ⟨Quotient.out c.1, c.2.1.1, c.2.1.2, c.2.2⟩
  refine ((Set.finite_range f).subset ?_).to_subtype
  rintro _ ⟨p, rfl⟩
  obtain ⟨γ, hγ⟩ := QuotientAddGroup.mk_out_eq_add Γ.periods p.corner
  refine ⟨((p.corner : LatticePoint a ⧸ Γ.periods), ⟨(p.lowAxis, p.highAxis),
    p.lowAxis_lt_highAxis⟩), ?_⟩
  have hp : (⟨Quotient.out (p.corner : LatticePoint a ⧸ Γ.periods), p.lowAxis, p.highAxis,
      p.lowAxis_lt_highAxis⟩ : ElementaryPlaquette a) = translateCorner p γ :=
    ElementaryPlaquette.ext hγ rfl rfl
  change Γ.plaquetteOrbit _ = Γ.plaquetteOrbit p
  rw [hp]
  exact plaquetteOrbit_translateCorner Γ h p γ.2
end PeriodQuotient
theorem periodQuotientFinite_holds (h : LatticeGeometry.LatticeGeometryStatement) :
    PeriodQuotientFinite := fun a ha Γ =>
  ⟨PeriodQuotient.finite_quotient Γ, PeriodQuotient.finite_quotientLink Γ,
    PeriodQuotient.finite_quotientPlaquette Γ (h a ha).2.2.1.2.1⟩
end YangMills.Construction.InfiniteLattice
