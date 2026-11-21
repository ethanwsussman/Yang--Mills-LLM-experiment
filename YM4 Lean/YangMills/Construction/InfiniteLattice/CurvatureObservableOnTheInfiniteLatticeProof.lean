import YangMills.Construction.InfiniteLattice.ActionsOfALatticeIsometry
import YangMills.Construction.InfiniteLattice.CurvatureObservableOnTheInfiniteLattice
import YangMills.Construction.InfiniteLattice.FactsOfOneLatticeAtOneSpacing
import YangMills.Construction.InfiniteLattice.GroupOfLatticeIsometries
import YangMills.Construction.InfiniteLattice.PlaquetteFunctionsAndExponentialsUnderALatticeIsometry
import YangMills.Construction.InfiniteLattice.ReflectionsLatticeMirrorsAndTuplesOnTheTwoSides
import YangMills.Construction.Lattice.ConnectedFunctionsAreAFiniteSumOverPlaquettes
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.InfiniteLattice YangMills.Construction.GibbsAtFixedSpacing
noncomputable section
namespace YangMills.Construction.FixedSpacing.CurvatureObservable
theorem toFun_mem_latticeMotions (hGroup : LatticeSymmetryGroup.SymmetryGroupStatement) (D : Setup)
    (r : LatticeSymmetry D.mesh) : r.toFun ∈ affineHyperoctahedralMaps D.mesh := by
  obtain ⟨hIso, -⟩ := hGroup _ D.mesh_pos
  obtain ⟨w, hw, v, hv⟩ := (hIso r.toFun).1 ⟨r.preservesDist, r.image_eq⟩
  exact ⟨w, hw, v, funext hv⟩
theorem actOn_smearedEnergy {a : ℝ} (r : LatticeSymmetry a)
    (hb : Function.Bijective r.plaquetteMap)
    (hx : ∀ p : ElementaryPlaquette a, (r.plaquetteMap p).center = r.toFun p.center)
    (hA : ∀ (p : ElementaryPlaquette a) (U : GaugeField a),
      faceEnergy (r.pullbackField U) p = faceEnergy U (r.plaquetteMap p))
    (f : AmbientSpace → ℝ) :
    r.actOn (smearedEnergy f : GaugeField a → ℝ) =
      smearedEnergy (r.pushforwardFun f) := by
  funext U
  change smearedEnergy f (r.pullbackField U) = smearedEnergy (r.pushforwardFun f) U
  unfold smearedEnergy
  rw [← finsum_comp_equiv (Equiv.ofBijective _ hb)
    (f := fun q => faceEnergy U q • r.pushforwardFun f q.center)]
  refine finsum_congr fun p => ?_
  simp only [Equiv.ofBijective_apply]
  rw [hx, hA, LatticeSymmetry.pushforwardFun_apply_toFun]
theorem pushforwardFun_mem_compactTestFunctions (hGroup : LatticeSymmetryGroup.SymmetryGroupStatement)
    (D : Setup) {f : AmbientSpace → ℝ} (hf : f ∈ compactTestFunctions) (r : LatticeSymmetry D.mesh) :
    r.pushforwardFun f ∈ compactTestFunctions := by
  obtain ⟨w, -, v, hv⟩ := toFun_mem_latticeMotions hGroup D r
  obtain ⟨hm, ⟨C, hC⟩, hc⟩ := hf
  let h : AmbientSpace ≃ₜ AmbientSpace :=
    (w.toContinuousLinearEquiv.toHomeomorph).trans (Homeomorph.addRight (v : AmbientSpace))
  have hh : ∀ x, h x = r.toFun x := fun x => by
    rw [hv]
    rfl
  have hinv : Function.invFun r.toFun = ⇑h.symm := by
    funext y
    have hy : r.toFun (h.symm y) = y := by
      rw [← hh]
      simp
    apply r.toFun_injective
    rw [Function.invFun_eq (f := r.toFun) ⟨_, hy⟩, hy]
  have hcomp : r.pushforwardFun f = f ∘ ⇑h.symm := by
    rw [← hinv]
    rfl
  rw [hcomp]
  exact ⟨hm.comp h.symm.measurable, ⟨C, fun x => hC _⟩, hc.comp_homeomorph h.symm⟩
theorem covariantUnderSymmetry (hGroup : LatticeSymmetryGroup.SymmetryGroupStatement)
    (hAct : LatticeSymmetryActions)
    (hPlaq : FaceEnergyAndExponentialCovariance) (D : Setup)
    {f : AmbientSpace → ℝ} (hf : f ∈ compactTestFunctions) (r : LatticeSymmetry D.mesh) :
    CovariantUnderSymmetry D f r := by
  have hr := toFun_mem_latticeMotions hGroup D r
  obtain ⟨-, ⟨-, -, -, hbij⟩, -, -⟩ := hAct _ D.mesh_pos r r hr hr
  have hp := (hPlaq _ D.mesh_pos r hr).1
  exact ⟨hbij, fun p => (hp p).2.1, fun p => (hp p).1, pushforwardFun_mem_compactTestFunctions hGroup D hf r,
    actOn_smearedEnergy r hbij (fun p => (hp p).1) (fun p => (hp p).2.2) f⟩
theorem covariantUnderShiftsRotationsReflections (hGroup : LatticeSymmetryGroup.SymmetryGroupStatement)
    (hAct : LatticeSymmetryActions)
    (hPlaq : FaceEnergyAndExponentialCovariance)
    (hMirror : EuclideanMirrors.MirrorReflections.Statement)
    (D : Setup) {f : AmbientSpace → ℝ} (hf : f ∈ compactTestFunctions) :
    CovariantUnderShiftsRotationsReflections D f := by
  have moves := fun r => (covariantUnderSymmetry hGroup hAct hPlaq D hf r).2.2.2.2
  obtain ⟨hIso, -⟩ := hGroup _ D.mesh_pos
  refine ⟨fun v => ?_, fun w hw => ?_, fun n c hM => ?_⟩
  · rw [moves]
    congr 1
    funext x
    have h := (shift v).pushforwardFun_apply_toFun f (x - (v : AmbientSpace))
    have e : (shift v).toFun (x - (v : AmbientSpace)) = x := sub_add_cancel x (v : AmbientSpace)
    rwa [e] at h
  · have hmap := (hIso ⇑w).2 ⟨w, hw, 0, fun x => by simp⟩
    let r : LatticeSymmetry D.mesh := ⟨⇑w, hmap.1, hmap.2⟩
    refine ⟨r, rfl, ?_⟩
    rw [moves]
    congr 1
    funext x
    have h := r.pushforwardFun_apply_toFun f (w.symm x)
    have e : r.toFun (w.symm x) = x := w.apply_symm_apply x
    rwa [e] at h
  · obtain ⟨hRefl, hLat, -, -⟩ := hMirror
    have hsurj := (hLat _ D.mesh_pos).1 _ hM
    obtain ⟨-, -, hiso, -, -, -, hinv, -, -⟩ := hRefl n c
    let r : LatticeSymmetry D.mesh := ⟨EuclideanMirrors.hyperplaneReflection n c, hiso, hsurj⟩
    refine ⟨r, rfl, ?_⟩
    rw [moves]
    congr 1
    funext x
    have h := r.pushforwardFun_apply_toFun f (EuclideanMirrors.hyperplaneReflection n c x)
    have e : r.toFun (EuclideanMirrors.hyperplaneReflection n c x) = x := hinv x
    rwa [e] at h
theorem finite_support_center {a : ℝ}
    (hfin : ∀ S : Set AmbientSpace, Bornology.IsBounded S →
      {p : ElementaryPlaquette a | p.center ∈ S}.Finite)
    {f : AmbientSpace → ℝ} (hf : f ∈ compactTestFunctions) :
    {p : ElementaryPlaquette a | f p.center ≠ 0}.Finite := by
  have hc : IsCompact (tsupport f) := hf.2.2
  exact (hfin _ hc.isBounded).subset fun p hp => subset_tsupport f hp
theorem smearedEnergy_eq_sum {a : ℝ} {f : AmbientSpace → ℝ}
    (hfin : {p : ElementaryPlaquette a | f p.center ≠ 0}.Finite) (U : GaugeField a) :
    smearedEnergy f U = ∑ p ∈ hfin.toFinset, faceEnergy U p * f p.center := by
  have hs : Function.support (fun p : ElementaryPlaquette a => faceEnergy U p • f p.center) ⊆
      ↑hfin.toFinset := by
    intro p hp
    simp only [Function.mem_support, smul_eq_mul] at hp
    simp only [Set.Finite.coe_toFinset]
    exact right_ne_zero_of_mul hp
  unfold smearedEnergy
  rw [finsum_eq_sum_of_support_subset _ hs]
  simp only [smul_eq_mul]
theorem faceEnergy_eq_of_restrict_eq {a : ℝ} {p : ElementaryPlaquette a}
    (hread : FactorsThroughFinite (CutoffLattice.faceLinks p)
      (fun U : GaugeField a => ((faceEnergy U p : ℝ) : ℂ)))
    {S : Set (Link a)} (hS : CutoffLattice.faceLinks p ⊆ S) {U U' : GaugeField a}
    (h : restrictField U S = restrictField U' S) :
    faceEnergy U p = faceEnergy U' p := by
  obtain ⟨-, -, φ, -, hφ⟩ := hread
  have h1 : restrictField U (CutoffLattice.faceLinks p) =
      restrictField U' (CutoffLattice.faceLinks p) := by
    funext b
    exact congrFun h ⟨b.1, hS b.2⟩
  have h2 := (hφ U).trans ((congrArg φ h1).trans (hφ U').symm)
  exact Complex.ofReal_injective h2
theorem smearedEnergy_dependsOnlyOnLinks {a : ℝ}
    (hread : ∀ p : ElementaryPlaquette a, FactorsThroughFinite (CutoffLattice.faceLinks p)
      (fun U : GaugeField a => ((faceEnergy U p : ℝ) : ℂ)))
    {f : AmbientSpace → ℝ} {S : Set (Link a)}
    (hS : ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → CutoffLattice.faceLinks p ⊆ S) :
    DependsOnlyOnLinks S (smearedEnergy f : GaugeField a → ℝ) := by
  intro U U' h
  unfold smearedEnergy
  refine finsum_congr fun p => ?_
  by_cases hp : f p.center = 0
  · simp [hp]
  · rw [faceEnergy_eq_of_restrict_eq (hread p) (hS p hp) h]
theorem edge_endpoints_mem {a : ℝ} {p : ElementaryPlaquette a} {S : Set AmbientSpace}
    (H : ∀ s t : ℝ, |s| ≤ |a / 2| → |t| ≤ |a / 2| → ∀ y : LatticePoint a,
      (y : AmbientSpace) = p.center + Pi.single p.lowAxis s + Pi.single p.highAxis t →
        (y : AmbientSpace) ∈ S)
    {b : Link a} (hb : b ∈ CutoffLattice.faceLinks p) :
    b ∈ positiveLinkSet a ∧ (b.initial : AmbientSpace) ∈ S ∧ (b.terminal : AmbientSpace) ∈ S := by
  have h0 : (p.corner : AmbientSpace) ∈ S := by
    refine H (-(a / 2)) (-(a / 2)) (by simp) (by simp) p.corner ?_
    funext μ
    simp only [ElementaryPlaquette.center, Pi.add_apply, Pi.single_apply]
    split_ifs <;> ring
  have h1 : (p.corner : AmbientSpace) + Pi.single p.lowAxis a ∈ S := by
    refine H (a / 2) (-(a / 2)) (by simp) (by simp) (p.corner + axisStep a p.lowAxis) ?_
    funext μ
    change (p.corner : AmbientSpace) μ + (Pi.single p.lowAxis a : AmbientSpace) μ = _
    simp only [ElementaryPlaquette.center, Pi.add_apply, Pi.single_apply]
    split_ifs <;> ring
  have h2 : (p.corner : AmbientSpace) + Pi.single p.highAxis a ∈ S := by
    refine H (-(a / 2)) (a / 2) (by simp) (by simp) (p.corner + axisStep a p.highAxis) ?_
    funext μ
    change (p.corner : AmbientSpace) μ + (Pi.single p.highAxis a : AmbientSpace) μ = _
    simp only [ElementaryPlaquette.center, Pi.add_apply, Pi.single_apply]
    split_ifs <;> ring
  have h3 : (p.corner : AmbientSpace) + Pi.single p.lowAxis a + Pi.single p.highAxis a ∈ S := by
    refine H (a / 2) (a / 2) (by simp) (by simp)
      (p.corner + axisStep a p.lowAxis + axisStep a p.highAxis) ?_
    funext μ
    change (p.corner : AmbientSpace) μ + (Pi.single p.lowAxis a : AmbientSpace) μ +
      (Pi.single p.highAxis a : AmbientSpace) μ = _
    simp only [ElementaryPlaquette.center, Pi.add_apply, Pi.single_apply]
    split_ifs <;> ring
  have h3' : (p.corner : AmbientSpace) + Pi.single p.highAxis a + Pi.single p.lowAxis a ∈ S := by
    rwa [add_right_comm]
  simp only [CutoffLattice.faceLinks, ElementaryPlaquette.edges, Set.mem_ofPred_eq, List.mem_cons,
    List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨⟨_, _, rfl⟩, h0, h1⟩
  · exact ⟨⟨_, _, rfl⟩, h1, h3⟩
  · exact ⟨⟨_, _, rfl⟩, h2, h3'⟩
  · exact ⟨⟨_, _, rfl⟩, h0, h2⟩
theorem reflNormal_integer_entries (n : EuclideanMirrors.ReflNormal) :
    ∃ z : Fin 4 → ℤ, (∀ μ, n.1 μ = (z μ : ℝ)) ∧ ∀ μ, |n.1 μ| ≤ 1 := by
  have hs : ∀ κ μ : Fin 4, (LatticeConventions.basisVector κ : AmbientSpace) μ =
      (((Pi.single κ 1 : Fin 4 → ℤ) μ : ℤ) : ℝ) := by
    intro κ μ
    by_cases h : μ = κ
    · subst h
      simp [LatticeConventions.basisVector]
    · simp [LatticeConventions.basisVector, Pi.single_eq_of_ne h]
  rcases n.2 with ⟨κ, h⟩ | ⟨κ, l, hl, h | h⟩
  · refine ⟨Pi.single κ 1, fun μ => by rw [h, hs], fun μ => ?_⟩
    rw [h]
    by_cases h' : μ = κ
    · subst h'
      simp [LatticeConventions.basisVector]
    · simp [LatticeConventions.basisVector, Pi.single_eq_of_ne h']
  · refine ⟨Pi.single κ 1 + Pi.single l 1, fun μ => by
      rw [h, Pi.add_apply, hs, hs]; simp, fun μ => ?_⟩
    rw [h]
    have hne : κ ≠ l := hl.ne
    by_cases h1 : μ = κ
    · subst h1
      simp [LatticeConventions.basisVector, Pi.single_eq_of_ne hne]
    · by_cases h2 : μ = l
      · subst h2
        simp [LatticeConventions.basisVector, Pi.single_eq_of_ne h1]
      · simp [LatticeConventions.basisVector, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
  · refine ⟨Pi.single κ 1 - Pi.single l 1, fun μ => by
      rw [h, Pi.sub_apply, hs, hs]; simp, fun μ => ?_⟩
    rw [h]
    have hne : κ ≠ l := hl.ne
    by_cases h1 : μ = κ
    · subst h1
      simp [LatticeConventions.basisVector, Pi.single_eq_of_ne hne]
    · by_cases h2 : μ = l
      · subst h2
        simp [LatticeConventions.basisVector, Pi.single_eq_of_ne h1]
      · simp [LatticeConventions.basisVector, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
theorem euclidDot_add_single (v x : AmbientSpace) (μ : Fin 4) (s : ℝ) :
    LatticeConventions.euclidDot v (x + Pi.single μ s) =
      LatticeConventions.euclidDot v x + v μ * s := by
  simp only [LatticeConventions.euclidDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ν _ hν
    simp [Pi.single_eq_of_ne hν]
  · simp
theorem euclidDot_corner_nonneg {a : ℝ} (ha : 0 < a) (n : EuclideanMirrors.ReflNormal)
    {p : ElementaryPlaquette a}
    (hpos : 0 < LatticeConventions.euclidDot n.1 p.center) {s t : ℝ} (hs : |s| ≤ |a / 2|)
    (ht : |t| ≤ |a / 2|) (y : LatticePoint a)
    (hy : (y : AmbientSpace) = p.center + Pi.single p.lowAxis s + Pi.single p.highAxis t) :
    0 ≤ LatticeConventions.euclidDot n.1 y := by
  obtain ⟨z, hz, hb⟩ := reflNormal_integer_entries n
  obtain ⟨m, hm⟩ : ∃ m : Fin 4 → ℤ, ∀ μ, (y : AmbientSpace) μ = (m μ : ℝ) * a := y.2
  have hk : LatticeConventions.euclidDot n.1 y = ((∑ μ, z μ * m μ : ℤ) : ℝ) * a := by
    simp only [LatticeConventions.euclidDot, hz, hm]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun μ _ => by ring
  have habs : |a / 2| = a / 2 := abs_of_pos (by linarith)
  rw [habs] at hs ht
  have hd : LatticeConventions.euclidDot n.1 y = LatticeConventions.euclidDot n.1 p.center +
      n.1 p.lowAxis * s + n.1 p.highAxis * t := by
    rw [hy, euclidDot_add_single, euclidDot_add_single]
  have b1 : -(a / 2) ≤ n.1 p.lowAxis * s := by
    have : |n.1 p.lowAxis * s| ≤ 1 * (a / 2) :=
      by rw [abs_mul]; exact mul_le_mul (hb _) hs (abs_nonneg _) zero_le_one
    have := (abs_le.1 this).1
    linarith
  have b2 : -(a / 2) ≤ n.1 p.highAxis * t := by
    have : |n.1 p.highAxis * t| ≤ 1 * (a / 2) :=
      by rw [abs_mul]; exact mul_le_mul (hb _) ht (abs_nonneg _) zero_le_one
    have := (abs_le.1 this).1
    linarith
  have hgt : -a < LatticeConventions.euclidDot n.1 y := by linarith
  rw [hk] at hgt ⊢
  have h1 : (-1 : ℝ) < ((∑ μ, z μ * m μ : ℤ) : ℝ) := by
    by_contra hc
    nlinarith
  have h2 : (-1 : ℤ) < ∑ μ, z μ * m μ := by exact_mod_cast h1
  have h3 : (0 : ℤ) ≤ ∑ μ, z μ * m μ := by omega
  have h4 : (0 : ℝ) ≤ ((∑ μ, z μ * m μ : ℤ) : ℝ) := by exact_mod_cast h3
  exact mul_nonneg h4 ha.le
theorem measurable_faceEnergy {a : ℝ} {p : ElementaryPlaquette a} {S : Set AmbientSpace}
    (hread : FactorsThroughFinite (CutoffLattice.faceLinks p)
      (fun U : GaugeField a => ((faceEnergy U p : ℝ) : ℂ)))
    (hS : CutoffLattice.faceLinks p ⊆ linksWithin S) :
    Measurable[regionSigma S] (fun U : GaugeField a => ((faceEnergy U p : ℝ) : ℂ)) := by
  obtain ⟨hfin, -, φ, hφc, hφ⟩ := hread
  have : Countable (CutoffLattice.faceLinks p) := hfin.countable.to_subtype
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have : SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
    TopologicalSpace.Subtype.secondCountableTopology
      (Matrices.ComplexMatrix2.specialUnitary : Set Matrices.ComplexMatrix2)
  have hr : Measurable[regionSigma S]
      (fun U : GaugeField a => restrictField U (CutoffLattice.faceLinks p)) := by
    refine @measurable_pi_lambda _ _ _ (regionSigma S) _ _ fun b => ?_
    refine measurable_iff_comap_le.2 ?_
    exact le_iSup₂_of_le (f := fun b (_ : b ∈ linksWithin S) =>
      MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) b.1 (hS b.2) le_rfl
  have he : (fun U : GaugeField a => ((faceEnergy U p : ℝ) : ℂ)) =
      φ ∘ fun U : GaugeField a => restrictField U (CutoffLattice.faceLinks p) := funext hφ
  rw [he]
  exact hφc.measurable.comp hr
theorem measurableOnClosedHalfSpace (hFacts : BasicFacts) (D : Setup) {f : AmbientSpace → ℝ}
    (hf : f ∈ compactTestFunctions) (n : EuclideanMirrors.ReflNormal) :
    MeasurableOnClosedHalfSpace D f n := by
  intro hv
  obtain ⟨-, hProd, hDense, -, -, hPF⟩ := hFacts D
  obtain ⟨hAct, hBdd, hObs, -, -⟩ := hPF
  have hread := fun p => (hAct p).1
  have ha := D.mesh_pos
  have hS : ∀ p : ElementaryPlaquette D.mesh, f p.center ≠ 0 → ∀ b ∈ CutoffLattice.faceLinks p,
      b ∈ positiveLinkSet D.mesh ∧ (b.initial : AmbientSpace) ∈ closedHalfSpace n ∧
        (b.terminal : AmbientSpace) ∈ closedHalfSpace n := by
    intro p hp b hb
    have hpos : 0 < LatticeConventions.euclidDot n.1 p.center := by
      by_contra hc
      exact hp (hv _ hc)
    exact edge_endpoints_mem (fun s t hs ht y hy => euclidDot_corner_nonneg ha n hpos hs ht y hy) hb
  have hcont : Continuous (curvatureObsComplex D f) := hDense.1 (hObs f hf).2
  have hfin := finite_support_center hBdd hf
  have := hProd.1
  refine ⟨⟨⟨hcont.measurable, ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
    exact ⟨C, fun U => hC U (mem_univ U)⟩
  · have he : curvatureObsComplex D f = fun U : D.Fields =>
        ∑ p ∈ hfin.toFinset, ((faceEnergy U p : ℝ) : ℂ) * ((f p.center : ℝ) : ℂ) := by
      funext U
      simp only [curvatureObsComplex, curvatureObs, smearedEnergy_eq_sum hfin U]
      push_cast
      rfl
    rw [he]
    refine Finset.measurable_sum _ fun p hp => ?_
    refine (measurable_faceEnergy (hread p) fun b hb => ?_).mul_const _
    have := hS p (by simpa using hp) b hb
    exact this.2
  · exact smearedEnergy_dependsOnlyOnLinks hread fun p hp b hb => by
      have := hS p hp b hb
      exact ⟨this.1, this.2⟩
theorem mem_closedCube_iff {x : AmbientSpace} {r : ℝ} : x ∈ closedCube r ↔ ∀ μ, |x μ| ≤ r := by
  simp only [closedCube, linfNorm, Set.mem_ofPred_eq, Finset.sup'_le_iff, Finset.mem_univ,
    true_imp_iff]
theorem corner_mem_closedCube {a R : ℝ} (ha : 0 < a) {p : ElementaryPlaquette a}
    (hp : p.center ∈ closedCube R) {s t : ℝ} (hs : |s| ≤ |a / 2|) (ht : |t| ≤ |a / 2|)
    (y : LatticePoint a)
    (hy : (y : AmbientSpace) = p.center + Pi.single p.lowAxis s + Pi.single p.highAxis t) :
    (y : AmbientSpace) ∈ closedCube (R + a / 2) := by
  have habs : |a / 2| = a / 2 := abs_of_pos (by linarith)
  rw [habs] at hs ht
  rw [mem_closedCube_iff] at hp ⊢
  intro μ
  have hne : p.lowAxis ≠ p.highAxis := p.lowAxis_lt_highAxis.ne
  have hb := hp μ
  rw [hy]
  simp only [Pi.add_apply, Pi.single_apply]
  by_cases h1 : μ = p.lowAxis
  · have h2 : μ ≠ p.highAxis := h1 ▸ hne
    simp only [h1, if_true, hne, if_false, add_zero] at hb ⊢
    exact (abs_add_le _ _).trans (add_le_add hb hs)
  · by_cases h2 : μ = p.highAxis
    · simp only [h2, if_true, hne.symm, if_false, add_zero] at hb ⊢
      exact (abs_add_le _ _).trans (add_le_add hb ht)
    · simp only [h1, h2, if_false, add_zero]
      linarith
theorem card_Icc_ceil_floor_le (lo c : ℝ) (hc : 0 ≤ c) :
    ((Finset.Icc ⌈lo⌉ ⌊lo + c⌋).card : ℝ) ≤ c + 1 := by
  rw [Int.card_Icc]
  have h1 : (⌊lo + c⌋ : ℝ) ≤ lo + c := Int.floor_le _
  have h2 : lo ≤ ⌈lo⌉ := Int.le_ceil _
  by_cases h : 0 ≤ ⌊lo + c⌋ + 1 - ⌈lo⌉
  · have h3 : (((⌊lo + c⌋ + 1 - ⌈lo⌉).toNat : ℤ) : ℝ) = ((⌊lo + c⌋ + 1 - ⌈lo⌉ : ℤ) : ℝ) := by
      rw [Int.toNat_of_nonneg h]
    have h4 : (((⌊lo + c⌋ + 1 - ⌈lo⌉).toNat : ℕ) : ℝ) =
        (((⌊lo + c⌋ + 1 - ⌈lo⌉).toNat : ℤ) : ℝ) := by norm_cast
    rw [h4, h3]
    push_cast
    linarith
  · have h3 : (⌊lo + c⌋ + 1 - ⌈lo⌉).toNat = 0 := Int.toNat_of_nonpos (by omega)
    rw [h3]
    simp only [Nat.cast_zero]
    linarith
theorem card_filter_axes_le {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R)
    (T : Finset (ElementaryPlaquette a))
    (hT : ∀ p ∈ T, p.center ∈ closedCube R) (q : Fin 4 × Fin 4) :
    (((T.filter fun p => (p.lowAxis, p.highAxis) = q).card : ℕ) : ℝ) ≤ (2 * R / a + 1) ^ 4 := by
  classical
  have hc : ∀ p : ElementaryPlaquette a, ∃ n : Fin 4 → ℤ,
      ∀ μ, (p.corner : AmbientSpace) μ = (n μ : ℝ) * a :=
    fun p => p.corner.2
  choose c hc using hc
  let δ : Fin 4 → ℝ := fun μ => (if μ = q.1 then a / 2 else 0) + (if μ = q.2 then a / 2 else 0)
  let lo : Fin 4 → ℝ := fun μ => (-R - δ μ) / a
  let I : Fin 4 → Finset ℤ := fun μ => Finset.Icc ⌈lo μ⌉ ⌊lo μ + 2 * R / a⌋
  have hle : ((T.filter fun p => (p.lowAxis, p.highAxis) = q).card : ℕ) ≤
      (Fintype.piFinset I).card := by
    refine Finset.card_le_card_of_injOn c ?_ ?_
    · intro p hp
      have hp' := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
      have hq : (p.lowAxis, p.highAxis) = q := hp'.2
      have hcube := mem_closedCube_iff.1 (hT p hp'.1)
      refine Finset.mem_coe.2 (Fintype.mem_piFinset.2 fun μ => ?_)
      have hbar : p.center μ = (c p μ : ℝ) * a + δ μ := by
        subst hq
        simp only [ElementaryPlaquette.center, Pi.add_apply, Pi.single_apply, hc, δ]
        ring
      have hb := abs_le.1 (hcube μ)
      rw [hbar] at hb
      refine Finset.mem_Icc.2 ⟨Int.ceil_le.2 ?_, Int.le_floor.2 ?_⟩
      · change (-R - δ μ) / a ≤ _
        rw [div_le_iff₀ ha]
        linarith [hb.1]
      · change _ ≤ (-R - δ μ) / a + 2 * R / a
        rw [← add_div, le_div_iff₀ ha]
        linarith [hb.2]
    · intro p hp p' hp' h
      have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
      have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hp')).2
      have h3 := h1.trans h2.symm
      refine ElementaryPlaquette.ext (Subtype.ext (funext fun μ => ?_)) (congrArg Prod.fst h3)
        (congrArg Prod.snd h3)
      rw [hc, hc, h]
  have hprod : (((Fintype.piFinset I).card : ℕ) : ℝ) ≤ (2 * R / a + 1) ^ 4 := by
    rw [Fintype.card_piFinset]
    push_cast
    calc ∏ μ, ((I μ).card : ℝ) ≤ ∏ _μ : Fin 4, (2 * R / a + 1) :=
          Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
            fun μ _ => card_Icc_ceil_floor_le _ _ (by positivity)
      _ = (2 * R / a + 1) ^ 4 := by simp
  exact le_trans (by exact_mod_cast hle) hprod
theorem card_le_of_center_mem {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R)
    (T : Finset (ElementaryPlaquette a))
    (hT : ∀ p ∈ T, p.center ∈ closedCube R) :
    (T.card : ℝ) ≤ 6 * (2 * R / a + 1) ^ 4 := by
  classical
  let P : Finset (Fin 4 × Fin 4) := Finset.univ.filter fun q => q.1 < q.2
  have hP : P.card = 6 := by decide
  have hmaps : ∀ p ∈ T, (p.lowAxis, p.highAxis) ∈ P := fun p _ =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, p.lowAxis_lt_highAxis⟩
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := fun p : ElementaryPlaquette a => (p.lowAxis, p.highAxis)) (s := T) (t := P) hmaps
  calc (T.card : ℝ) =
        ∑ q ∈ P, (((T.filter fun p => (p.lowAxis, p.highAxis) = q).card : ℕ) : ℝ) := by
        rw [hsum]
        push_cast
        rfl
    _ ≤ ∑ _q ∈ P, (2 * R / a + 1) ^ 4 :=
        Finset.sum_le_sum fun q _ => card_filter_axes_le ha hR T hT q
    _ = 6 * (2 * R / a + 1) ^ 4 := by
        rw [Finset.sum_const, hP]
        simp
theorem localAndBounded (hFacts : BasicFacts) (D : Setup) {f : AmbientSpace → ℝ}
    (hf : f ∈ compactTestFunctions) (R : ℝ) : LocalAndBounded D f R := by
  intro hR hsupp
  obtain ⟨hSp, -, hDense, -, hInt, hPF⟩ := hFacts D
  obtain ⟨hAct, hBdd, hObs, -, -⟩ := hPF
  have hread := fun p => (hAct p).1
  have ha := D.mesh_pos
  have ha1 : D.mesh ≤ 1 := hSp.1
  have hcont : Continuous (curvatureObsComplex D f) := hDense.1 (hObs f hf).2
  have hfin := finite_support_center hBdd hf
  have hbary : ∀ p : ElementaryPlaquette D.mesh, f p.center ≠ 0 → p.center ∈ closedCube R :=
    fun p hp => hsupp (subset_tsupport f hp)
  refine ⟨?_, ?_, ?_⟩
  · have hW : IsLinkSet (((D.cubeWindow (R + D.mesh / 2)).links : Set (Link D.mesh))) :=
      fun b hb => (D.mem_cubeWindow.1 hb).1
    refine hInt.1 _ (Finset.finite_toSet _) hW _ hcont ?_
    have hfun : DependsOnlyOnLinks ((D.cubeWindow (R + D.mesh / 2)).links : Set (Link D.mesh))
        (smearedEnergy f : GaugeField D.mesh → ℝ) :=
      smearedEnergy_dependsOnlyOnLinks hread fun p hp b hb => by
        have hends := edge_endpoints_mem (S := closedCube (R + D.mesh / 2))
          (fun s t hs ht y hy => corner_mem_closedCube ha (hbary p hp) hs ht y hy) hb
        exact D.mem_cubeWindow.2 hends
    intro U U' h
    exact congrArg (fun x : ℝ => (x : ℂ)) (hfun U U' h)
  · intro b hb
    obtain ⟨h1, h2, h3⟩ := D.mem_cubeWindow.1 hb
    have hmono : ∀ x : AmbientSpace, x ∈ closedCube (R + D.mesh / 2) → x ∈ closedCube (R + 1) := by
      intro x hx
      rw [mem_closedCube_iff] at hx ⊢
      intro μ
      linarith [hx μ]
    exact D.mem_cubeWindow.2 ⟨h1, hmono _ h2, hmono _ h3⟩
  · intro U
    have hbound : ∀ x, |f x| ≤ TestFunctions.uniformNorm f := by
      obtain ⟨C, hC⟩ := hf.2.1
      intro x
      exact le_ciSup (f := fun x => ‖f x‖) ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩ x
    have hS0 : 0 ≤ TestFunctions.uniformNorm f := Real.iSup_nonneg fun x => norm_nonneg _
    have hcard := card_le_of_center_mem ha hR hfin.toFinset fun p hp =>
      hbary p (by simpa using hp)
    have hsum : |curvatureObs D f U| ≤ ∑ _p ∈ hfin.toFinset, 2 * TestFunctions.uniformNorm f := by
      simp only [curvatureObs, smearedEnergy_eq_sum hfin U]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
      rw [abs_mul]
      obtain ⟨h0, h2⟩ := (hAct p).2 U
      rw [abs_of_nonneg h0]
      exact mul_le_mul h2 (hbound _) (abs_nonneg _) (by norm_num)
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have hRa : 2 * R / D.mesh + 1 ≤ 2 * (R / D.mesh + 1) := by
      have : 2 * R / D.mesh = 2 * (R / D.mesh) := by ring
      rw [this]
      linarith
    have hnn : 0 ≤ 2 * R / D.mesh + 1 := by positivity
    have hpow : (2 * R / D.mesh + 1) ^ 4 ≤ 16 * (R / D.mesh + 1) ^ 4 := by
      calc (2 * R / D.mesh + 1) ^ 4 ≤ (2 * (R / D.mesh + 1)) ^ 4 := pow_le_pow_left₀ hnn hRa 4
        _ = 16 * (R / D.mesh + 1) ^ 4 := by ring
    have hc2 : (hfin.toFinset.card : ℝ) ≤ 96 * (R / D.mesh + 1) ^ 4 := by linarith
    calc |curvatureObs D f U| ≤ (hfin.toFinset.card : ℝ) * (2 * TestFunctions.uniformNorm f) := hsum
      _ ≤ (96 * (R / D.mesh + 1) ^ 4) * (2 * TestFunctions.uniformNorm f) :=
          mul_le_mul_of_nonneg_right hc2 (by positivity)
      _ = curvatureBound * TestFunctions.uniformNorm f * (R / D.mesh + 1) ^ 4 := by
          simp only [curvatureBound]
          ring
def periodSite (D : Setup) (h : latticeSubgroup D.side ≤ D.latticeSites) (k : Fin 4 → ℤ) :
    LatticePoint D.mesh :=
  ⟨TestFunctions.latticeTranslate D.side k,
    h ⟨k, fun μ => by simp [TestFunctions.latticeTranslate, mul_comm]⟩⟩
theorem center_translateFace (D : Setup) (p : ElementaryPlaquette D.mesh) (v : LatticePoint D.mesh) :
    (CutoffLattice.translateFace p v).center = p.center + (v : AmbientSpace) := by
  funext μ
  simp only [CutoffLattice.translateFace, CutoffLattice.face, ElementaryPlaquette.center,
    AddSubgroup.coe_add, Pi.add_apply]
  ring
theorem side_ne_zero (hFacts : BasicFacts) (D : Setup) : D.side ≠ 0 := by
  intro h
  have h4 := (hFacts D).1.2.2.2.1
  rw [h, zero_div] at h4
  norm_num at h4
theorem periodization_center_eq_sum (hFacts : BasicFacts)
    (hCover : TorusCovering.Statement) (D : Setup) {f : AmbientSpace → ℝ}
    [DecidableEq D.TorusFace]
    (s : Finset (ElementaryPlaquette D.mesh)) (hs : ∀ p : ElementaryPlaquette D.mesh, f p.center ≠ 0 → p ∈ s)
    (p₀ : ElementaryPlaquette D.mesh) :
    D.periodization f (D.projFace p₀).barycenter =
      ∑ p ∈ s.filter (fun p => D.projFace p = D.projFace p₀), f p.center := by
  obtain ⟨⟨-, -, hle, -⟩, -, ⟨-, hfib, hbary⟩, -⟩ := hCover D
  have hside := side_ne_zero hFacts D
  rw [(hbary p₀).2.2, D.periodization_proj]
  set e : (Fin 4 → ℤ) → ElementaryPlaquette D.mesh :=
    fun k => CutoffLattice.translateFace p₀ (periodSite D hle k) with he
  have hbe : ∀ k, (e k).center = p₀.center + TestFunctions.latticeTranslate D.side k :=
    fun k => center_translateFace D _ _
  have hinj : Function.Injective e := by
    intro k k' h
    have hb : p₀.corner + periodSite D hle k = p₀.corner + periodSite D hle k' :=
      congrArg ElementaryPlaquette.corner h
    have hv := add_left_cancel hb
    funext μ
    have hμ : TestFunctions.latticeTranslate D.side k μ = TestFunctions.latticeTranslate D.side k' μ :=
      congrFun (congrArg Subtype.val hv) μ
    simp only [TestFunctions.latticeTranslate] at hμ
    exact_mod_cast mul_left_cancel₀ hside hμ
  have hmem : ∀ p, D.projFace p₀ = D.projFace p ↔ p ∈ range e := by
    intro p
    constructor
    · intro h
      obtain ⟨v, ⟨n, hn⟩, rfl⟩ := ((hfib p₀ p).1).1 h
      refine ⟨n, ?_⟩
      have : periodSite D hle n = v := by
        apply Subtype.ext
        funext μ
        change D.side * (n μ : ℝ) = _
        rw [hn μ, mul_comm]
      simp only [he, this]
    · rintro ⟨k, rfl⟩
      exact ((hfib p₀ (e k)).1).2 ⟨periodSite D hle k, ⟨k, fun μ => by
        change D.side * (k μ : ℝ) = _
        rw [mul_comm]⟩, rfl⟩
  let G : ElementaryPlaquette D.mesh → ℝ :=
    fun p => if D.projFace p = D.projFace p₀ then f p.center else 0
  have h1 : ∀ k, f (p₀.center + TestFunctions.latticeTranslate D.side k) = G (e k) := by
    intro k
    have hk : D.projFace (e k) = D.projFace p₀ := ((hmem (e k)).2 ⟨k, rfl⟩).symm
    simp only [G, if_pos hk, hbe]
  rw [tsum_congr h1, hinj.tsum_eq]
  · rw [tsum_eq_sum (s := s.filter (fun p => D.projFace p = D.projFace p₀))]
    · refine Finset.sum_congr rfl fun p hp => ?_
      simp only [G, if_pos (Finset.mem_filter.1 hp).2]
    · intro p hp
      simp only [G]
      split_ifs with hc
      · by_contra hne
        exact hp (Finset.mem_filter.2 ⟨hs p hne, hc⟩)
      · rfl
  · intro p hp
    simp only [G, Function.mem_support] at hp
    by_cases hc : D.projFace p = D.projFace p₀
    · exact (hmem p).1 hc.symm
    · simp [if_neg hc] at hp
theorem liftCompatible (hFacts : BasicFacts)
    (hCover : TorusCovering.Statement) (D : Setup) {f : AmbientSpace → ℝ}
    (hf : f ∈ compactTestFunctions) : LiftCompatible D f := by
  classical
  intro U
  obtain ⟨-, -, ⟨hsurj, -, -⟩, ⟨-, -, hact, -⟩⟩ := hCover D
  have hfin : {p : ElementaryPlaquette D.mesh | f p.center ≠ 0}.Finite :=
    ((hFacts D).2.2.2.2.2.2.1 (tsupport f) hf.2.2.isCompact.isBounded).subset
      fun p hp => subset_tsupport f hp
  set s := hfin.toFinset with hsdef
  have hs : ∀ p : ElementaryPlaquette D.mesh, f p.center ≠ 0 → p ∈ s :=
    fun p hp => hfin.mem_toFinset.2 hp
  change ∑ᶠ p : ElementaryPlaquette D.mesh, faceEnergy (liftCompactField U) p • f p.center =
    ∑ᶠ P : D.TorusFace,
      PeriodicLattice.plaquetteCost U.1 P • D.periodization f P.barycenter
  rw [finsum_eq_sum_of_support_subset (s := s) _ (fun p hp => by
      simp only [Function.mem_support] at hp
      exact Finset.mem_coe.2 (hs p fun h => hp (by rw [h, smul_zero]))),
    finsum_eq_sum_of_support_subset (s := s.image D.projFace) _ (fun P hP => by
      simp only [Function.mem_support] at hP
      have hne : D.periodization f P.barycenter ≠ 0 := fun h => hP (by rw [h, smul_zero])
      obtain ⟨p₀, rfl⟩ := hsurj P
      rw [periodization_center_eq_sum hFacts hCover D s hs p₀] at hne
      obtain ⟨p, hp, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨p, hp1, hp2⟩))]
  rw [← Finset.sum_fiberwise_of_maps_to (g := D.projFace) (t := s.image D.projFace)
    (fun p hp => Finset.mem_image_of_mem _ hp)]
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨p₀, -, rfl⟩ := Finset.mem_image.1 hP
  rw [periodization_center_eq_sum hFacts hCover D s hs p₀, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [hact U p, (Finset.mem_filter.1 hp).2]
  rfl
theorem continuous_smearedEnergy (hFacts : BasicFacts) (D : Setup) {f : AmbientSpace → ℝ}
    (hf : f ∈ compactTestFunctions) :
    Continuous fun U : D.Fields => ((smearedEnergy f U : ℝ) : ℂ) :=
  (hFacts D).2.2.1.1 ((hFacts D).2.2.2.2.2.2.2.1 f hf).2
theorem torusConnectedEqCumulant (hFacts : BasicFacts)
    (hCover : TorusCovering.Statement) (D : Setup) {n : ℕ}
    (f : Fin n → AmbientSpace → ℝ) (hf : ∀ i, f i ∈ compactTestFunctions) :
    TorusConnectedEqCumulant D f := by
  refine ⟨?_, rfl⟩
  obtain ⟨-, -, -, ⟨-, -, -, hcont'⟩⟩ := hCover D
  have hcont : Continuous D.lift := hcont'
  have hgen : Cumulants.momentGeneratingFunction D.liftedGibbs (fun i => curvatureObs D (f i)) =
      Cumulants.momentGeneratingFunction D.gibbs
        (fun i => D.smeared (D.periodization (f i))) := by
    funext t
    unfold Cumulants.momentGeneratingFunction Setup.liftedGibbs
    rw [integral_map (hcont.measurable.aemeasurable)]
    · refine integral_congr_ae (ae_of_all _ fun U => ?_)
      have : ∀ i, curvatureObs D (f i) (D.lift U) =
          D.smeared (D.periodization (f i)) U :=
        fun i => liftCompatible hFacts hCover D (hf i) U
      simp only [this]
    · apply Continuous.aestronglyMeasurable
      refine Complex.continuous_exp.comp (continuous_finsetSum _ fun i _ => ?_)
      exact continuous_const.mul (continuous_smearedEnergy hFacts D (hf i))
  unfold Setup.torusConnected Setup.cumulant Cumulants.mixedCumulant
  rw [hgen]
theorem measurableEmbedding_linkValues (L m : ℕ) (j : ℤ)
    [CompactSpace (PeriodicLattice.CompactGaugeField L m j)] :
    MeasurableEmbedding (fun U : PeriodicLattice.CompactGaugeField L m j => U.1) := by
  have : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  have hinj : Function.Injective (fun U : PeriodicLattice.CompactGaugeField L m j => U.1) :=
    Subtype.val_injective
  have hc : Continuous (fun U : PeriodicLattice.CompactGaugeField L m j => U.1) :=
    continuous_pi fun b => by
      have h1 : Continuous fun U : PeriodicLattice.CompactGaugeField L m j =>
          PeriodicLattice.CompactGaugeField.linkValue U b :=
        continuous_iInf_dom (i := b) continuous_induced_dom
      exact continuous_subtype_val.comp h1
  exact (hc.isClosedEmbedding hinj).measurableEmbedding
theorem gibbs_eq_boltzmannMeasure (hProd : GaugeFieldProduct.Statement) (D : Setup) :
    D.gibbs = PeriodicLattice.normalizedActionMeasure D.L D.m D.level D.β := by
  have hL := D.admissible
  obtain ⟨-, ⟨-, -, hfin, -⟩, -, hpa⟩ :=
    hProd.1 D.L D.m (D.level : ℤ) hL D.m.pos (by positivity)
  let _ : Fintype (PeriodicLattice.Plaquette D.L D.m (D.level : ℤ)) := Fintype.ofFinite _
  have hw : ∀ U : D.TorusFields,
      PeriodicLattice.barycenterWeightedEnergy (fun _ => (D.β : ℂ)) U.1 =
        ((D.β * D.wilsonEnergy U : ℝ) : ℂ) := by
    intro U
    have h1 : PeriodicLattice.barycenterWeightedEnergy (fun _ => (D.β : ℂ)) U.1 =
        ∑ p : PeriodicLattice.Plaquette D.L D.m (D.level : ℤ),
          (D.β : ℂ) * PeriodicLattice.plaquetteEnergy U.1 p :=
      finsum_eq_sum_of_fintype _
    have h2 : D.wilsonEnergy U = ∑ p : PeriodicLattice.Plaquette D.L D.m (D.level : ℤ),
        PeriodicLattice.plaquetteCost U.1 p := finsum_eq_sum_of_fintype _
    rw [h1, h2, Finset.mul_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    obtain ⟨t, -, ht⟩ := (hpa p).2 U
    have h3 : PeriodicLattice.plaquetteCost U.1 p = t := by
      have : PeriodicLattice.plaquetteCost U.1 p =
          (PeriodicLattice.plaquetteEnergy U.1 p).re := by
        simp [PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteEnergy]
      rw [this, ← ht]
      simp
    rw [h3, ← ht]
    push_cast
    rfl
  have hexp : ∀ U : D.TorusFields,
      Complex.exp (-PeriodicLattice.barycenterWeightedEnergy (fun _ => (D.β : ℂ)) U.1) =
        ((Real.exp (-D.β * D.wilsonEnergy U) : ℝ) : ℂ) := by
    intro U
    rw [hw U, neg_mul]
    push_cast
    rfl
  have hZ : (PeriodicLattice.sourcedPartitionFunction D.L D.m D.level D.β 0).re =
      D.partitionFunction := by
    unfold PeriodicLattice.sourcedPartitionFunction Setup.partitionFunction
    have : ∀ U : D.TorusFields,
        Complex.exp (-PeriodicLattice.barycenterWeightedEnergy
            (fun y => (D.β : ℂ) - (0 : PeriodicLattice.FourTorus D.L D.m → ℂ) y) U.1) =
          ((Real.exp (-D.β * D.wilsonEnergy U) : ℝ) : ℂ) := by
      intro U
      rw [← hexp U]
      congr 3
      funext y
      simp
    simp only [this]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  unfold Setup.gibbs PeriodicLattice.normalizedActionMeasure
  rw [hZ]
  congr 2
  funext U
  rw [hexp U, Complex.ofReal_re]
theorem mixedCumulant_map {L m : ℕ} {j : ℤ} {n : ℕ}
    [CompactSpace (PeriodicLattice.CompactGaugeField L m j)]
    (ν : Measure (PeriodicLattice.CompactGaugeField L m j))
    (X : Fin n → (PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2) → ℝ) :
    Cumulants.mixedCumulant (ν.map fun U => U.1) X =
      Cumulants.mixedCumulant ν fun i U => X i U.1 := by
  have hgen : Cumulants.momentGeneratingFunction (ν.map fun U => U.1) X =
      Cumulants.momentGeneratingFunction ν fun i U => X i U.1 := by
    funext t
    unfold Cumulants.momentGeneratingFunction
    exact (measurableEmbedding_linkValues L m j).integral_map _
  unfold Cumulants.mixedCumulant
  rw [hgen]
theorem torusConnectedEqSchwinger (hSum : ConnectedFunctionExpansion.Statement)
    (hProd : GaugeFieldProduct.Statement) (D : Setup) {n : ℕ} (f : Fin n → AmbientSpace → ℝ) :
    TorusConnectedEqSchwinger D f := by
  intro hK _ _
  have hL := D.admissible
  obtain ⟨-, -, ⟨-, -, hcomp, -⟩, -⟩ := hProd.1 D.L D.m (D.level : ℤ) hL D.m.pos (by positivity)
  have hmap := ((hSum D.L D.m D.level hL D.m.pos).2.2.2.2.1 D.β).2.2.2.2 hK D.β_pos
  unfold Setup.torusConnected Setup.cumulant SchwingerFunctions.connectedSchwingerR4
    SchwingerFunctions.connectedSchwinger PeriodicLattice.gibbsCumulant
  rw [← hmap.2, mixedCumulant_map, ← gibbs_eq_boltzmannMeasure hProd D]
  rfl
theorem curvatureProperties (hGroup : LatticeSymmetryGroup.SymmetryGroupStatement)
    (hAct : LatticeSymmetryActions)
    (hPlaq : FaceEnergyAndExponentialCovariance)
    (hMirror : EuclideanMirrors.MirrorReflections.Statement)
    (hFacts : BasicFacts)
    (hCover : TorusCovering.Statement)
    (hSum : ConnectedFunctionExpansion.Statement)
    (hProd : GaugeFieldProduct.Statement) : CurvatureConditions := by
  intro D
  exact ⟨fun f hf => ⟨fun r => covariantUnderSymmetry hGroup hAct hPlaq D hf r,
      covariantUnderShiftsRotationsReflections hGroup hAct hPlaq hMirror D hf,
      fun n => measurableOnClosedHalfSpace hFacts D hf n, fun R => localAndBounded hFacts D hf R,
      liftCompatible hFacts hCover D hf⟩,
    fun n f _ hf => ⟨torusConnectedEqCumulant hFacts hCover D f hf,
      torusConnectedEqSchwinger hSum hProd D f⟩⟩
end YangMills.Construction.FixedSpacing.CurvatureObservable
end
