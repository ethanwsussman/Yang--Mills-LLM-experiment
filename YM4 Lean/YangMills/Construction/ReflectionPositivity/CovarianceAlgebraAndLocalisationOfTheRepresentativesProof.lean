import YangMills.Construction.InfiniteLattice.IsometriesOfALatticePlaquettesAndGenerators
import YangMills.Construction.ReflectionPositivity.CovarianceAlgebraAndLocalisationOfTheRepresentatives
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity.RepresentativeCovariance
open SeparatedTupleFunctionals (contCompactSupp)
open InfiniteLattice (Link GaugeField LatticeSymmetry ElementaryPlaquette LatticePoint AmbientSpace
  refinedSpacing latticeMotion affineHyperoctahedralMaps linksWithin boundedRegionObservables
  faceEnergy regionSigma latticeSubgroup axisStep)
open LimitConventions (ApproxTriple supDist)
open SeparatedTuples (FormalSpan TupleFunctional IsC1c IsDisjointlySupported RealValued SepTuple
  push pushSpan pushList conjugation linearExtend invMap basisVec)
instance instSecondCountableSpecialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
  haveI : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _
section BoundedContinuousMeasurable
variable {Ω : Type*} [TopologicalSpace Ω] {m : MeasurableSpace Ω}
def IsCBM (m : MeasurableSpace Ω) (F : Ω → ℝ) : Prop :=
  Continuous F ∧ (∃ C : ℝ, ∀ ω, |F ω| ≤ C) ∧ Measurable[m] F
theorem isCBM_const (c : ℝ) : IsCBM m fun _ => c :=
  ⟨continuous_const, ⟨|c|, fun _ => le_rfl⟩, measurable_const⟩
theorem IsCBM.add {F G : Ω → ℝ} (hF : IsCBM m F) (hG : IsCBM m G) :
    IsCBM m fun ω => F ω + G ω := by
  obtain ⟨hFc, ⟨C, hC⟩, hFm⟩ := hF
  obtain ⟨hGc, ⟨D, hD⟩, hGm⟩ := hG
  exact ⟨hFc.add hGc, ⟨C + D, fun ω => (abs_add_le _ _).trans (add_le_add (hC ω) (hD ω))⟩,
    hFm.add hGm⟩
theorem IsCBM.mul {F G : Ω → ℝ} (hF : IsCBM m F) (hG : IsCBM m G) :
    IsCBM m fun ω => F ω * G ω := by
  obtain ⟨hFc, ⟨C, hC⟩, hFm⟩ := hF
  obtain ⟨hGc, ⟨D, hD⟩, hGm⟩ := hG
  refine ⟨hFc.mul hGc, ⟨|C| * |D|, fun ω => ?_⟩, hFm.mul hGm⟩
  rw [abs_mul]
  exact mul_le_mul ((hC ω).trans (le_abs_self C)) ((hD ω).trans (le_abs_self D)) (abs_nonneg _)
    (abs_nonneg _)
theorem isCBM_finsetSum {ι : Type*} (s : Finset ι) (F : ι → Ω → ℝ)
    (hF : ∀ i ∈ s, IsCBM m (F i)) :
    IsCBM m fun ω => ∑ i ∈ s, F i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCBM_const (m := m) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self i s)).add
      (ih fun k hk => hF k (Finset.mem_insert_of_mem hk))
theorem isCBM_listProd {ι : Type*} (X : List ι) (F : ι → Ω → ℝ) (hF : ∀ f ∈ X, IsCBM m (F f)) :
    IsCBM m fun ω => (X.map fun f => F f ω).prod := by
  induction X with
  | nil => simpa using isCBM_const (m := m) 1
  | cons f X ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hF f (by simp)).mul (ih fun k hk => hF k (by simp [hk]))
end BoundedContinuousMeasurable
section Plaquettes
variable {a : ℝ}
theorem finite_center_mem_of_isBounded (ha : 0 < a) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) :
    {p : ElementaryPlaquette a | p.center ∈ S}.Finite := by
  classical
  obtain ⟨R, hR⟩ := hS.subset_closedBall (0 : AmbientSpace)
  let N : ℤ := ⌈(|R| + a) / a⌉
  have hbox : (Set.Icc (fun _ => -N) (fun _ => N) : Set (Fin 4 → ℤ)).Finite := Set.finite_Icc _ _
  let φ : ElementaryPlaquette a → AmbientSpace × Fin 4 × Fin 4 :=
    fun p => ((p.corner : AmbientSpace), p.lowAxis, p.highAxis)
  have hφ : Function.Injective φ := by
    intro p q h
    simp only [φ, Prod.mk.injEq] at h
    exact ElementaryPlaquette.ext (Subtype.ext h.1) h.2.1 h.2.2
  refine Set.Finite.of_finite_image ?_ hφ.injOn
  refine ((hbox.image fun n : Fin 4 → ℤ => (fun μ => (n μ : ℝ) * a : AmbientSpace)).prod
    (Set.finite_univ (α := Fin 4 × Fin 4))).subset ?_
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨n, hn⟩ := p.corner.2
  refine ⟨⟨n, ?_, funext fun μ => (hn μ).symm⟩, Set.mem_univ _⟩
  have hsingle : ∀ (κ μ : Fin 4), |(Pi.single κ (a / 2) : AmbientSpace) μ| ≤ a / 2 := by
    intro κ μ
    by_cases h : μ = κ
    · subst h
      rw [Pi.single_eq_same, abs_of_pos (half_pos ha)]
    · rw [Pi.single_eq_of_ne h, abs_zero]
      exact (half_pos ha).le
  have hbound : ∀ μ, |(n μ : ℝ)| * a ≤ |R| + a := by
    intro μ
    have hb : |p.center μ| ≤ |R| := by
      have h1 : ‖p.center‖ ≤ R := by simpa using hR hp
      exact (norm_le_pi_norm p.center μ).trans (h1.trans (le_abs_self R))
    have heq : (p.corner : AmbientSpace) μ = p.center μ -
        (Pi.single p.lowAxis (a / 2) : AmbientSpace) μ -
        (Pi.single p.highAxis (a / 2) : AmbientSpace) μ := by
      simp only [ElementaryPlaquette.center, Pi.add_apply]
      ring
    have h2 := hsingle p.lowAxis μ
    have h3 := hsingle p.highAxis μ
    have h4 : |(p.corner : AmbientSpace) μ| ≤ |R| + a := by
      rw [heq]
      calc _ ≤ |p.center μ - (Pi.single p.lowAxis (a / 2) : AmbientSpace) μ| +
            |(Pi.single p.highAxis (a / 2) : AmbientSpace) μ| := abs_sub _ _
        _ ≤ |p.center μ| + |(Pi.single p.lowAxis (a / 2) : AmbientSpace) μ| +
            |(Pi.single p.highAxis (a / 2) : AmbientSpace) μ| := by
            gcongr
            exact abs_sub _ _
        _ ≤ |R| + a := by linarith
    rw [hn μ, abs_mul, abs_of_pos ha] at h4
    exact h4
  have hN : (|R| + a) / a ≤ (N : ℝ) := Int.le_ceil _
  constructor
  · intro μ
    have h1 : |(n μ : ℝ)| ≤ N := ((le_div_iff₀ ha).2 (hbound μ)).trans hN
    have h2 : -(N : ℝ) ≤ n μ := (abs_le.1 h1).1
    exact_mod_cast h2
  · intro μ
    have h1 : |(n μ : ℝ)| ≤ N := ((le_div_iff₀ ha).2 (hbound μ)).trans hN
    have h2 : (n μ : ℝ) ≤ N := (abs_le.1 h1).2
    exact_mod_cast h2
theorem finite_center_support (ha : 0 < a) {f : AmbientSpace → ℝ} (hf : HasCompactSupport f) :
    {p : ElementaryPlaquette a | f p.center ≠ 0}.Finite :=
  (finite_center_mem_of_isBounded ha (S := tsupport f) hf.isCompact.isBounded).subset
    fun _ hp => subset_tsupport f hp
def energyOfHolonomy
    (q : Matrices.ComplexMatrix2.specialUnitary × Matrices.ComplexMatrix2.specialUnitary ×
      Matrices.ComplexMatrix2.specialUnitary × Matrices.ComplexMatrix2.specialUnitary) : ℝ :=
  1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
    ((q.1 * q.2.1 * q.2.2.1⁻¹ * q.2.2.2⁻¹ : Matrices.ComplexMatrix2.specialUnitary) :
      Matrices.ComplexMatrix2)).re
theorem continuous_energyOfHolonomy : Continuous energyOfHolonomy := by
  unfold energyOfHolonomy
  have h : Continuous fun q : Matrices.ComplexMatrix2.specialUnitary ×
      Matrices.ComplexMatrix2.specialUnitary × Matrices.ComplexMatrix2.specialUnitary ×
      Matrices.ComplexMatrix2.specialUnitary =>
      q.1 * q.2.1 * q.2.2.1⁻¹ * q.2.2.2⁻¹ := by fun_prop
  have h' : Continuous fun q : Matrices.ComplexMatrix2.specialUnitary ×
      Matrices.ComplexMatrix2.specialUnitary × Matrices.ComplexMatrix2.specialUnitary ×
      Matrices.ComplexMatrix2.specialUnitary =>
      ((q.1 * q.2.1 * q.2.2.1⁻¹ * q.2.2.2⁻¹ : Matrices.ComplexMatrix2.specialUnitary) :
        Matrices.ComplexMatrix2) := continuous_subtype_val.comp h
  have h'' := Continuous.matrix_trace h'
  exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp h''))
theorem continuous_eval_link (b : Link a) : Continuous fun U : GaugeField a => U b :=
  (continuous_apply b).comp continuous_subtype_val
theorem isCBM_faceEnergy {m : MeasurableSpace (GaugeField a)} (p : ElementaryPlaquette a)
    (hb : ∀ b ∈ p.edges, Measurable[m] fun U : GaugeField a => U b) :
    IsCBM m fun U : GaugeField a => faceEnergy U p := by
  have hc := continuous_energyOfHolonomy
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have h : (fun U : GaugeField a => faceEnergy U p) = energyOfHolonomy ∘
      fun U : GaugeField a => (U (Link.forwardFrom p.corner p.lowAxis),
        U (Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis),
        U (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis),
        U (Link.forwardFrom p.corner p.highAxis)) := rfl
  rw [h]
  refine ⟨?_, ⟨C, fun U => ?_⟩, ?_⟩
  · exact hc.comp ((continuous_eval_link _).prodMk ((continuous_eval_link _).prodMk
      ((continuous_eval_link _).prodMk (continuous_eval_link _))))
  · exact hC _ (Set.mem_univ _)
  · refine hc.measurable.comp (Measurable.prodMk (hb _ ?_) (Measurable.prodMk (hb _ ?_)
      (Measurable.prodMk (hb _ ?_) (hb _ ?_)))) <;> simp [ElementaryPlaquette.edges]
end Plaquettes
section Smearing
variable {a : ℝ}
def plaquetteSmearing (c : ℝ) (f : AmbientSpace → ℝ) (U : GaugeField a) : ℝ :=
  ∑ᶠ p : ElementaryPlaquette a, f p.center * (faceEnergy U p - c)
theorem plaquetteSmearing_eq_finsetSum (ha : 0 < a) (c : ℝ) {f : AmbientSpace → ℝ}
    (hf : HasCompactSupport f) :
    ∃ s : Finset (ElementaryPlaquette a), (∀ p ∈ s, f p.center ≠ 0) ∧ ∀ U : GaugeField a,
      plaquetteSmearing c f U = ∑ p ∈ s, f p.center * (faceEnergy U p - c) := by
  refine ⟨(finite_center_support ha hf).toFinset, fun p hp => by simpa using hp, fun U => ?_⟩
  refine finsum_eq_sum_of_support_subset _ ?_
  intro p hp
  simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
  intro h0
  exact hp (by simp [h0])
theorem plaquetteSmearing_linear (ha : 0 < a) (c : ℝ) {f f' : AmbientSpace → ℝ}
    (hf : HasCompactSupport f) (hf' : HasCompactSupport f') (α α' : ℝ) (U : GaugeField a) :
    plaquetteSmearing c (α • f + α' • f') U =
      α * plaquetteSmearing c f U + α' * plaquetteSmearing c f' U := by
  have hF : (Function.support fun p : ElementaryPlaquette a =>
      f p.center * (faceEnergy U p - c)).Finite :=
    (finite_center_support ha hf).subset fun p hp h0 => hp (by simp [h0])
  have hG : (Function.support fun p : ElementaryPlaquette a =>
      f' p.center * (faceEnergy U p - c)).Finite :=
    (finite_center_support ha hf').subset fun p hp h0 => hp (by simp [h0])
  have hF' : (Function.support fun p : ElementaryPlaquette a =>
      α * (f p.center * (faceEnergy U p - c))).Finite :=
    hF.subset fun p hp h0 => hp (by simp [h0])
  have hG' : (Function.support fun p : ElementaryPlaquette a =>
      α' * (f' p.center * (faceEnergy U p - c))).Finite :=
    hG.subset fun p hp h0 => hp (by simp [h0])
  unfold plaquetteSmearing
  rw [mul_finsum, mul_finsum, ← finsum_add_distrib hF' hG']
  refine finsum_congr fun p => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem plaquetteSmearing_pullbackField (c : ℝ) (r : LatticeSymmetry a)
    (hbij : Function.Bijective r.plaquetteMap)
    (hbar : ∀ p : ElementaryPlaquette a, (r.plaquetteMap p).center = r.toFun p.center)
    (hact : ∀ p : ElementaryPlaquette a, r.actOn (fun U : GaugeField a => faceEnergy U p) =
      fun U : GaugeField a => faceEnergy U (r.plaquetteMap p))
    (f : AmbientSpace → ℝ) (U : GaugeField a) :
    plaquetteSmearing c f (r.pullbackField U) = plaquetteSmearing c (r.pushforwardFun f) U := by
  unfold plaquetteSmearing
  rw [← finsum_comp_equiv (Equiv.ofBijective _ hbij)
    (f := fun q => r.pushforwardFun f q.center * (faceEnergy U q - c))]
  refine finsum_congr fun p => ?_
  have h1 := congrFun (hact p) U
  simp only [Equiv.ofBijective_apply]
  rw [hbar, LatticeSymmetry.pushforwardFun_apply_toFun, ← h1]
  rfl
def symmOfEquiv (r : LatticeSymmetry a) (e : AmbientSpace ≃ AmbientSpace)
    (he : ∀ x, e x = r.toFun x) : LatticeSymmetry a where
  toFun := e.symm
  preservesDist x y := by
    have h := r.preservesDist (e.symm x) (e.symm y)
    rw [← he, ← he] at h
    simpa using h.symm
  image_eq := by
    have h := r.image_eq
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ r.toFun '' (latticeSubgroup a : Set AmbientSpace) := by
        rw [h]
        exact hy
      obtain ⟨z, hz, rfl⟩ := hy'
      rw [← he]
      simpa using hz
    · intro hx
      have hx' : r.toFun x ∈ r.toFun '' (latticeSubgroup a : Set AmbientSpace) := ⟨x, hx, rfl⟩
      rw [h] at hx'
      exact ⟨r.toFun x, hx', by rw [← he]; simp⟩
def affineHomeomorph (w : AmbientSpace ≃ₗ[ℝ] AmbientSpace) (v : AmbientSpace) :
    AmbientSpace ≃ₜ AmbientSpace where
  toFun x := w x + v
  invFun x := w.symm (x - v)
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := (w.toLinearMap.continuous_of_finiteDimensional).add continuous_const
  continuous_invFun :=
    (w.symm.toLinearMap.continuous_of_finiteDimensional).comp (continuous_id.sub continuous_const)
theorem exists_homeomorph_contDiff_symm (r : LatticeSymmetry a)
    (hr : r.toFun ∈ affineHyperoctahedralMaps a) :
    ∃ e : AmbientSpace ≃ₜ AmbientSpace, (∀ x, e x = r.toFun x) ∧ ContDiff ℝ 1 e.symm := by
  obtain ⟨w, -, v, h⟩ := hr
  refine ⟨affineHomeomorph w v, fun x => by rw [h]; rfl, ?_⟩
  exact (w.symm.toLinearMap.toContinuousLinearMap).contDiff.comp (contDiff_id.sub contDiff_const)
theorem invMap_eq_symm (r : LatticeSymmetry a) (e : AmbientSpace ≃ₜ AmbientSpace)
    (he : ∀ x, e x = r.toFun x) :
    invMap r.toFun = e.symm := by
  funext x
  have h : r.toFun (e.symm x) = x := by
    rw [← he]
    simp
  calc invMap r.toFun x = invMap r.toFun (r.toFun (e.symm x)) := by rw [h]
    _ = e.symm x := Function.leftInverse_invFun r.toFun_injective _
theorem bijective_plaquetteMap
    (hD : ∀ (r : LatticeSymmetry a) (p : ElementaryPlaquette a),
      (∃! q : ElementaryPlaquette a, q.cornerSet = r.pointMap '' p.cornerSet) ∧
        (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet)
    (r : LatticeSymmetry a) (e : AmbientSpace ≃ AmbientSpace) (he : ∀ x, e x = r.toFun x) :
    Function.Bijective r.plaquetteMap := by
  let s := symmOfEquiv r e he
  have hsr : ∀ x : LatticePoint a, s.pointMap (r.pointMap x) = x := fun x => Subtype.ext (by
    change e.symm (r.toFun x) = x
    rw [← he]
    simp)
  have hrs : ∀ x : LatticePoint a, r.pointMap (s.pointMap x) = x := fun x => Subtype.ext (by
    change r.toFun (e.symm x) = x
    rw [← he]
    simp)
  have hsr' : ∀ C : Set (LatticePoint a), s.pointMap '' (r.pointMap '' C) = C := fun C => by
    rw [Set.image_image]
    simp [hsr]
  have hrs' : ∀ C : Set (LatticePoint a), r.pointMap '' (s.pointMap '' C) = C := fun C => by
    rw [Set.image_image]
    simp [hrs]
  have key : ∀ (t : LatticeSymmetry a) (p q : ElementaryPlaquette a),
      q.cornerSet = t.pointMap '' p.cornerSet → t.plaquetteMap p = q :=
    fun t p q h => (hD t p).1.unique (hD t p).2 h
  constructor
  · intro p q hpq
    have h1 : s.plaquetteMap (r.plaquetteMap p) = p := key s _ _ (by rw [(hD r p).2, hsr'])
    have h2 : s.plaquetteMap (r.plaquetteMap q) = q := key s _ _ (by rw [(hD r q).2, hsr'])
    rw [← h1, hpq, h2]
  · intro q
    exact ⟨s.plaquetteMap q, key r _ _ (by rw [(hD s q).2, hrs'])⟩
theorem tsupport_comp_homeomorph_symm (e : AmbientSpace ≃ₜ AmbientSpace) (f : RealValued) :
    tsupport (f ∘ e.symm) = e.symm ⁻¹' tsupport f := by
  unfold tsupport
  rw [Function.support_comp_eq_preimage]
  exact (e.symm.preimage_closure _).symm
theorem isDisjointlySupported_map_comp (e : AmbientSpace ≃ₜ AmbientSpace)
    (he : ContDiff ℝ 1 e.symm) {X : List RealValued}
    (hX : IsDisjointlySupported X) : IsDisjointlySupported (X.map fun f => f ∘ e.symm) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    obtain ⟨h1, h2⟩ := hX.1 f hf
    refine ⟨(show ContDiff ℝ 1 f from h1).comp he, ?_⟩
    change IsCompact (tsupport _)
    rw [tsupport_comp_homeomorph_symm]
    exact e.symm.isCompact_preimage.2 h2
  · rw [List.pairwise_map]
    refine hX.2.imp ?_
    intro f h hfh
    rw [tsupport_comp_homeomorph_symm, tsupport_comp_homeomorph_symm]
    exact hfh.preimage _
theorem supNorm_vertex_sub_center_le (p : ElementaryPlaquette a) (ha : 0 < a) {y : AmbientSpace}
    {ε ε' : ℝ} (hε : ε = 0 ∨ ε = a) (hε' : ε' = 0 ∨ ε' = a)
    (hy : y = (p.corner : AmbientSpace) + Pi.single p.lowAxis ε + Pi.single p.highAxis ε') :
    LatticeConventions.supNorm (y - p.center) ≤ a / 2 := by
  have key : ∀ t : ℝ, (t = 0 ∨ t = a) → |t - a / 2| ≤ a / 2 := by
    rintro t (rfl | rfl) <;> rw [abs_le] <;> constructor <;> linarith
  have hne : p.lowAxis ≠ p.highAxis := p.lowAxis_lt_highAxis.ne
  refine Finset.sup'_le _ _ fun μ _ => ?_
  subst hy
  simp only [ElementaryPlaquette.center, Pi.sub_apply, Pi.add_apply]
  by_cases h1 : μ = p.lowAxis
  · have h2 : μ ≠ p.highAxis := h1 ▸ hne
    rw [h1] at h2 ⊢
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne h2]
    refine (le_of_eq (congrArg abs ?_)).trans (key ε hε)
    ring
  · by_cases h2 : μ = p.highAxis
    · rw [h2] at h1 ⊢
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne h1]
      refine (le_of_eq (congrArg abs ?_)).trans (key ε' hε')
      ring
    · simp only [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
      simp only [add_zero, sub_self, abs_zero]
      linarith
theorem edges_mem_linksWithin (ha : 0 < a) (p : ElementaryPlaquette a) {S : Set AmbientSpace}
    (hS : ∀ y : AmbientSpace, LatticeConventions.supNorm (y - p.center) ≤ a / 2 → y ∈ S) :
    ∀ b ∈ p.edges, b ∈ (linksWithin S : Set (Link a)) := by
  have c00 : ((p.corner : LatticePoint a) : AmbientSpace) ∈ S :=
    hS _ (supNorm_vertex_sub_center_le p ha (ε := 0) (ε' := 0) (Or.inl rfl) (Or.inl rfl)
      (by simp))
  have c10 : ((p.corner + axisStep a p.lowAxis : LatticePoint a) : AmbientSpace) ∈ S :=
    hS _ (supNorm_vertex_sub_center_le p ha (ε := a) (ε' := 0) (Or.inr rfl) (Or.inl rfl)
      (by simp [axisStep]))
  have c01 : ((p.corner + axisStep a p.highAxis : LatticePoint a) : AmbientSpace) ∈ S :=
    hS _ (supNorm_vertex_sub_center_le p ha (ε := 0) (ε' := a) (Or.inl rfl) (Or.inr rfl)
      (by simp [axisStep]))
  have c11 : ((p.corner + axisStep a p.lowAxis + axisStep a p.highAxis : LatticePoint a) :
      AmbientSpace) ∈ S :=
    hS _ (supNorm_vertex_sub_center_le p ha (ε := a) (ε' := a) (Or.inr rfl) (Or.inr rfl)
      (by simp [axisStep]))
  have c11' : ((p.corner + axisStep a p.highAxis + axisStep a p.lowAxis : LatticePoint a) :
      AmbientSpace) ∈ S := by
    rw [add_right_comm]
    exact c11
  intro b hb
  simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨c00, c10⟩
  · exact ⟨c10, c11⟩
  · exact ⟨c01, c11'⟩
  · exact ⟨c00, c01⟩
theorem measurable_eval_link {S : Set AmbientSpace} {b : Link a}
    (hb : b ∈ (linksWithin S : Set (Link a))) :
    Measurable[regionSigma S] fun U : GaugeField a => U b :=
  measurable_iff_comap_le.2 (le_iSup₂_of_le (f := fun b _ =>
    MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) b hb le_rfl)
theorem isCBM_plaquetteSmearing (ha : 0 < a) (c : ℝ) {f : AmbientSpace → ℝ}
    (hf : HasCompactSupport f) {m : MeasurableSpace (GaugeField a)}
    (hb : ∀ p : ElementaryPlaquette a, f p.center ≠ 0 → ∀ b ∈ p.edges,
      Measurable[m] fun U : GaugeField a => U b) :
    IsCBM m (plaquetteSmearing c f : GaugeField a → ℝ) := by
  obtain ⟨s, hs, hsum⟩ := plaquetteSmearing_eq_finsetSum (a := a) ha c hf
  have h : (plaquetteSmearing c f : GaugeField a → ℝ) = fun U : GaugeField a =>
      ∑ p ∈ s, f p.center * (faceEnergy U p + -c) := by
    funext U
    simp only [hsum U, sub_eq_add_neg]
  rw [h]
  exact isCBM_finsetSum s _ fun p hp => (isCBM_const _).mul
    ((isCBM_faceEnergy p (hb p (hs p hp))).add (isCBM_const (-c)))
theorem isCBM_tupleProd (ha : 0 < a) (c : ℝ) (X : SepTuple) :
    IsCBM (regionSigma (supportHalo a X))
      fun U : GaugeField a => (X.1.map fun f => plaquetteSmearing c f U).prod := by
  refine isCBM_listProd X.1 (fun f => plaquetteSmearing c f) fun f hf =>
    isCBM_plaquetteSmearing ha c (X.2.1 f hf).2 fun p hp b hb => measurable_eval_link
      (edges_mem_linksWithin ha p (fun y hy => ?_) b hb)
  have hmem : p.center ∈ ⋃ f ∈ X.1, tsupport f :=
    Set.mem_iUnion₂.2 ⟨f, hf, subset_tsupport f hp⟩
  have hle : supDist y (⋃ f ∈ X.1, tsupport f) ≤
      ENNReal.ofReal (LatticeConventions.supNorm (y - p.center)) :=
    iInf₂_le (f := fun z _ => ENNReal.ofReal (LatticeConventions.supNorm (y - z))) p.center hmem
  exact hle.trans (ENNReal.ofReal_le_ofReal hy)
theorem isBounded_supportHalo (ha : 0 < a) (X : SepTuple) :
    Bornology.IsBounded (supportHalo a X) := by
  have hU : Bornology.IsBounded (⋃ f ∈ X.1, tsupport f) :=
    (Bornology.isBounded_biUnion (List.finite_toSet X.1)).2 fun f hf =>
      (X.2.1 f hf).2.isCompact.isBounded
  obtain ⟨R, hR⟩ := hU.subset_closedBall (0 : AmbientSpace)
  refine (Metric.isBounded_closedBall (x := (0 : AmbientSpace)) (r := R + (a / 2 + 1))).subset ?_
  intro x hx
  have hlt : supDist x (⋃ f ∈ X.1, tsupport f) < ENNReal.ofReal (a / 2 + 1) :=
    lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
  unfold supDist at hlt
  obtain ⟨y, hlt'⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hy, hxy⟩ := iInf_lt_iff.1 hlt'
  have h1 : LatticeConventions.supNorm (x - y) < a / 2 + 1 :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 hxy
  rw [LatticeConventions.supNorm_eq_norm] at h1
  have h2 : ‖y‖ ≤ R := by simpa using hR hy
  have h3 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by simpa using norm_add_le (x - y) y
  simp only [Metric.mem_closedBall, dist_zero_right]
  linarith
end Smearing
section Representatives
variable {L : ℕ} (T : ApproxTriple L) (j : ℕ+)
theorem tupleRep_apply_eq (X : SepTuple)
    (U : InfiniteLattice.RefinedGaugeField L (T.cutoff j)) :
    T.tupleRep j X U = (X.1.map fun f => plaquetteSmearing (T.offset j) f U).prod := rfl
theorem tupleRep_pullbackField (r : LatticeSymmetry (refinedSpacing L (T.cutoff j)))
    (e : AmbientSpace ≃ₜ AmbientSpace) (he : ∀ x, e x = r.toFun x) (hcd : ContDiff ℝ 1 e.symm)
    (hbij : Function.Bijective r.plaquetteMap)
    (hbar : ∀ p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)),
      (r.plaquetteMap p).center = r.toFun p.center)
    (hact : ∀ p : ElementaryPlaquette (refinedSpacing L (T.cutoff j)),
      r.actOn (fun U : GaugeField (refinedSpacing L (T.cutoff j)) =>
        faceEnergy U p) =
        fun U : GaugeField (refinedSpacing L (T.cutoff j)) => faceEnergy U (r.plaquetteMap p))
    (X : SepTuple) (U : InfiniteLattice.RefinedGaugeField L (T.cutoff j)) :
    T.tupleRep j X (r.pullbackField U) =
      T.tupleRep j (push r.toFun X) U := by
  have hsep : IsDisjointlySupported (pushList r.toFun X.1) := by
    unfold pushList
    rw [invMap_eq_symm r e he]
    exact isDisjointlySupported_map_comp e hcd X.2
  have hval : (push r.toFun X).1 = pushList r.toFun X.1 := by
    unfold push
    rw [dif_pos hsep]
  rw [tupleRep_apply_eq, tupleRep_apply_eq, hval]
  unfold pushList
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun f _ => ?_
  exact plaquetteSmearing_pullbackField _ r hbij hbar hact f U
theorem actOn_spanRep (r : LatticeSymmetry (refinedSpacing L (T.cutoff j)))
    (hX : ∀ (X : SepTuple) (U : InfiniteLattice.RefinedGaugeField L (T.cutoff j)),
      T.tupleRep j X (r.pullbackField U) =
        T.tupleRep j (push r.toFun X) U)
    (Z : FormalSpan) :
    r.actOn (T.spanRep j Z) =
      T.spanRep j (pushSpan r.toFun Z) := by
  induction Z using Finsupp.induction_linear with
  | zero =>
    funext U
    simp [InfiniteLattice.LatticeSymmetry.actOn]
  | add Z W hZ hW =>
    rw [map_add, map_add, map_add, ← hZ, ← hW]
    rfl
  | single X c =>
    have h : Finsupp.single X c = c • basisVec X := by simp [basisVec]
    rw [h, map_smul, map_smul, map_smul]
    funext U
    simp only [ApproxTriple.spanRep, pushSpan,
      SeparatedTuples.linearExtend_basisVec, InfiniteLattice.LatticeSymmetry.actOn,
      Pi.smul_apply, hX]
theorem conj_spanRep (Z : FormalSpan)
    (U : InfiniteLattice.RefinedGaugeField L (T.cutoff j)) :
    conj (T.spanRep j Z U) = T.spanRep j (conjugation Z) U := by
  induction Z using Finsupp.induction_linear with
  | zero => simp
  | add Z W hZ hW => simp only [map_add, Pi.add_apply, hZ, hW]
  | single X c =>
    have h : Finsupp.single X c = c • basisVec X := by simp [basisVec]
    rw [h, map_smul, map_smulₛₗ, map_smul, SeparatedTuples.conjugation_basisVec]
    simp [ApproxTriple.spanRep, SeparatedTuples.linearExtend_basisVec]
theorem tupleRep_juxt {X Y : SepTuple} (h : SepTuple.Composable X Y) :
    T.tupleRep j (SepTuple.juxt X Y) =
      T.tupleRep j X * T.tupleRep j Y := by
  funext U
  rw [Pi.mul_apply, tupleRep_apply_eq, tupleRep_apply_eq, tupleRep_apply_eq,
    SepTuple.juxt_val h, List.map_append, List.prod_append]
theorem integrable_tupleRep (ha : 0 < refinedSpacing L (T.cutoff j)) (X : SepTuple) :
    Integrable (T.tupleRep j X) (T.state j) := by
  obtain ⟨hc, ⟨C, hC⟩, -⟩ := isCBM_tupleProd ha (T.offset j) X
  exact Integrable.of_bound hc.measurable.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun U => by
      rw [Real.norm_eq_abs]
      exact hC U)
def expectationFunctional : TupleFunctional where
  toFun X := ∫ U, T.tupleRep j X U ∂T.state j
  map_nil := by
    have h : ∀ U, T.tupleRep j SepTuple.nil U = 1 := fun U => rfl
    simp [h]
theorem isPermInvariant_expectationFunctional : (expectationFunctional T j).IsPermInvariant := by
  intro X ς
  change ∫ U, T.tupleRep j (X.reorder ς) U ∂T.state j =
    ∫ U, T.tupleRep j X U ∂T.state j
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  have hp : (X.reorder ς).1.Perm X.1 := by
    simpa [SepTuple.reorder] using Equiv.Perm.ofFn_comp_perm ς X.1.get
  exact (hp.map _).prod_eq
theorem isEntrywiseLinear_expectationFunctional (ha : 0 < refinedSpacing L (T.cutoff j)) :
    (expectationFunctional T j).IsEntrywiseLinear := by
  intro A B f f' α α' X X' Z hX hX' hZ
  have hf : HasCompactSupport f := (X.2.1 f (by rw [hX]; simp)).2
  have hf' : HasCompactSupport f' := (X'.2.1 f' (by rw [hX']; simp)).2
  change ∫ U, T.tupleRep j Z U ∂T.state j =
    α * ∫ U, T.tupleRep j X U ∂T.state j +
      α' * ∫ U, T.tupleRep j X' U ∂T.state j
  have hpt : ∀ U, T.tupleRep j Z U =
      α * T.tupleRep j X U + α' * T.tupleRep j X' U := by
    intro U
    rw [tupleRep_apply_eq, tupleRep_apply_eq, tupleRep_apply_eq, hX, hX', hZ]
    simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    rw [plaquetteSmearing_linear ha _ hf hf']
    ring
  simp only [hpt]
  rw [integral_add ((integrable_tupleRep T j ha X).const_mul α)
    ((integrable_tupleRep T j ha X').const_mul α'), integral_const_mul, integral_const_mul]
end Representatives
theorem representativesCovariantAndLocal_holds
    (H : InfiniteLattice.SymmetriesFacesAndGenerators.Claim) :
    RepresentativesCovariantAndLocal := by
  intro L hL T j
  have ha : 0 < refinedSpacing L (T.cutoff j) := by
    have hL0 : (0 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 0 < L)
    exact zpow_pos hL0 _
  obtain ⟨-, -, hC, hD, -, -⟩ := H _ ha
  have hfacts : ∀ r : LatticeSymmetry (refinedSpacing L (T.cutoff j)),
      r.toFun ∈ affineHyperoctahedralMaps (refinedSpacing L (T.cutoff j)) ∧
      ∃ e : AmbientSpace ≃ₜ AmbientSpace, (∀ x, e x = r.toFun x) ∧ ContDiff ℝ 1 e.symm ∧
        Function.Bijective r.plaquetteMap := by
    intro r
    have hrm := (hC r.toFun).1 ⟨r, rfl⟩
    obtain ⟨e, he, hcd⟩ := exists_homeomorph_contDiff_symm r hrm
    exact ⟨hrm, e, he, hcd, bijective_plaquetteMap
      (fun r p => ⟨(hD r p).1, (hD r p).2.1⟩) r e.toEquiv he⟩
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro r
    obtain ⟨hrm, e, he, hcd, hbij⟩ := hfacts r
    refine ⟨hrm, fun p => (hD r p).2.1, hbij, fun p => (hD r p).2.2.1, fun p => (hD r p).2.2.2,
      fun f _ => ?_⟩
    funext U
    exact plaquetteSmearing_pullbackField _ r hbij (fun p => (hD r p).2.2.1)
      (fun p => (hD r p).2.2.2) f U
  · intro r Z
    obtain ⟨-, e, he, hcd, hbij⟩ := hfacts r
    exact actOn_spanRep T j r (tupleRep_pullbackField T j r e he hcd hbij
      (fun p => (hD r p).2.2.1) (fun p => (hD r p).2.2.2)) Z
  · intro X Y h
    exact tupleRep_juxt T j h
  · intro Z
    funext U
    exact conj_spanRep T j Z U
  · intro X
    obtain ⟨hc, ⟨C, hCb⟩, hm⟩ := isCBM_tupleProd ha (T.offset j) X
    refine ⟨hc, ⟨⟨?_, C, fun U => ?_⟩, ?_⟩, isBounded_supportHalo ha X⟩
    · exact Complex.measurable_ofReal.comp hc.measurable
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact hCb U
    · exact Complex.measurable_ofReal.comp hm
  · intro f hf f' hf' α α'
    funext U
    exact plaquetteSmearing_linear ha _ hf.2 hf'.2 α α' U
  · exact ⟨expectationFunctional T j, fun X => rfl, isPermInvariant_expectationFunctional T j,
      isEntrywiseLinear_expectationFunctional T j ha⟩
end ReflectionPositivity.RepresentativeCovariance
end YangMills.Construction
end
