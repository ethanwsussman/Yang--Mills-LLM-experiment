import YangMills.Construction.InfiniteLattice.ExpansionsMeetTheConditionsOfTheReconstructionProof
import YangMills.Construction.InfiniteLattice.ReconstructionAtALatticeMirrorProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexOrder
namespace YangMills.Construction
namespace LatticeConventions
namespace ObservableRules
open InfiniteLattice (GaugeField IsSymmetricUnder IsSpaceIsometry IsBoundedObservable
  LatticeSymmetry LatticePoint localRegionObservables observableSupNorm boundedRegionObservables
  AmbientSpace shift)
open NormalHyperplane (reflectSymmetry)
variable {a : ℝ}
theorem symmetry_ext {r s : LatticeSymmetry a} (h : r.toFun = s.toFun) : r = s := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem euclidDot_comm (x y : Point) : euclidDot x y = euclidDot y x :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _
theorem euclidDot_add_right (x y z : Point) :
    euclidDot x (y + z) = euclidDot x y + euclidDot x z := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.euclidDot_add <;> assumption
theorem euclidDot_smul_right (k : ℝ) (x y : Point) : euclidDot x (k • y) = k * euclidDot x y := by apply _root_.YangMills.Construction.LatticeConventions.MirrorExpansionsProof.euclidDot_smul_right <;> assumption
theorem euclidDot_sub_right (x y z : Point) :
    euclidDot x (y - z) = euclidDot x y - euclidDot x z := by
  simp [euclidDot, mul_sub, Finset.sum_sub_distrib]
theorem euclidDot_smul_left (k : ℝ) (x y : Point) : euclidDot (k • x) y = k * euclidDot x y := by
  rw [euclidDot_comm, euclidDot_smul_right, euclidDot_comm]
theorem euclidDot_sub_left (x y z : Point) :
    euclidDot (x - y) z = euclidDot x z - euclidDot y z := by apply _root_.YangMills.Construction.LatticeConventions.MirrorExpansionsProof.euclidDot_sub_left <;> assumption
theorem euclidNorm_sq (x : Point) : euclidNorm x ^ 2 = euclidDot x x := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.euclidNorm_sq_eq_selfDot <;> assumption
theorem euclidDot_normal_self_ne_zero (Q : NormalHyperplane) : euclidDot Q.normal Q.normal ≠ 0 := by
  intro h
  have hz : ∀ μ, Q.normal μ = 0 := fun μ => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun μ _ => mul_self_nonneg (Q.normal μ)).mp h μ
      (Finset.mem_univ μ)
    exact mul_self_eq_zero.mp this
  rcases Q.normal_valid with ⟨μ, hμ⟩ | ⟨μ, lam, hne, hμ | hμ⟩
  · have := hz μ
    rw [hμ] at this
    simp [basisVector] at this
  · have := hz μ
    rw [hμ] at this
    simp [basisVector, hne.symm] at this
  · have := hz μ
    rw [hμ] at this
    simp [basisVector, hne.symm] at this
theorem reflectionLinear_isOrthogonal (Q : NormalHyperplane) :
    IsOrthogonalMap Q.reflectionLinear := by
  intro x y
  have hN := euclidDot_normal_self_ne_zero Q
  have hs : ∀ w : Point, Q.reflectionLinear w =
      w - (2 * (euclidDot Q.normal Q.normal)⁻¹ * euclidDot Q.normal w) • Q.normal := fun w => by
    rw [← euclidNorm_sq]
    rfl
  rw [hs, hs]
  simp only [euclidDot_sub_left, euclidDot_sub_right, euclidDot_smul_left, euclidDot_smul_right]
  rw [euclidDot_comm x Q.normal]
  field_simp
  ring
theorem imageSet_eq_of_forall_mem_iff {r : LatticeSymmetry a} (hr : Function.Surjective r.toFun)
    {S S' : Set Point} (h : ∀ x, x ∈ S ↔ r.toFun x ∈ S') : r.setImage S = S' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx
  · intro hy
    obtain ⟨x, rfl⟩ := hr y
    exact ⟨x, (h x).2 hy, rfl⟩
theorem level_apply_of_maps {r : LatticeSymmetry a} {R : Point →ₗ[ℝ] Point} {v : LatticePoint a}
    {ε : ℝ} {Q Q' : NormalHyperplane} (h : MapsHyperplane r R v ε Q Q') (x : Point) :
    euclidDot Q'.normal (r.toFun x) - Q'.level = ε * (euclidDot Q.normal x - Q.level) := by
  obtain ⟨hr, hR, _, hn, hc⟩ := h
  rw [hr, hn, hc, euclidDot_smul_left, euclidDot_add_right, hR]
  ring
theorem normal_norm_sq_of_maps {r : LatticeSymmetry a} {R : Point →ₗ[ℝ] Point}
    {v : LatticePoint a} {ε : ℝ} {Q Q' : NormalHyperplane} (h : MapsHyperplane r R v ε Q Q') :
    euclidNorm Q'.normal ^ 2 = euclidNorm Q.normal ^ 2 := by
  obtain ⟨_, hR, hε, hn, _⟩ := h
  rw [euclidNorm_sq, euclidNorm_sq, hn, euclidDot_smul_left, euclidDot_smul_right, hR]
  rcases hε with rfl | rfl <;> ring
theorem reflect_apply_of_maps {r : LatticeSymmetry a} {R : Point →ₗ[ℝ] Point}
    {v : LatticePoint a} {ε : ℝ} {Q Q' : NormalHyperplane} (h : MapsHyperplane r R v ε Q Q')
    (x : Point) : Q'.reflect (r.toFun x) = r.toFun (Q.reflect x) := by
  have hl := level_apply_of_maps h x
  have hN := normal_norm_sq_of_maps h
  obtain ⟨hr, _, hε, hn, _⟩ := h
  simp only [NormalHyperplane.reflect]
  rw [hl, hN, hn, hr, hr, map_sub, map_smul, smul_smul]
  have hk : 2 * (ε * (euclidDot Q.normal x - Q.level)) / euclidNorm Q.normal ^ 2 * ε =
      2 * (euclidDot Q.normal x - Q.level) / euclidNorm Q.normal ^ 2 := by
    rcases hε with rfl | rfl <;> ring
  rw [hk]
  abel
theorem maps_carrier_halfSpaces_reflect {r : LatticeSymmetry a} {R : Point →ₗ[ℝ] Point}
    {v : LatticePoint a} {ε : ℝ} {Q Q' : NormalHyperplane} (hs : Function.Surjective r.toFun)
    (h : MapsHyperplane r R v ε Q Q') :
    r.setImage Q.carrier = Q'.carrier ∧
      (ε = 1 → r.setImage Q.upperHalfSpace = Q'.upperHalfSpace ∧
        r.setImage Q.lowerHalfSpace = Q'.lowerHalfSpace) ∧
      (ε = -1 → r.setImage Q.upperHalfSpace = Q'.lowerHalfSpace ∧
        r.setImage Q.lowerHalfSpace = Q'.upperHalfSpace) ∧
      ∀ t : LatticeSymmetry a, t.IsInverse r →
        Q'.reflect = r.toFun ∘ Q.reflect ∘ t.toFun := by
  have hl := level_apply_of_maps h
  refine ⟨imageSet_eq_of_forall_mem_iff hs fun x => ?_,
    fun hε => ⟨imageSet_eq_of_forall_mem_iff hs fun x => ?_,
      imageSet_eq_of_forall_mem_iff hs fun x => ?_⟩,
    fun hε => ⟨imageSet_eq_of_forall_mem_iff hs fun x => ?_,
      imageSet_eq_of_forall_mem_iff hs fun x => ?_⟩, fun t ht => ?_⟩
  · have := hl x
    simp only [NormalHyperplane.carrier, mem_ofPred_eq]
    rcases h.2.2.1 with hε | hε <;> rw [hε] at this <;> constructor <;> intro h' <;> linarith
  · have := hl x
    rw [hε] at this
    simp only [NormalHyperplane.upperHalfSpace, mem_ofPred_eq]
    constructor <;> intro h' <;> linarith
  · have := hl x
    rw [hε] at this
    simp only [NormalHyperplane.lowerHalfSpace, mem_ofPred_eq]
    constructor <;> intro h' <;> linarith
  · have := hl x
    rw [hε] at this
    simp only [NormalHyperplane.upperHalfSpace, NormalHyperplane.lowerHalfSpace,
      mem_ofPred_eq]
    constructor <;> intro h' <;> linarith
  · have := hl x
    rw [hε] at this
    simp only [NormalHyperplane.upperHalfSpace, NormalHyperplane.lowerHalfSpace,
      mem_ofPred_eq]
    constructor <;> intro h' <;> linarith
  · funext y
    have hy : r.toFun (t.toFun y) = y := ht.2 y
    calc Q'.reflect y = Q'.reflect (r.toFun (t.toFun y)) := by rw [hy]
      _ = r.toFun (Q.reflect (t.toFun y)) := reflect_apply_of_maps h _
theorem isBoundedObservable_of_mem_local {S : Set AmbientSpace} {F : GaugeField a → ℂ}
    (hF : F ∈ localRegionObservables a S) : IsBoundedObservable F := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.isBoundedObservable_of_mem_local <;> assumption
theorem isBoundedObservable_conjFun {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable (conjFun F) := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.isBoundedObservable_conjFun <;> assumption
theorem isBoundedObservable_mul {F F' : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hF' : IsBoundedObservable F') : IsBoundedObservable (F * F') := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.isBoundedObservable_mul <;> assumption
theorem allRules_holds (hA : InfiniteLattice.SymmetryActionOnObservables)
    (hR : MirrorReflections.MirrorReflectionsStatement) : AllRules := by
  intro a
  obtain ⟨-, -, hKeep, hComp, -, hLin, hGrow, hAlg, hLoc, hInv, hInvar⟩ := hA a
  obtain ⟨-, -, -, -, hIso, -⟩ := hR a
  have hSurj : ∀ r : LatticeSymmetry (a : ℝ), Function.Surjective r.toFun :=
    fun r => (hInv r).1.2
  refine ⟨?_, ?_, ?_, ?_, hLoc.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro S S' h
    exact ⟨(hGrow.2.1 S S' h).1, (hGrow.2.1 S S' h).2, (hAlg S).1, (hAlg S).2⟩
  · intro r
    refine ⟨fun F F' hF hF' => ((hLin r).2 F hF).1 F' hF', fun c F hF => ((hLin r).2 F hF).2.1 c,
      (hLin r).1, fun F hF => ((hLin r).2 F hF).2.2.2⟩
  · intro F _
    funext U
    refine congrArg F (Subtype.ext (funext fun b => congrArg U.1 ?_))
    exact InfiniteLattice.Link.ext (Subtype.ext rfl) (Subtype.ext rfl)
  · intro r
    refine ⟨(hInv r).2.1, fun t ht F hF => ?_⟩
    have := ((hInv r).2.2 t ht).1 F hF
    exact ⟨this.2.symm, this.1.symm⟩
  · intro v v' F hF
    have e : (shift v).comp (shift v') = shift (v + v') := by
      apply symmetry_ext
      funext x
      change x + (v' : AmbientSpace) + (v : AmbientSpace) =
        x + ((v + v' : LatticePoint (a : ℝ)) : AmbientSpace)
      rw [AddSubgroup.coe_add, add_assoc, add_comm (v' : AmbientSpace)]
    rw [← e, ((hComp _ _).2 F hF)]
  · intro ν hν r r' h h'
    exact ⟨(hInvar ν hν).1 r r' h h', fun t ht => ((hInv r).2.2 t ht).2 ν hν h⟩
  · intro Q
    obtain ⟨hi, hinv, hadd, -⟩ := (hIso Q).1
    refine ⟨reflectionLinear_isOrthogonal Q, hadd, fun x y => ?_, hinv,
      fun hQ => ⟨reflectSymmetry hQ, rfl⟩⟩
    have hv : ∀ w : Point, euclidNorm w = TorusMetric.euclidNormVec w := fun w => by
      rw [euclidNorm, TorusMetric.euclidNormVec, ← Real.sqrt_eq_rpow]
      exact congrArg Real.sqrt (Finset.sum_congr rfl fun _ _ => (pow_two _).symm)
    have := hi x y
    rw [hv, hv] at this
    exact this
  · intro r R v ε Q Q' _ _ h
    exact maps_carrier_halfSpaces_reflect (hSurj r) h
  · intro r R v ε Q Q' hQ hQ' h ν hν hνr t ht
    have hcar := maps_carrier_halfSpaces_reflect (hSurj r) h
    have hobs : ∀ (s : LatticeSymmetry (a : ℝ)) (F : GaugeField (a : ℝ) → ℂ),
        IsBoundedObservable F → IsBoundedObservable (s.actOn F) :=
      fun s F hF => ((hKeep s).1 F F hF hF).1
    have hRefl : reflectSymmetry hQ' = r.comp ((reflectSymmetry hQ).comp t) :=
      symmetry_ext (hcar.2.2.2 t ht)
    have hkey : ∀ F : GaugeField (a : ℝ) → ℂ, IsBoundedObservable F →
        conjFun ((reflectSymmetry hQ').actOn F) * F =
          r.actOn (conjFun ((reflectSymmetry hQ).actOn (t.actOn F)) * t.actOn F) := by
      intro F hF
      have hF' := hobs t F hF
      have hX := hobs (reflectSymmetry hQ) _ hF'
      have hback : r.actOn (t.actOn F) = F :=
        (((hInv r).2.2 t ht).1 F hF).2.symm
      have hL : (reflectSymmetry hQ').actOn F =
          r.actOn ((reflectSymmetry hQ).actOn (t.actOn F)) := by
        rw [hRefl, (hComp _ _).2 F hF, (hComp _ _).2 F hF]
      rw [((hKeep r).1 _ _ (isBoundedObservable_conjFun hX) hF').2.1,
        ((hKeep r).1 _ _ hX hX).2.2, hback, hL]
    have hside : ∀ {S S' : Set Point}, r.setImage S = S' → ∀ F : GaugeField (a : ℝ) → ℂ,
        F ∈ localRegionObservables (a : ℝ) S' → t.actOn F ∈ localRegionObservables (a : ℝ) S := by
      intro S S' hS F hF
      have hts : t.setImage S' = S := by
        rw [← hS]
        ext x
        constructor
        · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
          rw [ht.1 y]
          exact hy
        · intro hx
          exact ⟨r.toFun x, ⟨x, hx, rfl⟩, ht.1 x⟩
      rw [← hts, ← hLoc.1 t S']
      exact ⟨F, hF, rfl⟩
    have hcarry : ∀ F : GaugeField (a : ℝ) → ℂ,
        F ∈ localRegionObservables (a : ℝ) Q'.upperHalfSpace ∨
          F ∈ localRegionObservables (a : ℝ) Q'.lowerHalfSpace →
        (t.actOn F ∈ localRegionObservables (a : ℝ) Q.upperHalfSpace ∨
          t.actOn F ∈ localRegionObservables (a : ℝ) Q.lowerHalfSpace) ∧
        ∫ U, (conjFun ((reflectSymmetry hQ').actOn F) * F) U ∂ν =
          ∫ U, r.actOn
            (conjFun ((reflectSymmetry hQ).actOn (t.actOn F)) * t.actOn F) U ∂ν ∧
        ∫ U, r.actOn
            (conjFun ((reflectSymmetry hQ).actOn (t.actOn F)) * t.actOn F) U ∂ν =
          ∫ U, (conjFun ((reflectSymmetry hQ).actOn (t.actOn F)) * t.actOn F) U ∂ν := by
      intro F hF
      have hFo : IsBoundedObservable F :=
        hF.elim isBoundedObservable_of_mem_local isBoundedObservable_of_mem_local
      have hF' := hobs t F hFo
      refine ⟨?_, by rw [hkey F hFo], hνr _ (isBoundedObservable_mul
        (isBoundedObservable_conjFun (hobs (reflectSymmetry hQ) _ hF')) hF')⟩
      rcases h.2.2.1 with hε | hε
      · obtain ⟨e₁, e₂⟩ := hcar.2.1 hε
        exact hF.elim (fun h' => Or.inl (hside e₁ F h')) (fun h' => Or.inr (hside e₂ F h'))
      · obtain ⟨e₁, e₂⟩ := hcar.2.2.1 hε
        exact hF.elim (fun h' => Or.inr (hside e₂ F h')) (fun h' => Or.inl (hside e₁ F h'))
    refine ⟨hcarry, fun hp hm => ?_⟩
    have hpos : ∀ F : GaugeField (a : ℝ) → ℂ,
        F ∈ localRegionObservables (a : ℝ) Q'.upperHalfSpace ∨
          F ∈ localRegionObservables (a : ℝ) Q'.lowerHalfSpace →
        0 ≤ ∫ U, (conjFun ((reflectSymmetry hQ').actOn F) * F) U ∂ν := by
      intro F hF
      obtain ⟨hs, e₁, e₂⟩ := hcarry F hF
      rw [e₁, e₂]
      exact hs.elim (hp _) (hm _)
    exact ⟨fun F hF => hpos F (Or.inl hF), fun F hF => hpos F (Or.inr hF)⟩
end ObservableRules
end LatticeConventions
end YangMills.Construction
