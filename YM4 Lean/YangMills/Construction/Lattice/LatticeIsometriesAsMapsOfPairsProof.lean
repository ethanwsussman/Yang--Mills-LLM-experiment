import YangMills.Construction.InfiniteLattice.BondsPlaquettesCircuitsAndConfigurationsOfTheLatticeOfACutoffProof
import YangMills.Construction.PassageToTheLimit.TransportedLatticeFunctionalsAreBoundedFormsProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegions
import YangMills.Construction.Lattice.LatticeIsometriesAsMapsOfPairs
import YangMills.Construction.Lattice.TorusItsLatticeAndItsLatticeIsometries
import YangMills.Construction.SystemOfAdmissibleConstants.CumulantConditionsFromTheInequalityProof
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set Matrix
open PeriodicLattice PeriodicLattice.PlaquetteCircuits TorusMetric
open InfiniteLattice (AmbientSpace hypercubicGroup frameLinearMap latticeSubgroup torusAffineMap
  InducesTorusMap)
namespace AffineTorusIsometries
variable {L m : ℕ} {j : ℤ}
theorem unit_cast_eq_one_or_neg_one (u : ℤˣ) : ((u : ℤ) : ℝ) = 1 ∨ ((u : ℤ) : ℝ) = -1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp
theorem torusProj_add' (S : ℝ) (x y : AmbientSpace) :
    torusProj S (x + y) = torusProj S x + torusProj S y := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
theorem torusProj_zero' (S : ℝ) : torusProj S (0 : AmbientSpace) = 0 := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.torusProj_zero <;> assumption
theorem torusProj_neg' (S : ℝ) (x : AmbientSpace) : torusProj S (-x) = -torusProj S x := by
  funext μ
  simp [torusProj]
theorem torusProj_sub' (S : ℝ) (x y : AmbientSpace) :
    torusProj S (x - y) = torusProj S x - torusProj S y := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
theorem torusSide_ne_zero' (hL : 0 < L) : torusSide L m ≠ 0 := by
  have : (0 : ℝ) < L := by exact_mod_cast hL
  unfold torusSide
  positivity
theorem meshSize_pos' (hL : 0 < L) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p16883 <;> assumption
theorem affine_pair_unique {S : ℝ} (hS : S ≠ 0) {w w' : AmbientSpace →ₗ[ℝ] AmbientSpace}
    {v v' : AmbientSpace}
    (h : ∀ x, torusProj S (w x + v) = torusProj S (w' x + v')) :
    w = w' ∧ ∃ k, v' = v + TestFunctions.latticeTranslate S k := by
  have h0 := h 0
  simp only [map_zero, zero_add] at h0
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq h0.symm
  refine ⟨?_, k, hk⟩
  have hd : ∀ x, torusProj S (w x - w' x) = 0 := by
    intro x
    have hx := h x
    rw [torusProj_add', torusProj_add', ← h0] at hx
    rw [torusProj_sub', add_right_cancel hx, sub_self]
  apply LinearMap.ext
  intro x
  funext μ
  by_contra hne
  have hc0 : w x μ - w' x μ ≠ 0 := sub_ne_zero.mpr hne
  have hz := congrFun (hd ((S / (2 * (w x μ - w' x μ))) • x)) μ
  have hv : (w ((S / (2 * (w x μ - w' x μ))) • x) - w' ((S / (2 * (w x μ - w' x μ))) • x)) μ
      = S / 2 := by
    simp only [map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub]
    field_simp
  have h2 : ((S / 2 : ℝ) : AddCircle S) = 0 := by
    rw [← hv]
    exact hz
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff S).1 h2
  rw [zsmul_eq_mul] at hn
  have h3 : (2 * (n : ℝ)) * S = 1 * S := by linarith
  have h4 : (2 * (n : ℝ)) = 1 := mul_right_cancel₀ hS h3
  have h5 : 2 * n = 1 := by exact_mod_cast h4
  omega
theorem exists_unit_of_sum_sq_eq_one (n : Fin 4 → ℤ) (hn : ∑ κ, n κ ^ 2 = 1) :
    ∃ κ, (n κ = 1 ∨ n κ = -1) ∧ ∀ κ', κ' ≠ κ → n κ' = 0 := by
  have hex : ∃ κ, n κ ≠ 0 := by
    by_contra hno
    have h0 : ∀ κ, n κ = 0 := fun κ => by_contra fun h => hno ⟨κ, h⟩
    simp [h0] at hn
  obtain ⟨κ, hκ⟩ := hex
  have hpos : 1 ≤ n κ ^ 2 := by
    have : 0 < n κ ^ 2 := by positivity
    omega
  have hrest : ∑ κ' ∈ Finset.univ.erase κ, n κ' ^ 2 = 1 - n κ ^ 2 := by
    rw [← hn, ← Finset.add_sum_erase _ _ (Finset.mem_univ κ)]
    ring
  have hnn : 0 ≤ ∑ κ' ∈ Finset.univ.erase κ, n κ' ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hone : n κ ^ 2 = 1 := by omega
  have hzero : ∑ κ' ∈ Finset.univ.erase κ, n κ' ^ 2 = 0 := by omega
  refine ⟨κ, ?_, fun κ' hne => ?_⟩
  · rw [sq] at hone
    exact mul_self_eq_one_iff.mp hone
  · have h := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity).mp hzero κ'
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
    exact pow_eq_zero_iff two_ne_zero |>.mp h
theorem exists_signedFrame_of_orthogonal {R : Matrix (Fin 4) (Fin 4) ℝ}
    (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ) {S : ℝ} (hS : S ≠ 0)
    (hlat : (fun x : AmbientSpace => R *ᵥ x) '' (latticeSubgroup S : Set AmbientSpace) =
      latticeSubgroup S) :
    ∃ f : SignedFrame, ∀ x, R *ᵥ x = f.actOnVector x := by
  classical
  have hint : ∀ μ ν, ∃ n : ℤ, R μ ν = n := by
    intro μ ν
    have hmem : R *ᵥ (Pi.single ν S : AmbientSpace) ∈ (latticeSubgroup S : Set AmbientSpace) := by
      rw [← hlat]
      refine ⟨Pi.single ν S, ⟨Pi.single ν 1, fun κ => ?_⟩, rfl⟩
      by_cases h : κ = ν
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    obtain ⟨N, hN⟩ := hmem
    have h : (R *ᵥ (Pi.single ν S : AmbientSpace)) μ = R μ ν * S := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    exact ⟨N μ, mul_right_cancel₀ hS (h.symm.trans (hN μ))⟩
  choose M hM using hint
  have hRR : R * Rᵀ = 1 := by
    have := (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).1 hR
    simpa [Matrix.star_eq_conjTranspose] using this
  have hij : ∀ μ μ', ∑ ν, R μ ν * R μ' ν = if μ = μ' then 1 else 0 := by
    intro μ μ'
    have := congrFun (congrFun hRR μ) μ'
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hrow : ∀ μ, ∃ κ, (M μ κ = 1 ∨ M μ κ = -1) ∧ ∀ κ', κ' ≠ κ → M μ κ' = 0 := by
    intro μ
    apply exists_unit_of_sum_sq_eq_one
    have h := hij μ μ
    simp only [if_true, hM] at h
    have h2 : ((∑ ν, M μ ν ^ 2 : ℤ) : ℝ) = 1 := by
      push_cast
      rw [← h]
      exact Finset.sum_congr rfl fun ν _ => by ring
    exact_mod_cast h2
  choose π hπ hz using hrow
  have hinj : Function.Injective π := by
    intro μ μ' he
    by_contra hne
    have h := hij μ μ'
    rw [if_neg hne, Finset.sum_eq_single (π μ)] at h
    · have h1 : M μ (π μ) ≠ 0 := by rcases hπ μ with h | h <;> simp [h]
      have h2 : M μ' (π μ) ≠ 0 := by rw [he]; rcases hπ μ' with h | h <;> simp [h]
      rw [hM, hM] at h
      have h3 : M μ (π μ) * M μ' (π μ) = 0 := by exact_mod_cast h
      rcases mul_eq_zero.mp h3 with h | h
      · exact h1 h
      · exact h2 h
    · intro κ _ hκ
      rw [hM μ κ, hz μ κ hκ]
      simp
    · simp
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective π (Finite.injective_iff_bijective.1 hinj)
  let u : Fin 4 → ℤˣ := fun μ => if M μ (π μ) = 1 then 1 else -1
  refine ⟨(e, u), fun x => ?_⟩
  funext μ
  have hu : ((u μ : ℤ) : ℝ) = R μ (π μ) := by
    rw [hM]
    rcases hπ μ with h | h
    · simp [u, h]
    · simp [u, h]
  have hsum : (R *ᵥ x) μ = R μ (π μ) * x (π μ) := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (π μ)]
    · intro κ _ hκ
      rw [hM μ κ, hz μ κ hκ]
      simp
    · simp
  rw [hsum, ← hu]
  rfl
theorem exists_signedFrame_of_isFlatIsometry (h : Tower.OrthogonalMotions.Classification)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (r : FourTorus L m ≃ FourTorus L m) (hr : IsFlatIsometry r) :
    ∃ (f : SignedFrame) (v : AmbientSpace), IsInducedByAffine r f v := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  obtain ⟨R, hR, hlat, v, hv⟩ := (h.2.2.2 L m hL hm).2.2.1 r hr
  obtain ⟨f, hf⟩ := exists_signedFrame_of_orthogonal hR (torusSide_ne_zero' hL0) hlat
  refine ⟨f, v, fun x => ?_⟩
  have := hv x
  rw [hf] at this
  exact this
def axisCount (p : Plaquette L m j) (κ : Fin 4) : ℤ :=
  (if κ = p.firstAxis then 1 else 0) + (if κ = p.secondAxis then 1 else 0)
theorem barycenter_apply_eq (p : Plaquette L m j) (n : Fin 4 → ℤ)
    (hn : ∀ μ, (p.origin : FourTorus L m) μ =
      (((n μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)))
    (κ : Fin 4) :
    p.barycenter κ = (((n κ : ℝ) * meshSize L j +
      (axisCount p κ : ℝ) * (meshSize L j / 2) : ℝ) : AddCircle (torusSide L m)) := by
  unfold Plaquette.barycenter axisCount pointOnAxis
  simp only [Pi.add_apply, hn, Pi.single_apply]
  split_ifs <;> simp only [add_zero, ← AddCircle.coe_add] <;> congr 1 <;> push_cast <;> ring
theorem axes_eq_of_axisCount {μ ν μ' ν' : Fin 4} (h : μ < ν) (h' : μ' < ν')
    (hc : ∀ κ : Fin 4, ((if κ = μ then 1 else 0) + (if κ = ν then 1 else 0) : ℤ) =
      (if κ = μ' then 1 else 0) + (if κ = ν' then 1 else 0)) : μ = μ' ∧ ν = ν' := by
  revert μ ν μ' ν'
  decide
theorem barycenter_injective_of_divides (hL : 0 < L)
    (hN : ∃ N : ℤ, torusSide L m = (N : ℝ) * meshSize L j) :
    Function.Injective (Plaquette.barycenter : Plaquette L m j → FourTorus L m) := by
  intro p p' hpp
  obtain ⟨N, hN⟩ := hN
  have ha : meshSize L j ≠ 0 := (meshSize_pos' hL).ne'
  obtain ⟨n, hn⟩ := p.origin.2
  obtain ⟨n', hn'⟩ := p'.origin.2
  have hcount : ∀ κ, axisCount p κ = axisCount p' κ := by
    intro κ
    have h := congrFun hpp κ
    rw [barycenter_apply_eq p n hn, barycenter_apply_eq p' n' hn'] at h
    have h1 : (((((n κ : ℝ) * meshSize L j + (axisCount p κ : ℝ) * (meshSize L j / 2)) -
        ((n' κ : ℝ) * meshSize L j + (axisCount p' κ : ℝ) * (meshSize L j / 2)) : ℝ)) :
        AddCircle (torusSide L m)) = 0 := by
      rw [AddCircle.coe_sub, h, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).1 h1
    rw [zsmul_eq_mul, hN] at hk
    have h2 : (2 * (k : ℝ) * (N : ℝ)) * meshSize L j =
        (2 * (n κ : ℝ) + axisCount p κ - 2 * (n' κ : ℝ) - axisCount p' κ) *
          meshSize L j := by
      linarith
    have h3 := mul_right_cancel₀ ha h2
    have h4 : 2 * k * N = 2 * n κ + axisCount p κ - 2 * n' κ - axisCount p' κ := by
      exact_mod_cast h3
    have hb : ∀ q : Plaquette L m j, 0 ≤ axisCount q κ ∧ axisCount q κ ≤ 1 := by
      intro q
      have := q.firstAxis_lt_secondAxis
      unfold axisCount
      split_ifs <;> omega
    have hb1 := hb p
    have hb2 := hb p'
    have h5 : 2 * (k * N - n κ + n' κ) = axisCount p κ - axisCount p' κ := by
      linarith
    omega
  obtain ⟨h1, h2⟩ :=
    axes_eq_of_axisCount p.firstAxis_lt_secondAxis p'.firstAxis_lt_secondAxis hcount
  have hbase : p.origin = p'.origin := by
    apply Subtype.ext
    unfold Plaquette.barycenter at hpp
    rw [h1, h2] at hpp
    exact add_right_cancel (add_right_cancel hpp)
  exact Plaquette.ext hbase h1 h2
theorem signedFrame_act_add (f : SignedFrame) (x y : AmbientSpace) :
    f.actOnVector (x + y) = f.actOnVector x + f.actOnVector y :=
  (frameLinearMap f).map_add x y
theorem signedFrame_act_smul (f : SignedFrame) (c : ℝ) (x : AmbientSpace) :
    f.actOnVector (c • x) = c • f.actOnVector x :=
  (frameLinearMap f).map_smul c x
theorem signedFrame_act_neg (f : SignedFrame) (x : AmbientSpace) :
    f.actOnVector (-x) = -f.actOnVector x :=
  (frameLinearMap f).map_neg x
theorem signedFrame_act_single (f : SignedFrame) (κ : Fin 4) (t : ℝ) :
    f.actOnVector (Pi.single κ t : AmbientSpace) =
      ((f.2 (f.1⁻¹ κ) : ℤ) : ℝ) • (Pi.single (f.1⁻¹ κ) t : AmbientSpace) := by
  funext μ
  by_cases h : μ = f.1⁻¹ κ
  · subst h
    simp [SignedFrame.actOnVector]
  · have h' : f.1 μ ≠ κ := fun hc => h (by simp [← hc])
    have h'' : μ ≠ f.1.symm κ := h
    simp [SignedFrame.actOnVector, Pi.single_eq_of_ne h'', Pi.single_eq_of_ne h']
theorem isAlongAxis_signedFrame_act (f : SignedFrame) {e : AmbientSpace} {κ : Fin 4}
    (he : IsAlongAxis e L j κ) : IsAlongAxis (f.actOnVector e) L j (f.1⁻¹ κ) := by
  have hs : f.actOnVector (meshVector L j κ) =
      ((f.2 (f.1⁻¹ κ) : ℤ) : ℝ) • meshVector L j (f.1⁻¹ κ) := signedFrame_act_single f κ _
  rcases he with rfl | rfl
  · rw [hs]
    rcases unit_cast_eq_one_or_neg_one (f.2 (f.1⁻¹ κ)) with h | h
    · left
      rw [h, one_smul]
    · right
      rw [h, neg_smul, one_smul]
  · rw [signedFrame_act_neg, hs]
    rcases unit_cast_eq_one_or_neg_one (f.2 (f.1⁻¹ κ)) with h | h
    · right
      rw [h, one_smul]
    · left
      rw [h, neg_smul, one_smul, neg_neg]
theorem signedFrame_act_mem_meshVectors (f : SignedFrame) {e : AmbientSpace}
    (he : e ∈ PlaquetteCircuits.meshVectors L j) :
    f.actOnVector e ∈ PlaquetteCircuits.meshVectors L j := by
  obtain ⟨κ, h⟩ := he
  exact ⟨_, isAlongAxis_signedFrame_act f h⟩
section Induced
variable {r : FourTorus L m ≃ FourTorus L m} {f : SignedFrame} {v : AmbientSpace}
theorem induced_add_torusProj (hf : IsInducedByAffine r f v) (y : FourTorus L m)
    (ζ : AmbientSpace) :
    r (y + torusProj (torusSide L m) ζ) = r y + torusProj (torusSide L m) (f.actOnVector ζ) := by
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ y
  have h1 : r (torusProj (torusSide L m) x) = torusProj (torusSide L m) (f.actOnVector x + v) :=
    hf x
  have h2 : r (torusProj (torusSide L m) (x + ζ)) =
      torusProj (torusSide L m) (f.actOnVector (x + ζ) + v) := hf _
  rw [← torusProj_add', h2, h1, ← torusProj_add', signedFrame_act_add]
  congr 1
  abel
theorem frameLinearMap_linearComponent (hL : 0 < L) (hf : IsInducedByAffine r f v) :
    frameLinearMap (linearComponent r) = frameLinearMap f := by
  have h : ∃ g : SignedFrame, HasLinearPart r g := ⟨f, v, hf⟩
  unfold linearComponent
  rw [dif_pos h]
  obtain ⟨v', hv'⟩ := h.choose_spec
  exact (affine_pair_unique (torusSide_ne_zero' hL) (w := frameLinearMap h.choose) (v := v')
    (w' := frameLinearMap f) (v' := v) fun x => (hv' x).symm.trans (hf x)).1
end Induced
theorem bond_ext_of_source_target {b b' : Bond L m j}
    (ht : (b.source : FourTorus L m) = b'.source)
    (hh : (b.target : FourTorus L m) = b'.target) : b = b' :=
  Bond.ext (Subtype.ext ht) (Subtype.ext hh)
section Carried
variable {r : FourTorus L m ≃ FourTorus L m} {f : SignedFrame} {v : AmbientSpace}
theorem mapsCells_site_mem (hc : MapsCellsAndCubes r j) (y : Site L m j) :
    r y ∈ sublattice L m j := by
  have h : r y ∈ r '' (sublattice L m j : Set (FourTorus L m)) := ⟨y, y.2, rfl⟩
  rw [hc.1] at h
  exact h
theorem bondImage_source' (hc : MapsCellsAndCubes r j) (b : Bond L m j) :
    ((bondImage r b).source : FourTorus L m) = r b.source := (hc.2.2.2.1 b).1
theorem bondImage_target' (hc : MapsCellsAndCubes r j) (b : Bond L m j) :
    ((bondImage r b).target : FourTorus L m) = r b.target := (hc.2.2.2.1 b).2
theorem bondImage_bondFrom (hf : IsInducedByAffine r f v) (hc : MapsCellsAndCubes r j)
    {y y' : Site L m j} {e e' : PlaquetteCircuits.meshVectors L j} (hy : (y' : FourTorus L m) = r y)
    (he : e'.1 = f.actOnVector e.1) : bondImage r (bondFrom y e) = bondFrom y' e' := by
  apply bond_ext_of_source_target
  · rw [bondImage_source' hc]
    exact hy.symm
  · rw [bondImage_target' hc]
    change r ((y : FourTorus L m) + torusProj (torusSide L m) e.1) =
      (y' : FourTorus L m) + torusProj (torusSide L m) e'.1
    rw [induced_add_torusProj hf, hy, he]
theorem bondFromSegment_image (hf : IsInducedByAffine r f v)
    {y y' : Site L m j} {e e' : PlaquetteCircuits.meshVectors L j} (hy : (y' : FourTorus L m) = r y)
    (he : e'.1 = f.actOnVector e.1) : bondFromSegment y' e' = r '' bondFromSegment y e := by
  have key : ∀ t : ℝ, r (addVector (y : FourTorus L m) (t • e.1)) =
      addVector (y' : FourTorus L m) (t • e'.1) := by
    intro t
    change r ((y : FourTorus L m) + torusProj (torusSide L m) (t • e.1)) =
      (y' : FourTorus L m) + torusProj (torusSide L m) (t • e'.1)
    rw [induced_add_torusProj hf, hy, he, signedFrame_act_smul]
  ext q
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, ⟨t, ht, rfl⟩, key t⟩
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, key t⟩
end Carried
theorem meshVector_eq_smul_coordVec (μ : Fin 4) :
    meshVector L j μ = meshSize L j • coordVec μ := by apply _root_.YangMills.Construction.RefinedLatticeSymmetries.meshVector_eq_smul <;> assumption
theorem torusProj_smul_coordVec (t : ℝ) (μ : Fin 4) :
    torusProj (torusSide L m) (t • coordVec μ) = pointOnAxis L m μ t := by
  funext σ
  by_cases h : σ = μ
  · subst h
    simp [torusProj, coordVec, pointOnAxis]
  · simp [torusProj, coordVec, pointOnAxis, Pi.single_eq_of_ne h]
theorem torusProj_smul_meshVector (t : ℝ) (μ : Fin 4) :
    torusProj (torusSide L m) (t • meshVector L j μ) = pointOnAxis L m μ (t * meshSize L j) := by
  rw [meshVector_eq_smul_coordVec, smul_smul, torusProj_smul_coordVec]
theorem faceSpannedBy_eq_face (hL : 0 < L) (p : Plaquette L m j) :
    faceSpannedBy p.origin p.firstAxis p.secondAxis = p.face := by
  have ha := meshSize_pos' (L := L) (j := j) hL
  have key : ∀ s t : ℝ, addVector (p.origin : FourTorus L m)
      (s • meshVector L j p.firstAxis + t • meshVector L j p.secondAxis) =
      (p.origin : FourTorus L m) + pointOnAxis L m p.firstAxis (s * meshSize L j) +
        pointOnAxis L m p.secondAxis (t * meshSize L j) := by
    intro s t
    change (p.origin : FourTorus L m) + torusProj (torusSide L m) _ = _
    rw [torusProj_add', torusProj_smul_meshVector, torusProj_smul_meshVector, add_assoc]
  ext q
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    refine ⟨s * meshSize L j, ⟨by have := hs.1; positivity, ?_⟩, t * meshSize L j,
      ⟨by have := ht.1; positivity, ?_⟩, key s t⟩
    · nlinarith [hs.2]
    · nlinarith [ht.2]
  · rintro ⟨s, hs, t, ht, rfl⟩
    refine ⟨s / meshSize L j, ⟨div_nonneg hs.1 ha.le, (div_le_one ha).2 hs.2⟩, t / meshSize L j,
      ⟨div_nonneg ht.1 ha.le, (div_le_one ha).2 ht.2⟩, ?_⟩
    rw [key, div_mul_cancel₀ _ ha.ne', div_mul_cancel₀ _ ha.ne']
theorem plaquetteSpannedBy_axes (p : Plaquette L m j) :
    plaquetteSpannedBy p.origin p.firstAxis p.secondAxis p.firstAxis_lt_secondAxis.ne = p := by
  unfold plaquetteSpannedBy
  rw [dif_pos p.firstAxis_lt_secondAxis]
theorem isFrame_plaquetteSpannedBy_iff {x : Site L m j} {μ ν : Fin 4} {h : μ ≠ ν}
    {e e' : PlaquetteCircuits.meshVectors L j} :
    IsFrame (plaquetteSpannedBy x μ ν h) e e' ↔
      (IsAlongAxis e.1 L j μ ∧ IsAlongAxis e'.1 L j ν) ∨
        (IsAlongAxis e.1 L j ν ∧ IsAlongAxis e'.1 L j μ) := by
  unfold IsFrame plaquetteSpannedBy
  split_ifs with hl
  · exact Iff.rfl
  · exact or_comm
theorem axis_and_scale_eq {u t : ℝ} {α β : Fin 4} (hu : u ≠ 0)
    (h : u • coordVec α = t • (Pi.single β 1 : AmbientSpace)) : α = β ∧ u = t := by
  have h1 := congrFun h α
  by_cases hab : α = β
  · subst hab
    refine ⟨rfl, ?_⟩
    simpa [coordVec] using h1
  · exact absurd (by simpa [coordVec, Pi.single_eq_of_ne hab] using h1) hu
section BasePoint
variable {r : FourTorus L m ≃ FourTorus L m} {f : SignedFrame} {v : AmbientSpace}
theorem plaquetteImage_plaquetteSpannedBy
    (hinj : Function.Injective (Plaquette.barycenter : Plaquette L m j → FourTorus L m))
    (hf : IsInducedByAffine r f v) (hc : MapsCellsAndCubes r j)
    (x : Site L m j) {μ ν μ' ν' : Fin 4} (h : μ ≠ ν) {u u' : ℝ} (hu : u = 1 ∨ u = -1)
    (hu' : u' = 1 ∨ u' = -1)
    (h1 : f.actOnVector (coordVec μ) = u • coordVec μ')
    (h2 : f.actOnVector (coordVec ν) = u' • coordVec ν') :
    ∃ h' : μ' ≠ ν', ∃ x' : Site L m j,
      plaquetteImage r (plaquetteSpannedBy x μ ν h) = plaquetteSpannedBy x' μ' ν' h' ∧
      (x' : FourTorus L m) =
        r (plaquetteSpannedBy x μ ν h).barycenter +
          torusProj (torusSide L m) (-((meshSize L j / 2) • coordVec μ')) +
          torusProj (torusSide L m) (-((meshSize L j / 2) • coordVec ν')) ∧
      (x' : FourTorus L m) =
        r x + torusProj (torusSide L m) (((u - 1) / 2 * meshSize L j) • coordVec μ') +
          torusProj (torusSide L m) (((u' - 1) / 2 * meshSize L j) • coordVec ν') := by
  have hu0 : u ≠ 0 := by rcases hu with rfl | rfl <;> norm_num
  have hu0' : u' ≠ 0 := by rcases hu' with rfl | rfl <;> norm_num
  have e1 : μ' = f.1⁻¹ μ := by
    have h3 := signedFrame_act_single f μ 1
    exact (axis_and_scale_eq hu0 (h1.symm.trans h3)).1
  have e2 : ν' = f.1⁻¹ ν := by
    have h3 := signedFrame_act_single f ν 1
    exact (axis_and_scale_eq hu0' (h2.symm.trans h3)).1
  have h' : μ' ≠ ν' := by
    rw [e1, e2]
    exact fun hc => h (f.1⁻¹.injective hc)
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℤ, (u - 1) / 2 = n := by
    rcases hu with rfl | rfl
    · exact ⟨0, by norm_num⟩
    · exact ⟨-1, by norm_num⟩
  obtain ⟨n₂, hn₂⟩ : ∃ n : ℤ, (u' - 1) / 2 = n := by
    rcases hu' with rfl | rfl
    · exact ⟨0, by norm_num⟩
    · exact ⟨-1, by norm_num⟩
  have hstep : ∀ (n : ℤ) (ρ : Fin 4), ((n • unitStep L m j ρ : Site L m j) : FourTorus L m) =
      torusProj (torusSide L m) (((n : ℝ) * meshSize L j) • coordVec ρ) := by
    intro n ρ
    rw [torusProj_smul_coordVec]
    funext σ
    by_cases hσ : σ = ρ
    · subst hσ
      simp [unitStep, pointOnAxis]
    · simp [unitStep, pointOnAxis, Pi.single_eq_of_ne hσ]
  let y : Site L m j := ⟨r x, mapsCells_site_mem hc x⟩
  let x' : Site L m j := y + n₁ • unitStep L m j μ' + n₂ • unitStep L m j ν'
  have hx' : (x' : FourTorus L m) =
      r x + torusProj (torusSide L m) (((u - 1) / 2 * meshSize L j) • coordVec μ') +
        torusProj (torusSide L m) (((u' - 1) / 2 * meshSize L j) • coordVec ν') := by
    rw [hn₁, hn₂, ← hstep, ← hstep]
    rfl
  have hhalf : ∀ ρ : Fin 4, (1 / 2 : ℝ) • meshVector L j ρ =
      (meshSize L j / 2) • coordVec ρ := by
    intro ρ
    rw [meshVector_eq_smul_coordVec, smul_smul]
    congr 1
    ring
  have hb : r (plaquetteSpannedBy x μ ν h).barycenter =
      r x + torusProj (torusSide L m) ((u * (meshSize L j / 2)) • coordVec μ') +
        torusProj (torusSide L m) ((u' * (meshSize L j / 2)) • coordVec ν') := by
    rw [barycenter_plaquetteSpannedBy, hhalf, hhalf]
    change r ((x : FourTorus L m) + torusProj (torusSide L m) _ + torusProj (torusSide L m) _) = _
    rw [induced_add_torusProj hf, induced_add_torusProj hf, signedFrame_act_smul,
      signedFrame_act_smul, h1, h2, smul_smul, smul_smul,
      mul_comm (meshSize L j / 2), mul_comm (meshSize L j / 2)]
  have k1 : ∀ c ρ, torusProj (torusSide L m) ((c * meshSize L j) • coordVec ρ) +
      torusProj (torusSide L m) ((meshSize L j / 2) • coordVec ρ) =
      torusProj (torusSide L m) (((c + 1 / 2) * meshSize L j) • coordVec ρ) := by
    intro c ρ
    rw [← torusProj_add', ← add_smul]
    congr 2
    ring
  have hb' : (plaquetteSpannedBy x' μ' ν' h').barycenter =
      r (plaquetteSpannedBy x μ ν h).barycenter := by
    rw [hb, barycenter_plaquetteSpannedBy, hhalf, hhalf]
    change (x' : FourTorus L m) + torusProj (torusSide L m) _ + torusProj (torusSide L m) _ = _
    rw [hx']
    have a1 := k1 ((u - 1) / 2) μ'
    have a2 := k1 ((u' - 1) / 2) ν'
    have b1 : ((u - 1) / 2 + 1 / 2) * meshSize L j = u * (meshSize L j / 2) := by ring
    have b2 : ((u' - 1) / 2 + 1 / 2) * meshSize L j = u' * (meshSize L j / 2) := by ring
    rw [b1] at a1
    rw [b2] at a2
    rw [← a1, ← a2]
    abel
  refine ⟨h', x', ?_, ?_, hx'⟩
  · apply hinj
    rw [(hc.2.2.2.2.2.2.2.1 _), hb']
  · rw [← hb', barycenter_plaquetteSpannedBy, hhalf, hhalf, torusProj_neg', torusProj_neg']
    change (x' : FourTorus L m) =
      (x' : FourTorus L m) + torusProj (torusSide L m) _ + torusProj (torusSide L m) _ + _ + _
    abel
end BasePoint
section Circuits
variable {r : FourTorus L m ≃ FourTorus L m} {f : SignedFrame} {v : AmbientSpace}
theorem bondImage_circuitFrom (hf : IsInducedByAffine r f v) (hc : MapsCellsAndCubes r j)
    {c c₁ : Site L m j} {e e₁ g g₁ : PlaquetteCircuits.meshVectors L j}
    (hc₁ : (c₁ : FourTorus L m) = r c)
    (he : g.1 = f.actOnVector e.1) (he₁ : g₁.1 = f.actOnVector e₁.1) :
    (fun i => bondImage r (circuitFrom c e e₁ i)) = circuitFrom c₁ g g₁ := by
  have ha : ((c₁ + meshVectorSite g : Site L m j) : FourTorus L m) =
      r ((c + meshVectorSite e : Site L m j)) := by
    change (c₁ : FourTorus L m) + torusProj (torusSide L m) g.1 =
      r ((c : FourTorus L m) + torusProj (torusSide L m) e.1)
    rw [induced_add_torusProj hf, hc₁, he]
  have hb : ((c₁ + meshVectorSite g₁ : Site L m j) : FourTorus L m) =
      r ((c + meshVectorSite e₁ : Site L m j)) := by
    change (c₁ : FourTorus L m) + torusProj (torusSide L m) g₁.1 =
      r ((c : FourTorus L m) + torusProj (torusSide L m) e₁.1)
    rw [induced_add_torusProj hf, hc₁, he₁]
  have hd : ((c₁ + meshVectorSite g + meshVectorSite g₁ : Site L m j) : FourTorus L m) =
      r ((c + meshVectorSite e + meshVectorSite e₁ : Site L m j)) := by
    change ((c₁ + meshVectorSite g : Site L m j) : FourTorus L m) +
        torusProj (torusSide L m) g₁.1 =
      r (((c + meshVectorSite e : Site L m j) : FourTorus L m) + torusProj (torusSide L m) e₁.1)
    rw [induced_add_torusProj hf, ha, he₁]
  have hn : (-g).1 = f.actOnVector (-e).1 := by
    change -g.1 = f.actOnVector (-e.1)
    rw [signedFrame_act_neg, he]
  have hn₁ : (-g₁).1 = f.actOnVector (-e₁).1 := by
    change -g₁.1 = f.actOnVector (-e₁.1)
    rw [signedFrame_act_neg, he₁]
  funext i
  fin_cases i
  · exact bondImage_bondFrom hf hc hc₁ he
  · exact bondImage_bondFrom hf hc ha he₁
  · exact bondImage_bondFrom hf hc hd hn
  · exact bondImage_bondFrom hf hc hb hn₁
theorem frameVertex_image (hf : IsInducedByAffine r f v) {p q : Plaquette L m j}
    (hq : q.barycenter = r p.barycenter)
    {e e₁ g g₁ : PlaquetteCircuits.meshVectors L j} (he : g.1 = f.actOnVector e.1)
    (he₁ : g₁.1 = f.actOnVector e₁.1) :
    frameVertex q g g₁ = r (frameVertex p e e₁) := by
  unfold frameVertex
  change q.barycenter + torusProj (torusSide L m) _ + torusProj (torusSide L m) _ =
    r (p.barycenter + torusProj (torusSide L m) _ + torusProj (torusSide L m) _)
  rw [induced_add_torusProj hf, induced_add_torusProj hf, hq, signedFrame_act_neg,
    signedFrame_act_neg, signedFrame_act_smul, signedFrame_act_smul, he, he₁]
end Circuits
theorem torusEquiv_isInducedByAffine (f : SignedFrame) :
    IsInducedByAffine (SignedFrame.torusEquiv L m f) f 0 := by
  intro x
  funext μ
  rcases Int.units_eq_one_or (f.2 μ) with hs | hs <;>
    simp [toFourTorus, SignedFrame.torusEquiv, signedCoordinatePerm, SignedFrame.actOnVector, hs]
theorem eq_torusAffineMap {w : AmbientSpace →ₗ[ℝ] AmbientSpace} (hw : w ∈ hypercubicGroup)
    {v : AmbientSpace} {g : FourTorus L m → FourTorus L m}
    (h : ∀ x, g (torusProj (torusSide L m) x) = torusProj (torusSide L m) (w x + v)) :
    g = torusAffineMap L m w v := by
  funext y
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ y
  rw [h, InfiniteLattice.torusAffineMap_torusProj L m hw]
theorem frameLinearMap_one_apply (x : AmbientSpace) : frameLinearMap (1 : SignedFrame) x = x := by
  funext μ
  simp [frameLinearMap, SignedFrame.actOnVector]
structure IsometryFacts (s : Conventions.StandingParameters) : Prop where
  L_pos : 0 < s.L
  isometries_eq : s.cutoffLatticeIsometries = latticeIsometries s.L s.m ((s.K : ℕ) : ℤ)
  affine : ∀ r ∈ s.cutoffLatticeIsometries, ∃ (f : SignedFrame) (v : AmbientSpace),
    v ∈ latticeSubgroup s.cutoffMesh ∧ IsInducedByAffine r f v
  mapsCells : ∀ r ∈ s.cutoffLatticeIsometries, MapsCellsAndCubes r ((s.K : ℕ) : ℤ)
  trans_mem : ∀ r ∈ s.cutoffLatticeIsometries, ∀ r' ∈ s.cutoffLatticeIsometries,
    r'.trans r ∈ s.cutoffLatticeIsometries
  symm_mem : ∀ r ∈ s.cutoffLatticeIsometries, r.symm ∈ s.cutoffLatticeIsometries
  refl_mem : Equiv.refl _ ∈ s.cutoffLatticeIsometries
  barycenter_injective :
    Function.Injective (Plaquette.barycenter : s.LatticePlaquette → s.Torus)
  lift : ∀ r : s.Torus ≃ s.Torus, IsFlatIsometry r →
    ∃ (f : SignedFrame) (v : AmbientSpace), IsInducedByAffine r f v
  torusProj_mem_iff : ∀ x : AmbientSpace, torusProj (torusSide s.L s.m) x ∈ s.cutoffLattice ↔
    x ∈ latticeSubgroup s.cutoffMesh
theorem isometryFacts (h₁ : LatticeIsometryGroupActionStatement)
    (h₂ : Tower.OrthogonalMotions.Classification)
    (h₃ : Conventions.StandingParameters.TorusLatticeAndIsometryFacts)
    (s : Conventions.StandingParameters) :
    IsometryFacts s := by
  have hL := s.isAdmissible
  have hL0 : 0 < s.L := by
    have := hL.2
    omega
  have hm : 0 < (s.m : ℕ) := s.m.pos
  have hi : -((s.m : ℕ) : ℤ) ≤ ((s.K : ℕ) : ℤ) := by omega
  obtain ⟨-, hdist, -, -, hcar⟩ := h₁ s.L s.m ((s.K : ℕ) : ℤ) hL hm hi
  obtain ⟨hside, -, -, hgroup⟩ := h₃ s
  have hlift : ∀ r : s.Torus ≃ s.Torus, IsFlatIsometry r →
      ∃ (f : SignedFrame) (v : AmbientSpace), IsInducedByAffine r f v :=
    fun r hr => exists_signedFrame_of_isFlatIsometry h₂ hL hm r hr
  have hmem : ∀ x : AmbientSpace, torusProj (torusSide s.L s.m) x ∈ s.cutoffLattice ↔
      x ∈ latticeSubgroup s.cutoffMesh := by
    intro x
    rw [hside.2.2.2 x]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, fun μ => mul_comm _ _⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, funext fun μ => by rw [hk μ]; exact mul_comm _ _⟩
  have haff : ∀ r ∈ s.cutoffLatticeIsometries, ∃ (f : SignedFrame) (v : AmbientSpace),
      v ∈ latticeSubgroup s.cutoffMesh ∧ IsInducedByAffine r f v := by
    intro r hr
    obtain ⟨f, v, hf⟩ := hlift r hr.1
    refine ⟨f, v, ?_, hf⟩
    have h0 : r (torusProj (torusSide s.L s.m) 0) =
        torusProj (torusSide s.L s.m) (f.actOnVector 0 + v) := hf 0
    have hz : f.actOnVector 0 = 0 := (frameLinearMap f).map_zero
    rw [hz, zero_add, torusProj_zero'] at h0
    rw [← hmem, ← h0]
    have h1 : r 0 ∈ r '' (s.cutoffLattice : Set s.Torus) := ⟨0, zero_mem _, rfl⟩
    rw [hr.2] at h1
    exact h1
  have hiso : s.cutoffLatticeIsometries = latticeIsometries s.L s.m ((s.K : ℕ) : ℤ) := by
    ext r
    constructor
    · intro hr
      obtain ⟨f, v, hv, hf⟩ := haff r hr
      exact ⟨f, v, hv, hf⟩
    · intro hr
      exact ⟨(hdist r hr).1.2.2.1, (hcar r hr _ le_rfl).1.1⟩
  have hN : ∃ N : ℤ, torusSide s.L s.m = (N : ℝ) * meshSize s.L ((s.K : ℕ) : ℤ) := by
    obtain ⟨n, hn⟩ := hside.2.1
    exact ⟨n, (div_eq_iff (meshSize_pos' hL0).ne').1 hn⟩
  exact
    { L_pos := hL0
      isometries_eq := hiso
      affine := haff
      mapsCells := fun r hr => (hcar r (hiso ▸ hr) _ le_rfl).1
      trans_mem := fun r hr r' hr' => hgroup.2.1 r r' hr hr'
      symm_mem := fun r hr => hgroup.2.2.1 r hr
      refl_mem := hgroup.1
      barycenter_injective := barycenter_injective_of_divides hL0 hN
      lift := hlift
      torusProj_mem_iff := hmem }
section Requirements
variable {s : Conventions.StandingParameters}
theorem linearOf_eq (F : IsometryFacts s) {r : s.Torus ≃ s.Torus} {f : SignedFrame}
    {v : AmbientSpace} (hf : IsInducedByAffine r f v) : s.linearOf r = frameLinearMap f :=
  frameLinearMap_linearComponent F.L_pos hf
theorem affineMapsAreIsometries (F : IsometryFacts s) : s.AffineMapsAreIsometries := by
  have ofPair : ∀ w ∈ hypercubicGroup, ∀ v ∈ latticeSubgroup s.cutoffMesh,
      ∃ r ∈ s.cutoffLatticeIsometries, (r : s.Torus → s.Torus) = torusAffineMap s.L s.m w v := by
    intro w hw v hv
    obtain ⟨f, rfl⟩ := InfiniteLattice.exists_frameLinearMap_eq_of_mem_hypercubicGroup hw
    let u : s.LatticeSite := ⟨torusProj (torusSide s.L s.m) v, (F.torusProj_mem_iff v).2 hv⟩
    let r : s.Torus ≃ s.Torus := (SignedFrame.torusEquiv s.L s.m f).trans (translateBy u)
    have hr : IsInducedByAffine r f v := by
      intro x
      have h := torusEquiv_isInducedByAffine (L := s.L) (m := s.m) f x
      change SignedFrame.torusEquiv s.L s.m f (toFourTorus s.L s.m x) +
        torusProj (torusSide s.L s.m) v = _
      rw [h, add_zero]
      exact (torusProj_add' _ _ _).symm
    refine ⟨r, ?_, eq_torusAffineMap hw hr⟩
    rw [F.isometries_eq]
    exact ⟨f, v, hv, hr⟩
  refine ⟨ofPair, ?_, ?_, ?_⟩
  · intro v hv u hu
    refine ⟨frameLinearMap 1, InfiniteLattice.frameLinearMap_mem_hypercubicGroup 1, v, hv, ?_⟩
    apply eq_torusAffineMap (InfiniteLattice.frameLinearMap_mem_hypercubicGroup 1)
    intro x
    change torusProj (torusSide s.L s.m) x + (u : s.Torus) = _
    rw [hu, ← torusProj_add', frameLinearMap_one_apply]
  · intro f
    apply eq_torusAffineMap (InfiniteLattice.frameLinearMap_mem_hypercubicGroup f)
    exact torusEquiv_isInducedByAffine f
  · intro μ c hc
    obtain ⟨q, hq⟩ := id hc
    refine ⟨InfiniteLattice.coordinateSignFlip μ,
      InfiniteLattice.coordinateSignFlip_mem_hypercubicGroup μ,
      (2 * c) • InfiniteLattice.basisVector μ, ⟨Pi.single μ q, fun κ => ?_⟩, ?_⟩
    · by_cases h : κ = μ
      · subst h
        simp [InfiniteLattice.basisVector, hq]
      · simp [InfiniteLattice.basisVector, Pi.single_eq_of_ne h]
    · apply eq_torusAffineMap (InfiniteLattice.coordinateSignFlip_mem_hypercubicGroup μ)
      intro x
      rw [PeriodicFunctions.axisReflection_torusProj]
      exact congrArg _ (InfiniteLattice.coordinateReflection_eq_signFlip_add μ c x)
theorem isometriesAreAffine (F : IsometryFacts s) : s.IsometriesAreAffine := by
  have hS : torusSide s.L s.m ≠ 0 := torusSide_ne_zero' F.L_pos
  have part : ∀ r ∈ s.cutoffLatticeIsometries, s.IsAffineTorusMap r := by
    intro r hr
    obtain ⟨f, v, hv, hf⟩ := F.affine r hr
    exact ⟨frameLinearMap f, InfiniteLattice.frameLinearMap_mem_hypercubicGroup f, v, hv,
      eq_torusAffineMap (InfiniteLattice.frameLinearMap_mem_hypercubicGroup f) hf⟩
  refine ⟨?_, ?_, part, ?_, F.isometries_eq, ?_⟩
  · intro r hr
    obtain ⟨f, v, hf⟩ := F.lift r hr
    refine ⟨frameLinearMap f, InfiniteLattice.frameLinearMap_mem_hypercubicGroup f, v, hf, ?_⟩
    intro w' _ v' h'
    obtain ⟨e, k, hk⟩ := affine_pair_unique hS (w := frameLinearMap f) (v := v) (w' := w')
      (v' := v') fun x => (hf x).symm.trans (h' x)
    refine ⟨e.symm, k, ?_⟩
    rw [hk, add_sub_cancel_left]
  · intro r hr w _ v h
    have h0 : r (torusProj (torusSide s.L s.m) 0) =
        torusProj (torusSide s.L s.m) (w 0 + v) := h 0
    rw [map_zero, zero_add, torusProj_zero'] at h0
    rw [← F.torusProj_mem_iff, ← h0]
    have h1 : r 0 ∈ r '' (s.cutoffLattice : Set s.Torus) := ⟨0, zero_mem _, rfl⟩
    rw [hr.2] at h1
    exact h1
  · ext r
    constructor
    · exact part r
    · rintro ⟨w, hw, v, hv, he⟩
      obtain ⟨f, rfl⟩ := InfiniteLattice.exists_frameLinearMap_eq_of_mem_hypercubicGroup hw
      rw [F.isometries_eq]
      refine ⟨f, v, hv, fun x => ?_⟩
      have h := InfiniteLattice.torusAffineMap_torusProj s.L s.m hw v x
      rw [← he] at h
      exact h
  · intro r _ w hw v _ he
    obtain ⟨f, rfl⟩ := InfiniteLattice.exists_frameLinearMap_eq_of_mem_hypercubicGroup hw
    refine linearOf_eq F (f := f) (v := v) fun x => ?_
    have h := InfiniteLattice.torusAffineMap_torusProj s.L s.m hw v x
    rw [← he] at h
    exact h
theorem linearOf_trans (F : IsometryFacts s) {r r' : s.Torus ≃ s.Torus}
    (hr : r ∈ s.cutoffLatticeIsometries) (hr' : r' ∈ s.cutoffLatticeIsometries) :
    s.linearOf (r'.trans r) = s.linearOf r ∘ₗ s.linearOf r' := by
  obtain ⟨f, v, -, hf⟩ := F.affine r hr
  obtain ⟨f', v', -, hf'⟩ := F.affine r' hr'
  obtain ⟨g, u, -, hg⟩ := F.affine _ (F.trans_mem r hr r' hr')
  rw [linearOf_eq F hf, linearOf_eq F hf', linearOf_eq F hg]
  refine (affine_pair_unique (torusSide_ne_zero' (m := s.m) F.L_pos) (w := frameLinearMap g)
    (v := u) (w' := frameLinearMap f ∘ₗ frameLinearMap f') (v' := frameLinearMap f v' + v)
    fun x => ?_).1
  have h1 : r' (torusProj (torusSide s.L s.m) x) =
      torusProj (torusSide s.L s.m) (f'.actOnVector x + v') := hf' x
  have h2 : r (torusProj (torusSide s.L s.m) (f'.actOnVector x + v')) =
      torusProj (torusSide s.L s.m) (f.actOnVector (f'.actOnVector x + v') + v) := hf _
  have h3 : (r'.trans r) (torusProj (torusSide s.L s.m) x) =
      torusProj (torusSide s.L s.m) (g.actOnVector x + u) := hg x
  refine h3.symm.trans ?_
  rw [Equiv.trans_apply, h1, h2, signedFrame_act_add, add_assoc]
  rfl
theorem linearOf_refl (F : IsometryFacts s) : s.linearOf (Equiv.refl s.Torus) = LinearMap.id := by
  have h : IsInducedByAffine (Equiv.refl s.Torus) (1 : SignedFrame) 0 := by
    intro x
    have e : (1 : SignedFrame).actOnVector x = x := frameLinearMap_one_apply x
    rw [e, add_zero]
    rfl
  rw [linearOf_eq F h]
  exact LinearMap.ext frameLinearMap_one_apply
theorem linearPartHom (F : IsometryFacts s) : s.LinearPartHom := by
  intro r hr r' hr'
  obtain ⟨f, v, -, hf⟩ := F.affine r hr
  refine ⟨fun y ζ => ?_, linearOf_trans F hr hr', ?_, ?_⟩
  · rw [linearOf_eq F hf]
    exact induced_add_torusProj hf y ζ
  · rw [← linearOf_trans F (F.symm_mem r hr) hr, Equiv.self_trans_symm, linearOf_refl F]
  · rw [← linearOf_trans F hr (F.symm_mem r hr), Equiv.symm_trans_self, linearOf_refl F]
theorem actionOnBonds (F : IsometryFacts s) : s.ActionOnBonds := by
  intro r hr r' hr'
  obtain ⟨f, v, -, hf⟩ := F.affine r hr
  have hp := linearOf_eq F hf
  have hc := F.mapsCells r hr
  have hc' := F.mapsCells r' hr'
  have hcs := F.mapsCells r.symm (F.symm_mem r hr)
  have hct := F.mapsCells _ (F.trans_mem r hr r' hr')
  have hleft : Function.LeftInverse (bondImage r.symm)
      (bondImage r : s.LatticeBond → s.LatticeBond) := by
    intro b
    apply bond_ext_of_source_target
    · rw [bondImage_source' hcs, bondImage_source' hc, Equiv.symm_apply_apply]
    · rw [bondImage_target' hcs, bondImage_target' hc, Equiv.symm_apply_apply]
  have hright : Function.RightInverse (bondImage r.symm)
      (bondImage r : s.LatticeBond → s.LatticeBond) := by
    intro b
    apply bond_ext_of_source_target
    · rw [bondImage_source' hc, bondImage_source' hcs, Equiv.apply_symm_apply]
    · rw [bondImage_target' hc, bondImage_target' hcs, Equiv.apply_symm_apply]
  refine ⟨?_, ?_, ?_, ?_, ⟨hleft.injective, hright.surjective⟩, hleft, hright, ?_⟩
  · rw [hp]
    ext e
    constructor
    · rintro ⟨e₀, he₀, rfl⟩
      exact signedFrame_act_mem_meshVectors f he₀
    · intro he
      obtain ⟨g, u, -, hg⟩ := F.affine _ (F.symm_mem r hr)
      refine ⟨g.actOnVector e, signedFrame_act_mem_meshVectors g he, ?_⟩
      have h := LinearMap.congr_fun ((linearPartHom F r hr r' hr').2.2.2) e
      rw [hp, linearOf_eq F hg] at h
      exact h
  · intro y y' e e' hy he
    rw [hp] at he
    refine ⟨bondImage_bondFrom hf hc hy he, bondFromSegment_image hf hy he, hy, ?_⟩
    change (y' : s.Torus) + torusProj (torusSide s.L s.m) e'.1 =
      r ((y : s.Torus) + torusProj (torusSide s.L s.m) e.1)
    rw [induced_add_torusProj hf, hy, he]
    rfl
  · intro b
    apply bond_ext_of_source_target
    · exact (bondImage_source' hc b.opposite).trans (bondImage_target' hc b).symm
    · exact (bondImage_target' hc b.opposite).trans (bondImage_source' hc b).symm
  · intro b
    apply bond_ext_of_source_target
    · rw [bondImage_source' hct, bondImage_source' hc, bondImage_source' hc']
      rfl
    · rw [bondImage_target' hct, bondImage_target' hc, bondImage_target' hc']
      rfl
  · exact fun b => ⟨bondImage_source' hc b, bondImage_target' hc b⟩
theorem actionOnPlaquettes (F : IsometryFacts s) : s.ActionOnPlaquettes := by
  refine ⟨F.barycenter_injective, fun r hr r' hr' => ?_⟩
  obtain ⟨f, v, -, hf⟩ := F.affine r hr
  have hp := linearOf_eq F hf
  have hc := F.mapsCells r hr
  have bary : ∀ {ρ : s.Torus ≃ s.Torus}, ρ ∈ s.cutoffLatticeIsometries →
      ∀ p : s.LatticePlaquette, (plaquetteImage ρ p).barycenter = ρ p.barycenter :=
    fun {ρ} hρ p => (F.mapsCells ρ hρ).2.2.2.2.2.2.2.1 p
  have hsymm := F.symm_mem r hr
  have hleft : Function.LeftInverse (plaquetteImage r.symm)
      (plaquetteImage r : s.LatticePlaquette → s.LatticePlaquette) := by
    intro p
    apply F.barycenter_injective
    rw [bary hsymm, bary hr, Equiv.symm_apply_apply]
  have hright : Function.RightInverse (plaquetteImage r.symm)
      (plaquetteImage r : s.LatticePlaquette → s.LatticePlaquette) := by
    intro p
    apply F.barycenter_injective
    rw [bary hr, bary hsymm, Equiv.apply_symm_apply]
  have hface : ∀ p : s.LatticePlaquette, (plaquetteImage r p).face = r '' p.face :=
    fun p => hc.2.2.2.2.2.1 p
  refine ⟨fun p => ⟨bary hr p, fun p' h => F.barycenter_injective (h.trans (bary hr p).symm),
      hface p, ?_⟩,
    fun p => ?_, ⟨hleft.injective, hright.surjective⟩, hleft, hright, fun p => ⟨?_, ?_⟩, ?_⟩
  · rw [faceSpannedBy_eq_face F.L_pos, faceSpannedBy_eq_face F.L_pos, hface]
  · apply F.barycenter_injective
    rw [bary (F.trans_mem r hr r' hr'), bary hr, bary hr']
    rfl
  · rintro γ ⟨e, e₁, hfr, c, hcc, rfl⟩
    let g : s.meshSteps := ⟨f.actOnVector e.1, signedFrame_act_mem_meshVectors f e.2⟩
    let g₁ : s.meshSteps := ⟨f.actOnVector e₁.1, signedFrame_act_mem_meshVectors f e₁.2⟩
    let c₁ : s.LatticeSite := ⟨r c, mapsCells_site_mem hc c⟩
    refine ⟨g, g₁, ?_, c₁, ?_, bondImage_circuitFrom hf hc rfl rfl rfl⟩
    · obtain ⟨h', x', he, -, -⟩ := plaquetteImage_plaquetteSpannedBy F.barycenter_injective hf hc
        p.origin p.firstAxis_lt_secondAxis.ne
        (unit_cast_eq_one_or_neg_one (f.2 (f.1⁻¹ p.firstAxis)))
        (unit_cast_eq_one_or_neg_one (f.2 (f.1⁻¹ p.secondAxis)))
        (signedFrame_act_single f p.firstAxis 1) (signedFrame_act_single f p.secondAxis 1)
      rw [plaquetteSpannedBy_axes] at he
      rw [he, isFrame_plaquetteSpannedBy_iff]
      rcases hfr with ⟨a, b⟩ | ⟨a, b⟩
      · exact Or.inl ⟨isAlongAxis_signedFrame_act f a, isAlongAxis_signedFrame_act f b⟩
      · exact Or.inr ⟨isAlongAxis_signedFrame_act f a, isAlongAxis_signedFrame_act f b⟩
    · rw [frameVertex_image hf (bary hr p) (e := e) (e₁ := e₁) rfl rfl, ← hcc]
  · intro e e₁ g g₁ c c₁ _ _ hc₁ he he₁
    rw [hp] at he he₁
    exact bondImage_circuitFrom hf hc hc₁ he he₁
  · intro x μ ν μ' ν' h u u' hu hu' h₁ h₂
    rw [hp] at h₁ h₂
    exact plaquetteImage_plaquetteSpannedBy F.barycenter_injective hf hc x h hu hu' h₁ h₂
end Requirements
end AffineTorusIsometries
theorem Conventions.StandingParameters.affineDescriptionOfIsometries_holds
    (h₁ : PeriodicLattice.LatticeIsometryGroupActionStatement)
    (h₂ : Tower.OrthogonalMotions.Classification)
    (h₃ : Conventions.StandingParameters.TorusLatticeAndIsometryFacts) :
    Conventions.StandingParameters.AffineDescriptionOfIsometries := fun s =>
  have F := AffineTorusIsometries.isometryFacts h₁ h₂ h₃ s
  ⟨AffineTorusIsometries.affineMapsAreIsometries F, AffineTorusIsometries.isometriesAreAffine F,
    AffineTorusIsometries.linearPartHom F, AffineTorusIsometries.actionOnBonds F,
    AffineTorusIsometries.actionOnPlaquettes F⟩
end YangMills.Construction
end
