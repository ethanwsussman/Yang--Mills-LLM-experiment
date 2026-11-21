import YangMills.Construction.Continuum.OperationsOnFunctionsOfSeveralPoints
import YangMills.Construction.GrowingTori.TranslationsIsometriesAndMirrorsOfFourSpaceProof
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotionsProof
import YangMills.Construction.Lattice.LatticeIsometriesAsMapsOfPairsProof
import YangMills.Construction.TorusOrFourSpace.IsometriesLiftToOrthogonalMotions
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefined
import Mathlib
set_option autoImplicit false
open Matrix
open scoped ContDiff
namespace YangMills.Construction
open Euclidean (RealMatrix4 hyperoctahedral4 O4 signedPermMatrix signedPermO4)
open Tower.OrthogonalMotions (IsIntegerMatrix)
open TorusMetric (euclidNormVec)
namespace PeriodicSpace.Kind.OrthogonalLift
theorem mul_transpose_self_of_mem {S : RealMatrix4} (hS : S ∈ O4) : S * Sᵀ = 1 := by apply _root_.YangMills.Construction.Tower.OrthogonalMotions.orth_mul_transpose_self <;> assumption
theorem transpose_mul_self_of_mem {S : RealMatrix4} (hS : S ∈ O4) : Sᵀ * S = 1 := by apply _root_.YangMills.Construction.ConfigSpace.orth_transpose_mul_self <;> assumption
theorem transpose_mem_O4 {S : RealMatrix4} (hS : S ∈ O4) : Sᵀ ∈ O4 := by apply _root_.YangMills.Construction.Tower.OrthogonalMotions.orth_transpose_mem <;> assumption
theorem inv_eq_transpose_of_mem {S : RealMatrix4} (hS : S ∈ O4) : S⁻¹ = Sᵀ :=
  Matrix.inv_eq_right_inv (mul_transpose_self_of_mem hS)
theorem euclidNormVec_mulVec {S : RealMatrix4} (hS : S ∈ O4) (x : Fin 4 → ℝ) :
    euclidNormVec (S *ᵥ x) = euclidNormVec x := by apply _root_.YangMills.Construction.ConfigSpace.euclidNormVec_orth_mulVec <;> assumption
theorem signedPermMatrix_isInteger (π : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤˣ) :
    IsIntegerMatrix (signedPermMatrix π s) := by
  intro μ ν
  by_cases h : ν = π μ
  · exact ⟨((s μ : ℤˣ) : ℤ), by simp [signedPermMatrix, h]⟩
  · exact ⟨0, by simp [signedPermMatrix, h]⟩
theorem mem_O4_and_isInteger_of_mem {S : RealMatrix4} (h : S ∈ hyperoctahedralMatrices) :
    S ∈ O4 ∧ IsIntegerMatrix S := by
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨π, s, hs⟩ : ∃ π s, w = signedPermO4 π s := hw
  refine ⟨w.2, ?_⟩
  rw [hs]
  exact signedPermMatrix_isInteger π s
theorem exists_sole_unit_coord (m : Fin 4 → ℤ) (h : ∑ ν, m ν ^ 2 = 1) :
    ∃ ν, (m ν = 1 ∨ m ν = -1) ∧ ∀ ν', ν' ≠ ν → m ν' = 0 := by apply _root_.YangMills.Construction.AffineTorusIsometries.exists_unit_of_sum_sq_eq_one <;> assumption
theorem mem_hyperoctahedralMatrices_of {S : RealMatrix4} (hS : S ∈ O4)
    (hI : IsIntegerMatrix S) : S ∈ hyperoctahedralMatrices := by
  choose m hm using hI
  have hrow : ∀ μ μ', ∑ ν, m μ ν * m μ' ν = if μ = μ' then 1 else 0 := by
    intro μ μ'
    have h := congrFun (congrFun (mul_transpose_self_of_mem hS) μ) μ'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, hm] at h
    exact_mod_cast h
  have hrow1 : ∀ μ, ∑ ν, m μ ν ^ 2 = 1 := by
    intro μ
    simpa [sq] using hrow μ μ
  choose π hπ hπ0 using fun μ => exists_sole_unit_coord (m μ) (hrow1 μ)
  have hinj : Function.Injective π := by
    intro μ μ' he
    by_contra hne
    have hsum : ∑ ν, m μ ν * m μ' ν = m μ (π μ) * m μ' (π μ) :=
      Finset.sum_eq_single (π μ) (fun b _ hb => by rw [hπ0 μ b hb, zero_mul])
        (fun h => absurd (Finset.mem_univ _) h)
    have h := hrow μ μ'
    rw [if_neg hne, hsum] at h
    have a := hπ μ
    have b := hπ μ'
    rw [← he] at b
    rcases a with a | a <;> rcases b with b | b <;> simp [a, b] at h
  obtain ⟨e, he⟩ : ∃ e : Equiv.Perm (Fin 4), ∀ μ, e μ = π μ :=
    ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.1 hinj), fun _ => rfl⟩
  have hu : ∀ μ, ∃ u : ℤˣ, (u : ℤ) = m μ (π μ) := by
    intro μ
    rcases hπ μ with h | h
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h]⟩
  choose sg hsg using hu
  refine ⟨signedPermO4 e sg, ⟨e, sg, rfl⟩, ?_⟩
  change signedPermMatrix e sg = S
  ext μ ν
  simp only [signedPermMatrix, Matrix.of_apply]
  rw [hm]
  by_cases h : ν = π μ
  · rw [if_pos (h.trans (he μ).symm), hsg, h]
  · rw [if_neg (fun h' => h (h'.trans (he μ))), hπ0 μ ν h]
    simp
theorem mulVec_mem_latticeSubgroup {S : RealMatrix4} (hI : IsIntegerMatrix S) {a : ℝ}
    {x : Fin 4 → ℝ} (hx : x ∈ InfiniteLattice.latticeSubgroup a) :
    S *ᵥ x ∈ InfiniteLattice.latticeSubgroup a := by
  obtain ⟨n, hn⟩ := hx
  choose m hm using hI
  refine ⟨fun μ => ∑ ν, m μ ν * n ν, fun μ => ?_⟩
  simp only [Matrix.mulVec, dotProduct, hm, hn]
  push_cast
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun ν _ => by ring
theorem isInteger_of_preserves_lattice {S : RealMatrix4} {a : ℝ} (ha : a ≠ 0)
    (h : ∀ x ∈ InfiniteLattice.latticeSubgroup a, S *ᵥ x ∈ InfiniteLattice.latticeSubgroup a) :
    IsIntegerMatrix S := by
  intro μ ν
  have hx : (Pi.single ν a : Fin 4 → ℝ) ∈ InfiniteLattice.latticeSubgroup a := by
    refine ⟨Pi.single ν 1, fun μ' => ?_⟩
    by_cases h' : μ' = ν
    · subst h'
      simp
    · simp [Pi.single_eq_of_ne h']
  obtain ⟨n, hn⟩ := h _ hx
  refine ⟨n μ, ?_⟩
  have h1 := hn μ
  have h2 : (S *ᵥ (Pi.single ν a : Fin 4 → ℝ)) μ = S μ ν * a := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h2] at h1
  exact mul_right_cancel₀ ha h1
variable {D : Params} {E : Kind}
theorem quotMap_add (hw : WellPosedness.WellPosed) (x x' : Fin 4 → ℝ) :
    E.quotMap D (x + x') = E.quotMap D x + E.quotMap D x' :=
  (hw D E).1.1 x x'
theorem quotMap_surjective (hw : WellPosedness.WellPosed) :
    Function.Surjective (E.quotMap D) :=
  (hw D E).1.2.1
theorem quotMap_eq_zero_iff (hw : WellPosedness.WellPosed)
    (x : Fin 4 → ℝ) : E.quotMap D x = 0 ↔ x ∈ E.periodGroup D :=
  (hw D E).1.2.2 x
theorem quotDist_euclidean (hw : WellPosedness.WellPosed)
    (y y' : Fin 4 → ℝ) : quotDist D Kind.euclidean y y' = euclidNormVec (y - y') := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := hw D Kind.euclidean
  exact h y y'
theorem quotDist_torus (hw : WellPosedness.WellPosed) (y y' : D.Torus) :
    quotDist D Kind.torus y y' = TorusMetric.torusEuclidNorm (y - y') := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := hw D Kind.torus
  exact (h y y').1
theorem params_side_ne_zero (D : Params) : D.side ≠ 0 := by
  have hL : 0 < D.L := by
    have := D.isAdmissible.2
    omega
  simp only [Params.side, PeriodicLattice.torusSide]
  positivity
theorem mulVec_mem_periodGroup_of_isInteger {S : RealMatrix4} (hI : IsIntegerMatrix S)
    {x : Fin 4 → ℝ} (hx : x ∈ E.periodGroup D) : S *ᵥ x ∈ E.periodGroup D := by
  cases E with
  | euclidean =>
    have h0 : x = 0 := AddSubgroup.mem_bot.1 hx
    rw [h0, Matrix.mulVec_zero]
    exact AddSubgroup.zero_mem _
  | torus => exact mulVec_mem_latticeSubgroup hI hx
theorem liftsVia_unique (hw : WellPosedness.WellPosed)
    {s s' : E.Pt D → E.Pt D} {S : RealMatrix4} {v : Fin 4 → ℝ}
    (h : LiftsVia D E s S v) (h' : LiftsVia D E s' S v) : s = s' := by
  funext y
  obtain ⟨x, rfl⟩ := quotMap_surjective (D := D) (E := E) hw y
  rw [h x, h' x]
theorem euclidNormVec_affine_sub {S : RealMatrix4} (hS : S ∈ O4) (v y y' : Fin 4 → ℝ) :
    euclidNormVec ((S *ᵥ y + v) - (S *ᵥ y' + v)) = euclidNormVec (y - y') := by
  have h : (S *ᵥ y + v) - (S *ᵥ y' + v) = S *ᵥ (y - y') := by
    rw [Matrix.mulVec_sub]
    abel
  rw [h, euclidNormVec_mulVec hS]
theorem exists_isometry_liftsVia (hy : Tower.OrthogonalMotions.Classification)
    (hw : WellPosedness.WellPosed) {S : RealMatrix4}
    (hS : S ∈ motionMatrices E) (v : Fin 4 → ℝ) :
    ∃ s, LiftsVia D E s S v ∧ IsIsometry D E s := by
  cases E with
  | euclidean =>
    have hO : S ∈ O4 := hS
    refine ⟨fun x : Fin 4 → ℝ => S *ᵥ x + v, fun x => rfl, fun y y' => ?_⟩
    exact (quotDist_euclidean hw _ _).trans
      ((euclidNormVec_affine_sub hO v y y').trans (quotDist_euclidean hw y y').symm)
  | torus =>
    have hS' : S ∈ hyperoctahedralMatrices := hS
    obtain ⟨hO, hI⟩ := mem_O4_and_isInteger_of_mem hS'
    obtain ⟨f, hf, hi⟩ :=
      (hy.2.2.2 D.L D.m D.isAdmissible D.m.pos).2.2.2 S hO hI v
    exact ⟨f, hf, fun y y' =>
      (quotDist_torus hw _ _).trans ((hi y y').trans (quotDist_torus hw y y').symm)⟩
theorem liftedMap_spec (hy : Tower.OrthogonalMotions.Classification)
    (hw : WellPosedness.WellPosed) {S : RealMatrix4}
    (hS : S ∈ motionMatrices E) (v : Fin 4 → ℝ) :
    LiftsVia D E (liftedMap D E S v) S v ∧ IsIsometry D E (liftedMap D E S v) := by
  obtain ⟨s, hl, hi⟩ := exists_isometry_liftsVia (D := D) hy hw hS v
  have hm : LiftsVia D E (liftedMap D E S v) S v :=
    Classical.epsilon_spec (p := fun s => LiftsVia D E s S v) ⟨s, hl⟩
  refine ⟨hm, ?_⟩
  rw [liftsVia_unique hw hm hl]
  exact hi
theorem mem_motionMatrices_of_hyperoctahedral {S : RealMatrix4}
    (h : S ∈ hyperoctahedralMatrices) : S ∈ motionMatrices E := by
  cases E with
  | euclidean => exact (mem_O4_and_isInteger_of_mem h).1
  | torus => exact h
theorem one_mem_hyperoctahedralMatrices : (1 : RealMatrix4) ∈ hyperoctahedralMatrices :=
  ⟨1, Subgroup.one_mem _, rfl⟩
theorem mulVec_mem_periodGroup_of_liftsVia (hw : WellPosedness.WellPosed)
    {s : E.Pt D → E.Pt D} {S : RealMatrix4} {v : Fin 4 → ℝ} (hl : LiftsVia D E s S v)
    {k : Fin 4 → ℝ} (hk : k ∈ E.periodGroup D) : S *ᵥ k ∈ E.periodGroup D := by
  have hk0 : E.quotMap D k = 0 := (quotMap_eq_zero_iff hw k).2 hk
  have h00 : E.quotMap D 0 = 0 :=
    (quotMap_eq_zero_iff hw 0).2 (AddSubgroup.zero_mem _)
  have h3 : E.quotMap D (S *ᵥ k) + E.quotMap D v = 0 + E.quotMap D v := by
    rw [zero_add]
    calc E.quotMap D (S *ᵥ k) + E.quotMap D v
        = E.quotMap D (S *ᵥ k + v) := (quotMap_add hw _ _).symm
      _ = s (E.quotMap D k) := (hl k).symm
      _ = s (E.quotMap D 0) := by rw [hk0, h00]
      _ = E.quotMap D (S *ᵥ 0 + v) := hl 0
      _ = E.quotMap D v := by rw [Matrix.mulVec_zero, zero_add]
  exact (quotMap_eq_zero_iff hw _).1 (add_right_cancel h3)
theorem mem_motionMatrices_of_liftsVia (hw : WellPosedness.WellPosed)
    {s : E.Pt D → E.Pt D} {S : RealMatrix4} {v : Fin 4 → ℝ} (hS : S ∈ O4)
    (hl : LiftsVia D E s S v) : S ∈ motionMatrices E := by
  cases E with
  | euclidean => exact hS
  | torus =>
    exact mem_hyperoctahedralMatrices_of hS (isInteger_of_preserves_lattice (params_side_ne_zero D)
      fun x hx => mulVec_mem_periodGroup_of_liftsVia hw hl hx)
theorem inv_mem_motionMatrices {S : RealMatrix4} (hS : S ∈ O4)
    (h : S ∈ motionMatrices E) : S⁻¹ ∈ motionMatrices E := by
  rw [inv_eq_transpose_of_mem hS]
  cases E with
  | euclidean => exact transpose_mem_O4 hS
  | torus =>
    have hI := (mem_O4_and_isInteger_of_mem h).2
    exact mem_hyperoctahedralMatrices_of (transpose_mem_O4 hS) fun μ ν => hI ν μ
theorem isometryInv_properties (hy : Tower.OrthogonalMotions.Classification)
    (hw : WellPosedness.WellPosed) {s : E.Pt D → E.Pt D}
    {S : RealMatrix4} {v : Fin 4 → ℝ} (hS : S ∈ O4) (hl : LiftsVia D E s S v) :
    Function.Bijective s ∧ Function.LeftInverse (isometryInv D E s) s ∧
      Function.RightInverse (isometryInv D E s) s ∧
      LiftsVia D E (isometryInv D E s) S⁻¹ (-(S⁻¹ *ᵥ v)) ∧
      IsIsometry D E (isometryInv D E s) := by
  have hm := mem_motionMatrices_of_liftsVia hw hS hl
  obtain ⟨s', hl', hi'⟩ := exists_isometry_liftsVia (D := D) hy hw
    (inv_mem_motionMatrices hS hm) (-(S⁻¹ *ᵥ v))
  have hinv1 : S⁻¹ * S = 1 := by
    rw [inv_eq_transpose_of_mem hS]
    exact transpose_mul_self_of_mem hS
  have hinv2 : S * S⁻¹ = 1 := by
    rw [inv_eq_transpose_of_mem hS]
    exact mul_transpose_self_of_mem hS
  have hL : Function.LeftInverse s' s := by
    intro y
    obtain ⟨x, rfl⟩ := quotMap_surjective (D := D) (E := E) hw y
    rw [hl x, hl' (S *ᵥ x + v), Matrix.mulVec_add, Matrix.mulVec_mulVec, hinv1,
      Matrix.one_mulVec, add_neg_cancel_right]
  have hR : Function.RightInverse s' s := by
    intro y
    obtain ⟨x, rfl⟩ := quotMap_surjective (D := D) (E := E) hw y
    rw [hl' x, hl (S⁻¹ *ᵥ x + -(S⁻¹ *ᵥ v)), Matrix.mulVec_add, Matrix.mulVec_neg,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hinv2, Matrix.one_mulVec, Matrix.one_mulVec,
      neg_add_cancel_right]
  have hinj : Function.Injective s := hL.injective
  have hsur : Function.Surjective s := hR.surjective
  have heq : isometryInv D E s = s' := by
    funext y
    have h := Function.leftInverse_invFun hinj (s' y)
    rw [hR y] at h
    exact h
  rw [heq]
  exact ⟨⟨hinj, hsur⟩, hL, hR, hl', hi'⟩
theorem isometryHasLift_holds (hy : Tower.OrthogonalMotions.Classification)
    (hw : WellPosedness.WellPosed) : IsometryHasLift D E := by
  intro s hs
  cases E with
  | euclidean =>
    obtain ⟨R, hR, v, hf⟩ := hy.2.1 s fun x y =>
      (quotDist_euclidean hw _ _).symm.trans ((hs x y).trans (quotDist_euclidean hw x y))
    exact ⟨R, hR, v, hf, fun h => by cases h⟩
  | torus =>
    obtain ⟨R, hR, hΓ, v, hf⟩ :=
      (hy.2.2.2 D.L D.m D.isAdmissible D.m.pos).2.2.1 s fun a b =>
        (quotDist_torus hw _ _).symm.trans ((hs a b).trans (quotDist_torus hw a b))
    refine ⟨R, hR, v, hf, fun _ => mem_hyperoctahedralMatrices_of hR ?_⟩
    refine isInteger_of_preserves_lattice (params_side_ne_zero D) fun x hx => ?_
    have hmem : R *ᵥ x ∈ (fun x : Fin 4 → ℝ => R *ᵥ x) ''
        (InfiniteLattice.latticeSubgroup (PeriodicLattice.torusSide D.L D.m) :
          Set (Fin 4 → ℝ)) := ⟨x, hx, rfl⟩
    rw [hΓ] at hmem
    exact hmem
theorem continuousPreservesCompact_of_isIsometry {s : E.Pt D → E.Pt D}
    (hs : IsIsometry D E s) : ContinuousPreservesCompact D E s := by
  refine ⟨fun x ε hε => ⟨ε, hε, fun y hxy => (hs x y).trans_lt hxy⟩, fun K hK 𝒰 hU hc => ?_⟩
  have hopen : ∀ V ∈ (fun U => s ⁻¹' U) '' 𝒰, MetricNotions.IsOpenWrt (quotDist D E) V := by
    rintro _ ⟨U, hUm, rfl⟩ x hx
    obtain ⟨r, hr, h⟩ := hU U hUm (s x) hx
    exact ⟨r, hr, fun y hxy => h (s y) ((hs x y).trans_lt hxy)⟩
  have hcov : K ⊆ ⋃₀ ((fun U => s ⁻¹' U) '' 𝒰) := by
    intro x hx
    obtain ⟨U, hUm, hxU⟩ := hc ⟨x, hx, rfl⟩
    exact ⟨s ⁻¹' U, ⟨U, hUm, rfl⟩, hxU⟩
  obtain ⟨𝒱, hsub, hfin, hcov'⟩ := hK _ hopen hcov
  obtain ⟨𝒰', hsub', hfin', hcov''⟩ :=
    (Set.exists_subset_image_finite_and (p := fun 𝒲 => K ⊆ ⋃₀ 𝒲)).1 ⟨𝒱, hsub, hfin, hcov'⟩
  refine ⟨𝒰', hsub', hfin', ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨_, ⟨U, hUm, rfl⟩, hxU⟩ := hcov'' hx
  exact ⟨U, hUm, hxU⟩
theorem supportQ_comp {s : E.Pt D → E.Pt D} (hs : IsIsometry D E s)
    (hsur : Function.Surjective s) {Z : Type} [Zero Z] (f : E.Pt D → Z) :
    supportQ D E (f ∘ s) = s ⁻¹' supportQ D E f := by
  ext x
  constructor
  · intro h r hr
    obtain ⟨y, hy, hd⟩ := h r hr
    exact ⟨s y, hy, (hs x y).trans_lt hd⟩
  · intro h r hr
    obtain ⟨z, hz, hd⟩ := h r hr
    obtain ⟨y, rfl⟩ := hsur z
    exact ⟨y, hz, (hs x y).symm.trans_lt hd⟩
theorem contDiff_affine (S : RealMatrix4) (v : Fin 4 → ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun x : Fin 4 → ℝ => S *ᵥ x + v := by apply _root_.YangMills.Construction.ToriLimits.EuclideanSymmetryFacts.contDiff_orthoAffine <;> assumption
theorem comp_comp_quotMap {s : E.Pt D → E.Pt D} {S : RealMatrix4} {v : Fin 4 → ℝ}
    (hl : LiftsVia D E s S v) (f : E.Pt D → ℝ) :
    (f ∘ s) ∘ E.quotMap D = (f ∘ E.quotMap D) ∘ fun x => S *ᵥ x + v := by
  funext x
  simp only [Function.comp_apply]
  rw [hl x]
theorem isometryOrthogonalLiftTheorem_holds (hy : Tower.OrthogonalMotions.Classification)
    (hw : WellPosedness.WellPosed) :
    IsometryOrthogonalLiftTheorem := by
  refine ⟨fun S => ⟨mem_O4_and_isInteger_of_mem,
    fun h => mem_hyperoctahedralMatrices_of h.1 h.2⟩, fun D E => ?_⟩
  have hlift := isometryHasLift_holds (D := D) (E := E) hy hw
  have hfacts : ∀ s, IsIsometry D E s → Function.Bijective s ∧
      Function.LeftInverse (isometryInv D E s) s ∧
      Function.RightInverse (isometryInv D E s) s ∧
      IsIsometry D E (isometryInv D E s) := by
    intro s hs
    obtain ⟨S, hS, v, hl, -⟩ := hlift s hs
    obtain ⟨hb, hL, hR, -, hi⟩ := isometryInv_properties hy hw hS hl
    exact ⟨hb, hL, hR, hi⟩
  have hclasses : RegularityCompIsometry D E := by
    intro s hs f
    obtain ⟨S, -, v, hl, -⟩ := hlift s hs
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · change ContDiff ℝ 1 ((f ∘ s) ∘ E.quotMap D)
      rw [comp_comp_quotMap hl f]
      exact ContDiff.comp hf (contDiff_affine S v)
    · change ContDiff ℝ ∞ ((f ∘ s) ∘ E.quotMap D)
      rw [comp_comp_quotMap hl f]
      exact ContDiff.comp hf (contDiff_affine S v)
  refine ⟨?_, hlift, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hclasses, ?_⟩
  · intro w hwm
    obtain ⟨hO, hI⟩ := mem_O4_and_isInteger_of_mem hwm
    ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact mulVec_mem_periodGroup_of_isInteger hI hx'
    · intro hx
      refine ⟨wᵀ *ᵥ x, mulVec_mem_periodGroup_of_isInteger (fun μ ν => hI ν μ) hx, ?_⟩
      change w *ᵥ (wᵀ *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, mul_transpose_self_of_mem hO, Matrix.one_mulVec]
  · intro v S hS
    obtain ⟨hl, hi⟩ := liftedMap_spec (D := D) hy hw hS v
    exact ⟨⟨_, hl, fun s' hs' => liftsVia_unique hw hs' hl⟩, hl, hi⟩
  · intro w hwm
    obtain ⟨hl, hi⟩ := liftedMap_spec (D := D) hy hw
      (mem_motionMatrices_of_hyperoctahedral (E := E) hwm) 0
    exact ⟨fun x => (hl x).trans (by rw [add_zero]), hi⟩
  · intro a v hv
    have hv' : E.quotMap D v = a := hv
    obtain ⟨hl, hi⟩ := liftedMap_spec (D := D) hy hw
      (mem_motionMatrices_of_hyperoctahedral (E := E) one_mem_hyperoctahedralMatrices) v
    have ht : LiftsVia D E (fun y => y + a) 1 v := by
      intro x
      rw [Matrix.one_mulVec, quotMap_add hw, hv']
    have heq : liftedMap D E 1 v = fun y => y + a := liftsVia_unique hw hl ht
    exact ⟨heq, heq ▸ hi⟩
  · intro s hs
    obtain ⟨hb, hL, hR, -⟩ := hfacts s hs
    exact ⟨hb, hL, hR⟩
  · intro s hs S hS v hl
    obtain ⟨-, -, -, hl', hi⟩ := isometryInv_properties hy hw hS hl
    refine ⟨hi, fun x => ?_, fun hE => ?_⟩
    · rw [sub_eq_add_neg]
      exact hl' x
    · subst hE
      exact mem_motionMatrices_of_liftsVia hw hS hl
  · intro s hs
    exact ⟨continuousPreservesCompact_of_isIsometry hs,
      continuousPreservesCompact_of_isIsometry (hfacts s hs).2.2.2⟩
  · intro s hs Z _ f
    exact supportQ_comp hs (hfacts s hs).1.2 f
  · intro s hs n _ f hf
    obtain ⟨hb, hL, hR, hi⟩ := hfacts s hs
    obtain ⟨hC, hK, hd⟩ := hf
    refine ⟨fun i => (hclasses s hs (f i)).1 (hC i), fun i => ?_, fun i k hne => ?_⟩
    · change IsCompactQ D E (supportQ D E (f i ∘ s))
      rw [supportQ_comp hs hb.2,
        ← Set.image_eq_preimage_of_inverse (f := isometryInv D E s) (g := s) hR hL]
      exact (continuousPreservesCompact_of_isIsometry hi).2 _ (hK i)
    · change Disjoint (supportQ D E (f i ∘ s)) (supportQ D E (f k ∘ s))
      rw [supportQ_comp hs hb.2, supportQ_comp hs hb.2]
      exact (hd i k hne).preimage s
end PeriodicSpace.Kind.OrthogonalLift
end YangMills.Construction
