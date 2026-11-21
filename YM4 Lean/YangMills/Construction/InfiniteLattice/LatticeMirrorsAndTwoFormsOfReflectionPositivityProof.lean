import YangMills.Construction.InfiniteLattice.ExpansionsMeetTheConditionsOfTheReconstructionProof
import YangMills.Construction.InfiniteLattice.LatticeMirrorsAndTwoFormsOfReflectionPositivity
import YangMills.Construction.InfiniteLattice.ReflectionPositivityDoesNotDependOnTheSide
import YangMills.Construction.InfiniteLattice.RulesForObservablesIsometriesAndMirrorsProof
import YangMills.Construction.InfiniteLattice.SpaceOfTheConfigurationsOfOneLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.LatticeConventions
namespace LatticeMirrorsAndReflectionPositivity
open YangMills.Construction.InfiniteLattice (Link GaugeField IsLocalObservable IsRegionMeasurable
  IsBoundedObservable IsReflectionPositiveAt IsReflectionPositiveOn LatticeSymmetry LatticeMirror
  ReflectionClass linksWithin localRegionObservables boundedRegionObservables hyperplaneReflect
  regionSigma)
open NormalHyperplane (IsReflectionPositiveAcrossMirror IsReflectionPositiveAcrossFamily
  reflectSymmetry reflect_eq_hyperplaneReflect toMirrorPair)
open MirrorSideIndependence (reflectedPairing)
theorem euclidDot_basisVector (μ : Direction) (x : Point) : euclidDot (basisVector μ) x = x μ := by
  simp [euclidDot, basisVector, Pi.single_apply]
theorem euclidDot_add_left (u v x : Point) : euclidDot (u + v) x = euclidDot u x + euclidDot v x := by
  simp [euclidDot, add_mul, Finset.sum_add_distrib]
theorem euclidDot_sub_left (u v x : Point) : euclidDot (u - v) x = euclidDot u x - euclidDot v x := by apply _root_.YangMills.Construction.LatticeConventions.MirrorExpansionsProof.euclidDot_sub_left <;> assumption
theorem euclidDot_smul_left (t : ℝ) (u x : Point) : euclidDot (t • u) x = t * euclidDot u x := by apply _root_.YangMills.Construction.LatticeConventions.ObservableRules.euclidDot_smul_left <;> assumption
theorem euclidDot_neg_left (u x : Point) : euclidDot (-u) x = -euclidDot u x := by
  simp [euclidDot, Finset.sum_neg_distrib]
theorem euclidDot_neg_right (u x : Point) : euclidDot u (-x) = -euclidDot u x := by
  simp [euclidDot, Finset.sum_neg_distrib]
theorem euclidDot_self_of_axial {u : Point} (h : IsAxialNormal u) : euclidDot u u = 1 := by
  obtain ⟨μ, rfl⟩ := h
  rw [euclidDot_basisVector]
  simp [basisVector]
theorem euclidDot_self_of_faceDiagonal {u : Point} (h : IsFaceDiagonalNormal u) :
    euclidDot u u = 2 := by
  obtain ⟨μ, lam, hne, rfl | rfl⟩ := h
  · rw [euclidDot_add_left, euclidDot_basisVector, euclidDot_basisVector]
    simp [basisVector, hne, hne.symm]
    norm_num
  · rw [euclidDot_sub_left, euclidDot_basisVector, euclidDot_basisVector]
    simp [basisVector, hne, hne.symm]
    norm_num
theorem realNormal_valid (F : ReflectionClass) :
    IsAxialNormal F.realNormal ∨ IsFaceDiagonalNormal F.realNormal := by
  cases F with
  | axial μ => exact Or.inl ⟨μ, ReflectionPositivity.MirrorHyperplanes.realNormal_axial μ⟩
  | diagonal μ ν lt s =>
    rcases Int.units_eq_one_or s with rfl | rfl
    · exact Or.inr ⟨μ, ν, lt.ne,
        Or.inl (ReflectionPositivity.MirrorHyperplanes.realNormal_diagonal_one μ ν lt)⟩
    · exact Or.inr ⟨μ, ν, lt.ne,
        Or.inr (ReflectionPositivity.MirrorHyperplanes.realNormal_diagonal_neg_one μ ν lt)⟩
theorem realNormal_diagonal_eq (μ ν : Direction) (lt : μ < ν) (s : ℤˣ) :
    (ReflectionClass.diagonal μ ν lt s).realNormal =
      basisVector μ + ((s : ℤ) : ℝ) • basisVector ν := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · refine (ReflectionPositivity.MirrorHyperplanes.realNormal_diagonal_one μ ν lt).trans ?_
    simp [basisVector]
  · refine (ReflectionPositivity.MirrorHyperplanes.realNormal_diagonal_neg_one μ ν lt).trans ?_
    simp [basisVector, sub_eq_add_neg]
theorem isFaceDiagonalNormal_add_smul {μ lam : Direction} (h : μ ≠ lam) (s : ℤˣ) :
    IsFaceDiagonalNormal (basisVector μ + ((s : ℤ) : ℝ) • basisVector lam) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact ⟨μ, lam, h, Or.inl (by simp)⟩
  · exact ⟨μ, lam, h, Or.inr (by simp [sub_eq_add_neg])⟩
theorem realNormal_diagonalClassOfPair (μ lam : Direction) (h : μ ≠ lam) (s : ℤˣ) :
    (diagonalClassOfPair μ lam h s).realNormal = basisVector μ + ((s : ℤ) : ℝ) • basisVector lam ∨
      (diagonalClassOfPair μ lam h s).realNormal =
        -(basisVector μ + ((s : ℤ) : ℝ) • basisVector lam) := by
  unfold diagonalClassOfPair
  split_ifs with hlt
  · exact Or.inl (realNormal_diagonal_eq _ _ _ _)
  · rw [realNormal_diagonal_eq]
    rcases Int.units_eq_one_or s with rfl | rfl
    · left
      simp [add_comm]
    · right
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_smul, one_smul]
      abel
def PairAgrees (F : ReflectionClass) (c : ℝ) (Q : NormalHyperplane) : Prop :=
  (F.realNormal = Q.normal ∧ c = Q.level) ∨ (F.realNormal = -Q.normal ∧ c = -Q.level)
theorem PairAgrees.normal {F : ReflectionClass} {c : ℝ} {Q : NormalHyperplane}
    (h : PairAgrees F c Q) : F.realNormal = Q.normal ∨ F.realNormal = -Q.normal :=
  h.imp (·.1) (·.1)
theorem PairAgrees.euclidDot_self {F : ReflectionClass} {c : ℝ} {Q : NormalHyperplane}
    (h : PairAgrees F c Q) : euclidDot F.realNormal F.realNormal = euclidDot Q.normal Q.normal := by
  rcases h.normal with h | h
  · rw [h]
  · rw [h, euclidDot_neg_left, euclidDot_neg_right, neg_neg]
theorem isAdmissibleLevel_of_pairAgrees {a : ℝ} {F : ReflectionClass} {c : ℝ}
    {Q : NormalHyperplane} (hQ : Q.IsLatticeMirror a) (h : PairAgrees F c Q) :
    F.IsAdmissibleLevel a c := by
  have hd := h.euclidDot_self
  have hc : c = Q.level ∨ c = -Q.level := h.imp (·.2) (·.2)
  cases F with
  | axial μ =>
    have h1 : euclidDot (ReflectionClass.axial μ).realNormal (ReflectionClass.axial μ).realNormal =
        1 := ReflectionClass.realNormal_dot_axial μ
    have haxial : IsAxialNormal Q.normal := by
      rcases Q.normal_valid with h2 | h2
      · exact h2
      · have h3 := euclidDot_self_of_faceDiagonal h2
        linarith
    obtain ⟨q, hq⟩ := hQ.1 haxial
    rcases hc with rfl | rfl
    · exact ⟨q, hq⟩
    · exact ⟨-q, by rw [hq]; push_cast; ring⟩
  | diagonal μ ν lt s =>
    have h1 : euclidDot (ReflectionClass.diagonal μ ν lt s).realNormal
        (ReflectionClass.diagonal μ ν lt s).realNormal = 2 :=
      ReflectionClass.realNormal_dot_diagonal μ ν lt s
    have hdiag : IsFaceDiagonalNormal Q.normal := by
      rcases Q.normal_valid with h2 | h2
      · have h3 := euclidDot_self_of_axial h2
        linarith
      · exact h2
    obtain ⟨q, hq⟩ := hQ.2 hdiag
    rcases hc with rfl | rfl
    · exact ⟨q, hq⟩
    · exact ⟨-q, by rw [hq]; push_cast; ring⟩
theorem isLatticeMirror_of_pairAgrees {a : ℝ} {F : ReflectionClass} {c : ℝ}
    {Q : NormalHyperplane} (hc : F.IsAdmissibleLevel a c) (h : PairAgrees F c Q) :
    Q.IsLatticeMirror a := by
  have hd := h.euclidDot_self
  have hpos : Q.level = c ∨ Q.level = -c := by
    rcases h with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, neg_neg])
  cases F with
  | axial μ =>
    have h1 : euclidDot (ReflectionClass.axial μ).realNormal (ReflectionClass.axial μ).realNormal =
        1 := ReflectionClass.realNormal_dot_axial μ
    obtain ⟨q, hq⟩ := hc
    refine ⟨fun _ => ?_, fun h2 => ?_⟩
    · rcases hpos with hp | hp
      · exact ⟨q, hp.trans hq⟩
      · exact ⟨-q, by rw [hp, hq]; push_cast; ring⟩
    · have h3 := euclidDot_self_of_faceDiagonal h2
      linarith
  | diagonal μ ν lt s =>
    have h1 : euclidDot (ReflectionClass.diagonal μ ν lt s).realNormal
        (ReflectionClass.diagonal μ ν lt s).realNormal = 2 :=
      ReflectionClass.realNormal_dot_diagonal μ ν lt s
    obtain ⟨q, hq⟩ := hc
    refine ⟨fun h2 => ?_, fun _ => ?_⟩
    · have h3 := euclidDot_self_of_axial h2
      linarith
    · rcases hpos with hp | hp
      · exact ⟨q, hp.trans hq⟩
      · exact ⟨-q, by rw [hp, hq]; push_cast; ring⟩
theorem plane_eq_of_pairAgrees {a : ℝ} {M : LatticeMirror a} {Q : NormalHyperplane}
    (h : PairAgrees M.cls M.level Q) : M.plane = Q.carrier := by
  ext x
  change M.cls.realNormal ⬝ᵥ x = M.level ↔ euclidDot Q.normal x = Q.level
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    rfl
  · rw [h1, h2, neg_dotProduct, neg_inj]
    rfl
theorem pairAgrees_of_plane_eq {a : ℝ} {M : LatticeMirror a} {Q : NormalHyperplane}
    (hQ : Q.IsLatticeMirror a) (h : M.plane = Q.carrier) : PairAgrees M.cls M.level Q := by
  obtain ⟨P, hn, ho, hp⟩ := ReflectionPositivity.MirrorHyperplanes.exists_of_latticeMirror M
  have hpts : (toMirrorPair hQ).hyperplane = P.hyperplane := by
    rw [hp, h]
    rfl
  rcases (toMirrorPair hQ).eq_or_eq_neg_of_hyperplane_eq P hpts with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hn.symm.trans h1, ho.symm.trans h2⟩
  · exact Or.inr ⟨hn.symm.trans h1, ho.symm.trans h2⟩
theorem exists_latticeMirror_of_normal {a : ℝ} (F : ReflectionClass) (Q : NormalHyperplane)
    (hQ : Q.IsLatticeMirror a) (hn : F.realNormal = Q.normal ∨ F.realNormal = -Q.normal) :
    ∃ M : LatticeMirror a, M.cls = F ∧ PairAgrees M.cls M.level Q := by
  rcases hn with hn | hn
  · have h : PairAgrees F Q.level Q := Or.inl ⟨hn, rfl⟩
    exact ⟨⟨F, _, isAdmissibleLevel_of_pairAgrees hQ h⟩, rfl, h⟩
  · have h : PairAgrees F (-Q.level) Q := Or.inr ⟨hn, rfl⟩
    exact ⟨⟨F, _, isAdmissibleLevel_of_pairAgrees hQ h⟩, rfl, h⟩
theorem exists_normalHyperplane_of_latticeMirror {a : ℝ} (M : LatticeMirror a) (u : Point)
    (hmem : IsAxialNormal u ∨ IsFaceDiagonalNormal u)
    (hn : M.cls.realNormal = u ∨ M.cls.realNormal = -u) :
    ∃ Q : NormalHyperplane, Q.normal = u ∧ PairAgrees M.cls M.level Q := by
  rcases hn with hn | hn
  · exact ⟨⟨u, M.level, hmem⟩, rfl, Or.inl ⟨hn, rfl⟩⟩
  · exact ⟨⟨u, -M.level, hmem⟩, rfl, Or.inr ⟨hn, (neg_neg _).symm⟩⟩
theorem carrier_image_eq_plane_image (a : ℝ) (F : ReflectionClass) (u : Point)
    (hmem : IsAxialNormal u ∨ IsFaceDiagonalNormal u)
    (hn : F.realNormal = u ∨ F.realNormal = -u) :
    NormalHyperplane.carrier '' NormalHyperplane.mirrorsWithNormal a u =
      (fun M : LatticeMirror a => M.plane) '' ReflectionClass.mirrors a F := by
  ext P
  constructor
  · rintro ⟨Q, ⟨hQn, hQ⟩, rfl⟩
    subst hQn
    obtain ⟨M, hM, h⟩ := exists_latticeMirror_of_normal F Q hQ hn
    exact ⟨M, hM, plane_eq_of_pairAgrees h⟩
  · rintro ⟨M, hM, rfl⟩
    have hM' : M.cls = F := hM
    subst hM'
    obtain ⟨Q, hQn, h⟩ := exists_normalHyperplane_of_latticeMirror M u hmem hn
    exact ⟨Q, ⟨hQn, isLatticeMirror_of_pairAgrees M.level_mem h⟩, (plane_eq_of_pairAgrees h).symm⟩
theorem carrier_of_axial {Q : NormalHyperplane} {μ : Direction}
    (hn : Q.normal = basisVector μ) : Q.carrier = {x | x μ = Q.level} := by
  ext x
  change euclidDot Q.normal x = Q.level ↔ x μ = Q.level
  rw [hn, euclidDot_basisVector]
theorem carrier_of_diagonal {Q : NormalHyperplane} {μ lam : Direction} {s : ℤˣ}
    (hn : Q.normal = basisVector μ + ((s : ℤ) : ℝ) • basisVector lam) :
    Q.carrier = {x | x μ + ((s : ℤ) : ℝ) * x lam = Q.level} := by
  ext x
  change euclidDot Q.normal x = Q.level ↔ x μ + ((s : ℤ) : ℝ) * x lam = Q.level
  rw [hn, euclidDot_add_left, euclidDot_smul_left, euclidDot_basisVector, euclidDot_basisVector]
theorem mirrorPlanes_part (a : ℝ) : MirrorPlanesEqLatticeMirrorCarriers a := by
  intro P
  constructor
  · rintro ⟨M, rfl⟩
    have h : PairAgrees M.cls M.level ⟨M.cls.realNormal, M.level, realNormal_valid _⟩ :=
      Or.inl ⟨rfl, rfl⟩
    exact ⟨_, isLatticeMirror_of_pairAgrees M.level_mem h, (plane_eq_of_pairAgrees h).symm⟩
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨M, hM, -⟩ := (toMirrorPair hQ).exists_latticeMirror_eq
    exact ⟨M, hM⟩
theorem axialMirror_part (a : ℝ) : AxialNormalMirror a := by
  intro μ Q hQ hn
  refine ⟨carrier_of_axial hn, ?_⟩
  have h : PairAgrees (ReflectionClass.axial μ) Q.level Q :=
    Or.inl ⟨(ReflectionPositivity.MirrorHyperplanes.realNormal_axial μ).trans hn.symm, rfl⟩
  refine ⟨⟨.axial μ, Q.level, isAdmissibleLevel_of_pairAgrees hQ h⟩, rfl, rfl,
    plane_eq_of_pairAgrees h, ?_, ?_⟩
  · constructor
    · rintro ⟨q, hq⟩
      exact ⟨hQ, ⟨μ, hn⟩, q, hq⟩
    · rintro ⟨-, -, q, hq⟩
      exact ⟨q, hq⟩
  · constructor
    · rintro ⟨q, hq⟩
      refine ⟨hQ, ⟨μ, hn⟩, q, ?_⟩
      change Q.level = _ at hq
      rw [hq]
      ring
    · rintro ⟨-, -, q, hq⟩
      refine ⟨q, ?_⟩
      change Q.level = _
      rw [hq]
      ring
theorem axialClass_part (a : ℝ) : AxialNormalClass a := by
  intro μ
  refine ⟨?_, carrier_image_eq_plane_image a (.axial μ) _ (Or.inl ⟨μ, rfl⟩)
    (Or.inl (ReflectionPositivity.MirrorHyperplanes.realNormal_axial μ))⟩
  ext P
  constructor
  · rintro ⟨Q, ⟨hn, hQ⟩, rfl⟩
    obtain ⟨q, hq⟩ := hQ.1 ⟨μ, hn⟩
    exact ⟨Q.level, ⟨q, hq⟩, carrier_of_axial hn⟩
  · rintro ⟨c', hc', rfl⟩
    have h : PairAgrees (ReflectionClass.axial μ) c' (NormalHyperplane.axial μ c') :=
      Or.inl ⟨ReflectionPositivity.MirrorHyperplanes.realNormal_axial μ, rfl⟩
    have hc'' : (ReflectionClass.axial μ).IsAdmissibleLevel a c' := hc'
    exact ⟨_, ⟨rfl, isLatticeMirror_of_pairAgrees hc'' h⟩, carrier_of_axial rfl⟩
theorem diagonalMirror_part (a : ℝ) : DiagonalNormalMirror a := by
  intro μ lam h s Q hQ hn
  refine ⟨carrier_of_diagonal hn, ?_⟩
  obtain ⟨M, hM, hA⟩ := exists_latticeMirror_of_normal (diagonalClassOfPair μ lam h s) Q hQ
    (by rw [hn]; exact realNormal_diagonalClassOfPair μ lam h s)
  exact ⟨M, hM, plane_eq_of_pairAgrees hA⟩
theorem diagonalClass_part (a : ℝ) : DiagonalNormalClass a := by
  intro μ lam h
  refine ⟨fun s => ⟨?_, carrier_image_eq_plane_image a _ _
    (Or.inr (isFaceDiagonalNormal_add_smul h s)) (realNormal_diagonalClassOfPair μ lam h s)⟩, ?_⟩
  · ext P
    constructor
    · rintro ⟨Q, ⟨hn, hQ⟩, rfl⟩
      obtain ⟨q, hq⟩ := hQ.2 (hn ▸ isFaceDiagonalNormal_add_smul h s)
      exact ⟨Q.level, ⟨q, hq⟩, carrier_of_diagonal hn⟩
    · rintro ⟨c', ⟨q, hq⟩, rfl⟩
      have hmem := isFaceDiagonalNormal_add_smul h s
      refine ⟨⟨_, c', Or.inr hmem⟩, ⟨rfl, fun h2 => ?_, fun _ => ⟨q, hq⟩⟩, carrier_of_diagonal rfl⟩
      have h3 := euclidDot_self_of_axial h2
      have h4 := euclidDot_self_of_faceDiagonal hmem
      simp only at h3
      linarith
  · have e : basisVector μ + (((-1 : ℤˣ) : ℤ) : ℝ) • basisVector lam =
        basisVector μ - basisVector lam := by
      simp [sub_eq_add_neg]
    have hn := realNormal_diagonalClassOfPair μ lam h (-1)
    rw [e] at hn
    have e' : basisVector lam - basisVector μ = -(basisVector μ - basisVector lam) := by abel
    rw [carrier_image_eq_plane_image a (diagonalClassOfPair μ lam h (-1)) _
        (Or.inr ⟨μ, lam, h, Or.inr rfl⟩) hn,
      carrier_image_eq_plane_image a (diagonalClassOfPair μ lam h (-1)) _
        (Or.inr ⟨lam, μ, h.symm, Or.inr rfl⟩) (by rw [e', neg_neg]; exact hn.symm)]
theorem symmetry_of_pairAgrees {a : ℝ} {M : LatticeMirror a} {Q : NormalHyperplane}
    (hQ : Q.IsLatticeMirror a) (h : PairAgrees M.cls M.level Q) :
    M.symmetry = reflectSymmetry hQ := by
  apply ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext
  change hyperplaneReflect M.cls.realNormal M.level = Q.reflect
  rw [reflect_eq_hyperplaneReflect]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, ReflectionPositivity.MirrorHyperplanes.hyperplaneReflect_neg]
theorem conjReflect_of_pairAgrees {a : ℝ} {M : LatticeMirror a} {Q : NormalHyperplane}
    (hQ : Q.IsLatticeMirror a) (h : PairAgrees M.cls M.level Q) (F : GaugeField a → ℂ) :
    M.conjReflect F = conjFun ((reflectSymmetry hQ).actOn F) := by
  funext U
  simp only [InfiniteLattice.LatticeMirror.conjReflect, conjFun, symmetry_of_pairAgrees hQ h]
theorem isHalfSpace_iff_of_pairAgrees {a : ℝ} {M : LatticeMirror a} {Q : NormalHyperplane}
    (h : PairAgrees M.cls M.level Q) (H : Set Point) :
    M.IsHalfSpace H ↔ H = Q.upperHalfSpace ∨ H = Q.lowerHalfSpace := by
  unfold InfiniteLattice.LatticeMirror.IsHalfSpace
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    rfl
  · rw [h1, h2]
    simp only [neg_dotProduct, neg_le_neg_iff]
    exact or_comm
theorem reflection_part (a : ℝ) : MirrorReflectionAndHalfSpaces a := by
  intro Q hQ M hM
  have h := pairAgrees_of_plane_eq hQ hM
  refine ⟨?_, fun F _ => conjReflect_of_pairAgrees hQ h F, isHalfSpace_iff_of_pairAgrees h⟩
  rw [symmetry_of_pairAgrees hQ h]
  rfl
section LocalObservables
variable {a : ℝ}
theorem opposite_mem_linksWithin {T : Set Point} {b : Link a} :
    b.opposite ∈ (linksWithin T : Set (Link a)) ↔ b ∈ (linksWithin T : Set (Link a)) :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
open Classical in
def splice (T : Set Point) (U U' : GaugeField a) : GaugeField a :=
  ⟨fun b => if b ∈ (linksWithin T : Set (Link a)) then U b else U' b, fun b => by
    by_cases hb : b ∈ (linksWithin T : Set (Link a))
    · simp only [opposite_mem_linksWithin, hb, if_true]
      exact U.2 b
    · simp only [opposite_mem_linksWithin, hb, if_false]
      exact U'.2 b⟩
theorem splice_of_mem {T : Set Point} {U U' : GaugeField a} {b : Link a}
    (hb : b ∈ (linksWithin T : Set (Link a))) : splice T U U' b = U b :=
  if_pos hb
theorem splice_of_not_mem {T : Set Point} {U U' : GaugeField a} {b : Link a}
    (hb : b ∉ (linksWithin T : Set (Link a))) : splice T U U' b = U' b :=
  if_neg hb
def unitField (a : ℝ) : GaugeField a := ⟨fun _ => 1, fun _ => by simp⟩
theorem eq_of_eqOn_links {S' : Set Point} {F : GaugeField a → ℂ} (hF : IsRegionMeasurable S' F)
    {U U' : GaugeField a} (h : ∀ b ∈ (linksWithin S' : Set (Link a)), U b = U' b) :
    F U = F U' := by
  let m : MeasurableSpace (GaugeField a) :=
    { MeasurableSet' := fun A => (U ∈ A ↔ U' ∈ A)
      measurableSet_empty := by simp
      measurableSet_compl := fun A hA => not_congr hA
      measurableSet_iUnion := fun f hf => by
        simp only [Set.mem_iUnion]
        exact exists_congr hf }
  have hle : regionSigma S' ≤ m := iSup₂_le fun b hb => by
    rintro _ ⟨t, -, rfl⟩
    change (U b ∈ t ↔ U' b ∈ t)
    rw [h b hb]
  have hm : MeasurableSet[regionSigma S'] (F ⁻¹' {F U}) := hF (measurableSet_singleton _)
  have h2 : U ∈ F ⁻¹' {F U} ↔ U' ∈ F ⁻¹' {F U} := hle _ hm
  exact (h2.1 rfl).symm
theorem eq_of_eqOn_links_inter {S Q : Set Point} {F : GaugeField a → ℂ}
    (hS : IsRegionMeasurable S F) (hQ : IsRegionMeasurable Q F) {U U' : GaugeField a}
    (h : ∀ b ∈ (linksWithin (S ∩ Q) : Set (Link a)), U b = U' b) : F U = F U' := by
  have h1 : F (splice S U U') = F U :=
    eq_of_eqOn_links hS fun b hb => splice_of_mem hb
  have h2 : F (splice S U U') = F U' := by
    refine eq_of_eqOn_links hQ fun b hb => ?_
    by_cases hbS : b ∈ (linksWithin S : Set (Link a))
    · rw [splice_of_mem hbS]
      exact h b ⟨⟨hbS.1, hb.1⟩, ⟨hbS.2, hb.2⟩⟩
    · exact splice_of_not_mem hbS
  exact h1.symm.trans h2
theorem measurable_splice_unitField (ha : 0 < a)
    (hspace : InfiniteLattice.GaugeFieldSpace.TopologyStatement) (T : Set Point) :
    Measurable[regionSigma T] fun U : GaugeField a => splice T U (unitField a) := by
  obtain ⟨-, -, -, -, -, hborel⟩ := hspace a ha
  have key : ∀ b : Link a, @Measurable _ _ (regionSigma T)
      (borel Matrices.ComplexMatrix2.specialUnitary)
      (fun U : GaugeField a => splice T U (unitField a) b) := fun b => by
    by_cases hb : b ∈ (linksWithin T : Set (Link a))
    · have h : (fun U : GaugeField a => splice T U (unitField a) b) =
          fun U : GaugeField a => U b := funext fun U => splice_of_mem hb
      rw [h]
      exact Measurable.of_comap_le (le_iSup₂_of_le (f := fun b _ =>
        MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) b hb le_rfl)
    · have h : (fun U : GaugeField a => splice T U (unitField a) b) =
          fun _ : GaugeField a => (1 : Matrices.ComplexMatrix2.specialUnitary) :=
        funext fun U => splice_of_not_mem hb
      rw [h]
      exact @measurable_const _ _ (borel Matrices.ComplexMatrix2.specialUnitary) (regionSigma T) _
  rw [measurable_iff_comap_le]
  have hinst :
      (InfiniteLattice.instMeasurableSpaceGaugeField : MeasurableSpace (GaugeField a)) =
      ⨆ b : Link a, MeasurableSpace.comap (fun U : GaugeField a => U b)
        (borel Matrices.ComplexMatrix2.specialUnitary) :=
    hborel
  rw [hinst, MeasurableSpace.comap_iSup]
  refine iSup_le fun b => ?_
  rw [MeasurableSpace.comap_comp]
  exact (key b).comap_le
theorem regionSigma_inter_le (S Q : Set Point) :
    (regionSigma (S ∩ Q) : MeasurableSpace (GaugeField a)) ≤ regionSigma S :=
  iSup₂_le fun b hb => le_iSup₂_of_le (f := fun b _ =>
    MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) b
    (show b ∈ (linksWithin S : Set (Link a)) from ⟨hb.1.1, hb.2.1⟩) le_rfl
theorem observables_part (ha : 0 < a) (hspace : InfiniteLattice.GaugeFieldSpace.TopologyStatement) :
    LocalRegionObservablesChar a := by
  intro S
  ext F
  constructor
  · intro hF
    obtain ⟨Q, hQ, hobs, hm⟩ : ∃ Q, Bornology.IsBounded Q ∧
        F ∈ boundedRegionObservables a (S ∩ Q) := by
      simpa [localRegionObservables] using hF
    exact ⟨hobs, ⟨S ∩ Q, hQ.subset Set.inter_subset_right, hm⟩,
      hm.mono (regionSigma_inter_le S Q) le_rfl⟩
  · rintro ⟨hobs, ⟨Q, hQ, hmQ⟩, hmS⟩
    refine Set.mem_iUnion₂.2 ⟨Q, hQ, hobs, ?_⟩
    have hflat : F = fun U => F (splice (S ∩ Q) U (unitField a)) := funext fun U =>
      eq_of_eqOn_links_inter hmS hmQ fun b hb => (splice_of_mem hb).symm
    change Measurable[regionSigma (S ∩ Q)] F
    rw [hflat]
    exact hobs.1.comp (measurable_splice_unitField ha hspace (S ∩ Q))
end LocalObservables
theorem positivity_part (a : Spacing)
    (hside : MirrorSideIndependence.Statement)
    (hspace : InfiniteLattice.GaugeFieldSpace.TopologyStatement) :
    OneSidedPositivityIffReflectionPositive (a : ℝ) := by
  intro Q hQ M hM H hH ν _
  have hA := pairAgrees_of_plane_eq hQ hM
  have hint : ∀ F : GaugeField (a : ℝ) → ℂ,
      ∫ U, F U * M.conjReflect F U ∂ν = reflectedPairing hQ ν F := fun F => by
    rw [conjReflect_of_pairAgrees hQ hA F]
    exact integral_congr_ae (Filter.Eventually.of_forall fun U => mul_comm _ _)
  have hL : (∀ F : GaugeField (a : ℝ) → ℂ, IsBoundedObservable F → IsLocalObservable F →
        IsRegionMeasurable H F → 0 ≤ ∫ U, F U * M.conjReflect F U ∂ν) ↔
      ∀ F ∈ localRegionObservables (a : ℝ) H,
        (reflectedPairing hQ ν F).im = 0 ∧ 0 ≤ (reflectedPairing hQ ν F).re := by
    rw [observables_part a.2 hspace H]
    constructor
    · rintro h F ⟨h1, h2, h3⟩
      have h4 := h F h1 h2 h3
      rw [hint, Complex.le_def] at h4
      exact ⟨h4.2.symm, h4.1⟩
    · intro h F h1 h2 h3
      obtain ⟨h4, h5⟩ := h F ⟨h1, h2, h3⟩
      rw [hint, Complex.le_def]
      exact ⟨h5, h4.symm⟩
  rw [hL]
  rcases hH with rfl | rfl
  · exact ⟨fun h F => h F.1 F.2, fun h F hF => h ⟨F, hF⟩⟩
  · exact (((hside a).1 Q hQ).2 ν).2.symm
theorem formulations_at_mirror (a : Spacing)
    (hc : OneSidedPositivityIffReflectionPositive (a : ℝ))
    (Q : NormalHyperplane) (hQ : Q.IsLatticeMirror (a : ℝ)) (M : LatticeMirror (a : ℝ))
    (hM : M.plane = Q.carrier) (ν : Measure (GaugeField (a : ℝ)))
    [IsProbabilityMeasure ν] : IsReflectionPositiveAt ν M ↔ IsReflectionPositiveAcrossMirror hQ ν := by
  have hA := pairAgrees_of_plane_eq hQ hM
  constructor
  · rintro ⟨-, h⟩
    exact (hc Q hQ M hM _ (Or.inl rfl) ν).1
      (h _ ((isHalfSpace_iff_of_pairAgrees hA _).2 (Or.inl rfl)))
  · intro h
    exact ⟨inferInstance, fun H hH =>
      (hc Q hQ M hM H ((isHalfSpace_iff_of_pairAgrees hA H).1 hH) ν).2 h⟩
theorem formulations_part (a : Spacing)
    (hc : OneSidedPositivityIffReflectionPositive (a : ℝ)) :
    ReflectionPositivityFormulationsAgree (a : ℝ) := by
  intro Q hQ M hM ν _
  have hA := pairAgrees_of_plane_eq hQ hM
  refine ⟨formulations_at_mirror a hc Q hQ M hM ν, ?_, ?_⟩
  · intro hfam Q' hQ'
    obtain ⟨hn, hlat⟩ := hQ'
    obtain ⟨M', hfam', hA'⟩ := exists_latticeMirror_of_normal M.cls Q' hlat (by
      rw [hn]
      exact hA.normal)
    exact (formulations_at_mirror a hc Q' hlat M' (plane_eq_of_pairAgrees hA') ν).1 (hfam M' hfam')
  · intro hfam M' hM'
    have hM'' : M'.cls = M.cls := hM'
    obtain ⟨Q', hn, hA'⟩ := exists_normalHyperplane_of_latticeMirror M' Q.normal Q.normal_valid (by
      rw [hM'']
      exact hA.normal)
    have hlat : Q'.IsLatticeMirror (a : ℝ) := isLatticeMirror_of_pairAgrees M'.level_mem hA'
    exact (formulations_at_mirror a hc Q' hlat M' (plane_eq_of_pairAgrees hA') ν).2
      (hfam Q' ⟨hn, hlat⟩)
theorem statement_holds (hside : MirrorSideIndependence.Statement)
    (hspace : InfiniteLattice.GaugeFieldSpace.TopologyStatement) : Statement := fun a =>
  ⟨mirrorPlanes_part _, axialMirror_part _, axialClass_part _, diagonalMirror_part _,
    diagonalClass_part _, reflection_part _, observables_part a.2 hspace,
    positivity_part a hside hspace,
    formulations_part a (positivity_part a hside hspace)⟩
end LatticeMirrorsAndReflectionPositivity
end YangMills.Construction.LatticeConventions
end
