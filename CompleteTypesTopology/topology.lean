import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Types
import Mathlib.ModelTheory.Equivalence
import Mathlib.Data.Fin.Basic
import Mathlib.Topology.Separation.Regular
import CompleteTypesTopology.general
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Set.Operations
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Topology.Instances.CantorSet
import Mathlib.SetTheory.Cardinal.Order

namespace CompleteTypesTopology
open FirstOrder

def basis_set {L : Language} {n : ℕ} (T : L.Theory) (φ : (L.withConstants (Fin n)).Sentence) :
  Set (T.CompleteType (Fin n)) := {p | φ ∈ p}

instance {L : Language} {T : L.Theory} {n : ℕ} : TopologicalSpace (T.CompleteType (Fin n)) :=
  TopologicalSpace.generateFrom
  {S | ∃φ, S = basis_set T φ}

lemma basis_set_intersection {L : Language} {n : ℕ} {T : L.Theory}
                            (φ ψ : (L.withConstants (Fin n)).Sentence) :
  basis_set T φ ∩ basis_set T ψ = basis_set T (φ ⊓ ψ) := by
  ext p
  unfold basis_set
  constructor
  · intro ⟨h1,h2⟩
    apply (FirstOrder.Language.Theory.IsMaximal.mem_iff_models p.isMaximal (φ ⊓ ψ)).mpr
    apply (FirstOrder.Language.Theory.IsMaximal.mem_iff_models p.isMaximal φ).mp at h1
    apply (FirstOrder.Language.Theory.IsMaximal.mem_iff_models p.isMaximal ψ).mp at h2
    exact
      Language.Theory.models_sentence_iff.mpr fun M a ↦
        a (h1 M default default) (h2 M default default)
  · simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    intro h
    apply (FirstOrder.Language.Theory.IsMaximal.mem_iff_models p.isMaximal (φ ⊓ ψ)).mp at h
    constructor
    · apply (FirstOrder.Language.Theory.IsMaximal.mem_iff_models p.isMaximal φ).mpr
      intro M a a2
      specialize h M a a2
      exact (Language.BoundedFormula.realize_inf.mp h).left
    · apply (FirstOrder.Language.Theory.IsMaximal.mem_iff_models p.isMaximal ψ).mpr
      intro M a a2
      specialize h M a a2
      exact (Language.BoundedFormula.realize_inf.mp h).right

lemma isBasis {L : Language} {T : L.Theory} {n : ℕ} :
  TopologicalSpace.IsTopologicalBasis {S : Set (T.CompleteType (Fin n)) | ∃φ, S = basis_set T φ}
  := by
  constructor
  · intro b1 h1 b2 h2 x hx
    obtain ⟨φ, hφ⟩ := h1
    obtain ⟨ψ, hψ⟩ := h2
    use basis_set T (φ ⊓ ψ)
    simp only [Set.mem_setOf_eq, exists_apply_eq_apply', Set.subset_inter_iff, true_and]
    constructor
    · rw [← basis_set_intersection φ ψ, ← hφ, ← hψ]
      exact hx
    · rw [← basis_set_intersection, ← hφ, ← hψ]
      grind
  · ext p
    constructor
    · intro h
      exact Set.mem_univ p
    · intro h
      simp only [Set.mem_sUnion, Set.mem_setOf_eq, ↓existsAndEq, true_and]
      use ⊤
      unfold basis_set
      rw [Set.mem_setOf_eq]
      exact Language.Theory.CompleteType.mem_of_models p fun M v xs a ↦ a
  · rfl

lemma basis_set_open {L : Language} (T : L.Theory) {n : ℕ}
                      (φ : (L.withConstants (Fin n)).Sentence) :
  IsOpen (basis_set T φ) := by
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  simp

lemma basis_set_closed {L : Language} (T : L.Theory) {n : ℕ}
                      (φ : (L.withConstants (Fin n)).Sentence) :
  IsClosed (basis_set T φ) := by
  rw [← isOpen_compl_iff]
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  use φ.not
  unfold basis_set
  exact Language.Theory.CompleteType.compl_setOf_mem

lemma basis_set_complement {L : Language} (T : L.Theory) {n : ℕ}
                      (φ : (L.withConstants (Fin n)).Sentence) :
  (basis_set T φ)ᶜ = basis_set T φ.not := by
  unfold basis_set
  exact FirstOrder.Language.Theory.CompleteType.compl_setOf_mem

instance {L : Language} {T : L.Theory} {n : ℕ} : T2Space (T.CompleteType (Fin n)) where
  t2 := by
    intro x y h
    obtain ⟨a, ha1, ha2⟩ := neq_element T h
    use basis_set T a
    use (basis_set T a)ᶜ
    exact ⟨by exact basis_set_open T a, by rw [isOpen_compl_iff]; exact basis_set_closed T a,
          by assumption, by assumption, by grind⟩

instance {L : Language} {T : L.Theory} {n : ℕ} : CompactSpace (T.CompleteType (Fin n)) where
  isCompact_univ := by
    intro f h1f h2f
    let s : (L.withConstants (Fin n)).Theory :=
      {φ : (L.withConstants (Fin n)).Sentence | basis_set T φ ∈ f}
    have h1 : s.IsSatisfiable := by
      rw [FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable]
      intro T0 hT0
      have h'1 : ⋂ φ ∈ T0, (basis_set T φ) ∈ f := by
        rw [Finset.iInter_mem_sets]
        intro i hi
        apply Filter.mem_of_superset (hT0 hi)
        trivial
      have h'2 : ∃ (p : T.CompleteType (Fin n)), SetLike.coe T0 ⊆ p.toTheory := by
        let s1 := ⋂ φ ∈ T0, basis_set T φ
        have hs1 : ∅ ∉ f := by exact Filter.empty_notMem f
        have hs2 : Nonempty s1 := by
          by_contra
          push_neg at this
          simp at this
          grind
        unfold basis_set at h'1
        rw [nonempty_subtype] at hs2
        have hs3 : ∀ p ∈ s1, SetLike.coe T0 ⊆ p.toTheory := by
          intro p hp a ha
          unfold s1 at hp
          simp only [Set.mem_iInter] at hp
          unfold basis_set at hp
          exact hp a ha
        let s1' := Classical.choose hs2
        use s1'
        grind
      obtain ⟨p, hp⟩ := h'2
      obtain ⟨h2p, _⟩ := p.isMaximal
      exact Language.Theory.IsSatisfiable.mono h2p hp
    have h2 : (L.lhomWithConstants (Fin n)).onTheory T ⊆ s := by
      intro φ hφ
      unfold s
      rw [Set.mem_setOf_eq]
      have h2' : basis_set T φ = (Set.univ : Set (T.CompleteType (Fin n))) := by
        ext k
        constructor
        · intro kh
          grind
        · intro kh
          unfold basis_set
          rw [Set.mem_setOf_eq]
          exact k.subset' hφ
      rw [h2']
      exact Filter.univ_mem
    obtain ⟨p, hp⟩ := extend_partial_type T s h1 h2
    use p
    constructor
    · trivial
    · rw [clusterPt_iff_nonempty]
      intro u hu v hv
      by_contra h
      push_neg at h
      rw [TopologicalSpace.IsTopologicalBasis.mem_nhds_iff isBasis] at hu
      obtain ⟨t, h1u, h2u, h3u⟩ := hu
      obtain ⟨φ, hφ⟩ := h1u
      have h3 : φ ∈ p := by
        rw [hφ] at h2u
        unfold basis_set at h2u
        simp at h2u
        assumption
      have h4 : v ⊆ basis_set T φ.not := by
        rw [← basis_set_complement]
        rw [Set.subset_compl_iff_disjoint_right]
        rw [Set.disjoint_iff_inter_eq_empty]
        grind
      have h5 : φ.not ∈ p := by
        suffices φ.not ∈ s by exact hp this
        unfold s
        rw [Set.mem_setOf_eq]
        exact f.sets_of_superset hv h4
      rw [FirstOrder.Language.Theory.CompleteType.not_mem_iff] at h5
      contradiction

instance {L : Language} {T : L.Theory} {n : ℕ} [h : Countable L.Symbols] :
  SecondCountableTopology (T.CompleteType (Fin n)) where
  is_open_generated_countable := by
    let B := {S : Set (T.CompleteType (Fin n)) | ∃φ, S = basis_set T φ}
    use B
    constructor
    · let f := fun (φ : (L.withConstants (Fin n)).Sentence) ↦ basis_set T φ
      have h1 : B = Set.range f := by grind
      rw [h1]
      have h2 : Countable (L.withConstants (Fin n)).Symbols := by
        rw [← Cardinal.mk_le_aleph0_iff]
        suffices (L.withConstants (Fin n)).card ≤ Cardinal.aleph0 by trivial
        rw [FirstOrder.Language.card_withConstants]
        simp only [Cardinal.lift_uzero, Cardinal.mk_fintype, Fintype.card_fin,
          Cardinal.lift_natCast, Cardinal.add_le_aleph0]
        constructor
        · suffices Cardinal.mk L.Symbols ≤ Cardinal.aleph0 by trivial
          rw [Cardinal.mk_le_aleph0_iff]
          assumption
        · exact Cardinal.ofENat_le_aleph0 n
      have h3 : Countable (L.withConstants (Fin n)).Sentence := by
        exact formulas_countable (by exact Subsingleton.to_countable) h2
      exact Set.countable_range f
    · rfl

instance {L : Language} {T : L.Theory} {n : ℕ} [h : Countable L.Symbols] :
  TopologicalSpace.MetrizableSpace (T.CompleteType (Fin n)) :=
  TopologicalSpace.metrizableSpace_of_t3_secondCountable (T.CompleteType (Fin n))

instance {L : Language} {T : L.Theory} {n : ℕ} [h : Countable L.Symbols] :
  TopologicalSpace.IsCompletelyMetrizableSpace (T.CompleteType (Fin n)) where
  complete := by
    let m := TopologicalSpace.metrizableSpaceMetric (T.CompleteType (Fin n))
    use m
    constructor
    · trivial
    · exact complete_of_compact

theorem countable_language_card {L : Language} (T : L.Theory) (n : ℕ) [h : Countable L.Symbols] :
  Cardinal.mk (T.CompleteType (Fin n)) ≤ Cardinal.aleph0 ∨
  Cardinal.mk (T.CompleteType (Fin n)) = Cardinal.continuum := by
  by_cases h1 : Countable (T.CompleteType (Fin n))
  · left
    exact Cardinal.mk_le_aleph0_iff.mpr h1
  · right
    push_neg at h1
    rw [le_antisymm_iff]
    constructor
    · obtain ⟨f,_,hf⟩ := PolishSpace.exists_nat_nat_continuous_surjective (T.CompleteType (Fin n))
      obtain ⟨g,hg⟩ := Function.Surjective.hasRightInverse hf
      let h2 : Nonempty (T.CompleteType (Fin n) ↪ (ℕ → ℕ)) := ⟨g,Function.RightInverse.injective hg⟩
      rw [← Cardinal.lift_mk_le'] at h2
      simp only [Cardinal.lift_uzero, Cardinal.mk_pi, Cardinal.mk_eq_aleph0, Cardinal.prod_const,
                  Cardinal.aleph0_power_aleph0, Cardinal.lift_continuum] at h2
      exact h2
    · let s := (Set.univ : Set (T.CompleteType (Fin n)))
      have h2 : IsClosed s := by exact isClosed_univ
      have h3 : ¬s.Countable := by exact Set.not_countable_univ_iff.mpr h1
      obtain ⟨f,_,_,hf⟩ := IsClosed.exists_nat_bool_injection_of_not_countable h2 h3
      let h4 : Nonempty ((ℕ → Bool) ↪ T.CompleteType (Fin n)) := ⟨f,hf⟩
      rw [← Cardinal.lift_mk_le'] at h4
      simp only [Cardinal.mk_pi, Cardinal.mk_fintype, Fintype.card_bool, Nat.cast_ofNat,
          Cardinal.prod_const, Cardinal.mk_eq_aleph0, Cardinal.two_power_aleph0,
          Cardinal.lift_continuum, Cardinal.lift_uzero] at h4
      exact h4

example {L : Language} {T : L.Theory} {n : ℕ}
        [h : Countable L.Symbols] (h1 : Uncountable (T.CompleteType (Fin n))) :
  Cardinal.mk (T.CompleteType (Fin n)) = Cardinal.continuum := by
  have h2 := countable_language_card T n
  rcases h2
  · rw [← Cardinal.aleph0_lt_mk_iff] at h1
    grind
  · assumption

end CompleteTypesTopology
