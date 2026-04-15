/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Axiom Verification

This file verifies that the main theorems of the project use only the expected
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).
No unexpected axioms (such as `sorry`) should appear.
-/

import ModalLogic.Metatheory.Overview
import ModalLogic.Semantics.Overview
import ModalLogic.Semantics.FMPDecidabilityAll
import ModalLogic.Semantics.FMPEuclidean
import ModalLogic.Semantics.FMPCluster
import ModalLogic.Cube

/-!
# Axiom Audit

Running `#print axioms` on each main theorem to confirm no `sorry` or
other unexpected axioms are used.

Expected axioms:
- `propext` (propositional extensionality)
- `Classical.choice` (axiom of choice, used in Lindenbaum's lemma)
- `Quot.sound` (quotient soundness)
-/

/-! ## Single-Agent Modal Logic -/

section Soundness

#print axioms Modal.soundness
#print axioms Modal.TSoundness
#print axioms Modal.S4Soundness
#print axioms Modal.S5Soundness
#print axioms Modal.KDSoundness
#print axioms Modal.KBSoundness
#print axioms Modal.K4Soundness
#print axioms Modal.KTBSoundness
#print axioms Modal.KB4Soundness

#print axioms Modal.K5Soundness
#print axioms Modal.KD5Soundness
#print axioms Modal.KD45Soundness

end Soundness

section Completeness

#print axioms completeness_K
#print axioms completeness_T
#print axioms completeness_S4
#print axioms completeness_S5
#print axioms completeness_KD
#print axioms completeness_KB
#print axioms completeness_K4
#print axioms completeness_KTB
#print axioms completeness_KB4
#print axioms completeness_K5

end Completeness

section Definability

#print axioms BasicModal.refDef
#print axioms BasicModal.symmDef
#print axioms BasicModal.transDef
#print axioms BasicModal.euclidDef
#print axioms BasicModal.serialDef
#print axioms BasicModal.equivRefEuclid

end Definability

section FrameHierarchy

#print axioms Modal.frameClassHierarchy
#print axioms Modal.T_included_in_S4
#print axioms Modal.T_included_in_S5
#print axioms Modal.S4_included_in_S5

#print axioms Modal.equivClass_sub_refSymmClass
#print axioms Modal.equivClass_sub_symmTransClass
#print axioms Modal.equivClass_sub_refTransClass
#print axioms Modal.refSymmClass_sub_refClass
#print axioms Modal.refSymmClass_sub_symmClass
#print axioms Modal.refTransClass_sub_refClass
#print axioms Modal.refTransClass_sub_transClass
#print axioms Modal.symmTransClass_sub_symmClass
#print axioms Modal.symmTransClass_sub_transClass
#print axioms Modal.equivClass_eq_refSymmTrans
#print axioms Modal.ProofK_monotone
#print axioms Modal.refClass_sub_serialClass
#print axioms Modal.equivClass_sub_euclidClass
#print axioms Modal.equivClass_eq_refEuclidClass
#print axioms Modal.T_implies_D
#print axioms Modal.S5_eq_T_union_5

end FrameHierarchy

section LocalConsequence

#print axioms Modal.localSemCsq_implies_globalSemCsq
#print axioms Modal.localSemCsq_empty_iff_globalSemCsq_empty
#print axioms Modal.global_nec_example
#print axioms Modal.local_nec_counterexample
#print axioms Modal.local_global_gap
#print axioms Modal.local_soundness

end LocalConsequence

section FiniteModelProperty

#print axioms Modal.finite_model_property
#print axioms Modal.filtration_lemma

end FiniteModelProperty

section Decidability

#print axioms Modal.kValid_iff_not_satisfiable_neg
#print axioms Modal.satisfiable_iff_finSatisfiable
#print axioms Modal.forces_eq_of_vars_eq
#print axioms Modal.satisfiable_implies_bounded
#print axioms Modal.kValid_iff_no_bounded_countermodel
#print axioms Modal.decidable_kValid
#print axioms Modal.bForces_iff_forces

end Decidability

section DecidabilityMore

#print axioms Modal.filtration_preserves_reflexivity
#print axioms Modal.filtration_preserves_seriality
#print axioms Modal.filtration_preserves_symmetry
#print axioms Modal.fmp_T
#print axioms Modal.fmp_KD
#print axioms Modal.fmp_KB
#print axioms Modal.fmp_S5
#print axioms Modal.forces_subtype
#print axioms Modal.filtrationFrame_card_le
#print axioms Modal.finite_model_to_fin_ref
#print axioms Modal.finite_model_to_fin_serial
#print axioms Modal.finite_model_to_fin_symm
#print axioms Modal.finite_model_to_fin_equiv
#print axioms Modal.tValid_iff_no_bounded_countermodel
#print axioms Modal.kdValid_iff_no_bounded_countermodel
#print axioms Modal.kbValid_iff_no_bounded_countermodel
#print axioms Modal.s5Valid_iff_no_bounded_countermodel
#print axioms Modal.decidable_tValid
#print axioms Modal.decidable_kdValid
#print axioms Modal.decidable_kbValid
#print axioms Modal.decidable_s5Valid

end DecidabilityMore

section FMPDecidabilityAll

#print axioms Modal.transFiltration_lemma
#print axioms Modal.transFiltration_transitive
#print axioms Modal.transFiltration_reflexive
#print axioms Modal.transFiltration_serial
#print axioms Modal.transFiltration_symmetric
#print axioms Modal.fmp_K4
#print axioms Modal.fmp_S4
#print axioms Modal.fmp_KD4
#print axioms Modal.fmp_KTB
#print axioms Modal.fmp_KDB
#print axioms Modal.fmp_KB4
#print axioms Modal.fmp_KB5
#print axioms Modal.k4Valid_iff_no_bounded_countermodel
#print axioms Modal.s4Valid_iff_no_bounded_countermodel
#print axioms Modal.kd4Valid_iff_no_bounded_countermodel
#print axioms Modal.ktbValid_iff_no_bounded_countermodel
#print axioms Modal.kdbValid_iff_no_bounded_countermodel
#print axioms Modal.kb4Valid_iff_no_bounded_countermodel
#print axioms Modal.kb5Valid_iff_no_bounded_countermodel
#print axioms Modal.decidable_k4Valid
#print axioms Modal.decidable_s4Valid
#print axioms Modal.decidable_kd4Valid
#print axioms Modal.decidable_ktbValid
#print axioms Modal.decidable_kdbValid
#print axioms Modal.decidable_kb4Valid
#print axioms Modal.decidable_kb5Valid

end FMPDecidabilityAll

section FMPEuclidean

#print axioms Modal.euclid_cluster'
#print axioms Modal.euclid_cluster_closed'
#print axioms Modal.euclidSubframe_filtration_euclidean
#print axioms Modal.fmp_K5
#print axioms Modal.fmp_KD5
#print axioms Modal.k5Valid_iff_no_bounded_countermodel
#print axioms Modal.kd5Valid_iff_no_bounded_countermodel
#print axioms Modal.decidable_k5Valid
#print axioms Modal.decidable_kd5Valid

end FMPEuclidean

section FMPCluster

#print axioms Modal.transEuclid_P_sees_cluster
#print axioms Modal.euclidSubframe_filtration_transitive
#print axioms Modal.fmp_K45
#print axioms Modal.fmp_KD45
#print axioms Modal.k45Valid_iff_no_bounded_countermodel
#print axioms Modal.kd45Valid_iff_no_bounded_countermodel
#print axioms Modal.decidable_k45Valid
#print axioms Modal.decidable_kd45Valid

end FMPCluster
