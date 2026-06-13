/-
# AIQ DKPS ForMathlib inventory solution: Approximate minimizers and Berge-style continuity

Imports the corresponding project `ForMathlib` staging files. The declarations
named in the comparator config are provided by those imports.
-/
import ForMathlib.Topology.ApproxMinimizer
import ForMathlib.Topology.Berge

/-! Axiom audit commands for this inventory group. -/
#print axioms ForMathlib.exists_subseq_tendsto_forall_le_of_approxMin
#print axioms ForMathlib.exists_subseq_tendsto_isMinOn_of_approxMinOn
#print axioms ForMathlib.tendsto_eval_sub_of_isCompact
#print axioms ForMathlib.tendsto_subseq_isMinOn_of_isMinOn
#print axioms ForMathlib.upperHemicontinuousAt_isMinOn
#print axioms ForMathlib.continuous_iInf_of_isCompact
#print axioms ForMathlib.exists_modulus_isMinOn_family
#print axioms ForMathlib.exists_modulus_isMinOn
