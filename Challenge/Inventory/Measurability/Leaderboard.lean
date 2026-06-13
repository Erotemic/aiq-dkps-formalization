/-
# AIQ DKPS ForMathlib inventory solution: Measurability and compact-existential infrastructure

Imports the corresponding project `ForMathlib` staging files. The declarations
named in the comparator config are provided by those imports.
-/
import ForMathlib.MeasureTheory.CfcMeasurable
import ForMathlib.MeasureTheory.CompactExists

/-! Axiom audit commands for this inventory group. -/
#print axioms ForMathlib.measurable_of_iUnion_restrict
#print axioms ForMathlib.measurable_cfc_comp
#print axioms ForMathlib.measurableSet_exists_mem_le
