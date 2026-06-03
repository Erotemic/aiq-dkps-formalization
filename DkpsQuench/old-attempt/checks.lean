

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open Filter MeasureTheory

-- set_option maxHeartbeats 0
-- set_option maxRecDepth 4000
-- set_option synthInstance.maxHeartbeats 20000
-- set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false


#check measurable_pi_iff
#check measurable_pi_apply
#check norm_add_le