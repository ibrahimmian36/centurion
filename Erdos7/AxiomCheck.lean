import Erdos7.Density
import Erdos7.AbundancyFloor
import Erdos7.Capacity

/-! Publication gate: every theorem below must depend on exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `_native.*`.
See erdos-engine/docs/ERDOS7_PLAN.md §5. -/

#print axioms card_filter_mod_le
#print axioms covering_density
#print axioms covering_density_rat
#print axioms covering_density_zmod
#print axioms sum_divisors_ge_of_covering
#print axioms not_deficient_of_covering
#print axioms covering_density_ge_one
#print axioms abundancy_floor_945
#print axioms sum_inv_divisors_eq
#print axioms sum_inv_divisors_erase_one
#print axioms sum_inv_le_abundancy
#print axioms odd_covering_lcm_ge_945

-- Step 4: the capacity bound (Erdos7.Capacity)
#print axioms prod_dvd_of_pairwise_coprime
#print axioms uncovered_card_ge
#print axioms capacity_prod_relax
#print axioms capacity_exclusion
#print axioms capacity_exclusion_int
#print axioms no_covering_lcm_dvd_945
#print axioms no_covering_lcm_dvd_1575
#print axioms no_covering_lcm_dvd_2205
#print axioms no_covering_lcm_dvd_2835
#print axioms no_covering_lcm_dvd_3465
#print axioms no_covering_lcm_dvd_4095
#print axioms no_covering_lcm_dvd_4725
#print axioms no_covering_lcm_dvd_5355
#print axioms no_covering_lcm_dvd_5775
#print axioms no_covering_lcm_dvd_5985
#print axioms no_covering_lcm_dvd_6435
#print axioms no_covering_lcm_dvd_6615
#print axioms no_covering_lcm_dvd_6825
#print axioms no_covering_lcm_dvd_7245
#print axioms no_covering_lcm_dvd_7425
#print axioms no_covering_lcm_dvd_7875
#print axioms no_covering_lcm_dvd_8085
#print axioms no_covering_lcm_dvd_8415
#print axioms no_covering_lcm_dvd_8505
#print axioms no_covering_lcm_dvd_8925
#print axioms no_covering_lcm_dvd_9135
#print axioms no_covering_lcm_dvd_9555
#print axioms no_covering_lcm_dvd_9765
#print axioms covering_lcm_notMem_oddAbundantBelow10000
#print axioms odd_covering_lcm_gt_945
