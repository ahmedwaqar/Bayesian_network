(******************************************************************************)
(*   Chemotherapy Drug Injection System Failure Analysis                      *)
(*              by Waqar Ahmed HVG Concordia University, Canada               *)
(*                                                                            *)
(******************************************************************************)


(*app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "numTheory", "dep_rewrite", 
          "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory","probabilityTheory", "measureTheory" ,"real_sigmaTheory","Arith","cond_probTheory","conditional_indepTheory","DAG_FTTheory"];
*)

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory dep_rewrite
     util_probTheory real_sigmaTheory extrealTheory measureTheory probabilityTheory
     Arith cond_probTheory conditional_indepTheory DAG_FTTheory;

open HolKernel boolLib bossLib Parse;

val _ = new_theory "drug_injec_sys";

val pop_orw = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
(*---------------------------*)
fun SET_TAC L =
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC (append [EXTENSION, SUBSET_DEF, PSUBSET_DEF, DISJOINT_DEF,
    SING_DEF] L) THEN SIMP_TAC std_ss [NOT_IN_EMPTY, IN_UNIV, IN_UNION,
    IN_INTER, IN_DIFF, IN_INSERT, IN_DELETE, IN_BIGINTER, IN_BIGUNION,
    IN_IMAGE, GSPECIFICATION, IN_DEF] THEN METIS_TAC [];

fun SET_RULE tm = prove(tm,SET_TAC []);


val set_rewrs
= [INTER_EMPTY, INTER_UNIV, UNION_EMPTY, UNION_UNIV, DISJOINT_UNION,
DISJOINT_INSERT, DISJOINT_EMPTY, GSYM DISJOINT_EMPTY_REFL,
DISJOINT_BIGUNION, INTER_SUBSET, INTER_IDEMPOT, UNION_IDEMPOT,
SUBSET_UNION];

val UNIONL_def = Define `(UNIONL [] = {})
/\ (UNIONL (s::ss) = (s:'a ->bool) UNION UNIONL ss)`;


val IN_UNIONL = store_thm
("IN_UNIONL",
``!l (v:'a ). v IN UNIONL l = (?s. MEM s l /\ v IN s)``,
Induct >> RW_TAC std_ss [UNIONL_def, MEM, NOT_IN_EMPTY]
\\ RW_TAC std_ss [UNIONL_def, MEM, NOT_IN_EMPTY, IN_UNION]
\\ PROVE_TAC []);


val elt_rewrs
= [SUBSET_DEF, IN_COMPL, IN_DIFF, IN_UNIV, NOT_IN_EMPTY, IN_UNION,
IN_INTER, IN_IMAGE, IN_FUNSET, IN_DFUNSET, GSPECIFICATION,
DISJOINT_DEF, IN_BIGUNION, IN_BIGINTER, IN_COUNT, IN_o,
IN_UNIONL, IN_DELETE, IN_PREIMAGE, IN_SING, IN_INSERT];


fun rewr_ss ths =
simpLib.++
(std_ss,
simpLib.SSFRAG
{ac = [],
name = NONE,
convs = [],
dprocs = [],
filter = NONE,
rewrs = set_rewrs @ elt_rewrs,
congs = []});
val pset_set_ss = rewr_ss set_rewrs;
val pset_elt_ss = rewr_ss elt_rewrs;
val pset_ss = rewr_ss (set_rewrs @ elt_rewrs);


fun PSET_TAC ths =
REPEAT (POP_ASSUM MP_TAC)
\\ RW_TAC pset_set_ss ths
\\ REPEAT (POP_ASSUM MP_TAC)
\\ RW_TAC pset_elt_ss ths;
(*--------------------*)

load "Arith";
open Arith;

val ARITH_PROVE = EQT_ELIM o ARITH_CONV;

val PROD_IMAGE_REAL_INSERT = store_thm("PROD_IMAGE_REAL_INSERT",
  ``!f e s.
             FINITE s ⇒
             (PROD_IMAGE_REAL f (e INSERT s) =
              f e * PROD_IMAGE_REAL f (s DELETE e))``,
rw[] \\ metis_tac[PROD_IMAGE_REAL]);

val count_delete_ID = store_thm("count_delete_ID",
  ``!a. (count a) DELETE a = count a``,
rw[EXTENSION,count_def]);


val test = save_thm ("test",
chain_rule_thm |> Q.SPECL[`(p :(α -> bool) # ((α -> bool) -> bool) # ((α -> bool) -> real))`,
                      `(\a. case a of 1 => x1 | 2 => x2 | 3 => x3 | 4 => x4 | 5 => x5 | _ => p_space p)`, `5:num`]
	       |> REWRITE_RULE[chain_rule_def,prove ( ``count 5 = {4;3;2;1;0}``,rw[count_def,EXTENSION] \\ metis_tac[])]
	       |> SIMP_RULE (srw_ss())[chain_rule_def,COUNT_SUC,FINITE_COUNT,PROD_IMAGE_REAL_INSERT,count_delete_ID,DELETE_DEF,PROD_IMAGE_REAL]
	       |> REWRITE_RULE[prove ( ``(count 4 = {3;2;1;0}) /\ (count 3 = {2;1;0}) /\(count 2 = {1;0}) /\ (count 1 = {0}) ``,rw[count_def,EXTENSION] \\ metis_tac[])]
	       |> SIMP_RULE (srw_ss())[GSYM INTER_ASSOC,INTER_IDEMPOT]);

val chain_rule_cell_injec = save_thm ("chain_rule_cell_injec",
chain_rule_thm |> Q.SPECL[`(p :(α -> bool) # ((α -> bool) -> bool) # ((α -> bool) -> real))`,
                      `(\a. case a of 1 => x1 |
		                      2 => x2 |
				      3 => x3 |
				      4 => x4 |
				      5 => x5 |
				      6 => x6 |
				      7 => x7 |
				      8 => x8 |
				      9 => y1 |
				      10 => y2 |
				      11 => y3 |
				      12 => y4 |
				      13 => y5 |
				      14 => T' |
				      _ => p_space p)`, `15:num`]
	       |> REWRITE_RULE[chain_rule_def,prove ( ``count 15 = count (SUC (SUC (SUC 12)))``,rw[count_def,EXTENSION]),COUNT_SUC,prove ( ``count 12 = {11;10;9;8;7;6;5;4;3;2;1;0}``,rw[count_def,EXTENSION])]	       
	       |> SIMP_RULE (srw_ss())[chain_rule_def,COUNT_SUC,FINITE_COUNT,PROD_IMAGE_REAL_INSERT,count_delete_ID,DELETE_DEF,PROD_IMAGE_REAL]	       
	       |> REWRITE_RULE[prove ( ``(count 13 = count (SUC 12)) /\
	       	  		         (count 12 = {11;10;9;8;7;6;5;4;3;2;1;0}) /\
	                                 (count 11 = {10;9;8;7;6;5;4;3;2;1;0}) /\
					 (count 10 = {9;8;7;6;5;4;3;2;1;0}) /\
					 (count 9 = {8;7;6;5;4;3;2;1;0}) /\
					 (count 8 = {7;6;5;4;3;2;1;0}) /\
					 (count 7 = {6;5;4;3;2;1;0}) /\
					 (count 6 = {5;4;3;2;1;0}) /\
					 ((count 5 = {4;3;2;1;0})) /\
					 (count 4 = {3;2;1;0}) /\
					 (count 3 = {2;1;0}) /\
					 (count 2 = {1;0}) /\
					 (count 1 = {0})``, rw[count_def,EXTENSION] \\ metis_tac[])]
	       |> SIMP_RULE (srw_ss())[GSYM INTER_ASSOC,INTER_IDEMPOT]
	       |> SIMP_RULE (srw_ss())[INTER_ASSOC]
	       |> REWRITE_RULE[chain_rule_def,prove ( ``count 13 = count (SUC 12)``,rw[count_def,EXTENSION]),COUNT_SUC,prove ( ``count 12 = {11;10;9;8;7;6;5;4;3;2;1;0}``,rw[count_def,EXTENSION])]
	       |> SIMP_RULE (srw_ss())[INTER_ASSOC,INTER_IDEMPOT]);

(*-------------------------*)
val cond_prob_reduce_y1 = store_thm("cond_prob_reduce_y1",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 y1.
   (0 < prob p (x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ (x2 ∩ x1)) ∧
    0 < prob p (x2 ∩ x1)) /\
   cond_indep p y1  (x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3) (x2 INTER x1) /\
   ALL_DISTINCT [x1;x2;x3;x4;x5;x6;x7;x8;y1] /\ prob_space p ==>
   (cond_prob p y1 (x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1) =
    cond_prob p y1 (x2 ∩ x1))``,
rw[]
\\ rw [prove(``(x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1) = (x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ (x2 ∩ x1))``,rw[EXTENSION] \\ metis_tac[])]
\\ DEP_ONCE_REWRITE_TAC[cond_prob_inter_swap1]
\\ fs[cond_indep_def]
\\ rw[]
\\ DEP_REWRITE_TAC[REAL_EQ_LDIV_EQ]
\\ rw[cond_prob_def]
>- (fs[])
\\ rw[REAL_LT_DIV]);

(*-------------------------*)
val cond_prob_reduce_y2 = store_thm("cond_prob_reduce_y2",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2.
   ( 0 < prob p (y1 ∩ x8 ∩ x7 ∩ x3 ∩ x2 ∩ x1 ∩ x6 ∩ x5 ∩ x4) ∧
    0 < prob p (x6 INTER x5 ∩ x4)) /\
   cond_indep p y2  (y1 ∩ x8 ∩ x7 ∩ x3 ∩ x2 ∩ x1) (x6 INTER x5 ∩ x4) /\
   ALL_DISTINCT [x1;x2;x3;x4;x5;x6;x7;x8;y1;y2] /\ prob_space p ==>
   (cond_prob p y2 (y1 INTER x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1) =
    cond_prob p y2 (x6 INTER x5 ∩ x4))``,
rw[]
\\ rw [prove(``(y1 INTER x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1) = (y1 INTER x8 ∩ x7 ∩ x3 ∩ x2 ∩ x1 ∩ (x6 ∩ x5 ∩ x4))``,rw[EXTENSION] \\ metis_tac[])]
\\ DEP_ONCE_REWRITE_TAC[cond_prob_inter_swap1]
\\ fs[cond_indep_def,INTER_ASSOC]
\\ rw[]
\\ DEP_REWRITE_TAC[REAL_EQ_LDIV_EQ]
\\ rw[cond_prob_def]
>- (fs[])
\\ rw[INTER_ASSOC,REAL_LT_DIV]);

(*---------------------*)

val cond_prob_reduce_y3 = store_thm("cond_prob_reduce_y3",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3.
   (0 < prob p (y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x2 ∩ x1 ∩ (y2 ∩ x3)) ∧
    0 < prob p (y2 ∩ x3)) /\
   cond_indep p y3  (y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x2 ∩ x1) (y2 ∩ x3 ) /\
   ALL_DISTINCT [x1;x2;x3;x4;x5;x6;x7;x8;y1;y2;y3] /\ prob_space p ==>
   (cond_prob p y3 (y2 INTER y1 INTER x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1) =
    cond_prob p y3 (y2 INTER x3))``,
rw[]
\\ rw [prove(``(y2 ∩ y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1) =
               (y1 INTER x8 ∩ x7 INTER x6 ∩ x5 ∩ x4 ∩ x2 ∩ x1 ∩ (y2 ∩ x3 ))``,
	       rw[EXTENSION] \\ metis_tac[])]
\\ DEP_ONCE_REWRITE_TAC[cond_prob_inter_swap1]
\\ fs[cond_indep_def,INTER_ASSOC]
\\ rw[]
\\ DEP_REWRITE_TAC[REAL_EQ_LDIV_EQ]
\\ rw[cond_prob_def]
>- (fs[])
\\ rw[INTER_ASSOC,REAL_LT_DIV]);

(*-------------------*)
val cond_prob_reduce_y4 = store_thm("cond_prob_reduce_y4",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4.
   (0 < prob p (y3 ∩ y2 ∩ y1 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1 ∩ x8 ∩ x7) ∧
    0 < prob p (x8 ∩ x7)) /\
   cond_indep p y4  (y3 INTER y2 INTER y1 ∩ x6 INTER x5 INTER x4 INTER x3 INTER x2 ∩ x1) (x8 INTER x7) /\
   ALL_DISTINCT [x1;x2;x3;x4;x5;x6;x7;x8;y1;y2;y3;y4] /\ prob_space p ==>
   (cond_prob p y4
     (y3 INTER y2 INTER y1 INTER x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1) =
    cond_prob p y4 (x8 INTER x7))``,
rw[]
\\ rw [prove(``(y3 INTER y2 ∩ y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1) =
               (y3 INTER y2 ∩ y1 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1 INTER (x8 INTER x7))``,
	       rw[EXTENSION] \\ metis_tac[])]
\\  DEP_ONCE_REWRITE_TAC[cond_prob_inter_swap1]
\\ fs[cond_indep_def,INTER_ASSOC]
\\ rw[]
\\ DEP_REWRITE_TAC[REAL_EQ_LDIV_EQ]
\\ rw[cond_prob_def]
>- (fs[])
\\ rw[INTER_ASSOC,REAL_LT_DIV]);
(*----------------------------*)
val cond_prob_reduce_y5 = store_thm("cond_prob_reduce_y5",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5.
   (0 < prob p (y4 ∩ y3 ∩ y2 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1 ∩ y3 ∩ y1) ∧
    0 < prob p (y3 ∩ y1)) /\
   cond_indep p y5  (y4 ∩ y3 INTER y2 INTER x8 ∩ x7 INTER  x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1)
                    (y3 INTER y1) /\
   ALL_DISTINCT [x1;x2;x3;x4;x5;x6;x7;x8;y1;y2;y3;y4;y5] /\ prob_space p ==>
   (cond_prob p y5
     (y4 INTER y3 INTER y2 INTER y1 INTER x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1) =
    cond_prob p y5 (y3 INTER y1))``,
rw[]
\\ once_rewrite_tac [prove(``(y4 INTER y3 INTER y2 ∩ y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1) =
               (y4 ∩ y3 INTER y2 INTER x8 ∩ x7 INTER  x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1 INTER (y3 INTER y1))``,
	       rw[EXTENSION] \\ metis_tac[])]
\\  DEP_ONCE_REWRITE_TAC[cond_prob_inter_swap1]
\\ fs[cond_indep_def,INTER_ASSOC]
\\ rw[]
\\ DEP_REWRITE_TAC[REAL_EQ_LDIV_EQ]
\\ rw[cond_prob_def]
>- (fs[])
\\ rw[INTER_ASSOC,REAL_LT_DIV]);
(*------------------------------*)
val cond_prob_reduce_T' = store_thm("cond_prob_reduce_T'",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T'.
   (0 < prob p (y3 ∩ y2 ∩ y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1 ∩ y5 ∩ y4) ∧
    0 < prob p (y5 ∩ y4)) /\
   cond_indep p T'  (y3 INTER y2 INTER y1 INTER x8 ∩ x7 INTER  x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1)
                    (y5 INTER y4) /\
   ALL_DISTINCT [x1;x2;x3;x4;x5;x6;x7;x8;y1;y2;y3;y4;y5;T'] /\ prob_space p ==>
   (cond_prob p T'
     (y5 INTER y4 INTER y3 INTER y2 INTER y1 INTER x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2
     ∩ x1) =
    cond_prob p T' (y5 INTER y4))``,
rw[]
\\ once_rewrite_tac [prove(``(y5 INTER y4 INTER y3 INTER y2 ∩ y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1) =
               (y3 INTER y2 INTER y1 INTER x8 ∩ x7 INTER  x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1 INTER (y5 INTER y4))``,
	       rw[EXTENSION] \\ metis_tac[])]
\\  DEP_ONCE_REWRITE_TAC[cond_prob_inter_swap1]
\\ fs[cond_indep_def,INTER_ASSOC]
\\ rw[]
\\ DEP_REWRITE_TAC[REAL_EQ_LDIV_EQ]
\\ rw[cond_prob_def]
>- (fs[])
\\ rw[INTER_ASSOC,REAL_LT_DIV]);
(*---------------------*)
val Prob_BN_cell_inject = store_thm("Prob_BN_cell_inject",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T'.
 (0 < prob p (x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ (x2 ∩ x1)) ∧
  0 < prob p (x2 ∩ x1) ∧
  cond_indep p y1 (x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3) (x2 ∩ x1)) /\
(*--cond for y2 *)
 (0 < prob p (y1 ∩ x8 ∩ x7 ∩ x3 ∩ x2 ∩ x1 ∩ x6 ∩ x5 ∩ x4) ∧
  0 < prob p (x6 ∩ x5 ∩ x4) ∧
  cond_indep p y2 (y1 ∩ x8 ∩ x7 ∩ x3 ∩ x2 ∩ x1) (x6 ∩ x5 ∩ x4)) /\
(*--cond for y3 --*)
 (0 < prob p (y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x2 ∩ x1 ∩ (y2 ∩ x3)) ∧
  0 < prob p (y2 ∩ x3) ∧
  cond_indep p y3 (y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x2 ∩ x1) (y2 ∩ x3)) /\
(*--cond for y4--*)
 (0 < prob p (y3 ∩ y2 ∩ y1 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1 ∩ x8 ∩ x7) ∧
  0 < prob p (x8 ∩ x7) ∧
  cond_indep p y4 (y3 ∩ y2 ∩ y1 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1) (x8 ∩ x7)) /\
(*--cond for y5 --*)
 (0 <
  prob p
    (y4 ∩ y3 ∩ y2 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1 ∩ y3 ∩ y1) ∧
  0 < prob p (y3 ∩ y1) ∧
  cond_indep p y5
    (y4 ∩ y3 ∩ y2 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1) (y3 ∩ y1)) /\
 (*-- cond for T' --*)
 (0 <
  prob p
    (y3 ∩ y2 ∩ y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1 ∩ y5 ∩ y4) ∧
  0 < prob p (y5 ∩ y4) ∧
  cond_indep p T'
    (y3 ∩ y2 ∩ y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1) (y5 ∩ y4)) /\ 
 ALL_DISTINCT [x1;x2;x3;x4;x5;x6;x7;x8;y1;y2;y3;y4;y5;T'] /\ prob_space p /\
 (!x. MEM x [x1;x2;x3;x4;x5;x6;x7;x8;y1;y2;y3;y4;y5;T'] ==> x IN events p) /\
 (∀B.
        no_parents_prob_ID p {x1; x2; x3; x4; x5; x6; x7; x8}
          (inject_sys_DAG x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T') B) ==>
 (prob p
    (T' ∩ y5 ∩ y4 ∩ y3 ∩ y2 ∩ y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩
     x1 ∩ p_space p) =
  cond_prob p T' (y5 ∩ y4) * cond_prob p y5 (y1 ∩ y3) *
  cond_prob p y4 (x7 ∩ x8) * cond_prob p y3 (y2 ∩ x3) *
  cond_prob p y2 (x4 ∩ (x6 ∩ x5)) * cond_prob p y1 (x2 ∩ x1) * prob p x8 *
  prob p x7 * prob p x6 * prob p x5 * prob p x4 * prob p x3 * prob p x2 *
  prob p x1)``,
rw[]
\\ DEP_REWRITE_TAC[chain_rule_cell_injec]
\\ RW_TAC std_ss[IN_FUNSET]
>- (fs[EVENTS_SPACE])
\\ DEP_REWRITE_TAC[COND_PROB_ITSELF]
\\ rw[EVENTS_SPACE,PROB_UNIV]
\\ fs[no_parents_prob_ID_def]
\\ rw[REAL_MUL_ASSOC]
\\ Q.ABBREV_TAC `T_top = cond_prob p T'
     (y5 ∩ y4 ∩ y3 ∩ y2 ∩ y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1 ∩
      p_space p) `
 \\  Q.ABBREV_TAC `Y5 = cond_prob p y5
      (y4 ∩ y3 ∩ y2 ∩ y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1 ∩
       p_space p ∩ p_space p)`
\\ Q.ABBREV_TAC `Y4 = cond_prob p y4
     (y3 ∩ y2 ∩ y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1 ∩ p_space p)`
\\ Q.ABBREV_TAC `Y3 = cond_prob p y3
     (y2 ∩ y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1 ∩ p_space p)`
 \\ Q.ABBREV_TAC `Y2 = cond_prob p y2 (y1 ∩ x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1 ∩ p_space p)`  
\\ Q.ABBREV_TAC  `Y1 = cond_prob p y1 (x8 ∩ x7 ∩ x6 ∩ x5 ∩ x4 ∩ x3 ∩ x2 ∩ x1 ∩ p_space p)`
\\ ntac 8 (DEP_ONCE_ASM_REWRITE_TAC[])
\\ rw[no_parents_prob_ID_def]
\\ rw[no_parents_nodes_def,inject_sys_DAG_def,node_parents_def]
\\ ntac 8 (disj2_tac)
\\ Q.UNABBREV_TAC `Y1`
\\ Q.UNABBREV_TAC `Y2`
\\ Q.UNABBREV_TAC `Y3`
\\ Q.UNABBREV_TAC `Y4`
\\ Q.UNABBREV_TAC `T_top`
\\ once_rewrite_tac[INTER_COMM]
\\ DEP_REWRITE_TAC[INTER_PSPACE]
\\ DEP_REWRITE_TAC[EVENTS_INTER]
\\ fs[]
\\ rw[cond_prob_reduce_y1]
\\ DEP_REWRITE_TAC[cond_prob_reduce_T']
\\ rw[]
\\ DEP_REWRITE_TAC[cond_prob_reduce_y4]
\\ rw[]
\\ DEP_REWRITE_TAC[cond_prob_reduce_y3]
\\ rw[]
\\ DEP_REWRITE_TAC[cond_prob_reduce_y2]
\\ rw[]
\\ Q.UNABBREV_TAC `Y5`
\\ once_rewrite_tac[INTER_COMM]
\\ DEP_REWRITE_TAC[INTER_PSPACE]
\\ once_rewrite_tac[INTER_COMM]
\\ DEP_REWRITE_TAC[INTER_PSPACE]
\\ DEP_REWRITE_TAC[EVENTS_INTER]
\\ fs[]
\\ DEP_REWRITE_TAC[cond_prob_reduce_y5]
\\ rw[]
\\ metis_tac[INTER_COMM]);


val fork_DAG_CI_def = Define
`fork_DAG_CI p x1 x2 x3 D = fork_DAG x1 x2 x3 D ==> cond_indep p x1 x2 x3`;


(*-------------------------*)

val _ = type_abbrev ("set", ``:'a -> bool``);


val pred_events_space_def = Define
`pred_events_space p f s =
(!x. x IN s ==> f x IN events p) /\
FINITE s /\ (∀x y. x ∈ s ∧ y ∈ s ∧ x ≠ y ⇒ DISJOINT (f x) (f y)) /\
(BIGUNION (IMAGE f s) ∩ p_space p = p_space p)`;


val pred_list_events_space_def = Define
`(pred_list_events_space p [] = T) /\
(pred_list_events_space p (h::t) =
pred_events_space p (FST h) (SND h) /\
pred_list_events_space p t)`;


val fail_prob_drug_inject_lemma = store_thm("fail_prob_drug_inject_lemma",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T' sx1 sx2 sx3 sx4 sx5 sx6 sx7 sx8 sy1 sy2 sy3 sy4 sy5.
prob_space p /\
(T' IN events p) /\
 (pred_list_events_space p [(y5,sy5);(y4,sy4);(y3,sy3);(y2,sy2);(y1,sy1);(x8,sx8);(x7,sx7);(x6,sx6);(x5,sx5);(x4,sx4);(x3,sx3);(x2,sx2);(x1,sx1)]) ==>
(prob p T' =
SIGMA (λx. SIGMA (λx'. SIGMA (λx''. SIGMA (λx'''. SIGMA (λx''''. SIGMA (λy'.
SIGMA (λy''. SIGMA (λy'''. SIGMA (λy''''. SIGMA (λz'. SIGMA (λz''. SIGMA (λz'''. SIGMA (λz''''.
      if z'''' IN sx1 then
      if z''' ∈ sx2 then
      if z'' ∈ sx3 then
      if z' ∈ sx4 then
      if y'''' ∈ sx5 then
      if y''' ∈ sx6 then
      if y'' ∈ sx7 then
      if y' ∈ sx8 then
      if  x'''' ∈ sy1 then
      if x''' ∈ sy2 then
      if x'' ∈ sy3 then
      if x' ∈ sy4 then
      if x ∈ sy5 then
   prob p (T' ∩ y5 x ∩ y4 x' ∩ y3 x'' ∩ y2 x''' ∩ y1 x'''' ∩ x8 y' ∩
          x7 y'' ∩ x6 y''' ∩ x5 y'''' ∩ x4 z' ∩ x3 z'' ∩ x2 z''' ∩ x1 z'''')
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
     else 0
     else 0)
   sx1) sx2) sx3) sx4) sx5) sx6) sx7) sx8) sy1) sy2) sy3) sy4) sy5)``,
rw[]
\\ mp_tac(Q.SPECL[`(p :α set # α set set # (α set -> real))`, `y5:'b -> 'a set`,`T':'a set`,`sy5:'b set`] PROB_REAL_SUM_IMAGE_FN)
\\ rw[]
\\ DEP_ASM_REWRITE_TAC[]
\\ pop_orw
\\ CONJ_TAC
>- (fs[pred_list_events_space_def] \\ metis_tac[pred_events_space_def,EVENTS_INTER])
\\ DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_IN_IF]
\\ rw[]
>- (fs[pred_list_events_space_def,pred_events_space_def,EVENTS_INTER])
\\ sg `!x.  (if x ∈ sy5 then prob p (T' ∩ y5 x) else 0) = SIGMA (λx'. (if x ∈ sy5 then prob p (T' ∩ y5 x INTER y4 x') else 0))  sy4`
\\ rw[]
\\ DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_0]
>- (HO_MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
   \\ fs[pred_list_events_space_def] \\ metis_tac[pred_events_space_def,EVENTS_INTER])
>- ((fs[pred_list_events_space_def,pred_events_space_def,EVENTS_INTER]))
\\ sg `!x. SIGMA (λx'. if x ∈ sy5 then prob p (T' ∩ y5 x ∩ y4 x') else 0) sy4 =
      	      (SIGMA
		(λx'.
		     if x' ∈ sy4 then if x ∈ sy5 then prob p (T' ∩ y5 x ∩ y4 x') else 0
           	     else 0) sy4)`
>- (gen_tac
    \\ DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_IN_IF]
    \\ fs[pred_list_events_space_def,pred_events_space_def])
\\ pop_orw
\\ sg ` !x x'.
          (if x' ∈ sy4 then if x ∈ sy5 then prob p (T' ∩ y5 x ∩ y4 x') else 0
          else 0) = SIGMA (λx''. (if x' ∈ sy4 then if x ∈ sy5 then prob p (T' ∩ y5 x ∩ y4 x' INTER y3 x'') else 0
          else 0)) sy3`
>- (rw[]
   >- (HO_MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
   \\ fs[pred_list_events_space_def,pred_events_space_def] \\ DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[pred_events_space_def,EVENTS_INTER])
   >- (fs[pred_list_events_space_def,pred_events_space_def,REAL_SUM_IMAGE_0])
   \\ fs[pred_list_events_space_def,pred_events_space_def,REAL_SUM_IMAGE_0])
\\ pop_orw
(*-----*)
\\ sg `!x x'. SIGMA (λx''. if x' ∈ sy4 then
                          if x ∈ sy5 then prob p (T' ∩ y5 x ∩ y4 x' ∩ y3 x'')
                          else 0
                        else 0) sy3 =
      	      (SIGMA
		(λx''.
		     if x'' IN sy3 then if x' ∈ sy4 then
                          if x ∈ sy5 then prob p (T' ∩ y5 x ∩ y4 x' ∩ y3 x'')
                          else 0
                        else 0 else 0) sy3)`
>- (rpt gen_tac
    \\ DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_IN_IF]
    \\ fs[pred_list_events_space_def,pred_events_space_def])
\\ pop_orw
\\ sg ` !x x' x''.
          (if x'' IN sy3 then if x' ∈ sy4 then
                          if x ∈ sy5 then prob p (T' ∩ y5 x ∩ y4 x' ∩ y3 x'')
                          else 0
                        else 0 else 0) = SIGMA (λx'''. if x'' IN sy3 then if x' ∈ sy4 then
                          if x ∈ sy5 then prob p (T' ∩ y5 x ∩ y4 x' ∩ y3 x'' INTER y2 x''')
                          else 0
                        else 0 else 0) sy2`

>- (rw[]
   >- (HO_MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
   \\ fs[pred_list_events_space_def,pred_events_space_def] \\ DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[pred_events_space_def,EVENTS_INTER])
   >- (fs[pred_list_events_space_def,pred_events_space_def,REAL_SUM_IMAGE_0])
   \\ fs[pred_list_events_space_def,pred_events_space_def,REAL_SUM_IMAGE_0])
\\ pop_orw
(*--y1---*)
\\ sg `!x x' x''. SIGMA (λx'''. if x'' IN sy3 then if x' ∈ sy4 then
                          if x ∈ sy5 then prob p (T' ∩ y5 x ∩ y4 x' ∩ y3 x'' INTER y2 x''')
                          else 0
                        else 0 else 0) sy2 =
      	      (SIGMA
		(λx'''. if x''' IN sy2 then if x'' IN sy3 then if x' ∈ sy4 then
                          if x ∈ sy5 then prob p (T' ∩ y5 x ∩ y4 x' ∩ y3 x'' INTER y2 x''')
                          else 0
                        else 0 else 0 else 0) sy2)`
>- (rpt gen_tac
    \\ DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_IN_IF]
    \\ fs[pred_list_events_space_def,pred_events_space_def])
\\ pop_orw
\\ sg ` !x x' x'' x'''.
          (if x''' IN sy2 then if x'' IN sy3 then if x' ∈ sy4 then
                          if x ∈ sy5 then prob p (T' ∩ y5 x ∩ y4 x' ∩ y3 x'' INTER y2 x''')
                          else 0
                        else 0 else 0 else 0) =
	SIGMA (λx''''.
		 if x''' IN sy2 then if x'' IN sy3 then if x' ∈ sy4 then
                          if x ∈ sy5 then prob p (T' ∩ y5 x ∩ y4 x' ∩ y3 x'' INTER y2 x''' INTER y1 x'''')
                          else 0
                        else 0 else 0 else 0) sy1`

>- (rw[]
   \\ fs[pred_list_events_space_def,pred_events_space_def,REAL_SUM_IMAGE_0]
   \\ HO_MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
   \\ fs[pred_list_events_space_def,pred_events_space_def] \\ rw [] \\   DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[pred_events_space_def,EVENTS_INTER])
\\ pop_orw

(*--x8---*)
\\ sg `!x x' x'' x'''. SIGMA (λx''''.
                                      if x''' ∈ sy2 then
                                        if x'' ∈ sy3 then
                                          if x' ∈ sy4 then
                                            if x ∈ sy5 then
                                              prob p
                                                (T' ∩ y5 x ∩ y4 x' ∩ y3 x'' ∩
                                                 y2 x''' ∩ y1 x'''')
                                            else 0
                                          else 0
                                        else 0
                                      else 0) sy1 =
      	      	    (SIGMA
			(λx''''.
				   if x'''' IN sy1 then
                                      if x''' ∈ sy2 then
                                        if x'' ∈ sy3 then
                                          if x' ∈ sy4 then
                                            if x ∈ sy5 then
                                              prob p
                                                (T' ∩ y5 x ∩ y4 x' ∩ y3 x'' ∩
                                                 y2 x''' ∩ y1 x'''')
                                            else 0
                                          else 0
                                        else 0
                                      else 0
				     else 0) sy1)`
>- (rpt gen_tac
    \\ DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_IN_IF]
    \\ fs[pred_list_events_space_def,pred_events_space_def])
\\ pop_orw
\\ sg ` !x x' x'' x''' x''''.
          (if x'''' IN sy1 then
                                      if x''' ∈ sy2 then
                                        if x'' ∈ sy3 then
                                          if x' ∈ sy4 then
                                            if x ∈ sy5 then
                                              prob p
                                                (T' ∩ y5 x ∩ y4 x' ∩ y3 x'' ∩
                                                 y2 x''' ∩ y1 x'''')
                                            else 0
                                          else 0
                                        else 0
                                      else 0
				     else 0) =
	SIGMA (λy'.
		if x'''' IN sy1 then
                                      if x''' ∈ sy2 then
                                        if x'' ∈ sy3 then
                                          if x' ∈ sy4 then
                                            if x ∈ sy5 then
                                              prob p
                                                (T' ∩ y5 x ∩ y4 x' ∩ y3 x'' ∩
                                                 y2 x''' ∩ y1 x'''' INTER x8 y')
                                            else 0
                                          else 0
                                        else 0
                                      else 0
				     else 0) sx8`

>- (rw[]
   \\ fs[pred_list_events_space_def,pred_events_space_def,REAL_SUM_IMAGE_0]
   \\ HO_MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
   \\ fs[pred_list_events_space_def,pred_events_space_def] \\ rw [] \\   DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[pred_events_space_def,EVENTS_INTER])
\\ pop_orw

(*----x7----*)
\\ sg `!x x' x'' x''' x''''.	    SIGMA
                                        (λy'.
                                             if x'''' ∈ sy1 then
                                               if x''' ∈ sy2 then
                                                 if x'' ∈ sy3 then
                                                   if x' ∈ sy4 then
                                                     if x ∈ sy5 then
                                                       prob p
                                                         (T' ∩ y5 x ∩ y4 x' ∩
                                                          y3 x'' ∩ y2 x''' ∩
                                                          y1 x'''' ∩ x8 y')
                                                     else 0
                                                   else 0
                                                 else 0
                                               else 0
                                             else 0) sx8 =
      	      	                  (SIGMA
                                        (λy'.
					     if y' IN sx8 then
                                             if x'''' ∈ sy1 then
                                               if x''' ∈ sy2 then
                                                 if x'' ∈ sy3 then
                                                   if x' ∈ sy4 then
                                                     if x ∈ sy5 then
                                                       prob p
                                                         (T' ∩ y5 x ∩ y4 x' ∩
                                                          y3 x'' ∩ y2 x''' ∩
                                                          y1 x'''' ∩ x8 y')
                                                     else 0
                                                   else 0
                                                 else 0
                                               else 0
                                             else 0
					    else 0) sx8)`
>- (rpt gen_tac
    \\ DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_IN_IF]
    \\ fs[pred_list_events_space_def,pred_events_space_def])
\\ pop_orw
\\ sg ` !x x' x'' x''' x'''' y'.
					    (if y' ∈ sx8 then
                                               if x'''' ∈ sy1 then
                                                 if x''' ∈ sy2 then
                                                   if x'' ∈ sy3 then
                                                     if x' ∈ sy4 then
                                                       if x ∈ sy5 then
                                                         prob p
                                                           (T' ∩ y5 x ∩
                                                            y4 x' ∩ y3 x'' ∩
                                                            y2 x''' ∩
                                                            y1 x'''' ∩ x8 y')
                                                       else 0
                                                     else 0
                                                   else 0
                                                 else 0
                                               else 0
                                             else 0) =
				SIGMA (λy''.
					    if y' ∈ sx8 then
                                               if x'''' ∈ sy1 then
                                                 if x''' ∈ sy2 then
                                                   if x'' ∈ sy3 then
                                                     if x' ∈ sy4 then
                                                       if x ∈ sy5 then
                                                         prob p
                                                           (T' ∩ y5 x ∩
                                                            y4 x' ∩ y3 x'' ∩
                                                            y2 x''' ∩
                                                            y1 x'''' ∩ x8 y' INTER x7 y'')
                                                       else 0
                                                     else 0
                                                   else 0
                                                 else 0
                                               else 0
                                             else 0) sx7`

>- (rw[]
   \\ fs[pred_list_events_space_def,pred_events_space_def,REAL_SUM_IMAGE_0]
   \\ HO_MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
   \\ fs[pred_list_events_space_def,pred_events_space_def] \\ rw [] \\   DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[pred_events_space_def,EVENTS_INTER])
\\ pop_orw
(*---x6---*)
\\ sg `!x x' x'' x''' x'''' y'.	    SIGMA
                                        (λy''.
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0) sx7 =
      	      	                  (SIGMA
                                       (λy''.
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0) sx7)`
>- (rpt gen_tac
    \\ DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_IN_IF]
    \\ fs[pred_list_events_space_def,pred_events_space_def])
\\ pop_orw
\\ sg ` !x x' x'' x''' x'''' y' y''.
					    ( if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0) =
				SIGMA (λy'''.
					    if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0) sx6`

>- (rw[]
   \\ fs[pred_list_events_space_def,pred_events_space_def,REAL_SUM_IMAGE_0]
   \\ HO_MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
   \\ fs[pred_list_events_space_def,pred_events_space_def] \\ rw [] \\   DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[pred_events_space_def,EVENTS_INTER])
\\ pop_orw
(*---x5---*)
\\ sg `!x x' x'' x''' x'''' y' y''.	    SIGMA
						(λy'''.
						   if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0) sx6 =
      	      	                  (SIGMA
                                       (λy'''.
						if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0) sx6)`
>- (rpt gen_tac
    \\ DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_IN_IF]
    \\ fs[pred_list_events_space_def,pred_events_space_def])
\\ pop_orw
\\ sg ` !x x' x'' x''' x'''' y' y'' y'''.
					    (if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0) =
				SIGMA (λy''''.
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0) sx5`

>- (rw[]
   \\ fs[pred_list_events_space_def,pred_events_space_def,REAL_SUM_IMAGE_0]
   \\ HO_MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
   \\ fs[pred_list_events_space_def,pred_events_space_def] \\ rw [] \\   DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[pred_events_space_def,EVENTS_INTER])
\\ pop_orw
(*----x4---*)
\\ sg `!x x' x'' x''' x'''' y' y'' y'''.  SIGMA (λy''''.
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0) sx5 =
      	      	                  (SIGMA (λy''''.
						if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0) sx5)`
>- (rpt gen_tac
    \\ DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_IN_IF]
    \\ fs[pred_list_events_space_def,pred_events_space_def])
\\ pop_orw
\\ sg ` !x x' x'' x''' x'''' y' y'' y''' y''''.
					    (if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0) =
				SIGMA (λz'.
					  	if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''' INTER
								   x4 z')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0) sx4`

>- (rw[]
   \\ fs[pred_list_events_space_def,pred_events_space_def,REAL_SUM_IMAGE_0]
   \\ HO_MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
   \\ fs[pred_list_events_space_def,pred_events_space_def] \\ rw [] \\   DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[pred_events_space_def,EVENTS_INTER])
\\ pop_orw
(*----x3---*)
\\ sg `!x x' x'' x''' x'''' y' y'' y''' y''''. SIGMA (λz'.
					  	if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''' INTER
								   x4 z')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0) sx4 =
      	      	                  (SIGMA (λz'.
					      if z' IN sx4 then
					  	if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''' INTER
								   x4 z')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0
						else 0) sx4)`
>- (rpt gen_tac
    \\ DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_IN_IF]
    \\ fs[pred_list_events_space_def,pred_events_space_def])
\\ pop_orw
\\ sg ` !x x' x'' x''' x'''' y' y'' y''' y'''' z'.
					    (if z' IN sx4 then
					  	if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''' INTER
								   x4 z')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0
						else 0) =
				SIGMA (λz''.
					  	if z' IN sx4 then
					  	if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''' INTER
								   x4 z' INTER x3 z'')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0
						else 0) sx3`

>- (rw[]
   \\ fs[pred_list_events_space_def,pred_events_space_def,REAL_SUM_IMAGE_0]
   \\ HO_MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
   \\ fs[pred_list_events_space_def,pred_events_space_def] \\ rw [] \\   DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[pred_events_space_def,EVENTS_INTER])
\\ pop_orw
(*---x2---*)
\\ sg `!x x' x'' x''' x'''' y' y'' y''' y'''' z'.
      	     	      	       	   	SIGMA (λz''.
					  	if z' IN sx4 then
					  	if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''' INTER
								   x4 z' INTER x3 z'')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0
						else 0) sx3 =
      	      	                  (SIGMA (λz''.
					    if z'' IN sx3 then
				  	      if z' IN sx4 then
					  	if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''' INTER
								   x4 z' INTER x3 z'')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0
						else 0
					       else 0) sx3)`
>- (rpt gen_tac
    \\ DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_IN_IF]
    \\ fs[pred_list_events_space_def,pred_events_space_def])
\\ pop_orw
\\ sg ` !x x' x'' x''' x'''' y' y'' y''' y'''' z' z''.
					    (if z'' IN sx3 then
				  	      if z' IN sx4 then
					  	if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''' INTER
								   x4 z' INTER x3 z'')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0
						else 0
					       else 0) =
				SIGMA (λz'''.
					   if z'' IN sx3 then
				  	      if z' IN sx4 then
					  	if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''' INTER
								   x4 z' INTER x3 z'' INTER x2 z''')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0
						else 0
					       else 0) sx2`

>- (rw[]
   \\ fs[pred_list_events_space_def,pred_events_space_def,REAL_SUM_IMAGE_0]
   \\ HO_MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
   \\ fs[pred_list_events_space_def,pred_events_space_def] \\ rw [] \\   DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[pred_events_space_def,EVENTS_INTER])
\\ pop_orw
(*----x1---*)
\\ sg `!x x' x'' x''' x'''' y' y'' y''' y'''' z' z''.
      	     	      	       	   	SIGMA (λz'''.
					   if z'' IN sx3 then
				  	      if z' IN sx4 then
					  	if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''' INTER
								   x4 z' INTER x3 z'' INTER x2 z''')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0
						else 0
					       else 0) sx2 =
      	      	                  (SIGMA (λz'''.
				  	 if z''' IN sx2 then 
					   if z'' IN sx3 then
				  	      if z' IN sx4 then
					  	if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''' INTER
								   x4 z' INTER x3 z'' INTER x2 z''')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0
						else 0
					       else 0
					      else 0) sx2)`
>- (rpt gen_tac
    \\ DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_IN_IF]
    \\ fs[pred_list_events_space_def,pred_events_space_def])
\\ pop_orw
\\ sg ` !x x' x'' x''' x'''' y' y'' y''' y'''' z' z'' z'''.
					 (if z''' IN sx2 then 
					   if z'' IN sx3 then
				  	      if z' IN sx4 then
					  	if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''' INTER
								   x4 z' INTER x3 z'' INTER x2 z''')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0
						else 0
					       else 0
					      else 0) =
				SIGMA (λz''''.
					   if z''' IN sx2 then 
					   if z'' IN sx3 then
				  	      if z' IN sx4 then
					  	if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''' INTER
								   x4 z' INTER x3 z'' INTER x2 z''' INTER
								   x1 z'''')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0
						else 0
					       else 0
					      else 0) sx1`

>- (rw[]
   \\ fs[pred_list_events_space_def,pred_events_space_def,REAL_SUM_IMAGE_0]
   \\ HO_MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
   \\ fs[pred_list_events_space_def,pred_events_space_def] \\ rw [] \\   DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[pred_events_space_def,EVENTS_INTER])
\\ pop_orw
\\ sg `!x x' x'' x''' x'''' y' y'' y''' y'''' z' z'' z'''.
      	     	      	       	   	SIGMA (λz''''.
					   if z''' IN sx2 then 
					   if z'' IN sx3 then
				  	      if z' IN sx4 then
					  	if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''' INTER
								   x4 z' INTER x3 z'' INTER x2 z''' INTER
								   x1 z'''')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0
						else 0
					       else 0
					      else 0) sx1 =
      	      	                  (SIGMA (λz''''.
				  	 if z'''' IN sx1 then
					   if z''' IN sx2 then 
					   if z'' IN sx3 then
				  	      if z' IN sx4 then
					  	if y'''' IN sx5 then
					  	if y''' IN sx6 then
						  if y'' IN sx7 then
                                                    if y' ∈ sx8 then
                                                      if x'''' ∈ sy1 then
                                                        if x''' ∈ sy2 then
                                                          if x'' ∈ sy3 then
                                                            if x' ∈ sy4 then
                                                              if x ∈ sy5 then
                                                                prob p
                                                                  (T' ∩
                                                                   y5 x ∩
                                                                   y4 x' ∩
                                                                   y3 x'' ∩
                                                                   y2 x''' ∩
                                                                   y1 x'''' ∩
                                                                   x8 y' ∩
                                                                   x7 y'' INTER x6 y''' INTER x5 y'''' INTER
								   x4 z' INTER x3 z'' INTER x2 z''' INTER
								   x1 z'''')
                                                              else 0
                                                            else 0
                                                          else 0
                                                        else 0
                                                      else 0
                                                    else 0
						   else 0
						  else 0
						 else 0
						else 0
					       else 0
					      else 0
					      else 0) sx1)`
>- (rpt gen_tac
    \\ DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_IN_IF]
    \\ fs[pred_list_events_space_def,pred_events_space_def])
\\ pop_orw
\\ metis_tac[]);


(*---------------------------*)
val pos_prob_drug_inj_sys_def = Define
`pos_prob_drug_inj_sys p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T' =
!(x:'b) (x':'b) (x'':'b) (x''':'b) (x'''':'b) (y':'b) (y'':'b) (y''':'b) y'''':'b z':'b z'':'b z''':'b z'''':'b.
(0 <
    prob p
      (x8 y' ∩ x7 y'' ∩ x6 y''' ∩ x5 y'''' ∩ x4 z' ∩ x3 z'' ∩
       (x2 z''' ∩ x1 z'''')) ∧ 0 < prob p (x2 z''' ∩ x1 z'''') ∧
    cond_indep p (y1 x'''')
      (x8 y' ∩ x7 y'' ∩ x6 y''' ∩ x5 y'''' ∩ x4 z' ∩ x3 z'')
      (x2 z''' ∩ x1 z'''') ∧
    0 <
    prob p
      (y1 x'''' ∩ x8 y' ∩ x7 y'' ∩ x3 z'' ∩ x2 z''' ∩ x1 z'''' ∩ x6 y''' ∩
       x5 y'''' ∩ x4 z') ∧ 0 < prob p (x6 y''' ∩ x5 y'''' ∩ x4 z') ∧
    cond_indep p (y2 x''')
      (y1 x'''' ∩ x8 y' ∩ x7 y'' ∩ x3 z'' ∩ x2 z''' ∩ x1 z'''')
      (x6 y''' ∩ x5 y'''' ∩ x4 z') ∧
    0 <
    prob p
      (y1 x'''' ∩ x8 y' ∩ x7 y'' ∩ x6 y''' ∩ x5 y'''' ∩ x4 z' ∩ x2 z''' ∩
       x1 z'''' ∩ (y2 x''' ∩ x3 z'')) ∧ 0 < prob p (y2 x''' ∩ x3 z'') ∧
    cond_indep p (y3 x'')
      (y1 x'''' ∩ x8 y' ∩ x7 y'' ∩ x6 y''' ∩ x5 y'''' ∩ x4 z' ∩ x2 z''' ∩
       x1 z'''') (y2 x''' ∩ x3 z'') ∧
    0 <
    prob p
      (y3 x'' ∩ y2 x''' ∩ y1 x'''' ∩ x6 y''' ∩ x5 y'''' ∩ x4 z' ∩ x3 z'' ∩
       x2 z''' ∩ x1 z'''' ∩ x8 y' ∩ x7 y'') ∧ 0 < prob p (x8 y' ∩ x7 y'') ∧
    cond_indep p (y4 x')
      (y3 x'' ∩ y2 x''' ∩ y1 x'''' ∩ x6 y''' ∩ x5 y'''' ∩ x4 z' ∩ x3 z'' ∩
       x2 z''' ∩ x1 z'''') (x8 y' ∩ x7 y'') ∧
    0 <
    prob p
      (y4 x' ∩ y3 x'' ∩ y2 x''' ∩ x8 y' ∩ x7 y'' ∩ x6 y''' ∩ x5 y'''' ∩
       x4 z' ∩ x3 z'' ∩ x2 z''' ∩ x1 z'''' ∩ y3 x'' ∩ y1 x'''') ∧
    0 < prob p (y3 x'' ∩ y1 x'''') ∧
    cond_indep p (y5 x)
      (y4 x' ∩ y3 x'' ∩ y2 x''' ∩ x8 y' ∩ x7 y'' ∩ x6 y''' ∩ x5 y'''' ∩
       x4 z' ∩ x3 z'' ∩ x2 z''' ∩ x1 z'''') (y3 x'' ∩ y1 x'''') ∧
    0 <
    prob p
      (y3 x'' ∩ y2 x''' ∩ y1 x'''' ∩ x8 y' ∩ x7 y'' ∩ x6 y''' ∩ x5 y'''' ∩
       x4 z' ∩ x3 z'' ∩ x2 z''' ∩ x1 z'''' ∩ y5 x ∩ y4 x') ∧
    0 < prob p (y5 x ∩ y4 x') ∧
    cond_indep p T'
      (y3 x'' ∩ y2 x''' ∩ y1 x'''' ∩ x8 y' ∩ x7 y'' ∩ x6 y''' ∩ x5 y'''' ∩
       x4 z' ∩ x3 z'' ∩ x2 z''' ∩ x1 z'''') (y5 x ∩ y4 x') ∧
    ALL_DISTINCT
      [x1 z''''; x2 z'''; x3 z''; x4 z'; x5 y''''; x6 y'''; x7 y''; x8 y';
       y1 x''''; y2 x'''; y3 x''; y4 x'; y5 x; T'] /\
    (∀B.
        no_parents_prob_ID p
          {x1 z''''; x2 z'''; x3 z''; x4 z'; x5 y''''; x6 y'''; x7 y'';
           x8 y'}
          (inject_sys_DAG (x1 z'''') (x2 z''') (x3 z'') (x4 z') (x5 y'''')
             (x6 y''') (x7 y'') (x8 y') (y1 x'''') (y2 x''') (y3 x'') (y4 x')
             (y5 x) T') B))`;


(*-------------------------------*)
val fail_prob_drug_inject = store_thm("fail_prob_drug_inject",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T' sx1 sx2 sx3 sx4 sx5 sx6 sx7 sx8 sy1 sy2 sy3 sy4 sy5.
prob_space p /\
pos_prob_drug_inj_sys p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T' /\
(T' IN events p) /\
 (pred_list_events_space p [(y5,sy5);(y4,sy4);(y3,sy3);(y2,sy2);(y1,sy1);(x8,sx8);(x7,sx7);(x6,sx6);(x5,sx5);(x4,sx4);(x3,sx3);(x2,sx2);(x1,sx1)]) ==>
(prob p T' =
SIGMA (λx. SIGMA (λx'. SIGMA (λx''. SIGMA (λx'''. SIGMA (λx''''. SIGMA (λy'.
SIGMA (λy''. SIGMA (λy'''. SIGMA (λy''''. SIGMA (λz'. SIGMA (λz''. SIGMA (λz'''. SIGMA (λz''''.
      if z'''' IN sx1 then
      if z''' ∈ sx2 then
      if z'' ∈ sx3 then
      if z' ∈ sx4 then
      if y'''' ∈ sx5 then
      if y''' ∈ sx6 then
      if y'' ∈ sx7 then
      if y' ∈ sx8 then
      if  x'''' ∈ sy1 then
      if x''' ∈ sy2 then
      if x'' ∈ sy3 then
      if x' ∈ sy4 then
      if x ∈ sy5 then
    cond_prob p T' (y5 x ∩ y4 x') * cond_prob p (y5 x) (y1 x'''' ∩ y3 x'') *
          cond_prob p (y4 x') (x7 y'' ∩ x8 y') * cond_prob p (y3 x'') (y2 x''' ∩ x3 z'') *
          cond_prob p (y2 x''') (x4 z' ∩ (x6 y''' ∩ x5 y'''')) * cond_prob p (y1 x'''') (x2 z''' ∩ x1 z'''') *
          prob p (x8 y') * prob p (x7 y'') * prob p (x6 y''') * prob p (x5 y'''') * prob p (x4 z') *
          prob p (x3 z'') * prob p (x2 z''') * prob p (x1 z'''')
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
     else 0
     else 0)
   sx1) sx2) sx3) sx4) sx5) sx6) sx7) sx8) sy1) sy2) sy3) sy4) sy5)``,
rw[]
\\ DEP_REWRITE_TAC[fail_prob_drug_inject_lemma]
\\ rw[]
\\  sg `!x x' x'' x''' x''' x'''' y' y'' y''' y'''' y''''' z' z'' z''' z''''.
    ( if z'''' ∈ sx1 then
      if z''' ∈ sx2 then
      if z'' ∈ sx3 then
      if z' ∈ sx4 then
      if y'''' ∈ sx5 then
      if y''' ∈ sx6 then
      if y'' ∈ sx7 then
      if y' ∈ sx8 then
      if  x'''' ∈ sy1 then
      if x''' ∈ sy2 then
      if x'' ∈ sy3 then
      if x' ∈ sy4 then
      if x ∈ sy5 then
    prob p (T' ∩ y5 x ∩ y4 x' ∩ y3 x'' ∩ y2 x''' ∩ y1 x'''' ∩ x8 y' ∩
          x7 y'' ∩ x6 y''' ∩ x5 y'''' ∩ x4 z' ∩ x3 z'' ∩ x2 z''' ∩ x1 z'''')
else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
     else 0
     else 0) =
 ( if z'''' IN sx1 then
	if z''' ∈ sx2 then
      if z'' ∈ sx3 then
      if z' ∈ sx4 then
      if y'''' ∈ sx5 then
      if y''' ∈ sx6 then
      if y'' ∈ sx7 then
      if y' ∈ sx8 then
      if  x'''' ∈ sy1 then
      if x''' ∈ sy2 then
      if x'' ∈ sy3 then
      if x' ∈ sy4 then
      if x ∈ sy5 then
cond_prob p T' (y5 x ∩ y4 x') * cond_prob p (y5 x) (y1 x'''' ∩ y3 x'') *
          cond_prob p (y4 x') (x7 y'' ∩ x8 y') * cond_prob p (y3 x'') (y2 x''' ∩ x3 z'') *
          cond_prob p (y2 x''') (x4 z' ∩ (x6 y''' ∩ x5 y'''')) * cond_prob p (y1 x'''') (x2 z''' ∩ x1 z'''') *
          prob p (x8 y') * prob p (x7 y'') * prob p (x6 y''') * prob p (x5 y'''') * prob p (x4 z') *
          prob p (x3 z'') * prob p (x2 z''') * prob p (x1 z'''')
else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
     else 0
     else 0)`

>- (rw[]
   \\ sg `(T' ∩ y5 x ∩ y4 x' ∩ y3 x'' ∩ y2 x''' ∩ y1 x'''' ∩ x8 y' ∩
          x7 y'' ∩ x6 y''' ∩ x5 y'''' ∩ x4 z' ∩ x3 z'' ∩ x2 z''' ∩ x1 z'''')
       =
     (T' ∩ y5 x ∩ y4 x' ∩ y3 x'' ∩ y2 x''' ∩ y1 x'''' ∩ x8 y' ∩
          x7 y'' ∩ x6 y''' ∩ x5 y'''' ∩ x4 z' ∩ x3 z'' ∩ x2 z''' ∩ x1 z'''') INTER p_space p`
    >- (once_rewrite_tac[EQ_SYM_EQ]
       \\ rewrite_tac[Once INTER_COMM]
       \\ DEP_REWRITE_TAC[INTER_PSPACE,EVENTS_INTER]
       \\ fs[pred_list_events_space_def,pred_events_space_def] \\ metis_tac[])
    \\ pop_orw
    \\ DEP_REWRITE_TAC[Prob_BN_cell_inject]
    \\ fs[pos_prob_drug_inj_sys_def,pred_list_events_space_def,pred_events_space_def] \\ metis_tac[])
\\ pop_orw
\\ metis_tac[]);

(*-------------------------------*)
val drug_injec_sys_sigma_def = Define
`drug_injec_sys_sigma p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T' sx1 sx2 sx3 sx4 sx5 sx6 sx7
         sx8 sy1 sy2 sy3 sy4 sy5 =
SIGMA (λx. SIGMA (λx'. SIGMA (λx''. SIGMA (λx'''. SIGMA (λx''''. SIGMA (λy'.
SIGMA (λy''. SIGMA (λy'''. SIGMA (λy''''. SIGMA (λz'. SIGMA (λz''. SIGMA (λz'''. SIGMA (λz''''.
      if z'''' IN sx1 then
      if z''' ∈ sx2 then
      if z'' ∈ sx3 then
      if z' ∈ sx4 then
      if y'''' ∈ sx5 then
      if y''' ∈ sx6 then
      if y'' ∈ sx7 then
      if y' ∈ sx8 then
      if  x'''' ∈ sy1 then
      if x''' ∈ sy2 then
      if x'' ∈ sy3 then
      if x' ∈ sy4 then
      if x ∈ sy5 then
    cond_prob p T' (y5 x ∩ y4 x') * cond_prob p (y5 x) (y1 x'''' ∩ y3 x'') *
          cond_prob p (y4 x') (x7 y'' ∩ x8 y') * cond_prob p (y3 x'') (y2 x''' ∩ x3 z'') *
          cond_prob p (y2 x''') (x4 z' ∩ (x6 y''' ∩ x5 y'''')) * cond_prob p (y1 x'''') (x2 z''' ∩ x1 z'''') *
          prob p (x8 y') * prob p (x7 y'') * prob p (x6 y''') * prob p (x5 y'''') * prob p (x4 z') *
          prob p (x3 z'') * prob p (x2 z''') * prob p (x1 z'''')
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
     else 0
     else 0)
   sx1) sx2) sx3) sx4) sx5) sx6) sx7) sx8) sy1) sy2) sy3) sy4) sy5`;

(*------------------------*)
val fail_prob_drug_inject_alt = store_thm("fail_prob_drug_inject_alt",
  ``!p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T' sx1 sx2 sx3 sx4 sx5 sx6 sx7 sx8 sy1 sy2 sy3 sy4 sy5.
prob_space p /\
pos_prob_drug_inj_sys p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T' /\
(T' IN events p) /\
 (pred_list_events_space p
 [(y5,sy5);(y4,sy4);(y3,sy3);(y2,sy2);(y1,sy1);(x8,sx8);
  (x7,sx7);(x6,sx6);(x5,sx5);(x4,sx4);(x3,sx3);(x2,sx2);
  (x1,sx1)]) ==>
(prob p T' =
 drug_injec_sys_sigma p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T'
   sx1 sx2 sx3 sx4 sx5 sx6 sx7 sx8 sy1 sy2 sy3 sy4 sy5)``,
rw[drug_injec_sys_sigma_def,fail_prob_drug_inject]
\\ metis_tac[]);


(*-------------------------*)

val cell_inject_sigma_def = Define
`cell_inject_sigma p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T' sx1 sx2 sx3 sx4 sx5 sx6 sx7 sx8 sy1 sy2 sy3 sy4 sy5 =
SIGMA
     (λx.
          SIGMA
            (λx'.
                 SIGMA
                   (λx''.
			SIGMA
			  (\x'''.
				SIGMA
				  (\x''''.
					 SIGMA
					   (\y'.
						SIGMA
						  (\y''.
							SIGMA
							  (\y'''.
								SIGMA
								  (\y''''.
									SIGMA
									  (\y'''''.
										SIGMA
										  (\z'.
										     SIGMA
										       (\z''.
											    SIGMA
										    	      (\z'''.
										prob p (T' ∩ y5 x ∩ y4 x' ∩ y3 x'' INTER y2 x''' INTER y1 x'''' INTER x8 y' INTER x7 y'' INTER x6 y''' INTER x5 y'''' INTER x4 y''''' INTER x3 z' INTER x2 z'' INTER x1 z''' INTER p_space p))
										       	     sx1)
										     sx2)
										sx3)
									 sx4)
						  		  sx5)
							  sx6)
						  sx7)
					   sx8)				
				sy1)
			   sy2)
	            sy3)
	     sy4)
      sy5`;


(*
`OR_CPT_table p y5 y4 T' [(0,0);(0,1);(1,0);(1,1)] /\
OR_CPT_table p y1  y3 (y5 1) [(0,0);(0,1);(1,0);(1,1)] /\
OR_CPT_table p x7 x8 (y4 1) [(0,0);(0,1);(1,0);(1,1)] /\
OR_CPT_table p y2 x3 (y3 1) [(0,0);(0,1);(1,0);(1,1)] /\
OR_CPT_table p x2 x1 (y1 1) [(0,0);(0,1);(1,0);(1,1)] /\
OR3_CPT_table p x4 x6 (y2 1) x5  [(0:num,0,0);(0,1,0);(1,0,0);(1,1,0);(0:num,0,1);(0,1,1);(1,0,1);(1,1,1)] ==>
(cond_prob p (x1 1) (T') = ((cell_inject_sigma p (x1:num -> 'a set) (x2:num -> 'a set) x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T' {1:num} {0;1:num} {0;1:num} {0;1:num} {0;1:num}  {0;1:num} {0;1:num} {0;1:num}  {0;1:num} {1:num} {1:num} {1:num} {1:num}) / prob p (T')))`

\\ once_rewrite_tac[REAL_SUM_IMAGE_THM]
\\ rw[REAL_SUM_IMAGE_INSERT_alt,DELETE_DEF,REAL_SUM_IMAGE_SING]
\\ rw[DELETE_DEF]
rw[REAL_SUM_IMAGE_SING,REAL_SUM_IMAGE_INSERT_alt]
*)
(*-----------*)
(*-----------*)
val posterior_prob_x1_given_T = store_thm("posterior_prob_x1_given_T",
  ``!p (x1:num -> 'a set) (x2:num -> 'a set) (x3:num -> 'a set) (x4:num -> 'a set) (x5:num -> 'a set) (x6:num -> 'a set)
  (x7:num -> 'a set) (x8:num -> 'a set) (y1:num -> 'a set) (y2:num -> 'a set) (y3:num -> 'a set) (y4:num -> 'a set)
  (y5:num -> 'a set) (T':'a set) (sx2:num set) (sx3:num set) (sx4:num set) (sx5:num set) (sx6:num set) (sx7:num set)
  (sx8:num set) (sy1:num set) (sy2:num set) (sy3:num set) (sy4:num set) (sy5:num set).
(prob_space p ∧
 pos_prob_drug_inj_sys p (x1) x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T' /\
T' ∩ x1 1 ∈ events p ∧
T' ∈ events p ∧
    pred_list_events_space p
      [(y5,sy5); (y4,sy4); (y3,sy3); (y2,sy2); (y1,sy1); (x8,sx8); (x7,sx7);
       (x6,sx6); (x5,sx5); (x4,sx4); (x3,sx3); (x2,sx2); (x1,{1})]) /\
0 < prob p T' ==> 
(cond_prob p (x1 1) (T') =
 drug_injec_sys_sigma p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T'
            {1:num} sx2 sx3 sx4 sx5 sx6 sx7 sx8 sy1 sy2 sy3 sy4 sy5 / prob p (T'))``,
rw[cond_prob_def]
\\ mp_tac(Q.ISPECL[`(p :α set # α set set # (α set -> real))`,`(x1):num -> 'a set`,`(x2):num -> 'a set`,
   		    `(x3):num -> 'a set`,`(x4):num -> 'a set`,`(x5):num -> 'a set`,`(x6):num -> 'a set`,
		    `(x7):num -> 'a set`,`(x8):num -> 'a set`,`(y1):num -> 'a set`,`(y2):num -> 'a set`,
		    `(y3):num -> 'a set`,`(y4):num -> 'a set`,`(y5):num -> 'a set`,`T' INTER (x1 (1:num))`,
		    `{1:num}`,`sx2:num set`,`sx3:num set`,`sx4:num set`,`sx5:num set`,`sx6:num set`,
		    `sx7:num set`,`sx8:num set`,`sy1:num set`,`sy2:num set`,`sy3:num set`,`sy4:num set`,
		    `sy5:num set`] fail_prob_drug_inject_lemma)
\\ rw[]
\\ rewrite_tac[Once INTER_COMM]
\\ pop_orw
\\ sg `!x x' x'' x''' x''' x'''' y' y'' y''' y'''' y''''' z' z'' z''' z''''.
      	  (T' ∩ x1 1 ∩ y5 x ∩ y4 x' ∩ y3 x'' ∩ y2 x''' ∩ y1 x'''' ∩ x8 y' ∩ x7 y'' ∩
	   x6  y''' ∩ x5  y'''' ∩  x4 z' ∩ x3 z'' ∩ x2 z''' ∩ x1 1) =
	  (T' ∩ y5 x ∩ y4 x' ∩ y3 x'' ∩ y2 x''' ∩ y1 x'''' ∩ x8 y' ∩ x7 y'' ∩
	   x6  y''' ∩ x5  y'''' ∩  x4 z' ∩ x3 z'' ∩ x2 z''' ∩ x1 1)`
>- (rw[EXTENSION,INTER_DEF] \\ metis_tac[])
\\ pop_orw
\\  sg `!x x' x'' x''' x''' x'''' y' y'' y''' y'''' y''''' z' z'' z''' z''''.
    ( if z'''' ∈ {1:num} then
      if z''' ∈ sx2 then
      if z'' ∈ sx3 then
      if z' ∈ sx4 then
      if y'''' ∈ sx5 then
      if y''' ∈ sx6 then
      if y'' ∈ sx7 then
      if y' ∈ sx8 then
      if  x'''' ∈ sy1 then
      if x''' ∈ sy2 then
      if x'' ∈ sy3 then
      if x' ∈ sy4 then
      if x ∈ sy5 then
    prob p (T' ∩ y5 x ∩ y4 x' ∩ y3 x'' ∩ y2 x''' ∩ y1 x'''' ∩ x8 y' ∩
          x7 y'' ∩ x6 y''' ∩ x5 y'''' ∩ x4 z' ∩ x3 z'' ∩ x2 z''' ∩ x1 1)
else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
     else 0
     else 0) =
 ( if z'''' IN {1:num} then
	if z''' ∈ sx2 then
      if z'' ∈ sx3 then
      if z' ∈ sx4 then
      if y'''' ∈ sx5 then
      if y''' ∈ sx6 then
      if y'' ∈ sx7 then
      if y' ∈ sx8 then
      if  x'''' ∈ sy1 then
      if x''' ∈ sy2 then
      if x'' ∈ sy3 then
      if x' ∈ sy4 then
      if x ∈ sy5 then
cond_prob p T' (y5 x ∩ y4 x') * cond_prob p (y5 x) (y1 x'''' ∩ y3 x'') *
          cond_prob p (y4 x') (x7 y'' ∩ x8 y') * cond_prob p (y3 x'') (y2 x''' ∩ x3 z'') *
          cond_prob p (y2 x''') (x4 z' ∩ (x6 y''' ∩ x5 y'''')) * cond_prob p (y1 x'''') (x2 z''' ∩ x1 1) *
          prob p (x8 y') * prob p (x7 y'') * prob p (x6 y''') * prob p (x5 y'''') * prob p (x4 z') *
          prob p (x3 z'') * prob p (x2 z''') * prob p (x1 1)
else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
      else 0
     else 0
     else 0)`

>- (rw[]
   \\ sg `(T' ∩ y5 x ∩ y4 x' ∩ y3 x'' ∩ y2 x''' ∩ y1 x'''' ∩ x8 y' ∩
          x7 y'' ∩ x6 y''' ∩ x5 y'''' ∩ x4 z' ∩ x3 z'' ∩ x2 z''' ∩ x1 1)
       =
     (T' ∩ y5 x ∩ y4 x' ∩ y3 x'' ∩ y2 x''' ∩ y1 x'''' ∩ x8 y' ∩
          x7 y'' ∩ x6 y''' ∩ x5 y'''' ∩ x4 z' ∩ x3 z'' ∩ x2 z''' ∩ x1 1) INTER p_space p`
    >- (once_rewrite_tac[EQ_SYM_EQ]
       \\ rewrite_tac[Once INTER_COMM]
       \\ DEP_REWRITE_TAC[INTER_PSPACE,EVENTS_INTER]
       \\ fs[pred_list_events_space_def,pred_events_space_def] \\ metis_tac[])
    \\ pop_orw
    \\ DEP_REWRITE_TAC[Prob_BN_cell_inject]
    \\ fs[pos_prob_drug_inj_sys_def,pred_list_events_space_def,pred_events_space_def] \\ metis_tac[])
\\ fs[]
\\ pop_orw
\\ rw[drug_injec_sys_sigma_def]);
(*-------------*)
val posterior_prob_x1_given_T_alt = store_thm("posterior_prob_x1_given_T_alt",
  ``!p (x1:num -> 'a set) (x2:num -> 'a set) (x3:num -> 'a set) (x4:num -> 'a set)
     (x5:num -> 'a set) (x6:num -> 'a set) (x7:num -> 'a set) (x8:num -> 'a set)
     (y1:num -> 'a set) (y2:num -> 'a set) (y3:num -> 'a set) (y4:num -> 'a set)
     (y5:num -> 'a set) (T':'a set) (sx2:num set) (sx3:num set) (sx4:num set)
     (sx5:num set) (sx6:num set) (sx7:num set) (sx8:num set) (sy1:num set)
     (sy2:num set) (sy3:num set) (sy4:num set) (sy5:num set).
prob_space p ∧
pos_prob_drug_inj_sys p (x1) x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T' /\
T' ∈ events p ∧
pred_list_events_space p
      [(y5,sy5); (y4,sy4); (y3,sy3); (y2,sy2); (y1,sy1); (x8,sx8); (x7,sx7);
       (x6,sx6); (x5,sx5); (x4,sx4); (x3,sx3); (x2,sx2); (x1,{1})] /\
0 < prob p T' ==> 
(cond_prob p (x1 1) (T') =
 drug_injec_sys_sigma p x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T'
   {1:num} sx2 sx3 sx4 sx5 sx6 sx7 sx8 sy1 sy2 sy3 sy4 sy5 /
 prob p (T'))``,
rw[]
\\ irule posterior_prob_x1_given_T
\\ rw[] \\ DEP_REWRITE_TAC[EVENTS_INTER]
\\ rw[]
\\ fs[pos_prob_drug_inj_sys_def,pred_list_events_space_def,pred_events_space_def] \\ metis_tac[]);
(*-----------------*)
val _ = export_theory();