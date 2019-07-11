(******************************************************************************)
(*   Directed Acyclic Graph and Mapping to Fault Tree                         *)
(*              by Waqar Ahmed HVG Concordia University, Canada               *)
(*                                                                            *)
(******************************************************************************)


(*app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "numTheory", "dep_rewrite", 
          "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory","probabilityTheory", "measureTheory" ,"real_sigmaTheory","Arith","cond_probTheory","conditional_indepTheory"];
*)

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory dep_rewrite
     util_probTheory real_sigmaTheory extrealTheory measureTheory probabilityTheory
     Arith cond_probTheory conditional_indepTheory;

open HolKernel boolLib bossLib Parse;

val _ = new_theory "DAG_FT";

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

(*------------*)
(* Directed Acyclic Graph *)

(*-------*)


val edges_def = Define
`edges V = {(x,y) | (x <> y) /\ x IN V /\ y IN V}`;


val is_direct_edges_def = Define
`is_direct_edges D = !x y. (x,y) IN D /\ (y,x) NOTIN D`;


val direct_edges_def = Define
`direct_edges V =
 {x |
 !y. x <> y /\ x IN edges V /\ y IN edges V /\
     ((FST x,SND x) = (SND y, FST y))}`;

val undirect_edges_def = Define
`undirect_edges V = (edges V) DIFF (direct_edges V)`;

val all_edges = store_thm("all_edges",
  ``!s. edges s = (direct_edges s) UNION (undirect_edges s)``,
rw[edges_def,undirect_edges_def,direct_edges_def,EXTENSION]
\\ metis_tac[]);


val node_parents_def = Define
`node_parents a (D:('a->bool)#('a->bool) ->bool) = {b | (b,a) IN D} `;

val set_node_parents_def = Define
`set_node_parents A D = BIGUNION (IMAGE (\a. node_parents a D) A)`;

val node_childs_def = Define
`node_childs a D = {b | (a,b) IN D}`;

val direct_neibr_node_def = Define
`direct_neibr_node a D = (node_parents a D) UNION (node_childs a D)`;

val chain_DAG_def = Define
`chain_DAG x1 x2 x3 D =
 x1 IN (node_parents x2 D) /\ (x3 IN node_childs x2 D)`;

val fork_DAG_def = Define
`fork_DAG x1 x2 x3 D =
 (x1 IN node_childs x2 D) /\ (x3 IN node_childs x2 D)`;

val collider_DAG_def = Define
`collider_DAG x1 x2 x3 D = x1 IN (node_parents x2 D) /\ x2 IN (node_parents x2 D)`;

val no_parents_nodes_def = Define
`no_parents_nodes x D = (node_parents x D = {})`;

val no_parents_prob_ID_def = Define
`no_parents_prob_ID p A D B =
 !x. x IN A /\ (no_parents_nodes x D) ==> (cond_prob p x B = prob p x)`;


val set_node_parents_def = Define
`set_node_parents A V = BIGUNION {(node_parents a V) DIFF A |a | a IN A /\ A SUBSET V}`;


val cond_prob_node_parents_def = Define
`cond_prob_node_parents p A D =
!x y. x IN (node_parents A D) /\ y NOTIN (node_parents A D) ==>
(cond_prob p A (x INTER y) = cond_prob p A x)`;


val inject_sys_DAG_def = Define
`inject_sys_DAG (x1:'a->bool) (x2:'a->bool) x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T' =
{(x1,y1);(x2,y1);(y1,y5);(y5,T');(x3,y3);(y3,y5);(x4,y2);
 (x5,y2);(x6,y2);(y2,y3);(x7,y4);(x8,y4);(y4,T')}`;

val cond_prob_cell_inj_lemma = store_thm("cond_prob_cell_inj_lemma",
  ``ALL_DISTINCT[x1; x2; x3 ;x4; x5; x6; x7; x8; y1; y2; y3; y4; y5; T'] /\ no_parents_prob_ID p {x1;x2} 
  (inject_sys_DAG x1 x2 x3 x4 x5 x6 x7 x8 y1 y2 y3 y4 y5 T') (y1 INTER y2) ==>
(cond_prob p x1 (y1 INTER y2) = prob p x1)``,
rw[no_parents_prob_ID_def]
\\ first_x_assum (match_mp_tac)
\\ rw[]
\\ rw[EXTENSION,no_parents_nodes_def,node_parents_def,inject_sys_DAG_def]);


val is_direct_edges_def = Define
`is_direct_edges D E =  !x. (x IN D = x IN E) /\ (SND x, FST x) NOTIN E`;


val notin_direct_edges_test = store_thm("notin_direct_edges_test",
  ``!a b. ALL_DISTINCT [a;b] ==> (b,a) NOTIN direct_edges {a;b}``,
rw[direct_edges_def,edges_def,EXTENSION,GSPECIFICATION]
\\ RW_TAC std_ss[EXTENSION,GSPECIFICATION]
\\ Q.EXISTS_TAC `(b,a)`
\\ rw[FST,SND]);

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



val fork_DAG_CI_def = Define
`fork_DAG_CI p x1 x2 x3 D = fork_DAG x1 x2 x3 D ==> cond_indep p x1 x2 x3`;


(*-------------------------*)

val _ = type_abbrev ("set", ``:'a -> bool``);

(*-------------------------------*)
val AND_BN_lemma = save_thm ("AND_BN_lemma",
chain_rule_thm |> Q.SPECL[`(p :(α -> bool) # ((α -> bool) -> bool) # ((α -> bool) -> real))`,
                      `(\a. case a of 0 => A | 1 => B | 2 => C | _ => p_space p)`, `3:num`]
	       |> REWRITE_RULE[chain_rule_def,prove (``count 3 = {2;1;0}``,rw[count_def,EXTENSION] \\ metis_tac[])]

	       |> SIMP_RULE (srw_ss())[chain_rule_def,COUNT_SUC,FINITE_COUNT,PROD_IMAGE_REAL_INSERT,count_delete_ID,DELETE_DEF,PROD_IMAGE_REAL]
	       |> REWRITE_RULE[prove (``(count 3 = {2;1;0}) /\ (count 2 = {1;0}) /\ (count 1 = {0}) ``,rw[count_def,EXTENSION] \\ metis_tac[])]
	       |> SIMP_RULE (srw_ss())[INTER_ASSOC,INTER_IDEMPOT]);

(*------*)


val CPT_AND_def = Define
`CPT_AND p A B C =
\ (x:num, y:num). (if (x = 0) /\ (y = 0) then ( cond_prob p C ((A x) INTER (B y)) = 0)
	       	      	     else (if (x = 0) /\ (y = 1) then ( cond_prob p C ((A x) INTER (B y)) = 0)
			     else (if (x = 1) /\ (y = 0) then ( cond_prob p C ((A x) INTER (B y)) = 0)
			     else (if (x = 1) /\ (y = 1) then (cond_prob p C ((A x) INTER (B y)) = 1)
			     else T))))`;

val CPT_AND_list_def = Define
`(CPT_AND_list p A B C [] = T) /\
 (CPT_AND_list p A B C (h::t) = CPT_AND p A B C (FST h,SND h) /\ CPT_AND_list p A B C t)`;


val AND_BN_lemma1 = store_thm("AND_BN_lemma1",
  ``!A B C p.
  prob_space p /\ (0 < prob p A) /\
     (λa:num.
          if a = (0:num) then A
          else if a = (1:num) then B
          else if a = (2:num) then C
          else p_space p) ∈ ({2:num; 1:num; 0:num} -> events p) /\
  indep p A B
  ==> (prob p (C INTER B INTER A) =  cond_prob p C (B INTER A) * prob p B * prob p A)``,
rw[]
\\ sg `(C INTER B INTER A) = p_space p INTER (C INTER B INTER A)`
>- (DEP_REWRITE_TAC[INTER_PSPACE,EVENTS_INTER]
   \\ fs[IN_FUNSET] \\ rw[]
   >- (first_x_assum (mp_tac o Q.SPEC `2`)
      \\ rw[]
      \\ metis_tac[])
   >- (first_x_assum (mp_tac o Q.SPEC `1`)
      \\ rw[]
      \\ metis_tac[])
   \\ metis_tac[])
\\ pop_orw
\\ rewrite_tac[Once INTER_COMM]
\\ DEP_REWRITE_TAC[AND_BN_lemma]
\\ fs[IN_FUNSET]
\\ rw[]
>- (metis_tac[])
>- metis_tac[]
>- (metis_tac[])
\\ once_rewrite_tac[INTER_COMM]
\\ DEP_REWRITE_TAC[INTER_PSPACE,EVENTS_INTER]
\\ rw[]
>- (first_x_assum (mp_tac o Q.SPEC `1`)
   \\ rw[]
   \\ metis_tac[])
>- metis_tac[]
>- metis_tac[]
\\ mp_tac(Q.ISPECL[`B:'a set`,`A:'a set`] cond_prob_alt)
\\ rw[]
\\ once_rewrite_tac[INTER_COMM]
\\ fs[indep_def]
\\ sg `cond_prob p A (p_space p) =  prob p A`
 >- (mp_tac(Q.ISPECL[`A:'a set`,`p_space p :'a set`] cond_prob_alt)
    \\ rw[]
    \\ fs[PROB_UNIV]
    \\ once_rewrite_tac[INTER_COMM]
    \\ DEP_REWRITE_TAC[INTER_PSPACE,EVENTS_INTER]
    \\ rw[])
\\ pop_orw
\\ rewrite_tac[Once INTER_COMM]
\\ rewrite_tac[GSYM REAL_MUL_ASSOC]
\\ once_rewrite_tac[REAL_MUL_COMM]
\\ DEP_REWRITE_TAC[REAL_EQ_RMUL]
\\ disj2_tac
\\ disj2_tac
\\ DEP_REWRITE_TAC[REAL_EQ_LDIV_EQ]
\\ metis_tac[REAL_MUL_COMM]);

(*-------*)
val REAL_SUM_IMAGE_INSERT_alt = store_thm("REAL_SUM_IMAGE_INSERT_alt",
  ``∀f e s. FINITE s ⇒ (REAL_SUM_IMAGE f (e INSERT s) = f e + REAL_SUM_IMAGE f (s DELETE e))  ``,
metis_tac[REAL_SUM_IMAGE_THM]);

(*-------*)

val PROB_REAL_SUM_IMAGE_FN_alt = store_thm("PROB_REAL_SUM_IMAGE_FN_alt",
  ``∀s e f p.
         prob_space p ∧ e ∈ events p ∧ (∀x. x ∈ s ⇒ e ∩ f x ∈ events p) ∧
         FINITE s ∧ (∀x y. x ∈ s ∧ y ∈ s ∧ x ≠ y ⇒ DISJOINT (f x) (f y)) ∧
         (BIGUNION (IMAGE f s) ∩ p_space p = p_space p) ⇒
         (prob p e = REAL_SUM_IMAGE (λx. prob p (e ∩ f x)) (s:num set))  ``,
metis_tac[PROB_REAL_SUM_IMAGE_FN]);

(*------*)
val AND_BN_thm = store_thm("AND_BN_thm",
  ``!A B C p.
  prob_space p /\
CPT_AND_list p A B C [(0,0);(0,1);(1,0);(1,1)] /\
C IN events p /\
(!x x'.
    (0 < prob p (A x')) ∧
    indep p (A x') (B x)) /\
pred_events_space p B {0;1:num} /\
pred_events_space p A {0;1:num} ==>
(prob p (C) =  prob p (B (1:num)) * prob p (A (1:num)))``,
rw[]
\\  mp_tac(Q.ISPECL[`{0;1}:num set`,`C:'a set`,`B:num -> 'a set`] PROB_REAL_SUM_IMAGE_FN_alt)
\\ rw[]
\\ DEP_ASM_REWRITE_TAC[]
\\ rw[]
>- (fs[pred_events_space_def,IN_FUNSET]
   \\ DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[])
>- (fs[pred_events_space_def]
   \\ DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[])
>- (fs[pred_events_space_def]
   \\ DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[])
>- (fs[pred_events_space_def]
   \\ DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[])
>- (fs[pred_events_space_def]
   \\ DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[])
\\ sg `!x.  (if (x IN {0;1:num}) then prob p (C ∩ B x) else 0) = REAL_SUM_IMAGE (\x'.  if (x IN {0;1:num}) then prob p (C ∩ B x INTER A x') else 0) ({0;1}:num set)`
>- (rw[]
   >- (HO_MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
      \\ rw[]
      >- (fs[pred_events_space_def]
      	 \\ DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[])
      >- (fs[pred_events_space_def]
      	 \\ DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[])
      >- (fs[pred_events_space_def]
      	 \\ DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[])
      >- (fs[pred_events_space_def]
      	 \\ DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[])
      >- (fs[pred_events_space_def]
      	 \\ DEP_REWRITE_TAC[EVENTS_INTER] \\ metis_tac[])
      \\ (fs[pred_events_space_def]
      	 \\ DEP_REWRITE_TAC[EVENTS_INTER,INTER_PSPACE] \\ metis_tac[]))
   >- (HO_MATCH_MP_TAC PROB_REAL_SUM_IMAGE_FN
      \\ rw[]\\ fs[pred_events_space_def]
      	 \\ DEP_REWRITE_TAC[EVENTS_INTER,INTER_PSPACE] \\ metis_tac[]) 
   \\ rw[REAL_SUM_IMAGE_0])
\\ DEP_ONCE_REWRITE_TAC[REAL_SUM_IMAGE_IN_IF]
\\ pop_orw
\\  DEP_REWRITE_TAC[REAL_SUM_IMAGE_INSERT_alt,REAL_SUM_IMAGE_SING]
\\ rw[DELETE_DEF]
\\  DEP_REWRITE_TAC[REAL_SUM_IMAGE_INSERT_alt]
\\ rw[DELETE_DEF]
\\ rw[REAL_SUM_IMAGE_SING,REAL_SUM_IMAGE_THM ]
\\ DEP_REWRITE_TAC[ AND_BN_lemma1]
\\ rw[IN_FUNSET]
\\ fs[IN_FUNSET,pred_events_space_def]
\\ DEP_REWRITE_TAC[EVENTS_INTER,INTER_PSPACE]
\\ fs[CPT_AND_list_def,pred_events_space_def,CPT_AND_def]
\\ once_rewrite_tac[INTER_COMM]
\\ rw[] \\ metis_tac[]);





val OR_CPT_def = Define
`OR_CPT p  A B C =
         (λ(x:num,y:num).
              if (x = 0) ∧ (y = 0) then cond_prob p C (A x ∩ B y) = 0
              else if (x = 0) ∧ (y = 1) then cond_prob p C (A x ∩ B y) = 1
              else if (x = 1) ∧ (y = 0) then cond_prob p C (A x ∩ B y) = 1
              else if (x = 1) ∧ (y = 1) then cond_prob p C (A x ∩ B y) = 1
              else T)`;

val OR_CPT_table_def = Define
`(OR_CPT_table p A B C [] = T) /\
(OR_CPT_table p A B C (h::t) =
 OR_CPT p A B C (FST h,SND h) /\ OR_CPT_table p A B C t)`;


val OR3_CPT_def = Define
`OR3_CPT p A B C D =
         (λ(x:num,y:num,z:num).
              if (x = 0) ∧ (y = 0) /\ (z = 0) then cond_prob p C (A x ∩ B y INTER D z) = 0
              else if (x = 0) ∧ (y = 1) /\ (z = 0) then cond_prob p C (A x ∩ B y INTER D z) = 1
              else if (x = 1) ∧ (y = 0) /\ (z = 0) then cond_prob p C (A x ∩ B y INTER D z) = 1
              else if (x = 1) ∧ (y = 1) /\ (z =0) then cond_prob p C (A x ∩ B y INTER D z) = 1
	      else if (x = 0) ∧ (y = 0) /\ (z = 1) then cond_prob p C (A x ∩ B y INTER D z) = 1
              else if (x = 0) ∧ (y = 1) /\ (z = 1) then cond_prob p C (A x ∩ B y INTER D z) = 1
              else if (x = 1) ∧ (y = 0) /\ (z = 1) then cond_prob p C (A x ∩ B y INTER D z) = 1
              else if (x = 1) ∧ (y = 1) /\ (z = 1) then cond_prob p C (A x ∩ B y INTER D z) = 1
              else T)`;

val OR3_CPT_table_def = Define
`(OR3_CPT_table p A B C D [] = T) /\
(OR3_CPT_table p A B C D ((h1,h2,h3)::t) =
 OR3_CPT p A B C D (h1,h2,h3) /\ OR3_CPT_table p A B C D t)`;

(*-----------*)

(*-----------------*)
val _ = export_theory();