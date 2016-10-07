(* *********************************************************************)
(*                                                                     *)
(*              The L2C verified compiler                              *)
(*                                                                     *)
(*            L2C Group, Tsinghua University                           *)
(*                                                                     *)
(*  Copyright Tsinghua University.  All rights reserved.  This file is *)
(*  distributed under the terms of the GNU General Public License as   *)
(*  published by the Free Software Foundation, either version 2 of the *)
(*  License, or (at your option) any later version.  This file is also *)
(*  distributed under the terms of the INRIA Non-Commercial License    *)
(*  Agreement.                                                         *)
(*                                                                     *)
(* *********************************************************************)

(** The whole compiler and its proof of semantic preservation *)

(** Libraries. *)
Require Import Coqlib.
Require Import Errors.
Require Import AST.
(** Languages (syntax and semantics). *)
Require Import Lident.
Require Import Lustre.
Require LustreS.
Require LustreR.
Require LustreF.
Require Lenv.
Require Lsem.
Require LsemT.
Require LsemS.
Require LsemF.
Require LsemD.
Require Clight.
Require ClightBigstep.
(** Translation passes. *)
Require LustreSGen.
Require Toposort.
Require LustreRGen.
Require TransMainArgs.
Require TransTypecmp.
Require LustreFGen.
Require OutstructGen.
Require ClassifyRetsVar.
Require ResetfuncGen.
Require SimplEnv.
Require ClassifyArgsVar.
Require CtempGen.
Require ClightGen.

(** Proofs of semantic preservation and typing preservation. *)
Require ToposortNodesProof.
Require ToposortStmtsProof.
Require Lu2ltProof.
Require Lt2lsProof.
Require LustreRGenProof.
Require TransMainArgsProof.
Require TransTypecmpProof.
Require LustreFGenProof.
Require OutstructGenProof.
Require ClassifyRetsVarProof.
Require ResetfuncGenProof.
Require SimplEnvProof.
Require ClassifyArgsVarProof.
Require CtempGenProof.
Require ClightGenProof.

(** Pretty-printers (defined in Caml). *)
Parameter print_LustreT: LustreS.program -> unit.
Parameter print_LustreS: LustreS.program -> unit.
Parameter print_LustreR1: LustreR.program -> unit.
Parameter print_LustreR2: LustreR.program -> unit.
Parameter print_LustreR3: LustreR.program -> unit.
Parameter print_LustreF1: LustreF.program -> unit.
Parameter print_LustreF2: LustreF.program -> unit.
Parameter print_LustreE1: LustreF.program -> unit.
Parameter print_LustreE2: LustreF.program -> unit.
Parameter print_LustreD: LustreF.program -> unit.
Parameter print_LustreC: LustreF.program -> unit.
Parameter print_Ctemp: Ctemp.program -> unit.

Open Local Scope string_scope.

(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

Definition transf_ldc_program (d: LustreF.program)
  : res Clight.program :=
   OK d
   @@ print print_LustreD
  @@@ ClassifyArgsVar.trans_program
   @@ print print_LustreC
   @@ CtempGen.trans_program
   @@ print print_Ctemp
   @@ ClightGen.trans_program.

Definition transf_lrd_program (r: LustreR.program)
  : res LustreF.program :=
   OK r
   @@ print print_LustreR3
   @@ LustreFGen.trans_program
   @@ print print_LustreF1
  @@@ OutstructGen.trans_program
   @@ print print_LustreF2
   @@ ClassifyRetsVar.trans_program
   @@ print print_LustreE1
  @@@ ResetfuncGen.trans_program
   @@ print print_LustreE2
  @@@ SimplEnv.trans_program.

Definition transf_lsr_program (p: LustreS.program)
  : res LustreR.program :=
  OK p
  @@@ LustreRGen.trans_program
   @@ print print_LustreR1
  @@@ TransMainArgs.trans_program
   @@ print print_LustreR2
  @@@ TransTypecmp.trans_program.

Definition transf_lts_program (p: LustreS.program)
  : res LustreS.program :=
  OK p
   @@ print print_LustreT
  @@@ Toposort.toposort_nodes_program
  @@@ Toposort.toposort_stmts_program
   @@ print print_LustreS.

Definition transf_lt_program (p: LustreS.program)
  : res Clight.program :=
  OK p
  @@@ transf_lts_program
  @@@ transf_lsr_program
  @@@ transf_lrd_program
  @@@ transf_ldc_program.

(** The following lemmas help reason over compositions of passes. *)

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. destruct (printer prog); auto.
Qed.

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit),
  x @@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto.
Qed.

Section CORRECTNESS.


Theorem transf_lts_program_correct:
  forall prog1 prog2 gc e main1 vass vrss maxn,
  transf_lts_program prog1 = OK prog2 ->
  LustreS.ids_range ACG_B (Lustre.node_block prog1) ->
  ids_plt ACG_EQU (globidspltof prog1) ->
  list_norepet (globidsof prog1) ->
  Lenv.initial_state prog1 gc LsemT.init_node main1 e->
  Lenv.exec_prog prog1 gc (LsemT.eval_node true) main1 e 1 maxn vass vrss ->
  exists main2, Lenv.initial_state prog2 gc LsemT.init_node main2 e
    /\ Lenv.exec_prog prog2 gc (LsemT.eval_node false) main2 e 1 maxn vass vrss
    /\ topo_sorted (Toposort.deps_of_nodes (node_block prog2))
    /\ LustreS.ids_range ACG_B (Lustre.node_block prog2)
    /\ ids_plt ACG_EQU (globidspltof prog2)
    /\ list_norepet (globidsof prog2)
    /\ nd_rets (snd main1) = nd_rets (snd main2)
    /\ nd_args (snd main1) = nd_args (snd main2).
Proof.
  intros. unfold transf_lts_program in H.
  repeat rewrite compose_print_identity in H.
  simpl in H.

  destruct (Toposort.toposort_nodes_program prog1) eqn:?; simpl in *; try congruence.
  eapply ToposortNodesProof.trans_program_correct in H4; eauto.
  destruct H4 as [A A1].
  apply Toposort.toposort_nodes_program_ids_range with (p':=p) in H0; auto.

  destruct (Toposort.toposort_stmts_program p) eqn:?; simpl in *; try congruence.
  eapply ToposortStmtsProof.trans_program_correct in A; eauto.
  destruct A as [main2 [A [A2 [A3 A4]]]].
  eapply Toposort.toposort_stmts_program_ids_range in H0; eauto.

  eapply Lu2ltProof.exec_prog_correct in A2; eauto.

  inv H. exists main2. repeat (split; auto).
  +apply ToposortStmtsProof.toposort_stmts_nodes_topo_sorted with p; auto.
   eapply ToposortNodesProof.toposort_nodes_program_topo_sorted; eauto.
  +eapply Toposort.toposort_stmts_program_gids_range; eauto.
   eapply Toposort.toposort_nodes_program_gids_range; eauto.
  +rewrite ToposortStmtsProof.toposort_stmts_program_globids with p prog2; auto.
   eapply ToposortNodesProof.toposort_nodes_program_globids_norepet; eauto.
  +intros. eapply ToposortStmtsProof.toposort_stmts_program_topo_sorted; eauto.
Qed.

Theorem transf_lsr_program_correct:
  forall prog1 prog2 gc e main1 vass vrss maxn,
  transf_lsr_program prog1 = OK prog2 ->
  list_norepet (globidsof prog1) ->
  LustreS.ids_range ACG_B (Lustre.node_block prog1) ->
  ids_plt ACG_EQU (globidspltof prog1) ->
  topo_sorted (Toposort.deps_of_nodes (node_block prog1)) ->
  Lenv.initial_state prog1 gc LsemT.init_node main1 e->
  Lenv.exec_prog prog1 gc (LsemT.eval_node false) main1 e 1 maxn vass vrss ->
  forall mass,
  Lenv.vargs_matchss (Lustre.nd_args (snd main1)) vass mass ->
  exists main2, Lenv.initial_state1 prog2 gc LsemR.init_node main2 e
    /\ Lenv.exec_prog1 prog2 gc (LsemR.eval_node false) main2 e 1 maxn mass vrss
    /\ LustreR.ids_range ACG_INIT (node_block prog2)
    /\ ids_plt ACG_EQU (map fst (const_block prog2)++ map fst (node_block prog2))
    /\ list_norepet (globidsof prog2)
    /\ nd_rets (snd main1) = nd_rets (snd main2)
    /\ nd_kind (snd main2) = true.
Proof.
  intros. unfold transf_lsr_program in H.
  repeat rewrite compose_print_identity in H.
  simpl in H.

  eapply Lt2lsProof.exec_prog_correct in H5; eauto.

  remember (LustreRGen.trans_program prog1) as t2.
  destruct t2; simpl in H; try congruence.
  eapply LustreRGenProof.trans_program_correct in H5; eauto.
  destruct H5 as [main3 [? [? [? A]]]].

  apply Toposort.topo_sorted_nodes_simpl in H3.
  erewrite LustreRGen.trans_program_deps_of_nodes in H3; eauto.
  erewrite <-LustreRGen.trans_program_globidspltof in H2; eauto.

  destruct (TransMainArgs.trans_program p) eqn:?; simpl in *; try congruence.
  eapply TransMainArgsProof.trans_program_correct with (mass:=mass) in A; eauto.
  erewrite <-TransMainArgs.trans_program_globidspltof in H2; eauto.
  destruct A as [main4 [? [? [? A]]]].

  eapply TransTypecmpProof.trans_program_node_correct in A; eauto.
  destruct A as [main5 [? [A [? ?]]]].

  exists main5. inv H. repeat (split; auto); try congruence.
  +eapply TransTypecmp.trans_program_ids_range; eauto.
   eapply TransMainArgs.trans_program_ids_range; eauto.
   eapply LustreRGen.trans_program_ids_range; eauto.
  +erewrite <-TransTypecmp.trans_program_ids_plt with (p:=p0); eauto.
  +eapply TransTypecmp.trans_program_gids_norepet; eauto.
   eapply TransMainArgs.trans_program_gids_norepet; eauto.
   erewrite LustreRGen.trans_program_gids_eq; eauto.
  +eapply LustreRGen.trans_program_ids_range; eauto.
  +congruence.
Qed.

Theorem transf_lrd_program_node_correct:
  forall prog1 prog2 gc e1 main1 mass vrss maxn,
  transf_lrd_program prog1 = OK prog2 ->
  LustreR.ids_range ACG_INIT (Lustre.node_block prog1) ->
  ids_plt ACG_EQU (map fst (const_block prog1)++ map fst (node_block prog1)) ->
  list_norepet (globidsof prog1) ->
  Lenv.initial_state1 prog1 gc LsemR.init_node main1 e1 ->
  nd_kind (snd main1) = true ->
  Lenv.exec_prog1 prog1 gc (LsemR.eval_node false) main1 e1 1 maxn mass vrss ->
  exists mrss main2 e2, LsemD.initial_state prog2 gc LsemD.eval_node main2 e2
    /\ LsemD.exec_prog prog2 gc LsemD.eval_node main2 e2 1 maxn mass mrss
    /\ Lenv.vrets_matchss (Lustre.nd_rets (snd main1)) vrss mrss
    /\ list_norepet (globidsof prog2)
    /\ ids_plt ACG_EQU (map fst (const_block prog2))
    /\ LustreF.ids_range ACG_MEMCPY (node_block prog2).
Proof.
  intros. unfold transf_lrd_program in H.
  repeat rewrite compose_print_identity in H.
  simpl in H.

  eapply LustreFGenProof.trans_program_correct in H5; eauto.
  destruct H5 as [? [? [A [? ?]]]].
  erewrite <-LustreFGen.trans_program_gids_norepet in H2; eauto.
  erewrite LustreFGen.trans_program_const_block in H1; eauto.

  destruct (OutstructGen.trans_program _) eqn:?; simpl in H; try congruence.
  eapply OutstructGenProof.trans_program_node_correct in A; eauto.
  destruct A as [main3 [? [A [? [? ?]]]]].
  eapply OutstructGen.trans_program_ids_plt in H1; eauto.
  eapply OutstructGen.trans_program_gids_norepet in H2; eauto.

  eapply ClassifyRetsVarProof.trans_program_correct in A; eauto.
  destruct A as [main4 [e2 [? [A [? [? ?]]]]]].
  rewrite <-ClassifyRetsVar.trans_program_gids in H2.

  destruct (ResetfuncGen.trans_program _) eqn:?; simpl in *; try congruence.
  eapply ResetfuncGenProof.trans_program_node_correct  in A; eauto.
  destruct A as [? A].
  eapply ResetfuncGen.trans_program_gids_norepet in H2; eauto.

  cut (ids_plt ACG_EQU (map fst (const_block p0))). intros.
  cut (LustreF.ids_range OUTSTRUCT (node_block p0)). intros.
  apply SimplEnvProof.trans_program_correct with (prog2:=prog2) in A; eauto.
  destruct A as [mrss [main5 [e3 [? [A ?]]]]].
  exists mrss, main5, e3. split; [| split; [| split; [| split; [| split]]]]; auto.
  -unfold LustreF.func in *. congruence.
  -erewrite SimplEnv.trans_program_gids_norepet; eauto.
  -monadInv H; auto.
  -eapply SimplEnv.trans_program_ids_range; eauto.
  -unfold LustreF.func in *. congruence.
  -eapply ResetfuncGen.trans_program_ids_range; eauto.
   eapply ClassifyRetsVar.trans_program_ids_range; eauto.
   eapply OutstructGen.trans_program_ids_range; eauto.
   eapply LustreFGen.trans_program_ids_range; eauto.
   apply LustreR.ids_range_le with ACG_INIT; auto.
   unfold Ple, OUTSTRUCT, ACG_INIT. omega.
  -unfold ResetfuncGen.trans_program in Heqr0.
   destruct (list_in_list _ _); inv Heqr0. auto.
Qed.

Theorem transf_ldc_program_correct:
  forall prog1 prog2 gc e main vass vrss maxn,
  transf_ldc_program prog1 = OK prog2 ->
  list_norepet (globidsof prog1) ->
  ids_plt ACG_EQU (map fst (const_block prog1)) ->
  LustreF.ids_range ACG_MEMCPY (node_block prog1) ->
  LsemD.initial_state prog1 gc LsemD.eval_node main e ->
  LsemD.exec_prog prog1 gc LsemD.eval_node main e 1 maxn vass vrss ->
  exists mainC bi bo m, Csem.initial_state prog2 bi bo mainC m
    /\ Csem.exec_prog prog2 bi bo mainC m 1 maxn vass vrss.
Proof.
  intros. unfold transf_ldc_program in H.
  repeat rewrite compose_print_identity in H.
  simpl in H.

  remember (ClassifyArgsVar.trans_program prog1) as t1.
  destruct t1; simpl in *; try congruence.
  eapply ClassifyArgsVarProof.trans_program_correct in H2; eauto.
  destruct H2 as [main2 [gc2 [A A1]]].

  remember (CtempGen.trans_program p) as progC.
  eapply CtempGenProof.trans_program_correct in A1; eauto.
  destruct A1 as [mainC [bi [bo [m [A2 A3]]]]].

  inv H.
  eapply ClightGenProof.trans_program_correct in A3; eauto.
  destruct A3 as [mainC' [A3 A4]].
  exists mainC', bi, bo, m. split; auto.

  eapply ClassifyArgsVarProof.trans_gids_norepet; eauto.
Qed.

Theorem transf_lt_program_correct:
  forall prog progC gc e main vass vrss mass maxn,
  transf_lt_program prog = OK progC ->
  LustreS.ids_range ACG_B (Lustre.node_block prog) ->
  ids_plt ACG_EQU (globidspltof prog) ->
  list_norepet (globidsof prog) ->
  Lenv.vargs_matchss (Lustre.nd_args (snd main)) vass mass ->
  Lenv.initial_state prog gc LsemT.init_node main e->
  Lenv.exec_prog prog gc (LsemT.eval_node true) main e 1 maxn vass vrss ->
  exists mrss mainC bi bo m, Csem.initial_state progC bi bo mainC m
    /\ Csem.exec_prog progC bi bo mainC m 1 maxn mass mrss
    /\ Lenv.vrets_matchss (Lustre.nd_rets (snd main)) vrss mrss.
Proof.
  intros. unfold transf_lt_program in H.
  repeat rewrite compose_print_identity in H.
  simpl in H.

  destruct (transf_lts_program prog) eqn:?; simpl in *; try congruence.
  eapply transf_lts_program_correct in H5; eauto.
  destruct H5 as [main1 [? [A [? [? [? [? [? ?]]]]]]]].

  destruct (transf_lsr_program p) eqn:?; simpl in *; try congruence.
  rewrite H10,H11 in *.
  eapply transf_lsr_program_correct in A; eauto.
  destruct A as [main2 [? [A [? [? [? [? ?]]]]]]].

  destruct (transf_lrd_program p0) eqn:?; simpl in *; try congruence.
  eapply transf_lrd_program_node_correct in A; eauto.
  destruct A as [mrss [main3 [e2 [? [A [? [? [? ?]]]]]]]].

  eapply transf_ldc_program_correct in A; eauto.
  destruct A as [mainC [bi [bo [m [? A]]]]].
  exists mrss, mainC, bi, bo, m. split; [| split]; auto.
  congruence.
Qed.

End CORRECTNESS.

(** * Semantic preservation *)
