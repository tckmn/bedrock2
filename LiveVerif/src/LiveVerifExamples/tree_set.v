(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.onesize_malloc.
Require Import coqutil.Datatypes.PropSet.

Inductive tree_skeleton: Set :=
| Leaf
| Node(leftChild rightChild: tree_skeleton).

Definition tree_skeleton_lt(sk1 sk2: tree_skeleton): Prop :=
  match sk2 with
  | Node leftChild rightChild => sk1 = leftChild \/ sk1 = rightChild
  | Leaf => False
  end.

Lemma tree_skeleton_lt_wf: well_founded tree_skeleton_lt.
Proof.
  unfold well_founded. intros sk2.
  induction sk2; eapply Acc_intro; intros sk1 Lt; unfold tree_skeleton_lt in Lt.
  - contradiction.
  - destruct Lt; subst; assumption.
Qed.

#[local] Hint Resolve tree_skeleton_lt_wf: wf_of_type.

Lemma tree_skeleton_lt_l: forall sk1 sk2,
    safe_implication True (tree_skeleton_lt sk1 (Node sk1 sk2)).
Proof. unfold safe_implication, tree_skeleton_lt. intros. auto. Qed.

Lemma tree_skeleton_lt_r: forall sk1 sk2,
    safe_implication True (tree_skeleton_lt sk2 (Node sk1 sk2)).
Proof. unfold safe_implication, tree_skeleton_lt. intros. auto. Qed.

#[local] Hint Resolve tree_skeleton_lt_l tree_skeleton_lt_r : safe_implication.

Load LiveVerif.

Context {consts: malloc_constants}.

Fixpoint bst'(sk: tree_skeleton)(s: set Z)(addr: word){struct sk}: mem -> Prop :=
  match sk with
  | Leaf => emp (addr = /[0] /\ forall x, ~ s x)
  | Node skL skR => EX (p: word) (v: Z) (q: word),
      <{ * emp (addr <> /[0])
         * emp (s v)
         * freeable 12 addr
         * <{ + uintptr p
              + uint 32 v
              + uintptr q }> addr
         * bst' skL (fun x => s x /\ x < v) p
         * bst' skR (fun x => s x /\ v < x) q }>
  end.

(* Note: one level of indirection because sometimes we have to change the root
   pointer (eg from null (empty) to non-null or vice versa) *)
Definition bst(s: set Z)(addr: word): mem -> Prop :=
  EX rootp, <{ * uintptr rootp addr
               * EX sk: tree_skeleton, bst' sk s rootp }>.

Local Hint Extern 1 (PredicateSize (bst' ?sk)) =>
  let r := eval cbv iota in
    (match sk with
     | Node _ _ => 12
     | Leaf => 0
     end) in
  exact r
: typeclass_instances.

#[local] Hint Extern 1 (cannot_purify (bst' _ _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (bst _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (freeable _ _))
      => constructor : suppressed_warnings.

#[local] Hint Unfold bst : heapletwise_always_unfold.

(* TODO move *)
#[local] Hint Extern 1 (cannot_purify (uint _ ? _))
      => constructor : suppressed_warnings.

Lemma invert_bst'_null{sk s p m}:
    p = /[0] ->
    m |= bst' sk s p ->
    sk = Leaf /\
    m |= emp (forall x, ~ s x).
Proof.
  unfold with_mem. intros. subst. destruct sk; simpl in *.
  - unfold emp in *. intuition auto.
  - repeat heapletwise_step. exfalso. apply H1. reflexivity.
Qed.

Lemma invert_bst'_nonnull{sk s p m}:
    p <> /[0] ->
    m |= bst' sk s p ->
    exists skL skR pL v pR,
      sk = Node skL skR /\
      s v /\
      <{ * freeable 12 p
         * <{ + uintptr pL
              + uint 32 v
              + uintptr pR }> p
         * bst' skL (fun x => s x /\ x < v) pL
         * bst' skR (fun x => s x /\ v < x) pR }> m.
Proof.
  intros.
  destruct sk; simpl in *|-.
  { exfalso. unfold with_mem, emp in *. intuition idtac. }
  repeat heapletwise_step.
  eexists _, _, p0, v, q. split. 1: reflexivity.
  split. 1: eassumption.
  repeat heapletwise_step.
Qed.

  (* TODO use and move or delete *)
  Lemma after_if_skip' b fs (PThen PElse Post: trace -> mem -> locals -> Prop):
    bool_expr_branches b (forall t m l, PThen t m l -> Post t m l)
                         (forall t m l, PElse t m l -> Post t m l) True ->
    @after_if _ _ _ _ _ _ fs b PThen PElse cmd.skip Post.
  Proof.
    intros.
    unfold after_if.
    intros ? ? ? [? ? ?]. subst x.
    eapply wp_skip.
    apply proj1 in H.
    destruct b; eauto.
  Qed.

Definition same_set{A: Type}(s1 s2: set A) := forall x, s1 x <-> s2 x.

Import FunctionalExtensionality PropExtensionality.

Lemma bst'_change_set: forall sk a s1 s2,
    safe_implication (same_set s1 s2) (impl1 (bst' sk s1 a) (bst' sk s2 a)).
Proof.
  unfold safe_implication, same_set. intros.
  replace s2 with s1. 1: reflexivity.
  extensionality x.
  apply propositional_extensionality.
  apply H.
Qed.

#[local] Hint Resolve bst'_change_set : safe_implication.

(* always unify (set A) with (A -> Prop) *)
#[global] Hint Transparent set : safe_implication.

Ltac step_hook ::=
  match goal with
  | |- _ => progress cbn [bst']
  | sk: tree_skeleton |- _ => progress subst sk
  | |- same_set _ _ => reflexivity (* <- might instantiate evars and we're fine with that *)
  | |- same_set _ _ => solve [unfold same_set; intros; split; steps; intuition congruence]
  | H: _ |= bst' _ _ ?p, E: ?p = /[0] |- _ =>
      assert_fails (has_evar H); eapply (invert_bst'_null E) in H
  | H: _ |= bst' _ _ ?p, N: ?p <> /[0] |- _ =>
      assert_fails (has_evar H); eapply (invert_bst'_nonnull N) in H
  | H: ?addr <> /[0] |- context[bst' ?sk_evar _ ?addr] =>
      is_evar sk_evar;
      let n := open_constr:(Node _ _) in unify sk_evar n
  | s: set Z, H: forall x: Z, ~ _ |- _ =>
      lazymatch goal with
      | |- context[s ?v] =>
          lazymatch type of H with
          | context[s] => unique pose proof (H v)
          end
      end
  | |- ?A \/ ?B =>
      tryif (assert_succeeds (assert (~ A) by (zify_goal; xlia zchecker)))
      then right else
      tryif (assert_succeeds (assert (~ B) by (zify_goal; xlia zchecker)))
      then left else fail
  | H1: ?x <= ?y, H2: ?y <= ?x, C: ?s ?x |- ?s ?y =>
      (replace y with x by xlia zchecker); exact C
  | H: _ \/ _ |- _ => decompose [and or] H; clear H; try (exfalso; xlia zchecker); []
  | |- _ => solve [auto 3 with nocore safe_core]
  end.

Ltac predicates_safe_to_cancel_hook hypPred conclPred ::=
  lazymatch conclPred with
  | bst' ?sk2 ?s2 =>
      lazymatch hypPred with
      | bst' ?sk1 ?s1 =>
          (* Note: address has already been checked, and if sk and/or s don't
             unify, sidecondition solving steps will make them match later,
             so here, we just need to take care of instantiating evars from conclPred *)
          try syntactic_unify_only_inst_r s1 s2;
          try syntactic_unify_only_inst_r sk1 sk2
      end
  end.

#[export] Instance spec_of_bst_init: fnspec :=                              .**/

void bst_init(uintptr_t p) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * array (uint 8) 4 ? p
                     * R }> m;
  ensures t' m' := t' = t /\
                   <{ * bst (fun _ => False) p
                      * R }> m' #**/                                       /**.
Derive bst_init SuchThat (fun_correct! bst_init) As bst_init_ok.                .**/
{                                                                          /**. .**/
  store(p, 0);                                                             /**. .**/
}                                                                          /*?.
  step. step. step. step. step. step. step. step.
  instantiate (1 := Leaf).
  steps.
Qed.

#[export] Instance spec_of_bst_add: fnspec :=                              .**/

uintptr_t bst_add(uintptr_t p, uintptr_t vAdd) /**#
  ghost_args := s (R: mem -> Prop);
  requires t m := <{ * allocator
                     * bst s p
                     * R }> m;
  ensures t' m' r := t' = t /\
                     ((\[r] = 0 /\ <{ * allocator_failed_below 12
                                      * bst s p
                                      * R }> m') \/
                      (\[r] = 1 /\ <{ * allocator
                                      * bst (fun x => x = \[vAdd] \/ s x) p
                                      * R }> m')) #**/                     /**.
Derive bst_add SuchThat (fun_correct! bst_add) As bst_add_ok.                   .**/
{                                                                          /**. .**/
  uintptr_t a = load(p);                                                   /**.
  (* invariant: *p = a *)                                                       .**/
  uintptr_t found = 0;                                                     /**.

  pose (measure := sk).
  prove (found = /[0] /\ measure = sk \/ found = /[1] /\ s \[vAdd]) as A.
  move A before sk.
  clearbody measure.
  delete (#(found = /[0])).
  move p after t.
  move sk before t.
  Local Arguments ready : clear implicits.
  loop invariant above a.
  (* Ltac log_packaged_context P ::= idtac P. *)
                                                                                .**/
  while (a != NULL && !found)
    /* initial_ghosts(p, s, sk, R); decreases(measure) */
  {                                                                        /**. .**/
    uintptr_t x = load32(a + 4);                                           /**. .**/
    if (x == vAdd) /* split */ {                                           /**. .**/
      found = 1;                                                           /**. .**/
    }                                                                      /**.
      (* Note: (Node skL skR) doesn't decrease but that's also not the measure *)
      new_ghosts(_, _, Node skL skR , _).

      step. step. step. step. step. step. step. step. step. step. step. step.

Definition not_a_function_pre(P: Prop) := P.

lazymatch goal with
| |- ?A /\ ?B /\ True =>
enough ((not_a_function_pre A /\ True) /\ B) as HH
end.
{ unfold not_a_function_pre. decompose [and] HH. auto. }

step. step.

(* function_pre needs to be default because function specs don't have special
   markers and we can't easily descend into them to change them.
   so TODO we need to add the marker in non_function context, let's add it
   in PackageContext: move_mem_hyp_just_below_scope_marker *)
unfold not_a_function_pre.
step.
      step. step. step. step. step. step. step. step. step. step.

1-2: cycle 1.

step. step. step. step. step. step. step. step. step. step. step. step. step. step.
step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
steps.
      { subst vAdd. bottom_up_simpl_in_goal. assumption. }
split.
      { (* arbitrarily pick skL, could also pick skR, just need something smaller *)
        eapply tree_skeleton_lt_l. constructor. }

step.
step.
                                                                                .**/
    else {                                                                 /**. .**/
      if (vAdd < x) /* split */ {                                          /**. .**/
        p = a;                                                             /**. .**/
        a = load(p);                                                       /**. .**/
      }                                                                    /**.
        new_ghosts(_, _, skL, _).
        steps.
        lazymatch goal with
        | H: _ \/ _ |- _ \/ _ => destruct H; [left|right]
        end.
        steps.
        steps.
                                                                                .**/
      else {                                                               /**. .**/
        p = a + 8;                                                         /**. .**/
        a = load(p);                                                       /**. .**/
      }                                                                    /**.
      (* TODO can we pull this out of the branches?
        a = load(p);                         *)

        new_ghosts(_, _, skR, _).
        steps.
        lazymatch goal with
        | H: _ \/ _ |- _ \/ _ => destruct H; [left|right]
        end.
        steps.
        steps.
                                                                                .**/
    }                                                                      /**. .**/
  }                                                                        /**. .**/
  if (found) /* split */ {                                                 /**. .**/
    return 1;                                                              /**. .**/
  }                                                                        /**. .**/
  else {                                                                   /**. .**/
    /* key not found, so we zoomed into the tree until it is empty, and
       shrinked the function's postcondition and the context -- there's
       no more tree around, and we'll just retrun a singleton tree! */     /**. .**/
    uintptr_t res = malloc(12);                                            /**. .**/
    if (res) /* split */ {                                                 /**.
      destruct_one_match_hyp. 1: solve [exfalso; steps].
      let h := constr:(#(@with_mem)) in unfold with_mem in h. unfold ready. steps.

      (* ugh, turning malloc'd bytes into a sepapps takes too much code: *)
      assert (<{ * uintptr ? res
                 * uint 32 ? (res ^+ /[4])
                 * uintptr ? (res ^+ /[8]) }> m1). {
        clear_mem_split_eqs. revert H2. clear_heapletwise_hyps.
        intros. unfold anyval in *|-. repeat heapletwise_step.
        set (mAll := m1).
        assert (mmap.du (mmap.Def m1) (mmap.Def map.empty) = mmap.Def mAll) as D. {
          rewrite mmap.du_empty_r. reflexivity.
        }
        clearbody mAll.
        steps.
      }
      clear H2.
      unfold ready. steps.

                                                                                .**/
      store(res, 0);                                                       /**. .**/
      store32(res+4, vAdd);                                                /**. .**/
      store(res+8, 0);                                                     /**. .**/
      store(p, res);                                                       /**. .**/
      return 1;                                                            /**. .**/
    }                                                                      /**.
clear Error. unfold find_hyp_for_range.
instantiate (1 := Leaf).
instantiate (1 := Leaf).
steps. 1-2: intuition lia.

                                                                                .**/
  else {                                                                   /**.
    destruct_one_match_hyp. 2: exfalso; congruence.
    (* malloc failed! *)                                                        .**/
    return 0;                                                              /**. .**/
  }                                                                        /**.
  clear Error.
  instantiate (1 := Leaf).
  unfold find_hyp_for_range.
  steps.
                                                                                .**/
}                                                                          /**. .**/
}                                                                          /**.
(* TODO indentation? *)
Qed.

#[export] Instance spec_of_bst_contains: fnspec :=                              .**/

uintptr_t bst_contains(uintptr_t p, uintptr_t v) /**#
  ghost_args := s (R: mem -> Prop);
  requires t m := <{ * bst s p
                     * R }> m;
  ensures t' m' b := t' = t /\
                     (\[b] = 1 /\ s \[v] \/ \[b] = 0 /\ ~ s \[v]) /\
                     <{ * bst s p
                        * R }> m' #**/                                     /**.
Derive bst_contains SuchThat (fun_correct! bst_contains) As bst_contains_ok.    .**/
{                                                                          /**. .**/
  uintptr_t res = 0;                                                       /**. .**/
  uintptr_t a = load(p);                                                   /**.

  let h := constr:(#bst') in loop pre above h.
  (* TODO this step is needed because `m2 |= uintptr a p` will get pulled into
     the loop pre/post even though it could remain outside (because we currently
     mention the whole memory in the loop). Better: Use/integrate frame rule in
     loop rule so that unneeded mem hyps can stay outside *)
  let h := constr:(#(uintptr a p)) in remember a as root in h.

  unfold ready.
  let cond := constr:(live_expr:(!res && a != 0)) in
  let measure0 := constr:(sk) in
  eapply (wp_while_tailrec_skip_last_pre measure0 (s, a, R) cond).
  1: eauto with wf_of_type.
  { collect_heaplets_into_one_sepclause.
    package_context. }
  { start_loop_body.
    steps.
    { (* loop condition false implies post (which could be constructed here from
         the context, hopefully) *)
      instantiate (1 := fun '(s, olda, F, sk, ti, mi, li) =>
                        exists newa res,
                        li = map.of_list [|("a", newa); ("p", p); ("res", res); ("v", v)|] /\
                          <{ * uintptr a p
                             * freeable 4 p
                             * bst' sk s olda
                             * F }> mi /\
                        (\[res] = 1 /\ s \[v] \/ \[res] = 0 /\ ~ s \[v]) /\
                        ti = t).
      cbv beta iota.
      steps.
(*
    }
    (* loop body: *)
                                                                                .**/
    uintptr_t here = load32(a+4);                                          /**. .**/
    if (v < here) /* split */ {                                            /**. .**/
      a = load(a);                                                         /**. .**/
    }                                                                      /*?.

step. step. step. step. step. step. step. step. step. step. step. step.
step. step. step. step.
step. step.

step. (* change: applies invert_bst'_nonnull in H3, earlier than before! *)

step. step. step. step. step. step. step. step. new_ghosts(_, _, _). step. step. step.
step. step. step. step. step. step. step. step. step. step. step. step. step. step.
step. step. step. step.

.**/
    else {                                                                 /**. .**/
      if (here < v) /* split */ {                                          /**. .**/
        a = load(a+8);                                                     /**. .**/
      }                                                                    /**. .**/
      else {                                                               /**. .**/
        res = 1;                                                           /**. .**/
      }                                                                    /**. .**/
    }                                                                      /**. .**/
  }                                                                        /**.
  }
  (* after loop *)
  subst a. clear res Def0.
  clear_until_LoopInvOrPreOrPost_marker.
  steps.
  subst l.
                                                                                .**/
  return res;                                                              /**. .**/
}                                                                          /**.
Qed.
*)
Abort.

(* note: inability to break out of loop is cumbersome, because it complicates pre:
   it has to incorporate almost all of post for the res=true case,
   and even if we break, we still have to decrease the termination measure *)

End LiveVerif. Comments .**/ //.
