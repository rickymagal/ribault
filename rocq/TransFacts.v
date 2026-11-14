From Coq Require Import String ZArith List Bool Arith Lia.
Import ListNotations.
From Ribault Require Import Syntax Interp Dfg Trans.
Local Open Scope string_scope.

(* every node id in ns is < b *)
Definition nodes_below (ns : list (nodeid * node)) (b : nat) : Prop :=
  forall i nd, In (i, nd) ns -> i < b.

(* every edge source and target in es is < b *)
Definition edges_below (es : list (nodeid * portid * nodeid * portid)) (b : nat) : Prop :=
  forall s sp t tp, In (s, sp, t, tp) es -> s < b /\ t < b.

(* the edge chosen by feeder belongs to the list *)
Lemma feeder_in : forall es tgt tport s sp,
  feeder es tgt tport = Some (s, sp) -> In (s, sp, tgt, tport) es.
Proof.
  induction es as [|[[[s0 sp0] t0] tp0] r IH]; simpl; intros tgt tport s sp H.
  - discriminate.
  - destruct (andb (Nat.eqb t0 tgt) (String.eqb tp0 tport)) eqn:E.
    + apply andb_true_iff in E. destruct E as [E1 E2].
      apply Nat.eqb_eq in E1. apply String.eqb_eq in E2. subst.
      inversion H; subst. left. reflexivity.
    + right. apply IH. exact H.
Qed.

(* a prefix of fresh nodes (id >= b) does not affect the lookup of an id < b *)
Lemma lookup_node_app_skip : forall ns_ex ns m b,
  (forall i nd, In (i, nd) ns_ex -> b <= i) -> m < b ->
  lookup_node (ns_ex ++ ns) m = lookup_node ns m.
Proof.
  induction ns_ex as [|[j nd] r IH]; intros ns m b Hex Hm; simpl.
  - reflexivity.
  - destruct (Nat.eqb m j) eqn:E.
    + apply Nat.eqb_eq in E. subst j.
      specialize (Hex m nd (or_introl eq_refl)). lia.
    + apply (IH ns m b); [| exact Hm].
      intros i nd' Hin. apply (Hex i nd'). right. exact Hin.
Qed.

(* a prefix of edges with a fresh target (>= b) does not affect the feeder of a target < b *)
Lemma feeder_app_skip : forall es_ex es m p b,
  (forall s sp t tp, In (s, sp, t, tp) es_ex -> b <= t) -> m < b ->
  feeder (es_ex ++ es) m p = feeder es m p.
Proof.
  induction es_ex as [|[[[s sp] t] tp] r IH]; intros es m p b Hex Hm; simpl.
  - reflexivity.
  - destruct (andb (Nat.eqb t m) (String.eqb tp p)) eqn:E.
    + apply andb_true_iff in E. destruct E as [E1 _].
      apply Nat.eqb_eq in E1. subst t.
      specialize (Hex s sp m tp (or_introl eq_refl)). lia.
    + apply (IH es m p b); [| exact Hm].
      intros s' sp' t' tp' Hin. apply (Hex s' sp' t' tp'). right. exact Hin.
Qed.

(* MONOTONICITY: evaluating an old node (m < b) is invariant under prepending
   fresh nodes (id >= b) and edges with a fresh target (target >= b). *)
Lemma eval_dfg_extend :
  forall fuel ns_ex es_ex ns es env b,
    edges_below es b ->
    (forall i nd, In (i, nd) ns_ex -> b <= i) ->
    (forall s sp t tp, In (s, sp, t, tp) es_ex -> b <= t) ->
    forall m p, m < b ->
      eval_dfg fuel {| dnodes := ns; dedges := es |} env m p
      = eval_dfg fuel {| dnodes := ns_ex ++ ns; dedges := es_ex ++ es |} env m p.
Proof.
  induction fuel as [|fuel IH]; intros ns_ex es_ex ns es env b Heb Hnx Hex m p Hm.
  - reflexivity.
  - cbn [eval_dfg dnodes dedges]. cbv zeta.
    rewrite (lookup_node_app_skip ns_ex ns m b Hnx Hm).
    assert (Hres : forall p',
      match feeder (es_ex ++ es) m p' with
      | Some (s, sp) =>
          eval_dfg fuel {| dnodes := ns_ex ++ ns; dedges := es_ex ++ es |} env s sp
      | None => Err
      end
      = match feeder es m p' with
        | Some (s, sp) => eval_dfg fuel {| dnodes := ns; dedges := es |} env s sp
        | None => Err
        end).
    { intro p'. rewrite (feeder_app_skip es_ex es m p' b Hex Hm).
      destruct (feeder es m p') as [[s sp]|] eqn:Ef; [| reflexivity].
      assert (Hs : s < b) by (apply (Heb s sp m p'); apply feeder_in; exact Ef).
      symmetry. apply (IH ns_ex es_ex ns es env b Heb Hnx Hex s sp Hs). }
    destruct (lookup_node ns m) as [nd|]; [| reflexivity].
    destruct nd; repeat rewrite Hres; reflexivity.
Qed.
